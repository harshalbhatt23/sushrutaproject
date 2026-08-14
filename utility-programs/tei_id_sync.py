#!/usr/bin/env python3
"""
tei-id-sync — parallel xml:id work across TEI/XML transcriptions of one text.

Usage:
    python3 tei_id_sync.py /path/to/folder
    python3 tei_id_sync.py file1.xml file2.txt file3.xml
    python3 tei_id_sync.py /path/to/folder --port 8765 --no-browser

Opens a local page in your browser. Nothing leaves your machine; no
dependencies beyond the Python standard library (3.8+).

What it does
------------
* Renames @xml:id values in parallel across every file, updating the
  pointing attributes (@corresp, @target ...) that refer to them.
* Merges two identifiers into one, either by folding the values together
  or by joining two adjacent elements into a single passage.
* Splits one passage into two at a point you choose, giving the second
  half a new identifier.
* Gives an @xml:id to an element that has none.

Design notes
------------
* Extension is not taken as a guarantee of content: .xml/.tei/.xhtml are
  always read, .txt files in a folder are read when they contain markup,
  and any file named directly on the command line is read regardless.
* Edits are made on the raw text of each file. The files are never parsed
  and re-serialised, so whitespace, comments, entity references, attribute
  order and line endings survive untouched.
* A rename set is applied in ONE pass, so swaps (a -> b, b -> a) and
  cascades (a -> b, b -> c) behave as you would expect.
* Structural edits are splices at offsets that are re-derived from the
  file on every preview and checked against a fingerprint before saving.
* Every save writes a timestamped backup of each touched file, plus a
  JSON log of what was done.
"""

import argparse
import difflib
import html
import json
import os
import re
import shutil
import sys
import threading
import webbrowser
from bisect import bisect_right
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

# --------------------------------------------------------------------------
# scanning
# --------------------------------------------------------------------------

XML_EXTS = (".xml", ".tei", ".xhtml")
# extensions that are only picked up if the file actually contains markup,
# so a stray notes.txt in the folder does not become a phantom witness
SNIFF_EXTS = (".txt",)
BACKUP_DIR = ".tei-id-sync-backups"

# attributes whose value may contain one or more "#id" pointers
POINTER_ATTRS = [
    "corresp", "target", "ref", "sameAs", "copyOf", "next", "prev",
    "source", "synch", "facs", "select", "exclude", "from", "to",
    "start", "end", "who", "spanTo", "resp", "decls", "change",
    "adj", "mergedIn", "location",
]
ALL_ATTRS = ["xml:id"] + POINTER_ATTRS

ATTR_RE = re.compile(
    r"(?<![\w:.-])(" + "|".join(re.escape(a) for a in ALL_ATTRS) + r")(\s*=\s*)([\"'])(.*?)\3",
    re.S,
)
ANY_ATTR_RE = re.compile(r"([\w:.-]+)\s*=\s*([\"'])(.*?)\2", re.S)
TAG_NAME_RE = re.compile(r"<\s*([\w:.-]+)")
TAGGISH_RE = re.compile(r"<[A-Za-z_][\w:.-]*[\s/>]")
TAG_STRIP_RE = re.compile(r"<[^>]*>")
WS_RE = re.compile(r"\s+")
NCNAME_RE = re.compile(r"^[A-Za-z_][\w.\-]*$")
MASK_RE = re.compile(r"<!--.*?-->|<!\[CDATA\[.*?\]\]>", re.S)

# elements offered in the structure view when they carry no xml:id
DEFAULT_STRUCTURE_ELEMENTS = "div p lg l ab seg head trailer label app note"


def masked(text):
    """Start offsets of comments/CDATA, so their contents are left alone."""
    spans = [(m.start(), m.end()) for m in MASK_RE.finditer(text)]
    starts = [s for s, _ in spans]

    def inside(pos):
        i = bisect_right(starts, pos) - 1
        return i >= 0 and pos < spans[i][1]

    return inside


def looks_like_xml(path, probe=16384):
    """True if the head of the file contains at least one element tag."""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            return bool(TAGGISH_RE.search(fh.read(probe)))
    except OSError:
        return False


def collect_files(paths, extra_exts=()):
    always = XML_EXTS + tuple(extra_exts)
    out = []
    for p in paths:
        if os.path.isdir(p):
            for root, dirs, names in os.walk(p):
                dirs[:] = [d for d in dirs if not d.startswith(".")]
                for n in sorted(names):
                    low, full = n.lower(), os.path.join(root, n)
                    if low.endswith(always):
                        out.append(full)
                    elif low.endswith(SNIFF_EXTS) and looks_like_xml(full):
                        out.append(full)
        elif os.path.isfile(p):
            out.append(p)  # named outright, so take it at its word
    return sorted(dict.fromkeys(os.path.abspath(f) for f in out))


def read_text(path):
    with open(path, "r", encoding="utf-8", newline="") as fh:
        return fh.read()


def line_of(text, pos):
    return text.count("\n", 0, pos) + 1


def element_at(text, pos):
    start = text.rfind("<", 0, pos)
    if start == -1:
        return "?"
    m = TAG_NAME_RE.match(text, start)
    return m.group(1) if m else "?"


def plain(fragment, out=150):
    s = TAG_STRIP_RE.sub(" ", fragment)
    s = html.unescape(s)
    return WS_RE.sub(" ", s).strip()[:out]


def context_at(text, pos, width=260, out=150):
    return plain(text[pos: pos + width], out)


def scan(files, root):
    """Return (file_records, groups)."""
    file_recs = []
    groups = {}

    def group(v):
        return groups.setdefault(v, {"id": v, "defs": [], "refs": []})

    for path in files:
        try:
            text = read_text(path)
        except (OSError, UnicodeDecodeError) as exc:
            file_recs.append({"path": path, "label": os.path.relpath(path, root),
                              "error": str(exc), "defs": 0, "refs": 0})
            continue
        rel = os.path.relpath(path, root)
        ndef = nref = 0
        skip = masked(text)
        for m in ATTR_RE.finditer(text):
            attr, val, pos = m.group(1), m.group(4), m.start()
            if skip(pos):
                continue
            if attr == "xml:id":
                ndef += 1
                group(val)["defs"].append({
                    "file": rel,
                    "line": line_of(text, pos),
                    "element": element_at(text, pos),
                    "context": context_at(text, m.end()),
                })
            else:
                for tok in val.split():
                    if tok.startswith("#") and len(tok) > 1:
                        nref += 1
                        group(tok[1:])["refs"].append({
                            "file": rel,
                            "line": line_of(text, pos),
                            "element": element_at(text, pos),
                            "attr": attr,
                        })
        file_recs.append({"path": path, "label": rel, "defs": ndef, "refs": nref})

    n_files = len([f for f in file_recs if "error" not in f])
    for g in groups.values():
        files_with_def = sorted({d["file"] for d in g["defs"]})
        g["files"] = files_with_def
        g["nDefs"] = len(g["defs"])
        g["nRefs"] = len(g["refs"])
        g["duplicated"] = len(files_with_def) != len(g["defs"])
        g["partial"] = 0 < len(files_with_def) < n_files
        g["dangling"] = len(g["defs"]) == 0

    ordered = sorted(groups.values(), key=lambda g: g["id"])
    return file_recs, ordered


# --------------------------------------------------------------------------
# a small tag walker — enough to find element boundaries in well-formed XML
# --------------------------------------------------------------------------

def iter_tags(text, start=0):
    """Yield (kind, start, end, name); kind is open/close/empty/skip."""
    i, n = start, len(text)
    while True:
        j = text.find("<", i)
        if j == -1:
            return
        for opener, closer in (("<!--", "-->"), ("<![CDATA[", "]]>"), ("<?", "?>")):
            if text.startswith(opener, j):
                k = text.find(closer, j + len(opener))
                k = n if k == -1 else k + len(closer)
                yield ("skip", j, k, None)
                i = k
                break
        else:
            if text.startswith("<!", j):          # doctype or other declaration
                k = text.find(">", j)
                k = n if k == -1 else k + 1
                yield ("skip", j, k, None)
                i = k
                continue
            k, quote = j + 1, None                # element tag; mind quoted '>'
            while k < n:
                c = text[k]
                if quote:
                    if c == quote:
                        quote = None
                elif c in "\"'":
                    quote = c
                elif c == ">":
                    break
                k += 1
            end = min(k + 1, n)
            raw = text[j:end]
            if raw.startswith("</"):
                yield ("close", j, end, raw[2:-1].strip())
            else:
                m = TAG_NAME_RE.match(raw)
                name = m.group(1) if m else ""
                yield ("empty" if raw.rstrip().endswith("/>") else "open", j, end, name)
            i = end


def element_span(text, tag_start):
    """(open_end, content_end, close_end, name) for the element opening here."""
    it = iter_tags(text, tag_start)
    kind, s, open_end, name = next(it, (None, 0, 0, None))
    if kind not in ("open", "empty") or s != tag_start:
        raise ValueError("no element starts at that position")
    if kind == "empty":
        return open_end, open_end, open_end, name
    depth = 1
    for kind, s, e, nm in it:
        if kind == "open" and nm == name:
            depth += 1
        elif kind == "close" and nm == name:
            depth -= 1
            if depth == 0:
                return open_end, s, e, name
    raise ValueError("<%s> is never closed" % name)


def attrs_of(text, tag_start, open_end):
    raw = text[tag_start:open_end]
    m = TAG_NAME_RE.match(raw)
    raw = raw[m.end():] if m else raw
    return {a.group(1): a.group(3) for a in ANY_ATTR_RE.finditer(raw)}


def next_sibling(text, close_end, name):
    """Offset of the next sibling <name> if only whitespace/comments precede."""
    for kind, s, e, nm in iter_tags(text, close_end):
        if text[close_end:s].strip():
            return None
        if kind == "skip":
            close_end = e
            continue
        if kind in ("open", "empty") and nm == name:
            return s
        return None
    return None


def top_level_parts(text, content_start, content_end):
    """Words and whole child elements at depth 0 inside an element."""
    parts, i = [], content_start
    for kind, s, e, nm in iter_tags(text, content_start):
        if s >= content_end:
            break
        if s < i:            # already inside a child element we consumed
            continue
        if s > i:
            for m in re.finditer(r"\S+", text[i:s]):
                parts.append({"kind": "word", "at": i + m.start(),
                              "text": html.unescape(m.group(0))})
        if kind == "skip":
            parts.append({"kind": "other", "at": s, "text": plain(text[s:e], 40)})
            i = e
            continue
        if kind == "empty":
            parts.append({"kind": "node", "at": s, "name": nm, "text": ""})
            i = e
            continue
        if kind == "close":
            i = e
            continue
        _oe, _ce, close_end, _nm = element_span(text, s)
        parts.append({"kind": "node", "at": s, "name": nm,
                      "text": plain(text[s:close_end], 60)})
        i = close_end
    if content_end > i:
        for m in re.finditer(r"\S+", text[i:content_end]):
            parts.append({"kind": "word", "at": i + m.start(),
                          "text": html.unescape(m.group(0))})
    return parts


def element_detail(text, rel, at):
    """Everything the structure view needs about one element."""
    open_end, content_end, close_end, name = element_span(text, at)
    attrs = attrs_of(text, at, open_end)
    nxt, sib = next_sibling(text, close_end, name), None
    if nxt is not None:
        n_open_end, n_content_end, _nc, _nn = element_span(text, nxt)
        n_attrs = attrs_of(text, nxt, n_open_end)
        sib = {"at": nxt, "id": n_attrs.get("xml:id"), "line": line_of(text, nxt),
               "attrs": {k: v for k, v in n_attrs.items() if k != "xml:id"},
               "preview": plain(text[n_open_end:n_content_end], 180)}
    return {"file": rel, "at": at, "name": name, "id": attrs.get("xml:id"),
            "attrs": {k: v for k, v in attrs.items() if k != "xml:id"},
            "check": text[at:open_end][:48], "line": line_of(text, at),
            "parts": top_level_parts(text, open_end, content_end), "sibling": sib}


def outline(text, rel, names, only_unlabelled=False):
    """Structural blocks of one file, for the structure view."""
    wanted, blocks, stack = set(names), [], []
    skip = masked(text)
    for kind, s, e, nm in iter_tags(text):
        if kind == "skip" or skip(s):
            continue
        if kind == "close":
            if stack:
                stack.pop()
            continue
        depth = len(stack)
        if kind == "open":
            stack.append(nm)
        attrs = attrs_of(text, s, e)
        ident = attrs.get("xml:id")
        if not (ident or nm in wanted):
            continue
        if only_unlabelled and ident:
            continue
        try:
            _oe, content_end, close_end, _nm = element_span(text, s)
        except ValueError:
            continue
        blocks.append({
            "file": rel, "elem": s, "name": nm, "id": ident, "depth": min(depth, 6),
            "line": line_of(text, s), "check": text[s:e][:48],
            "attrs": {k: v for k, v in attrs.items() if k != "xml:id"},
            "preview": plain(text[e:content_end], 180),
            "empty": e == close_end,
            "joinable": next_sibling(text, close_end, nm) is not None,
        })
    return blocks


# --------------------------------------------------------------------------
# editing
# --------------------------------------------------------------------------

def rewrite(text, mapping):
    """Apply the whole rename mapping in a single pass."""
    hits = [0]
    skip = masked(text)

    def repl(m):
        if skip(m.start()):
            return m.group(0)
        attr, eq, q, val = m.group(1), m.group(2), m.group(3), m.group(4)
        if attr == "xml:id":
            if val in mapping:
                hits[0] += 1
                return attr + eq + q + mapping[val] + q
            return m.group(0)
        if "#" not in val:
            return m.group(0)
        parts, changed = [], False
        for tok in val.split():
            if tok.startswith("#") and tok[1:] in mapping:
                parts.append("#" + mapping[tok[1:]])
                changed = True
            else:
                parts.append(tok)
        if not changed:
            return m.group(0)
        hits[0] += 1
        return attr + eq + q + " ".join(parts) + q

    return ATTR_RE.sub(repl, text), hits[0]


def splices_for(text, op):
    """Turn one structural operation into (start, end, replacement) edits."""
    at = op["elem"]
    if op.get("check") and not text.startswith(op["check"], at):
        raise ValueError("the file has changed since this was queued")
    open_end, content_end, close_end, name = element_span(text, at)
    kind = op["kind"]

    if kind == "assign":
        if "xml:id" in attrs_of(text, at, open_end):
            raise ValueError("<%s> already carries an xml:id" % name)
        cut = at + text[at:open_end].index(name) + len(name)
        return [(cut, cut, ' xml:id="%s"' % op["id"])]

    if kind == "split":
        cut = int(op["cut"])
        if not open_end < cut < content_end:
            raise ValueError("the split point is no longer inside the element")
        keep = ""
        if op.get("copyAttrs"):
            keep = "".join(' %s="%s"' % (k, v) for k, v in
                           attrs_of(text, at, open_end).items() if k != "xml:id")
        return [(cut, cut, '</%s><%s xml:id="%s"%s>' % (name, name, op["id"], keep))]

    if kind == "join":
        nxt = next_sibling(text, close_end, name)
        if nxt is None:
            raise ValueError("there is no adjacent <%s> to join with" % name)
        n_open_end, _n_content_end, _n_close_end, _nm = element_span(text, nxt)
        first_id = attrs_of(text, at, open_end).get("xml:id")
        second_id = attrs_of(text, nxt, n_open_end).get("xml:id")
        retired = first_id if op.get("keep") == "second" else second_id
        edits = []
        if op.get("keep") == "second" and second_id:
            m = ATTR_RE.search(text, at, open_end)
            while m and m.group(1) != "xml:id":
                m = ATTR_RE.search(text, m.end(), open_end)
            if m:
                edits.append((m.start(), m.end(), 'xml:id="%s"' % second_id))
            else:
                cut = at + text[at:open_end].index(name) + len(name)
                edits.append((cut, cut, ' xml:id="%s"' % second_id))
        anchor = ('<anchor xml:id="%s"/>' % retired) if (op.get("anchor") and retired) else ""
        edits.append((content_end, close_end, anchor))   # drop first close tag
        edits.append((nxt, n_open_end, ""))              # drop second open tag
        return edits

    raise ValueError("unknown operation " + kind)


def apply_ops(text, ops):
    """Apply structural operations to one file's text; returns (text, n)."""
    edits = []
    for op in ops:
        edits.extend(splices_for(text, op))
    edits.sort(key=lambda e: e[0], reverse=True)
    last_start = last_end = None
    for start, end, _repl in edits:
        if last_start is not None and end > last_start:
            raise ValueError("two queued changes overlap in this file")
        if (start, end) == (last_start, last_end):
            raise ValueError("two queued changes fall at the same point in this file")
        last_start, last_end = start, end
    for start, end, repl in edits:
        text = text[:start] + repl + text[end:]
    return text, len(edits)


def new_text(path, ops, mapping):
    text = read_text(path)
    out, n_ops = apply_ops(text, ops) if ops else (text, 0)
    out, n_ren = rewrite(out, mapping) if mapping else (out, 0)
    return text, out, n_ops + n_ren


def diff_lines(old, new, cap=500):
    out = []
    for line in difflib.unified_diff(old.splitlines(), new.splitlines(),
                                     n=1, lineterm=""):
        if line.startswith(("---", "+++")):
            continue
        out.append({"t": line[0] if line[:1] in ("@", "-", "+") else " ",
                    "s": line[1:] if line[:1] in ("-", "+", " ") else line})
        if len(out) >= cap:
            out.append({"t": "@", "s": " … truncated"})
            break
    return out


def duplicate_ids(text):
    seen, dupes = set(), set()
    skip = masked(text)
    for m in ATTR_RE.finditer(text):
        if m.group(1) == "xml:id" and not skip(m.start()):
            v = m.group(4)
            if v in seen:
                dupes.add(v)
            seen.add(v)
    return sorted(dupes)


def by_file(ops, files, root):
    """Group queued operations by absolute path."""
    index = {os.path.relpath(p, root): p for p in files}
    out = {}
    for op in ops:
        path = index.get(op.get("file"))
        if path:
            out.setdefault(path, []).append(op)
    return out


def plan(files, root, mapping, ops):
    grouped = by_file(ops, files, root)
    result, total = [], 0
    for path in files:
        rel = os.path.relpath(path, root)
        try:
            old, new, hits = new_text(path, grouped.get(path, []), mapping)
        except (OSError, UnicodeDecodeError):
            continue
        except ValueError as exc:
            result.append({"label": rel, "hits": 0, "diff": [],
                           "duplicates": [], "error": str(exc)})
            continue
        if not hits or old == new:
            continue
        total += hits
        result.append({"label": rel, "hits": hits, "diff": diff_lines(old, new),
                       "duplicates": duplicate_ids(new)})
    return result, total


def apply_changes(files, root, mapping, ops):
    grouped = by_file(ops, files, root)
    stamp = datetime.now().strftime("%Y-%m-%d_%H%M%S")
    bdir = os.path.join(root, BACKUP_DIR, stamp)
    prepared, errors = [], []
    for path in files:                      # everything is computed before
        rel = os.path.relpath(path, root)   # anything is written
        try:
            old, new, hits = new_text(path, grouped.get(path, []), mapping)
        except (OSError, UnicodeDecodeError):
            continue
        except ValueError as exc:
            errors.append({"label": rel, "error": str(exc)})
            continue
        if hits and old != new:
            prepared.append((path, rel, new, hits))
    if errors:
        return {"errors": errors, "files": [], "stamp": None}
    touched, dupes = [], {}
    for path, rel, new, hits in prepared:
        dest = os.path.join(bdir, rel)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        shutil.copy2(path, dest)
        with open(path, "w", encoding="utf-8", newline="") as fh:
            fh.write(new)
        touched.append({"label": rel, "hits": hits})
        d = duplicate_ids(new)
        if d:
            dupes[rel] = d
    if touched:
        with open(os.path.join(bdir, "changes.json"), "w", encoding="utf-8") as fh:
            json.dump({"when": stamp, "renames": mapping, "operations": ops,
                       "files": [t["label"] for t in touched]}, fh,
                      ensure_ascii=False, indent=2)
    return {"stamp": stamp, "backup": bdir, "files": touched,
            "duplicates": dupes, "errors": []}


def list_backups(root):
    base = os.path.join(root, BACKUP_DIR)
    if not os.path.isdir(base):
        return []
    return sorted((d for d in os.listdir(base)
                   if os.path.isdir(os.path.join(base, d))), reverse=True)


def restore(root, stamp):
    base = os.path.join(root, BACKUP_DIR, stamp)
    if not os.path.isdir(base):
        raise ValueError("no such backup")
    restored = []
    for droot, _dirs, names in os.walk(base):
        for n in names:
            if n == "changes.json":
                continue
            src = os.path.join(droot, n)
            rel = os.path.relpath(src, base)
            shutil.copy2(src, os.path.join(root, rel))
            restored.append(rel)
    return restored


# --------------------------------------------------------------------------
# page
# --------------------------------------------------------------------------

PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>xml:id sync</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=EB+Garamond:ital,wght@0,400;0,500;0,600;1,400&display=swap" rel="stylesheet">
<style>
:root{
  --leaf:#e9e6dd; --paper:#faf9f6; --rule:#cfc9bb; --rule-soft:#e2ddd2;
  --ink:#1e1b16; --ink-soft:#6d665a; --rubric:#9e2b25; --indigo:#27455c;
  --indigo-soft:#e6ecf0; --rubric-soft:#f6e6e3;
  --serif:"EB Garamond","Iowan Old Style",Palatino,"Palatino Linotype",Georgia,serif;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,"DejaVu Sans Mono",monospace;
}
*{box-sizing:border-box}
html,body{height:100%}
body{margin:0;background:var(--leaf);color:var(--ink);font-family:var(--serif);font-size:17px;line-height:1.45}
button,input,select{font:inherit;color:inherit}
h1,h2,h3{margin:0;font-weight:500}

#app{display:flex;flex-direction:column;height:100vh}
header{display:flex;align-items:baseline;gap:18px;flex-wrap:wrap;
  padding:10px 20px;background:var(--paper);border-bottom:1px solid var(--rule)}
header .mark{font-size:20px;letter-spacing:.02em}
header .mark em{font-style:italic;color:var(--rubric)}
header .path{font-family:var(--mono);font-size:12px;color:var(--ink-soft);
  overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:34ch}
header .tally{font-size:14px;color:var(--ink-soft)}
header .spacer{flex:1}
.views{display:flex;border:1px solid var(--rule);border-radius:2px;overflow:hidden}
.views button{background:var(--paper);border:0;padding:5px 14px;cursor:pointer;font-size:15px}
.views button+button{border-left:1px solid var(--rule)}
.views button[aria-pressed="true"]{background:var(--indigo);color:#fff}

main{flex:1;display:grid;grid-template-columns:270px minmax(0,1fr) 340px;min-height:0}
main.wide{grid-template-columns:minmax(0,1fr) 340px}
.pane{min-height:0;overflow:auto;background:var(--paper)}
.pane+.pane{border-left:1px solid var(--rule)}
.pane h2{font-size:13px;letter-spacing:.14em;text-transform:uppercase;color:var(--ink-soft);
  padding:12px 16px 6px;font-family:var(--mono);font-weight:400}

.filters{padding:0 16px 10px;display:flex;flex-wrap:wrap;gap:5px}
.filters button{background:none;border:1px solid var(--rule-soft);border-radius:999px;
  padding:2px 10px;font-size:13px;cursor:pointer;color:var(--ink-soft)}
.filters button[aria-pressed="true"]{border-color:var(--indigo);color:var(--indigo);background:var(--indigo-soft)}
.search{padding:0 16px 10px}
.search input{width:100%;padding:6px 8px;border:1px solid var(--rule);border-radius:2px;
  background:#fff;font-family:var(--mono);font-size:13px}
ul.ids{list-style:none;margin:0;padding:0 0 40px}
ul.ids li{border-top:1px solid var(--rule-soft)}
ul.ids button{width:100%;text-align:left;background:none;border:0;cursor:pointer;
  padding:7px 16px;display:flex;align-items:baseline;gap:8px}
ul.ids button:hover{background:var(--indigo-soft)}
ul.ids li.on button{background:var(--indigo);color:#fff}
ul.ids .name{font-family:var(--mono);font-size:13px;flex:1;overflow-wrap:anywhere}
ul.ids .n{font-size:12px;color:var(--ink-soft);font-family:var(--mono)}
ul.ids li.on .n{color:#cfe0ea}
ul.ids .flag{color:var(--rubric);font-size:13px}
ul.ids li.on .flag{color:#ffb9b4}
ul.ids .queued .name{text-decoration:line-through;opacity:.65}

.detail{padding:4px 22px 60px}
.detail .idhead{font-family:var(--mono);font-size:19px;padding:6px 0 2px;overflow-wrap:anywhere}
.detail .sub{color:var(--ink-soft);font-size:14px;margin-bottom:14px}
.witness{border-top:1px solid var(--rule-soft);padding:9px 0}
.witness .file{font-family:var(--mono);font-size:12px;color:var(--indigo)}
.witness .where{font-family:var(--mono);font-size:12px;color:var(--ink-soft)}
.witness .ctx{margin-top:3px;font-size:16px}
.witness .ctx:empty::after{content:"(no text follows)";color:var(--ink-soft);font-style:italic}
.reflist{margin-top:16px;font-size:14px;color:var(--ink-soft)}
.reflist code{font-family:var(--mono);font-size:12px}
.empty{padding:40px 22px;color:var(--ink-soft);font-style:italic}

.matrixwrap{overflow:auto;height:100%;padding:0 0 60px}
table.matrix{border-collapse:collapse;font-size:13px}
table.matrix th,table.matrix td{border:1px solid var(--rule-soft);padding:3px 7px}
table.matrix thead th{position:sticky;top:0;background:var(--paper);z-index:2;
  font-family:var(--mono);font-weight:400;font-size:11px;text-align:left;
  writing-mode:vertical-rl;transform:rotate(180deg);height:150px;white-space:nowrap}
table.matrix tbody th{position:sticky;left:0;background:var(--paper);text-align:left;
  font-family:var(--mono);font-weight:400;z-index:1;cursor:pointer;white-space:nowrap}
table.matrix tbody th:hover{color:var(--rubric)}
table.matrix td{text-align:center;color:var(--indigo)}
table.matrix td.miss{color:var(--rule)}
table.matrix td.dup{background:var(--rubric-soft);color:var(--rubric);font-weight:600}
table.matrix td.ref{color:var(--ink-soft)}
table.matrix tr.on th,table.matrix tr.on td{background:var(--indigo-soft)}
.legend{padding:10px 16px;font-size:13px;color:var(--ink-soft)}
.legend code{font-family:var(--mono);color:var(--indigo)}

/* ---- structure ---- */
.stbar{position:sticky;top:0;background:var(--paper);border-bottom:1px solid var(--rule);
  padding:10px 20px;display:flex;gap:10px;flex-wrap:wrap;align-items:center;z-index:3}
.stbar select,.stbar input[type=text]{padding:5px 8px;border:1px solid var(--rule);
  border-radius:2px;background:#fff;font-family:var(--mono);font-size:13px}
.stbar select{max-width:26ch}
.stbar .grow{flex:1;min-width:120px}
.stbar label{font-size:14px;color:var(--ink-soft);display:flex;align-items:center;gap:5px}
.blocks{padding:0 0 80px}
.blk{border-bottom:1px solid var(--rule-soft);padding:9px 20px}
.blk:hover{background:#fdfdfb}
.bhead{display:flex;align-items:baseline;gap:9px;flex-wrap:wrap}
.blk .ln{font-family:var(--mono);font-size:11px;color:var(--ink-soft);min-width:3.5ch;text-align:right}
.blk .gi{font-family:var(--mono);font-size:13px;color:var(--indigo)}
.blk .idchip{font-family:var(--mono);font-size:13px;background:var(--indigo-soft);
  color:var(--indigo);padding:0 6px;border-radius:2px;overflow-wrap:anywhere}
.blk .idchip.none{background:var(--rubric-soft);color:var(--rubric);font-style:italic}
.blk .acts{margin-left:auto;display:flex;gap:6px}
.blk .acts button{background:none;border:1px solid var(--rule-soft);border-radius:2px;
  padding:1px 9px;font-size:14px;cursor:pointer;color:var(--indigo);white-space:nowrap}
.blk .acts button:hover{border-color:var(--indigo);background:var(--indigo-soft)}
.blk .prev{margin:2px 0 0 4.6ch;color:var(--ink)}
.blk[data-indent="1"] .prev,.blk[data-indent="1"] .bhead{margin-left:14px}
.blk[data-indent="2"] .prev,.blk[data-indent="2"] .bhead{margin-left:28px}
.blk[data-indent="3"] .prev,.blk[data-indent="3"] .bhead{margin-left:42px}
.work{margin:10px 0 4px 4.6ch;border-left:2px solid var(--rubric);padding:8px 0 8px 14px;background:#fff}
.work .lede{font-size:14px;color:var(--ink-soft);margin-bottom:8px}
.work .field{display:flex;gap:8px;align-items:center;flex-wrap:wrap;margin-top:9px}
.work input[type=text]{padding:5px 8px;border:1px solid var(--rule);border-radius:2px;
  background:#fff;font-family:var(--mono);font-size:14px;min-width:22ch}
.work label{font-size:14px;display:flex;align-items:center;gap:5px}
.work .warn{color:var(--rubric);font-size:14px;margin-top:7px}

/* the split ruler: click a gap to place the division */
.ruler{line-height:2.1;font-size:17px}
.ruler .tok{white-space:pre-wrap}
.ruler .node{font-family:var(--mono);font-size:12px;background:var(--indigo-soft);
  color:var(--indigo);padding:1px 5px;border-radius:2px}
.ruler .gap{display:inline-block;width:1.1ch;margin:0 -.1ch;padding:0;border:0;background:none;
  color:transparent;cursor:pointer;font-size:17px;line-height:1;vertical-align:baseline}
.ruler .gap::before{content:"।"}
.ruler .gap:hover{color:var(--rule)}
.ruler .gap[aria-pressed="true"]{color:var(--rubric);font-weight:600}
.ruler .gap:focus-visible{color:var(--rubric)}

.editor{padding:0 16px 16px;border-bottom:1px solid var(--rule)}
.editor label{display:block;font-size:12px;letter-spacing:.1em;text-transform:uppercase;
  font-family:var(--mono);color:var(--ink-soft);margin:8px 0 3px}
.editor input{width:100%;padding:6px 8px;border:1px solid var(--rule);border-radius:2px;
  background:#fff;font-family:var(--mono);font-size:14px}
.editor input:disabled{background:var(--leaf);color:var(--ink-soft)}
.row{display:flex;gap:8px;margin-top:10px}
.btn{border:1px solid var(--indigo);background:var(--indigo);color:#fff;border-radius:2px;
  padding:6px 14px;cursor:pointer;font-size:15px}
.btn.ghost{background:none;color:var(--indigo)}
.btn.warn{border-color:var(--rubric);background:var(--rubric)}
.btn:disabled{opacity:.4;cursor:not-allowed}
.note{font-size:13px;margin-top:7px;color:var(--rubric)}
.note.ok{color:var(--indigo)}
table.queue{width:100%;border-collapse:collapse;font-size:13px}
table.queue td{border-top:1px solid var(--rule-soft);padding:4px 6px;vertical-align:top;overflow-wrap:anywhere}
table.queue .what{font-family:var(--mono);font-size:11px;letter-spacing:.06em;
  text-transform:uppercase;color:var(--ink-soft);width:5.4em}
table.queue .lbl{font-family:var(--mono);font-size:12px}
table.queue .lbl b{color:var(--rubric);font-weight:400}
table.queue td.kill{width:1.6em;text-align:center}
table.queue button{background:none;border:0;color:var(--ink-soft);cursor:pointer;font-size:14px;padding:0}
table.queue button:hover{color:var(--rubric)}
.bulk{padding:12px 16px;border-top:1px solid var(--rule)}
.bulk input{width:100%;margin-bottom:6px;padding:5px 8px;border:1px solid var(--rule);
  border-radius:2px;background:#fff;font-family:var(--mono);font-size:13px}

.sheet{position:fixed;inset:0;background:rgba(30,27,22,.45);display:flex;
  align-items:center;justify-content:center;padding:26px;z-index:10}
.sheet .card{background:var(--paper);border-radius:3px;max-width:960px;width:100%;
  max-height:100%;display:flex;flex-direction:column;box-shadow:0 18px 50px rgba(0,0,0,.3)}
.sheet .card>h3{padding:16px 22px;border-bottom:1px solid var(--rule);font-size:20px}
.sheet .body{overflow:auto;padding:8px 22px 22px}
.sheet .foot{padding:12px 22px;border-top:1px solid var(--rule);display:flex;gap:10px;justify-content:flex-end}
.dfile{font-family:var(--mono);font-size:13px;color:var(--indigo);margin:16px 0 4px}
.dl{font-family:var(--mono);font-size:12px;white-space:pre-wrap;padding:1px 6px;overflow-wrap:anywhere}
.dl.minus{background:var(--rubric-soft);color:var(--rubric)}
.dl.plus{background:var(--indigo-soft);color:var(--indigo)}
.dl.at{color:var(--ink-soft);margin-top:6px}
.alarm{background:var(--rubric-soft);border-left:3px solid var(--rubric);padding:9px 14px;margin:12px 0;font-size:15px}
.toast{position:fixed;bottom:18px;left:50%;transform:translateX(-50%);background:var(--ink);
  color:var(--paper);padding:9px 18px;border-radius:2px;font-size:15px;z-index:20}
@media (max-width:1100px){main,main.wide{grid-template-columns:1fr}.pane+.pane{border-left:0;border-top:1px solid var(--rule)}}
:focus-visible{outline:2px solid var(--rubric);outline-offset:1px}
</style>
</head>
<body>
<div id="app">
  <header>
    <span class="mark">xml:<em>id</em> sync</span>
    <span class="path" id="root"></span>
    <span class="tally" id="tally"></span>
    <span class="spacer"></span>
    <span class="views">
      <button id="vList" aria-pressed="true">Passages</button>
      <button id="vMatrix" aria-pressed="false">Witness grid</button>
      <button id="vStruct" aria-pressed="false">Structure</button>
    </span>
    <button class="btn ghost" id="rescan">Reload files</button>
    <button class="btn ghost" id="undo">Restore backup</button>
  </header>
  <main id="main">
    <section class="pane" id="paneList">
      <h2>Identifiers</h2>
      <div class="search"><input id="q" placeholder="filter…" autocomplete="off"></div>
      <div class="filters">
        <button data-f="all" aria-pressed="true">all</button>
        <button data-f="partial" aria-pressed="false">not in every file</button>
        <button data-f="dup" aria-pressed="false">repeated in a file</button>
        <button data-f="dangling" aria-pressed="false">pointed at, undefined</button>
        <button data-f="queued" aria-pressed="false">queued</button>
      </div>
      <ul class="ids" id="idlist"></ul>
    </section>
    <section class="pane" id="paneMain"></section>
    <section class="pane" id="paneEdit">
      <h2>Rename or merge</h2>
      <div class="editor">
        <label for="from">Current</label>
        <input id="from" disabled>
        <label for="to">New</label>
        <input id="to" placeholder="select an identifier" autocomplete="off" spellcheck="false" disabled>
        <div class="note" id="valid"></div>
        <div class="row">
          <button class="btn" id="queue" disabled>Add to queue</button>
          <button class="btn ghost" id="next" disabled>Add &amp; next</button>
        </div>
      </div>
      <h2>Queued changes (<span id="qn">0</span>)</h2>
      <table class="queue" id="qtable"></table>
      <div class="row" style="padding:12px 16px 0">
        <button class="btn" id="review" disabled>Review changes</button>
        <button class="btn ghost" id="clear" disabled>Empty queue</button>
      </div>
      <div class="bulk">
        <h2 style="padding-left:0">Pattern rename</h2>
        <input id="rxFind" placeholder="find (regular expression)" autocomplete="off" spellcheck="false">
        <input id="rxRepl" placeholder="replace with (use $1 for groups)" autocomplete="off" spellcheck="false">
        <div class="row">
          <button class="btn ghost" id="rxRun">Queue every match</button>
        </div>
        <div class="note" id="rxNote"></div>
      </div>
    </section>
  </main>
</div>
<script>
const $ = s => document.querySelector(s);
let DATA = null, sel = null, filter = "all", view = "list";
let stFile = null, stBlocks = [], stOpen = null, stFind = "";
const DEFAULT_ELEMS = "__DEFAULT_ELEMS__";
const changes = new Map();   // key -> {kind:"rename"|"assign"|"split"|"join", ...}

const esc = s => String(s == null ? "" : s).replace(/[&<>"]/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));
const NCNAME = /^[A-Za-z_][\w.\-]*$/;
const toast = m => { const t = document.createElement("div"); t.className = "toast"; t.textContent = m;
  document.body.appendChild(t); setTimeout(() => t.remove(), 3600); };

async function api(path, body) {
  const r = await fetch(path, body ? {method:"POST", headers:{"Content-Type":"application/json"},
    body: JSON.stringify(body)} : undefined);
  if (!r.ok) { toast("Request failed: " + r.status); throw new Error(r.status); }
  return r.json();
}

const renameMap = () => Object.fromEntries([...changes.values()]
  .filter(c => c.kind === "rename").map(c => [c.from, c.to]));
const opList = () => [...changes.values()].filter(c => c.kind !== "rename");

async function load() {
  DATA = await api("/api/scan");
  $("#root").textContent = DATA.root;
  $("#root").title = DATA.root;
  const bad = DATA.files.filter(f => f.error).length;
  $("#tally").textContent = DATA.files.length + " files · " + DATA.groups.length + " identifiers"
    + (bad ? " · " + bad + " unreadable" : "");
  if (sel && !DATA.groups.some(g => g.id === sel)) sel = null;
  const names = DATA.files.filter(f => !f.error).map(f => f.label);
  if (!names.includes(stFile)) stFile = names[0] || null;
  if (view === "struct") await loadStructure(); else render();
}

/* ---------- identifier list ---------- */
function visible() {
  const q = $("#q").value.trim().toLowerCase();
  return DATA.groups.filter(g => {
    if (q && !g.id.toLowerCase().includes(q)) return false;
    if (filter === "partial") return g.partial;
    if (filter === "dup") return g.duplicated;
    if (filter === "dangling") return g.dangling;
    if (filter === "queued") return changes.has("r:" + g.id);
    return true;
  });
}

function renderList() {
  $("#idlist").innerHTML = visible().map(g => {
    const flag = g.duplicated ? "‡" : g.dangling ? "†" : g.partial ? "·" : "";
    return `<li class="${g.id === sel ? "on" : ""} ${changes.has("r:" + g.id) ? "queued" : ""}" data-id="${esc(g.id)}">
      <button><span class="name">${esc(g.id)}</span>
      <span class="flag">${flag}</span>
      <span class="n">${g.files.length}/${DATA.files.length}</span></button></li>`;
  }).join("") || `<li><div class="empty">Nothing matches.</div></li>`;
}

/* ---------- middle pane ---------- */
function renderMain() {
  const pane = $("#paneMain");
  if (view === "matrix") return renderMatrix(pane);
  if (view === "struct") return renderStructure(pane);
  const g = DATA.groups.find(x => x.id === sel);
  if (!g) { pane.innerHTML = `<div class="empty">Pick an identifier on the left to see every place it occurs.</div>`; return; }
  const defs = g.defs.map(d => `<div class="witness">
      <span class="file">${esc(d.file)}</span>
      <span class="where"> · line ${d.line} · &lt;${esc(d.element)}&gt;</span>
      <div class="ctx">${esc(d.context)}</div></div>`).join("");
  const refs = g.refs.length ? `<div class="reflist">Pointed at from ${g.refs.length} place${g.refs.length > 1 ? "s" : ""}: `
      + g.refs.slice(0, 40).map(r => `<code>${esc(r.file)}:${r.line} @${esc(r.attr)}</code>`).join(", ")
      + (g.refs.length > 40 ? " …" : "") + ` — these follow any rename.</div>` : "";
  const missing = DATA.files.filter(f => !f.error && !g.files.includes(f.label)).map(f => f.label);
  const gap = missing.length ? `<div class="alarm">Absent from ${missing.length} file${missing.length > 1 ? "s" : ""}: `
      + missing.map(esc).join(", ") + `</div>` : "";
  const dup = g.duplicated ? `<div class="alarm">This identifier occurs more than once inside a single file, which is invalid XML. Joining the two passages in the Structure view is usually the fix.</div>` : "";
  pane.innerHTML = `<div class="detail">
      <div class="idhead">${esc(g.id)}</div>
      <div class="sub">${g.nDefs} definition${g.nDefs === 1 ? "" : "s"} across ${g.files.length} file${g.files.length === 1 ? "" : "s"}</div>
      ${dup}${gap}${defs || `<div class="empty">No <code>@xml:id</code> defines this; it only appears in pointers.</div>`}${refs}</div>`;
}

function renderMatrix(pane) {
  const files = DATA.files.filter(f => !f.error);
  const rows = visible().slice(0, 600);
  const head = files.map(f => `<th title="${esc(f.label)}">${esc(f.label)}</th>`).join("");
  const body = rows.map(g => {
    const cells = files.map(f => {
      const n = g.defs.filter(d => d.file === f.label).length;
      if (n > 1) return `<td class="dup" title="${n} times — duplicate">${n}</td>`;
      if (n === 1) return `<td>✓</td>`;
      if (g.refs.some(r => r.file === f.label)) return `<td class="ref" title="pointer only">◦</td>`;
      return `<td class="miss">·</td>`;
    }).join("");
    return `<tr class="${g.id === sel ? "on" : ""}" data-id="${esc(g.id)}"><th>${esc(g.id)}</th>${cells}</tr>`;
  }).join("");
  pane.innerHTML = `<div class="matrixwrap">
    <div class="legend"><code>✓</code> defined here · <code>◦</code> only pointed at · <code>·</code> absent ·
      <code class="dup">2</code> repeated in one file. Click a row to load it into the rename box.</div>
    <table class="matrix"><thead><tr><th></th>${head}</tr></thead><tbody>${body}</tbody></table></div>`;
}

/* ---------- structure view ---------- */
async function loadStructure() {
  if (!stFile) { stBlocks = []; render(); return; }
  const r = await api("/api/outline?file=" + encodeURIComponent(stFile)
    + "&names=" + encodeURIComponent($("#stNames") ? $("#stNames").value : "")
    + (($("#stBare") && $("#stBare").checked) ? "&bare=1" : ""));
  stBlocks = r.blocks;
  if (r.error) toast(r.error);
  render();
}

function opKey(kind, file, at) { return "o:" + kind + ":" + file + ":" + at; }

function renderStructure(pane) {
  const files = DATA.files.filter(f => !f.error);
  const names = $("#stNames") ? $("#stNames").value : DEFAULT_ELEMS;
  const bare = $("#stBare") ? $("#stBare").checked : false;
  const bar = `<div class="stbar">
    <select id="stFile">${files.map(f => `<option ${f.label === stFile ? "selected" : ""}>${esc(f.label)}</option>`).join("")}</select>
    <input type="text" id="stNames" value="${esc(names)}" title="element names to list even when they carry no xml:id" style="width:26ch">
    <label><input type="checkbox" id="stBare" ${bare ? "checked" : ""}> only without an xml:id</label>
    <input type="text" class="grow" id="stFind" value="${esc(stFind)}" placeholder="find in this file…">
  </div>`;
  pane.innerHTML = bar + `<div class="blocks"></div>`;
  renderBlocks();
}

function renderBlocks() {
  const host = document.querySelector(".blocks");
  if (!host) return;
  const find = stFind.trim().toLowerCase();
  const shown = stBlocks.filter(b => !find
    || (b.id || "").toLowerCase().includes(find) || b.preview.toLowerCase().includes(find));
  host.innerHTML = shown.slice(0, 600).map(b => {
    const k = ["assign", "split", "join"].map(x => opKey(x, b.file, b.elem)).filter(x => changes.has(x));
    const acts = [];
    if (!b.id) acts.push(`<button data-act="assign">Give it an xml:id</button>`);
    if (!b.empty) acts.push(`<button data-act="split">Divide…</button>`);
    if (b.joinable) acts.push(`<button data-act="join">Join with next…</button>`);
    return `<article class="blk" data-at="${b.elem}" data-indent="${Math.min(b.depth, 3)}">
      <div class="bhead">
        <span class="ln">${b.line}</span>
        <span class="gi">&lt;${esc(b.name)}&gt;</span>
        ${b.id ? `<span class="idchip">${esc(b.id)}</span>` : `<span class="idchip none">no xml:id</span>`}
        ${k.length ? `<span class="idchip none">queued</span>` : ""}
        <span class="acts">${acts.join("")}</span>
      </div>
      <div class="prev">${esc(b.preview)}</div>
      <div class="work" id="work-${b.elem}" hidden></div>
    </article>`;
  }).join("") || `<div class="empty">No elements to show. Widen the element list, or clear the filter.</div>`;
  if (shown.length > 600) host.insertAdjacentHTML("beforeend",
    `<div class="empty">Showing the first 600 of ${shown.length}. Narrow it with the find box.</div>`);
  if (stOpen) openWork(stOpen.at, stOpen.act);
}

async function openWork(at, act) {
  const host = $("#work-" + at);
  if (!host) { stOpen = null; return; }
  stOpen = {at, act};
  host.hidden = false;
  host.innerHTML = `<div class="lede">Reading the passage…</div>`;
  const d = await api("/api/element?file=" + encodeURIComponent(stFile) + "&at=" + at);
  if (d.error) { host.innerHTML = `<div class="warn">${esc(d.error)}</div>`; return; }
  if (act === "assign") host.innerHTML = assignForm(d);
  if (act === "split") host.innerHTML = splitForm(d);
  if (act === "join") host.innerHTML = joinForm(d);
  host.dataset.at = at;
}

function assignForm(d) {
  return `<div class="lede">Give this &lt;${esc(d.name)}&gt; an identifier of its own. Nothing else in the passage changes.</div>
    <div class="field"><input type="text" data-role="id" placeholder="new xml:id" spellcheck="false">
      <button class="btn" data-do="assign">Queue it</button>
      <button class="btn ghost" data-do="close">Cancel</button></div>
    <div class="warn" data-role="msg"></div>`;
}

function splitForm(d) {
  const toks = d.parts.map((p, i) => {
    const gap = i ? `<button class="gap" data-cut="${p.at}" aria-pressed="false" title="divide here"></button>` : "";
    const body = p.kind === "node"
      ? `<span class="node" title="${esc(p.text)}">&lt;${esc(p.name)}&gt;</span>`
      : `<span class="tok">${esc(p.text)}</span>`;
    return gap + body + " ";
  }).join("");
  const twin = [...changes.values()].find(c => c.kind === "split" && c.of && c.of === d.id);
  const suggest = twin ? twin.id : (d.id ? d.id + ".2" : "");
  return `<div class="lede">Click a daṇḍa to place the division. Everything after it moves into a second
      &lt;${esc(d.name)}&gt;, which needs its own identifier. Only positions between whole words and whole
      child elements are offered, so the markup cannot break.</div>
    ${twin ? `<div class="lede">${esc(twin.file)} is already queued to divide ${esc(d.id)} at this identifier,
      so the same name is offered here — that is how one division is carried across the witnesses.</div>` : ""}
    <div class="ruler">${toks}</div>
    <div class="field"><input type="text" data-role="id" value="${esc(suggest)}" placeholder="xml:id for the second half" spellcheck="false">
      ${Object.keys(d.attrs).length ? `<label><input type="checkbox" data-role="copy" checked> copy ${Object.keys(d.attrs).map(esc).join(", ")}</label>` : ""}
      <button class="btn" data-do="split">Queue it</button>
      <button class="btn ghost" data-do="close">Cancel</button></div>
    <div class="warn" data-role="msg"></div>`;
}

function joinForm(d) {
  const s = d.sibling;
  const lost = Object.keys(s.attrs);
  return `<input type="hidden" data-role="second" value="${esc(s.id || "")}">
    <div class="lede">Fold the next &lt;${esc(d.name)}&gt; (line ${s.line}) into this one, so the two
      become a single passage.</div>
    <div class="witness"><span class="where">second passage · ${s.id ? esc(s.id) : "no xml:id"}</span>
      <div class="ctx">${esc(s.preview)}</div></div>
    <div class="field">
      <label><input type="radio" name="keep-${d.at}" data-role="keep" value="first" checked> keep ${d.id ? esc(d.id) : "the first (unnamed)"}</label>
      <label><input type="radio" name="keep-${d.at}" data-role="keep" value="second"> keep ${s.id ? esc(s.id) : "the second (unnamed)"}</label>
    </div>
    <div class="field"><label><input type="checkbox" data-role="anchor" checked>
      leave an &lt;anchor&gt; carrying the retired identifier at the seam</label></div>
    <div class="field"><button class="btn" data-do="join">Queue it</button>
      <button class="btn ghost" data-do="close">Cancel</button></div>
    ${lost.length ? `<div class="warn">The second element's ${lost.map(esc).join(", ")} will be dropped.</div>` : ""}
    <div class="warn" data-role="msg"></div>`;
}

/* ---------- rename box ---------- */
function validate() {
  const from = $("#from").value, to = $("#to").value.trim(), note = $("#valid");
  const set = (cls, t, ok) => { note.className = "note" + cls; note.textContent = t;
    $("#queue").disabled = !ok; $("#next").disabled = !ok; };
  if (!from || !to) return set("", "", false);
  if (to === from) return set("", "Same as the current value.", false);
  if (!NCNAME.test(to))
    return set("", "An xml:id must start with a letter or underscore and contain only letters, digits, . - _", false);
  if ([...changes.values()].some(c => c.kind === "rename" && c.from !== from && c.to === to))
    return set("", "Another queued rename already produces this value.", false);
  const g = DATA.groups.find(x => x.id === from);
  const target = DATA.groups.find(x => x.id === to);
  const cost = g ? g.nDefs + " definition(s) and " + g.nRefs + " pointer(s)" : "";
  if (target && !changes.has("r:" + to)) {
    const clash = g && target.files.some(f => g.files.includes(f));
    return set("", "Merges " + cost + " into an existing identifier."
      + (clash ? " Both occur in the same file, so this would produce a duplicate — join the passages in the Structure view instead." : ""), true);
  }
  return set(" ok", "Will change " + cost + ".", true);
}

function select(id) {
  sel = id;
  $("#from").value = id;
  $("#to").disabled = false;
  $("#to").value = (changes.get("r:" + id) || {}).to || id;
  validate();
  render();
  $("#to").focus();
  $("#to").setSelectionRange($("#to").value.length, $("#to").value.length);
}

function label(c) {
  if (c.kind === "rename") return esc(c.from) + " <b>→</b> " + esc(c.to);
  if (c.kind === "assign") return esc(c.file) + " &lt;" + esc(c.name) + "&gt; line " + c.line + " <b>→</b> " + esc(c.id);
  if (c.kind === "split") return esc(c.file) + " " + esc(c.of || c.name) + " <b>÷</b> " + esc(c.id);
  if (c.kind === "join") return esc(c.file) + " " + esc(c.first || "—") + " <b>+</b> " + esc(c.second || "—")
    + " → " + esc(c.keep === "second" ? c.second : c.first);
  return "";
}

function renderQueue() {
  $("#qn").textContent = changes.size;
  $("#qtable").innerHTML = [...changes].map(([k, c]) =>
    `<tr><td class="what">${c.kind === "rename" ? (DATA.groups.some(g => g.id === c.to) ? "merge" : "rename") : c.kind}</td>
     <td class="lbl">${label(c)}</td>
     <td class="kill"><button data-drop="${esc(k)}" title="remove">×</button></td></tr>`).join("");
  $("#review").disabled = changes.size === 0;
  $("#clear").disabled = changes.size === 0;
}

function render() {
  $("#main").classList.toggle("wide", view === "struct");
  $("#paneList").hidden = view === "struct";
  if (view !== "struct") renderList();
  renderMain();
  renderQueue();
}

/* ---------- review & save ---------- */
async function review() {
  const res = await api("/api/plan", {renames: renameMap(), ops: opList()});
  const bad = res.files.filter(f => f.error).map(f =>
    `<div class="alarm"><b>${esc(f.label)}</b> — ${esc(f.error)}</div>`);
  res.files.forEach(f => { if (f.duplicates && f.duplicates.length)
    bad.push(`<div class="alarm"><b>${esc(f.label)}</b> would end up with repeated identifiers: `
      + f.duplicates.map(esc).join(", ") + `</div>`); });
  const body = res.files.filter(f => !f.error).map(f =>
      `<div class="dfile">${esc(f.label)} — ${f.hits} change${f.hits === 1 ? "" : "s"}</div>`
      + f.diff.map(d => `<div class="dl ${d.t === "-" ? "minus" : d.t === "+" ? "plus" : d.t === "@" ? "at" : ""}">${esc(d.t === " " ? "  " + d.s : d.t + " " + d.s)}</div>`).join("")
    ).join("") || `<div class="empty">These changes match nothing in the files.</div>`;
  const blocked = res.files.some(f => f.error);
  const sheet = document.createElement("div");
  sheet.className = "sheet";
  sheet.innerHTML = `<div class="card"><h3>${res.total} change${res.total === 1 ? "" : "s"} in ${res.files.length} file${res.files.length === 1 ? "" : "s"}</h3>
    <div class="body">${bad.join("")}${body}</div>
    <div class="foot"><button class="btn ghost" data-x>Back</button>
    <button class="btn ${bad.length ? "warn" : ""}" data-go ${res.total && !blocked ? "" : "disabled"}>Save to disk</button></div></div>`;
  document.body.appendChild(sheet);
  sheet.addEventListener("click", async e => {
    if (e.target.hasAttribute("data-x") || e.target === sheet) sheet.remove();
    if (e.target.hasAttribute("data-go")) {
      e.target.disabled = true;
      const r = await api("/api/apply", {renames: renameMap(), ops: opList()});
      sheet.remove();
      if (r.errors && r.errors.length) { toast("Nothing was written: " + r.errors[0].error); return; }
      changes.clear(); stOpen = null;
      await load();
      toast("Saved " + r.files.length + " files. Backup: " + r.stamp);
    }
  });
}

/* ---------- events ---------- */
$("#idlist").addEventListener("click", e => {
  const li = e.target.closest("li[data-id]"); if (li) select(li.dataset.id);
});
$("#paneMain").addEventListener("click", async e => {
  const tr = e.target.closest("tr[data-id]");
  if (tr) return select(tr.dataset.id);
  const act = e.target.closest("button[data-act]");
  if (act) { const blk = act.closest(".blk"); return openWork(+blk.dataset.at, act.dataset.act); }
  const gap = e.target.closest("button.gap");
  if (gap) {
    gap.closest(".ruler").querySelectorAll(".gap").forEach(g => g.setAttribute("aria-pressed", g === gap));
    return;
  }
  const go = e.target.closest("button[data-do]");
  if (go) return commit(go);
});
$("#paneMain").addEventListener("change", e => {
  if (e.target.id === "stFile") { stFile = e.target.value; stOpen = null; loadStructure(); }
  if (e.target.id === "stNames" || e.target.id === "stBare") { stOpen = null; loadStructure(); }
});
$("#paneMain").addEventListener("input", e => {
  if (e.target.id === "stFind") { stFind = e.target.value; renderBlocks(); }
});

function commit(btn) {
  const host = btn.closest(".work"), at = +host.dataset.at;
  const msg = host.querySelector('[data-role="msg"]');
  const blk = stBlocks.find(b => b.elem === at);
  const kind = btn.dataset.do;
  if (kind === "close") { host.hidden = true; stOpen = null; return; }
  const idBox = host.querySelector('[data-role="id"]');
  const wanted = idBox ? idBox.value.trim() : "";
  if (kind !== "join") {
    if (!NCNAME.test(wanted)) { msg.textContent = "That is not a usable xml:id."; return; }
    if (DATA.groups.some(g => g.id === wanted)) { msg.textContent = "That identifier is already in use."; return; }
  }
  const base = {file: stFile, elem: at, check: blk.check, name: blk.name, line: blk.line};
  if (kind === "assign") changes.set(opKey("assign", stFile, at), {...base, kind: "assign", id: wanted});
  if (kind === "split") {
    const gap = host.querySelector('.gap[aria-pressed="true"]');
    if (!gap) { msg.textContent = "Click a daṇḍa first to say where the passage divides."; return; }
    const copy = host.querySelector('[data-role="copy"]');
    changes.set(opKey("split", stFile, at), {...base, kind: "split", cut: +gap.dataset.cut,
      id: wanted, copyAttrs: !!(copy && copy.checked), of: blk.id || ("<" + blk.name + "> line " + blk.line)});
  }
  if (kind === "join") {
    const keep = host.querySelector('[data-role="keep"]:checked').value;
    const anchor = host.querySelector('[data-role="anchor"]').checked;
    const second = host.querySelector('[data-role="second"]').value || "unnamed";
    changes.set(opKey("join", stFile, at), {...base, kind: "join", keep, anchor,
      first: blk.id || ("<" + blk.name + "> line " + blk.line), second});
  }
  host.hidden = true; stOpen = null;
  render();
}

$("#qtable").addEventListener("click", e => {
  const b = e.target.closest("button[data-drop]");
  if (b) { changes.delete(b.dataset.drop); render(); validate(); }
});
$("#q").addEventListener("input", renderList);
document.querySelectorAll(".filters button").forEach(b => b.addEventListener("click", () => {
  filter = b.dataset.f;
  document.querySelectorAll(".filters button").forEach(o => o.setAttribute("aria-pressed", o === b));
  renderList();
}));
const setView = v => {
  view = v;
  $("#vList").setAttribute("aria-pressed", v === "list");
  $("#vMatrix").setAttribute("aria-pressed", v === "matrix");
  $("#vStruct").setAttribute("aria-pressed", v === "struct");
  if (v === "struct" && !stBlocks.length) loadStructure(); else render();
};
$("#vList").addEventListener("click", () => setView("list"));
$("#vMatrix").addEventListener("click", () => setView("matrix"));
$("#vStruct").addEventListener("click", () => setView("struct"));
$("#to").addEventListener("input", validate);
$("#to").addEventListener("keydown", e => { if (e.key === "Enter" && !$("#queue").disabled) addRename(false); });
$("#queue").addEventListener("click", () => addRename(false));
$("#next").addEventListener("click", () => addRename(true));
function addRename(advance) {
  const from = $("#from").value;
  changes.set("r:" + from, {kind: "rename", from, to: $("#to").value.trim()});
  const list = visible(), i = list.findIndex(g => g.id === sel);
  render();
  if (advance && i > -1 && list[i + 1]) select(list[i + 1].id);
  else { $("#to").value = ""; validate(); }
}
$("#clear").addEventListener("click", () => { changes.clear(); stOpen = null; render(); validate(); });
$("#review").addEventListener("click", review);
$("#rescan").addEventListener("click", () => { stBlocks = []; stOpen = null; load(); });
$("#rxRun").addEventListener("click", () => {
  const note = $("#rxNote");
  let rx;
  try { rx = new RegExp($("#rxFind").value); }
  catch (err) { note.textContent = "That is not a valid regular expression."; return; }
  const repl = $("#rxRepl").value;
  let n = 0;
  DATA.groups.forEach(g => {
    if (!rx.test(g.id)) return;
    const out = g.id.replace(rx, repl);
    if (out !== g.id && NCNAME.test(out)) { changes.set("r:" + g.id, {kind: "rename", from: g.id, to: out}); n++; }
  });
  note.textContent = n ? "Queued " + n + " renames — review before saving." : "No identifier matches.";
  render();
});
$("#undo").addEventListener("click", async () => {
  const list = await api("/api/backups");
  if (!list.backups.length) { toast("No backups yet."); return; }
  const stamp = prompt("Restore which backup?\n\n" + list.backups.join("\n"), list.backups[0]);
  if (!stamp) return;
  const r = await api("/api/restore", {stamp});
  changes.clear(); stBlocks = []; stOpen = null;
  await load();
  toast("Restored " + r.restored.length + " files from " + stamp);
});
document.addEventListener("keydown", e => {
  if (e.key === "Escape") document.querySelector(".sheet")?.remove();
});
load();
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------
# server
# --------------------------------------------------------------------------

class State:
    def __init__(self, paths, root, exts=()):
        self.paths = paths
        self.root = root
        self.exts = tuple(exts)
        self.files = collect_files(paths, self.exts)

    def resolve(self, rel):
        """Absolute path for a file label, or None if it is not ours."""
        for p in self.files:
            if os.path.relpath(p, self.root) == rel:
                return p
        return None


class Handler(BaseHTTPRequestHandler):
    state = None

    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="application/json; charset=utf-8"):
        data = body if isinstance(body, bytes) else body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def _json(self, obj, code=200):
        self._send(code, json.dumps(obj, ensure_ascii=False))

    def do_GET(self):
        url = urlparse(self.path)
        query = parse_qs(url.query)
        one = lambda k, d="": (query.get(k) or [d])[0]
        st = self.state

        if url.path in ("/", "/index.html"):
            page = PAGE.replace("__DEFAULT_ELEMS__", DEFAULT_STRUCTURE_ELEMENTS)
            return self._send(200, page, "text/html; charset=utf-8")

        if url.path == "/api/scan":
            st.files = collect_files(st.paths, st.exts)
            files, groups = scan(st.files, st.root)
            return self._json({
                "root": st.root,
                "files": [{k: v for k, v in f.items() if k != "path"} for f in files],
                "groups": groups})

        if url.path == "/api/outline":
            rel = one("file")
            path = st.resolve(rel)
            if not path:
                return self._json({"error": "unknown file", "blocks": []}, 404)
            names = (one("names") or DEFAULT_STRUCTURE_ELEMENTS).split()
            try:
                blocks = outline(read_text(path), rel, names, bool(one("bare")))
            except (OSError, UnicodeDecodeError, ValueError) as exc:
                return self._json({"error": str(exc), "blocks": []})
            return self._json({"blocks": blocks})

        if url.path == "/api/element":
            rel = one("file")
            path = st.resolve(rel)
            if not path:
                return self._json({"error": "unknown file"}, 404)
            try:
                return self._json(element_detail(read_text(path), rel, int(one("at", "-1"))))
            except (OSError, UnicodeDecodeError, ValueError) as exc:
                return self._json({"error": str(exc)})

        if url.path == "/api/backups":
            return self._json({"backups": list_backups(st.root)})

        return self._json({"error": "not found"}, 404)

    def do_POST(self):
        url = urlparse(self.path)
        st = self.state
        length = int(self.headers.get("Content-Length", 0))
        try:
            payload = json.loads(self.rfile.read(length) or b"{}")
        except json.JSONDecodeError:
            return self._json({"error": "bad json"}, 400)

        mapping = {k: v for k, v in (payload.get("renames") or {}).items()
                   if isinstance(k, str) and isinstance(v, str) and NCNAME_RE.match(v)}
        ops = []
        for op in payload.get("ops") or []:
            if not isinstance(op, dict) or op.get("kind") not in ("assign", "split", "join"):
                continue
            if op.get("kind") in ("assign", "split") and not NCNAME_RE.match(op.get("id") or ""):
                continue
            ops.append(op)

        if url.path == "/api/plan":
            files, total = plan(st.files, st.root, mapping, ops)
            return self._json({"total": total, "files": files})

        if url.path == "/api/apply":
            if not mapping and not ops:
                return self._json({"error": "nothing to do"}, 400)
            return self._json(apply_changes(st.files, st.root, mapping, ops))

        if url.path == "/api/restore":
            stamp = payload.get("stamp", "")
            if not re.match(r"^[\w\-]+$", stamp):
                return self._json({"error": "bad stamp"}, 400)
            try:
                return self._json({"restored": restore(st.root, stamp)})
            except ValueError as exc:
                return self._json({"error": str(exc)}, 404)

        return self._json({"error": "not found"}, 404)


def main(argv=None):
    ap = argparse.ArgumentParser(description="Parallel xml:id work across TEI files.")
    ap.add_argument("paths", nargs="+",
                    help="a folder of XML/TEI files, or individual files. In a folder, "
                         ".xml/.tei/.xhtml are always read and .txt files are read if they "
                         "contain markup; a .txt named on the command line is always read.")
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--ext", nargs="+", default=[], metavar="EXT",
                    help="further extensions to treat as XML, e.g. --ext .inc .frag")
    ap.add_argument("--no-browser", action="store_true")
    args = ap.parse_args(argv)

    paths = [os.path.abspath(p) for p in args.paths]
    for p in paths:
        if not os.path.exists(p):
            sys.exit("No such path: " + p)
    root = paths[0] if os.path.isdir(paths[0]) else os.path.dirname(paths[0])

    exts = tuple(e if e.startswith(".") else "." + e for e in (x.lower() for x in args.ext))
    state = State(paths, root, exts)
    if not state.files:
        sys.exit("No XML found under " + root
                 + " (looked for " + ", ".join(XML_EXTS + SNIFF_EXTS + exts) + ")")

    Handler.state = state
    server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    url = "http://127.0.0.1:%d/" % args.port
    print("tei-id-sync — %d files under %s" % (len(state.files), root))
    print("Open %s  (Ctrl-C to stop)" % url)
    if not args.no_browser:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopped.")


if __name__ == "__main__":
    main()
