#!/usr/bin/env python3
"""
tei-id-sync — parallel xml:id editing across a set of TEI/XML files.

Usage:
    python3 tei_id_sync.py /path/to/folder
    python3 tei_id_sync.py file1.xml file2.txt file3.xml
    python3 tei_id_sync.py /path/to/folder --port 8765 --no-browser

Opens a local page in your browser. Nothing leaves your machine; no
dependencies beyond the Python standard library (3.8+).

Design notes
------------
* Extension is not taken as a guarantee of content: .xml/.tei/.xhtml are
  always read, .txt files in a folder are read when they contain markup,
  and any file named directly on the command line is read regardless.
* Edits are made on the raw text of each file with targeted substitutions.
  The files are never parsed and re-serialised, so whitespace, comments,
  entity references, attribute order and line endings survive untouched.
* A rename set is applied in ONE pass, so swaps (a -> b, b -> a) and
  cascades (a -> b, b -> c) behave as you would expect.
* Pointing attributes (@corresp, @target, @ref ...) that contain "#id"
  are updated together with the @xml:id they point at.
* Every save writes a timestamped backup of each touched file, plus a
  JSON log of the renames.
"""

import argparse
import html
import json
import os
import re
import shutil
import sys
import threading
import time
import webbrowser
from bisect import bisect_right
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse

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
TAG_NAME_RE = re.compile(r"<\s*([\w:.-]+)")
TAGGISH_RE = re.compile(r"<[A-Za-z_][\w:.-]*[\s/>]")
TAG_STRIP_RE = re.compile(r"<[^>]*>")
WS_RE = re.compile(r"\s+")
NCNAME_RE = re.compile(r"^[A-Za-z_][\w.\-]*$")
MASK_RE = re.compile(r"<!--.*?-->|<!\[CDATA\[.*?\]\]>", re.S)


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


def context_at(text, pos, width=260, out=150):
    chunk = text[pos: pos + width]
    chunk = TAG_STRIP_RE.sub(" ", chunk)
    chunk = html.unescape(chunk)
    chunk = WS_RE.sub(" ", chunk).strip()
    return chunk[:out]


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
# rewriting
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


def line_diff(old, new):
    """Changed lines only, paired by line number (rewrite never adds lines)."""
    o, n = old.split("\n"), new.split("\n")
    out = []
    for i, (a, b) in enumerate(zip(o, n), start=1):
        if a != b:
            out.append({"line": i, "old": a.strip()[:400], "new": b.strip()[:400]})
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


def plan(files, root, mapping):
    """Dry run: per-file diffs plus warnings."""
    result, total = [], 0
    for path in files:
        try:
            text = read_text(path)
        except (OSError, UnicodeDecodeError):
            continue
        new, hits = rewrite(text, mapping)
        if not hits:
            continue
        total += hits
        result.append({
            "path": path,
            "label": os.path.relpath(path, root),
            "hits": hits,
            "diff": line_diff(text, new)[:400],
            "duplicates": duplicate_ids(new),
        })
    return result, total


def apply_changes(files, root, mapping):
    stamp = datetime.now().strftime("%Y-%m-%d_%H%M%S")
    bdir = os.path.join(root, BACKUP_DIR, stamp)
    touched, dupes = [], {}
    for path in files:
        try:
            text = read_text(path)
        except (OSError, UnicodeDecodeError):
            continue
        new, hits = rewrite(text, mapping)
        if not hits:
            continue
        rel = os.path.relpath(path, root)
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
        with open(os.path.join(bdir, "renames.json"), "w", encoding="utf-8") as fh:
            json.dump({"when": stamp, "renames": mapping,
                       "files": [t["label"] for t in touched]}, fh,
                      ensure_ascii=False, indent=2)
    return {"stamp": stamp, "backup": bdir, "files": touched, "duplicates": dupes}


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
            if n == "renames.json":
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

/* ---- frame ---- */
#app{display:flex;flex-direction:column;height:100vh}
header{display:flex;align-items:baseline;gap:18px;flex-wrap:wrap;
  padding:10px 20px;background:var(--paper);border-bottom:1px solid var(--rule)}
header .mark{font-size:20px;letter-spacing:.02em}
header .mark em{font-style:italic;color:var(--rubric)}
header .path{font-family:var(--mono);font-size:12px;color:var(--ink-soft);
  overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:38ch}
header .tally{font-size:14px;color:var(--ink-soft)}
header .spacer{flex:1}
.views{display:flex;border:1px solid var(--rule);border-radius:2px;overflow:hidden}
.views button{background:var(--paper);border:0;padding:5px 14px;cursor:pointer;font-size:15px}
.views button+button{border-left:1px solid var(--rule)}
.views button[aria-pressed="true"]{background:var(--indigo);color:#fff}

main{flex:1;display:grid;grid-template-columns:270px minmax(0,1fr) 340px;min-height:0}
.pane{min-height:0;overflow:auto;background:var(--paper)}
.pane+.pane{border-left:1px solid var(--rule)}
.pane h2{font-size:13px;letter-spacing:.14em;text-transform:uppercase;color:var(--ink-soft);
  padding:12px 16px 6px;font-family:var(--mono);font-weight:400}

/* ---- id list ---- */
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

/* ---- occurrences ---- */
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

/* ---- matrix ---- */
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

/* ---- queue ---- */
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
table.queue{width:100%;border-collapse:collapse;font-family:var(--mono);font-size:12px}
table.queue td{border-top:1px solid var(--rule-soft);padding:4px 6px;vertical-align:top;overflow-wrap:anywhere}
table.queue td.arrow{color:var(--rubric);width:1.4em;text-align:center}
table.queue td.kill{width:1.6em;text-align:center}
table.queue button{background:none;border:0;color:var(--ink-soft);cursor:pointer;font-size:14px;padding:0}
table.queue button:hover{color:var(--rubric)}
.bulk{padding:12px 16px;border-top:1px solid var(--rule)}
.bulk input{width:100%;margin-bottom:6px;padding:5px 8px;border:1px solid var(--rule);
  border-radius:2px;background:#fff;font-family:var(--mono);font-size:13px}

/* ---- sheet ---- */
.sheet{position:fixed;inset:0;background:rgba(30,27,22,.45);display:flex;
  align-items:center;justify-content:center;padding:26px;z-index:10}
.sheet .card{background:var(--paper);border-radius:3px;max-width:960px;width:100%;
  max-height:100%;display:flex;flex-direction:column;box-shadow:0 18px 50px rgba(0,0,0,.3)}
.sheet .card>h3{padding:16px 22px;border-bottom:1px solid var(--rule);font-size:20px}
.sheet .body{overflow:auto;padding:8px 22px 22px}
.sheet .foot{padding:12px 22px;border-top:1px solid var(--rule);display:flex;gap:10px;justify-content:flex-end}
.dfile{font-family:var(--mono);font-size:13px;color:var(--indigo);margin:16px 0 4px}
.dline{display:grid;grid-template-columns:4.5em 1fr;gap:8px;font-family:var(--mono);
  font-size:12px;padding:2px 0;border-top:1px solid var(--rule-soft)}
.dline .no{color:var(--ink-soft);text-align:right}
.dline del{background:var(--rubric-soft);text-decoration:none;color:var(--rubric)}
.dline ins{background:var(--indigo-soft);text-decoration:none;color:var(--indigo)}
.alarm{background:var(--rubric-soft);border-left:3px solid var(--rubric);padding:9px 14px;margin:12px 0;font-size:15px}
.toast{position:fixed;bottom:18px;left:50%;transform:translateX(-50%);background:var(--ink);
  color:var(--paper);padding:9px 18px;border-radius:2px;font-size:15px;z-index:20}
@media (max-width:1100px){main{grid-template-columns:1fr}.pane+.pane{border-left:0;border-top:1px solid var(--rule)}}
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
    </span>
    <button class="btn ghost" id="rescan">Reload files</button>
    <button class="btn ghost" id="undo">Restore backup</button>
  </header>
  <main>
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
      <h2>Rename</h2>
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
      <h2>Queued renames (<span id="qn">0</span>)</h2>
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
const renames = new Map();

const esc = s => String(s).replace(/[&<>"]/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));
const toast = m => { const t = document.createElement("div"); t.className = "toast"; t.textContent = m;
  document.body.appendChild(t); setTimeout(() => t.remove(), 3200); };

async function api(path, body) {
  const r = await fetch(path, body ? {method:"POST", headers:{"Content-Type":"application/json"},
    body: JSON.stringify(body)} : undefined);
  if (!r.ok) { toast("Request failed: " + r.status); throw new Error(r.status); }
  return r.json();
}

async function load() {
  DATA = await api("/api/scan");
  $("#root").textContent = DATA.root;
  $("#root").title = DATA.root;
  const bad = DATA.files.filter(f => f.error).length;
  $("#tally").textContent = DATA.files.length + " files · " + DATA.groups.length + " identifiers"
    + (bad ? " · " + bad + " unreadable" : "");
  if (sel && !DATA.groups.some(g => g.id === sel)) sel = null;
  render();
}

/* ---------- id list ---------- */
function visible() {
  const q = $("#q").value.trim().toLowerCase();
  return DATA.groups.filter(g => {
    if (q && !g.id.toLowerCase().includes(q)) return false;
    if (filter === "partial") return g.partial;
    if (filter === "dup") return g.duplicated;
    if (filter === "dangling") return g.dangling;
    if (filter === "queued") return renames.has(g.id);
    return true;
  });
}

function renderList() {
  const ul = $("#idlist");
  ul.innerHTML = visible().map(g => {
    const flag = g.duplicated ? "‡" : g.dangling ? "†" : g.partial ? "·" : "";
    return `<li class="${g.id === sel ? "on" : ""} ${renames.has(g.id) ? "queued" : ""}" data-id="${esc(g.id)}">
      <button><span class="name">${esc(g.id)}</span>
      <span class="flag">${flag}</span>
      <span class="n">${g.files.length}/${DATA.files.length}</span></button></li>`;
  }).join("") || `<li><div class="empty">Nothing matches.</div></li>`;
}

/* ---------- middle pane ---------- */
function renderMain() {
  const pane = $("#paneMain");
  if (view === "matrix") return renderMatrix(pane);
  const g = DATA.groups.find(x => x.id === sel);
  if (!g) { pane.innerHTML = `<div class="empty">Pick an identifier on the left to see every place it occurs.</div>`; return; }
  const defs = g.defs.map(d => `<div class="witness">
      <span class="file">${esc(d.file)}</span>
      <span class="where"> · line ${d.line} · &lt;${esc(d.element)}&gt;</span>
      <div class="ctx">${esc(d.context)}</div></div>`).join("");
  const refs = g.refs.length ? `<div class="reflist">Pointed at from ${g.refs.length} place${g.refs.length > 1 ? "s" : ""}: `
      + g.refs.slice(0, 40).map(r => `<code>${esc(r.file)}:${r.line} @${esc(r.attr)}</code>`).join(", ")
      + (g.refs.length > 40 ? " …" : "") + ` — these will be renamed too.</div>` : "";
  const missing = DATA.files.filter(f => !f.error && !g.files.includes(f.label)).map(f => f.label);
  const gap = missing.length ? `<div class="alarm">Absent from ${missing.length} file${missing.length > 1 ? "s" : ""}: `
      + missing.map(esc).join(", ") + `</div>` : "";
  const dup = g.duplicated ? `<div class="alarm">This identifier occurs more than once inside a single file, which is invalid XML.</div>` : "";
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

/* ---------- rename box ---------- */
function validate() {
  const from = $("#from").value, to = $("#to").value.trim(), note = $("#valid");
  const ok = t => { note.className = "note ok"; note.textContent = t; $("#queue").disabled = false; $("#next").disabled = false; };
  const no = t => { note.className = "note"; note.textContent = t; $("#queue").disabled = true; $("#next").disabled = true; };
  if (!from) return no("");
  if (!to) return no("");
  if (to === from) return no("Same as the current value.");
  if (!/^[A-Za-z_][\w.\-]*$/.test(to))
    return no("An xml:id must start with a letter or underscore and contain only letters, digits, . - _");
  const taken = DATA.groups.some(g => g.id === to) && !renames.has(to);
  const claimed = [...renames.values()].includes(to);
  if (taken) return no("Already used by another passage. Rename that one too, or pick another value.");
  if (claimed) return no("Another queued rename already produces this value.");
  const g = DATA.groups.find(x => x.id === from);
  ok("Will change " + (g ? g.nDefs + " definition(s) and " + g.nRefs + " pointer(s)" : "") + ".");
}

function select(id) {
  sel = id;
  $("#from").value = id;
  $("#to").disabled = false;
  $("#to").value = renames.get(id) || id;
  validate();
  render();
  $("#to").focus();
  $("#to").setSelectionRange($("#to").value.length, $("#to").value.length);
}

function renderQueue() {
  $("#qn").textContent = renames.size;
  $("#qtable").innerHTML = [...renames].map(([a, b]) =>
    `<tr><td>${esc(a)}</td><td class="arrow">→</td><td>${esc(b)}</td>
     <td class="kill"><button data-drop="${esc(a)}" title="remove">×</button></td></tr>`).join("");
  $("#review").disabled = renames.size === 0;
  $("#clear").disabled = renames.size === 0;
}

function render() { renderList(); renderMain(); renderQueue(); }

/* ---------- review & save ---------- */
async function review() {
  const res = await api("/api/plan", {renames: Object.fromEntries(renames)});
  const warn = [];
  res.files.forEach(f => { if (f.duplicates.length)
    warn.push(`<div class="alarm"><b>${esc(f.label)}</b> would end up with repeated identifiers: `
      + f.duplicates.map(esc).join(", ") + `</div>`); });
  const body = res.files.map(f => `<div class="dfile">${esc(f.label)} — ${f.hits} attribute${f.hits === 1 ? "" : "s"}</div>`
      + f.diff.map(d => `<div class="dline"><span class="no">${d.line}</span><span><del>${esc(d.old)}</del><br><ins>${esc(d.new)}</ins></span></div>`).join("")
    ).join("") || `<div class="empty">These renames match nothing in the files.</div>`;
  const sheet = document.createElement("div");
  sheet.className = "sheet";
  sheet.innerHTML = `<div class="card"><h3>${res.total} attribute${res.total === 1 ? "" : "s"} in ${res.files.length} file${res.files.length === 1 ? "" : "s"}</h3>
    <div class="body">${warn.join("")}${body}</div>
    <div class="foot"><button class="btn ghost" data-x>Back</button>
    <button class="btn ${warn.length ? "warn" : ""}" data-go ${res.total ? "" : "disabled"}>Save to disk</button></div></div>`;
  document.body.appendChild(sheet);
  sheet.addEventListener("click", async e => {
    if (e.target.hasAttribute("data-x") || e.target === sheet) sheet.remove();
    if (e.target.hasAttribute("data-go")) {
      e.target.disabled = true;
      const r = await api("/api/apply", {renames: Object.fromEntries(renames)});
      sheet.remove(); renames.clear(); await load();
      toast("Saved " + r.files.length + " files. Backup: " + r.stamp);
    }
  });
}

/* ---------- events ---------- */
$("#idlist").addEventListener("click", e => {
  const li = e.target.closest("li[data-id]"); if (li) select(li.dataset.id);
});
$("#paneMain").addEventListener("click", e => {
  const tr = e.target.closest("tr[data-id]"); if (tr) select(tr.dataset.id);
});
$("#qtable").addEventListener("click", e => {
  const b = e.target.closest("button[data-drop]");
  if (b) { renames.delete(b.dataset.drop); render(); validate(); }
});
$("#q").addEventListener("input", renderList);
document.querySelectorAll(".filters button").forEach(b => b.addEventListener("click", () => {
  filter = b.dataset.f;
  document.querySelectorAll(".filters button").forEach(o => o.setAttribute("aria-pressed", o === b));
  renderList();
}));
$("#vList").addEventListener("click", () => setView("list"));
$("#vMatrix").addEventListener("click", () => setView("matrix"));
function setView(v) {
  view = v;
  $("#vList").setAttribute("aria-pressed", v === "list");
  $("#vMatrix").setAttribute("aria-pressed", v === "matrix");
  renderMain();
}
$("#to").addEventListener("input", validate);
$("#to").addEventListener("keydown", e => { if (e.key === "Enter" && !$("#queue").disabled) addQueued(false); });
$("#queue").addEventListener("click", () => addQueued(false));
$("#next").addEventListener("click", () => addQueued(true));
function addQueued(advance) {
  renames.set($("#from").value, $("#to").value.trim());
  const list = visible(), i = list.findIndex(g => g.id === sel);
  render();
  if (advance && i > -1 && list[i + 1]) select(list[i + 1].id);
  else { $("#to").value = ""; validate(); }
}
$("#clear").addEventListener("click", () => { renames.clear(); render(); validate(); });
$("#review").addEventListener("click", review);
$("#rescan").addEventListener("click", load);
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
    if (out !== g.id && /^[A-Za-z_][\w.\-]*$/.test(out)) { renames.set(g.id, out); n++; }
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

    def do_GET(self):
        path = urlparse(self.path).path
        st = self.state
        if path in ("/", "/index.html"):
            return self._send(200, PAGE, "text/html; charset=utf-8")
        if path == "/api/scan":
            st.files = collect_files(st.paths, st.exts)
            files, groups = scan(st.files, st.root)
            return self._send(200, json.dumps({
                "root": st.root,
                "files": [{k: v for k, v in f.items() if k != "path"} for f in files],
                "groups": groups}, ensure_ascii=False))
        if path == "/api/backups":
            return self._send(200, json.dumps({"backups": list_backups(st.root)}))
        return self._send(404, json.dumps({"error": "not found"}))

    def do_POST(self):
        path = urlparse(self.path).path
        st = self.state
        length = int(self.headers.get("Content-Length", 0))
        try:
            payload = json.loads(self.rfile.read(length) or b"{}")
        except json.JSONDecodeError:
            return self._send(400, json.dumps({"error": "bad json"}))
        mapping = {k: v for k, v in (payload.get("renames") or {}).items()
                   if isinstance(k, str) and isinstance(v, str) and NCNAME_RE.match(v)}
        if path == "/api/plan":
            files, total = plan(st.files, st.root, mapping)
            return self._send(200, json.dumps({
                "total": total,
                "files": [{k: v for k, v in f.items() if k != "path"} for f in files]},
                ensure_ascii=False))
        if path == "/api/apply":
            if not mapping:
                return self._send(400, json.dumps({"error": "nothing to do"}))
            result = apply_changes(st.files, st.root, mapping)
            return self._send(200, json.dumps(result, ensure_ascii=False))
        if path == "/api/restore":
            stamp = payload.get("stamp", "")
            if not re.match(r"^[\w\-]+$", stamp):
                return self._send(400, json.dumps({"error": "bad stamp"}))
            try:
                restored = restore(st.root, stamp)
            except ValueError as exc:
                return self._send(404, json.dumps({"error": str(exc)}))
            return self._send(200, json.dumps({"restored": restored}))
        return self._send(404, json.dumps({"error": "not found"}))


def main(argv=None):
    ap = argparse.ArgumentParser(description="Parallel xml:id editing across TEI files.")
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
