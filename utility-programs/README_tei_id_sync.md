# tei-id-sync

A small local tool for renaming `@xml:id` values in parallel across several
TEI/XML transcriptions of the same text (witnesses, editions, commentaries).

## Running it

```
python3 tei_id_sync.py /path/to/folder-of-xml
python3 tei_id_sync.py A.xml B.txt print-ed.xml
```

Extension is not taken as a guarantee of content. In a folder, `.xml`, `.tei`
and `.xhtml` are always read, and `.txt` files are read too whenever they
actually contain markup — so TEI kept under a `.txt` name is picked up, while
a plain `notes.txt` sitting in the same folder is left out of the corpus. A
file named directly on the command line is always read, whatever it is
called. For other extensions: `--ext .inc .frag`.

Python 3.8+; no libraries to install. It starts a server on 127.0.0.1 and
opens your browser. Nothing is sent anywhere. Stop it with Ctrl-C.

Options: `--port 8765`, `--no-browser`, `--ext .inc`.

## What you see

**Passages** — every distinct identifier in the corpus, with a badge showing
how many files define it. Select one and the middle pane lists each
occurrence: file, line number, enclosing element, and the first line of text
that follows, so you can confirm you are looking at the same passage in every
witness before renaming it. Flags: `·` not present in every file, `‡`
repeated within one file (invalid XML), `†` pointed at but never defined.

**Witness grid** — the whole corpus as a collation table: identifiers down the
side, files across the top, `✓ ◦ ·` in the cells. Gaps and misalignments in
the id scheme are visible at a glance. Click any row to load it for renaming.

**Rename** — type the new value. It is checked live against XML naming rules
and against every other identifier in the corpus, so a collision is caught
before it reaches the disk. Renames accumulate in a queue; nothing touches
the files until you press **Review changes**, which shows every affected line,
old above new, and flags any file that would end up with a repeated id.

**Pattern rename** queues many at once from a regular expression, e.g.
find `^(ci24\.\d+)\.([a-z])$` replace `$1.add$2` — still reviewable line by
line before saving.

## What it guarantees

- Files are edited as text, never parsed and re-serialised, so whitespace,
  attribute order, comments, entities and line endings (including CRLF)
  are untouched. Only the attribute values you asked for change.
- A queue is applied in a single pass, so swaps (`a→b`, `b→a`) and chains
  (`a→b`, `b→c`) do what you mean rather than colliding.
- Pointing attributes — `@corresp`, `@target`, `@ref`, `@next`, `@prev`,
  `@sameAs`, `@copyOf`, `@source`, `@facs` and others — are updated wherever
  they contain `#id`, including inside space-separated pointer lists.
- Markup inside `<!-- comments -->` and CDATA is ignored, so superseded
  drafts are neither counted nor rewritten.
- Every save first copies the affected files to
  `.tei-id-sync-backups/YYYY-MM-DD_HHMMSS/`, together with a `renames.json`
  log. **Restore backup** in the toolbar puts any of them back.

## Limits

It reads attributes with a pattern rather than an XML parser, which is what
keeps your files byte-stable — but it means malformed markup is not detected.
Validate as usual afterwards. It does not follow XInclude, and it treats
`#id` in an attribute as a pointer regardless of which file defines the id,
which is what you want for a corpus edited as a unit.
