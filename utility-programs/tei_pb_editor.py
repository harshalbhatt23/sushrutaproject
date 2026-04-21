#!/usr/bin/env python3
"""
TEI/XML <pb> Element Editor
Opens a TEI/XML file, displays all <pb> elements with context,
allows editing attributes, and saves with '-pb-edits' appended to filename.
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import xml.etree.ElementTree as ET
import re
import os
from copy import deepcopy

# ── Constants ──────────────────────────────────────────────────────────────────
CONTEXT_CHARS = 60          # characters of surrounding text to show
BG_DARK       = "#1e1e2e"
BG_PANEL      = "#252535"
BG_CARD       = "#2a2a3e"
BG_INPUT      = "#1a1a2a"
ACCENT        = "#7c6af7"
ACCENT_LIGHT  = "#a89cf7"
TEXT_MAIN     = "#e0deff"
TEXT_DIM      = "#8888aa"
TEXT_CONTEXT  = "#c0bce8"
SUCCESS       = "#50fa7b"
WARN          = "#f1fa8c"
FONT_MONO     = ("Courier New", 10)
FONT_UI       = ("Segoe UI", 10)
FONT_TITLE    = ("Segoe UI", 13, "bold")
FONT_SMALL    = ("Segoe UI", 9)

TEI_NS_PATTERN = re.compile(r'\{[^}]+\}')


# ── Helpers ────────────────────────────────────────────────────────────────────

def strip_ns(tag: str) -> str:
    """Return tag name without namespace."""
    return TEI_NS_PATTERN.sub('', tag)


def get_ns(tag: str) -> str:
    """Return namespace URI (with braces) or empty string."""
    m = TEI_NS_PATTERN.match(tag)
    return m.group(0) if m else ''


def extract_context(raw_xml: str, pb_index: int, context_chars: int = CONTEXT_CHARS):
    """
    Given raw XML text and the index (0-based) of the <pb> occurrence,
    return (before_text, pb_tag, after_text).
    """
    # Find all <pb ...> or <pb/> occurrences
    pattern = re.compile(r'<pb\b[^>]*/?>|<pb\b[^>]*>', re.IGNORECASE)
    matches = list(pattern.finditer(raw_xml))
    if pb_index >= len(matches):
        return ('', '', '')
    m = matches[pb_index]
    start, end = m.start(), m.end()

    # Grab surrounding raw text (strip tags for readability)
    def clean(s):
        return re.sub(r'<[^>]+>', '', s)

    before = clean(raw_xml[max(0, start - context_chars * 3): start])[-context_chars:]
    after  = clean(raw_xml[end: end + context_chars * 3])[:context_chars]
    return before, m.group(0), after


# ── Main Application ───────────────────────────────────────────────────────────

class PbEditor(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("TEI <pb> Editor")
        self.configure(bg=BG_DARK)
        self.minsize(860, 600)
        self.geometry("1000x720")

        # State
        self.filepath    = None
        self.raw_xml     = None
        self.tree        = None          # ET.ElementTree
        self.root_elem   = None          # ET.Element
        self.pb_elements = []            # list of ET.Element
        self.attr_widgets = {}           # row_index -> {attr_name -> StringVar}
        self.new_attr_rows = []          # rows added dynamically

        self._build_ui()

    # ── UI Construction ──────────────────────────────────────────────────────

    def _build_ui(self):
        # Top bar
        topbar = tk.Frame(self, bg=BG_DARK, pady=10, padx=16)
        topbar.pack(fill='x')

        tk.Label(topbar, text="TEI <pb> Editor", font=FONT_TITLE,
                 bg=BG_DARK, fg=ACCENT_LIGHT).pack(side='left')

        btn_frame = tk.Frame(topbar, bg=BG_DARK)
        btn_frame.pack(side='right')

        self._btn_open = self._make_btn(btn_frame, "📂  Open File", self._open_file, ACCENT)
        self._btn_open.pack(side='left', padx=4)

        self._btn_save = self._make_btn(btn_frame, "💾  Save Edits", self._save_file,
                                        "#3dba6e", state='disabled')
        self._btn_save.pack(side='left', padx=4)

        # Status bar
        self._status_var = tk.StringVar(value="No file loaded. Click 'Open File' to begin.")
        status_bar = tk.Label(self, textvariable=self._status_var, font=FONT_SMALL,
                              bg=BG_PANEL, fg=TEXT_DIM, anchor='w', padx=12, pady=5)
        status_bar.pack(fill='x')

        # Scrollable canvas for pb cards
        container = tk.Frame(self, bg=BG_DARK)
        container.pack(fill='both', expand=True, padx=12, pady=8)

        self._canvas = tk.Canvas(container, bg=BG_DARK, highlightthickness=0)
        scrollbar = ttk.Scrollbar(container, orient='vertical', command=self._canvas.yview)
        self._canvas.configure(yscrollcommand=scrollbar.set)

        scrollbar.pack(side='right', fill='y')
        self._canvas.pack(side='left', fill='both', expand=True)

        self._scroll_frame = tk.Frame(self._canvas, bg=BG_DARK)
        self._canvas_window = self._canvas.create_window(
            (0, 0), window=self._scroll_frame, anchor='nw')

        self._scroll_frame.bind('<Configure>', self._on_frame_configure)
        self._canvas.bind('<Configure>', self._on_canvas_configure)
        self._canvas.bind_all('<MouseWheel>', self._on_mousewheel)

        # Style tweaks for ttk scrollbar
        style = ttk.Style(self)
        style.theme_use('clam')
        style.configure('Vertical.TScrollbar', troughcolor=BG_PANEL,
                        background=ACCENT, bordercolor=BG_DARK, arrowcolor=TEXT_DIM)

    def _make_btn(self, parent, text, command, color, state='normal'):
        btn = tk.Button(parent, text=text, command=command,
                        bg=color, fg='white', font=FONT_UI,
                        relief='flat', bd=0, padx=12, pady=6,
                        cursor='hand2', activebackground=ACCENT_LIGHT,
                        activeforeground='white', state=state)
        btn.bind('<Enter>', lambda e: btn.config(bg=self._lighten(color)))
        btn.bind('<Leave>', lambda e: btn.config(bg=color))
        return btn

    @staticmethod
    def _lighten(hex_color):
        """Very simple color lightening."""
        r, g, b = int(hex_color[1:3],16), int(hex_color[3:5],16), int(hex_color[5:7],16)
        r, g, b = min(255, r+30), min(255, g+30), min(255, b+30)
        return f'#{r:02x}{g:02x}{b:02x}'

    # ── Scroll helpers ────────────────────────────────────────────────────────

    def _on_frame_configure(self, _event):
        self._canvas.configure(scrollregion=self._canvas.bbox('all'))

    def _on_canvas_configure(self, event):
        self._canvas.itemconfig(self._canvas_window, width=event.width)

    def _on_mousewheel(self, event):
        self._canvas.yview_scroll(int(-1 * (event.delta / 120)), 'units')

    # ── File I/O ──────────────────────────────────────────────────────────────

    def _open_file(self):
        path = filedialog.askopenfilename(
            title="Open TEI/XML File",
            filetypes=[("XML files", "*.xml"), ("TEI files", "*.tei"),
                       ("All files", "*.*")])
        if not path:
            return
        try:
            with open(path, 'r', encoding='utf-8') as f:
                self.raw_xml = f.read()
            self.filepath = path
            self.tree = ET.parse(path)
            self.root_elem = self.tree.getroot()
            self._load_pb_elements()
            self._btn_save.config(state='normal')
        except Exception as e:
            messagebox.showerror("Error", f"Could not open file:\n{e}")

    def _load_pb_elements(self):
        """Find all <pb> elements and render cards."""
        ns = get_ns(self.root_elem.tag)
        search_tag = f"{ns}pb" if ns else 'pb'

        self.pb_elements = self.root_elem.findall(f'.//{search_tag}')
        if not self.pb_elements:
            # Try case-insensitive search via iteration
            self.pb_elements = [e for e in self.root_elem.iter()
                                 if strip_ns(e.tag).lower() == 'pb']

        count = len(self.pb_elements)
        fname = os.path.basename(self.filepath)
        self._status_var.set(
            f"Loaded: {fname}  —  {count} <pb> element{'s' if count != 1 else ''} found")

        self._render_cards()

    def _render_cards(self):
        """Clear scroll frame and rebuild all pb cards."""
        for widget in self._scroll_frame.winfo_children():
            widget.destroy()
        self.attr_widgets = {}
        self.new_attr_rows = []

        if not self.pb_elements:
            tk.Label(self._scroll_frame, text="No <pb> elements found in this file.",
                     font=FONT_UI, bg=BG_DARK, fg=WARN).pack(pady=40)
            return

        for idx, elem in enumerate(self.pb_elements):
            self._build_card(idx, elem)

        # Small bottom padding
        tk.Frame(self._scroll_frame, bg=BG_DARK, height=20).pack()

    def _build_card(self, idx: int, elem: ET.Element):
        """Build one card for a <pb> element."""
        before, pb_raw, after = extract_context(self.raw_xml, idx)

        card = tk.Frame(self._scroll_frame, bg=BG_CARD, bd=0,
                        highlightthickness=1, highlightbackground=ACCENT)
        card.pack(fill='x', padx=8, pady=6)
        card.columnconfigure(0, weight=1)

        # ── Card header ──
        header = tk.Frame(card, bg=ACCENT, padx=10, pady=4)
        header.grid(row=0, column=0, sticky='ew')

        tk.Label(header, text=f"<pb>  #{idx + 1}", font=("Segoe UI", 10, "bold"),
                 bg=ACCENT, fg='white').pack(side='left')

        # ── Context display ──
        ctx_frame = tk.Frame(card, bg=BG_CARD, padx=10, pady=6)
        ctx_frame.grid(row=1, column=0, sticky='ew')

        ctx_text = tk.Text(ctx_frame, height=2, wrap='word', font=FONT_MONO,
                           bg=BG_INPUT, fg=TEXT_CONTEXT, bd=0,
                           relief='flat', padx=6, pady=4,
                           state='normal', cursor='arrow')
        ctx_text.pack(fill='x')

        # Insert with tags for color coding
        ctx_text.tag_configure('dim',  foreground=TEXT_DIM)
        ctx_text.tag_configure('pb',   foreground=WARN, font=("Courier New", 10, "bold"))
        ctx_text.tag_configure('ctx',  foreground=TEXT_CONTEXT)

        ctx_text.insert('end', '…' + before, 'dim')
        ctx_text.insert('end', pb_raw, 'pb')
        ctx_text.insert('end', after + '…', 'dim')
        ctx_text.config(state='disabled')

        # ── Attributes section ──
        attr_outer = tk.Frame(card, bg=BG_CARD, padx=10, pady=6)
        attr_outer.grid(row=2, column=0, sticky='ew')

        tk.Label(attr_outer, text="Attributes", font=("Segoe UI", 9, "bold"),
                 bg=BG_CARD, fg=TEXT_DIM).grid(row=0, column=0, columnspan=3,
                                                sticky='w', pady=(0, 4))

        # Header row
        for col, (label, w) in enumerate([("Attribute Name", 22), ("Value", 36)]):
            tk.Label(attr_outer, text=label, font=FONT_SMALL,
                     bg=BG_CARD, fg=TEXT_DIM, width=w, anchor='w').grid(
                         row=1, column=col, padx=(0, 6), sticky='w')

        tk.Label(attr_outer, text="Action", font=FONT_SMALL,
                 bg=BG_CARD, fg=TEXT_DIM).grid(row=1, column=2, sticky='w')

        self.attr_widgets[idx] = {}
        row_num = 2

        for attr_name, attr_val in elem.attrib.items():
            row_num = self._add_attr_row(attr_outer, idx, elem,
                                          attr_name, attr_val, row_num,
                                          deletable=True)

        # "Add attribute" button
        add_btn_row = row_num
        add_btn = self._make_btn(attr_outer, "+ Add Attribute",
                                 lambda i=idx, e=elem, f=attr_outer,
                                        r=add_btn_row: self._add_new_attr(i, e, f, r),
                                 "#2e4060")
        add_btn.grid(row=add_btn_row, column=0, columnspan=3,
                     sticky='w', pady=(8, 2))

        attr_outer.add_btn_row = add_btn_row   # store for dynamic additions
        attr_outer.add_btn = add_btn

    def _add_attr_row(self, frame, idx, elem, attr_name, attr_val,
                      row_num, deletable=True):
        """Add a name/value row inside an attribute frame. Returns next row_num."""
        name_var = tk.StringVar(value=attr_name)
        val_var  = tk.StringVar(value=attr_val)

        name_entry = tk.Entry(frame, textvariable=name_var, font=FONT_MONO,
                              bg=BG_INPUT, fg=TEXT_MAIN, insertbackground=ACCENT,
                              relief='flat', bd=0, width=22)
        name_entry.grid(row=row_num, column=0, padx=(0, 6), pady=2, sticky='w')

        val_entry = tk.Entry(frame, textvariable=val_var, font=FONT_MONO,
                             bg=BG_INPUT, fg=ACCENT_LIGHT, insertbackground=ACCENT,
                             relief='flat', bd=0, width=36)
        val_entry.grid(row=row_num, column=1, padx=(0, 6), pady=2, sticky='ew')

        if deletable:
            del_btn = tk.Button(frame, text="✕", font=FONT_SMALL,
                                bg="#5c2a2a", fg="#ff6b6b",
                                relief='flat', bd=0, padx=6, pady=2,
                                cursor='hand2',
                                command=lambda nv=name_var, vv=val_var,
                                               ne=name_entry, ve=val_entry,
                                               db=None, e=elem, i=idx: (
                                    ne.destroy(), ve.destroy(),
                                    self.attr_widgets[i].pop(id(nv), None),
                                    self._sync_elem_attrs(i, e)
                                ))
            # Patch the del_btn reference
            del_btn.config(command=lambda nv=name_var, vv=val_var,
                                          ne=name_entry, ve=val_entry,
                                          e=elem, i=idx: (
                ne.grid_remove(), ve.grid_remove(),
                del_btn.grid_remove(),
                self.attr_widgets[i].pop(id(nv), None),
                self._sync_elem_attrs(i, e)
            ))
            del_btn.grid(row=row_num, column=2, padx=2, pady=2)

        key = id(name_var)
        self.attr_widgets[idx][key] = (name_var, val_var)

        # Live sync on change
        name_var.trace_add('write', lambda *_, e=elem, i=idx: self._sync_elem_attrs(i, e))
        val_var.trace_add('write',  lambda *_, e=elem, i=idx: self._sync_elem_attrs(i, e))

        return row_num + 1

    def _add_new_attr(self, idx, elem, frame, base_row):
        """Dynamically add a new blank attribute row."""
        # Move the Add button down
        current_row = frame.add_btn_row + 1
        frame.add_btn.grid_remove()

        self._add_attr_row(frame, idx, elem, '', '', current_row, deletable=True)
        frame.add_btn_row = current_row + 1
        frame.add_btn.grid(row=frame.add_btn_row, column=0, columnspan=3,
                           sticky='w', pady=(8, 2))
        frame.add_btn.config(
            command=lambda i=idx, e=elem, f=frame,
                           r=frame.add_btn_row: self._add_new_attr(i, e, f, r))

    def _sync_elem_attrs(self, idx, elem):
        """Write current widget values back into the ET element."""
        if idx not in self.attr_widgets:
            return
        new_attrib = {}
        for (name_var, val_var) in self.attr_widgets[idx].values():
            n = name_var.get().strip()
            v = val_var.get()
            if n:
                new_attrib[n] = v
        elem.attrib.clear()
        elem.attrib.update(new_attrib)

    # ── Save ──────────────────────────────────────────────────────────────────

    def _save_file(self):
        if not self.filepath or self.tree is None:
            return

        # Flush all attr edits
        for idx, elem in enumerate(self.pb_elements):
            self._sync_elem_attrs(idx, elem)

        # Build output path
        base, ext = os.path.splitext(self.filepath)
        out_path = base + "-pb-edits" + ext

        try:
            # Preserve XML declaration and namespaces
            ET.register_namespace('', 'http://www.tei-c.org/ns/1.0')
            # Write with xml_declaration
            self.tree.write(out_path, encoding='unicode', xml_declaration=True)

            # Ensure <?xml version="1.0" ?> has proper encoding tag if missing
            with open(out_path, 'r', encoding='utf-8') as f:
                content = f.read()
            if content.startswith("<?xml version='1.0' encoding='us-ascii'?>") or \
               not 'encoding' in content[:40]:
                content = '<?xml version=\'1.0\' encoding=\'UTF-8\'?>\n' + \
                          content.split('\n', 1)[-1] if '\n' in content else content

            with open(out_path, 'w', encoding='utf-8') as f:
                f.write(content)

            fname = os.path.basename(out_path)
            self._status_var.set(f"✔  Saved: {fname}")
            messagebox.showinfo("Saved", f"File saved as:\n{out_path}")
        except Exception as e:
            messagebox.showerror("Save Error", f"Could not save file:\n{e}")


# ── Entry point ────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    app = PbEditor()
    app.mainloop()
