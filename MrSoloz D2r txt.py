#!/usr/bin/env python3
# MrSoloz D2r txt
# Created for and owned by MrSoloz.

from __future__ import annotations

import csv
import json
import tkinter as tk
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk
from typing import List, Optional, Sequence, Tuple

APP_TITLE = "MrSoloz D2r txt"
APP_VERSION = "v1.0.1"
SETTINGS_FILE = Path(__file__).with_name("d2text_settings.json")
MAX_PREVIEW_ROWS = 5000
MAX_UNDO_STEPS = 50
DEFAULT_ROW_HEIGHT = 24
ROW_NUMBER_WIDTH = 64
MIN_COLUMN_WIDTH = 90
MAX_COLUMN_WIDTH: Optional[int] = None
MIN_ROW_HEIGHT = 18
MAX_ROW_HEIGHT: Optional[int] = None
TEXT_PAD_X = 6
SUPPORTED_FILETYPES = [
    ("Text Tables", "*.txt *.tsv *.csv *.tab *.dat"),
    ("Text Files", "*.txt"),
    ("Tab Separated", "*.tsv *.tab"),
    ("Comma Separated", "*.csv"),
    ("All Files", "*.*"),
]

HEADER_BG = "#d9ffb8"
HEADER_BG_ALT = "#ccf59f"
HEADER_BORDER = "#5a8f38"
FROZEN_BG = "#d7ffb1"
FROZEN_ALT_BG = "#caef99"
CORNER_BG = "#bfe67c"
CELL_BG = "#ffffff"
CELL_ALT_BG = "#f3f5f8"
GRID_LINE = "#98a3b2"
TEXT_COLOR = "#111111"
SELECTION_FILL = "#cfe5ff"
SELECTION_OUTLINE = "#4a90e2"
MARKER_FILL = "#d9f3cf"
MARKER_OUTLINE = "#6aa84f"
DRAG_AUTOSCROLL_DELAY_MS = 65
DRAG_AUTOSCROLL_EDGE_MARGIN = 28
DRAG_AUTOSCROLL_MAX_STEP = 4
RESIZE_REDRAW_DELAY_MS = 16


class D2TextApp(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title(f"{APP_TITLE} {APP_VERSION}")
        self.geometry("1260x800")
        self.minsize(980, 640)
        try:
            self.state("zoomed")
        except Exception:
            pass

        self.current_path: Optional[Path] = None
        self.last_open_dir: Path = Path.cwd()
        self.backup_dir: Optional[Path] = None
        self.current_doc_index: Optional[int] = None
        self.documents: List[dict] = []
        self.undo_stack: List[dict] = []
        self.loaded_columns: List[str] = []
        self.loaded_rows: List[List[str]] = []
        self.loaded_details = ""
        self.column_widths: List[int] = []
        self.row_heights: List[int] = []

        self.status_var = tk.StringVar(value="Open a text file to preview it in a D2ExcelPlus-style grid.")
        self.path_var = tk.StringVar(value="No file loaded")
        self.info_var = tk.StringVar(value="")
        self.total_var = tk.StringVar(value="Rows: 0 | Columns: 0")
        self.find_text_var = tk.StringVar(value="")
        self.lock_rows_var = tk.BooleanVar(value=False)
        self.lock_columns_var = tk.BooleanVar(value=True)
        self.lock_row_count_var = tk.IntVar(value=1)
        self.lock_column_count_var = tk.IntVar(value=1)
        self.cell_font_size_var = tk.IntVar(value=9)
        self.cell_bold_var = tk.BooleanVar(value=False)
        self.center_selection_var = tk.BooleanVar(value=False)

        self.body_row_offset = 0
        self.body_col_offset = 0
        self.selection_anchor: Optional[Tuple[int, int]] = None
        self.selection_focus: Optional[Tuple[int, int]] = None
        self.marked_rows: set[int] = set()
        self.marked_columns: set[int] = set()
        self.drag_widget: Optional[tk.Widget] = None
        self.drag_last_x = 0
        self.drag_last_y = 0
        self.drag_autoscroll_job: Optional[str] = None
        self.resize_mode: Optional[str] = None
        self.resize_index: Optional[int] = None
        self.resize_start_x = 0
        self.resize_start_y = 0
        self.resize_origin_size = 0
        self.resize_last_size = 0
        self.resize_widget: Optional[tk.Widget] = None
        self.resize_start_local_x = 0
        self.resize_start_local_y = 0
        self.resize_widget_root_x = 0
        self.resize_widget_root_y = 0
        self.resize_widget_width = 0
        self.resize_widget_height = 0
        self.resize_redraw_job: Optional[str] = None
        self.defer_document_capture = False
        self.editor_entry: Optional[ttk.Entry] = None
        self.editing_cell: Optional[Tuple[int, int]] = None
        self.editing_var = tk.StringVar(value="")
        self.find_dialog: Optional[tk.Toplevel] = None
        self.find_entry: Optional[ttk.Entry] = None
        self.find_last_query = ""
        self.find_last_match: Optional[Tuple[int, int]] = None
        self.find_last_doc_index: Optional[int] = None

        self.corner_canvas: Optional[tk.Canvas] = None
        self.top_canvas: Optional[tk.Canvas] = None
        self.left_canvas: Optional[tk.Canvas] = None
        self.body_canvas: Optional[tk.Canvas] = None
        self.document_tabs: Optional[ttk.Notebook] = None
        self.tab_menu: Optional[tk.Menu] = None
        self.tab_menu_index: Optional[int] = None
        self.workspace_tree: Optional[ttk.Treeview] = None
        self.workspace_refreshing = False
        self.corner_frame: Optional[ttk.Frame] = None
        self.top_frame: Optional[ttk.Frame] = None
        self.left_frame: Optional[ttk.Frame] = None
        self._x_scrollbar: Optional[ttk.Scrollbar] = None
        self._y_scrollbar: Optional[ttk.Scrollbar] = None

        self._load_settings()
        self._apply_panel_theme()
        self._build_ui()

    def _apply_panel_theme(self) -> None:
        panel_bg = "#000000"
        panel_alt = "#111111"
        panel_border = "#2f2f2f"
        text_fg = "#f2f2f2"
        accent_bg = "#c8ff8a"
        button_active = "#d9ffb8"

        self.configure(bg=panel_bg)
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        style.configure(".", background=panel_bg, foreground=text_fg)
        style.configure("TFrame", background=panel_bg)
        style.configure("TLabel", background=panel_bg, foreground=text_fg)
        style.configure("TLabelFrame", background=panel_bg, foreground=text_fg, bordercolor=panel_border)
        style.configure("TLabelFrame.Label", background=panel_bg, foreground=text_fg)
        style.configure(
            "TButton",
            background=accent_bg,
            foreground="#000000",
            bordercolor=panel_border,
            lightcolor=accent_bg,
            darkcolor=accent_bg,
            relief="flat",
            focusthickness=1,
            focuscolor=panel_border,
            padding=(10, 5),
            font=("Segoe UI", 9, "bold italic"),
        )
        style.map(
            "TButton",
            background=[("active", button_active), ("pressed", button_active), ("!disabled", accent_bg)],
            foreground=[("active", "#000000"), ("pressed", "#000000"), ("!disabled", "#000000")],
            lightcolor=[("active", button_active), ("pressed", button_active), ("!disabled", accent_bg)],
            darkcolor=[("active", button_active), ("pressed", button_active), ("!disabled", accent_bg)],
        )
        style.configure("TCheckbutton", background=panel_bg, foreground=text_fg)
        style.map("TCheckbutton", background=[("active", panel_bg)], foreground=[("active", text_fg)])
        style.configure("TSpinbox", fieldbackground=accent_bg, background=accent_bg, foreground="#000000", arrowcolor="#000000", bordercolor=panel_border)
        style.configure("TEntry", fieldbackground=accent_bg, foreground="#000000", bordercolor=panel_border, font=("Segoe UI", 9, "bold italic"))
        style.configure("TCombobox", fieldbackground=accent_bg, background=accent_bg, foreground=text_fg, arrowcolor=text_fg, bordercolor=panel_border)
        style.map("TCombobox", fieldbackground=[("readonly", accent_bg)], foreground=[("readonly", text_fg)])
        style.configure("Treeview", background=panel_bg, fieldbackground=panel_bg, foreground=text_fg, bordercolor=panel_border, indent=10)
        style.configure("Treeview.Heading", background=accent_bg, foreground=text_fg, bordercolor=panel_border)
        style.configure("TNotebook", background=panel_bg, bordercolor=panel_border, tabmargins=(2, 2, 2, 0))
        style.configure("TNotebook.Tab", background="#bfff8a", foreground="#000000", bordercolor=panel_border, padding=(8, 4), font=("Segoe UI", 9, "bold"))
        style.map("TNotebook.Tab", background=[("selected", "#d9ffb8"), ("active", "#d1ffa8")], foreground=[("selected", "#000000"), ("active", "#000000")])
        style.configure("Horizontal.TScrollbar", background=accent_bg, troughcolor=panel_bg, bordercolor=panel_border, arrowcolor=text_fg)
        style.configure("Vertical.TScrollbar", background=accent_bg, troughcolor=panel_bg, bordercolor=panel_border, arrowcolor=text_fg)

    def _build_ui(self) -> None:
        self._build_menu()
        self.columnconfigure(0, weight=1)
        self.rowconfigure(2, weight=1)

        toolbar = ttk.Frame(self, padding=(6, 0, 6, 0))
        toolbar.grid(row=0, column=0, sticky="ew")
        toolbar.columnconfigure(19, weight=1)
        toolbar.columnconfigure(20, weight=1)
        ttk.Button(toolbar, text="Open Text File", command=self.open_file).grid(row=0, column=0, padx=(0, 6))
        ttk.Button(toolbar, text="Save", command=self.save_file).grid(row=0, column=1, padx=6)
        ttk.Button(toolbar, text="Save As", command=self.save_file_as).grid(row=0, column=2, padx=6)
        ttk.Button(toolbar, text="Backup", command=self.backup_file).grid(row=0, column=3, padx=6)
        ttk.Button(toolbar, text="Find Text", command=self.find_text).grid(row=0, column=4, padx=6)
        ttk.Button(toolbar, text="Reload", command=self.reload_file).grid(row=0, column=5, padx=6)
        ttk.Button(toolbar, text="Clear", command=self.clear_table).grid(row=0, column=6, padx=6)
        ttk.Button(toolbar, text="Undo Edit", command=self.undo_edit).grid(row=0, column=7, padx=6)
        ttk.Checkbutton(toolbar, text="Lock first", variable=self.lock_rows_var, command=self._on_freeze_option_changed).grid(row=0, column=8, padx=(12, 4))
        row_spin = ttk.Spinbox(toolbar, from_=1, to=99, textvariable=self.lock_row_count_var, width=5, command=self._on_freeze_option_changed)
        row_spin.grid(row=0, column=9, padx=(0, 4))
        row_spin.bind("<Return>", lambda _event: self._on_freeze_option_changed())
        row_spin.bind("<FocusOut>", lambda _event: self._on_freeze_option_changed())
        ttk.Label(toolbar, text="Rows").grid(row=0, column=10, padx=(0, 10))
        ttk.Checkbutton(toolbar, text="Lock first", variable=self.lock_columns_var, command=self._on_freeze_option_changed).grid(row=0, column=11, padx=(0, 4))
        col_spin = ttk.Spinbox(toolbar, from_=1, to=99, textvariable=self.lock_column_count_var, width=5, command=self._on_freeze_option_changed)
        col_spin.grid(row=0, column=12, padx=(0, 4))
        col_spin.bind("<Return>", lambda _event: self._on_freeze_option_changed())
        col_spin.bind("<FocusOut>", lambda _event: self._on_freeze_option_changed())
        ttk.Label(toolbar, text="Columns").grid(row=0, column=13, padx=(0, 10))
        ttk.Label(toolbar, text="Font").grid(row=0, column=14, padx=(0, 4))
        font_spin = ttk.Spinbox(toolbar, from_=6, to=72, textvariable=self.cell_font_size_var, width=5, command=self._on_font_option_changed)
        font_spin.grid(row=0, column=15, padx=(0, 6))
        font_spin.bind("<Return>", lambda _event: self._on_font_option_changed())
        font_spin.bind("<FocusOut>", lambda _event: self._on_font_option_changed())
        ttk.Checkbutton(toolbar, text="Bold", variable=self.cell_bold_var, command=self._on_font_option_changed).grid(row=0, column=16, padx=(0, 10))
        ttk.Checkbutton(toolbar, text="Center Cell", variable=self.center_selection_var, command=self._on_center_selection_changed).grid(row=0, column=17, padx=(0, 10))
        ttk.Separator(toolbar, orient="vertical").grid(row=0, column=18, sticky="ns", padx=(0, 10))
        ttk.Label(toolbar, textvariable=self.status_var, anchor="w").grid(row=0, column=19, sticky="ew", padx=(0, 12))
        title_frame = tk.Frame(toolbar, bg="#000000")
        title_frame.grid(row=0, column=20, sticky="nsew")
        title_frame.grid_columnconfigure(0, weight=1)
        tk.Label(
            title_frame,
            text="MrSoloz",
            font=("Segoe UI", 78, "bold italic"),
            fg="#7dff3a",
            bg="#000000",
            padx=0,
            pady=0,
        ).grid(row=0, column=0, sticky="w", padx=(8, 0))
        tk.Label(
            title_frame,
            text=APP_VERSION,
            font=("Segoe UI", 12, "bold italic"),
            fg="#c8ff8a",
            bg="#000000",
            padx=0,
            pady=0,
        ).grid(row=0, column=1, sticky="sw", padx=(14, 0))

        meta = ttk.Frame(self, padding=(6, 0, 6, 1))
        meta.grid(row=1, column=0, sticky="ew")
        meta.columnconfigure(1, weight=1)
        ttk.Label(meta, text="Path", width=8).grid(row=0, column=0, sticky="w", padx=(0, 8))
        ttk.Label(meta, textvariable=self.path_var, justify="left").grid(row=0, column=1, sticky="w")
        ttk.Label(meta, text="Details", width=8).grid(row=1, column=0, sticky="w", padx=(0, 8))
        ttk.Label(meta, textvariable=self.info_var, justify="left").grid(row=1, column=1, sticky="w")
        ttk.Label(meta, text="Totals", width=8).grid(row=2, column=0, sticky="w", padx=(0, 8))
        ttk.Label(meta, textvariable=self.total_var, justify="left").grid(row=2, column=1, sticky="w")

        viewer_shell = ttk.Frame(self, padding=(6, 0, 6, 6))
        viewer_shell.grid(row=2, column=0, sticky="nsew")
        viewer_shell.columnconfigure(0, weight=1)
        viewer_shell.rowconfigure(1, weight=1)

        tabs_bar = ttk.Frame(viewer_shell, padding=(0, 0, 0, 1))
        tabs_bar.grid(row=0, column=0, sticky="ew")
        tabs_bar.columnconfigure(0, weight=1)
        self.document_tabs = ttk.Notebook(tabs_bar, height=24)
        self.document_tabs.grid(row=0, column=0, sticky="ew")
        self.document_tabs.bind("<<NotebookTabChanged>>", self._on_tab_changed)
        self.document_tabs.bind("<Button-3>", self._show_tab_menu)
        self.tab_menu = tk.Menu(self, tearoff=0)
        self._style_menu(self.tab_menu)
        self.tab_menu.add_command(label="Close Tab", command=self._close_tab_from_menu)

        splitter = tk.PanedWindow(
            viewer_shell,
            orient=tk.HORIZONTAL,
            sashwidth=8,
            bg="#000000",
            bd=0,
            relief="flat",
            showhandle=False,
            opaqueresize=True,
        )
        splitter.grid(row=1, column=0, sticky="nsew")
        self.workspace_splitter = splitter

        workspace = ttk.LabelFrame(splitter, text="Workspace", padding=(4, 4, 4, 4))
        workspace.columnconfigure(0, weight=1)
        workspace.rowconfigure(1, weight=1)
        ttk.Label(workspace, text="Loaded Path").grid(row=0, column=0, sticky="w", pady=(0, 6))
        self.workspace_tree = ttk.Treeview(workspace, show="tree", height=24)
        self.workspace_tree.grid(row=1, column=0, sticky="nsew")
        self.workspace_tree.column("#0", width=340, minwidth=180, stretch=True)
        self.workspace_tree.bind("<<TreeviewSelect>>", self._on_workspace_tree_select)
        splitter.add(workspace, minsize=220, width=360)

        sheet_host = ttk.Frame(splitter)
        sheet_host.columnconfigure(0, weight=1)
        sheet_host.rowconfigure(1, weight=1)
        splitter.add(sheet_host, minsize=500)
        self.after_idle(lambda: self.workspace_splitter.sash_place(0, 360, 0))

        viewer = ttk.Frame(sheet_host)
        viewer.grid(row=1, column=0, sticky="nsew")
        viewer.columnconfigure(0, weight=0)
        viewer.columnconfigure(1, weight=1)
        viewer.rowconfigure(1, weight=0)
        viewer.rowconfigure(2, weight=1)

        sheet_controls = ttk.Frame(sheet_host, padding=(0, 0, 0, 1))
        sheet_controls.grid(row=0, column=0, sticky="ew")
        ttk.Checkbutton(sheet_controls, text="Lock first", variable=self.lock_rows_var, command=self._on_freeze_option_changed).grid(row=0, column=0, padx=(0, 4))
        row_spin_small = ttk.Spinbox(sheet_controls, from_=1, to=99, textvariable=self.lock_row_count_var, width=4, command=self._on_freeze_option_changed)
        row_spin_small.grid(row=0, column=1, padx=(0, 4))
        row_spin_small.bind("<Return>", lambda _event: self._on_freeze_option_changed())
        row_spin_small.bind("<FocusOut>", lambda _event: self._on_freeze_option_changed())
        ttk.Label(sheet_controls, text="Rows").grid(row=0, column=2, padx=(0, 10))
        ttk.Checkbutton(sheet_controls, text="Lock first", variable=self.lock_columns_var, command=self._on_freeze_option_changed).grid(row=0, column=3, padx=(0, 4))
        col_spin_small = ttk.Spinbox(sheet_controls, from_=1, to=99, textvariable=self.lock_column_count_var, width=4, command=self._on_freeze_option_changed)
        col_spin_small.grid(row=0, column=4, padx=(0, 4))
        col_spin_small.bind("<Return>", lambda _event: self._on_freeze_option_changed())
        col_spin_small.bind("<FocusOut>", lambda _event: self._on_freeze_option_changed())
        ttk.Label(sheet_controls, text="Columns").grid(row=0, column=5, padx=(0, 10))

        self.corner_frame = ttk.Frame(viewer)
        self.corner_frame.grid(row=1, column=0, sticky="nsew")
        self.top_frame = ttk.Frame(viewer)
        self.top_frame.grid(row=1, column=1, sticky="ew")
        self.left_frame = ttk.Frame(viewer)
        self.left_frame.grid(row=2, column=0, sticky="ns")
        body_frame = ttk.Frame(viewer)
        body_frame.grid(row=2, column=1, sticky="nsew")

        self.corner_frame.columnconfigure(0, weight=1)
        self.corner_frame.rowconfigure(0, weight=1)
        self.top_frame.columnconfigure(0, weight=1)
        self.top_frame.rowconfigure(0, weight=1)
        self.left_frame.columnconfigure(0, weight=1)
        self.left_frame.rowconfigure(0, weight=1)
        body_frame.columnconfigure(0, weight=1)
        body_frame.rowconfigure(0, weight=1)

        self.corner_canvas = tk.Canvas(self.corner_frame, bg=CORNER_BG, highlightthickness=1, highlightbackground=HEADER_BORDER)
        self.top_canvas = tk.Canvas(self.top_frame, bg=HEADER_BG, highlightthickness=1, highlightbackground=HEADER_BORDER)
        self.left_canvas = tk.Canvas(self.left_frame, bg=FROZEN_BG, highlightthickness=1, highlightbackground=HEADER_BORDER)
        self.body_canvas = tk.Canvas(body_frame, bg=CELL_BG, highlightthickness=1, highlightbackground=HEADER_BORDER)

        self.corner_canvas.grid(row=0, column=0, sticky="nsew")
        self.top_canvas.grid(row=0, column=0, sticky="ew")
        self.left_canvas.grid(row=0, column=0, sticky="ns")
        self.body_canvas.grid(row=0, column=0, sticky="nsew")

        self._y_scrollbar = ttk.Scrollbar(body_frame, orient="vertical", command=self._on_vertical_scroll)
        self._x_scrollbar = ttk.Scrollbar(body_frame, orient="horizontal", command=self._on_horizontal_scroll)
        self._y_scrollbar.grid(row=0, column=1, sticky="ns")
        self._x_scrollbar.grid(row=1, column=0, sticky="ew")

        self.body_canvas.bind("<Configure>", lambda _event: self._redraw())
        self.top_canvas.bind("<Configure>", lambda _event: self._redraw())
        self.left_canvas.bind("<Configure>", lambda _event: self._redraw())
        self.body_canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.left_canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.top_canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.corner_canvas.bind("<MouseWheel>", self._on_mousewheel)

        self.top_canvas.bind("<Button-3>", self._show_top_menu)
        self.corner_canvas.bind("<Button-3>", self._show_corner_menu)
        self.left_canvas.bind("<Button-3>", self._show_row_menu)
        self.body_canvas.bind("<Button-3>", self._show_cell_menu)
        self.top_canvas.bind("<Motion>", self._update_resize_cursor)
        self.left_canvas.bind("<Motion>", self._update_resize_cursor)
        self.corner_canvas.bind("<Motion>", self._update_resize_cursor)

        self.body_canvas.bind("<Button-1>", self._start_selection)
        self.body_canvas.bind("<Double-1>", self._begin_edit_from_event)
        self.body_canvas.bind("<B1-Motion>", self._drag_selection)
        self.body_canvas.bind("<ButtonRelease-1>", self._finish_selection)
        self.body_canvas.bind("<Key>", lambda _event: "break")
        self.body_canvas.bind("<Up>", lambda event: self._move_selection_by_key(event, -1, 0))
        self.body_canvas.bind("<Down>", lambda event: self._move_selection_by_key(event, 1, 0))
        self.body_canvas.bind("<Left>", lambda event: self._move_selection_by_key(event, 0, -1))
        self.body_canvas.bind("<Right>", lambda event: self._move_selection_by_key(event, 0, 1))
        self.body_canvas.bind("<Return>", self._begin_edit_from_selection_shortcut)
        self.body_canvas.bind("<KP_Enter>", self._begin_edit_from_selection_shortcut)
        self.body_canvas.bind("<F2>", self._begin_edit_from_selection_shortcut)
        self.body_canvas.bind("<KeyPress>", self._start_typing_edit)

        for canvas in [self.corner_canvas, self.top_canvas, self.left_canvas]:
            canvas.bind("<Button-1>", self._start_resize_or_selection)
            canvas.bind("<Double-1>", self._begin_edit_from_event)
            canvas.bind("<B1-Motion>", self._drag_selection)
            canvas.bind("<ButtonRelease-1>", self._finish_selection)
            canvas.bind("<Key>", lambda _event: "break")
            canvas.bind("<Up>", lambda event: self._move_selection_by_key(event, -1, 0))
            canvas.bind("<Down>", lambda event: self._move_selection_by_key(event, 1, 0))
            canvas.bind("<Left>", lambda event: self._move_selection_by_key(event, 0, -1))
            canvas.bind("<Right>", lambda event: self._move_selection_by_key(event, 0, 1))
            canvas.bind("<Return>", self._begin_edit_from_selection_shortcut)
            canvas.bind("<KP_Enter>", self._begin_edit_from_selection_shortcut)
            canvas.bind("<F2>", self._begin_edit_from_selection_shortcut)
            canvas.bind("<KeyPress>", self._start_typing_edit)

        self.bind("<Control-c>", self._copy_selection_shortcut)
        self.bind("<Control-C>", self._copy_selection_shortcut)
        self.bind("<Control-v>", self._paste_selection_shortcut)
        self.bind("<Control-V>", self._paste_selection_shortcut)
        self.bind("<Control-f>", self._find_text_shortcut)
        self.bind("<Control-F>", self._find_text_shortcut)
        self.bind("<Up>", lambda event: self._move_selection_by_key(event, -1, 0))
        self.bind("<Down>", lambda event: self._move_selection_by_key(event, 1, 0))
        self.bind("<Left>", lambda event: self._move_selection_by_key(event, 0, -1))
        self.bind("<Right>", lambda event: self._move_selection_by_key(event, 0, 1))
        self.bind("<Return>", self._begin_edit_from_selection_shortcut)
        self.bind("<KP_Enter>", self._begin_edit_from_selection_shortcut)
        self.bind("<F2>", self._begin_edit_from_selection_shortcut)
        self.bind("<KeyPress>", self._start_typing_edit)

        self._reset_view()

    def _build_menu(self) -> None:
        menu_bar = tk.Menu(self)

        file_menu = tk.Menu(menu_bar, tearoff=0)
        self._style_menu(file_menu)
        file_menu.add_command(label="Open", command=self.open_file)
        file_menu.add_command(label="Save", command=self.save_file)
        file_menu.add_command(label="Save As", command=self.save_file_as)
        file_menu.add_command(label="Backup", command=self.backup_file)
        file_menu.add_command(label="Choose Backup Folder", command=self.choose_backup_folder)
        file_menu.add_command(label="Find Text", command=self.find_text)
        file_menu.add_command(label="Reload", command=self.reload_file)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.destroy)
        menu_bar.add_cascade(label="File", menu=file_menu)

        edit_menu = tk.Menu(menu_bar, tearoff=0)
        self._style_menu(edit_menu)
        edit_menu.add_command(label="Increase Row/Column", state="disabled")
        edit_menu.add_command(label="Decrease Row/Column", state="disabled")
        menu_bar.add_cascade(label="Edit", menu=edit_menu)

        help_menu = tk.Menu(menu_bar, tearoff=0)
        self._style_menu(help_menu)
        help_menu.add_command(
            label="About",
            command=lambda: messagebox.showinfo(
                APP_TITLE,
                f"{APP_TITLE} {APP_VERSION}\nD2ExcelPlus-style text table viewer.",
                parent=self,
            ),
        )
        menu_bar.add_cascade(label="Help", menu=help_menu)

        self.config(menu=menu_bar)

    def _style_menu(self, menu: tk.Menu) -> None:
        menu.configure(
            background="#d9ffb8",
            foreground="#000000",
            activebackground="#bfff8a",
            activeforeground="#000000",
            selectcolor="#000000",
            font=("Segoe UI", 9, "bold"),
            borderwidth=1,
            relief="solid",
        )

    def _load_settings(self) -> None:
        if not SETTINGS_FILE.exists():
            return
        try:
            settings = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        except Exception:
            return
        last_open_dir = settings.get("last_open_dir")
        if last_open_dir:
            path = Path(last_open_dir)
            if path.exists():
                self.last_open_dir = path
        backup_dir = settings.get("backup_dir")
        if backup_dir:
            path = Path(backup_dir)
            if path.exists():
                self.backup_dir = path
        cell_font_size = settings.get("cell_font_size")
        if cell_font_size is not None:
            try:
                self.cell_font_size_var.set(max(6, int(cell_font_size)))
            except Exception:
                pass
        cell_bold = settings.get("cell_bold")
        if cell_bold is not None:
            self.cell_bold_var.set(bool(cell_bold))
        center_selection = settings.get("center_selection")
        if center_selection is not None:
            self.center_selection_var.set(bool(center_selection))

    def _save_settings(self) -> None:
        settings = {
            "last_open_dir": str(self.last_open_dir),
            "backup_dir": str(self.backup_dir) if self.backup_dir is not None else "",
            "cell_font_size": int(self.cell_font_size_var.get() or 9),
            "cell_bold": bool(self.cell_bold_var.get()),
            "center_selection": bool(self.center_selection_var.get()),
        }
        try:
            SETTINGS_FILE.write_text(json.dumps(settings, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _push_undo_state(self, label: str) -> None:
        if self.current_doc_index is None:
            return
        state = {
            "doc_index": self.current_doc_index,
            "label": label,
            "loaded_columns": list(self.loaded_columns),
            "loaded_rows": [list(row) for row in self.loaded_rows],
            "column_widths": list(self.column_widths),
            "row_heights": list(self.row_heights),
            "body_row_offset": self.body_row_offset,
            "body_col_offset": self.body_col_offset,
            "selection_anchor": self.selection_anchor,
            "selection_focus": self.selection_focus,
            "marked_rows": sorted(self.marked_rows),
            "marked_columns": sorted(self.marked_columns),
        }
        self.undo_stack.append(state)
        if len(self.undo_stack) > MAX_UNDO_STEPS:
            self.undo_stack = self.undo_stack[-MAX_UNDO_STEPS:]

    def undo_edit(self) -> None:
        if not self.undo_stack:
            self.status_var.set("Nothing to undo.")
            return
        state = self.undo_stack.pop()
        doc_index = state["doc_index"]
        if doc_index >= len(self.documents):
            self.status_var.set("Undo target is no longer available.")
            return
        self._activate_document(doc_index)
        self.loaded_columns = list(state["loaded_columns"])
        self.loaded_rows = [list(row) for row in state["loaded_rows"]]
        self.column_widths = list(state["column_widths"])
        self.row_heights = list(state["row_heights"])
        self.body_row_offset = int(state["body_row_offset"])
        self.body_col_offset = int(state["body_col_offset"])
        self.selection_anchor = state["selection_anchor"]
        self.selection_focus = state["selection_focus"]
        self.marked_rows = set(state.get("marked_rows", []))
        self.marked_columns = set(state.get("marked_columns", []))
        self._capture_current_document_state()
        self._update_info()
        self.status_var.set(f"Undid {state['label']}.")
        self._redraw()

    def _find_text_shortcut(self, _event: tk.Event) -> str:
        self.find_text()
        return "break"

    def _move_selection_by_key(self, _event: tk.Event, row_delta: int, col_delta: int) -> str:
        if self._keyboard_focus_blocks_grid_navigation():
            return ""
        if not self.loaded_rows or not self.loaded_columns:
            return "break"
        if self.editor_entry is not None:
            return ""
        row_index, column_index = self._selected_cell_for_navigation()
        row_index = max(0, min(len(self.loaded_rows) - 1, row_index + row_delta))
        column_index = max(0, min(len(self.loaded_columns) - 1, column_index + col_delta))
        self.selection_anchor = (row_index, column_index)
        self.selection_focus = (row_index, column_index)
        self._position_selected_cell(row_index, column_index)
        self.status_var.set(f"Selected row {row_index + 1}, column {column_index + 1}.")
        self._redraw()
        return "break"

    def _commit_edit_and_move(self, row_delta: int, col_delta: int) -> str:
        if self.editing_cell is None or not self.loaded_rows or not self.loaded_columns:
            return "break"
        row_index, column_index = self.editing_cell
        self._commit_edit()
        next_row = max(0, min(len(self.loaded_rows) - 1, row_index + row_delta))
        next_col = max(0, min(len(self.loaded_columns) - 1, column_index + col_delta))
        self.selection_anchor = (next_row, next_col)
        self.selection_focus = (next_row, next_col)
        self._position_selected_cell(next_row, next_col)
        self.status_var.set(f"Selected row {next_row + 1}, column {next_col + 1}.")
        self._redraw()
        return "break"

    def _begin_edit_from_selection_shortcut(self, _event: tk.Event) -> str:
        if self._keyboard_focus_blocks_grid_navigation():
            return ""
        if self.editor_entry is not None:
            return ""
        cell = self._selected_single_cell()
        if cell is None:
            return "break"
        self._begin_edit(cell)
        return "break"

    def _start_typing_edit(self, event: tk.Event) -> str:
        if self._keyboard_focus_blocks_grid_navigation():
            return ""
        if event.state & 0x4:
            return ""
        if self.editor_entry is not None:
            return ""
        if not event.char or not event.char.isprintable():
            return ""
        cell = self._selected_single_cell()
        if cell is None:
            return ""
        self._begin_edit(cell, initial_text=event.char, select_all=False)
        if self.editor_entry is not None:
            self.editor_entry.icursor("end")
        return "break"

    def _keyboard_focus_blocks_grid_navigation(self) -> bool:
        focus_widget = self.focus_get()
        if focus_widget is None:
            return False
        return bool(isinstance(focus_widget, (tk.Entry, ttk.Entry, tk.Spinbox, ttk.Spinbox)))

    def _selected_cell_for_navigation(self) -> Tuple[int, int]:
        if self.selection_focus is not None:
            return self.selection_focus
        if self.selection_anchor is not None:
            return self.selection_anchor
        return 0, 0

    def _selected_single_cell(self) -> Optional[Tuple[int, int]]:
        bounds = self._selection_bounds()
        if bounds is None:
            if self.loaded_rows and self.loaded_columns:
                cell = (0, 0)
                self.selection_anchor = cell
                self.selection_focus = cell
                return cell
            return None
        min_row, max_row, min_col, max_col = bounds
        if min_row != max_row or min_col != max_col:
            return None
        if self.selection_focus is not None:
            return self.selection_focus
        return min_row, min_col

    def find_text(self) -> None:
        if not self.loaded_rows or not self.loaded_columns:
            messagebox.showinfo(APP_TITLE, "Open a text file first.")
            return

        if self.find_dialog is not None and self.find_dialog.winfo_exists():
            self.find_dialog.deiconify()
            self.find_dialog.lift()
            if self.find_entry is not None:
                self.find_entry.focus_set()
                self.find_entry.selection_range(0, "end")
            return

        dialog = tk.Toplevel(self)
        self.find_dialog = dialog
        dialog.title("Find Text")
        dialog.transient(self)
        dialog.resizable(False, False)
        dialog.protocol("WM_DELETE_WINDOW", self._close_find_dialog)

        container = ttk.Frame(dialog, padding=12)
        container.grid(row=0, column=0, sticky="nsew")
        container.columnconfigure(1, weight=1)

        ttk.Label(container, text="Find").grid(row=0, column=0, sticky="w", padx=(0, 8))
        entry = ttk.Entry(container, textvariable=self.find_text_var, width=28, font=("Segoe UI", 9, "bold italic"))
        entry.grid(row=0, column=1, sticky="ew")
        self.find_entry = entry

        buttons = ttk.Frame(container)
        buttons.grid(row=1, column=0, columnspan=2, sticky="e", pady=(12, 0))
        ttk.Button(buttons, text="Find Next", command=self._run_find_next).grid(row=0, column=0, padx=(0, 6))
        ttk.Button(buttons, text="Cancel", command=self._close_find_dialog).grid(row=0, column=1)

        entry.focus_set()
        entry.selection_range(0, "end")
        dialog.bind("<Return>", lambda _event: self._run_find_next())
        dialog.bind("<Escape>", lambda _event: self._close_find_dialog())

    def _close_find_dialog(self) -> None:
        if self.find_dialog is not None:
            try:
                self.find_dialog.destroy()
            except Exception:
                pass
        self.find_dialog = None
        self.find_entry = None

    def _run_find_next(self) -> None:
        needle = self.find_text_var.get().strip()
        if not needle:
            messagebox.showinfo(APP_TITLE, "Enter text to find.", parent=self.find_dialog or self)
            return
        query_changed = needle != self.find_last_query or self.find_last_doc_index != self.current_doc_index
        start_after = None if query_changed else self.find_last_match
        match = self._find_next_match(needle, start_after)
        if match is None and not query_changed:
            self.find_last_match = None
            match = self._find_next_match(needle, None)
        if match is None:
            messagebox.showinfo(APP_TITLE, f"No match found for '{needle}'.", parent=self.find_dialog or self)
            return
        row_index, column_index = match
        self.find_last_query = needle
        self.find_last_match = match
        self.find_last_doc_index = self.current_doc_index
        self.selection_anchor = match
        self.selection_focus = match
        self._scroll_to_cell(row_index, column_index)
        self.status_var.set(f"Found '{needle}' at row {row_index + 1}, column {column_index + 1}.")
        self._redraw()

    def _find_next_match(self, needle: str, start_after: Optional[Tuple[int, int]]) -> Optional[Tuple[int, int]]:
        lowered = needle.lower()
        start_row = 0
        start_column = 0
        if start_after is not None:
            start_row, start_column = start_after
            start_column += 1

        for row_index in range(start_row, len(self.loaded_rows)):
            row = self.loaded_rows[row_index]
            col_start = start_column if row_index == start_row else 0
            for column_index in range(col_start, len(row)):
                if lowered in str(row[column_index]).lower():
                    return row_index, column_index
        return None

    def _scroll_to_cell(self, row_index: int, column_index: int) -> None:
        frozen_rows = self._frozen_row_count()
        frozen_columns = self._frozen_column_count()
        if row_index >= frozen_rows:
            visible_rows = max(1, self._body_visible_row_count())
            target_row_offset = row_index - frozen_rows - (visible_rows // 2)
            self.body_row_offset = max(0, target_row_offset)
        if column_index >= frozen_columns:
            visible_columns = max(1, self._body_visible_column_count())
            target_col_offset = column_index - frozen_columns - (visible_columns // 2)
            self.body_col_offset = max(0, target_col_offset)
        self._clamp_offsets()

    def _ensure_cell_visible(self, row_index: int, column_index: int) -> None:
        frozen_rows = self._frozen_row_count()
        frozen_columns = self._frozen_column_count()
        if row_index >= frozen_rows:
            visible_rows = max(1, self._body_visible_row_count())
            visible_row_start = frozen_rows + self.body_row_offset
            visible_row_end = visible_row_start + visible_rows - 1
            if row_index < visible_row_start:
                self.body_row_offset = max(0, row_index - frozen_rows)
            elif row_index > visible_row_end:
                self.body_row_offset = max(0, row_index - frozen_rows - visible_rows + 1)
        if column_index >= frozen_columns:
            visible_columns = max(1, self._body_visible_column_count())
            visible_col_start = frozen_columns + self.body_col_offset
            visible_col_end = visible_col_start + visible_columns - 1
            if column_index < visible_col_start:
                self.body_col_offset = max(0, column_index - frozen_columns)
            elif column_index > visible_col_end:
                self.body_col_offset = max(0, column_index - frozen_columns - visible_columns + 1)
        self._clamp_offsets()

    def _position_selected_cell(self, row_index: int, column_index: int) -> None:
        if self.center_selection_var.get():
            self._scroll_to_cell(row_index, column_index)
        else:
            self._ensure_cell_visible(row_index, column_index)

    def open_file(self) -> None:
        initial_dir = str(self.current_path.parent) if self.current_path else str(self.last_open_dir)
        path_str = filedialog.askopenfilename(title="Open text file", initialdir=initial_dir, filetypes=SUPPORTED_FILETYPES)
        if path_str:
            self._open_document(Path(path_str))

    def reload_file(self) -> None:
        if self.current_path is None:
            messagebox.showinfo(APP_TITLE, "Open a text file first.")
            return
        if self.current_doc_index is None:
            self._open_document(self.current_path)
            return
        self._load_file_into_document(self.current_path, self.current_doc_index)

    def save_file(self) -> None:
        if self.current_doc_index is None or self.current_path is None:
            messagebox.showinfo(APP_TITLE, "Open a text file first.")
            return
        try:
            self._write_current_document(self.current_path)
        except Exception as exc:
            messagebox.showerror(APP_TITLE, f"Could not save file:\n{exc}")
            return
        self.status_var.set(f"Saved {self.current_path.name}")

    def save_file_as(self) -> None:
        if self.current_doc_index is None or self.current_path is None:
            messagebox.showinfo(APP_TITLE, "Open a text file first.")
            return
        path_str = filedialog.asksaveasfilename(
            title="Save text file as",
            initialdir=str(self.current_path.parent if self.current_path.parent.exists() else self.last_open_dir),
            initialfile=self.current_path.name,
            filetypes=SUPPORTED_FILETYPES,
            defaultextension=self.current_path.suffix or ".txt",
        )
        if not path_str:
            return
        new_path = Path(path_str)
        try:
            self._write_current_document(new_path)
        except Exception as exc:
            messagebox.showerror(APP_TITLE, f"Could not save file:\n{exc}")
            return
        document = self.documents[self.current_doc_index]
        document["path"] = new_path
        self.current_path = new_path
        self.path_var.set(str(new_path))
        if self.document_tabs is not None and document.get("tab_frame") is not None:
            self.document_tabs.tab(document["tab_frame"], text=new_path.name)
        if new_path.parent.exists():
            self.last_open_dir = new_path.parent
            self._save_settings()
        self._refresh_workspace_tree()
        self.status_var.set(f"Saved as {new_path.name}")

    def choose_backup_folder(self) -> Optional[Path]:
        initial_dir = str(self.backup_dir or (self.current_path.parent if self.current_path else self.last_open_dir))
        folder = filedialog.askdirectory(title="Choose backup folder", initialdir=initial_dir, mustexist=True)
        if not folder:
            return None
        path = Path(folder)
        self.backup_dir = path
        self._save_settings()
        self.status_var.set(f"Backup folder set to {path}")
        return path

    def backup_file(self) -> None:
        if self.current_doc_index is None or self.current_path is None:
            messagebox.showinfo(APP_TITLE, "Open a text file first.")
            return
        backup_dir = self.backup_dir
        if backup_dir is None or not backup_dir.exists():
            backup_dir = self.choose_backup_folder()
            if backup_dir is None:
                return
        backup_path = backup_dir / self.current_path.name
        try:
            self._write_current_document(backup_path)
        except Exception as exc:
            messagebox.showerror(APP_TITLE, f"Could not create backup:\n{exc}")
            return
        self.status_var.set(f"Backed up {self.current_path.name} to {backup_path}")

    def clear_table(self) -> None:
        if self.current_doc_index is not None:
            self._close_current_document()
            return
        self.current_path = None
        self.current_doc_index = None
        self.loaded_columns = []
        self.loaded_rows = []
        self.loaded_details = ""
        self.column_widths = []
        self.row_heights = []
        self.selection_anchor = None
        self.selection_focus = None
        self.path_var.set("No file loaded")
        self.info_var.set("")
        self.status_var.set("Cleared the grid.")
        self._refresh_workspace_tree()
        self._reset_view()
        self._redraw()

    def _open_document(self, path: Path) -> None:
        for index, document in enumerate(self.documents):
            if document["path"] == path:
                self._activate_document(index)
                return
        new_index = len(self.documents)
        self.documents.append(self._empty_document(path))
        if self.document_tabs is not None:
            tab_frame = ttk.Frame(self.document_tabs)
            self.document_tabs.add(tab_frame, text=path.name)
            self.documents[new_index]["tab_frame"] = tab_frame
        self._load_file_into_document(path, new_index)

    def _load_file_into_document(self, path: Path, document_index: int) -> None:
        try:
            columns, rows, details, delimiter, use_first_row_as_header = self._read_table(path)
        except Exception as exc:
            messagebox.showerror(APP_TITLE, f"Could not open file:\n{exc}")
            self.status_var.set(f"Failed to open {path.name}")
            return

        document = self.documents[document_index]
        document.update(
            {
                "path": path,
                "columns": columns,
                "rows": rows,
                "details": details,
                "delimiter": delimiter,
                "use_first_row_as_header": use_first_row_as_header,
                "column_widths": [self._measure_column_width(name, index, rows) for index, name in enumerate(columns)],
                "row_heights": [DEFAULT_ROW_HEIGHT for _ in rows],
                "body_row_offset": 0,
                "body_col_offset": 0,
                "selection_anchor": None,
                "selection_focus": None,
                "lock_rows": document.get("lock_rows", False),
                "lock_columns": document.get("lock_columns", True),
                "lock_row_count": document.get("lock_row_count", 1),
                "lock_column_count": document.get("lock_column_count", 1),
            }
        )
        if self.document_tabs is not None and document.get("tab_frame") is not None:
            self.document_tabs.tab(document["tab_frame"], text=path.name)
        self._activate_document(document_index)

    def _read_table(self, path: Path) -> Tuple[List[str], List[List[str]], str, Optional[str], bool]:
        text = path.read_text(encoding="utf-8-sig")
        lines = text.splitlines()
        delimiter_name, delimiter = self._detect_delimiter(path, lines)
        parsed_rows = self._parse_rows(lines, delimiter)
        max_columns = max((len(row) for row in parsed_rows), default=1)
        normalized_rows = [row + ([""] * (max_columns - len(row))) for row in parsed_rows]
        columns, use_first_row_as_header = self._make_column_names(normalized_rows, delimiter is not None)
        data_rows = normalized_rows[1:] if use_first_row_as_header else normalized_rows
        preview_rows = data_rows[:MAX_PREVIEW_ROWS]

        details = (
            f"Format: {delimiter_name} | "
            f"Columns: {len(columns)} | "
            f"Rows: {len(preview_rows)} of {len(data_rows)} | "
            f"Size: {path.stat().st_size:,} bytes"
        )
        if len(data_rows) > MAX_PREVIEW_ROWS:
            details += f" | Preview limited to first {MAX_PREVIEW_ROWS:,} rows"
        return columns, preview_rows, details, delimiter, use_first_row_as_header

    def _detect_delimiter(self, path: Path, lines: Sequence[str]) -> Tuple[str, Optional[str]]:
        suffix = path.suffix.lower()
        if suffix in {".tsv", ".tab"}:
            return "Tab separated", "\t"
        if suffix == ".csv":
            return "Comma separated", ","

        sample_lines = [line for line in lines[:25] if line.strip()]
        if not sample_lines:
            return "Plain text", None

        candidates = [("\t", "Tab separated"), (",", "Comma separated"), ("|", "Pipe separated"), (";", "Semicolon separated")]
        best_name = "Plain text"
        best_delimiter: Optional[str] = None
        best_score = 1
        for delimiter, name in candidates:
            counts = [len(line.split(delimiter)) for line in sample_lines if delimiter in line]
            if counts and min(counts) >= 2 and min(counts) > best_score:
                best_score = min(counts)
                best_name = name
                best_delimiter = delimiter
        return best_name, best_delimiter

    def _parse_rows(self, lines: Sequence[str], delimiter: Optional[str]) -> List[List[str]]:
        if delimiter is None:
            return [[line] for line in lines]
        return [list(row) for row in csv.reader(lines, delimiter=delimiter)]

    def _make_column_names(self, rows: Sequence[Sequence[str]], parsed_as_table: bool) -> Tuple[List[str], bool]:
        if not rows:
            return ["Column 1"], False
        first_row = [cell.strip() for cell in rows[0]]
        use_first_row_as_header = parsed_as_table and self._looks_like_header(first_row)
        header_source = first_row if use_first_row_as_header else [f"Column {index + 1}" for index in range(len(first_row))]
        seen: dict[str, int] = {}
        headers: List[str] = []
        for index, name in enumerate(header_source):
            base = name or f"Column {index + 1}"
            seen[base] = seen.get(base, 0) + 1
            headers.append(base if seen[base] == 1 else f"{base} ({seen[base]})")
        return headers, use_first_row_as_header

    def _looks_like_header(self, row: Sequence[str]) -> bool:
        if not any(row):
            return False
        text_cells = sum(1 for cell in row if any(character.isalpha() for character in cell))
        return text_cells >= max(1, len(row) // 2)

    def _measure_column_width(self, header: str, index: int, rows: Sequence[Sequence[str]]) -> int:
        sample_values = [row[index] for row in rows[:40] if index < len(row)]
        header_length = max(8, len(header or f"Column {index + 1}"))
        value_length = max((len(str(value)) for value in sample_values), default=0)
        # Favor the header width so full column names stay visible by default.
        longest = max(header_length + 2, value_length)
        return self._clamp_size((longest * 8) + 22, MIN_COLUMN_WIDTH, MAX_COLUMN_WIDTH)

    def _empty_document(self, path: Path) -> dict:
        return {
            "path": path,
            "columns": [],
            "rows": [],
            "details": "",
            "delimiter": None,
            "use_first_row_as_header": False,
            "column_widths": [],
            "row_heights": [],
            "body_row_offset": 0,
            "body_col_offset": 0,
            "selection_anchor": None,
            "selection_focus": None,
            "marked_rows": [],
            "marked_columns": [],
            "lock_rows": False,
            "lock_columns": True,
            "lock_row_count": 1,
            "lock_column_count": 1,
                "tab_frame": None,
        }

    def _capture_current_document_state(self) -> None:
        if self.current_doc_index is None or self.current_doc_index >= len(self.documents):
            return
        document = self.documents[self.current_doc_index]
        document["body_row_offset"] = self.body_row_offset
        document["body_col_offset"] = self.body_col_offset
        document["selection_anchor"] = self.selection_anchor
        document["selection_focus"] = self.selection_focus
        document["marked_rows"] = sorted(self.marked_rows)
        document["marked_columns"] = sorted(self.marked_columns)
        document["column_widths"] = list(self.column_widths)
        document["row_heights"] = list(self.row_heights)
        document["lock_rows"] = self.lock_rows_var.get()
        document["lock_columns"] = self.lock_columns_var.get()
        document["lock_row_count"] = self.lock_row_count_var.get()
        document["lock_column_count"] = self.lock_column_count_var.get()

    def _activate_document(self, document_index: int) -> None:
        if document_index < 0 or document_index >= len(self.documents):
            return
        self._capture_current_document_state()
        document = self.documents[document_index]
        self.current_doc_index = document_index
        self.current_path = document["path"]
        if self.current_path.parent.exists():
            self.last_open_dir = self.current_path.parent
            self._save_settings()
        self.loaded_columns = list(document["columns"])
        self.loaded_rows = [list(row) for row in document["rows"]]
        self.loaded_details = document["details"]
        self.column_widths = list(document["column_widths"])
        self.row_heights = list(document["row_heights"])
        self._ensure_header_widths()
        self.body_row_offset = int(document["body_row_offset"])
        self.body_col_offset = int(document["body_col_offset"])
        self.selection_anchor = document["selection_anchor"]
        self.selection_focus = document["selection_focus"]
        self.marked_rows = set(document.get("marked_rows", []))
        self.marked_columns = set(document.get("marked_columns", []))
        self.lock_rows_var.set(bool(document["lock_rows"]))
        self.lock_columns_var.set(bool(document["lock_columns"]))
        self.lock_row_count_var.set(int(document["lock_row_count"]))
        self.lock_column_count_var.set(int(document["lock_column_count"]))
        self.path_var.set(str(self.current_path))
        self._refresh_workspace_tree()
        self._update_info()
        self.status_var.set(f"Loaded {self.current_path.name}")
        if self.document_tabs is not None and document.get("tab_frame") is not None:
            current_tab = self.document_tabs.select()
            target_tab = str(document["tab_frame"])
            if current_tab != target_tab:
                self.document_tabs.select(document["tab_frame"])
        self._redraw()
        self._focus_grid_for_navigation()

    def _ensure_header_widths(self) -> None:
        if not self.loaded_columns:
            return
        recalculated = [self._measure_column_width(name, index, self.loaded_rows) for index, name in enumerate(self.loaded_columns)]
        if not self.column_widths:
            self.column_widths = recalculated
            return
        while len(self.column_widths) < len(recalculated):
            self.column_widths.append(recalculated[len(self.column_widths)])
        self.column_widths = [max(current, required) for current, required in zip(self.column_widths[: len(recalculated)], recalculated)]

    def _close_current_document(self) -> None:
        if self.current_doc_index is None or self.current_doc_index >= len(self.documents):
            return
        closing_index = self.current_doc_index
        self._capture_current_document_state()
        document = self.documents.pop(closing_index)
        if self.document_tabs is not None and document.get("tab_frame") is not None:
            self.document_tabs.forget(document["tab_frame"])
        if not self.documents:
            self.current_doc_index = None
            self.current_path = None
            self.loaded_columns = []
            self.loaded_rows = []
            self.loaded_details = ""
            self.column_widths = []
            self.row_heights = []
            self.selection_anchor = None
            self.selection_focus = None
            self.marked_rows = set()
            self.marked_columns = set()
            self.path_var.set("No file loaded")
            self.info_var.set("")
            self.status_var.set("Closed the last document.")
            self._refresh_workspace_tree()
            self._reset_view()
            self._redraw()
            return
        next_index = min(closing_index, len(self.documents) - 1)
        self._activate_document(next_index)

    def _close_document_at_index(self, document_index: int) -> None:
        if document_index < 0 or document_index >= len(self.documents):
            return
        current_index = self.current_doc_index
        if current_index == document_index:
            self._close_current_document()
            return
        if current_index is not None:
            self._capture_current_document_state()
        document = self.documents.pop(document_index)
        if self.document_tabs is not None and document.get("tab_frame") is not None:
            self.document_tabs.forget(document["tab_frame"])
        if not self.documents:
            self.current_doc_index = None
            self.current_path = None
            self.loaded_columns = []
            self.loaded_rows = []
            self.loaded_details = ""
            self.column_widths = []
            self.row_heights = []
            self.selection_anchor = None
            self.selection_focus = None
            self.marked_rows = set()
            self.marked_columns = set()
            self.path_var.set("No file loaded")
            self.info_var.set("")
            self.status_var.set("Closed the last document.")
            self._refresh_workspace_tree()
            self._reset_view()
            self._redraw()
            return
        if current_index is None:
            next_index = min(document_index, len(self.documents) - 1)
        elif document_index < current_index:
            next_index = current_index - 1
        else:
            next_index = current_index
        self._activate_document(next_index)

    def _on_tab_changed(self, _event: tk.Event) -> None:
        if self.document_tabs is None:
            return
        selected = self.document_tabs.select()
        if not selected:
            return
        for index, document in enumerate(self.documents):
            if str(document.get("tab_frame")) == selected:
                if self.current_doc_index != index:
                    self._activate_document(index)
                return

    def _show_tab_menu(self, event: tk.Event) -> str:
        if self.document_tabs is None or self.tab_menu is None:
            return "break"
        clicked_index = self.document_tabs.index(f"@{event.x},{event.y}")
        if clicked_index is None:
            return "break"
        self.tab_menu_index = int(clicked_index)
        self.tab_menu.tk_popup(event.x_root, event.y_root)
        self.tab_menu.grab_release()
        return "break"

    def _close_tab_from_menu(self) -> None:
        if self.tab_menu_index is None:
            return
        index = self.tab_menu_index
        self.tab_menu_index = None
        self._close_document_at_index(index)

    def _refresh_workspace_tree(self) -> None:
        if self.workspace_tree is None:
            return
        self.workspace_refreshing = True
        self.workspace_tree.delete(*self.workspace_tree.get_children())
        if self.current_path is None:
            self.workspace_refreshing = False
            return

        try:
            parents = list(self.current_path.parents)
            parents.reverse()
            parent_iid = ""
            for path_part in parents:
                node_id = str(path_part)
                label = path_part.name or str(path_part)
                if not self.workspace_tree.exists(node_id):
                    self.workspace_tree.insert(parent_iid, "end", iid=node_id, text=label, open=True)
                parent_iid = node_id

            if self.current_path.suffix.lower() == ".txt":
                base_dir = self.current_path.parent
                txt_files = sorted([path for path in base_dir.glob("*.txt") if path.is_file()], key=lambda item: item.name.lower())
                for file_path in txt_files:
                    file_id = str(file_path)
                    if not self.workspace_tree.exists(file_id):
                        self.workspace_tree.insert(parent_iid, "end", iid=file_id, text=file_path.name, open=False)
                current_id = str(self.current_path)
                if self.workspace_tree.exists(current_id):
                    self.workspace_tree.selection_set(current_id)
                    self.workspace_tree.focus(current_id)
                    self.workspace_tree.see(current_id)
            else:
                current_id = str(self.current_path)
                if not self.workspace_tree.exists(current_id):
                    self.workspace_tree.insert(parent_iid, "end", iid=current_id, text=self.current_path.name or str(self.current_path), open=False)
                self.workspace_tree.selection_set(current_id)
                self.workspace_tree.focus(current_id)
                self.workspace_tree.see(current_id)
        except Exception:
            fallback_id = str(self.current_path)
            self.workspace_tree.insert("", "end", iid=fallback_id, text=str(self.current_path), open=False)
        self.workspace_refreshing = False

    def _on_workspace_tree_select(self, _event: tk.Event) -> str:
        if self.workspace_refreshing or self.workspace_tree is None:
            return "break"
        selection = self.workspace_tree.selection()
        if not selection:
            return "break"
        selected_path = Path(selection[0])
        if not selected_path.is_file():
            return "break"
        if self.current_path is not None and selected_path == self.current_path:
            return "break"
        try:
            self._open_document(selected_path)
        except Exception:
            return "break"
        return "break"

    def _reset_view(self) -> None:
        self.body_row_offset = 0
        self.body_col_offset = 0
        self._update_scrollbars()

    def _clamp_offsets(self) -> None:
        frozen_row_count = self._frozen_row_count()
        frozen_column_count = self._frozen_column_count()
        max_row_offset = max(0, len(self.loaded_rows) - frozen_row_count - self._body_visible_row_count())
        max_col_offset = max(0, len(self.loaded_columns) - frozen_column_count - self._body_visible_column_count())
        self.body_row_offset = max(0, min(max_row_offset, int(self.body_row_offset)))
        self.body_col_offset = max(0, min(max_col_offset, int(self.body_col_offset)))

    def _frozen_row_count(self) -> int:
        if not self.lock_rows_var.get() or not self.loaded_rows:
            return 0
        return max(0, min(len(self.loaded_rows), int(self.lock_row_count_var.get() or 0)))

    def _frozen_column_count(self) -> int:
        if not self.lock_columns_var.get() or not self.loaded_columns:
            return 0
        return max(0, min(len(self.loaded_columns), int(self.lock_column_count_var.get() or 0)))

    def _frozen_rows_height(self) -> int:
        return sum(self.row_heights[: self._frozen_row_count()])

    def _on_freeze_option_changed(self) -> None:
        self.body_row_offset = 0
        self.body_col_offset = 0
        self._clamp_offsets()
        self._update_info()
        self._redraw()
        self._capture_current_document_state()

    def _update_info(self) -> None:
        frozen_rows = self._frozen_row_count()
        frozen_columns = self._frozen_column_count()
        self.info_var.set(
            f"{self.loaded_details} | Locked rows: {frozen_rows} | Locked columns: {frozen_columns} | Right-click headers to resize | Right-click cells or use Ctrl+C / Ctrl+V"
        )
        self.total_var.set(f"Rows: {len(self.loaded_rows)} | Columns: {len(self.loaded_columns)}")

    def _on_center_selection_changed(self) -> None:
        self._save_settings()
        focus_cell = self._selected_single_cell()
        if focus_cell is not None:
            self._position_selected_cell(*focus_cell)
            self._redraw()
        self._focus_grid_for_navigation()

    def _on_font_option_changed(self) -> None:
        self.cell_font_size_var.set(max(6, int(self.cell_font_size_var.get() or 9)))
        if self.editor_entry is not None:
            self.editor_entry.configure(font=self._cell_font())
        self._save_settings()
        self._focus_grid_for_navigation()
        self._redraw()

    def _cell_font(self) -> Tuple[str, int, str]:
        weight = "bold" if self.cell_bold_var.get() else "normal"
        return ("Segoe UI", max(6, int(self.cell_font_size_var.get() or 9)), weight)

    def _focus_grid_for_navigation(self) -> None:
        if self.editor_entry is not None:
            return
        target = self.body_canvas or self.top_canvas or self.left_canvas or self.corner_canvas
        if target is not None:
            try:
                target.focus_set()
            except Exception:
                pass

    def _start_selection(self, event: tk.Event) -> str:
        if self.resize_mode is not None:
            return "break"
        self.drag_widget = event.widget
        self.drag_last_x = event.x
        self.drag_last_y = event.y
        header_selection = self._header_selection(event.widget, event.x, event.y)
        if header_selection is not None:
            self.selection_anchor, self.selection_focus = header_selection
            self._redraw()
            return "break"
        hit = self._hit_test_cell(event.widget, event.x, event.y)
        if hit is None:
            self._cancel_drag_autoscroll()
            self.selection_anchor = None
            self.selection_focus = None
            self.drag_widget = None
            self._redraw()
            return "break"
        self.selection_anchor = hit
        self.selection_focus = hit
        self._position_selected_cell(*hit)
        self._redraw()
        return "break"

    def _drag_selection(self, event: tk.Event) -> str:
        if self.resize_mode is not None:
            self._perform_resize(event)
            return "break"
        if self.selection_anchor is None:
            return "break"
        self.drag_widget = event.widget
        self.drag_last_x = event.x
        self.drag_last_y = event.y
        if self._extend_header_selection(event.widget, event.x, event.y):
            self._schedule_drag_autoscroll()
            return "break"
        if self._selection_is_header_locked():
            return "break"
        hit = self._hit_test_cell(event.widget, event.x, event.y)
        if hit is not None:
            self.selection_focus = hit
            self._redraw()
        self._schedule_drag_autoscroll()
        return "break"

    def _finish_selection(self, event: tk.Event) -> str:
        if self.resize_mode is not None:
            self._finish_resize()
            return "break"
        if self.selection_anchor is None:
            return "break"
        self._cancel_drag_autoscroll()
        if self._extend_header_selection(event.widget, event.x, event.y):
            self.drag_widget = None
            return "break"
        if self._selection_is_header_locked():
            return "break"
        hit = self._hit_test_cell(event.widget, event.x, event.y)
        if hit is not None:
            self.selection_focus = hit
            self._redraw()
        self.drag_widget = None
        return "break"

    def _start_resize_or_selection(self, event: tk.Event) -> str:
        resize_hit = self._resize_hit_test(event.widget, event.x, event.y)
        if resize_hit is None:
            return self._start_selection(event)
        mode, index = resize_hit
        self._push_undo_state("resize")
        self.resize_mode = mode
        self.resize_index = index
        self.resize_widget = event.widget
        self.resize_start_x = event.x_root
        self.resize_start_y = event.y_root
        self.resize_start_local_x = event.x
        self.resize_start_local_y = event.y
        self.resize_widget_root_x = event.widget.winfo_rootx()
        self.resize_widget_root_y = event.widget.winfo_rooty()
        self.resize_widget_width = event.widget.winfo_width()
        self.resize_widget_height = event.widget.winfo_height()
        self.resize_origin_size = self.column_widths[index] if mode == "column" else self.row_heights[index]
        self.resize_last_size = self.resize_origin_size
        self._cancel_drag_autoscroll()
        return "break"

    def _perform_resize(self, event: tk.Event) -> None:
        if self.resize_mode is None or self.resize_index is None or self.resize_widget is None:
            return
        if self.resize_mode == "column":
            local_x = self.winfo_pointerx() - self.resize_widget_root_x
            local_y = self.winfo_pointery() - self.resize_widget_root_y
            if (
                local_x < 0
                or local_x > self.resize_widget_width
                or local_y < 0
                or local_y > self.resize_widget_height
            ):
                return
            clamped_x = max(0, min(self.resize_widget_width, local_x))
            delta = clamped_x - self.resize_start_local_x
            self.resize_last_size = self._clamp_size(self.resize_origin_size + delta, MIN_COLUMN_WIDTH, MAX_COLUMN_WIDTH)
            self.column_widths[self.resize_index] = self.resize_last_size
            self.status_var.set(f"Column '{self.loaded_columns[self.resize_index]}' width: {self.column_widths[self.resize_index]}px")
        else:
            local_x = self.winfo_pointerx() - self.resize_widget_root_x
            local_y = self.winfo_pointery() - self.resize_widget_root_y
            if (
                local_x < 0
                or local_x > self.resize_widget_width
                or local_y < 0
                or local_y > self.resize_widget_height
            ):
                return
            clamped_y = max(0, min(self.resize_widget_height, local_y))
            delta = clamped_y - self.resize_start_local_y
            self.resize_last_size = self._clamp_size(self.resize_origin_size + delta, MIN_ROW_HEIGHT, MAX_ROW_HEIGHT)
            self.row_heights[self.resize_index] = self.resize_last_size
            self.status_var.set(f"Row {self.resize_index + 1} height: {self.row_heights[self.resize_index]}px")
        self._schedule_resize_redraw()

    def _finish_resize(self) -> None:
        self.resize_mode = None
        self.resize_index = None
        self.resize_widget = None
        self.resize_widget_width = 0
        self.resize_widget_height = 0
        self._run_resize_redraw()
        if self.top_canvas is not None:
            self.top_canvas.configure(cursor="")
        if self.left_canvas is not None:
            self.left_canvas.configure(cursor="")
        if self.corner_canvas is not None:
            self.corner_canvas.configure(cursor="")
        self._capture_current_document_state()

    def _selection_bounds(self) -> Optional[Tuple[int, int, int, int]]:
        if self.selection_anchor is None or self.selection_focus is None:
            return None
        row1, col1 = self.selection_anchor
        row2, col2 = self.selection_focus
        return min(row1, row2), max(row1, row2), min(col1, col2), max(col1, col2)

    def _is_selected(self, row_index: int, column_index: int) -> bool:
        bounds = self._selection_bounds()
        if bounds is None:
            return False
        min_row, max_row, min_col, max_col = bounds
        return min_row <= row_index <= max_row and min_col <= column_index <= max_col

    def _selection_is_header_locked(self) -> bool:
        if self.selection_anchor is None or self.selection_focus is None:
            return False
        max_row_index = max(0, len(self.loaded_rows) - 1)
        max_col_index = max(0, len(self.loaded_columns) - 1)
        row1, col1 = self.selection_anchor
        row2, col2 = self.selection_focus
        return (
            (row1 == 0 and row2 == max_row_index and col1 == col2)
            or (col1 == 0 and col2 == max_col_index and row1 == row2)
        )

    def _extend_header_selection(self, widget: tk.Widget, x: int, y: int) -> bool:
        column_indices = self._selected_column_indices()
        row_indices = self._selected_row_indices()
        max_row_index = max(0, len(self.loaded_rows) - 1)
        max_col_index = max(0, len(self.loaded_columns) - 1)

        if column_indices and widget in (self.top_canvas, self.corner_canvas):
            column_index = self._column_from_header_click(widget, x)
            if column_index is not None:
                anchor_col = min(column_indices)
                self.selection_anchor = (0, anchor_col)
                self.selection_focus = (max_row_index, column_index)
                self._redraw()
                return True

        if row_indices and widget in (self.left_canvas, self.corner_canvas):
            row_index = self._row_from_click(widget, y)
            if row_index is not None:
                anchor_row = min(row_indices)
                self.selection_anchor = (anchor_row, 0)
                self.selection_focus = (row_index, max_col_index)
                self._redraw()
                return True
        return False

    def _selected_column_indices(self) -> List[int]:
        bounds = self._selection_bounds()
        if bounds is None or not self.loaded_rows:
            return []
        min_row, max_row, min_col, max_col = bounds
        if min_row != 0 or max_row != len(self.loaded_rows) - 1:
            return []
        return list(range(min_col, max_col + 1))

    def _selected_row_indices(self) -> List[int]:
        bounds = self._selection_bounds()
        if bounds is None or not self.loaded_columns:
            return []
        min_row, max_row, min_col, max_col = bounds
        if min_col != 0 or max_col != len(self.loaded_columns) - 1:
            return []
        return list(range(min_row, max_row + 1))

    def _resize_hit_test(self, widget: tk.Widget, x: int, y: int) -> Optional[Tuple[str, int]]:
        edge_margin = 4
        if widget in (self.top_canvas, self.corner_canvas) and y <= DEFAULT_ROW_HEIGHT:
            if widget == self.corner_canvas:
                running_x = ROW_NUMBER_WIDTH
                for column_index in range(self._frozen_column_count()):
                    running_x += self.column_widths[column_index]
                    if abs(x - running_x) <= edge_margin:
                        return "column", column_index
            else:
                running_x = 0
                for column_index in self._visible_columns(self._frozen_column_count() + self.body_col_offset, self.top_canvas.winfo_width() if self.top_canvas else 0):
                    running_x += self.column_widths[column_index]
                    if abs(x - running_x) <= edge_margin:
                        return "column", column_index
        if widget in (self.left_canvas, self.corner_canvas) and x <= ROW_NUMBER_WIDTH:
            if widget == self.corner_canvas:
                running_y = DEFAULT_ROW_HEIGHT
                for row_index in range(self._frozen_row_count()):
                    running_y += self.row_heights[row_index]
                    if abs(y - running_y) <= edge_margin:
                        return "row", row_index
            else:
                running_y = 0
                for row_index in self._visible_rows(self.body_row_offset + self._frozen_row_count(), self.left_canvas.winfo_height() if self.left_canvas else 0):
                    running_y += self.row_heights[row_index]
                    if abs(y - running_y) <= edge_margin:
                        return "row", row_index
        return None

    def _update_resize_cursor(self, event: tk.Event) -> str:
        hit = self._resize_hit_test(event.widget, event.x, event.y)
        if event.widget == self.top_canvas or event.widget == self.corner_canvas:
            if hit is not None and hit[0] == "column":
                event.widget.configure(cursor="sb_h_double_arrow")
                return "break"
        if event.widget == self.left_canvas or event.widget == self.corner_canvas:
            if hit is not None and hit[0] == "row":
                event.widget.configure(cursor="sb_v_double_arrow")
                return "break"
        event.widget.configure(cursor="")
        return "break"

    def _schedule_drag_autoscroll(self) -> None:
        if self.drag_autoscroll_job is not None:
            return
        self.drag_autoscroll_job = self.after(DRAG_AUTOSCROLL_DELAY_MS, self._run_drag_autoscroll)

    def _cancel_drag_autoscroll(self) -> None:
        if self.drag_autoscroll_job is None:
            return
        try:
            self.after_cancel(self.drag_autoscroll_job)
        except Exception:
            pass
        self.drag_autoscroll_job = None

    def _run_drag_autoscroll(self) -> None:
        self.drag_autoscroll_job = None
        if self.selection_anchor is None or self.drag_widget is None or self._selection_is_header_locked():
            return

        widget = self.drag_widget
        width = max(1, widget.winfo_width())
        height = max(1, widget.winfo_height())
        horizontal_step = self._edge_scroll_step(self.drag_last_x, width)
        vertical_step = self._edge_scroll_step(self.drag_last_y, height)

        if vertical_step:
            self._scroll_rows(vertical_step)
        if horizontal_step:
            self._scroll_columns(horizontal_step)

        pointer_x = self.winfo_pointerx() - widget.winfo_rootx()
        pointer_y = self.winfo_pointery() - widget.winfo_rooty()
        self.drag_last_x = pointer_x
        self.drag_last_y = pointer_y

        hit = self._hit_test_cell(widget, pointer_x, pointer_y)
        if hit is not None:
            self.selection_focus = hit
            self._redraw()

        if horizontal_step or vertical_step:
            self._schedule_drag_autoscroll()

    def _edge_scroll_step(self, pointer_pos: int, span: int) -> int:
        margin = min(DRAG_AUTOSCROLL_EDGE_MARGIN, max(8, span // 4))
        if pointer_pos < 0:
            return -DRAG_AUTOSCROLL_MAX_STEP
        if pointer_pos > span:
            return DRAG_AUTOSCROLL_MAX_STEP
        if pointer_pos <= margin:
            return -self._scaled_edge_step(margin - pointer_pos, margin)
        if pointer_pos >= span - margin:
            return self._scaled_edge_step(pointer_pos - (span - margin), margin)
        return 0

    def _scaled_edge_step(self, distance_into_margin: int, margin: int) -> int:
        if margin <= 0:
            return 1
        ratio = max(0.0, min(1.0, distance_into_margin / margin))
        step = 1 + int(round(ratio * (DRAG_AUTOSCROLL_MAX_STEP - 1)))
        return max(1, min(DRAG_AUTOSCROLL_MAX_STEP, step))

    def _header_selection(self, widget: tk.Widget, x: int, y: int) -> Optional[Tuple[Tuple[int, int], Tuple[int, int]]]:
        if not self.loaded_rows or not self.loaded_columns:
            return None
        max_row_index = len(self.loaded_rows) - 1
        max_col_index = len(self.loaded_columns) - 1

        if widget == self.top_canvas:
            column_index = self._column_from_header_click(widget, x)
            if column_index is None:
                return None
            return (0, column_index), (max_row_index, column_index)

        if widget == self.left_canvas and x <= ROW_NUMBER_WIDTH:
            row_index = self._row_from_click(widget, y)
            if row_index is None:
                return None
            return (row_index, 0), (row_index, max_col_index)

        if widget == self.corner_canvas:
            if y <= DEFAULT_ROW_HEIGHT and x > ROW_NUMBER_WIDTH:
                column_index = self._column_from_header_click(widget, x)
                if column_index is None:
                    return None
                return (0, column_index), (max_row_index, column_index)
            if x <= ROW_NUMBER_WIDTH and y > DEFAULT_ROW_HEIGHT:
                row_index = self._row_from_click(widget, y)
                if row_index is None:
                    return None
                return (row_index, 0), (row_index, max_col_index)
        return None

    def _on_mousewheel(self, event: tk.Event) -> str:
        delta = -1 if event.delta > 0 else 1
        self._scroll_rows(delta)
        return "break"

    def _on_vertical_scroll(self, action: str, value: str, units: Optional[str] = None) -> None:
        if self.resize_mode is not None:
            return
        frozen_row_count = self._frozen_row_count()
        scrollable_rows = max(0, len(self.loaded_rows) - frozen_row_count)
        if action == "moveto":
            visible_rows = self._body_visible_row_count()
            max_offset = max(0, scrollable_rows - visible_rows)
            self.body_row_offset = int(round(float(value) * max_offset))
        elif action == "scroll":
            step = int(value)
            multiplier = self._body_visible_row_count() if units == "pages" else 1
            self._scroll_rows(step * multiplier)
            return
        self._clamp_offsets()
        self._update_scrollbars()
        self._redraw()

    def _on_horizontal_scroll(self, action: str, value: str, units: Optional[str] = None) -> None:
        if self.resize_mode is not None:
            return
        frozen_column_count = self._frozen_column_count()
        scrollable_columns = max(0, len(self.loaded_columns) - frozen_column_count)
        if action == "moveto":
            visible_columns = self._body_visible_column_count()
            max_offset = max(0, scrollable_columns - visible_columns)
            self.body_col_offset = int(round(float(value) * max_offset))
        elif action == "scroll":
            step = int(value)
            multiplier = self._body_visible_column_count() if units == "pages" else 1
            self._scroll_columns(step * multiplier)
            return
        self._clamp_offsets()
        self._update_scrollbars()
        self._redraw()

    def _scroll_rows(self, amount: int) -> None:
        frozen_row_count = self._frozen_row_count()
        scrollable_rows = max(0, len(self.loaded_rows) - frozen_row_count)
        max_offset = max(0, scrollable_rows - self._body_visible_row_count())
        self.body_row_offset = max(0, min(max_offset, self.body_row_offset + amount))
        self._clamp_offsets()
        self._update_scrollbars()
        self._redraw()

    def _scroll_columns(self, amount: int) -> None:
        frozen_column_count = self._frozen_column_count()
        scrollable_columns = max(0, len(self.loaded_columns) - frozen_column_count)
        max_offset = max(0, scrollable_columns - self._body_visible_column_count())
        self.body_col_offset = max(0, min(max_offset, self.body_col_offset + amount))
        self._clamp_offsets()
        self._update_scrollbars()
        self._redraw()

    def _body_visible_row_count(self) -> int:
        if self.body_canvas is None:
            return 1
        height = max(1, self.body_canvas.winfo_height())
        used = 0
        count = 0
        start = self.body_row_offset + self._frozen_row_count()
        while start + count < len(self.row_heights):
            row_height = self.row_heights[start + count]
            if used + row_height > height and count > 0:
                break
            used += row_height
            count += 1
            if used >= height:
                break
        return max(1, count)

    def _body_visible_column_count(self) -> int:
        if self.body_canvas is None:
            return 1
        width = max(1, self.body_canvas.winfo_width())
        start_column = self.body_col_offset + self._frozen_column_count()
        return max(1, self._count_fit_columns(start_column, width))

    def _count_fit_columns(self, start_index: int, width: int) -> int:
        used = 0
        count = 0
        for column_width in self.column_widths[start_index:]:
            if used + column_width > width and count > 0:
                break
            used += column_width
            count += 1
            if used >= width:
                break
        return max(1, count)

    def _update_scrollbars(self) -> None:
        if self._y_scrollbar is None or self._x_scrollbar is None:
            return
        self._clamp_offsets()

        frozen_row_count = self._frozen_row_count()
        total_rows = max(0, len(self.loaded_rows) - frozen_row_count)
        visible_rows = min(total_rows, self._body_visible_row_count())
        row_end = self.body_row_offset + visible_rows
        if total_rows <= 0:
            self._y_scrollbar.set(0.0, 1.0)
        else:
            self._y_scrollbar.set(self.body_row_offset / total_rows, row_end / total_rows)

        frozen_column_count = self._frozen_column_count()
        total_columns = max(0, len(self.loaded_columns) - frozen_column_count)
        visible_columns = min(total_columns, self._body_visible_column_count())
        col_end = self.body_col_offset + visible_columns
        if total_columns <= 0:
            self._x_scrollbar.set(0.0, 1.0)
        else:
            self._x_scrollbar.set(self.body_col_offset / total_columns, col_end / total_columns)

    def _redraw(self) -> None:
        self._clamp_offsets()
        self._update_scrollbars()
        self._draw_corner()
        self._draw_top()
        self._draw_left()
        self._draw_body()
        if not self.defer_document_capture:
            self._capture_current_document_state()

    def _schedule_resize_redraw(self) -> None:
        self.defer_document_capture = True
        if self.resize_redraw_job is not None:
            return
        self.resize_redraw_job = self.after(RESIZE_REDRAW_DELAY_MS, self._run_resize_redraw)

    def _run_resize_redraw(self) -> None:
        if self.resize_redraw_job is not None:
            try:
                self.after_cancel(self.resize_redraw_job)
            except Exception:
                pass
            self.resize_redraw_job = None
        self.defer_document_capture = False
        self._redraw()

    def _draw_corner(self) -> None:
        if self.corner_canvas is None or self.corner_frame is None:
            return
        self.corner_canvas.delete("all")
        frozen_rows = self._frozen_row_count()
        frozen_columns = self._frozen_column_count()
        if not self.loaded_columns:
            self.corner_frame.grid_remove()
            return
        self.corner_frame.grid()
        frozen_width = sum(self.column_widths[:frozen_columns])
        width = max(ROW_NUMBER_WIDTH, ROW_NUMBER_WIDTH + frozen_width)
        height = DEFAULT_ROW_HEIGHT + self._frozen_rows_height()
        self.corner_canvas.configure(width=width, height=height)
        self._draw_cell(self.corner_canvas, 0, 0, ROW_NUMBER_WIDTH, DEFAULT_ROW_HEIGHT, "#", CORNER_BG, anchor="center", bold_text=True)
        x = ROW_NUMBER_WIDTH
        for column_index in range(frozen_columns):
            self._draw_cell(self.corner_canvas, x, 0, self.column_widths[column_index], DEFAULT_ROW_HEIGHT, self.loaded_columns[column_index], self._marker_bg(CORNER_BG, column_index=column_index), bold_text=True)
            x += self.column_widths[column_index]
        y = DEFAULT_ROW_HEIGHT
        for row_index in range(frozen_rows):
            row_height = self.row_heights[row_index]
            bg = self._marker_bg(FROZEN_BG if row_index % 2 == 0 else FROZEN_ALT_BG, row_index=row_index)
            self._draw_cell(self.corner_canvas, 0, y, ROW_NUMBER_WIDTH, row_height, str(row_index + 1), bg, anchor="center", bold_text=True)
            x = ROW_NUMBER_WIDTH
            for column_index in range(frozen_columns):
                cell_bg = self._marker_bg(bg, row_index=row_index, column_index=column_index)
                self._draw_cell(self.corner_canvas, x, y, self.column_widths[column_index], row_height, self._cell_text(row_index, column_index), cell_bg, selected=self._is_selected(row_index, column_index))
                x += self.column_widths[column_index]
            y += row_height

    def _draw_top(self) -> None:
        if self.top_canvas is None or self.top_frame is None:
            return
        self.top_canvas.delete("all")
        frozen_rows = self._frozen_row_count()
        frozen_columns = self._frozen_column_count()
        if not self.loaded_columns:
            self.top_frame.grid_remove()
            return
        self.top_frame.grid()
        fallback_width = self.body_canvas.winfo_width() if self.body_canvas is not None else 0
        canvas_width = max(1, self.top_canvas.winfo_width(), fallback_width)
        canvas_height = DEFAULT_ROW_HEIGHT + self._frozen_rows_height()
        self.top_canvas.configure(height=canvas_height)
        self.top_canvas.create_rectangle(0, 0, canvas_width, canvas_height, fill=HEADER_BG, outline="")
        start_column = frozen_columns + self.body_col_offset
        columns = self._visible_columns(start_column, canvas_width)
        if not columns and start_column < len(self.loaded_columns):
            columns = [start_column]
        x = 0
        for offset, column_index in enumerate(columns):
            bg = self._marker_bg(HEADER_BG if offset % 2 == 0 else HEADER_BG_ALT, column_index=column_index)
            header_text = self.loaded_columns[column_index] or f"Column {column_index + 1}"
            self._draw_cell(self.top_canvas, x, 0, self.column_widths[column_index], DEFAULT_ROW_HEIGHT, header_text, bg, bold_text=True)
            y = DEFAULT_ROW_HEIGHT
            for row_index in range(frozen_rows):
                row_height = self.row_heights[row_index]
                row_bg = self._marker_bg(FROZEN_BG if row_index % 2 == 0 else FROZEN_ALT_BG, row_index=row_index, column_index=column_index)
                self._draw_cell(self.top_canvas, x, y, self.column_widths[column_index], row_height, self._cell_text(row_index, column_index), row_bg, selected=self._is_selected(row_index, column_index))
                y += row_height
            x += self.column_widths[column_index]
        if x < canvas_width:
            self.top_canvas.create_rectangle(x, 0, canvas_width, DEFAULT_ROW_HEIGHT, fill=HEADER_BG, outline=GRID_LINE, width=1)
            if frozen_rows:
                fill_y = DEFAULT_ROW_HEIGHT
                for row_index in range(frozen_rows):
                    row_height = self.row_heights[row_index]
                    row_bg = FROZEN_BG if row_index % 2 == 0 else FROZEN_ALT_BG
                    self.top_canvas.create_rectangle(x, fill_y, canvas_width, fill_y + row_height, fill=row_bg, outline=GRID_LINE, width=1)
                    fill_y += row_height

    def _draw_left(self) -> None:
        if self.left_canvas is None or self.left_frame is None:
            return
        self.left_canvas.delete("all")
        frozen_columns = self._frozen_column_count()
        if not self.loaded_columns:
            self.left_frame.grid_remove()
            return
        self.left_frame.grid()
        width = max(ROW_NUMBER_WIDTH, ROW_NUMBER_WIDTH + sum(self.column_widths[:frozen_columns]))
        canvas_height = max(1, self.left_canvas.winfo_height())
        self.left_canvas.configure(width=width)
        self.left_canvas.create_rectangle(0, 0, width, canvas_height, fill=FROZEN_BG, outline="")
        start_row = self.body_row_offset + self._frozen_row_count()
        rows = self._visible_rows(start_row, self.left_canvas.winfo_height())
        if not rows and start_row < len(self.loaded_rows):
            rows = [start_row]
        y = 0
        for row_index in rows:
            row_height = self.row_heights[row_index]
            bg = self._marker_bg(FROZEN_BG if row_index % 2 == 0 else FROZEN_ALT_BG, row_index=row_index)
            self._draw_cell(self.left_canvas, 0, y, ROW_NUMBER_WIDTH, row_height, str(row_index + 1), bg, anchor="center", bold_text=True)
            x = ROW_NUMBER_WIDTH
            for column_index in range(frozen_columns):
                cell_bg = self._marker_bg(bg, row_index=row_index, column_index=column_index)
                self._draw_cell(self.left_canvas, x, y, self.column_widths[column_index], row_height, self._cell_text(row_index, column_index), cell_bg, selected=self._is_selected(row_index, column_index))
                x += self.column_widths[column_index]
            y += row_height
        if y < canvas_height:
            self.left_canvas.create_rectangle(0, y, width, canvas_height, fill=FROZEN_BG, outline=GRID_LINE, width=1)

    def _draw_body(self) -> None:
        if self.body_canvas is None:
            return
        self.body_canvas.delete("all")
        start_row = self.body_row_offset + self._frozen_row_count()
        start_column = self.body_col_offset + self._frozen_column_count()
        rows = self._visible_rows(start_row, self.body_canvas.winfo_height())
        columns = self._visible_columns(start_column, self.body_canvas.winfo_width())
        y = 0
        for row_index in rows:
            row_height = self.row_heights[row_index]
            bg = CELL_BG if row_index % 2 == 0 else CELL_ALT_BG
            x = 0
            for column_index in columns:
                cell_bg = self._marker_bg(bg, row_index=row_index, column_index=column_index)
                self._draw_cell(self.body_canvas, x, y, self.column_widths[column_index], row_height, self._cell_text(row_index, column_index), cell_bg, selected=self._is_selected(row_index, column_index))
                x += self.column_widths[column_index]
            if x < max(1, self.body_canvas.winfo_width()):
                self.body_canvas.create_rectangle(x, y, max(1, self.body_canvas.winfo_width()), y + row_height, fill=bg, outline=GRID_LINE, width=1)
            y += row_height
        if y < max(1, self.body_canvas.winfo_height()):
            self.body_canvas.create_rectangle(0, y, max(1, self.body_canvas.winfo_width()), max(1, self.body_canvas.winfo_height()), fill=CELL_BG, outline=GRID_LINE, width=1)

    def _visible_rows(self, start_row: int, canvas_height: int) -> List[int]:
        rows: List[int] = []
        used = 0
        height = max(1, canvas_height)
        row_index = max(0, start_row)
        while row_index < len(self.loaded_rows):
            row_height = self.row_heights[row_index]
            if used + row_height > height and rows:
                break
            rows.append(row_index)
            used += row_height
            row_index += 1
            if used >= height:
                break
        return rows

    def _visible_columns(self, start_column: int, canvas_width: int) -> List[int]:
        columns: List[int] = []
        used = 0
        width = max(1, canvas_width)
        for column_index in range(start_column, len(self.loaded_columns)):
            column_width = self.column_widths[column_index]
            if used + column_width > width and columns:
                break
            columns.append(column_index)
            used += column_width
            if used >= width:
                break
        return columns

    def _cell_text(self, row_index: int, column_index: int) -> str:
        if row_index >= len(self.loaded_rows):
            return ""
        row = self.loaded_rows[row_index]
        if column_index >= len(row):
            return ""
        return str(row[column_index])

    def _hit_test_cell(self, widget: tk.Widget, x: int, y: int) -> Optional[Tuple[int, int]]:
        if widget == self.body_canvas:
            return self._body_hit_test(x, y)
        if widget == self.top_canvas:
            return self._top_hit_test(x, y)
        if widget == self.left_canvas:
            return self._left_hit_test(x, y)
        if widget == self.corner_canvas:
            return self._corner_hit_test(x, y)
        return None

    def _begin_edit_from_event(self, event: tk.Event) -> str:
        hit = self._hit_test_cell(event.widget, event.x, event.y)
        if hit is None:
            return "break"
        self._begin_edit(hit)
        return "break"

    def _begin_edit(self, cell: Tuple[int, int], initial_text: Optional[str] = None, select_all: bool = True) -> None:
        row_index, column_index = cell
        if row_index < 0 or column_index < 0:
            return
        bbox = self._cell_bbox(row_index, column_index)
        if bbox is None:
            return
        self._cancel_edit()
        self._push_undo_state("cell edit")
        self.editing_cell = cell
        self.editing_var.set(self._cell_text(row_index, column_index) if initial_text is None else initial_text)
        entry = ttk.Entry(self, textvariable=self.editing_var, font=self._cell_font())
        self.editor_entry = entry
        x, y, width, height = bbox
        entry.place(x=x, y=y, width=max(24, width), height=max(20, height))
        entry.focus_set()
        if select_all:
            entry.selection_range(0, "end")
        else:
            entry.icursor("end")
        entry.bind("<Return>", lambda _event: self._commit_edit())
        entry.bind("<Up>", lambda _event: self._commit_edit_and_move(-1, 0))
        entry.bind("<Down>", lambda _event: self._commit_edit_and_move(1, 0))
        entry.bind("<Left>", lambda _event: self._commit_edit_and_move(0, -1))
        entry.bind("<Right>", lambda _event: self._commit_edit_and_move(0, 1))
        entry.bind("<Escape>", lambda _event: self._cancel_edit())
        entry.bind("<FocusOut>", lambda _event: self._commit_edit())

    def _commit_edit(self) -> None:
        if self.editing_cell is None:
            return
        row_index, column_index = self.editing_cell
        while row_index >= len(self.loaded_rows):
            self.loaded_rows.append([""] * len(self.loaded_columns))
            self.row_heights.append(DEFAULT_ROW_HEIGHT)
        while len(self.loaded_rows[row_index]) < len(self.loaded_columns):
            self.loaded_rows[row_index].append("")
        self.loaded_rows[row_index][column_index] = self.editing_var.get()
        self.selection_anchor = (row_index, column_index)
        self.selection_focus = (row_index, column_index)
        self._ensure_header_widths()
        self._cancel_edit(keep_value=True)
        self._capture_current_document_state()
        self.status_var.set(f"Updated row {row_index + 1}, column {column_index + 1}.")
        self._redraw()

    def _cancel_edit(self, keep_value: bool = False) -> None:
        if self.editor_entry is not None:
            try:
                self.editor_entry.place_forget()
                self.editor_entry.destroy()
            except Exception:
                pass
        self.editor_entry = None
        self.editing_cell = None
        if not keep_value:
            self.editing_var.set("")

    def _cell_bbox(self, row_index: int, column_index: int) -> Optional[Tuple[int, int, int, int]]:
        frozen_rows = self._frozen_row_count()
        frozen_columns = self._frozen_column_count()

        if row_index < frozen_rows and column_index < frozen_columns:
            return self._cell_bbox_in_corner(row_index, column_index)
        if row_index < frozen_rows and column_index >= frozen_columns:
            return self._cell_bbox_in_top(row_index, column_index)
        if row_index >= frozen_rows and column_index < frozen_columns:
            return self._cell_bbox_in_left(row_index, column_index)
        return self._cell_bbox_in_body(row_index, column_index)

    def _cell_bbox_in_corner(self, row_index: int, column_index: int) -> Optional[Tuple[int, int, int, int]]:
        if self.corner_canvas is None:
            return None
        x = ROW_NUMBER_WIDTH + sum(self.column_widths[:column_index])
        y = DEFAULT_ROW_HEIGHT + sum(self.row_heights[:row_index])
        return self._widget_relative_bbox(self.corner_canvas, x, y, self.column_widths[column_index], self.row_heights[row_index])

    def _cell_bbox_in_top(self, row_index: int, column_index: int) -> Optional[Tuple[int, int, int, int]]:
        if self.top_canvas is None:
            return None
        visible_columns = self._visible_columns(self._frozen_column_count() + self.body_col_offset, max(1, self.top_canvas.winfo_width(), self.body_canvas.winfo_width() if self.body_canvas else 0))
        if column_index not in visible_columns:
            self._scroll_to_cell(row_index, column_index)
            visible_columns = self._visible_columns(self._frozen_column_count() + self.body_col_offset, max(1, self.top_canvas.winfo_width(), self.body_canvas.winfo_width() if self.body_canvas else 0))
            if column_index not in visible_columns:
                return None
        x = 0
        for idx in visible_columns:
            if idx == column_index:
                break
            x += self.column_widths[idx]
        y = DEFAULT_ROW_HEIGHT + sum(self.row_heights[:row_index])
        return self._widget_relative_bbox(self.top_canvas, x, y, self.column_widths[column_index], self.row_heights[row_index])

    def _cell_bbox_in_left(self, row_index: int, column_index: int) -> Optional[Tuple[int, int, int, int]]:
        if self.left_canvas is None:
            return None
        visible_rows = self._visible_rows(self.body_row_offset + self._frozen_row_count(), self.left_canvas.winfo_height())
        if row_index not in visible_rows:
            self._scroll_to_cell(row_index, column_index)
            visible_rows = self._visible_rows(self.body_row_offset + self._frozen_row_count(), self.left_canvas.winfo_height())
            if row_index not in visible_rows:
                return None
        x = ROW_NUMBER_WIDTH + sum(self.column_widths[:column_index])
        y = 0
        for idx in visible_rows:
            if idx == row_index:
                break
            y += self.row_heights[idx]
        return self._widget_relative_bbox(self.left_canvas, x, y, self.column_widths[column_index], self.row_heights[row_index])

    def _cell_bbox_in_body(self, row_index: int, column_index: int) -> Optional[Tuple[int, int, int, int]]:
        if self.body_canvas is None:
            return None
        visible_rows = self._visible_rows(self.body_row_offset + self._frozen_row_count(), self.body_canvas.winfo_height())
        visible_columns = self._visible_columns(self.body_col_offset + self._frozen_column_count(), self.body_canvas.winfo_width())
        if row_index not in visible_rows or column_index not in visible_columns:
            self._scroll_to_cell(row_index, column_index)
            visible_rows = self._visible_rows(self.body_row_offset + self._frozen_row_count(), self.body_canvas.winfo_height())
            visible_columns = self._visible_columns(self.body_col_offset + self._frozen_column_count(), self.body_canvas.winfo_width())
            if row_index not in visible_rows or column_index not in visible_columns:
                return None
        x = 0
        for idx in visible_columns:
            if idx == column_index:
                break
            x += self.column_widths[idx]
        y = 0
        for idx in visible_rows:
            if idx == row_index:
                break
            y += self.row_heights[idx]
        return self._widget_relative_bbox(self.body_canvas, x, y, self.column_widths[column_index], self.row_heights[row_index])

    def _widget_relative_bbox(self, widget: tk.Widget, x: int, y: int, width: int, height: int) -> Tuple[int, int, int, int]:
        return (
            widget.winfo_rootx() - self.winfo_rootx() + x,
            widget.winfo_rooty() - self.winfo_rooty() + y,
            width,
            height,
        )

    def _body_hit_test(self, x: int, y: int) -> Optional[Tuple[int, int]]:
        row_index = self._row_from_position(self.body_row_offset + self._frozen_row_count(), y)
        column_index = self._column_from_position(self.body_col_offset + self._frozen_column_count(), x)
        if row_index is None or column_index is None:
            return None
        return row_index, column_index

    def _top_hit_test(self, x: int, y: int) -> Optional[Tuple[int, int]]:
        if y < DEFAULT_ROW_HEIGHT:
            return None
        row_index = self._row_from_frozen_band(y - DEFAULT_ROW_HEIGHT)
        column_index = self._column_from_position(self.body_col_offset + self._frozen_column_count(), x)
        if row_index is None or column_index is None:
            return None
        return row_index, column_index

    def _left_hit_test(self, x: int, y: int) -> Optional[Tuple[int, int]]:
        if x < ROW_NUMBER_WIDTH:
            return None
        row_index = self._row_from_position(self.body_row_offset + self._frozen_row_count(), y)
        column_index = self._column_from_frozen_band(x - ROW_NUMBER_WIDTH)
        if row_index is None or column_index is None:
            return None
        return row_index, column_index

    def _corner_hit_test(self, x: int, y: int) -> Optional[Tuple[int, int]]:
        if x < ROW_NUMBER_WIDTH or y < DEFAULT_ROW_HEIGHT:
            return None
        row_index = self._row_from_frozen_band(y - DEFAULT_ROW_HEIGHT)
        column_index = self._column_from_frozen_band(x - ROW_NUMBER_WIDTH)
        if row_index is None or column_index is None:
            return None
        return row_index, column_index

    def _row_from_position(self, start_row: int, y: int) -> Optional[int]:
        running_y = 0
        row_index = max(0, start_row)
        while row_index < len(self.loaded_rows):
            row_height = self.row_heights[row_index]
            if running_y <= y < running_y + row_height:
                return row_index
            running_y += row_height
            row_index += 1
        return None

    def _row_from_frozen_band(self, y: int) -> Optional[int]:
        running_y = 0
        for row_index in range(self._frozen_row_count()):
            row_height = self.row_heights[row_index]
            if running_y <= y < running_y + row_height:
                return row_index
            running_y += row_height
        return None

    def _column_from_position(self, start_column: int, x: int) -> Optional[int]:
        running_x = 0
        for column_index in range(start_column, len(self.loaded_columns)):
            column_width = self.column_widths[column_index]
            if running_x <= x < running_x + column_width:
                return column_index
            running_x += column_width
        return None

    def _column_from_frozen_band(self, x: int) -> Optional[int]:
        running_x = 0
        for column_index in range(self._frozen_column_count()):
            column_width = self.column_widths[column_index]
            if running_x <= x < running_x + column_width:
                return column_index
            running_x += column_width
        return None

    def _draw_cell(self, canvas: tk.Canvas, x: int, y: int, width: int, height: int, text: str, bg: str, anchor: str = "w", selected: bool = False, bold_text: bool = False) -> None:
        marked = bg == MARKER_FILL
        fill = SELECTION_FILL if selected else bg
        outline = SELECTION_OUTLINE if selected else (MARKER_OUTLINE if marked else GRID_LINE)
        line_width = 2 if selected else 1
        canvas.create_rectangle(x, y, x + width, y + height, fill=fill, outline=outline, width=line_width)
        clipped = self._clip_text(text, width)
        cell_font = ("Segoe UI", self._cell_font()[1], "bold") if bold_text else self._cell_font()
        if anchor == "center":
            canvas.create_text(x + (width / 2), y + (height / 2), text=clipped, fill=TEXT_COLOR, font=cell_font, anchor="center")
        else:
            canvas.create_text(x + TEXT_PAD_X, y + (height / 2), text=clipped, fill=TEXT_COLOR, font=cell_font, anchor="w")

    def _marker_bg(self, base_bg: str, row_index: Optional[int] = None, column_index: Optional[int] = None) -> str:
        if (row_index is not None and row_index in self.marked_rows) or (column_index is not None and column_index in self.marked_columns):
            return MARKER_FILL
        return base_bg

    def _clip_text(self, text: str, width: int) -> str:
        if not text:
            return ""
        max_chars = max(1, (width - (TEXT_PAD_X * 2)) // 7)
        if len(text) <= max_chars:
            return text
        if max_chars <= 3:
            return text[:max_chars]
        return text[: max_chars - 3] + "..."

    def _show_top_menu(self, event: tk.Event) -> str:
        if not self.loaded_columns:
            return "break"

        if event.y > DEFAULT_ROW_HEIGHT:
            return "break"
        column_index = self._column_from_header_click(event.widget, event.x)
        if column_index is None:
            return "break"
        selected_columns = self._selected_column_indices()
        if self.loaded_rows and column_index not in selected_columns:
            self.selection_anchor = (0, column_index)
            self.selection_focus = (len(self.loaded_rows) - 1, column_index)
            self._redraw()
            selected_columns = [column_index]

        menu = tk.Menu(self, tearoff=0)
        self._style_menu(menu)
        menu.add_command(label="Marker On", command=self._mark_selected_columns)
        menu.add_command(label="Marker Off", command=self._unmark_selected_columns)
        menu.add_separator()
        menu.add_command(label="Set Column To...", command=lambda: self._open_set_value_dialog("column", column_index))
        menu.add_separator()
        menu.add_command(label="Increase Column Values...", command=lambda: self._open_adjust_dialog("column", column_index, "increase"))
        menu.add_command(label="Decrease Column Values...", command=lambda: self._open_adjust_dialog("column", column_index, "decrease"))
        menu.tk_popup(event.x_root, event.y_root)
        menu.grab_release()
        return "break"

    def _show_corner_menu(self, event: tk.Event) -> str:
        if not self.loaded_columns:
            return "break"
        if event.y <= DEFAULT_ROW_HEIGHT:
            return self._show_top_menu(event)
        if event.x <= ROW_NUMBER_WIDTH:
            return self._show_row_menu(event)
        return "break"

    def _show_row_menu(self, event: tk.Event) -> str:
        if not self.loaded_rows:
            return "break"

        row_index = self._row_from_click(event.widget, event.y)
        if row_index is None:
            return "break"
        if event.x > ROW_NUMBER_WIDTH:
            return "break"
        selected_rows = self._selected_row_indices()
        if self.loaded_columns and row_index not in selected_rows:
            self.selection_anchor = (row_index, 0)
            self.selection_focus = (row_index, len(self.loaded_columns) - 1)
            self._redraw()
            selected_rows = [row_index]

        menu = tk.Menu(self, tearoff=0)
        self._style_menu(menu)
        menu.add_command(label="Marker On", command=self._mark_selected_rows)
        menu.add_command(label="Marker Off", command=self._unmark_selected_rows)
        menu.add_separator()
        menu.add_command(label="Insert Row Below...", command=lambda: self._insert_rows_below(row_index))
        menu.add_command(label="Remove Row", command=lambda: self._remove_row_at(row_index))
        menu.add_separator()
        menu.add_command(label="Set Row To...", command=lambda: self._open_set_value_dialog("row", row_index))
        menu.add_separator()
        menu.add_command(label="Increase Row Values...", command=lambda: self._open_adjust_dialog("row", row_index, "increase"))
        menu.add_command(label="Decrease Row Values...", command=lambda: self._open_adjust_dialog("row", row_index, "decrease"))
        menu.tk_popup(event.x_root, event.y_root)
        menu.grab_release()
        return "break"

    def _show_cell_menu(self, event: tk.Event) -> str:
        hit = self._hit_test_cell(event.widget, event.x, event.y)
        if hit is not None:
            if not self._is_selected(*hit):
                self.selection_anchor = hit
                self.selection_focus = hit
                self._redraw()
        menu = tk.Menu(self, tearoff=0)
        self._style_menu(menu)
        menu.add_command(label="Copy", command=self.copy_selection)
        menu.add_command(label="Paste", command=self.paste_into_selection)
        menu.tk_popup(event.x_root, event.y_root)
        menu.grab_release()
        return "break"

    def _mark_selected_columns(self) -> None:
        columns = self._selected_column_indices()
        if not columns:
            return
        self._push_undo_state("mark columns")
        self.marked_columns.update(columns)
        self._capture_current_document_state()
        self.status_var.set(f"Marked {len(columns)} column{'s' if len(columns) != 1 else ''}.")
        self._redraw()

    def _unmark_selected_columns(self) -> None:
        columns = self._selected_column_indices()
        if not columns:
            return
        self._push_undo_state("unmark columns")
        for column_index in columns:
            self.marked_columns.discard(column_index)
        self._capture_current_document_state()
        self.status_var.set(f"Cleared marker from {len(columns)} column{'s' if len(columns) != 1 else ''}.")
        self._redraw()

    def _mark_selected_rows(self) -> None:
        rows = self._selected_row_indices()
        if not rows:
            return
        self._push_undo_state("mark rows")
        self.marked_rows.update(rows)
        self._capture_current_document_state()
        self.status_var.set(f"Marked {len(rows)} row{'s' if len(rows) != 1 else ''}.")
        self._redraw()

    def _unmark_selected_rows(self) -> None:
        rows = self._selected_row_indices()
        if not rows:
            return
        self._push_undo_state("unmark rows")
        for row_index in rows:
            self.marked_rows.discard(row_index)
        self._capture_current_document_state()
        self.status_var.set(f"Cleared marker from {len(rows)} row{'s' if len(rows) != 1 else ''}.")
        self._redraw()

    def _column_from_header_click(self, widget: tk.Widget, x: int) -> Optional[int]:
        if widget == self.corner_canvas:
            if x < ROW_NUMBER_WIDTH:
                return None
            running_x = ROW_NUMBER_WIDTH
            for column_index in range(self._frozen_column_count()):
                column_width = self.column_widths[column_index]
                if running_x <= x < running_x + column_width:
                    return column_index
                running_x += column_width
            return None
        running_x = 0
        for column_index in self._visible_columns(self._frozen_column_count() + self.body_col_offset, self.top_canvas.winfo_width() if self.top_canvas else 0):
            column_width = self.column_widths[column_index]
            if running_x <= x < running_x + column_width:
                return column_index
            running_x += column_width
        return None

    def _row_from_click(self, widget: tk.Widget, y: int) -> Optional[int]:
        if widget == self.corner_canvas:
            if y <= DEFAULT_ROW_HEIGHT:
                return None
            running_y = DEFAULT_ROW_HEIGHT
            for row_index in range(self._frozen_row_count()):
                row_height = self.row_heights[row_index]
                if running_y <= y < running_y + row_height:
                    return row_index
                running_y += row_height
            return None

        running_y = 0
        for row_index in self._visible_rows(self.body_row_offset + self._frozen_row_count(), self.left_canvas.winfo_height() if self.left_canvas else 0):
            row_height = self.row_heights[row_index]
            if running_y <= y < running_y + row_height:
                return row_index
            running_y += row_height
        return None

    def _copy_selection_shortcut(self, _event: tk.Event) -> str:
        self.copy_selection()
        return "break"

    def _paste_selection_shortcut(self, _event: tk.Event) -> str:
        self.paste_into_selection()
        return "break"

    def copy_selection(self) -> None:
        bounds = self._selection_bounds()
        if bounds is None or not self.loaded_rows or not self.loaded_columns:
            return
        min_row, max_row, min_col, max_col = bounds
        lines: List[str] = []
        for row_index in range(min_row, max_row + 1):
            values = [self._cell_text(row_index, column_index) for column_index in range(min_col, max_col + 1)]
            lines.append("\t".join(values))
        try:
            self.clipboard_clear()
            self.clipboard_append("\n".join(lines))
            self.status_var.set("Copied selection.")
        except Exception:
            pass

    def paste_into_selection(self) -> None:
        if not self.loaded_rows or not self.loaded_columns:
            return
        try:
            raw_text = self.clipboard_get()
        except Exception:
            return
        if not raw_text:
            return

        start_row, start_col = self.selection_anchor or (0, 0)
        rows = [line.split("\t") for line in raw_text.replace("\r\n", "\n").replace("\r", "\n").split("\n")]
        if rows and rows[-1] == [""]:
            rows = rows[:-1]
        if not rows:
            return
        self._push_undo_state("paste")

        max_needed_columns = max(start_col + len(row) for row in rows)
        self._ensure_column_capacity(max_needed_columns)

        for row_offset, values in enumerate(rows):
            target_row = start_row + row_offset
            while target_row >= len(self.loaded_rows):
                self.loaded_rows.append([""] * len(self.loaded_columns))
                self.row_heights.append(DEFAULT_ROW_HEIGHT)
            while len(self.loaded_rows[target_row]) < len(self.loaded_columns):
                self.loaded_rows[target_row].append("")
            for col_offset, value in enumerate(values):
                target_col = start_col + col_offset
                if target_col < len(self.loaded_columns):
                    self.loaded_rows[target_row][target_col] = value

        self.selection_focus = (
            min(len(self.loaded_rows) - 1, start_row + len(rows) - 1),
            min(len(self.loaded_columns) - 1, start_col + max(len(row) for row in rows) - 1),
        )
        self._ensure_header_widths()
        self._capture_current_document_state()
        self._update_info()
        self.status_var.set("Pasted clipboard content.")
        self._redraw()

    def _ensure_column_capacity(self, required_columns: int) -> None:
        while len(self.loaded_columns) < required_columns:
            new_index = len(self.loaded_columns)
            self.loaded_columns.append(f"Column {new_index + 1}")
            self.column_widths.append(self._measure_column_width(self.loaded_columns[new_index], new_index, self.loaded_rows))
        for row in self.loaded_rows:
            while len(row) < len(self.loaded_columns):
                row.append("")

    def _insert_rows_below(self, row_index: int) -> None:
        if row_index < 0:
            return
        count = simpledialog.askinteger(
            APP_TITLE,
            "How many rows do you want to insert below the selected row?",
            parent=self,
            minvalue=1,
            initialvalue=1,
        )
        if count is None:
            return
        insert_at = max(0, min(len(self.loaded_rows), row_index + 1))
        self._push_undo_state("insert row")
        for _ in range(count):
            self.loaded_rows.insert(insert_at, [""] * len(self.loaded_columns))
            self.row_heights.insert(insert_at, DEFAULT_ROW_HEIGHT)
            insert_at += 1
        first_inserted = max(0, min(len(self.loaded_rows) - 1, row_index + 1))
        if self.loaded_columns:
            self.selection_anchor = (first_inserted, 0)
            self.selection_focus = (min(len(self.loaded_rows) - 1, first_inserted + count - 1), len(self.loaded_columns) - 1)
        else:
            self.selection_anchor = None
            self.selection_focus = None
        self._scroll_to_cell(first_inserted, 0 if self.loaded_columns else 0)
        self._capture_current_document_state()
        self._update_info()
        self.status_var.set(f"Inserted {count} row{'s' if count != 1 else ''} below row {row_index + 1}.")
        self._redraw()

    def _remove_row_at(self, row_index: int) -> None:
        if not self.loaded_rows or row_index < 0 or row_index >= len(self.loaded_rows):
            return
        self._push_undo_state("remove row")
        del self.loaded_rows[row_index]
        if row_index < len(self.row_heights):
            del self.row_heights[row_index]
        if self.loaded_rows and not self.row_heights:
            self.row_heights = [DEFAULT_ROW_HEIGHT for _ in self.loaded_rows]

        if not self.loaded_rows or not self.loaded_columns:
            self.selection_anchor = None
            self.selection_focus = None
        else:
            next_row = min(row_index, len(self.loaded_rows) - 1)
            self.selection_anchor = (next_row, 0)
            self.selection_focus = (next_row, len(self.loaded_columns) - 1)
            self._scroll_to_cell(next_row, 0)
        self._capture_current_document_state()
        self._update_info()
        self.status_var.set(f"Removed row {row_index + 1}.")
        self._redraw()

    def _write_current_document(self, path: Path) -> None:
        if self.current_doc_index is None:
            raise ValueError("No active document.")
        document = self.documents[self.current_doc_index]
        delimiter: Optional[str] = document.get("delimiter")
        use_first_row_as_header = bool(document.get("use_first_row_as_header"))
        rows_to_write = [list(row) for row in self.loaded_rows]
        if use_first_row_as_header:
            rows_to_write = [list(self.loaded_columns)] + rows_to_write

        if delimiter is None:
            text = "\n".join((row[0] if row else "") for row in rows_to_write)
            path.write_text(text, encoding="utf-8")
        else:
            with path.open("w", encoding="utf-8", newline="") as handle:
                writer = csv.writer(handle, delimiter=delimiter, lineterminator="\n")
                for row in rows_to_write:
                    writer.writerow(row)

    def _open_adjust_dialog(self, kind: str, index: int, operation: str) -> None:
        title = f"{operation.title()} {'Column' if kind == 'column' else 'Row'} Values"
        dialog = tk.Toplevel(self)
        dialog.title(title)
        dialog.transient(self)
        dialog.grab_set()
        dialog.resizable(False, False)

        mode_var = tk.StringVar(value="Number")
        amount_var = tk.StringVar(value="10")

        ttk.Frame(dialog, padding=12).grid(row=0, column=0, sticky="nsew")
        container = dialog.grid_slaves(row=0, column=0)[0]
        container.columnconfigure(1, weight=1)

        label_text = self.loaded_columns[index] if kind == "column" else f"Row {index + 1}"
        ttk.Label(container, text=f"Target: {label_text}").grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 10))
        ttk.Label(container, text="Mode").grid(row=1, column=0, sticky="w", padx=(0, 8), pady=4)
        mode_box = ttk.Combobox(container, textvariable=mode_var, values=["Number", "Percentage"], state="readonly", width=16)
        mode_box.grid(row=1, column=1, sticky="ew", pady=4)
        ttk.Label(container, text="Value").grid(row=2, column=0, sticky="w", padx=(0, 8), pady=4)
        entry = ttk.Entry(container, textvariable=amount_var, width=18, font=("Segoe UI", 9, "bold italic"))
        entry.grid(row=2, column=1, sticky="ew", pady=4)

        buttons = ttk.Frame(container)
        buttons.grid(row=3, column=0, columnspan=2, sticky="e", pady=(12, 0))
        ttk.Button(buttons, text="OK", command=lambda: self._apply_value_adjustment(dialog, kind, index, operation, mode_var.get(), amount_var.get())).grid(row=0, column=0, padx=(0, 6))
        ttk.Button(buttons, text="Cancel", command=dialog.destroy).grid(row=0, column=1)

        entry.focus_set()
        dialog.bind("<Return>", lambda _event: self._apply_value_adjustment(dialog, kind, index, operation, mode_var.get(), amount_var.get()))
        dialog.bind("<Escape>", lambda _event: dialog.destroy())

    def _open_set_value_dialog(self, kind: str, index: int) -> None:
        label_text = self.loaded_columns[index] if kind == "column" else f"Row {index + 1}"
        value = simpledialog.askstring(
            APP_TITLE,
            f"Set all cells in {label_text} to this exact value or phrase:",
            parent=self,
        )
        if value is None:
            return
        self._push_undo_state("set values")
        if kind == "column":
            changed = self._set_column_values(index, value)
            self.status_var.set(f"Set {changed} cell{'s' if changed != 1 else ''} in column '{label_text}'.")
        else:
            changed = self._set_row_values(index, value)
            self.status_var.set(f"Set {changed} cell{'s' if changed != 1 else ''} in row {index + 1}.")
        self._ensure_header_widths()
        self._capture_current_document_state()
        self._redraw()

    def _apply_value_adjustment(self, dialog: tk.Toplevel, kind: str, index: int, operation: str, mode: str, raw_value: str) -> None:
        try:
            amount = float(raw_value.strip())
        except ValueError:
            messagebox.showerror(APP_TITLE, "Enter a valid number.", parent=dialog)
            return
        if amount < 0:
            messagebox.showerror(APP_TITLE, "Use a positive number.", parent=dialog)
            return
        self._push_undo_state("value adjust")

        if kind == "column":
            changed, skipped = self._adjust_column_values(index, amount, mode, operation)
            label = self.loaded_columns[index]
            self.status_var.set(f"{operation.title()}d values in column '{label}'. Changed: {changed}, skipped: {skipped}.")
        else:
            changed, skipped = self._adjust_row_values(index, amount, mode, operation)
            self.status_var.set(f"{operation.title()}d values in row {index + 1}. Changed: {changed}, skipped: {skipped}.")

        dialog.destroy()
        self._ensure_header_widths()
        self._capture_current_document_state()
        self._redraw()

    def _adjust_column_values(self, column_index: int, amount: float, mode: str, operation: str) -> Tuple[int, int]:
        changed = 0
        skipped = 0
        for row_index, row in enumerate(self.loaded_rows):
            if column_index >= len(row):
                skipped += 1
                continue
            updated = self._adjust_numeric_text(row[column_index], amount, mode, operation)
            if updated is None:
                skipped += 1
                continue
            self.loaded_rows[row_index][column_index] = updated
            changed += 1
        return changed, skipped

    def _adjust_row_values(self, row_index: int, amount: float, mode: str, operation: str) -> Tuple[int, int]:
        if row_index >= len(self.loaded_rows):
            return 0, 0
        changed = 0
        skipped = 0
        for column_index, value in enumerate(self.loaded_rows[row_index]):
            updated = self._adjust_numeric_text(value, amount, mode, operation)
            if updated is None:
                skipped += 1
                continue
            self.loaded_rows[row_index][column_index] = updated
            changed += 1
        return changed, skipped

    def _set_column_values(self, column_index: int, value: str) -> int:
        changed = 0
        for row_index, row in enumerate(self.loaded_rows):
            if column_index >= len(row):
                continue
            self.loaded_rows[row_index][column_index] = value
            changed += 1
        return changed

    def _set_row_values(self, row_index: int, value: str) -> int:
        if row_index >= len(self.loaded_rows):
            return 0
        changed = 0
        for column_index in range(len(self.loaded_rows[row_index])):
            self.loaded_rows[row_index][column_index] = value
            changed += 1
        return changed

    def _adjust_numeric_text(self, value: str, amount: float, mode: str, operation: str) -> Optional[str]:
        text = str(value).strip()
        if not text:
            return None
        try:
            if any(character in text.lower() for character in [".", "e"]):
                numeric_value = float(text)
                integer_style = False
            else:
                numeric_value = int(text)
                integer_style = True
        except ValueError:
            return None

        if mode == "Percentage":
            change = numeric_value * (amount / 100.0)
        else:
            change = amount
        new_value = numeric_value + change if operation == "increase" else numeric_value - change

        if integer_style and float(new_value).is_integer():
            return str(int(round(new_value)))
        return str(round(float(new_value), 6)).rstrip("0").rstrip(".")

    def _clamp_size(self, value: int, minimum: int, maximum: Optional[int]) -> int:
        if maximum is None:
            return max(minimum, int(value))
        return max(minimum, min(maximum, int(value)))


def main() -> None:
    app = D2TextApp()
    app.mainloop()


if __name__ == "__main__":
    main()
