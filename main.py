import configparser
import ctypes
import math
import sys
import threading
from PIL import Image, ImageDraw, ImageTk, ImageFilter, ImageEnhance
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, colorchooser
import numpy
import os
import io
from rembg import remove

def resource_path(relative_path):

    try:
        base_path = sys._MEIPASS

    except Exception:
        base_path = os.path.abspath(".")
    full_path = os.path.join(base_path, relative_path)

    if not os.path.exists(full_path):
        raise FileNotFoundError(f"Resource not found: {full_path}")
    return full_path

try:
    from tkinterdnd2 import TkinterDnD, DND_FILES
    dnd_supported = True

except ImportError:
    DND_FILES = None
    dnd_supported = False

class PremiumImageEditor:

    def __init__(self, root):
        self.root = root
        self.root.title("Image Editor")
        self.root.geometry("1200x700")
        self.root.configure(bg="#1e1e2e")
        self.data_dir = os.path.join(os.path.expanduser("~"), ".ImageEditorApp")
        os.makedirs(self.data_dir, exist_ok=True)
        os.makedirs(self.data_dir, exist_ok=True)
        u2net_models_dir = os.path.join(self.data_dir, 'u2net_models')
        os.makedirs(u2net_models_dir, exist_ok=True)
        os.environ['U2NET_HOME'] = u2net_models_dir

        try:
            icon_path = resource_path("icons/icon.ico")
            root.iconbitmap(icon_path)

        except Exception as e:
            print("Icon load error:", e)
        self.root.resizable(True, True)
        self.config_file = os.path.join(self.data_dir, "config.ini")
        self.original_image = None
        self.current_image = None
        self.display_image = None
        self.image_path = None
        self.crop_rect = None
        self.base_thumbnail = None
        self.crop_start = None
        self.saved_after_last_change = False
        self.exposure_session_active = False
        self.exposure_base = None
        self.crop_end = None
        self.contrast_session_active = False
        self.contrast_effect_base = None
        self.contrast_intensity = 0
        self.skip_contrast_slider_events = False
        self.eraser_mode = False
        self.brush_size = 30
        self.last_eraser_pos = None
        self.eraser_backup = None
        self.base_thumbnail = None
        self.eraser_cursor = None
        self.exposure_effect_base = None
        self.exposure_intensity = 0
        self.brightness_session_active = False
        self.brightness_effect_base = None
        self.rect_id = None
        self.use_custom_bg = False
        self.bg_removal_color = (255, 255, 255, 0)
        self.crop_mode = False
        self.crop_handles = []
        self.original_bindings = {}
        self.effect_canvas_states = {}
        self.main_filter_buttons = {}
        self.active_main_button = None
        self.crop_drag = None
        self.eraser_drawing = False
        self.eraser_stroke_image = None
        self.crop_start_pos = None
        self.crop_start_rect = None
        self.history = []
        self.sub_filter_states = {}
        self.current_effect = None
        self.current_history_index = -1
        self.redo_icon = None
        self.undo_icon = None
        self.canvas_image_x = 0
        self.canvas_image_y = 0
        self.current_selected_sub_button = None
        self.canvas_image_width = 0
        self.rotation_mode = False
        self.canvas_image_height = 0
        self.animation_running = False
        self.original_with_bg = None
        self.dots = ""
        self.dot_index = 0
        self.brightness_intensity = 0
        self.skip_brightness_slider_events = False
        self.all_filter_states = {}
        self.sub_filter_intensities = {}
        self.effect_base_images = {}
        self.remove_bg_button = None
        self.zoom_level = 1.0
        self.pan_start = None
        self.initial_zoom_level = 1.0
        self.pan_offset = [0, 0]
        self.zoom_center = None
        self.doodle_mode = False
        self.doodle_start = None
        self.doodle_color = (255, 0, 0)
        self.doodle_brush_size = 10
        self.doodle_backup = None
        self.doodle_temp_image = None
        self.doodle_drawing = False
        self.doodle_current_shape = None
        self.doodle_last_pos = None
        self.doodle_stroke_image = None
        self.saturation_session_active = self.vignette_session_active = self.sharpness_session_active = self.gain_session_active = self.fade_session_active = self.highlight_session_active = self.shadows_session_active = self.vibrance_session_active =  self.wormth_session_active = self.tint_session_active = self.tint_session_active = False
        self.saturation_effect_base = self.vignette_effect_base = self.sharpness_effect_base = self.gain_effect_base = self.fade_effect_base = self.shadows_effect_base = self.highlight_effect_base =self.tint_effect_base =  self.wormth_effect_base = self.vibrance_effect_base = None
        self.skip_vibrance_slider_events = self.skip_vignette_slider_events = self.skip_sharpness_slider_events = self.skip_gain_slider_events = self.skip_saturation_slider_events = self.skip_wormth_slider_events = self.skip_tint_slider_events = self.skip_highlight_slider_events = self.skip_shadows_slider_events = self.skip_fade_slider_events = False
        self.vibrance_intensity = self.vignette_intensity = self.sharpness_intensity = self.gain_intensity = self.saturation_intensity =  self.wormth_intensity = self.tint_intensity = self.highlight_intensity = self.shadows_intensity = self.fade_intensity = 0
        self.load_window_geometry()
        self.setup_ui()
        self.set_custom_theme()
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        root.bind("<Control-b>", self.browse_files)
        root.bind("<Control-B>", self.browse_files)

    def load_window_geometry(self):

        if os.path.exists(self.config_file):
            config = configparser.ConfigParser()
            config.read(self.config_file)

            if "Geometry" in config:
                geometry = config["Geometry"].get("size", "")
                state = config["Geometry"].get("state", "normal")

                if geometry:
                    self.root.geometry(geometry)
                    self.root.update_idletasks()
                    self.root.update()

                if state == "zoomed":
                    self.root.state("zoomed")
                elif state == "iconic":
                    self.root.iconify()

    def save_window_geometry(self):
        config = configparser.ConfigParser()
        config["Geometry"] = {
            "size": self.root.geometry(),
            "state": self.root.state()
        }

        with open(self.config_file, "w") as f:
            config.write(f)

    def has_unsaved_changes(self):
        return (self.current_image is not None and
                self.original_image is not None and
                (self.current_history_index != 0 or
                self.sub_filter_intensities) and
                not self.saved_after_last_change)

    def on_close(self):

        if self.has_unsaved_changes():
            response = messagebox.askyesnocancel(
                "Save Changes?",
                "Do you want to save your changes?",
                detail="Your changes will be lost if you don't save it.",
                icon=messagebox.WARNING
            )

            if response is None:
                return

            if response:

                if not self.export_image():
                    return
        self.save_window_geometry()
        self.root.destroy()

    def set_custom_theme(self):
        style = ttk.Style()
        style.theme_use('clam')
        style.configure('.', background='#1e1e2e', foreground='#e0e0ff')
        style.configure('TFrame', background='#1e1e2e')
        style.configure('TButton',
                        background='#4a4a6e',
                        foreground='#ffffff',
                        font=('Arial', 12, 'bold'),
                        borderwidth=1,
                        focuscolor='#1e1e2e')
        style.map('TButton',
                 background=[('active', '#5a5a8e'), ('pressed', '#3a3a5e')],
                 foreground=[('active', 'white')])
        style.configure('Undo.TButton',
                        background='#4a4a6e',
                        foreground='#ffffff',
                        font=('Arial', 12, 'bold'),
                        borderwidth=0,
                        padding=8,
                        focuscolor='#1e1e2e')
        style.map('Undo.TButton',
                 background=[('active', '#5a5a8e'), ('pressed', '#3a3a5e')],
                 foreground=[('active', 'white')])
        style.configure('Redo.TButton',
                        background='#4a6e4a',
                        foreground='#ffffff',
                        font=('Arial', 12, 'bold'),
                        borderwidth=0,
                        padding=8,
                        focuscolor='#1e1e2e')
        style.map('Redo.TButton',
                 background=[('active', '#5a8e5a'), ('pressed', '#3a5e3a')],
                 foreground=[('active', 'white')])
        style.configure('TLabel', background='#1e1e2e', foreground='#e0e0ff')
        style.configure('Header.TLabel', font=('Segoe UI', 18, 'bold'), foreground='#aaccff')
        style.configure('TCombobox', fieldbackground='#2a2a3a', foreground='#e0e0ff')
        style.configure('TScale', background='#1e1e2e')
        style.configure('TSeparator', background='#4a4a6e')
        style.configure('TLabelframe', background='#1e1e2e', foreground='#aaccff', font=('Segoe UI', 10, 'bold'))
        style.configure('TLabelframe.Label', background='#1e1e2e', foreground='#aaccff')
        style.configure('TNotebook', background='#1e1e2e', borderwidth=0)
        style.configure('TNotebook.Tab',
                       background='#2a2a3a',
                       foreground='#bdc3c7',
                       padding=[15, 5],
                       font=('Arial', 10, 'bold'))
        style.map('TNotebook.Tab',
                 background=[('selected', '#4a4a6e'), ('active', '#3a3a5e')],
                 foreground=[('selected', '#ffffff'), ('active', '#ffffff')])
        style.configure('Zoom.Horizontal.TScale',
                       background='#1e1e2e',
                       troughcolor='#2a2a3a',
                       bordercolor='#4a4a6e',
                       sliderthickness=15,
                       sliderrelief='flat',
                       troughrelief='flat')
        style.map('Zoom.Horizontal.TScale',
                 sliderrelief=[('pressed', 'sunken'), ('active', 'raised')],
                 slidercolor=[('pressed', '#5a5a8e'), ('active', '#4a4a6e')])
        style.configure('BigFont.TRadiobutton',
                    font=('Arial', 12, 'bold'),
                    background='#1e1e2e',
                    foreground='#e0e0ff',
                    padding=8,
                    indicatorsize=20,
                    indicatorbackground="#0dee2f",
                    indicatorcolor="#f50e0e",
                    selectcolor="#1e1e2e")
        style.map('BigFont.TRadiobutton',
                background=[('active',
                              "#2C6136"
                              )],
                foreground=[('active', '#ffffff')],
                indicatorcolor=[('selected', '#4a9dff'), ('!selected', '#4a4a6e')])
        style.element_create('Custom.Vertical.Scrollbar.trough', 'from', 'clam')
        style.element_create('Custom.Vertical.Scrollbar.thumb', 'from', 'clam')
        style.layout('Vertical.TScrollbar', [
            ('Vertical.Scrollbar.trough', {
                'children': [
                    ('Vertical.Scrollbar.thumb', {'unit': '1', 'sticky': 'nswe'})
                ],
                'sticky': 'ns'
            })
        ])
        style.configure("Vertical.TScrollbar",
            gripcount=0,
            background="#5A5A8E",     # Thumb color
            troughcolor="#2a2a3a",    # Track color
            bordercolor="#1e1e2e",
            arrowcolor="#ffffff",
            darkcolor="#444",
            lightcolor="#666",
            borderwidth=1,
            width=12
        )
        style.map("Vertical.TScrollbar",
            background=[('active', "#A4A4D4")],
            arrowcolor=[('active', 'white')],
            troughcolor=[('active', '#2f2f4f')]
        )
        style.theme_use('clam')
        style.element_create('Custom.Horizontal.Scrollbar.trough', 'from', 'clam')
        style.element_create('Custom.Horizontal.Scrollbar.thumb', 'from', 'clam')
        style.layout('Horizontal.TScrollbar', [
            ('Custom.Horizontal.Scrollbar.trough', {
                'children': [
                    ('Custom.Horizontal.Scrollbar.thumb', {'unit': '1', 'sticky': 'nswe'})
                ],
                'sticky': 'nswe'
            })
        ])
        style.configure("Horizontal.TScrollbar",
            gripcount=0,
            background="#5A5A8E",     # Thumb color
            troughcolor="#2a2a3a",    # Track color
            bordercolor="#1e1e2e",
            darkcolor="#444",
            lightcolor="#666",
            borderwidth=1,
            width=12
        )
        style.map("Horizontal.TScrollbar",
            background=[('active', "#ACC6EE")],
            troughcolor=[('active', '#2f2f4f')]
        )

    def setup_ui(self):
        header_frame = tk.Frame(self.root,bg='#1E1E2E')
        header_frame.pack(fill='x', padx=20, pady=(15, 10))
        redo_undo_frame = tk.Frame(header_frame,bg = '#1E1E2E')
        redo_undo_frame.pack(side=tk.LEFT)
        undo_img = Image.open(resource_path(r"icons\undo.png")).resize((20, 20))
        self.undo_icon = ImageTk.PhotoImage(undo_img)

        try:
            undo_btn = tk.Button(redo_undo_frame, image=self.undo_icon, background='#1E1E2E', activebackground="#3C4885", borderwidth=0, command=self.undo)
            undo_btn.pack(side='left', fill='x', expand=True, padx=(10))

        except:
            pass
        redo_img = Image.open(resource_path(r"icons\redo.png")).resize((20, 20))
        self.redo_icon = ImageTk.PhotoImage(redo_img)

        try:
            redo_btn = tk.Button(redo_undo_frame, image=self.redo_icon, background='#1E1E2E', activebackground="#3C4885", borderwidth=0, command=self.redo)
            redo_btn.pack(side='left', fill='x', expand=True, padx=(10))

        except:
            pass
        text_frame = tk.Frame(header_frame,bg='#1E1E2E')
        text_frame.pack(side=tk.LEFT)
        text_frame_center = tk.Frame(header_frame,bg = '#1E1E2E')
        text_frame_center.pack(fill='x', expand=True)
        ttk.Label(text_frame_center, text="Image Editor", style='Header.TLabel').pack()
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill='both', expand=True, padx=20, pady=10)
        self.paned_window = tk.PanedWindow(
            main_frame, orient=tk.HORIZONTAL,
            sashwidth=6, sashrelief=tk.RAISED,
            bg='#2a2a3a', bd=0
        )
        self.paned_window.pack(fill='both', expand=True)
        self.left_panel = ttk.Frame(self.paned_window, width=380)
        self.left_panel.pack_propagate(False)
        self.paned_window.add(self.left_panel, minsize=382, stretch="never")
        self.image_frame = ttk.Frame(self.paned_window, style='TFrame')
        self.paned_window.add(self.image_frame, minsize=400, stretch="always")
        self.canvas_frame = ttk.Frame(self.image_frame, style='TFrame')
        self.canvas_frame.pack(fill='both', expand=True, padx=5, pady=5)
        self.canvas = tk.Canvas(
            self.canvas_frame, bg='#2a2a3a',
            bd=0, highlightthickness=0, relief='sunken'
        )
        self.canvas.pack(fill='both', expand=True, padx=2, pady=2)
        self.canvas.bind("<ButtonPress-1>", self.on_canvas_press)
        self.canvas.bind("<B1-Motion>", self.on_canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_canvas_release)
        self.canvas.bind("<MouseWheel>", self.on_mouse_wheel)
        self.zoom_frame = ttk.Frame(self.canvas_frame)
        ttk.Label(self.zoom_frame, text="Zoom:", font=('Arial',10)).pack(side='left', padx=(0, 5))
        self.zoom_var = tk.DoubleVar(value=100)
        self.zoom_slider = ttk.Scale(
            self.zoom_frame, from_=10, to=100,
            orient='horizontal', variable=self.zoom_var,
            command=self.update_zoom, style='Zoom.Horizontal.TScale'
        )
        self.zoom_slider.pack(side='left', fill='x', expand=True, padx=(0, 5))
        self.zoom_label = ttk.Label(self.zoom_frame, text="100%", font=('Arial',10))
        self.zoom_label.pack(side='left')
        self.zoom_frame.pack_forget()
        notebook = ttk.Notebook(self.left_panel)
        notebook.pack(fill='both', expand=True, padx=5, pady=5)
        file_frame = ttk.Frame(notebook)
        notebook.add(file_frame, text="File")
        tk.Label(
            file_frame, bg='#1E1E2E', text="Import Image",
            font=('Times New Roman', 20, 'bold'), fg='white'
        ).pack(padx=10, pady=8)
        self.setup_drag_drop(file_frame)
        ttk.Button(file_frame, text="Export Image", command=self.export_image,
                style='TButton').pack(fill='x', padx=10, pady=8)
        ttk.Separator(file_frame, orient='horizontal').pack(fill='x', padx=10, pady=5)
        self.image_info = tk.Text(
            file_frame, height=15, bg="#2a2a3a", fg="#e0e0ff",
            font=("Arial", 12), bd=0, highlightthickness=0
        )
        self.image_info.pack(fill='x', padx=10, pady=5)
        self.image_info.insert("1.0", "\n\n     ❌ No Image Loaded")
        self.image_info.configure(state='disabled')
        edit_frame = ttk.Frame(notebook)
        notebook.add(edit_frame, text="Edit")
        history_frame = ttk.Frame(edit_frame, style='TFrame')
        history_frame.pack(fill='x', pady=(10, 15), padx=10)
        btn_container = tk.Frame(history_frame, bg='#2a2a3a', bd=0, highlightthickness=0)
        btn_container.pack(fill='x', pady=(10, 0))
        self.root.bind("<Control-z>", self.undo)
        self.root.bind("<Control-Z>", self.undo)
        self.root.bind("<Control-y>", self.redo)
        self.root.bind("<Control-Y>", self.redo)
        self.root.bind("<Control-plus>", self.zoom_in)
        self.root.bind("<Control-minus>", self.zoom_out)
        self.root.bind("<Control-KP_Add>", self.zoom_in)
        self.root.bind("<Control-KP_Subtract>", self.zoom_out)
        crop_container = ttk.Frame(edit_frame)
        crop_container.pack(fill='x', padx=10, pady=(0, 0))
        ttk.Button(crop_container, text="Crop Image", command=self.enter_crop_mode).pack(fill='x', padx=0, pady=8)
        ttk.Button(edit_frame, text="Rotate Image", command=self.enter_rotation_mode).pack(fill='x', padx=10, pady=8)
        ttk.Separator(edit_frame, orient='horizontal').pack(fill='x', padx=10, pady=8)
        ttk.Button(edit_frame, text="Reset Image", command=self.reset_image).pack(fill='x', padx=10, pady=8)
        format_frame = ttk.Frame(notebook)
        notebook.add(format_frame, text="Format")
        ttk.Label(format_frame, text="Export Format", font=('Times New Roman', 20, 'bold'), style='TLabel').pack(pady=(15, 15))
        self.format_var = tk.StringVar(value="PNG")
        radio_frame = ttk.Frame(format_frame, style='TFrame')
        radio_frame.pack(padx=20, pady=10, fill='x')
        formats = ["  PNG (Transparency)", "  JPG (High Quality)", "  ICO (Icon)"]
        for fmt in formats:
            rb = ttk.Radiobutton(
                radio_frame, text=fmt, variable=self.format_var,
                value=fmt.split()[0], style='BigFont.TRadiobutton'
            )
            rb.pack(anchor='w', padx=15, pady=2, fill='x')
            rb.bind("<Enter>", lambda e, b=rb: b.configure(style='BigFont.TRadiobutton'))
            rb.bind("<Leave>", lambda e, b=rb: b.configure(style='BigFont.TRadiobutton'))
        ttk.Separator(format_frame, orient='horizontal').pack(fill='x', padx=10, pady=8)
        ttk.Label(format_frame, text="Compress Image", font=('Times New Roman', 20, 'bold'), style='TLabel').pack(pady=(10, 15))
        self.compress_frame = ttk.Frame(format_frame)
        self.compress_frame.pack(fill='x', padx=20, pady=10)
        ttk.Button(self.compress_frame, text="Compress by Reducing Quality", command=self.show_quality_popup).pack(fill='x', pady=5)
        ttk.Button(self.compress_frame, text="Compress by Resizing", command=self.show_resize_popup).pack(fill='x', pady=5)
        self.quality_popup = ttk.Frame(format_frame, style='TFrame')
        self.resize_popup = ttk.Frame(format_frame, style='TFrame')
        bg_frame = ttk.Frame(notebook)
        notebook.add(bg_frame, text="Background")
        self.remove_bg_button = ttk.Button(bg_frame, text="Remove Background", command=self.remove_background)
        self.remove_bg_button.pack(fill='x', padx=10, pady=(30,10))
        self.original_background = ttk.Button(bg_frame, text="Original Background", command=self.restore_original_background)
        self.original_background.pack(fill='x', padx=10, pady=10)
        self.animation_label = ttk.Label(
            bg_frame,
            text="",
            foreground="#1afb0e",
            background='#1e1e2e',
            font=("Consolas", 12, "bold")
        )
        self.animation_label.pack(pady=5)
        ttk.Separator(bg_frame, orient='horizontal').pack(fill='x', padx=10, pady=5)
        ttk.Label(bg_frame, text="Set Background Colour:", font=('Arial', 15)).pack(anchor='w', padx=10, pady=(10, 5))
        color_frame = ttk.Frame(bg_frame)
        color_frame.pack(fill='x', padx=10, pady=5)
        self.bg_color_var = tk.StringVar(value="#2a2a3a")
        ttk.Button(color_frame, text="Choose", command=self.choose_bg_color, width=8).pack(side=tk.LEFT,fill='x',expand=True, padx=10)
        ttk.Button(color_frame, text="No Background Colour", command=self.remove_background_color, width=22).pack(side=tk.LEFT,fill='x',expand=True, padx=10)
        ttk.Separator(bg_frame, orient='horizontal').pack(fill='x', padx=10, pady=(10, 5))
        ttk.Label(bg_frame, text="Erase Object", font=('Arial', 15)).pack(anchor='w', padx=10, pady=(10, 5))
        erase_btn = ttk.Button(bg_frame, text="Erase", command=self.enter_eraser_mode, width=22)
        erase_btn.pack(padx=10,  pady=5, fill='x')
        self.eraser_control_frame = ttk.Frame(bg_frame)
        top_row = ttk.Frame(self.eraser_control_frame)
        top_row.pack(fill='x', pady=(0, 5))
        ttk.Label(top_row, text="Brush Size:", font=('Arial', 12)).pack(side=tk.LEFT, padx=(5,10), pady=(20,0))
        self.brush_slider = tk.Scale(
            top_row,
            from_=5,
            to=200,
            orient=tk.HORIZONTAL,
            command=self.update_brush_size,
            length=200,
            background="#1e1e2e",
            troughcolor="#353568",
            highlightthickness=0,
            foreground="white",
            border=1,
            borderwidth=2,
            sliderrelief='flat',
            relief='flat',
            font=('arial',12),
            activebackground="#E32C32",
        )
        self.brush_slider.set(self.brush_size)
        self.brush_slider.pack(side=tk.LEFT,fill='x',expand=True, padx=5)
        btn_row = ttk.Frame(self.eraser_control_frame)
        btn_row.pack(fill='x')
        apply_btn = tk.Button(btn_row, text="Apply",font=('Arial', 12, 'bold'), fg='white', bg='#4a4a7a',
            activebackground="#383860", activeforeground="lightgreen", border=0, command=self.apply_eraser)
        apply_btn.pack(fill='x', expand=True, side='left', padx=5, pady=5)
        cancel_btn = tk.Button(btn_row, text="Cancel",font=('Arial', 12, 'bold'), fg='white', bg='red',
            activebackground="orange", activeforeground="white", border=0, command=self.cancel_eraser)
        cancel_btn.pack(fill='x', side='left',expand=True, padx=5, pady=5)
        effects_frame = ttk.Frame(notebook)
        notebook.add(effects_frame, text="Effects")
        container = ttk.Frame(effects_frame)
        container.pack(fill='both', expand=True)
        canvas = tk.Canvas(container, bg='#1e1e2e', highlightthickness=0)
        self.effects_canvas = canvas
        scrollbar = ttk.Scrollbar(container, orient="vertical", command=canvas.yview, style="Vertical.TScrollbar")
        scrollable_frame = ttk.Frame(canvas)
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(
                scrollregion=canvas.bbox("all")
            )
        )
        canvas_frame = canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.grid(row=0, column=0, sticky="nsew")
        scrollbar.grid(row=0, column=1, sticky="ns")
        container.columnconfigure(0, weight=1)
        container.rowconfigure(0, weight=1)

        def update_canvas_width(event):
            canvas.itemconfig(canvas_frame, width=event.width)
        canvas.bind("<Configure>", update_canvas_width)
        effects = [
            "Filter",
            "Expouse",
            "Brightness",
            "Contrast",
            "Saturation",
            "Vibrance",
            "Wormth",
            "Tint",
            "Highlight",
            "Shadows",
            "Fade",
            "Gain",
            "Sharpness",
            "Vignette",
            "Doodle",
        ]
        for name in effects:
            effect_container = ttk.Frame(scrollable_frame)
            effect_container.pack(fill='x', expand=True, padx=10, pady=(0,0))
            effect_container.bind("<MouseWheel>", self._on_mousewheel)
            btn = ttk.Button(
                effect_container,
                text=name,
                command=lambda n=name: self.toggle_effect_canvas(n)
            )
            btn.pack(fill='x', expand=True, pady=(5, 0))
            btn.bind("<MouseWheel>", self._on_mousewheel)
            toggle_frame = tk.Frame(
                effect_container,
                height=0,
                relief='sunken',
                borderwidth=1,
                bg="#1e1e2e",
            )
            toggle_frame.pack(fill='x', expand=True, pady=(0,5))
            toggle_frame.pack_propagate(False)
            toggle_frame.bind("<MouseWheel>", self._on_mousewheel)

            if name == "Filter":
                self.setup_filter_buttons(toggle_frame)

            if name == "Expouse":
                self.setup_expause_frame(toggle_frame)

            if name == "Brightness":
                self.setup_brightness_frame(toggle_frame)

            if name == "Contrast":
                self.setup_contrast_frame(toggle_frame)

            if name == "Saturation":
                self.setup_saturation_frame(toggle_frame)

            if name == "Vibrance":
                self.setup_vibrance_frame(toggle_frame)

            if name == "Wormth":
                self.setup_wormth_frame(toggle_frame)

            if name == "Tint":
                self.setup_tint_frame(toggle_frame)

            if name == "Highlight":
                self.setup_highlight_frame(toggle_frame)

            if name == "Shadows":
                self.setup_shadows_frame(toggle_frame)

            if name == "Fade":
                self.setup_fade_frame(toggle_frame)

            if name == "Gain":
                self.setup_gain_frame(toggle_frame)

            if name == "Sharpness":
                self.setup_sharpness_frame(toggle_frame)

            if name == "Vignette":
                self.setup_vignette_frame(toggle_frame)

            if name == "Doodle":
                self.setup_doodle_frame(toggle_frame)
            self.effect_canvas_states[name] = {
                'visible': False,
                'frame': toggle_frame,
                'animating': False,
                'target_height': 0
            }
        self.effects_canvas.bind("<MouseWheel>", self._on_mousewheel)
        scrollable_frame.bind("<MouseWheel>", self._on_mousewheel)
        canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.crop_control_frame = ttk.Frame(crop_container)
        self.crop_control_frame.pack(fill='x', side='bottom', padx=10, pady=10)
        self.crop_control_frame.pack_forget()
        tk.Button(
            self.crop_control_frame, text="Apply Crop", command=self.apply_crop,
            font=('Arial', 12, 'bold'), fg='white', bg='#4a4a7a',
            activebackground="#383860", activeforeground="lightgreen", border=0
        ).pack(side='left',fill='x',expand=True, padx=5, pady=5)
        tk.Button(
            self.crop_control_frame, text="Cancel", command=self.cancel_crop,
            font=('Arial', 12, 'bold'), fg='white', bg='red',
            activebackground="orange", activeforeground="white", border=0
        ).pack(side='left',fill='x',expand=True, padx=5, pady=5)

    def _on_mousewheel(self, event):
        self.effects_canvas.yview_scroll(int(-1*(event.delta/120)), "units")

    def toggle_effect_canvas(self, effect_name):
        state = self.effect_canvas_states[effect_name]

        if state.get('animating'):
            return
        frame = state['frame']
        is_expanding = not state['visible']
        state['target_height'] = 189 if is_expanding else 0
        state['animating'] = True

        if is_expanding:
            frame.pack(fill='x', expand=True, pady=(0, 5))
            frame.update_idletasks()
            frame.configure(height=0, borderwidth=1)
            frame.pack_propagate(False)
        self.animate_frame(state, 0 if is_expanding else frame.winfo_height(), state['target_height'])

    def animate_frame(self, state, current_height, target_height):
        frame = state['frame']

        if current_height == target_height:
            state['visible'] = (target_height != 0)
            state['animating'] = False

            if target_height == 0:
                frame.pack_forget()
            else:
                frame.configure(borderwidth=1)
            return
        step = 25

        if current_height < target_height:
            new_height = min(current_height + step, target_height)
            frame.configure(height=new_height)
        else:
            new_height = max(current_height - step, target_height)
            frame.configure(height=new_height)
        frame.after(5, lambda: self.animate_frame(state, new_height, target_height))

    def reset_filter_states(self):
        self.sub_filter_intensities = {}
        self.effect_base_images = {}
        self.current_effect = None
        self.current_selected_sub_button = None

        if self.active_main_button:
            prev_btn = self.main_filter_buttons[self.active_main_button]
            prev_btn.image = self.create_rounded_button_image(bg="#3232D5")
            prev_btn.config(image=prev_btn.image, fg='white')
            self.active_main_button = None
        for widget in self.frame3.winfo_children():
            widget.destroy()
        for widget in self.frame2.winfo_children():
            widget.destroy()

    def create_rounded_button(self, master, text, width=100, height=40, radius=20, bg="#3232D5", fg="white", font=('Arial', 11), command=None):
        image = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        draw = ImageDraw.Draw(image)
        draw.rounded_rectangle((0, 0, width, height), radius=radius, fill=bg)
        tk_image = ImageTk.PhotoImage(image)
        label = tk.Label(master, image=tk_image, text=text, compound='center',
                        fg=fg, font=font, cursor="hand2", bg="#1E1E2E")
        label.image = tk_image

        if command:
            label.bind("<Button-1>", lambda e: command())
        return label

    def make_rounded_thumb(self, img, size=(55,55), radius=15):

        if self.current_effect and self.sub_filter_intensities:
            filter_name, sub_name = self.current_effect
            key = (filter_name, sub_name)

            if key in self.sub_filter_intensities:
                intensity = self.sub_filter_intensities[key] / 100.0
                img = self.apply_sub_filter_to_image(img.copy(), sub_name, intensity)

        if img.mode == 'RGBA':

            if self.use_custom_bg:
                bg_color = self.bg_removal_color[:3]
                bg = Image.new('RGB', img.size, bg_color)
                img = Image.alpha_composite(bg.convert('RGBA'), img)
            else:
                img = self.composite_over_checkerboard(img)

        if img.size != size:
            img = img.resize(size, Image.LANCZOS)
        img = img.convert("RGBA")
        mask = Image.new('L', size, 0)
        draw = ImageDraw.Draw(mask)
        draw.rounded_rectangle([0, 0, size[0]-1, size[1]-1], radius, fill=255)
        img.putalpha(mask)
        background = Image.new("RGBA", size, "#1E1E2E")
        final_img = Image.alpha_composite(background, img)
        return ImageTk.PhotoImage(final_img)

    def create_rounded_button_image(self, width=80, height=30, radius=20, bg="#3232D5"):
        image = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        draw = ImageDraw.Draw(image)
        draw.rounded_rectangle((0, 0, width, height), radius=radius, fill=bg)
        return ImageTk.PhotoImage(image)

    def update_all_thumbnails(self):

        if not self.current_image:
            return
        base_img = self.current_image.copy()
        base_img.thumbnail((55, 55), Image.LANCZOS)
        for widget in self.frame2.winfo_children():

            if hasattr(widget, 'thumb_img'):
                rounded_thumb = self.make_rounded_thumb(base_img)
                widget.children['!button'].configure(image=rounded_thumb)
                widget.children['!button'].image = rounded_thumb

    def apply_sub_filter_to_image(self, img, sub_name, intensity):

        if sub_name == "Arctic":
            return self.apply_arctic_effect(img, intensity)
        elif sub_name == "Cobalt":
            return self.apply_cobalt_effect(img, intensity)
        return img

    def _on_mousewheel(self, event):

        if event.num == 5 or event.delta == -120:
            direction = 1
        elif event.num == 4 or event.delta == 120:
            direction = -1
        else:
            return
        self.effects_canvas.yview_scroll(direction, "units")

    def bind_mousewheel_to_children(self, widget):
        widget.bind("<MouseWheel>", self._on_mousewheel)
        for child in widget.winfo_children():
            self.bind_mousewheel_to_children(child)

    def setup_filter_buttons(self, parent_frame):
        self.filter_container = ttk.Frame(parent_frame)
        self.filter_container.pack(fill='both', expand=True)
        self.bind_mousewheel_to_children(self.filter_container)
        scrollable_container = ttk.Frame(self.filter_container)
        scrollable_container.pack(fill='both', expand=True, padx=5, pady=0)
        canvas_container = ttk.Frame(scrollable_container)
        canvas_container.pack(fill='both', expand=True, padx=0, pady=0)
        self.horizontal_scrollbar = ttk.Scrollbar(
            canvas_container,
            orient="horizontal",
            style="Horizontal.TScrollbar",
        )
        self.horizontal_scrollbar.pack(side="bottom", fill="x", padx=5, pady=(0, 0))
        self.horizontal_scrollbar.bind("<MouseWheel>", self._on_mousewheel)
        self.frame3 = tk.Frame(canvas_container, height=40, bg="#1e1e2e")
        self.frame3.pack(side="bottom", fill="x", padx=5, pady=(0, 0))
        self.bind_mousewheel_to_children(self.frame3)
        self.filter_canvas = tk.Canvas(
            canvas_container,
            bg='#1e1e2e',
            highlightthickness=0,
            xscrollcommand=self.horizontal_scrollbar.set
        )
        self.filter_canvas.pack(side="top", fill="both", expand=True, padx=0, pady=0)
        self.filter_canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.horizontal_scrollbar.config(command=self.filter_canvas.xview)
        self.filter_content = ttk.Frame(self.filter_canvas)
        self.filter_canvas.create_window((0, 0), window=self.filter_content, anchor="nw")
        self.filter_content.bind(
            "<Configure>",
            lambda e: self.filter_canvas.configure(
                scrollregion=self.filter_canvas.bbox("all"),
                width=e.width
            )
        )
        self.frame1 = tk.Frame(self.filter_content, bg="#1e1e2e")
        self.frame1.pack(fill='x', side='top', padx=5, pady=(5, 0))
        self.bind_mousewheel_to_children(self.frame1)
        self.frame2 = tk.Frame(self.filter_content, bg="#1e1e2e")
        self.frame2.pack(fill='x', side='top', padx=5, pady=(0, 5))
        self.bind_mousewheel_to_children(self.frame2)
        self.sub_filters = {
            "Popular": ["Arctic", "Cobalt", "Harvest", "Pumpkin", "Noir", "Verdant", "Zenith", "Bloom"],
            "Film": ["R600", "P100F", "f-50", "KC64", "V-250", "H-400", "KP160", "FC400", "C-50D", "KG200"],
            "Classic": ["Vivid", "Sangria", "Rhodium", "Lime", "Film", "Purple"],
            "Portrait": ["Colour fo..", "Starlight", "Sunbeam", "Azure", "Bud", "Original", "Holiday", "Oxygen", "Mint", "Nature", "Pink"],
            "Food": ["Gourmand", "Food", "Soda", "Mango"],
            "Movie": ["Action", "Drama", "Horror", "Comedy", "Sci-Fi", "Romance", "Fantasy"],
            "Travel": ["Landscape", "Cityscape", "Seascape", "Mountains", "Beach", "Urban"],
            "Night": ["Moonlight", "City Lights", "Stars", "Neon", "Fireworks"],
            "Lit": ["Warm Glow", "Golden Hour", "Sunset", "Candlelight"],
            "B&W": ["High Contrast", "Low Contrast", "Grainy", "Smooth", "Vintage",],
            "Fresh": ["Spring", "Summer", "Autumn", "Winter"]
        }
        self.filter_container.pack_forget()

    def show_filter_buttons(self):

        if not self.filter_container.winfo_ismapped():
            self.filter_container.pack(fill='both', expand=True)

        if not self.main_filter_buttons:
            for filter_name in self.sub_filters.keys():
                btn = self.create_rounded_button(
                    self.frame1,
                    text=filter_name,
                    width=80,
                    height=30,
                    radius=20,
                    bg="#3232D5",
                    fg="white",
                    font=('Arial', 10, 'bold'),
                    command=lambda f=filter_name: self.show_sub_filters(f)
                )
                btn.pack(side='left', padx=5, pady=(5, 0))
                btn.bind("MouseWheel>", self._on_mousewheel)
                self.bind_mousewheel_to_children(btn)
                self.main_filter_buttons[filter_name] = btn
        self.base_thumbnail = None

    def show_sub_filters(self, filter_name):
        for widget in self.frame3.winfo_children():
            widget.destroy()
        self.current_selected_sub_button = None

        if self.active_main_button:
            prev_btn = self.main_filter_buttons[self.active_main_button]
            prev_btn.image = self.create_rounded_button_image(bg="#3232D5")
            prev_btn.config(image=prev_btn.image, fg='white')
            prev_btn.image_ref = prev_btn.image
        current_btn = self.main_filter_buttons[filter_name]
        current_btn.image = self.create_rounded_button_image(bg="#57fa11")
        current_btn.config(image=current_btn.image, fg='black')
        current_btn.image_ref = current_btn.image
        self.active_main_button = filter_name
        for widget in self.frame2.winfo_children():
            widget.destroy()

        if self.current_image:

            if self.base_thumbnail is None or self.base_thumbnail.size != self.current_image.size:
                base_img = self.current_image.copy()
                base_img.thumbnail((60, 60), Image.LANCZOS)
                self.base_thumbnail = base_img
            self.sub_filter_buttons = {}
            for sub_name in self.sub_filters[filter_name]:
                filter_frame = tk.Frame(self.frame2, bg="#1e1e2e")
                filter_frame.pack(side='left', padx=5, pady=5)
                filter_frame.bind("<MouseWheel>", self._on_mousewheel)
                thumb_img = self.make_rounded_thumb(base_img)
                btn = tk.Button(
                    filter_frame,
                    image=thumb_img,
                    bg='#1e1e2e',
                    activebackground='#1e1e2e',
                    bd=0,
                    highlightthickness=0,
                    relief='flat'
                )
                btn.pack()
                btn.configure(image=thumb_img)
                btn.image = thumb_img
                btn.normal_thumb = thumb_img
                filter_frame.thumb_img = thumb_img
                btn.bind("<MouseWheel>", self._on_mousewheel)
                btn.configure(
                        command=lambda f=filter_name, s=sub_name: self.setup_effect_slider(f, s)
                    )
                btn.sub_name = sub_name
                btn.filter_name = filter_name
                self.sub_filter_buttons[sub_name] = btn
                label = tk.Label(
                    filter_frame,
                    text=sub_name,
                    fg='white',
                    bg='#1e1e2e',
                    font=('Arial', 10)
                )
                label.pack()
                label.bind("<MouseWheel>", self._on_mousewheel)
                label.sub_name = sub_name
            self.filter_content.update_idletasks()
            self.filter_canvas.configure(scrollregion=self.filter_canvas.bbox("all"))

    def reset_thumbnail_sizes(self):
        for btn in self.sub_filter_buttons.values():

            if hasattr(btn, 'normal_thumb'):
                btn.configure(image=btn.normal_thumb)
                btn.image = btn.normal_thumb

    def show_quality_popup(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return
        self.hide_popups()
        self.quality_popup = ttk.Frame(self.compress_frame, style='TFrame', borderwidth=2, relief='sunken')
        self.quality_popup.pack(fill='x', padx=5, pady=(0, 5))
        for widget in self.quality_popup.winfo_children():
            widget.destroy()
        tk.Label(self.quality_popup,
                text="Select Quality Percentage:",
                font=('Arial', 15),
                bg='#1E1E2E',
                fg='white').pack(anchor='w', padx=10, pady=5)
        btn_frame = ttk.Frame(self.quality_popup)
        btn_frame.pack(fill='x', padx=10, pady=5)
        for i, percent in enumerate(range(10, 101, 10)):
            row = i // 5
            col = i % 5

            if col == 0:
                row_frame = ttk.Frame(btn_frame)
                row_frame.pack(fill='x', pady=2)
            btn = tk.Button(
                row_frame,
                text=f"{percent}%",
                font=('Arial', 12, 'bold'),
                width=5,
                bg='#4a4a6e',
                fg='white',
                activebackground='#5a5a8e',
                border=0,
                command=lambda p=percent: self.apply_quality_compression(p)
            )
            btn.pack(side='left',fill='x',expand=True, padx=2)
        cancel_frame = ttk.Frame(self.quality_popup)
        cancel_frame.pack(fill='x', pady=(5, 5))
        tk.Button(
            cancel_frame,
            text="Cancel",
            font=('Arial', 12, 'bold'),
            command=self.hide_popups,
            bg="#e21212",
            fg='white',
            activebackground="#e96726",
            activeforeground='white',
            width=15
        ).pack(pady=5)

    def show_resize_popup(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return
        self.hide_popups()
        self.resize_popup = ttk.Frame(self.compress_frame, style='TFrame', borderwidth=2, relief='sunken')
        self.resize_popup.pack(fill='x', padx=5, pady=(0, 5))
        self.quality_popup.pack_forget()
        self.resize_popup.pack(fill='x', padx=20, pady=10)
        for widget in self.resize_popup.winfo_children():
            widget.destroy()
        self.maintain_aspect = tk.BooleanVar(value=True)
        self.original_width, self.original_height = self.current_image.size
        width_frame = ttk.Frame(self.resize_popup)
        width_frame.pack(fill='x', pady=5)
        tk.Label(width_frame, text="Width:", font=('Arial', 12), bg='#1E1E2E', fg='white').pack(side='left', padx=(0, 10))
        self.width_var = tk.StringVar(value=str(self.original_width))
        width_entry = tk.Entry(
                width_frame,
                textvariable=self.width_var,
                width=10,
                bg='#5A5A8E',   # Changed background color
                fg='white',
                insertbackground='white',
                relief='flat',
                font=('Arial', 12)
            )
        width_entry.pack(side='left')
        tk.Label(width_frame, text="px", font=('Arial', 12), bg='#1E1E2E', fg='white').pack(side='left', padx=(5, 0))
        height_frame = ttk.Frame(self.resize_popup)
        height_frame.pack(fill='x', pady=5)
        tk.Label(height_frame, text="Height:",font=('Arial', 12), bg='#1E1E2E', fg='white').pack(side='left', padx=(0, 10))
        self.height_var = tk.StringVar(value=str(self.original_height))
        height_entry = tk.Entry(
                height_frame,
                textvariable=self.height_var,
                width=10,
                bg='#5A5A8E',   # Changed background color
                fg='white',
                insertbackground='white',
                relief='flat',
                font=('Arial', 12)
            )
        height_entry.pack(side='left')
        tk.Label(height_frame, text="px",font=('Arial', 12), bg='#1E1E2E', fg='white').pack(side='left', padx=(5, 0))
        aspect_frame = ttk.Frame(self.resize_popup)
        aspect_frame.pack(fill='x', pady=5)
        tk.Checkbutton(
            aspect_frame,
            text="Maintain aspect ratio",
            font=('Arial', 12),
            background='#1E1E2E',
            fg='white',
            selectcolor='#1E1E2E',
            activebackground="#434374",
            activeforeground='white',
            foreground='white',
            variable=self.maintain_aspect
        ).pack(anchor='w')
        self.width_var.trace_add("write", self.update_dimension)
        self.height_var.trace_add("write", self.update_dimension)
        btn_frame = ttk.Frame(self.resize_popup)
        btn_frame.pack(fill='x', pady=(10, 0))
        tk.Button(
            btn_frame,
            text="Apply",
            command=self.apply_resize_compression,
            font=('Arial', 12, 'bold'), fg='white', bg='#4a4a7a',
            activebackground="#383860", activeforeground="lightgreen", border=0
        ).pack(side='left',fill='x',expand=True, padx=(10, 10), pady=(10))
        tk.Button(
            btn_frame,
            text="Cancel",
            command=self.hide_popups,
            font=('Arial', 12, 'bold'), fg='white', bg='red',
            activebackground="orange", activeforeground="white", border=0
        ).pack(side='left',fill='x',expand=True,padx=10, pady=10)

    def hide_popups(self):
        self.quality_popup.pack_forget()
        self.resize_popup.pack_forget()

    def update_dimension(self, *args):

        if not self.maintain_aspect.get():
            return

        try:

            if self.width_var.trace_info():
                new_width = int(self.width_var.get())
                ratio = new_width / self.original_width
                new_height = int(self.original_height * ratio)
                self.height_var.set(str(new_height))
            else:
                new_height = int(self.height_var.get())
                ratio = new_height / self.original_height
                new_width = int(self.original_width * ratio)
                self.width_var.set(str(new_width))

        except (ValueError, ZeroDivisionError):
            pass

    def apply_quality_compression(self, quality):

        if not self.current_image:
            return
        self.saved_after_last_change = False
        original = self.current_image

        try:
            buffer = io.BytesIO()

            if self.current_image.mode == 'RGBA':
                img = self.current_image.convert('RGB')
                img.save(buffer, format='JPEG', quality=quality)
            else:
                self.current_image.save(buffer, format='JPEG', quality=quality)
            buffer.seek(0)
            compressed_size = len(buffer.getvalue()) / 1024
            buffer.seek(0)
            self.current_image = Image.open(buffer)
            messagebox.showinfo(
                "Success",
                f"Image compressed to {quality}% quality\n"
                f"New size: {compressed_size:.2f} KB"
            )
            self.reset_filter_states()
            self.add_to_history()
            self.display_image_on_canvas()

        except Exception as e:
            self.current_image = original
            messagebox.showerror("Error", f"Compression failed: {str(e)}")

    def apply_resize_compression(self):

        if not self.current_image:
            return
        self.saved_after_last_change = False
        original = self.current_image

        try:
            width = int(self.width_var.get())
            height = int(self.height_var.get())
            MAX_DIMENSION = 10000

            if width <= 0 or height <= 0:
                raise ValueError("Dimensions must be positive numbers")

            if width > MAX_DIMENSION or height > MAX_DIMENSION:
                raise ValueError(f"Width and height must not exceed {MAX_DIMENSION} pixels.")
            self.current_image = self.current_image.resize(
                (width, height),
                Image.LANCZOS
            )
            self.reset_filter_states()
            self.add_to_history()
            self.display_image_on_canvas()
            self.hide_popups()
            messagebox.showinfo(
                "Success",
                f"Image resized to {width}×{height} pixels"
            )

        except ValueError as e:
            self.current_image = original
            messagebox.showerror("Error", f"Invalid dimensions: {str(e)}")

        except Exception as e:
            self.current_image = original
            messagebox.showerror("Error", f"Resizing failed: {str(e)}")

    def zoom_in(self, event=None):

        if not self.current_image:
            return
        new_zoom = min(1.0, self.zoom_level * 1.1)
        self.zoom_level = new_zoom
        self.zoom_var.set(new_zoom * 100)
        self.zoom_label.config(text=f"{int(new_zoom * 100)}%")
        self.display_image_on_canvas()

    def zoom_out(self, event=None):

        if not self.current_image:
            return
        new_zoom = max(0.1, self.zoom_level * 0.9)
        self.zoom_level = new_zoom
        self.zoom_var.set(new_zoom * 100)
        self.zoom_label.config(text=f"{int(new_zoom * 100)}%")
        self.display_image_on_canvas()

    def setup_drag_drop(self, parent_frame):
        drop_frame = ttk.Frame(parent_frame, style='TFrame')
        drop_frame.pack(fill='x', padx=10, pady=10)
        ttk.Label(drop_frame, text="Drag and drop Image here:",
                 font=('Arial', 15), foreground='#aaccff').pack(anchor='w', pady=(0, 5))
        self.drop_canvas = tk.Canvas(
            drop_frame,
            height=100,
            bg='#2a2a3a',
            bd=2,
            relief='sunken',
            highlightthickness=0
        )
        self.drop_canvas.pack(fill='x', pady=(0, 5))
        self.drop_text = self.drop_canvas.create_text(
                0, 0,
                text="Drop Image Here",
                fill="#aaccff",
                font=("Arial", 12, 'italic'),
                anchor='center'
            )

        def center_drop_text(event=None):
            width = self.drop_canvas.winfo_width()
            height = self.drop_canvas.winfo_height()

            if width > 0 and height > 0:
                self.drop_canvas.coords(
                    self.drop_text,
                    width / 2,
                    height / 2
                )
        self.drop_canvas.bind("<Configure>", center_drop_text)
        center_drop_text()
        self.drop_canvas.bind("<Enter>", self.on_drag_enter)
        self.drop_canvas.bind("<Leave>", self.on_drag_leave)
        self.drop_canvas.bind("<Button-1>", self.browse_files)
        self.drop_canvas.bind("<B1-Motion>", self.on_drag_motion)

        if dnd_supported:
            self.drop_canvas.drop_target_register(DND_FILES)
            self.drop_canvas.dnd_bind('<<DragEnter>>', self.on_dnd_enter)
            self.drop_canvas.dnd_bind('<<DragLeave>>', self.on_dnd_leave)
            self.drop_canvas.dnd_bind('<<Drop>>', self.on_dnd_drop)
        else:
            self.drop_canvas.itemconfig(self.drop_text,
                text="Drag/drop not supported\nClick 'Browse Files'")
        tk.Label(drop_frame, text="OR", bg="#1E1E2E",fg='white', font=('Arial', 15)).pack(pady=(5, 5))
        tk.Button(drop_frame, text="Browse Files   (Ctrl+B)", command=self.browse_files,
                  font=('Arial', 12), bg='#5A5A8E', fg='white', activebackground="#1E1E2E", activeforeground="white", border=3, borderwidth=5, relief='flat').pack(fill='x')

    def browse_files(self, event=None):

        if self.has_unsaved_changes():
            response = messagebox.askyesnocancel(
                "Save Changes?",
                "Do you want to save your changes before loading a new image?",
                detail="Your current changes will be lost.",
                icon=messagebox.WARNING
            )

            if response is None:
                return

            if response:

                if not self.export_image():
                    return
        self.import_image()

    def process_dropped_file(self, file_path):

        if self.has_unsaved_changes():
            response = messagebox.askyesnocancel(
                "Save Changes?",
                "Do you want to save your changes before loading a new image?",
                detail="Your current changes will be lost.",
                icon=messagebox.WARNING
            )

            if response is None:
                return

            if response:
                self.export_image()

        if any(file_path.lower().endswith(ext) for ext in
              ['.png','.jpg','.jpeg','.bmp','.ico','.gif','.tiff']):
            self.load_image(file_path)
        else:
            messagebox.showerror("Error", "Unsupported file format")
            self.drop_canvas.itemconfig(self.drop_text, text="      Drop Image Here")

    def load_image(self, file_path):

        try:
            self.sub_filter_intensities = {}
            self.effect_base_images = {}
            self.current_selected_sub_button = None
            self.current_effect = None
            self.base_thumbnail = None
            self.saved_after_last_change = True
            self.image_path = file_path
            self.original_image = Image.open(file_path)
            self.current_image = self.original_image.copy()
            self.add_to_history()
            self.zoom_level = 1.0
            self.zoom_var.set(100)
            self.zoom_label.config(text="100%")
            self.pan_offset = [0, 0]

            if not self.zoom_frame.winfo_ismapped():
                self.zoom_frame.pack(fill='x', padx=5, pady=(0, 5))
            self.set_exposure_slider_visibility(True)
            self.set_brightness_slider_visibility(True)
            self.set_contrast_slider_visibility(True)
            self.set_saturation_slider_visibility(True)
            self.set_vibrance_slider_visibility(True)
            self.set_wormth_slider_visibility(True)
            self.set_tint_slider_visibility(True)
            self.set_highlight_slider_visibility(True)
            self.set_shadows_slider_visibility(True)
            self.set_fade_slider_visibility(True)
            self.set_gain_slider_visibility(True)
            self.set_sharpness_slider_visibility(True)
            self.set_vignette_slider_visibility(True)
            self.set_doodle_slider_visibility(True)
            self.canvas.update_idletasks()
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()

            if canvas_width > 1 and canvas_height > 1:
                img_width, img_height = self.original_image.size
                scale_x = canvas_width / img_width
                scale_y = canvas_height / img_height
                fit_zoom = min(scale_x, scale_y, 1.0)
                self.zoom_level = fit_zoom
                self.zoom_var.set(fit_zoom * 100)
                self.zoom_label.config(text=f"{int(fit_zoom * 100)}%")
                self.initial_zoom_level = fit_zoom
            self.show_filter_buttons()
            self.display_image_on_canvas()
            self.update_all_thumbnails()
            self.image_info.configure(state='normal')
            self.image_info.delete("1.0", "end")

            def get_image_size(file_path):
                size_bytes = os.path.getsize(file_path)

                if size_bytes < 1024:
                    size = f"{size_bytes:.2f} B"
                elif size_bytes < 1024 ** 2:
                    size = f"{size_bytes / 1024:.2f} KB"
                elif size_bytes < 1024 ** 3:
                    size = f"{size_bytes / (1024 ** 2):.2f} MB"
                else:
                    size = f"{size_bytes / (1024 ** 3):.2f} GB"
                return size
            info = f"\n   File:  {os.path.basename(file_path)}\n"
            info += f"\n   Size:  {self.original_image.width}×{self.original_image.height} px | With {get_image_size(file_path)}\n"
            info += f"\n   Format:  {self.original_image.format}\n"
            info += f"\n   Mode:  {self.original_image.mode}"
            self.image_info.insert("1.0", info)
            self.image_info.configure(state='disabled')
            self.drop_canvas.itemconfig(self.drop_text, text="Drop Image Here")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to load image: {str(e)}")
            self.drop_canvas.itemconfig(self.drop_text, text="Drop Image Here")
        self.base_thumbnail = None

    def on_drag_enter(self, event):
        self.drop_canvas.configure(bg='#3a3a5a')
        self.drop_canvas.itemconfig(self.drop_text, text="Release to Import")

    def on_drag_leave(self, event):
        self.drop_canvas.configure(bg='#2a2a3a')
        self.drop_canvas.itemconfig(self.drop_text, text="Drop Image Here")

    def on_drag_motion(self, event):
        self.drop_canvas.configure(bg='#3a3a5a')
        self.drop_canvas.itemconfig(self.drop_text, text="Release to Import")

    def on_dnd_enter(self, event):
        self.drop_canvas.configure(bg='#4a4a7a')
        self.drop_canvas.itemconfig(self.drop_text, text="Drop to Import")
        return event.action

    def on_dnd_leave(self, event):
        self.drop_canvas.configure(bg='#2a2a3a')
        self.drop_canvas.itemconfig(self.drop_text, text="Drop Image Here")
        return event.action

    def on_dnd_drop(self, event):
        self.drop_canvas.configure(bg='#2a2a3a')
        self.drop_canvas.itemconfig(self.drop_text, text="Processing...")
        file_paths = self.root.tk.splitlist(event.data)

        if file_paths:
            self.process_dropped_file(file_paths[0])
        return event.action

    def on_drop(self, event):
        self.drop_canvas.configure(bg='#2a2a3a')
        self.drop_canvas.itemconfig(self.drop_text, text="Drop Image Here")

    def import_image(self):
        file_path = filedialog.askopenfilename(
            filetypes=[("Image Files", "*.png;*.jpg;*.jpeg;*.bmp;*.ico;*.gif;*.tiff")]
        )

        if file_path:
            self.load_image(file_path)

    def display_image_on_canvas(self, event=None):
        cursor_preserved = False
        cursor_coords = None
        self.canvas.delete("all")

        if not self.current_image:
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()

            if canvas_width > 1 and canvas_height > 1:
                self.canvas.create_text(
                    canvas_width/2,
                    canvas_height/2,
                    text="Image Area",
                    font=("Arial", 58, "bold"),
                    fill="#73767b",
                    anchor="center",
                    tags="placeholder"
                )

            if self.zoom_frame.winfo_ismapped():
                self.zoom_frame.pack_forget()
            return

        if self.eraser_cursor:
            cursor_coords = self.canvas.coords(self.eraser_cursor)
            cursor_preserved = True
            self.canvas.delete(self.eraser_cursor)

        if not self.current_image:

            if self.zoom_frame.winfo_ismapped():
                self.zoom_frame.pack_forget()
            return

        if not self.zoom_frame.winfo_ismapped():
            self.zoom_frame.pack(fill='x', padx=5, pady=(0, 5))
        self.canvas.delete("all")
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()

        if canvas_width <= 1 or canvas_height <= 1:
            return
        img_width, img_height = self.current_image.size
        fit_zoom = self.zoom_level
        scaled_width = int(img_width * fit_zoom)
        scaled_height = int(img_height * fit_zoom)
        pan_x, pan_y = self.pan_offset
        x_pos = (canvas_width - scaled_width) // 2 + pan_x
        y_pos = (canvas_height - scaled_height) // 2 + pan_y
        scaled_img = self.current_image.resize((scaled_width, scaled_height), Image.LANCZOS)

        if self.use_custom_bg and scaled_img.mode == 'RGBA':
            bg = Image.new('RGB', scaled_img.size, self.bg_removal_color[:3])
            scaled_img = Image.alpha_composite(bg.convert('RGBA'), scaled_img)
        elif scaled_img.mode == 'RGBA':
            scaled_img = self.composite_over_checkerboard(scaled_img)
        self.display_image = ImageTk.PhotoImage(scaled_img)
        self.canvas.create_image(x_pos, y_pos, anchor='nw', image=self.display_image)
        self.canvas_image_x = x_pos
        self.canvas_image_y = y_pos
        self.canvas_image_width = scaled_width
        self.canvas_image_height = scaled_height

        if self.crop_mode:
            self.draw_crop_rectangle()

        if cursor_preserved and self.eraser_mode and cursor_coords and len(cursor_coords) == 4:
            x0, y0, x1, y1 = cursor_coords
            center_x = (x0 + x1) / 2
            center_y = (y0 + y1) / 2
            r = (x1 - x0) / 2
            self.eraser_cursor = self.canvas.create_oval(
                center_x - r, center_y - r,
                center_x + r, center_y + r,
                outline="red", width=2, tags="eraser_cursor"
            )

        if not self.zoom_frame.winfo_ismapped():
            self.zoom_frame.pack(fill='x', padx=5, pady=(0, 5))

    def update_zoom(self, value):

        if not self.current_image or not hasattr(self, 'canvas_image_width') or self.canvas_image_width == 0:
            return
        new_zoom = min(1.0, float(value) / 100.0)
        mouse_x = self.canvas.winfo_pointerx() - self.canvas.winfo_rootx()
        mouse_y = self.canvas.winfo_pointery() - self.canvas.winfo_rooty()
        img_x = mouse_x - self.canvas_image_x
        img_y = mouse_y - self.canvas_image_y
        img_x_percent = img_x / self.canvas_image_width if self.canvas_image_width else 0
        img_y_percent = img_y / self.canvas_image_height if self.canvas_image_height else 0
        self.zoom_level = new_zoom
        self.zoom_label.config(text=f"{int(new_zoom * 100)}%")
        img_width, img_height = self.current_image.size
        new_width = int(img_width * new_zoom)
        new_height = int(img_height * new_zoom)
        new_img_x = img_x_percent * new_width
        new_img_y = img_y_percent * new_height
        self.pan_offset[0] += (mouse_x - new_img_x - self.canvas_image_x)
        self.pan_offset[1] += (mouse_y - new_img_y - self.canvas_image_y)
        max_pan_x = max(0, (new_width - self.canvas.winfo_width()) // 2)
        max_pan_y = max(0, (new_height - self.canvas.winfo_height()) // 2)
        self.pan_offset[0] = max(-max_pan_x, min(max_pan_x, self.pan_offset[0]))
        self.pan_offset[1] = max(-max_pan_y, min(max_pan_y, self.pan_offset[1]))
        self.display_image_on_canvas()

    def on_mouse_wheel(self, event):

        if not self.current_image:
            return
        zoom_factor = 1.05 if event.delta > 0 else 0.95
        new_zoom = min(1.0, self.zoom_level * zoom_factor)

        if abs(new_zoom - self.zoom_level) > 0.001:
            self.zoom_level = new_zoom
            self.zoom_var.set(new_zoom * 100)
            self.zoom_label.config(text=f"{int(new_zoom * 100)}%")
            self.display_image_on_canvas()

    def on_canvas_press(self, event):

        if self.crop_mode:

            if not self.crop_rect:
                return
            x, y = event.x, event.y
            x1, y1, x2, y2 = self.crop_rect
            tolerance = 15
            mid_x = (x1 + x2) // 2
            mid_y = (y1 + y2) // 2

            if abs(x - x1) < tolerance and abs(y - y1) < tolerance:
                self.crop_drag = "nw"
            elif abs(x - x2) < tolerance and abs(y - y1) < tolerance:
                self.crop_drag = "ne"
            elif abs(x - x1) < tolerance and abs(y - y2) < tolerance:
                self.crop_drag = "sw"
            elif abs(x - x2) < tolerance and abs(y - y2) < tolerance:
                self.crop_drag = "se"
            elif abs(x - mid_x) < tolerance and abs(y - y1) < tolerance:
                self.crop_drag = "n"
            elif abs(x - mid_x) < tolerance and abs(y - y2) < tolerance:
                self.crop_drag = "s"
            elif abs(x - x1) < tolerance and abs(y - mid_y) < tolerance:
                self.crop_drag = "w"
            elif abs(x - x2) < tolerance and abs(y - mid_y) < tolerance:
                self.crop_drag = "e"
            elif x1 <= x <= x2 and y1 <= y <= y2:
                self.crop_drag = "move"
            else:
                return
            self.crop_start_pos = (x, y)
            self.crop_start_rect = self.crop_rect.copy()
        else:
            self.pan_start = (event.x, event.y)

    def on_canvas_drag(self, event):

        if self.eraser_mode:
            self.update_eraser_cursor(x=event.x, y=event.y)

        if self.crop_mode:

            if not self.crop_mode or not self.crop_drag:
                return
            x, y = event.x, event.y
            dx = x - self.crop_start_pos[0]
            dy = y - self.crop_start_pos[1]
            img_x, img_y, img_w, img_h = self.canvas_image_x, self.canvas_image_y, self.canvas_image_width, self.canvas_image_height
            canvas_width = self.canvas.winfo_width()
            canvas_height = self.canvas.winfo_height()
            min_x = max(0, img_x)
            min_y = max(0, img_y)
            max_x = min(canvas_width, img_x + img_w)
            max_y = min(canvas_height, img_y + img_h)

            if self.crop_drag == "move":
                new_x1 = max(min_x, min(self.crop_start_rect[0] + dx, max_x))
                new_y1 = max(min_y, min(self.crop_start_rect[1] + dy, max_y))
                new_x2 = max(min_x, min(self.crop_start_rect[2] + dx, max_x))
                new_y2 = max(min_y, min(self.crop_start_rect[3] + dy, max_y))
                width = new_x2 - new_x1
                height = new_y2 - new_y1

                if new_x1 + width > max_x:
                    new_x1 = max_x - width

                if new_y1 + height > max_y:
                    new_y1 = max_y - height
                self.crop_rect = [new_x1, new_y1, new_x1 + width, new_y1 + height]
            else:
                x1, y1, x2, y2 = self.crop_start_rect

                if self.crop_drag == "n":
                    y1 = max(min_y, min(y1 + dy, y2 - 20))
                elif self.crop_drag == "s":
                    y2 = max(min_y, min(y2 + dy, max_y))
                elif self.crop_drag == "w":
                    x1 = max(min_x, min(x1 + dx, x2 - 20))
                elif self.crop_drag == "e":
                    x2 = max(min_x, min(x2 + dx, max_x))
                else:

                    if "n" in self.crop_drag:
                        y1 = max(min_y, min(y1 + dy, y2 - 20))

                    if "s" in self.crop_drag:
                        y2 = max(min_y, min(y2 + dy, max_y))

                    if "w" in self.crop_drag:
                        x1 = max(min_x, min(x1 + dx, x2 - 20))

                    if "e" in self.crop_drag:
                        x2 = max(min_x, min(x2 + dx, max_x))
                self.crop_rect = [x1, y1, x2, y2]
                self.crop_rect[0] = max(min_x, min(self.crop_rect[0], max_x))
                self.crop_rect[1] = max(min_y, min(self.crop_rect[1], max_y))
                self.crop_rect[2] = max(min_x, min(self.crop_rect[2], max_x))
                self.crop_rect[3] = max(min_y, min(self.crop_rect[3], max_y))
            self.canvas.delete("crop_rect")
            self.canvas.delete("crop_handle")
            self.canvas.delete("crop_overlay")
            self.draw_crop_rectangle()
        else:

            if self.pan_start:
                dx = event.x - self.pan_start[0]
                dy = event.y - self.pan_start[1]
                self.pan_offset[0] += dx
                self.pan_offset[1] += dy
                self.pan_start = (event.x, event.y)
                self.display_image_on_canvas()

    def on_canvas_release(self, event):

        if self.crop_mode:
            self.crop_drag = None
        else:
            self.pan_start = None

    def enter_crop_mode(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return

        if self.crop_mode:
            return
        self.crop_mode = True
        self.crop_control_frame.pack(fill='x', padx=0, pady=(5,0))
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        visible_x1 = max(self.canvas_image_x, 0)
        visible_y1 = max(self.canvas_image_y, 0)
        visible_x2 = min(self.canvas_image_x + self.canvas_image_width, canvas_width)
        visible_y2 = min(self.canvas_image_y + self.canvas_image_height, canvas_height)
        margin_x = (visible_x2 - visible_x1) * 0.1
        margin_y = (visible_y2 - visible_y1) * 0.1
        self.crop_rect = [
            visible_x1 + margin_x,
            visible_y1 + margin_y,
            visible_x2 - margin_x,
            visible_y2 - margin_y
        ]
        self.draw_crop_rectangle()

    def draw_crop_rectangle(self):

        if not self.crop_rect:
            return
        x1, y1, x2, y2 = self.crop_rect
        self.canvas.create_rectangle(
            x1, y1, x2, y2,
            outline="#4a9dff",
            width=2,
            dash=(4, 4),
            tags="crop_rect"
        )
        canvas_width = self.canvas.winfo_width()
        canvas_height = self.canvas.winfo_height()
        self.crop_rect[0] = max(0, min(self.crop_rect[0], canvas_width))
        self.crop_rect[1] = max(0, min(self.crop_rect[1], canvas_height))
        self.crop_rect[2] = max(0, min(self.crop_rect[2], canvas_width))
        self.crop_rect[3] = max(0, min(self.crop_rect[3], canvas_height))
        self.canvas.create_rectangle(
            0, 0, canvas_width, y1,
            fill="#000000",
            stipple="gray25",
            tags="crop_overlay"
        )
        self.canvas.create_rectangle(
            0, y2, canvas_width, canvas_height,
            fill="#000000",
            stipple="gray25",
            tags="crop_overlay"
        )
        self.canvas.create_rectangle(
            0, y1, x1, y2,
            fill="#000000",
            stipple="gray25",
            tags="crop_overlay"
        )
        self.canvas.create_rectangle(
            x2, y1, canvas_width, y2,
            fill="#000000",
            stipple="gray25",
            tags="crop_overlay"
        )
        handle_size = 10
        self.crop_handles = []
        self.crop_handles.append(self.canvas.create_rectangle(
            x1 - handle_size//2, y1 - handle_size//2,
            x1 + handle_size//2, y1 + handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        self.crop_handles.append(self.canvas.create_rectangle(
            x2 - handle_size//2, y1 - handle_size//2,
            x2 + handle_size//2, y1 + handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        self.crop_handles.append(self.canvas.create_rectangle(
            x1 - handle_size//2, y2 - handle_size//2,
            x1 + handle_size//2, y2 + handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        self.crop_handles.append(self.canvas.create_rectangle(
            x2 - handle_size//2, y2 - handle_size//2,
            x2 + handle_size//2, y2 + handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        mid_handle_size = 8
        self.crop_handles.append(self.canvas.create_rectangle(
            (x1 + x2) // 2 - mid_handle_size//2, y1 - mid_handle_size//2,
            (x1 + x2) // 2 + mid_handle_size//2, y1 + mid_handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        self.crop_handles.append(self.canvas.create_rectangle(
            (x1 + x2) // 2 - mid_handle_size//2, y2 - mid_handle_size//2,
            (x1 + x2) // 2 + mid_handle_size//2, y2 + mid_handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        self.crop_handles.append(self.canvas.create_rectangle(
            x1 - mid_handle_size//2, (y1 + y2) // 2 - mid_handle_size//2,
            x1 + mid_handle_size//2, (y1 + y2) // 2 + mid_handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        self.crop_handles.append(self.canvas.create_rectangle(
            x2 - mid_handle_size//2, (y1 + y2) // 2 - mid_handle_size//2,
            x2 + mid_handle_size//2, (y1 + y2) // 2 + mid_handle_size//2,
            fill="#4a9dff", outline="#ffffff", width=1, tags="crop_handle"
        ))
        for handle in self.crop_handles:
            self.canvas.tag_raise(handle)

    def apply_crop(self):

        if not self.crop_mode or not self.crop_rect:
            return
        self.saved_after_last_change = False
        scale_x = self.current_image.width / self.canvas_image_width
        scale_y = self.current_image.height / self.canvas_image_height
        x1, y1, x2, y2 = self.crop_rect
        img_x1 = int((x1 - self.canvas_image_x) * scale_x)
        img_y1 = int((y1 - self.canvas_image_y) * scale_y)
        img_x2 = int((x2 - self.canvas_image_x) * scale_x)
        img_y2 = int((y2 - self.canvas_image_y) * scale_y)

        if img_x2 > img_x1 and img_y2 > img_y1:
            self.current_image = self.current_image.crop((img_x1, img_y1, img_x2, img_y2))
            self.add_to_history()
            self.display_image_on_canvas()
        self.add_to_history()
        self.reset_filter_states()
        self.exit_crop_mode()

    def cancel_crop(self):
        self.exit_crop_mode()

    def exit_crop_mode(self):
        self.crop_mode = False
        self.crop_rect = None
        self.crop_drag = None
        self.crop_control_frame.pack_forget()
        self.display_image_on_canvas()

    def remove_background(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return
        self.original_with_bg = self.current_image.copy()
        self.remove_bg_button.config(state="disabled")
        self.show_animation()
        threading.Thread(target=self._remove_background_thread, daemon=True).start()
        self.reset_filter_states()

    def restore_original_background(self):

        if not self.current_image:
            return

        if not self.original_with_bg:
            messagebox.showinfo("Info", "No background to restore")
            return
        self.saved_after_last_change = False
        self.current_image = self.original_with_bg.copy()
        self.use_custom_bg = False
        self.reset_filter_states()
        self.add_to_history()
        self.display_image_on_canvas()

    def _remove_background_thread(self):

        try:
            img_byte_arr = io.BytesIO()
            self.current_image.save(img_byte_arr, format='PNG')
            img_bytes = img_byte_arr.getvalue()
            output_bytes = remove(img_bytes)
            output_image = Image.open(io.BytesIO(output_bytes)).convert("RGBA")
            self.root.after(0, lambda: self.on_background_removed(output_image))

        except Exception as e:
            self.root.after(0, lambda: self.on_removal_error(str(e)))

    def on_background_removed(self, output_image):
        self.stop_animation()
        self.remove_bg_button.config(state="normal")
        self.saved_after_last_change = False
        self.current_image = output_image
        self.add_to_history()
        self.display_image_on_canvas()

    def on_removal_error(self, error):
        self.stop_animation()
        self.remove_bg_button.config(state="normal")
        messagebox.showerror("Error", f"Failed to remove background: {error}")

    def choose_bg_color(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return
        color = colorchooser.askcolor(title="Choose Background Color",
                                     initialcolor=self.bg_color_var.get())

        if color[1]:
            self.bg_color_var.set(color[1])
            hex_color = color[1].lstrip('#')
            rgb = tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))
            self.bg_removal_color = rgb + (255,)
            self.use_custom_bg = True
            self.display_image_on_canvas()
            self.update_all_thumbnails()

    def remove_background_color(self):
        self.use_custom_bg = False
        self.display_image_on_canvas()
        self.update_all_thumbnails()

    def export_image(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return False
        format_name = self.format_var.get()
        file_types = {
            'PNG': [('PNG files', '*.png')],
            'JPG': [('JPEG files', '*.jpg')],
            'ICO': [('ICO files', '*.ico')]
        }

        default_ext = {
            'PNG': '.png',
            'JPG': '.jpg',
            'ICO': '.ico'
        }[format_name]
        file_path = filedialog.asksaveasfilename(

            defaultextension=default_ext,
            filetypes=file_types[format_name],
            initialfile=f"edited_image{default_ext}"
        )

        if not file_path:
            return False

        try:
            export_image = self.current_image.copy()

            if self.use_custom_bg and export_image.mode == 'RGBA':
                hex_color = self.bg_color_var.get().lstrip('#')
                bg_color = tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))
                bg = Image.new('RGB', export_image.size, bg_color)
                bg.paste(export_image, mask=export_image.split()[3])
                export_image = bg

            if format_name == 'JPG' and export_image.mode == 'RGBA' and not self.use_custom_bg:
                hex_color = self.bg_color_var.get().lstrip('#')
                bg_color = tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))
                bg = Image.new('RGB', export_image.size, bg_color)
                bg.paste(export_image, mask=export_image.split()[3])
                export_image = bg

            if format_name == 'ICO':

                if export_image.mode != 'RGBA':
                    export_image = export_image.convert('RGBA')
                sizes = [(size, size) for size in [16, 32, 48, 64, 128]]
                export_image.save(file_path, sizes=sizes)
            else:
                save_format = 'JPEG' if format_name == 'JPG' else format_name
                export_image.save(file_path, format=save_format, quality=95)
            messagebox.showinfo("Success", "Image exported successfully!")
            self.saved_after_last_change = True
            return True

        except Exception as e:
            messagebox.showerror("Error", f"Failed to export image: {str(e)}")
            return False

    def add_to_history(self):
        self.all_filter_states = {
            'sub_filter_intensities': self.sub_filter_intensities.copy(),
            'effect_base_images': {k: v.copy() for k, v in self.effect_base_images.items()},
            'current_effect': self.current_effect,
            'exposure_value': self.exposure_intensity,
            'brightness_value': self.brightness_intensity,
            'contrast_value': self.contrast_intensity,
            'saturation_value': self.saturation_intensity,
            'vibrance_value': self.vibrance_intensity,
            'wormth_value': self.wormth_intensity,
            'tint_value': self.tint_intensity,
            'highlight_value': self.highlight_intensity,
            'shadows_value': self.shadows_intensity,
            'fade_value': self.fade_intensity,
            'gain_value': self.gain_intensity,
            'sharpness_value': self.sharpness_intensity,
            'vignette_value': self.vignette_intensity,
        }
        history_state = {
            'image': self.current_image.copy(),
            'filter_states': self.all_filter_states.copy()
        }

        if not self.history or history_state['image'] != self.history[-1]['image']:

            if self.current_history_index < len(self.history) - 1:
                self.history = self.history[:self.current_history_index + 1]
            self.history.append(history_state)
            self.current_history_index = len(self.history) - 1

            if len(self.history) > 20:
                self.history.pop(0)
                self.current_history_index -= 1
        self.update_all_thumbnails()
        self.saved_after_last_change = False

    def reset_image(self):
        self.saved_after_last_change = False

        if self.rotation_mode:
            self.exit_rotation_mode()
        self.sub_filter_intensities = {}
        self.effect_base_images = {}
        self.current_selected_sub_button = None
        self.current_effect = None
        self.exposure_intensity = 0
        self.expause_intensity.set(0)
        self.brightness_intensity = 0
        self.brightness_intensity_var.set(0)
        self.contrast_intensity = 0
        self.contrast_intensity_var.set(0)
        self.saturation_intensity = 0
        self.saturation_intensity_var.set(0)
        self.vibrance_intensity = 0
        self.vibrance_intensity_var.set(0)
        self.wormth_intensity = 0
        self.wormth_intensity_var.set(0)
        self.tint_intensity = 0
        self.tint_intensity_var.set(0)
        self.highlight_intensity = 0
        self.highlight_intensity_var.set(0)
        self.shadows_intensity = 0
        self.shadows_intensity_var.set(0)
        self.fade_intensity = 0
        self.fade_intensity_var.set(0)
        self.gain_intensity = 0
        self.gain_intensity_var.set(0)
        self.sharpness_intensity = 0
        self.sharpness_intensity_var.set(0)
        self.vignette_intensity = 0
        self.vignette_intensity_var.set(0)

        if self.active_main_button:
            prev_btn = self.main_filter_buttons[self.active_main_button]
            prev_btn.image = self.create_rounded_button_image(bg="#3232D5")
            prev_btn.config(image=prev_btn.image, fg='white')
            prev_btn.image_ref = prev_btn.image
            self.active_main_button = None
        for widget in self.frame3.winfo_children():
            widget.destroy()
        for widget in self.frame2.winfo_children():
            widget.destroy()

        if self.original_image:
            self.current_image = self.original_image.copy()
            self.zoom_level = self.initial_zoom_level
            self.zoom_var.set(self.initial_zoom_level * 100)
            self.zoom_label.config(text=f"{int(self.initial_zoom_level * 100)}%")
            self.pan_offset = [0, 0]
            self.reset_filter_states()
            self.add_to_history()
            self.display_image_on_canvas()
            self.set_exposure_slider_visibility(True)
            self.set_brightness_slider_visibility(True)
            self.set_contrast_slider_visibility(True)
            self.set_saturation_slider_visibility(True)
            self.set_vibrance_slider_visibility(True)
            self.set_wormth_slider_visibility(True)
            self.set_tint_slider_visibility(True)
            self.set_highlight_slider_visibility(True)
            self.set_shadows_slider_visibility(True)
            self.set_fade_slider_visibility(True)
            self.set_gain_slider_visibility(True)
            self.set_sharpness_slider_visibility(True)
            self.set_vignette_slider_visibility(True)
            self.set_doodle_slider_visibility(True)
        else:
            self.set_exposure_slider_visibility(False)
            self.set_brightness_slider_visibility(False)
            self.set_contrast_slider_visibility(False)
            self.set_saturation_slider_visibility(False)
            self.set_vibrance_slider_visibility(False)
            self.set_wormth_slider_visibility(False)
            self.set_tint_slider_visibility(False)
            self.set_highlight_slider_visibility(False)
            self.set_shadows_slider_visibility(False)
            self.set_fade_slider_visibility(False)
            self.set_gain_slider_visibility(False)
            self.set_vignette_slider_visibility(False)
            self.set_doodle_slider_visibility(False)

    def undo(self, e=None):

        if self.doodle_mode:

            if self.current_history_index > 0:
                self.current_history_index -= 1
                state = self.history[self.current_history_index]
                self.current_image = state['image'].copy()
                self.doodle_temp_image = self.current_image.copy()
                self.display_image_on_canvas()
        else:

            if self.current_history_index > 0:
                self.current_history_index -= 1
                state = self.history[self.current_history_index]
                self.current_image = state['image'].copy()
                filter_states = state['filter_states']
                self.sub_filter_intensities = filter_states['sub_filter_intensities'].copy()
                self.effect_base_images = {k: v.copy() for k, v in filter_states['effect_base_images'].items()}
                self.current_effect = filter_states['current_effect']
                self.display_image_on_canvas()
                self.update_all_thumbnails()
                self.exposure_intensity = state['filter_states'].get('exposure_value', 0)
                self.brightness_intensity = state['filter_states'].get('brightness_value', 0)
                self.expause_intensity.set(self.exposure_intensity)
                self.skip_brightness_slider_events = True
                self.brightness_intensity_var.set(self.brightness_intensity)
                self.skip_brightness_slider_events = False
                self.contrast_intensity = state['filter_states'].get('contrast_value', 0)
                self.skip_contrast_slider_events = True
                self.contrast_intensity_var.set(self.contrast_intensity)
                self.skip_contrast_slider_events = False
                self.saturation_intensity = state['filter_states'].get('saturation_value', 0)
                self.skip_saturation_slider_events = True
                self.saturation_intensity_var.set(self.saturation_intensity)
                self.skip_saturation_slider_events = False
                self.vibrance_intensity = state['filter_states'].get('vibrance_value', 0)
                self.skip_vibrance_slider_events = True
                self.vibrance_intensity_var.set(self.vibrance_intensity)
                self.skip_vibrance_slider_events = False
                self.wormth_intensity = state['filter_states'].get('wormth_value', 0)
                self.skip_wormth_slider_events = True
                self.wormth_intensity_var.set(self.wormth_intensity)
                self.skip_wormth_slider_events = False
                self.wormth_intensity = state['filter_states'].get('wormth_value', 0)
                self.skip_wormth_slider_events = True
                self.wormth_intensity_var.set(self.wormth_intensity)
                self.skip_wormth_slider_events = False
                self.tint_intensity = state['filter_states'].get('tint_value', 0)
                self.skip_tint_slider_events = True
                self.tint_intensity_var.set(self.tint_intensity)
                self.skip_tint_slider_events = False
                self.highlight_intensity = state['filter_states'].get('highlight_value', 0)
                self.skip_highlight_slider_events = True
                self.highlight_intensity_var.set(self.highlight_intensity)
                self.skip_highlight_slider_events = False
                self.shadows_intensity = state['filter_states'].get('shadows_value', 0)
                self.skip_shadows_slider_events = True
                self.shadows_intensity_var.set(self.shadows_intensity)
                self.skip_shadows_slider_events = False
                self.fade_intensity = state['filter_states'].get('fade_value', 0)
                self.skip_fade_slider_events = True
                self.fade_intensity_var.set(self.fade_intensity)
                self.skip_fade_slider_events = False
                self.gain_intensity = state['filter_states'].get('gain_value', 0)
                self.skip_gain_slider_events = True
                self.gain_intensity_var.set(self.gain_intensity)
                self.skip_gain_slider_events = False
                self.sharpness_intensity = state['filter_states'].get('sharpness_value', 0)
                self.skip_sharpness_slider_events = True
                self.sharpness_intensity_var.set(self.sharpness_intensity)
                self.skip_sharpness_slider_events = False
                self.vignette_intensity = state['filter_states'].get('vignette_value', 0)
                self.skip_vignette_slider_events = True
                self.vignette_intensity_var.set(self.vignette_intensity)
                self.skip_vignette_slider_events = False

                if self.current_effect:
                    filter_name, sub_name = self.current_effect
                    self.show_sub_filters(filter_name)
                    self.setup_effect_slider(filter_name, sub_name)
                    key = (filter_name, sub_name)

                    if key in self.sub_filter_intensities:
                        self.effect_intensity.set(self.sub_filter_intensities[key])

    def redo(self, e=None):

        if self.doodle_mode:

            if self.current_history_index < len(self.history) - 1:
                self.current_history_index += 1
                state = self.history[self.current_history_index]
                self.current_image = state['image'].copy()
                self.doodle_temp_image = self.current_image.copy()
                self.display_image_on_canvas()
        else:

            if self.current_history_index < len(self.history) - 1:
                self.current_history_index += 1
                state = self.history[self.current_history_index]
                self.current_image = state['image'].copy()
                filter_states = state['filter_states']
                self.sub_filter_intensities = filter_states['sub_filter_intensities'].copy()
                self.effect_base_images = {k: v.copy() for k, v in filter_states['effect_base_images'].items()}
                self.current_effect = filter_states['current_effect']
                self.display_image_on_canvas()
                self.update_all_thumbnails()
                self.exposure_intensity = state['filter_states'].get('exposure_value', 0)
                self.expause_intensity.set(self.exposure_intensity)
                self.brightness_intensity = state['filter_states'].get('brightness_value', 0)
                self.skip_brightness_slider_events = True
                self.brightness_intensity_var.set(self.brightness_intensity)
                self.skip_brightness_slider_events = False
                self.contrast_intensity = state['filter_states'].get('contrast_value', 0)
                self.skip_contrast_slider_events = True
                self.contrast_intensity_var.set(self.contrast_intensity)
                self.skip_contrast_slider_events = False
                self.saturation_intensity = state['filter_states'].get('saturation_value', 0)
                self.skip_saturation_slider_events = True
                self.saturation_intensity_var.set(self.saturation_intensity)
                self.skip_saturation_slider_events = False
                self.vibrance_intensity = state['filter_states'].get('vibrance_value', 0)
                self.skip_vibrance_slider_events = True
                self.vibrance_intensity_var.set(self.vibrance_intensity)
                self.skip_vibrance_slider_events = False
                self.wormth_intensity = state['filter_states'].get('wormth_value', 0)
                self.skip_wormth_slider_events = True
                self.wormth_intensity_var.set(self.wormth_intensity)
                self.skip_wormth_slider_events = False
                self.tint_intensity = state['filter_states'].get('tint_value', 0)
                self.skip_tint_slider_events = True
                self.tint_intensity_var.set(self.tint_intensity)
                self.skip_tint_slider_events = False
                self.highlight_intensity = state['filter_states'].get('highlight_value', 0)
                self.skip_highlight_slider_events = True
                self.highlight_intensity_var.set(self.highlight_intensity)
                self.skip_highlight_slider_events = False
                self.shadows_intensity = state['filter_states'].get('shadows_value', 0)
                self.skip_shadows_slider_events = True
                self.shadows_intensity_var.set(self.shadows_intensity)
                self.skip_shadows_slider_events = False
                self.fade_intensity = state['filter_states'].get('fade_value', 0)
                self.skip_fade_slider_events = True
                self.fade_intensity_var.set(self.fade_intensity)
                self.skip_fade_slider_events = False
                self.gain_intensity = state['filter_states'].get('gain_value', 0)
                self.skip_gain_slider_events = True
                self.gain_intensity_var.set(self.gain_intensity)
                self.skip_gain_slider_events = False
                self.sharpness_intensity = state['filter_states'].get('sharpness_value', 0)
                self.skip_sharpness_slider_events = True
                self.sharpness_intensity_var.set(self.sharpness_intensity)
                self.skip_sharpness_slider_events = False
                self.vignette_intensity = state['filter_states'].get('vignette_value', 0)
                self.skip_vignette_slider_events = True
                self.vignette_intensity_var.set(self.vignette_intensity)
                self.skip_vignette_slider_events = False

                if self.current_effect:
                    filter_name, sub_name = self.current_effect
                    self.show_sub_filters(filter_name)
                    self.setup_effect_slider(filter_name, sub_name)
                    key = (filter_name, sub_name)

                    if key in self.sub_filter_intensities:
                        self.effect_intensity.set(self.sub_filter_intensities[key])

    def enter_rotation_mode(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return

        if self.rotation_mode:
            return
        self.rotation_mode = True
        self.rotation_angle = tk.DoubleVar(value=0)
        self.rotation_control_frame = tk.Frame(self.image_frame, bg='#1E1E2E')
        self.rotation_control_frame.pack(fill='x', side='bottom', padx=10, pady=10)
        top_line = tk.Frame(self.rotation_control_frame, bg='#1E1E2E')  # Container for X, slider, Y
        top_line.pack(pady=10)
        side_mirror_img = Image.open(resource_path(r"icons\side_mirror_img.png")).resize((32, 32))
        self.side_mirror_icon = ImageTk.PhotoImage(side_mirror_img)

        try:
            side_mirror_btn = tk.Button(top_line,
                        image=self.side_mirror_icon,
                        background='#1E1E2E',
                        activebackground="#3C4885",
                        borderwidth=0,
                    command=self.flip_image_horizontally)
            side_mirror_btn.pack(side=tk.LEFT, padx=10, pady=(18,0))

        except:
            pass
        angle_frame = tk.Frame(top_line, bg='#1E1E2E')
        angle_frame.pack(side=tk.LEFT)
        self.angle_label = ttk.Label(angle_frame, text="0.0°", font=('Arial', 12))
        self.angle_label.pack()
        self.rotation_slider = ttk.Scale(
            angle_frame,
            from_=-180,
            to=180,
            orient='horizontal',
            variable=self.rotation_angle,
            command=self.rotate_preview,
            length=400,
            style='Zoom.Horizontal.TScale'
        )
        self.rotation_slider.pack(pady=10)
        top_bottom_mirror_img = Image.open(resource_path(r"icons\top_bottom_mirror_img.png")).resize((32, 32))
        self.top_bottom_mirror_icon = ImageTk.PhotoImage(top_bottom_mirror_img)

        try:
            top_btm_mirror_btn = tk.Button(top_line,
                        image=self.top_bottom_mirror_icon,
                        background='#1E1E2E',
                        activebackground="#3C4885",
                        borderwidth=0,
                        command=self.flip_image_vertically
                    )
            top_btm_mirror_btn.pack(side=tk.LEFT, padx=10,pady=(18,0))

        except:
            pass
        button_frame = tk.Frame(self.rotation_control_frame, bg='#1E1E2E')
        button_frame.pack(pady=10)
        tk.Button(
            button_frame,
            text="Apply Rotation",
            command=self.apply_rotation,
            font=('Arial', 12, 'bold'),
            fg='white',
            bg='#4a4a7a',
            activebackground="#383860",
            activeforeground="lightgreen",
            border=0
        ).pack(side=tk.LEFT, padx=10)
        tk.Button(
            button_frame,
            text="Cancel",
            command=self.cancel_rotation,
            font=('Arial', 12, 'bold'),
            fg='white',
            bg='red',
            activebackground="orange",
            activeforeground="white",
            border=0
        ).pack(side=tk.LEFT, padx=10)
        self.rotation_backup = self.current_image.copy()
        self.rotation_angle.trace_add("write", self.update_angle_display)
        self.trace_id = self.rotation_angle.trace_add("write", self.update_angle_display)

    def flip_image_horizontally(self):

        if not self.current_image:
            return
        self.saved_after_last_change = False
        self.current_image = self.current_image.transpose(Image.FLIP_LEFT_RIGHT)
        self.reset_filter_states()
        self.add_to_history()
        self.display_image_on_canvas()

    def flip_image_vertically(self):

        if not self.current_image:
            return
        self.saved_after_last_change = False
        self.current_image = self.current_image.transpose(Image.FLIP_TOP_BOTTOM)
        self.reset_filter_states()
        self.add_to_history()
        self.display_image_on_canvas()

    def update_angle_display(self, *args):

        if not self.rotation_mode or not hasattr(self, 'angle_label'):
            return

        try:
            angle = self.rotation_angle.get()
            self.angle_label.config(text=f"{angle:.1f}°")

        except tk.TclError:
            pass

    def rotate_preview(self, angle):

        if not self.rotation_mode:
            return

        try:
            angle_val = float(angle)
            rotated_img = self.rotation_backup.rotate(
                angle_val,
                expand=True,
                fillcolor=self.get_bg_color_for_rotation()
            )
            self.current_image = rotated_img
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Rotation error: {str(e)}")

    def get_bg_color_for_rotation(self):
        hex_color = self.bg_color_var.get().lstrip('#')

        if len(hex_color) == 6:
            return tuple(int(hex_color[i:i+2], 16) for i in (0, 2, 4))
        return (42, 42, 58)

    def apply_rotation(self):

        if not self.current_image:
            return
        self.saved_after_last_change = False
        self.reset_filter_states()
        self.add_to_history()
        self.exit_rotation_mode()

    def cancel_rotation(self):

        if self.rotation_mode:
            self.current_image = self.rotation_backup
            self.display_image_on_canvas()
            self.exit_rotation_mode()

    def exit_rotation_mode(self):

        if not self.rotation_mode:
            return

        if hasattr(self, 'trace_id'):
            self.rotation_angle.trace_remove("write", self.trace_id)
            del self.trace_id
        self.rotation_mode = False

        if hasattr(self, 'rotation_control_frame'):
            self.rotation_control_frame.pack_forget()
            self.rotation_control_frame.destroy()
            del self.rotation_control_frame
        self.rotation_angle.set(0.0)

        if hasattr(self, 'rotation_backup'):
            del self.rotation_backup

    def show_animation(self):
        self.animation_running = True
        self.dots = "|...|...|...|...|...|...|...|"
        self.dot_index = 0
        self.animate_line()

    def animate_line(self):

        if self.animation_running:
            visible = self.dots[:self.dot_index] + "█" + self.dots[self.dot_index+1:]
            self.animation_label.config(text=visible)
            self.dot_index = (self.dot_index + 1) % len(self.dots)
            self.root.after(100, self.animate_line)

    def stop_animation(self):
        self.animation_running = False
        self.animation_label.config(text="")

    def composite_over_checkerboard(self, img, checker_size=10):
        w, h = img.size
        checker = Image.new("RGB", (w, h), "#f1f1f1")  # Dark background
        draw = ImageDraw.Draw(checker)
        for y in range(0, h, checker_size):
            for x in range(0, w, checker_size):

                if (x // checker_size + y // checker_size) % 2 == 0:
                    draw.rectangle([x, y, x + checker_size, y + checker_size], fill="#252323")

        if img.mode == 'RGBA':
            checker = checker.convert("RGBA")
            return Image.alpha_composite(checker, img)
        return img

    def enter_eraser_mode(self):

        if not self.current_image:
            messagebox.showwarning("No Image", "Please import an image first")
            return

        if self.crop_mode:
            self.exit_crop_mode()

        if self.rotation_mode:
            self.exit_rotation_mode()
        self.eraser_mode = True
        self.eraser_stroke_image = None
        self.eraser_drawing = False
        self.eraser_backup = self.current_image.copy()
        self.eraser_control_frame.pack(fill='x', padx=10, pady=5)
        self.original_bindings = {
            "<B1-Motion>": self.canvas.bind("<B1-Motion>"),
            "<Button-1>": self.canvas.bind("<Button-1>"),
            "<ButtonRelease-1>": self.canvas.bind("<ButtonRelease-1>"),
            "<Motion>": self.canvas.bind("<Motion>"),
            "<Leave>": self.canvas.bind("<Leave>")
        }
        self.canvas.bind("<B1-Motion>", lambda e: self.erase(e))
        self.canvas.bind("<Button-1>", lambda e: self.erase(e))
        self.canvas.bind("<ButtonRelease-1>", lambda e: self.reset_eraser_last(e))
        self.canvas.bind("<Motion>", lambda e: self.update_eraser_cursor(e))
        self.canvas.bind("<Leave>", lambda e: self.hide_eraser_cursor(e))

    def update_brush_size(self, value):
        self.brush_size = int(value)

        if self.eraser_cursor:
            self.hide_eraser_cursor()
            x = self.canvas.winfo_pointerx() - self.canvas.winfo_rootx()
            y = self.canvas.winfo_pointery() - self.canvas.winfo_rooty()

            if 0 <= x < self.canvas.winfo_width() and 0 <= y < self.canvas.winfo_height():
                self.update_eraser_cursor(x, y)

    def update_eraser_cursor(self, event=None, x=None, y=None):

        if self.eraser_cursor:
            self.canvas.delete(self.eraser_cursor)
            self.eraser_cursor = None

        if event:
            x, y = event.x, event.y
        elif x is None or y is None:
            return
        r = max(1, int(self.brush_size * self.zoom_level/0.75))
        self.eraser_cursor = self.canvas.create_oval(
            x - r, y - r,
            x + r, y + r,
            outline="red", width=2, tags="eraser_cursor"
        )

    def hide_eraser_cursor(self, event=None):

        if self.eraser_cursor:
            self.canvas.delete(self.eraser_cursor)
            self.eraser_cursor = None

    def reset_eraser_last(self, event):

        if self.eraser_drawing:
            self.add_to_history()
            self.eraser_drawing = False
            self.last_eraser_pos = None

    def erase(self, event):

        if not self.eraser_mode or self.crop_mode or self.rotation_mode:
            return

        if not self.eraser_drawing:
            self.eraser_drawing = True
            self.eraser_stroke_image = self.current_image.copy()
            self.last_eraser_pos = None
        x = event.x - self.canvas_image_x
        y = event.y - self.canvas_image_y

        if not (0 <= x < self.canvas_image_width and 0 <= y < self.canvas_image_height):
            return
        orig_x = int(x / self.zoom_level)
        orig_y = int(y / self.zoom_level)
        img_width, img_height = self.current_image.size

        if orig_x < 0 or orig_y < 0 or orig_x >= img_width or orig_y >= img_height:
            return
        draw = ImageDraw.Draw(self.eraser_stroke_image)
        r = max(1, int(self.brush_size / self.zoom_level  /4.6))

        if self.last_eraser_pos:
            last_x, last_y = self.last_eraser_pos
            distance = max(abs(orig_x - last_x), abs(orig_y - last_y))
            steps = max(1, distance // max(1, r//4))
            for i in range(1, steps + 1):
                frac = i / steps
                interp_x = int(last_x + frac * (orig_x - last_x))
                interp_y = int(last_y + frac * (orig_y - last_y))
                draw.ellipse(
                    (interp_x - r, interp_y - r,
                    interp_x + r, interp_y + r),
                    fill=(0,0,0,0)
                )
        draw.ellipse(
            (orig_x - r, orig_y - r,
            orig_x + r, orig_y + r),
            fill=(0,0,0,0)
        )
        self.last_eraser_pos = (orig_x, orig_y)
        self.current_image = self.eraser_stroke_image
        self.display_image_on_canvas()

        if self.eraser_mode:
            self.update_eraser_cursor(x=event.x, y=event.y)

    def apply_eraser(self):
        self.saved_after_last_change = False
        self.reset_filter_states()
        self.add_to_history()
        self.exit_eraser_mode()

    def cancel_eraser(self):
        self.current_image = self.eraser_backup
        self.display_image_on_canvas()
        self.exit_eraser_mode()

    def exit_eraser_mode(self):
        self.eraser_mode = False
        self.eraser_control_frame.pack_forget()
        self.last_eraser_pos = None
        self.hide_eraser_cursor()
        for event, handler in self.original_bindings.items():

            if handler:
                self.canvas.bind(event, handler)
            else:
                self.canvas.unbind(event)
        self.original_bindings = {}

    def run(self):
        self.canvas.bind("<Configure>", lambda e: self.display_image_on_canvas())
        self.root.mainloop()

    def setup_effect_slider(self, filter_name, sub_name):

        if hasattr(self, 'current_selected_sub_button') and self.current_selected_sub_button:
            prev_btn, prev_label = self.current_selected_sub_button
            prev_label.config(fg='white', font=('Arial', 10))
        self.reset_thumbnail_sizes()
        btn = self.sub_filter_buttons.get(sub_name)

        if not btn:
            return
        frame = btn.master
        label = None
        for child in frame.winfo_children():

            if isinstance(child, tk.Label) and hasattr(child, 'sub_name') and child.sub_name == sub_name:
                label = child
                break

        if not label:
            return

        if not hasattr(self, 'base_thumbnail') or self.base_thumbnail is None:

            if self.current_image:
                base_img = self.current_image.copy()
                base_img.thumbnail((60, 60), Image.LANCZOS)
                self.base_thumbnail = base_img
            else:
                return
        base_img = self.base_thumbnail.copy()
        large_thumb = self.make_rounded_thumb(base_img, size=(65, 65))
        btn.configure(image=large_thumb)
        btn.image = large_thumb
        label.config(fg='#57fa11', font=('Arial', 12, 'bold'))
        self.current_selected_sub_button = (btn, label)
        for widget in self.frame3.winfo_children():
            widget.destroy()
        self.effect_intensity = tk.DoubleVar(value=0)
        key = (filter_name, sub_name)
        self.effect_base_images[key] = self.current_image.copy()
        self.effect_base_image = self.effect_base_images[key].copy()

        if key in self.sub_filter_intensities:
            self.effect_intensity.set(self.sub_filter_intensities[key])
        self.last_slider_value = self.effect_intensity.get()
        slider = tk.Scale(
            self.frame3,
            from_=0,
            to=100,
            sliderlength=20,
            width=8,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white'   ,
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            variable=self.effect_intensity,
            length=250,
            sliderrelief='flat',
            command=lambda v: self.on_slider_drag(filter_name, sub_name, float(v))
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0,5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonRelease-1>",
               lambda e: self.on_slider_release(filter_name, sub_name))
        key = (filter_name, sub_name)

        if key not in self.effect_base_images:
            self.effect_base_images[key] = self.current_image.copy()
        self.current_effect = (filter_name, sub_name)
        self.effect_base_image = self.effect_base_images[key].copy()

        if key in self.sub_filter_intensities:
            self.apply_sub_filter(filter_name, sub_name, self.sub_filter_intensities[key])

    def apply_effect_by_name(self, img, effect_name, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')

        if has_alpha:
            img = img.convert('RGBA')
            img.putalpha(alpha)

        if effect_name == "Arctic":
            img = self.apply_arctic_effect(img, intensity)
        elif effect_name == "Cobalt":
            img = self.apply_cobalt_effect(img, intensity)
        elif effect_name == "Harvest":
            img = self.apply_harvest_effect(img, intensity)
        elif effect_name == "Pumpkin":
            img = self.apply_pumpkin_effect(img, intensity)
        elif effect_name == "Noir":
            img = self.apply_noir_effect(img, intensity)
        elif effect_name == "Verdant":
            img = self.apply_verdant_effect(img, intensity)
        elif effect_name == "Zenith":
            img = self.apply_zenith_effect(img, intensity)
        elif effect_name == "Bloom":
            img = self.apply_bloom_effect(img, intensity)
        elif effect_name == "R600":
            img = self.apply_r600_effect(img, intensity)
        elif effect_name == "P100F":
            img = self.apply_p100f_effect(img, intensity)
        elif effect_name == "f-50":
            img = self.apply_f50_effect(img, intensity)
        elif effect_name == "KC64":
            img = self.apply_kc64_effect(img, intensity)
        elif effect_name == "V-250":
            img = self.apply_v250_effect(img, intensity)
        elif effect_name == "H-400":
            img = self.apply_h400_effect(img, intensity)
        elif effect_name == "KP160":
            img = self.apply_kp160_effect(img, intensity)
        elif effect_name == "FC400":
            img = self.apply_fc400_effect(img, intensity)
        elif effect_name == "C-50D":
            img = self.apply_c50d_effect(img, intensity)
        elif effect_name == "KG200":
            img = self.apply_kg200_effect(img, intensity)
        elif effect_name == "Vivid":
            img = self.apply_vivid_effect(img, intensity)
        elif effect_name == "Sangria":
            img = self.apply_sangria_effect(img, intensity)
        elif effect_name == "Rhodium":
            img = self.apply_rhodium_effect(img, intensity)
        elif effect_name == "Lime":
            img = self.apply_lime_effect(img, intensity)
        elif effect_name == "Film":
            img = self.apply_film_effect(img, intensity)
        elif effect_name == "Purple":
            img = self.apply_purple_effect(img, intensity)
        elif effect_name == "Colour fo..":
            img = self.apply_colour_fo_effect(img, intensity)
        elif effect_name == "Starlight":
            img = self.apply_starlight_effect(img, intensity)
        elif effect_name == "Sunbeam":
            img = self.apply_sunbeam_effect(img, intensity)
        elif effect_name == "Azure":
            img = self.apply_azure_effect(img, intensity)
        elif effect_name == "Bud":
            img = self.apply_bud_effect(img, intensity)
        elif effect_name == "Original":
            img = self.apply_original_effect(img, intensity)
        elif effect_name == "Holiday":
            img = self.apply_holiday_effect(img, intensity)
        elif effect_name == "Oxygen":
            img = self.apply_oxygen_effect(img, intensity)
        elif effect_name == "Mint":
            img = self.apply_mint_effect(img, intensity)
        elif effect_name == "Nature":
            img = self.apply_nature_effect(img, intensity)
        elif effect_name == "Pink":
            img = self.apply_pink_effect(img, intensity)
        elif effect_name == "Gourmand":
            img = self.apply_gourmand_effect(img, intensity)
        elif effect_name == "Food":
            img = self.apply_food_effect(img, intensity)
        elif effect_name == "Soda":
            img = self.apply_soda_effect(img, intensity)
        elif effect_name == "Mango":
            img = self.apply_mango_effect(img, intensity)
        elif effect_name == "Action":
            img = self.apply_action_effect(img, intensity)
        elif effect_name == "Drama":
            img = self.apply_drama_effect(img, intensity)
        elif effect_name == "Horror":
            img = self.apply_horror_effect(img, intensity)
        elif effect_name == "Comedy":
            img = self.apply_comedy_effect(img, intensity)
        elif effect_name == "Sci-Fi":
            img = self.apply_scifi_effect(img, intensity)
        elif effect_name == "Romance":
            img = self.apply_romance_effect(img, intensity)
        elif effect_name == "Fantasy":
            img = self.apply_fantasy_effect(img, intensity)
        elif effect_name == "Landscape":
            img = self.apply_landscape_effect(img, intensity)
        elif effect_name == "Cityscape":
            img = self.apply_cityscape_effect(img, intensity)
        elif effect_name == "Seascape":
            img = self.apply_seascape_effect(img, intensity)
        elif effect_name == "Mountains":
            img = self.apply_mountains_effect(img, intensity)
        elif effect_name == "Beach":
            img = self.apply_beach_effect(img, intensity)
        elif effect_name == "Urban":
            img = self.apply_urban_effect(img, intensity)
        elif effect_name == "Moonlight":
            img = self.apply_moonlight_effect(img, intensity)
        elif effect_name == "City Lights":
            img = self.apply_city_lights_effect(img, intensity)
        elif effect_name == "Stars":
            img = self.apply_stars_effect(img, intensity)
        elif effect_name == "Neon":
            img = self.apply_neon_effect(img, intensity)
        elif effect_name == "Fireworks":
            img = self.apply_fireworks_effect(img, intensity)
        elif effect_name == "Warm Glow":
            img = self.apply_warm_glow_effect(img, intensity)
        elif effect_name == "Golden Hour":
            img = self.apply_golden_hour_effect(img, intensity)
        elif effect_name == "Sunset":
            img = self.apply_sunset_effect(img, intensity)
        elif effect_name == "Candlelight":
            img = self.apply_candlelight_effect(img, intensity)
        elif effect_name == "High Contrast":
            img = self.apply_high_contrast_effect(img, intensity)
        elif effect_name == "Low Contrast":
            img = self.apply_low_contrast_effect(img, intensity)
        elif effect_name == "Grainy":
            img = self.apply_grainy_effect(img, intensity)
        elif effect_name == "Smooth":
            img = self.apply_smooth_effect(img, intensity)
        elif effect_name == "Vintage":
            img = self.apply_vintage_effect(img, intensity)
        elif effect_name == "Spring":
            img = self.apply_spring_effect(img, intensity)
        elif effect_name == "Summer":
            img = self.apply_summer_effect(img, intensity)
        elif effect_name == "Autumn":
            img = self.apply_autumn_effect(img, intensity)
        elif effect_name == "Winter":
            img = self.apply_winter_effect(img, intensity)
        elif effect_name == "Expouse":
            img = self.apply_exposure_effect(img, intensity)
        elif effect_name == "Brightness":
            img = self.apply_brightness_effect(img, intensity)
        elif effect_name == "Contrast":
            img = self.apply_contrast_effect(img, intensity)
        elif effect_name == "Saturation":
            img = self.apply_saturation_effect(img, intensity)
        elif effect_name == "Vibrance":
            img = self.apply_vibrance_effect(img, intensity)
        elif effect_name == "Wormth":
            img = self.apply_wormth_effect(img, intensity)
        elif effect_name == "Tint":
            img = self.apply_tint_effect(img, intensity)
        elif effect_name == "Highlight":
            img = self.apply_highlight_effect(img, intensity)
        elif effect_name == "Shadows":
            img = self.apply_shadows_effect(img, intensity)
        elif effect_name == "Fade":
            img = self.apply_fade_effect(img, intensity)
        elif effect_name == "Gain":
            img = self.apply_gain_effect(img, intensity)
        elif effect_name == "Sharpness":
            img = self.apply_sharpness_effect(img, intensity)
        elif effect_name == "Vignette":
            img = self.apply_vignette_effect(img, intensity)
        return img

    def apply_sub_filter(self, filter_name, sub_name, intensity):

        if sub_name == "Expouse":
            normalized_intensity = intensity / 100.0
        else:
            normalized_intensity = intensity / 100.0

        if intensity == self.last_slider_value:
            return
        self.last_slider_value = intensity
        key = (filter_name, sub_name)
        self.sub_filter_intensities[key] = intensity

        if key not in self.effect_base_images:
            self.effect_base_images[key] = self.current_image.copy()
        img = self.effect_base_images[key].copy()

        try:
            img = self.apply_effect_by_name(img, sub_name, normalized_intensity)
            self.current_image = img
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Error applying {sub_name} effect: {str(e)}")

    def on_slider_drag(self, filter_name, sub_name, intensity):
        key = (filter_name, sub_name)
        self.sub_filter_intensities[key] = intensity
        self.apply_sub_filter(filter_name, sub_name, intensity)

    def on_slider_release(self, filter_name, sub_name):
        self.add_to_history()
        self.saved_after_last_change = False

    def apply_arctic_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: i * (1 - intensity * 0.5))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        return Image.merge('RGB', (r, g, b))

    def apply_cobalt_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        return enhancer.enhance(1 + intensity * 0.7)

    def apply_harvest_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.2)))
        return Image.merge('RGB', (r, g, b))

    def apply_pumpkin_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.1)))
        b = b.point(lambda i: i * (1 - intensity * 0.6))
        return Image.merge('RGB', (r, g, b))

    def apply_noir_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        img = img.convert('L')
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 1.5)

    def apply_verdant_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.6)))
        b = b.point(lambda i: i * (1 - intensity * 0.2))
        return Image.merge('RGB', (r, g, b))

    def apply_zenith_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        enhancer = ImageEnhance.Brightness(Image.merge('RGB', (r, g, b)))
        return enhancer.enhance(1 + intensity * 0.3)

    def apply_bloom_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        blur_radius = int(5 * intensity)
        blurred = img.filter(ImageFilter.GaussianBlur(blur_radius))
        return Image.blend(img, blurred, intensity * 0.7)

    def apply_r600_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        sepia = Image.new('RGB', img.size, (112, 66, 20))
        return Image.blend(img, sepia, intensity * 0.6)

    def apply_p100f_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Contrast(img)
        img = enhancer.enhance(1 + intensity * 0.8)
        fade = Image.new('RGB', img.size, (240, 240, 240))
        return Image.blend(img, fade, intensity * 0.3)

    def apply_f50_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 - intensity * 0.5)
        blue_tint = Image.new('RGB', img.size, (200, 220, 255))
        return Image.blend(img, blue_tint, intensity * 0.4)

    def apply_kc64_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        warm = Image.new('RGB', img.size, (255, 220, 180))
        img = Image.blend(img, warm, intensity * 0.4)
        r, g, b = img.split()
        b = b.point(lambda i: i * (1 - intensity * 0.3))
        return Image.merge('RGB', (r, g, b))

    def apply_v250_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 1.2)
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 0.8)

    def apply_h400_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 - intensity * 0.6)
        cool_tint = Image.new('RGB', img.size, (180, 220, 240))
        return Image.blend(img, cool_tint, intensity * 0.5)

    def apply_kp160_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        golden = Image.new('RGB', img.size, (255, 220, 150))
        img = Image.blend(img, golden, intensity * 0.6)
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.2)))
        return Image.merge('RGB', (r, g, b))

    def apply_fc400_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Brightness(img)
        img = enhancer.enhance(1 + intensity * 0.4)
        fade = Image.new('RGB', img.size, (240, 240, 240))
        return Image.blend(img, fade, intensity * 0.3)

    def apply_c50d_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        cool = Image.new('RGB', img.size, (180, 220, 255))
        img = Image.blend(img, cool, intensity * 0.5)
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 0.7)

    def apply_kg200_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        green_tint = Image.new('RGB', img.size, (180, 220, 180))
        img = Image.blend(img, green_tint, intensity * 0.4)
        r, g, b = img.split()
        r = r.point(lambda i: i * (1 - intensity * 0.2))
        return Image.merge('RGB', (r, g, b))

    def apply_vivid_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 1.2)
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 0.5)

    def apply_sangria_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.6)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        return Image.merge('RGB', (r, g, b))

    def apply_rhodium_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        gray = img.convert('L')
        r = gray.point(lambda i: min(255, i * 1.2))
        g = gray.point(lambda i: min(255, i * 1.1))
        b = gray
        return Image.merge('RGB', (r, g, b))

    def apply_lime_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.8)))
        b = b.point(lambda i: i * (1 - intensity * 0.4))
        return Image.merge('RGB', (r, g, b))

    def apply_film_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        grain = Image.effect_noise(img.size, intensity * 50)
        img = Image.blend(img, grain, intensity * 0.1)
        fade = Image.new('RGB', img.size, (240, 240, 240))
        return Image.blend(img, fade, intensity * 0.3)

    def apply_purple_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.6)))
        g = g.point(lambda i: i * (1 - intensity * 0.2))
        return Image.merge('RGB', (r, g, b))

    def apply_colour_fo_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 0.8)
        vignette = Image.new('L', img.size, 0)
        draw = ImageDraw.Draw(vignette)
        width, height = img.size
        draw.ellipse((0, 0, width, height), fill=255)
        vignette = vignette.filter(ImageFilter.GaussianBlur(width/4))
        vignette = ImageEnhance.Brightness(vignette).enhance(1 - intensity * 0.3)
        return Image.composite(img, Image.new('RGB', img.size, (50, 50, 50)), vignette)

    def apply_starlight_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        cool = Image.new('RGB', img.size, (180, 220, 255))
        img = Image.blend(img, cool, intensity * 0.4)
        sparkles = Image.effect_noise(img.size, intensity * 100).convert('L')
        sparkles = sparkles.point(lambda i: 255 if i > 200 else 0)
        bright = Image.new('RGB', img.size, (255, 255, 255))
        return Image.composite(bright, img, sparkles)

    def apply_sunbeam_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        warm = Image.new('RGB', img.size, (255, 230, 180))
        img = Image.blend(img, warm, intensity * 0.3)
        gradient = Image.new('L', img.size, 0)
        draw = ImageDraw.Draw(gradient)
        width, height = img.size
        center_x, center_y = width // 2, height // 2
        max_radius = max(width, height) // 2
        for r in range(max_radius, 0, -10):
            alpha = int(255 * (1 - r/max_radius) * intensity)
            draw.ellipse((center_x - r, center_y - r, center_x + r, center_y + r), fill=alpha)
        bright = Image.new('RGB', img.size, (255, 255, 200))
        return Image.composite(bright, img, gradient)

    def apply_azure_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.8)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.2)))
        return Image.merge('RGB', (r, g, b))

    def apply_bud_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.7)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.1)))
        return Image.merge('RGB', (r, g, b))

    def apply_original_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Contrast(img)
        img = enhancer.enhance(1 + intensity * 0.2)
        enhancer = ImageEnhance.Color(img)
        return enhancer.enhance(1 + intensity * 0.3)

    def apply_holiday_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 1.0)
        warm = Image.new('RGB', img.size, (255, 220, 180))
        return Image.blend(img, warm, intensity * 0.2)

    def apply_oxygen_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Brightness(img)
        img = enhancer.enhance(1 + intensity * 0.3)
        enhancer = ImageEnhance.Contrast(img)
        img = enhancer.enhance(1 + intensity * 0.4)
        r, g, b = img.split()
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.2)))
        return Image.merge('RGB', (r, g, b))

    def apply_mint_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        return Image.merge('RGB', (r, g, b))

    def apply_nature_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.6)))
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.2)))
        return Image.merge('RGB', (r, g, b))

    def apply_pink_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        return Image.merge('RGB', (r, g, b))

    def apply_gourmand_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        b = b.point(lambda i: i * (1 - intensity * 0.2))
        return Image.merge('RGB', (r, g, b))

    def apply_food_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 1.0)
        warm = Image.new('RGB', img.size, (255, 230, 200))
        return Image.blend(img, warm, intensity * 0.2)

    def apply_soda_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.2)))
        return Image.merge('RGB', (r, g, b))

    def apply_mango_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.6)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        b = b.point(lambda i: i * (1 - intensity * 0.4))
        return Image.merge('RGB', (r, g, b))

    def apply_action_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Contrast(img)
        img = enhancer.enhance(1 + intensity * 1.0)
        cool = Image.new('RGB', img.size, (180, 220, 255))
        return Image.blend(img, cool, intensity * 0.3)

    def apply_drama_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 - intensity * 0.7)
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 0.8)

    def apply_horror_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Brightness(img)
        img = enhancer.enhance(1 - intensity * 0.4)
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        g = g.point(lambda i: i * (1 - intensity * 0.4))
        b = b.point(lambda i: i * (1 - intensity * 0.4))
        return Image.merge('RGB', (r, g, b))

    def apply_comedy_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 1.5)
        enhancer = ImageEnhance.Brightness(img)
        return enhancer.enhance(1 + intensity * 0.3)

    def apply_scifi_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.6)))
        img = Image.merge('RGB', (r, g, b))
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 0.7)

    def apply_romance_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        pink = Image.new('RGB', img.size, (255, 220, 230))
        img = Image.blend(img, pink, intensity * 0.4)
        blur_radius = int(10 * intensity)
        blurred = img.filter(ImageFilter.GaussianBlur(blur_radius))
        return Image.blend(img, blurred, intensity * 0.3)

    def apply_fantasy_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 2.0)
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        return Image.merge('RGB', (r, g, b))

    def apply_landscape_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        img = Image.merge('RGB', (r, g, b))
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 0.6)

    def apply_cityscape_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        cool = Image.new('RGB', img.size, (200, 220, 240))
        img = Image.blend(img, cool, intensity * 0.3)
        enhancer = ImageEnhance.Sharpness(img)
        return enhancer.enhance(1 + intensity * 1.5)

    def apply_seascape_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.7)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        return Image.merge('RGB', (r, g, b))

    def apply_mountains_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Contrast(img)
        img = enhancer.enhance(1 + intensity * 1.2)
        cool = Image.new('RGB', img.size, (180, 220, 240))
        return Image.blend(img, cool, intensity * 0.2)

    def apply_beach_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.5)))
        return Image.merge('RGB', (r, g, b))

    def apply_urban_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 - intensity * 0.6)
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 0.9)

    def apply_moonlight_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        blue = Image.new('RGB', img.size, (150, 180, 220))
        img = Image.blend(img, blue, intensity * 0.7)
        enhancer = ImageEnhance.Brightness(img)
        return enhancer.enhance(1 - intensity * 0.3)

    def apply_city_lights_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Contrast(img)
        img = enhancer.enhance(1 + intensity * 1.5)
        enhancer = ImageEnhance.Brightness(img)
        return enhancer.enhance(1 + intensity * 0.2)

    def apply_stars_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Brightness(img)
        img = enhancer.enhance(1 - intensity * 0.5)
        stars = Image.effect_noise(img.size, intensity * 50).convert('L')
        stars = stars.point(lambda i: 255 if i > 240 else 0)
        bright = Image.new('RGB', img.size, (255, 255, 220))
        return Image.composite(bright, img, stars)

    def apply_neon_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 2.5)
        blur_radius = int(5 * intensity)
        blurred = img.filter(ImageFilter.GaussianBlur(blur_radius))
        return Image.blend(img, blurred, intensity * 0.4)

    def apply_fireworks_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Brightness(img)
        img = enhancer.enhance(1 - intensity * 0.6)
        noise = Image.effect_noise(img.size, 100).convert('RGB')
        return Image.blend(img, noise, intensity * 0.5)

    def apply_warm_glow_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        warm = Image.new('RGB', img.size, (255, 230, 180))
        img = Image.blend(img, warm, intensity * 0.5)
        blur_radius = int(10 * intensity)
        blurred = img.filter(ImageFilter.GaussianBlur(blur_radius))
        return Image.blend(img, blurred, intensity * 0.3)

    def apply_golden_hour_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.7)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        b = b.point(lambda i: i * (1 - intensity * 0.5))
        return Image.merge('RGB', (r, g, b))

    def apply_sunset_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.8)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        g = g.point(lambda i: i * (1 - intensity * 0.3))
        return Image.merge('RGB', (r, g, b))

    def apply_candlelight_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        warm = Image.new('RGB', img.size, (255, 180, 100))
        img = Image.blend(img, warm, intensity * 0.6)
        enhancer = ImageEnhance.Brightness(img)
        img = enhancer.enhance(1 - intensity * 0.4)
        vignette = Image.new('L', img.size, 255)
        draw = ImageDraw.Draw(vignette)
        width, height = img.size
        draw.ellipse((0, 0, width, height), fill=0)
        vignette = vignette.filter(ImageFilter.GaussianBlur(width/5))
        vignette = ImageEnhance.Brightness(vignette).enhance(1 - intensity * 0.7)
        return Image.composite(img, Image.new('RGB', img.size, (0, 0, 0)), vignette)

    def apply_high_contrast_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        img = img.convert('L')
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 + intensity * 2.0)

    def apply_low_contrast_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        img = img.convert('L')
        enhancer = ImageEnhance.Contrast(img)
        return enhancer.enhance(1 - intensity * 0.7)

    def apply_grainy_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        grain = Image.effect_noise(img.size, intensity * 80)
        return Image.blend(img, grain, intensity * 0.2)

    def apply_smooth_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        blur_radius = int(5 * intensity)
        return img.filter(ImageFilter.GaussianBlur(blur_radius))

    def apply_vintage_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        sepia = Image.new('RGB', img.size, (112, 66, 20))
        img = Image.blend(img, sepia, intensity * 0.7)
        fade = Image.new('RGB', img.size, (240, 240, 240))
        return Image.blend(img, fade, intensity * 0.3)

    def apply_spring_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.6)))
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.3)))
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        return Image.merge('RGB', (r, g, b))

    def apply_summer_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        enhancer = ImageEnhance.Color(img)
        img = enhancer.enhance(1 + intensity * 1.2)
        warm = Image.new('RGB', img.size, (255, 220, 180))
        return Image.blend(img, warm, intensity * 0.3)

    def apply_autumn_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        r = r.point(lambda i: min(255, i * (1 + intensity * 0.8)))
        g = g.point(lambda i: min(255, i * (1 + intensity * 0.4)))
        b = b.point(lambda i: i * (1 - intensity * 0.5))
        return Image.merge('RGB', (r, g, b))

    def apply_winter_effect(self, img, intensity):

        if img.mode != 'RGB':
            img = img.convert('RGB')
        r, g, b = img.split()
        b = b.point(lambda i: min(255, i * (1 + intensity * 0.7)))
        r = r.point(lambda i: i * (1 - intensity * 0.3))
        enhancer = ImageEnhance.Brightness(Image.merge('RGB', (r, g, b)))
        return enhancer.enhance(1 + intensity * 0.4)

    def set_exposure_slider_visibility(self, visible):

        if visible:

            if not self.expause_container.winfo_ismapped():
                self.expause_container.pack(fill='both', expand=True)
        else:

            if self.expause_container.winfo_ismapped():
                self.expause_container.pack_forget()

    def setup_expause_frame(self, parent_frame):
        self.expause_container = tk.Frame(parent_frame,bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.expause_container)
        self.expause_intensity = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.expause_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            variable=self.expause_intensity,
            length=300,
            sliderrelief='flat',
            font=('arial',15,'bold'),
            command=self.on_expause_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0,5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_expause_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_expause_slider_release)

    def on_expause_slider_press(self, event):

        if not self.current_image:
            return
        self.exposure_session_active = True
        self.exposure_effect_base = self.current_image.copy()
        self.expause_intensity.set(0)

    def on_expause_slider_drag(self, value):

        if not self.exposure_session_active or not self.exposure_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.exposure_intensity = float(value)
            exposed = self.apply_exposure_effect(self.exposure_effect_base.copy(), normalized)
            self.current_image = exposed
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Exposure error: {str(e)}")

    def on_expause_slider_release(self, event):

        if not self.current_image:
            return

        if self.exposure_session_active:
            self.exposure_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.exposure_effect_base = None

    def apply_exposure_effect(self, img, normalized_intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_np = numpy.array(img).astype(numpy.float32)
        brightness_boost = normalized_intensity * 255
        mask = img_np > 180
        img_np[mask] += brightness_boost
        img_np = numpy.clip(img_np, 0, 255)
        result = Image.fromarray(img_np.astype(numpy.uint8))

        if has_alpha:
            result = result.convert('RGBA')
            result.putalpha(alpha)
        return result

    def set_brightness_slider_visibility(self, visible):

        if visible:

            if not self.brightness_container.winfo_ismapped():
                self.brightness_container.pack(fill='both', expand=True)
        else:

            if self.brightness_container.winfo_ismapped():
                self.brightness_container.pack_forget()

    def setup_brightness_frame(self, parent_frame):
        self.brightness_container = tk.Frame(parent_frame,bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.brightness_container)
        self.brightness_intensity_var  = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.brightness_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial',15,'bold'),
            variable=self.brightness_intensity_var ,
            command=self.on_brightness_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0,5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_brightness_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_brightness_slider_release)

    def on_brightness_slider_press(self, event):

        if not self.current_image:
            return
        self.brightness_session_active = True
        self.brightness_effect_base = self.current_image.copy()
        self.brightness_intensity_var.set(0)

    def on_brightness_slider_drag(self, value):

        if self.skip_brightness_slider_events:
            return

        if not self.brightness_session_active or not self.brightness_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            brightened = self.apply_brightness_effect(self.brightness_effect_base.copy(), normalized)
            self.current_image = brightened
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Brightness error: {str(e)}")
        self.brightness_intensity = float(value)

    def on_brightness_slider_release(self, event):

        if not self.current_image:
            return

        if self.brightness_session_active:
            self.brightness_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.brightness_effect_base = None

    def apply_brightness_effect(self, img, normalized_intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        factor = 1.0 + normalized_intensity
        enhancer = ImageEnhance.Brightness(img)
        result = enhancer.enhance(factor)

        if has_alpha:
            result = result.convert('RGBA')
            result.putalpha(alpha)
        return result

    def set_contrast_slider_visibility(self, visible):

        if visible:

            if not self.contrast_container.winfo_ismapped():
                self.contrast_container.pack(fill='both', expand=True)
        else:

            if self.contrast_container.winfo_ismapped():
                self.contrast_container.pack_forget()

    def setup_contrast_frame(self, parent_frame):
        self.contrast_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.contrast_container)
        self.contrast_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.contrast_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.contrast_intensity_var,
            command=self.on_contrast_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_contrast_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_contrast_slider_release)

    def on_contrast_slider_press(self, event):

        if not self.current_image:
            return
        self.contrast_session_active = True
        self.contrast_effect_base = self.current_image.copy()
        self.contrast_intensity_var.set(0)

    def on_contrast_slider_drag(self, value):

        if not self.contrast_session_active or not self.contrast_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.contrast_intensity = float(value)
            contrasted = self.apply_contrast_effect(self.contrast_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_contrast_slider_release(self, event):

        if not self.current_image:
            return

        if self.contrast_session_active:
            self.contrast_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.contrast_effect_base = None

    def apply_contrast_effect(self, img, normalized_intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        factor = 1.0 + normalized_intensity
        enhancer = ImageEnhance.Contrast(img)
        result = enhancer.enhance(factor)

        if has_alpha:
            result = result.convert('RGBA')
            result.putalpha(alpha)
        return result

    def set_saturation_slider_visibility(self, visible):

        if visible:

            if not self.saturation_container.winfo_ismapped():
                self.saturation_container.pack(fill='both', expand=True)
        else:

            if self.saturation_container.winfo_ismapped():
                self.saturation_container.pack_forget()

    def setup_saturation_frame(self, parent_frame):
        self.saturation_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.saturation_container)
        self.saturation_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.saturation_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.saturation_intensity_var,
            command=self.on_saturation_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_saturation_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_saturation_slider_release)

    def on_saturation_slider_press(self, event):

        if not self.current_image:
            return
        self.saturation_session_active = True
        self.saturation_effect_base = self.current_image.copy()
        self.saturation_intensity_var.set(0)

    def on_saturation_slider_drag(self, value):

        if not self.saturation_session_active or not self.saturation_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.saturation_intensity = float(value)
            contrasted = self.apply_saturation_effect(self.saturation_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_saturation_slider_release(self, event):

        if not self.current_image:
            return

        if self.saturation_session_active:
            self.saturation_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.saturation_effect_base = None

    def apply_saturation_effect(self, img, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        gray_img = img.convert('L')

        if intensity >= 0:
            factor = 1.0 + 2.0 * intensity
        else:
            factor = 1.0 + 0.5 * intensity
        enhancer = ImageEnhance.Contrast(gray_img)
        contrasted = enhancer.enhance(factor)
        result = contrasted.convert('RGB')

        if has_alpha:
            result = result.convert('RGBA')
            result.putalpha(alpha)
        return result

    def set_vibrance_slider_visibility(self, visible):

        if visible:

            if not self.vibrance_container.winfo_ismapped():
                self.vibrance_container.pack(fill='both', expand=True)
        else:

            if self.vibrance_container.winfo_ismapped():
                self.vibrance_container.pack_forget()

    def setup_vibrance_frame(self, parent_frame):
        self.vibrance_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.vibrance_container)
        self.vibrance_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.vibrance_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.vibrance_intensity_var,
            command=self.on_vibrance_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_vibrance_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_vibrance_slider_release)

    def on_vibrance_slider_press(self, event):

        if not self.current_image:
            return
        self.vibrance_session_active = True
        self.vibrance_effect_base = self.current_image.copy()
        self.vibrance_intensity_var.set(0)

    def on_vibrance_slider_drag(self, value):

        if not self.vibrance_session_active or not self.vibrance_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.vibrance_intensity = float(value)
            contrasted = self.apply_vibrance_effect(self.vibrance_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_vibrance_slider_release(self, event):

        if not self.current_image:
            return

        if self.vibrance_session_active:
            self.vibrance_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.vibrance_effect_base = None

    def apply_vibrance_effect(self, img, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.asarray(img).astype(numpy.float32)
        r, g, b = img_array[..., 0], img_array[..., 1], img_array[..., 2]
        avg = (r + g + b) / 3.0
        saturation = numpy.sqrt((r - avg)**2 + (g - avg)**2 + (b - avg)**2)
        vibrance_mask = 1.0 - (saturation / 128.0)
        vibrance_mask = numpy.clip(vibrance_mask, 0.0, 1.0)
        r += (r - avg) * vibrance_mask * intensity * 2.0
        g += (g - avg) * vibrance_mask * intensity * 2.0
        b += (b - avg) * vibrance_mask * intensity * 2.0
        result_array = numpy.stack([
            numpy.clip(r, 0, 255),
            numpy.clip(g, 0, 255),
            numpy.clip(b, 0, 255)
        ], axis=-1).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert("RGBA")
            result.putalpha(alpha)
        return result

    def set_wormth_slider_visibility(self, visible):

        if visible:

            if not self.wormth_container.winfo_ismapped():
                self.wormth_container.pack(fill='both', expand=True)
        else:

            if self.wormth_container.winfo_ismapped():
                self.wormth_container.pack_forget()

    def setup_wormth_frame(self, parent_frame):
        self.wormth_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.wormth_container)
        self.wormth_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.wormth_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.wormth_intensity_var,
            command=self.on_wormth_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_wormth_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_wormth_slider_release)

    def on_wormth_slider_press(self, event):

        if not self.current_image:
            return
        self.wormth_session_active = True
        self.wormth_effect_base = self.current_image.copy()
        self.wormth_intensity_var.set(0)

    def on_wormth_slider_drag(self, value):

        if not self.wormth_session_active or not self.wormth_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.wormth_intensity = float(value)
            contrasted = self.apply_wormth_effect(self.wormth_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_wormth_slider_release(self, event):

        if not self.current_image:
            return

        if self.wormth_session_active:
            self.wormth_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.wormth_effect_base = None

    def apply_wormth_effect(self, img, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.asarray(img).astype(numpy.float32)
        r, g, b = img_array[..., 0], img_array[..., 1], img_array[..., 2]
        r += intensity * 30
        g += intensity * 10
        b -= intensity * 20
        result_array = numpy.stack([
            numpy.clip(r, 0, 255),
            numpy.clip(g, 0, 255),
            numpy.clip(b, 0, 255)
        ], axis=-1).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert("RGBA")
            result.putalpha(alpha)
        return result

    def set_tint_slider_visibility(self, visible):

        if visible:

            if not self.tint_container.winfo_ismapped():
                self.tint_container.pack(fill='both', expand=True)
        else:

            if self.tint_container.winfo_ismapped():
                self.tint_container.pack_forget()

    def setup_tint_frame(self, parent_frame):
        self.tint_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.tint_container)
        self.tint_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.tint_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.tint_intensity_var,
            command=self.on_tint_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_tint_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_tint_slider_release)

    def on_tint_slider_press(self, event):

        if not self.current_image:
            return
        self.tint_session_active = True
        self.tint_effect_base = self.current_image.copy()
        self.tint_intensity_var.set(0)

    def on_tint_slider_drag(self, value):

        if not self.tint_session_active or not self.tint_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.tint_intensity = float(value)
            contrasted = self.apply_tint_effect(self.tint_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_tint_slider_release(self, event):

        if not self.current_image:
            return

        if self.tint_session_active:
            self.tint_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.tint_effect_base = None

    def apply_tint_effect(self, img, intensity, tint_color=(0, 128, 255)):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.asarray(img).astype(numpy.float32)
        tint_array = numpy.array(tint_color, dtype=numpy.float32)
        result_array = img_array * (1 - intensity) + tint_array * intensity
        result_array = numpy.clip(result_array, 0, 255).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert('RGBA')
            result.putalpha(alpha)
        return result

    def set_highlight_slider_visibility(self, visible):

        if visible:

            if not self.highlight_container.winfo_ismapped():
                self.highlight_container.pack(fill='both', expand=True)
        else:

            if self.highlight_container.winfo_ismapped():
                self.highlight_container.pack_forget()

    def setup_highlight_frame(self, parent_frame):
        self.highlight_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.highlight_container)
        self.highlight_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.highlight_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.highlight_intensity_var,
            command=self.on_highlight_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_highlight_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_highlight_slider_release)

    def on_highlight_slider_press(self, event):

        if not self.current_image:
            return
        self.highlight_session_active = True
        self.highlight_effect_base = self.current_image.copy()
        self.highlight_intensity_var.set(0)

    def on_highlight_slider_drag(self, value):

        if not self.highlight_session_active or not self.highlight_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.highlight_intensity = float(value)
            contrasted = self.apply_highlight_effect(self.highlight_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_highlight_slider_release(self, event):

        if not self.current_image:
            return

        if self.highlight_session_active:
            self.highlight_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.highlight_effect_base = None

    def apply_highlight_effect(self, img,intensity, highlight_color=(255, 255, 224)):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.asarray(img).astype(numpy.float32)
        r, g, b = img_array[..., 0], img_array[..., 1], img_array[..., 2]
        r += intensity * 30
        g += intensity * 10
        b -= intensity * 20
        brightness = 0.299 * r + 0.587 * g + 0.114 * b
        highlight_mask = numpy.zeros_like(brightness)

        if intensity > 0:
            highlight_mask = (brightness / 255.0) * intensity * 50
        elif intensity < 0:
            highlight_mask = ((1.0 - brightness / 255.0) * abs(intensity)) * -50
        r = numpy.clip(r + highlight_mask, 0, 255)
        g = numpy.clip(g + highlight_mask, 0, 255)
        b = numpy.clip(b + highlight_mask, 0, 255)
        result_array = numpy.stack([r, g, b], axis=-1).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert("RGBA")
            result.putalpha(alpha)
        return result

    def set_shadows_slider_visibility(self, visible):

        if visible:

            if not self.shadows_container.winfo_ismapped():
                self.shadows_container.pack(fill='both', expand=True)
        else:

            if self.shadows_container.winfo_ismapped():
                self.shadows_container.pack_forget()

    def setup_shadows_frame(self, parent_frame):
        self.shadows_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.shadows_container)
        self.shadows_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.shadows_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.shadows_intensity_var,
            command=self.on_shadows_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_shadows_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_shadows_slider_release)

    def on_shadows_slider_press(self, event):

        if not self.current_image:
            return
        self.shadows_session_active = True
        self.shadows_effect_base = self.current_image.copy()
        self.shadows_intensity_var.set(0)

    def on_shadows_slider_drag(self, value):

        if not self.shadows_session_active or not self.shadows_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.shadows_intensity = float(value)
            contrasted = self.apply_shadows_effect(self.shadows_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_shadows_slider_release(self, event):

        if not self.current_image:
            return

        if self.shadows_session_active:
            self.shadows_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.shadows_effect_base = None

    def apply_shadows_effect(self, img, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.asarray(img).astype(numpy.float32)
        r, g, b = img_array[..., 0], img_array[..., 1], img_array[..., 2]
        brightness = (0.299 * r + 0.587 * g + 0.114 * b) / 255.0
        shadow_mask = (1.0 - brightness)
        adjustment = shadow_mask * intensity * 60
        r = numpy.clip(r - adjustment, 0, 255)
        g = numpy.clip(g - adjustment, 0, 255)
        b = numpy.clip(b - adjustment, 0, 255)
        result_array = numpy.stack([r, g, b], axis=-1).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert("RGBA")
            result.putalpha(alpha)
        return result

    def set_fade_slider_visibility(self, visible):

        if visible:

            if not self.fade_container.winfo_ismapped():
                self.fade_container.pack(fill='both', expand=True)
        else:

            if self.fade_container.winfo_ismapped():
                self.fade_container.pack_forget()

    def setup_fade_frame(self, parent_frame):
        self.fade_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.fade_container)
        self.fade_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.fade_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.fade_intensity_var,
            command=self.on_fade_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_fade_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_fade_slider_release)

    def on_fade_slider_press(self, event):

        if not self.current_image:
            return
        self.fade_session_active = True
        self.fade_effect_base = self.current_image.copy()
        self.fade_intensity_var.set(0)

    def on_fade_slider_drag(self, value):

        if not self.fade_session_active or not self.fade_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.fade_intensity = float(value)
            contrasted = self.apply_fade_effect(self.fade_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_fade_slider_release(self, event):

        if not self.current_image:
            return

        if self.fade_session_active:
            self.fade_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.fade_effect_base = None

    def apply_fade_effect(self, img, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.asarray(img).astype(numpy.float32)
        r, g, b = img_array[..., 0], img_array[..., 1], img_array[..., 2]
        fade_color = 220
        r = r + (fade_color - r) * intensity
        g = g + (fade_color - g) * intensity
        b = b + (fade_color - b) * intensity
        r = numpy.clip(r, 0, 255)
        g = numpy.clip(g, 0, 255)
        b = numpy.clip(b, 0, 255)
        result_array = numpy.stack([r, g, b], axis=-1).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert("RGBA")
            result.putalpha(alpha)
        return result

    def set_gain_slider_visibility(self, visible):

        if visible:

            if not self.gain_container.winfo_ismapped():
                self.gain_container.pack(fill='both', expand=True)
        else:

            if self.gain_container.winfo_ismapped():
                self.gain_container.pack_forget()

    def setup_gain_frame(self, parent_frame):
        self.gain_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.gain_container)
        self.gain_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.gain_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.gain_intensity_var,
            command=self.on_gain_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_gain_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_gain_slider_release)

    def on_gain_slider_press(self, event):

        if not self.current_image:
            return
        self.gain_session_active = True
        self.gain_effect_base = self.current_image.copy()
        self.gain_intensity_var.set(0)

    def on_gain_slider_drag(self, value):

        if not self.gain_session_active or not self.gain_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.gain_intensity = float(value)
            contrasted = self.apply_gain_effect(self.gain_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_gain_slider_release(self, event):

        if not self.current_image:
            return

        if self.gain_session_active:
            self.gain_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.gain_effect_base = None

    def apply_gain_effect(self, img, gain):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.asarray(img).astype(numpy.float32) / 255.0
        r, g, b = img_array[..., 0], img_array[..., 1], img_array[..., 2]
        r = numpy.power(r, 1.0 / max(gain, 0.01))
        g = numpy.power(g, 1.0 / max(gain, 0.01))
        b = numpy.power(b, 1.0 / max(gain, 0.01))
        r = numpy.clip(r * 255.0, 0, 255)
        g = numpy.clip(g * 255.0, 0, 255)
        b = numpy.clip(b * 255.0, 0, 255)
        result_array = numpy.stack([r, g, b], axis=-1).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert("RGBA")
            result.putalpha(alpha)
        return result

    def set_sharpness_slider_visibility(self, visible):

        if visible:

            if not self.sharpness_container.winfo_ismapped():
                self.sharpness_container.pack(fill='both', expand=True)
        else:

            if self.sharpness_container.winfo_ismapped():
                self.sharpness_container.pack_forget()

    def setup_sharpness_frame(self, parent_frame):
        self.sharpness_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.sharpness_container)
        self.sharpness_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.sharpness_container,
            from_=0,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.sharpness_intensity_var,
            command=self.on_sharpness_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_sharpness_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_sharpness_slider_release)

    def on_sharpness_slider_press(self, event):

        if not self.current_image:
            return
        self.sharpness_session_active = True
        self.sharpness_effect_base = self.current_image.copy()
        self.sharpness_intensity_var.set(0)

    def on_sharpness_slider_drag(self, value):

        if not self.sharpness_session_active or not self.sharpness_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.sharpness_intensity = float(value)
            contrasted = self.apply_sharpness_effect(self.sharpness_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_sharpness_slider_release(self, event):

        if not self.current_image:
            return

        if self.sharpness_session_active:
            self.sharpness_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.sharpness_effect_base = None

    def apply_sharpness_effect(self, img, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        img_array = numpy.array(img).astype(numpy.float32)
        blurred = img.filter(ImageFilter.GaussianBlur(radius=1))
        blurred_array = numpy.array(blurred).astype(numpy.float32)
        amount = intensity * 20.0
        sharpened_array = img_array + amount * (img_array - blurred_array)
        sharpened_array = numpy.clip(sharpened_array, 0, 255).astype(numpy.uint8)
        result = Image.fromarray(sharpened_array)

        if has_alpha:
            result = result.convert('RGBA')
            result.putalpha(alpha)
        return result

    def set_vignette_slider_visibility(self, visible):

        if visible:

            if not self.vignette_container.winfo_ismapped():
                self.vignette_container.pack(fill='both', expand=True)
        else:

            if self.vignette_container.winfo_ismapped():
                self.vignette_container.pack_forget()

    def setup_vignette_frame(self, parent_frame):
        self.vignette_container = tk.Frame(parent_frame, bg='#1e1e2e')
        self.bind_mousewheel_to_children(self.vignette_container)
        self.vignette_intensity_var = tk.DoubleVar(value=0)
        slider = tk.Scale(
            self.vignette_container,
            from_=-100,
            to=100,
            sliderlength=20,
            width=8,
            length=300,
            orient='horizontal',
            troughcolor="#444",
            bg="#1e1e2e",
            fg='white',
            activebackground="#00c8ff",
            bd=1,
            highlightthickness=0,
            sliderrelief='flat',
            font=('arial', 15, 'bold'),
            variable=self.vignette_intensity_var,
            command=self.on_vignette_slider_drag
        )
        slider.pack(side=tk.LEFT, padx=5, pady=(0, 5), expand=True)
        self.bind_mousewheel_to_children(slider)
        slider.bind("<ButtonPress-1>", self.on_vignette_slider_press)
        slider.bind("<ButtonRelease-1>", self.on_vignette_slider_release)

    def on_vignette_slider_press(self, event):

        if not self.current_image:
            return
        self.vignette_session_active = True
        self.vignette_effect_base = self.current_image.copy()
        self.vignette_intensity_var.set(0)

    def on_vignette_slider_drag(self, value):

        if not self.vignette_session_active or not self.vignette_effect_base:
            return

        try:
            normalized = float(value) / 100.0
            self.vignette_intensity = float(value)
            contrasted = self.apply_vignette_effect(self.vignette_effect_base.copy(), normalized)
            self.current_image = contrasted
            self.display_image_on_canvas()

        except Exception as e:
            print(f"Contrast error: {str(e)}")

    def on_vignette_slider_release(self, event):

        if not self.current_image:
            return

        if self.vignette_session_active:
            self.vignette_session_active = False
            self.add_to_history()
            self.saved_after_last_change = False
            self.vignette_effect_base = None

    def apply_vignette_effect(self, img, intensity):
        has_alpha = img.mode == 'RGBA'

        if has_alpha:
            alpha = img.split()[3]
            img = img.convert('RGB')
        width, height = img.size
        img_array = numpy.array(img).astype(numpy.float32)
        y, x = numpy.ogrid[0:height, 0:width]
        center_x, center_y = width / 2, height / 2
        distance = numpy.sqrt((x - center_x) ** 2 + (y - center_y) ** 2)
        max_distance = numpy.sqrt(center_x**2 + center_y**2)
        distance = distance / max_distance
        distance = numpy.clip(distance, 0.0001, 1.0)
        vignette_mask = 1 - distance
        power = 2 + intensity * 8
        vignette_mask = vignette_mask ** power
        vignette_mask = vignette_mask[..., numpy.newaxis]
        vignette_mask = numpy.repeat(vignette_mask, 3, axis=2)
        result_array = img_array * vignette_mask
        result_array = numpy.clip(result_array, 0, 255).astype(numpy.uint8)
        result = Image.fromarray(result_array)

        if has_alpha:
            result = result.convert('RGBA')
            result.putalpha(alpha)
        return result

    def set_doodle_slider_visibility(self, visible):

        if visible:

            if not self.doodle_container.winfo_ismapped():
                self.doodle_container.pack(fill='both', expand=True)
        else:

            if self.doodle_container.winfo_ismapped():
                self.doodle_container.pack_forget()

    def setup_doodle_frame(self, parent_frame):
        self.doodle_container = tk.Frame(parent_frame, bg="#1e1e2e")
        self.bind_mousewheel_to_children(self.doodle_container)
        brush_frame = tk.Frame(self.doodle_container, bg='#1e1e2e')
        brush_frame.pack(fill='x', pady=5)
        self.bind_mousewheel_to_children(brush_frame)
        brush_label = tk.Label(brush_frame, text="Brush Size:", font=('Arial', 12), bg='#1e1e2e', fg='white')
        brush_label.pack(side='left', padx=(0, 10))
        self.bind_mousewheel_to_children(brush_label)
        self.doodle_brush_size = tk.IntVar(value=10)
        brush_slider = tk.Scale(
            brush_frame, from_=1, to=100, orient='horizontal',
            variable=self.doodle_brush_size, length=200,
            bg='#1e1e2e', fg='white', troughcolor='#3a3a5a',
            font=('arial',10),
            highlightthickness=0,
            width=10, sliderlength=20,
            sliderrelief='flat',
        )
        brush_slider.pack(side='left', fill='x', padx=5, expand=True)
        self.bind_mousewheel_to_children(brush_slider)
        color_frame = tk.Frame(self.doodle_container, bg='#1e1e2e')
        color_frame.pack(fill='x', pady=5)
        self.bind_mousewheel_to_children(color_frame)
        self.doodle_color = (255, 0, 0)
        self.color_btn = tk.Button(
            color_frame,
            text="Choose Color >>",
            command=self.choose_doodle_color,
            bg="#2d3869",
            fg='white',
            font=('arial',12),
            activebackground='#2d3869',
            border=0,
            borderwidth=0,
            activeforeground= 'white',
        )
        self.color_btn.pack(side='left', padx=(10, 10))
        self.bind_mousewheel_to_children(self.color_btn)
        self.display_color_btn = tk.Button(
            color_frame, text="   ", width=20, command=self.choose_doodle_color,
            bg="#f50101", fg='white', activebackground='#f50101', border=0,
        )
        self.display_color_btn.pack(side='left', padx=(0, 10), expand=True)
        self.bind_mousewheel_to_children(self.display_color_btn)
        shape_frame = tk.Frame(self.doodle_container, bg='#1e1e2e')
        shape_frame.pack(fill='x', pady=5)
        self.bind_mousewheel_to_children(shape_frame)
        square_img = Image.open(resource_path(r"icons\square.png")).resize((27, 27))
        self.square_icon = ImageTk.PhotoImage(square_img)
        circle_img = Image.open(resource_path(r"icons\circle.png")).resize((30, 30))
        self.circle_icon = ImageTk.PhotoImage(circle_img)
        curve_img = Image.open(resource_path(r"icons\curve.png")).resize((40, 40))
        self.free_hand_icon = ImageTk.PhotoImage(curve_img)
        line_img = Image.open(resource_path(r"icons\line.png")).resize((50, 50))
        self.line_icon = ImageTk.PhotoImage(line_img)
        arrow_img = Image.open(resource_path(r"icons\arrow.png")).resize((70, 70))
        self.arrow_icon = ImageTk.PhotoImage(arrow_img)
        mosaic_img = Image.open(resource_path(r"icons\mosaic.png")).resize((30, 30))
        self.mosaic_icon = ImageTk.PhotoImage(mosaic_img)
        self.doodle_shape = tk.StringVar(value="freehand")
        shapes = [ (self.free_hand_icon, "freehand"), (self.square_icon, "square"), (self.circle_icon, "circle"), (self.line_icon, "line"),(self.arrow_icon, "arrow"),(self.mosaic_icon, "mosaic")]
        for img, mode in shapes:
            b = tk.Radiobutton(
                shape_frame, image= img, variable=self.doodle_shape, value=mode,
                bg='#1e1e2e', fg='yellow', selectcolor="#050F7E" , activebackground='#2a2a3a',
                indicatoron=False,
                width=10,
                border=0,
                height=40
            )
            b.pack(side='left', fill='x', expand=True, padx=5)
            self.bind_mousewheel_to_children(b)
        btn_frame = tk.Frame(self.doodle_container, bg='#1e1e2e')
        btn_frame.pack(fill='x', pady=10)
        self.bind_mousewheel_to_children(btn_frame)
        self.start_doodling = tk.Button(
            btn_frame,
            text="Start Doodling",
            bg='#4a4a7a',
            font=('arial',12,'bold'),
            border=0,
            activebackground="#5b5bc3",
            activeforeground='white',
            fg='white',
            command=self.enter_doodle_mode,
        )
        self.start_doodling.pack(side='left', fill='x', expand=True, padx=5)
        self.bind_mousewheel_to_children(self.start_doodling)
        self.apply_btn = tk.Button(
            btn_frame,
            text="Apply",
            bg="#0a722b",
            font=('arial',12, 'bold'),
            border=0,
            activebackground="#2af80f",
            activeforeground='black',
            fg='white',
            command=self.apply_doodle
        )
        self.bind_mousewheel_to_children(self.apply_btn )
        self.cancel_btn = tk.Button(
            btn_frame,
            text="Cancel",
            bg="#b50d1e",
            font=('arial',12, 'bold'),
            border=0,
            activebackground="#ff0000",
            activeforeground='white',
            fg='white',
            command=self.cancel_doodle
        )
        self.bind_mousewheel_to_children(self.cancel_btn)

    def choose_doodle_color(self):
        color = colorchooser.askcolor(title="Choose Drawing Color", initialcolor=(255, 0, 0))

        if color[0]:
            self.doodle_color = tuple(map(int, color[0]))
            self.hex_color = f"#{self.doodle_color[0]:02x}{self.doodle_color[1]:02x}{self.doodle_color[2]:02x}"
            self.display_color_btn.config(bg=self.hex_color, activebackground=self.hex_color)

    def enter_doodle_mode(self):

        if not self.current_image:
            return
        self.start_doodling.pack_forget()
        self.apply_btn .pack(side='left', fill='x', expand=True, padx=5)
        self.cancel_btn.pack(side='left', fill='x', expand=True, padx=5)
        self.doodle_backup = self.current_image.copy()
        self.doodle_temp_image = self.doodle_backup.copy()
        self.doodle_drawing = False
        self.doodle_start = None
        self.doodle_current_shape = None
        self.doodle_preview_layer = Image.new("RGBA", self.current_image.size, (0, 0, 0, 0))
        self.original_bindings = {
            "<Button-1>": self.canvas.bind("<Button-1>"),
            "<B1-Motion>": self.canvas.bind("<B1-Motion>"),
            "<ButtonRelease-1>": self.canvas.bind("<ButtonRelease-1>")
        }
        self.canvas.bind("<Button-1>", self.on_doodle_press)
        self.canvas.bind("<B1-Motion>", self.on_doodle_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_doodle_release)
        self.doodle_mode = True
        self.doodle_initial_state = self.current_image.copy()
        self.add_to_history()

    def on_doodle_press(self, event):

        if not self.doodle_mode:
            return
        self.doodle_drawing = True
        self.doodle_start = (event.x, event.y)
        self.doodle_last_pos = None
        self.doodle_preview_layer = Image.new("RGBA", self.current_image.size, (0, 0, 0, 0))

    def on_doodle_drag(self, event):

        if not self.doodle_drawing or not self.doodle_start:
            return
        img_x = int((event.x - self.canvas_image_x) / self.zoom_level)
        img_y = int((event.y - self.canvas_image_y) / self.zoom_level)
        start_img_x = int((self.doodle_start[0] - self.canvas_image_x) / self.zoom_level)
        start_img_y = int((self.doodle_start[1] - self.canvas_image_y) / self.zoom_level)
        brush_size = max(1, int(self.doodle_brush_size.get() / self.zoom_level))
        shape = self.doodle_shape.get()

        if shape == "freehand":
            draw = ImageDraw.Draw(self.doodle_temp_image)
            current_pos = (img_x, img_y)

            if self.doodle_last_pos:
                x0, y0 = self.doodle_last_pos
                x1, y1 = current_pos
                distance = max(abs(x1 - x0), abs(y1 - y0))
                steps = max(1, int(distance))
                for i in range(steps):
                    frac = i / max(1, steps - 1)
                    x = int(x0 + frac * (x1 - x0))
                    y = int(y0 + frac * (y1 - y0))
                    draw.ellipse(
                        [x - brush_size//2, y - brush_size//2,
                        x + brush_size//2, y + brush_size//2],
                        fill=self.doodle_color
                    )
            else:
                draw.ellipse(
                    [img_x - brush_size//2, img_y - brush_size//2,
                    img_x + brush_size//2, img_y + brush_size//2],
                    fill=self.doodle_color
                )
            self.doodle_last_pos = current_pos
            self.current_image = self.doodle_temp_image
        else:
            self.doodle_preview_layer = Image.new("RGBA", self.current_image.size, (0, 0, 0, 0))
            draw = ImageDraw.Draw(self.doodle_preview_layer)

            if shape == "square":
                x0, y0 = min(start_img_x, img_x), min(start_img_y, img_y)
                x1, y1 = max(start_img_x, img_x), max(start_img_y, img_y)
                draw.rectangle(
                    [x0, y0, x1, y1],
                    outline=self.doodle_color + (255,),
                    width=brush_size
                )
            elif shape == "circle":
                x0, y0 = min(start_img_x, img_x), min(start_img_y, img_y)
                x1, y1 = max(start_img_x, img_x), max(start_img_y, img_y)
                draw.ellipse(
                    [x0, y0, x1, y1],
                    outline=self.doodle_color + (255,),
                    width=brush_size
                )
            elif shape == "arrow":
                dx = img_x - start_img_x
                dy = img_y - start_img_y
                length = math.hypot(dx, dy)

                if length < 2:
                    return
                ux, uy = dx / length, dy / length
                perp_x, perp_y = -uy, ux
                shaft_start = 2
                shaft_end = brush_size
                head_length = max(10, brush_size * 1.5)
                head_width = max(20, brush_size * 2.5)
                sx, sy = img_x - ux * head_length, img_y - uy * head_length
                p1 = (start_img_x - perp_x * shaft_start / 2, start_img_y - perp_y * shaft_start / 2)
                p2 = (start_img_x + perp_x * shaft_start / 2, start_img_y + perp_y * shaft_start / 2)
                p3 = (sx + perp_x * shaft_end / 2, sy + perp_y * shaft_end / 2)
                p4 = (sx - perp_x * shaft_end / 2, sy - perp_y * shaft_end / 2)
                left = (sx + perp_x * head_width / 2, sy + perp_y * head_width / 2)
                right = (sx - perp_x * head_width / 2, sy - perp_y * head_width / 2)
                tip = (img_x, img_y)
                draw.polygon([p1, p2, p3, left, tip, right, p4], fill=self.doodle_color + (255,))
            elif shape == "line":
                draw.line(
                    [(start_img_x, start_img_y), (img_x, img_y)],
                    fill=self.doodle_color + (255,),
                    width=brush_size
                )
            elif shape == "mosaic":
                current_pos = (img_x, img_y)
                brush_radius = brush_size // 2

                if self.doodle_last_pos:
                    dx = img_x - self.doodle_last_pos[0]
                    dy = img_y - self.doodle_last_pos[1]

                    if abs(dx) < 3 and abs(dy) < 3:
                        return
                x0 = max(0, img_x - brush_radius)
                y0 = max(0, img_y - brush_radius)
                x1 = min(self.doodle_temp_image.width, img_x + brush_radius)
                y1 = min(self.doodle_temp_image.height, img_y + brush_radius)

                if x1 > x0 and y1 > y0:
                    region = self.doodle_temp_image.crop((x0, y0, x1, y1))
                    block_size = max(1, brush_size // 4)
                    small = region.resize(
                        (max(1, region.width // block_size), max(1, region.height // block_size)),
                        resample=Image.Resampling.NEAREST
                    )
                    mosaic_region = small.resize(region.size, Image.Resampling.NEAREST)
                    patch = Image.new("RGBA", self.doodle_temp_image.size, (0, 0, 0, 0))
                    patch.paste(mosaic_region, (x0, y0))
                    mask = Image.new("L", self.doodle_temp_image.size, 0)
                    draw_mask = ImageDraw.Draw(mask)
                    draw_mask.ellipse(
                        [img_x - brush_radius, img_y - brush_radius, img_x + brush_radius, img_y + brush_radius],
                        fill=255
                    )
                    self.doodle_temp_image.paste(patch, (0, 0), mask)
                self.current_image = self.doodle_temp_image
                self.doodle_last_pos = current_pos
            combined = self.doodle_temp_image.copy()

            if combined.mode != 'RGBA':
                combined = combined.convert('RGBA')
            combined.alpha_composite(self.doodle_preview_layer)
            self.current_image = combined
        self.display_image_on_canvas()

    def on_doodle_release(self, event):

        if not self.doodle_drawing or not self.doodle_start:
            return
        shape = self.doodle_shape.get()

        if shape != "freehand":
            draw = ImageDraw.Draw(self.doodle_temp_image)
            img_x1 = int((self.doodle_start[0] - self.canvas_image_x) / self.zoom_level)
            img_y1 = int((self.doodle_start[1] - self.canvas_image_y) / self.zoom_level)
            img_x2 = int((event.x - self.canvas_image_x) / self.zoom_level)
            img_y2 = int((event.y - self.canvas_image_y) / self.zoom_level)
            brush_size = max(1, int(self.doodle_brush_size.get() / self.zoom_level))

        if shape == "square":
            x0, y0 = min(img_x1, img_x2), min(img_y1, img_y2)
            x1, y1 = max(img_x1, img_x2), max(img_y1, img_y2)
            draw.rectangle(
                [x0, y0, x1, y1],
                outline=self.doodle_color,
                width=brush_size
            )
        elif shape == "circle":
            x0, y0 = min(img_x1, img_x2), min(img_y1, img_y2)
            x1, y1 = max(img_x1, img_x2), max(img_y1, img_y2)
            draw.ellipse(
                [x0, y0, x1, y1],
                outline=self.doodle_color,
                width=brush_size
            )
            self.current_image = self.doodle_temp_image
        elif shape == "arrow":
            dx = img_x2 - img_x1
            dy = img_y2 - img_y1
            length = math.hypot(dx, dy)

            if length < 2:
                return
            ux, uy = dx / length, dy / length
            perp_x, perp_y = -uy, ux
            shaft_start = 2
            shaft_end = brush_size
            head_length = max(10, brush_size * 1.5)
            head_width = max(20, brush_size * 2.5)
            sx, sy = img_x2 - ux * head_length, img_y2 - uy * head_length
            p1 = (img_x1 - perp_x * shaft_start / 2, img_y1 - perp_y * shaft_start / 2)
            p2 = (img_x1 + perp_x * shaft_start / 2, img_y1 + perp_y * shaft_start / 2)
            p3 = (sx + perp_x * shaft_end / 2, sy + perp_y * shaft_end / 2)
            p4 = (sx - perp_x * shaft_end / 2, sy - perp_y * shaft_end / 2)
            left = (sx + perp_x * head_width / 2, sy + perp_y * head_width / 2)
            right = (sx - perp_x * head_width / 2, sy - perp_y * head_width / 2)
            tip = (img_x2, img_y2)
            draw.polygon([p1, p2, p3, left, tip, right, p4], fill=self.doodle_color)
            self.current_image = self.doodle_temp_image
        elif shape == "line":
            draw.line(
                [(img_x1, img_y1), (img_x2, img_y2)],
                fill=self.doodle_color,
                width=brush_size
            )
            self.current_image = self.doodle_temp_image
        elif shape == "mosaic":
            self.current_image = self.doodle_temp_image
        self.doodle_preview_layer = Image.new("RGBA", self.current_image.size, (0, 0, 0, 0))
        self.display_image_on_canvas()
        self.add_to_history()
        self.doodle_drawing = False
        self.doodle_start = None
        self.doodle_last_pos = None

    def apply_doodle(self):
            self.add_to_history()
            self.saved_after_last_change = False
            self.exit_doodle_mode()
            self.apply_btn.pack_forget()
            self.cancel_btn.pack_forget()
            self.start_doodling.pack(side='left', fill='x', expand=True, padx=5)

    def cancel_doodle(self):

        if self.doodle_mode:
            self.current_image = self.doodle_backup
            self.add_to_history()
            self.display_image_on_canvas()
            self.exit_doodle_mode()
            self.apply_btn.pack_forget()
            self.cancel_btn.pack_forget()
            self.start_doodling.pack(side='left', fill='x', expand=True, padx=5)

    def exit_doodle_mode(self):

        if not self.doodle_mode:
            return
        for event, handler in self.original_bindings.items():

            if handler:
                self.canvas.bind(event, handler)
            else:
                self.canvas.unbind(event)
        self.doodle_mode = False
        self.doodle_backup = None
        self.doodle_temp_image = None
        self.doodle_preview_layer = None
        self.doodle_drawing = False
        self.doodle_start = None
        self.doodle_current_shape = None

if __name__ == "__main__":

    if sys.platform == "win32":
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("com.example.ImageEditor")

    if DND_FILES is not None:
        root = TkinterDnD.Tk()
    else:
        root = tk.Tk()
    app = PremiumImageEditor(root)
    app.run()
