import tkinter as tk
from tkinter import ttk, colorchooser, filedialog, simpledialog, messagebox
from PIL import Image, ImageTk, ImageOps
import math, random, json, time, io, re, sys

# ---- Вспомогательные векторы ----
def v_add(a, b):
    return {'x': a['x'] + b['x'], 'z': a['z'] + b['z']}

def v_sub(a, b):
    return {'x': a['x'] - b['x'], 'z': a['z'] - b['z']}

def v_scale(a, s):
    return {'x': a['x'] * s, 'z': a['z'] * s}

def v_dot(a, b):
    return a['x'] * b['x'] + a['z'] * b['z']

def v_len(a):
    return math.hypot(a['x'], a['z'])

def v_norm(a):
    L = v_len(a) or 1.0
    return {'x': a['x'] / L, 'z': a['z'] / L}

def v_perp(a):
    return {'x': -a['z'], 'z': a['x']}

def cross2(a, b):
    return a['x'] * b['z'] - a['z'] * b['x']


# ---- Приложение ----
class LaserApp:
    def __init__(self, root):
        self.root = root
        root.title('Лазер — рикошеты (Tkinter)')

        # Камера / координаты мира
        self.camX = 0.0
        self.camZ = 0.0
        self.scale = 20.0
        self.angleDeg = 0.0
        self._update_angle()

        # Состояния
        self.drawing_enabled = True
        self.is_drawing = False
        self.is_panning = False
        self.is_framing = False
        self.is_erasing = False
        self.frame = None
        self.last_mouse = {'x': 0, 'y': 0}

        # Рисунок
        # each: {color, size, points: [{'x','z'}, ...]}
        self.strokes = []

        # Метки (теги)
        # each: {id, number, a: {x,z}, b: {x,z}, strokeIndex}
        self.tags = []

        # Лазер
        self.laser_visible = True
        self.laser_reflect = True
        self.laser_length = 200.0
        self.laser_angle_deg = 0.0
        self.laser_max_bounces = 5
        self.laser_unlimited = False

        # Цвет, кисть
        self.current_color = '#000000'
        self.brush_size = 1

        # Изображение (маска)
        # image_obj: dict with img, mask(u8array), w, h, pixel_world, world_rect, canvas_img
        self.image_obj = None
        self.reflect_lum_threshold = 200
        self.sat_threshold = 0.15
        self.image_reflect_color = True

        # Поиск рикошетов
        self._search_running = False
        self._search_target = None
        self._search_step_deg = 1.0
        self._search_initial_angle = None
        self._search_steps_done = 0

        # Окно рикошетов (реальное время)
        self.ricochet_window = None
        self.ricochet_var = tk.StringVar(value='')
        self.ricochet_count_var = tk.StringVar(value='0')
        # ----Новое: частичная прогрузка (инициализация)----
        self.partial_load_enabled = False                      # флаг включения частичной прогрузки
        self.partial_load_per_interval = 1                     # сколько рикошетов показывать за 1 шаг
        self.partial_load_interval = 0.1                       # интервал в секундах между шагами (по умолчанию 0.1)
        # кэш расчёта трассировки и состояние прогрузки
        self._partial_cast_cache = None
        self._partial_visible_hits = 0
        self._partial_visible_segments = 0
        self._partial_task_id = None

        # UI
        self._build_ui()
        # Bindings
        self._bind_canvas_events()
        # Initial render
        self.render()

    # ---- UI ----
    def _build_ui(self):
        top = ttk.Frame(self.root)
        top.pack(side='top', fill='x')

        # Canvas
        self.canvas_w = 1200
        self.canvas_h = 800
        self.canvas = tk.Canvas(self.root, width=self.canvas_w, height=self.canvas_h, bg='white', cursor='cross')
        self.canvas.pack(fill='both', expand=True)

        # Controls frame
        ctrl = ttk.Frame(top)
        ctrl.pack(side='left', padx=6, pady=6)

        # Camera X/Z
        ttk.Label(ctrl, text='X:').grid(row=0, column=0)
        self.x_entry = ttk.Entry(ctrl, width=7)
        self.x_entry.grid(row=0, column=1)
        self.x_entry.insert(0, '0')

        ttk.Label(ctrl, text='Z:').grid(row=0, column=2)
        self.z_entry = ttk.Entry(ctrl, width=7)
        self.z_entry.grid(row=0, column=3)
        self.z_entry.insert(0, '0')

        ttk.Button(ctrl, text='Переместиться', command=self.goto_cam).grid(row=0, column=4, padx=4)
        ttk.Button(ctrl, text='Очистить всё', command=self.clear_all).grid(row=0, column=5, padx=4)

        # Rotation
        ttk.Label(ctrl, text='Поворот:').grid(row=1, column=0)
        self.rotate_scale = ttk.Scale(ctrl, from_=0, to=360, command=self._on_rotate)
        self.rotate_scale.set(0)
        self.rotate_scale.grid(row=1, column=1, columnspan=3, sticky='we')
        ttk.Button(ctrl, text='⤾', command=self.reset_rotation).grid(row=1, column=4)

        # Color & brush
        ttk.Button(ctrl, text='Цвет', command=self.pick_color).grid(row=2, column=0)
        self.color_preview = tk.Label(ctrl, bg=self.current_color, width=3)
        self.color_preview.grid(row=2, column=1)

        ttk.Label(ctrl, text='Размер кисти').grid(row=2, column=2)
        self.brush_entry = ttk.Entry(ctrl, width=5)
        self.brush_entry.grid(row=2, column=3)
        self.brush_entry.insert(0, '1')
        ttk.Button(ctrl, text='Применить', command=self.apply_brush).grid(row=2, column=4)

        # Laser controls
        laser_fr = ttk.LabelFrame(top, text='Лазер')
        laser_fr.pack(side='left', padx=6, pady=6)

        ttk.Label(laser_fr, text='Длина').grid(row=0, column=0)
        self.laser_len_entry = ttk.Entry(laser_fr, width=8)
        self.laser_len_entry.grid(row=0, column=1)
        self.laser_len_entry.insert(0, str(int(self.laser_length)))
        ttk.Button(laser_fr, text='OK', command=self.apply_laser_length).grid(row=0, column=2, padx=(4, 0))

        ttk.Label(laser_fr, text='Угол').grid(row=1, column=0)
        self.laser_angle_scale = ttk.Scale(laser_fr, from_=0, to=360, command=self._on_laser_angle)
        self.laser_angle_scale.set(self.laser_angle_deg)
        self.laser_angle_scale.grid(row=1, column=1, columnspan=2, sticky='we')

        self.laser_reflect_var = tk.BooleanVar(value=self.laser_reflect)
        ttk.Checkbutton(laser_fr, text='Отражения', variable=self.laser_reflect_var, command=self.toggle_laser_reflect).grid(row=2, column=0, columnspan=3)
        ttk.Button(laser_fr, text='Без лимита', command=self.toggle_laser_unlimited).grid(row=3, column=0, pady=4)

        self.laser_bounces_entry = ttk.Entry(laser_fr, width=8)
        self.laser_bounces_entry.grid(row=3, column=1)
        self.laser_bounces_entry.insert(0, str(self.laser_max_bounces))
        ttk.Button(laser_fr, text='OK', command=self.apply_laser_bounces).grid(row=3, column=2, padx=(4, 0))

        # bind Enter key in these entries
        self.laser_len_entry.bind('<Return>', lambda ev: self.apply_laser_length())
        self.laser_bounces_entry.bind('<Return>', lambda ev: self.apply_laser_bounces())

        # Modes and tags
        modes_fr = ttk.Frame(top)
        modes_fr.pack(side='left', padx=6, pady=6)

        self.frame_btn = ttk.Button(modes_fr, text='Режим рамки: Выкл', command=self.toggle_frame_mode)
        self.frame_btn.grid(row=0, column=0, padx=2)

        self.draw_btn = ttk.Button(modes_fr, text='Рисование: Вкл', command=self.toggle_draw)
        self.draw_btn.grid(row=0, column=1, padx=2)

        self.erase_btn = ttk.Button(modes_fr, text='Ластик', command=self.toggle_eraser)
        self.erase_btn.grid(row=0, column=2, padx=2)

        ttk.Label(modes_fr, text='Номер:').grid(row=1, column=0)
        self.frame_number_entry = ttk.Entry(modes_fr, width=6)
        self.frame_number_entry.grid(row=1, column=1)
        self.frame_number_entry.insert(0, '1')
        ttk.Button(modes_fr, text='Нанести номер', command=self.apply_number_from_frame).grid(row=1, column=2)

        ttk.Button(modes_fr, text='Очистить метки', command=self.clear_tags).grid(row=2, column=0)
        ttk.Button(modes_fr, text='Экспорт TXT', command=self.export_txt).grid(row=2, column=1)
        ttk.Button(modes_fr, text='Импорт TXT', command=self.import_txt).grid(row=2, column=2)
        ttk.Button(modes_fr, text='Процедурно расставить', command=self.procedural_assign_prompt).grid(row=3, column=0, columnspan=3, pady=4)

        # Поиск рикошетов
        self.search_btn = ttk.Button(modes_fr, text='Поиск рикошетов', command=self.search_ricochet_file)
        self.search_btn.grid(row=4, column=0, columnspan=2, pady=4, sticky='w')

        # Скачать рикошеты
        self.download_btn = ttk.Button(modes_fr, text='Скачать рикошеты', command=self.download_ricochets)
        self.download_btn.grid(row=4, column=2, pady=4, padx=(6, 0))

        # Показать рикошеты (окно)
        self.show_hits_btn = ttk.Button(modes_fr, text='Показать рикошеты', command=self.toggle_show_ricochets)
        self.show_hits_btn.grid(row=4, column=0, columnspan=3, pady=4)

        # Image controls
        img_fr = ttk.LabelFrame(top, text='Изображение (стена)')
        img_fr.pack(side='left', padx=6, pady=6)

        ttk.Button(img_fr, text='Загрузить изображение', command=self.load_image).grid(row=0, column=0)
        ttk.Button(img_fr, text='Удалить', command=self.remove_image).grid(row=0, column=1)

        ttk.Label(img_fr, text='Порог яркости').grid(row=1, column=0)
        self.lum_scale = ttk.Scale(img_fr, from_=0, to=255, command=self._on_lum)
        self.lum_scale.set(self.reflect_lum_threshold)
        self.lum_scale.grid(row=1, column=1)

        self.sat_scale = ttk.Scale(img_fr, from_=0, to=100, command=self._on_sat)
        self.sat_scale.set(int(self.sat_threshold * 100))
        self.sat_scale.grid(row=2, column=1)

        self.image_colorvar = tk.BooleanVar(value=self.image_reflect_color)
        ttk.Checkbutton(img_fr, text='Цветные отражают', variable=self.image_colorvar, command=self._on_image_color_toggle).grid(row=3, column=0, columnspan=2)

        # Status bar
        self.status_var = tk.StringVar(value='X:0 Z:0')
        status = ttk.Label(self.root, textvariable=self.status_var)
        status.pack(side='bottom', fill='x')
        # ----Новое(частичная прогрузка)----
        self.partial_btn = ttk.Button(laser_fr, text='Прогружать частично: Выкл', command=self.toggle_partial_load)
        self.partial_btn.grid(row=4, column=0, pady=(6,2), columnspan=1)

        ttk.Label(laser_fr, text='шт/шаг:').grid(row=4, column=1, sticky='e')
        self.partial_count_entry = ttk.Entry(laser_fr, width=6)
        self.partial_count_entry.grid(row=4, column=2, sticky='w')
        self.partial_count_entry.insert(0, str(self.partial_load_per_interval))

        ttk.Label(laser_fr, text='Интервал (с):').grid(row=5, column=0, sticky='e')
        self.partial_interval_entry = ttk.Entry(laser_fr, width=6)
        self.partial_interval_entry.grid(row=5, column=1, sticky='w')
        self.partial_interval_entry.insert(0, str(self.partial_load_interval))

        ttk.Button(laser_fr, text='Применить', command=self.apply_partial_params).grid(row=5, column=2, padx=(4,0))

        # бинды: Enter применяет параметры
        self.partial_count_entry.bind('<Return>', lambda ev: self.apply_partial_params())
        self.partial_interval_entry.bind('<Return>', lambda ev: self.apply_partial_params())
    
    # ---- Events / transforms ----
    def _bind_canvas_events(self):
        self.canvas.bind('<ButtonPress-1>', self.on_pointer_down)
        self.canvas.bind('<B1-Motion>', self.on_pointer_move)
        self.canvas.bind('<ButtonRelease-1>', self.on_pointer_up)
        self.canvas.bind('<ButtonPress-3>', self.on_right_down)
        self.canvas.bind('<B3-Motion>', self.on_right_move)
        self.canvas.bind('<ButtonRelease-3>', self.on_right_up)
        self.canvas.bind('<MouseWheel>', self.on_mouse_wheel)
        self.canvas.bind('<Double-Button-1>', self.on_double_click)

    def _update_angle(self):
        self.angleRad = math.radians(self.angleDeg % 360)
        self.cosA = math.cos(self.angleRad)
        self.sinA = math.sin(self.angleRad)

    def _on_rotate(self, val):
        try:
            self.angleDeg = float(val)
            self._update_angle()
            self.render()
        except Exception:
            pass

    def reset_rotation(self):
        self.angleDeg = 0
        self.rotate_scale.set(0)
        self._update_angle()
        self.render()

    def screen_to_world(self, sx, sy):
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        cx = w / 2
        cz = h / 2
        dx = (sx - cx) / self.scale
        dz = (sy - cz) / self.scale
        wx = self.camX + dx * self.cosA + dz * self.sinA
        wz = self.camZ - dx * self.sinA + dz * self.cosA
        return {'x': wx, 'z': wz}

    def world_to_screen(self, wx, wz):
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()
        cx = w / 2
        cz = h / 2
        vx = wx - self.camX
        vz = wz - self.camZ
        sx = cx + (vx * self.cosA - vz * self.sinA) * self.scale
        sy = cz + (vx * self.sinA + vz * self.cosA) * self.scale
        return {'x': sx, 'y': sy}

    # ---- Mouse handlers ----
    def on_pointer_down(self, ev):
        sx, sy = ev.x, ev.y
        if self.is_framing or self.is_erasing:
            self.frame = {'x1': sx, 'y1': sy, 'x2': sx, 'y2': sy, 'active': True, 'selecting': True}
            self.render()
            return

        if self.drawing_enabled:
            self.is_drawing = True
            p = self.screen_to_world(sx, sy)
            stroke = {'color': self.current_color, 'size': self.brush_size, 'points': [p]}
            self.strokes.append(stroke)
            self.render()
        else:
            self.is_panning = True
            self.last_mouse = {'x': ev.x, 'y': ev.y}

    def on_pointer_move(self, ev):
        sx, sy = ev.x, ev.y
        world_pt = self.screen_to_world(sx, sy)
        self.status_var.set(f"X:{int(world_pt['x'])} Z:{int(world_pt['z'])}")

        if self.is_drawing:
            stroke = self.strokes[-1]
            last = stroke['points'][-1]
            dx = world_pt['x'] - last['x']
            dz = world_pt['z'] - last['z']
            minDist = 0.2 / max(1, self.scale)
            if dx * dx + dz * dz > minDist * minDist:
                stroke['points'].append(world_pt)
                self.render()

        elif self.is_panning:
            dx = ev.x - self.last_mouse['x']
            dy = ev.y - self.last_mouse['y']
            vScreenX = dx / self.scale
            vScreenZ = dy / self.scale
            worldDx = vScreenX * self.cosA + vScreenZ * self.sinA
            worldDz = -vScreenX * self.sinA + vScreenZ * self.cosA
            self.camX -= worldDx
            self.camZ -= worldDz
            self.last_mouse = {'x': ev.x, 'y': ev.y}
            self.x_entry.delete(0, 'end')
            self.x_entry.insert(0, str(int(self.camX)))
            self.z_entry.delete(0, 'end')
            self.z_entry.insert(0, str(int(self.camZ)))
            self.render()

        elif self.frame and self.frame.get('selecting'):
            self.frame['x2'] = sx
            self.frame['y2'] = sy
            self.render()

    def on_pointer_up(self, ev):
        if self.is_drawing:
            self.is_drawing = False
            self.is_panning = False

        if self.frame and self.frame.get('selecting'):
            self.frame['selecting'] = False
            if self.is_erasing:
                self.erase_strokes_in_frame(self.frame)
                self.frame = None
                self.is_erasing = False
                self.render()
            elif self.is_framing:
                self.apply_number_from_frame()
                self.frame = None
                self.render()
            else:
                self.frame = None
                self.render()

    def on_right_down(self, ev):
        self.is_panning = True
        self.last_mouse = {'x': ev.x, 'y': ev.y}

    def on_right_move(self, ev):
        self.on_pointer_move(ev)

    def on_right_up(self, ev):
        self.is_panning = False

    def on_mouse_wheel(self, ev):
        delta = ev.delta / 120
        sx, sy = ev.x, ev.y
        before = self.screen_to_world(sx, sy)
        factor = 1.0 + delta * 0.1
        self.scale = max(4, min(160, self.scale * factor))
        after = self.screen_to_world(sx, sy)
        self.camX += before['x'] - after['x']
        self.camZ += before['z'] - after['z']
        self.render()

    def on_double_click(self, ev):
        sx, sy = ev.x, ev.y
        best = None
        best_dist = 1e9
        for t in self.tags:
            sA = self.world_to_screen(t['a']['x'], t['a']['z'])
            sB = self.world_to_screen(t['b']['x'], t['b']['z'])
            midx = (sA['x'] + sB['x']) / 2
            midy = (sA['y'] + sB['y']) / 2
            d = math.hypot(midx - sx, midy - sy)
            if d < best_dist:
                best_dist = d
                best = t
        if best and best_dist < 24:
            if messagebox.askyesno('Удалить метку', f"Удалить метку '{best['number']}'?"):
                self.tags = [x for x in self.tags if x['id'] != best['id']]
                self.render()

    # ---- Drawing / utilities ----
    def draw_grid(self, ctx):
        w = self.canvas.winfo_width()
        h = self.canvas.winfo_height()

        lt = self.screen_to_world(0, 0)
        rb = self.screen_to_world(w, h)

        for x in range(math.floor(lt['x']), math.ceil(rb['x']) + 1):
            s = self.world_to_screen(x, 0)
            ctx.create_line(s['x'], 0, s['x'], h, fill='#000000', width=1)

        for z in range(math.floor(lt['z']), math.ceil(rb['z']) + 1):
            s = self.world_to_screen(0, z)
            ctx.create_line(0, s['y'], w, s['y'], fill="#000000", width=1)

    def draw_strokes(self, ctx):
        for s in self.strokes:
            pts = s['points']
            if not pts:
                continue
            width = max(1, s['size'] * max(0.6, self.scale / 20))
            if len(pts) == 1:
                p = self.world_to_screen(pts[0]['x'], pts[0]['z'])
                ctx.create_oval(p['x'] - width / 2, p['y'] - width / 2,
                                p['x'] + width / 2, p['y'] + width / 2,
                                fill=s['color'], outline='')
                continue
            coords = []
            for p in pts:
                sp = self.world_to_screen(p['x'], p['z'])
                coords.extend([sp['x'], sp['y']])
            ctx.create_line(*coords, fill=s['color'], width=width, capstyle='round', joinstyle='round')

    def draw_tags(self, ctx):
        for t in self.tags:
            sA = self.world_to_screen(t['a']['x'], t['a']['z'])
            sB = self.world_to_screen(t['b']['x'], t['b']['z'])
            ctx.create_line(sA['x'], sA['y'], sB['x'], sB['y'], fill='#B41E1E', width=3)
            midx = (sA['x'] + sB['x']) / 2
            midy = (sA['y'] + sB['y']) / 2
            ctx.create_text(midx, midy - 8, text=str(t['number']), fill='#141414', font=('Arial', 12))

    def draw_frame(self, ctx):
        if not self.frame:
            return
        f = self.frame
        x1, y1, x2, y2 = f['x1'], f['y1'], f['x2'], f['y2']
        xMin, xMax = min(x1, x2), max(x1, x2)
        yMin, yMax = min(y1, y2), max(y1, y2)
        ctx.create_rectangle(xMin, yMin, xMax, yMax, dash=(6, 4), outline='#1478DC')

    def draw_image_if_any(self, ctx):
        if not self.image_obj:
            return
        rect = self.image_obj['world_rect']
        a = self.world_to_screen(rect['minX'], rect['minZ'])
        try:
            img = ImageTk.PhotoImage(self.image_obj['canvas_img'])
            self.canvas.image_ref = img
            self.canvas.create_image(a['x'], a['y'], anchor='nw', image=img)
        except Exception:
            pass

    # ---- Rendering ----
    def render(self):
        self.canvas.delete('all')
        self.canvas.create_rectangle(0, 0, self.canvas.winfo_width(), self.canvas.winfo_height(), fill='#ffffff', outline='')

        # Optional grid
        # self.draw_grid(self.canvas)
        self.draw_image_if_any(self.canvas)
        self.draw_strokes(self.canvas)

        # Laser cast & draw
        if self.laser_visible:
            origin = {'x': 0.0, 'z': 0.0}
            angle = math.radians(self.laser_angle_deg)
            dir_vec = {'x': math.cos(angle), 'z': math.sin(angle)}
            maxB = None if self.laser_unlimited else int(self.laser_max_bounces) - 1

        # При включенной частичной прогрузке используем кэш трассировки и
        # отрисовываем только видимые сегменты/попадания; если кэша нет — создаём её.
            if self.partial_load_enabled:
                if not self._partial_cast_cache:
                    if self.laser_reflect:
                        self._partial_cast_cache = self.cast_laser(origin, dir_vec, float(self.laser_length), maxB)
                    else:
                        self._partial_cast_cache = {
                            'segments': [{'a': origin, 'b': v_add(origin, v_scale(dir_vec, self.laser_length))}],
                            'hits': []
                        }
                    # Инициализация видимых счётчиков
                    self._partial_visible_segments = 1 if self._partial_cast_cache.get('segments') else 0
                    self._partial_visible_hits = 0

                cast = self._partial_cast_cache
                segments = cast.get('segments', [])
                hits = cast.get('hits', [])

                draw_segments = min(self._partial_visible_segments, len(segments))
                draw_hits = min(self._partial_visible_hits, len(hits))
            else:
                # Обычная (полная) отрисовка — пересчитываем трассу и показываем всё
                if self.laser_reflect:
                    cast = self.cast_laser(origin, dir_vec, float(self.laser_length), maxB)
                else:
                    cast = {
                        'segments': [{'a': origin, 'b': v_add(origin, v_scale(dir_vec, self.laser_length))}],
                        'hits': []
                    }
                segments = cast.get('segments', [])
                hits = cast.get('hits', [])

                draw_segments = len(segments)
                draw_hits = len(hits)

            # Отрисовать сегменты (только нужное количество)
            for i in range(min(draw_segments, len(segments))):
                seg = segments[i]
                A = self.world_to_screen(seg['a']['x'], seg['a']['z'])
                B = self.world_to_screen(seg['b']['x'], seg['b']['z'])
                # сохраняем прежний стиль: прерывистая красная линия
                self.canvas.create_line(A['x'], A['y'], B['x'], B['y'], fill='#C81E1E', width=2, dash=(6, 4))

            # Отрисовать попадания (только нужное количество)
            for i in range(min(draw_hits, len(hits))):
                h = hits[i]
                p = self.world_to_screen(h['point']['x'], h['point']['z'])
                color = '#50A028' if h.get('source') == 'image' else '#FFC828'
                self.canvas.create_oval(p['x'] - 4, p['y'] - 4, p['x'] + 4, p['y'] + 4, fill=color, outline='')

            originS = self.world_to_screen(0, 0)
            self.canvas.create_line(originS['x'] - 8, originS['y'], originS['x'] + 8, originS['y'], fill='#000000', width=1)
            self.canvas.create_line(originS['x'], originS['y'] - 8, originS['x'], originS['y'] + 8, fill='#000000', width=1)

            # Обновление текстовой информации (сколько всего и сколько видно при partial)
            total_segments = len(segments)
            total_hits = len(hits)
            txt = f"segments: {total_segments}, hits: {total_hits}"
            if self.partial_load_enabled:
                txt += f"   (visible segments: {draw_segments}, visible hits: {draw_hits})"
            self.canvas.create_text(10, self.canvas.winfo_height() - 10, anchor='sw', text=txt, fill='black')

        # Если рамка есть — отрисовать её и метки
        if self.frame and self.frame.get('active'):
            self.draw_frame(self.canvas)
        self.draw_tags(self.canvas)

        # Обновление окна рикошетов, если открыто
        if self.ricochet_window:
            try:
                seq = self._get_ricochet_sequence_for_angle(self.laser_angle_deg)
                current_seq_str = ' '.join(seq)
                self.ricochet_var.set(current_seq_str)
                self.ricochet_count_var.set(str(len(seq)) if current_seq_str.strip() else '0')
            except Exception:
                pass

    # ---- Geometry intersections ----
    def intersect_ray_segment(self, P, r, Q, Rseg):
        s = v_sub(Rseg, Q)
        denom = cross2(r, s)
        EPS = 1e-9
        if abs(denom) < EPS:
            return None
        qmp = v_sub(Q, P)
        t = cross2(qmp, s) / denom
        u = cross2(qmp, r) / denom
        if t > 1e-7 and u >= -1e-7 and u <= 1 + 1e-7:
            return {'t': t, 'u': u, 'point': v_add(P, v_scale(r, t))}
        return None

    def seg_seg_intersection(self, A, B, C, D):
        r = v_sub(B, A)
        s = v_sub(D, C)
        denom = cross2(r, s)
        EPS = 1e-9
        if abs(denom) < EPS:
            return None
        qp = v_sub(C, A)
        t = cross2(qp, s) / denom
        u = cross2(qp, r) / denom
        if t >= -EPS and t <= 1 + EPS and u >= -EPS and u <= 1 + EPS:
            return v_add(A, v_scale(r, t))
        return None

    def intersect_ray_aabb(self, P, R, rect):
        EPS = 1e-9
        tmin = -1e9
        tmax = 1e9

        # X slab
        if abs(R['x']) < EPS:
            if P['x'] < rect['minX'] or P['x'] > rect['maxX']:
                return None
        else:
            tx1 = (rect['minX'] - P['x']) / R['x']
            tx2 = (rect['maxX'] - P['x']) / R['x']
            ta = min(tx1, tx2)
            tb = max(tx1, tx2)
            tmin = max(tmin, ta)
            tmax = min(tmax, tb)

        # Z slab
        if abs(R['z']) < EPS:
            if P['z'] < rect['minZ'] or P['z'] > rect['maxZ']:
                return None
        else:
            tz1 = (rect['minZ'] - P['z']) / R['z']
            tz2 = (rect['maxZ'] - P['z']) / R['z']
            ta = min(tz1, tz2)
            tb = max(tz1, tz2)
            tmin = max(tmin, ta)
            tmax = min(tmax, tb)

        if tmax < tmin:
            return None
        return {'tmin': tmin, 'tmax': tmax}

    def intersect_image_along_ray(self, P, R, remaining):
        if not self.image_obj:
            return None
        rect = self.image_obj['world_rect']
        slab = self.intersect_ray_aabb(P, R, rect)
        if not slab:
            return None
        tStart = max(slab['tmin'], 1e-6)
        tEnd = min(slab['tmax'], remaining)
        if tStart > tEnd:
            return None

        pxW = self.image_obj['pixel_world']
        step = max(pxW * 0.5, pxW * 0.2)
        t = tStart
        W = self.image_obj['w']
        H = self.image_obj['h']
        mask = self.image_obj['mask']

        while t <= tEnd + 1e-9:
            pt = v_add(P, v_scale(R, t))
            u = (pt['x'] - rect['minX']) / pxW
            v = (pt['z'] - rect['minZ']) / pxW
            ix = int(math.floor(u))
            iy = int(math.floor(v))
            if 0 <= ix < W and 0 <= iy < H:
                if mask[iy * W + ix]:
                    # binary refine
                    lo = max(t - step, tStart)
                    hi = t
                    for _ in range(20):
                        mid = (lo + hi) / 2.0
                        pm = v_add(P, v_scale(R, mid))
                        uu = (pm['x'] - rect['minX']) / pxW
                        vv = (pm['z'] - rect['minZ']) / pxW
                        ixm = int(math.floor(uu))
                        iym = int(math.floor(vv))
                        if 0 <= ixm < W and 0 <= iym < H and mask[iym * W + ixm]:
                            hi = mid
                        else:
                            lo = mid
                    tHit = hi
                    hitPt = v_add(P, v_scale(R, tHit))

                    ix0 = max(0, min(W - 1, int(math.floor((hitPt['x'] - rect['minX']) / pxW))))
                    iy0 = max(0, min(H - 1, int(math.floor((hitPt['z'] - rect['minZ']) / pxW))))

                    left = mask[iy0 * W + (ix0 - 1)] if ix0 > 0 else 0
                    right = mask[iy0 * W + (ix0 + 1)] if ix0 < W - 1 else 0
                    top = mask[(iy0 - 1) * W + ix0] if iy0 > 0 else 0
                    bottom = mask[(iy0 + 1) * W + ix0] if iy0 < H - 1 else 0

                    gx = right - left
                    gz = bottom - top
                    n = {'x': gx, 'z': gz}
                    nlen = math.hypot(n['x'], n['z'])
                    if nlen < 1e-3:
                        n = v_perp(R)
                    else:
                        n = {'x': n['x'] / nlen, 'z': n['z'] / nlen}
                    if v_dot(R, n) > 0:
                        n = v_scale(n, -1)
                    return {'t': tHit, 'point': hitPt, 'normal': n}
            t += step
        return None

    def cast_laser(self, origin, dir_vec, maxLen, maxBounces):
        segs = []
        hits = []

        P = {'x': origin['x'], 'z': origin['z']}
        remaining = maxLen
        R = v_norm(dir_vec)
        unlimited = (maxBounces is None)
        bounce = 0

        while True:
            best = None
            bestStrokeIdx = -1

            # stroke segments
            for si, s in enumerate(self.strokes):
                if not s or 'points' not in s or len(s['points']) < 2:
                    continue
                for i in range(1, len(s['points'])):
                    A = s['points'][i - 1]
                    B = s['points'][i]
                    inter = self.intersect_ray_segment(P, R, A, B)
                    if not inter:
                        continue
                    if inter['t'] <= remaining + 1e-8:
                        if not best or inter['t'] < best['t']:
                            best = {'t': inter['t'], 'point': inter['point'], 'segA': A, 'segB': B, 'type': 'stroke'}
                            bestStrokeIdx = si

            # image
            if self.image_obj:
                imgHit = self.intersect_image_along_ray(P, R, remaining)
                if imgHit:
                    if not best or imgHit['t'] < best['t']:
                        best = {'t': imgHit['t'], 'point': imgHit['point'], 'normal': imgHit.get('normal'), 'type': 'image'}

            if not best:
                end = v_add(P, v_scale(R, remaining))
                segs.append({'a': P, 'b': end})
                break

            segs.append({'a': P, 'b': best['point']})

            if best['type'] == 'stroke':
                hits.append({'point': best['point'], 'strokeIndex': bestStrokeIdx})
            else:
                hits.append({'point': best['point'], 'source': 'image'})

            remaining -= best['t']
            if remaining <= 1e-6:
                break
            if not unlimited and bounce >= maxBounces:
                break

            # reflection
            if best['type'] == 'stroke':
                segDir = v_norm(v_sub(best['segB'], best['segA']))
                n = v_perp(segDir)
                if v_dot(R, n) > 0:
                    n = v_scale(n, -1)
            else:
                n = best.get('normal') or v_perp(R)
                if v_dot(R, n) > 0:
                    n = v_scale(n, -1)

            dotrn = v_dot(R, n)
            Rref = v_sub(R, v_scale(n, 2 * dotrn))

            P = v_add(best['point'], v_scale(Rref, 1e-6))
            R = v_norm(Rref)
            bounce += 1

        return {'segments': segs, 'hits': hits}

    # ---- Frame / tags / erase ----
    def rect_from_frame_screen(self, f):
        xMin = min(f['x1'], f['x2'])
        xMax = max(f['x1'], f['x2'])
        yMin = min(f['y1'], f['y2'])
        yMax = max(f['y1'], f['y2'])
        return {'xMin': xMin, 'xMax': xMax, 'yMin': yMin, 'yMax': yMax}

    def clip_segment_to_rect_screen(self, A, B, rect):
        x0, y0 = A['x'], A['y']
        x1, y1 = B['x'], B['y']
        dx = x1 - x0
        dy = y1 - y0
        p = [-dx, dx, -dy, dy]
        q = [x0 - rect['xMin'], rect['xMax'] - x0, y0 - rect['yMin'], rect['yMax'] - y0]
        u1 = 0.0
        u2 = 1.0
        for i in range(4):
            if abs(p[i]) < 1e-9:
                if q[i] < 0:
                    return None
            else:
                t = q[i] / p[i]
                if p[i] < 0:
                    if t > u2:
                        return None
                    if t > u1:
                        u1 = t
                else:
                    if t < u1:
                        return None
                    if t < u2:
                        u2 = t
        if u2 < u1:
            return None
        C = {'x': x0 + u1 * dx, 'y': y0 + u1 * dy}
        D = {'x': x0 + u2 * dx, 'y': y0 + u2 * dy}
        return {'a': C, 'b': D}

    def get_segments_in_frame(self, frame):
        if not frame:
            return []
        rect = self.rect_from_frame_screen(frame)
        found = []
        for si, s in enumerate(self.strokes):
            if not s or 'points' not in s or len(s['points']) < 2:
                continue
            for i in range(1, len(s['points'])):
                A = self.world_to_screen(s['points'][i - 1]['x'], s['points'][i - 1]['z'])
                B = self.world_to_screen(s['points'][i]['x'], s['points'][i]['z'])
                clipped = self.clip_segment_to_rect_screen(A, B, rect)
                if clipped:
                    found.append({'strokeIndex': si, 'a': clipped['a'], 'b': clipped['b'], 'strokeSize': s['size']})
        return found

    def apply_number_from_frame(self):
        if not self.frame:
            messagebox.showinfo('Ошибка', 'Создайте рамку прежде чем наносить номер.')
            return
        try:
            n = int(self.frame_number_entry.get())
        except:
            messagebox.showinfo('Ошибка', 'Введите корректный номер.')
            return

        segs = self.get_segments_in_frame(self.frame)
        if not segs:
            messagebox.showinfo('Результат', 'В рамке не найдено отрезков.')
            return

        for s in segs:
            worldA = self.screen_to_world(s['a']['x'], s['a']['y'])
            worldB = self.screen_to_world(s['b']['x'], s['b']['y'])
            _id = str(time.time()) + str(random.random())
            strokeIndex = s.get('strokeIndex', None)
            self.tags.append({'id': _id, 'number': n, 'a': worldA, 'b': worldB, 'strokeIndex': strokeIndex})
        self.render()

    def point_on_segment(self, pt, A, B, eps=1e-6):
        v = v_sub(B, A)
        w = v_sub(pt, A)
        if abs(cross2(v, w)) > eps:
            return False
        dot = v_dot(w, v)
        if dot < -eps:
            return False
        vLenSq = v['x'] * v['x'] + v['z'] * v['z']
        if dot > vLenSq + eps:
            return False
        return True

    def segment_rect_intersections_screen(self, A, B, rect):
        edges = [
            ({'x': rect['xMin'], 'y': rect['yMin']}, {'x': rect['xMax'], 'y': rect['yMin']}),
            ({'x': rect['xMax'], 'y': rect['yMin']}, {'x': rect['xMax'], 'y': rect['yMax']}),
            ({'x': rect['xMax'], 'y': rect['yMax']}, {'x': rect['xMin'], 'y': rect['yMax']}),
            ({'x': rect['xMin'], 'y': rect['yMax']}, {'x': rect['xMin'], 'y': rect['yMin']})
        ]
        inters = []
        for e in edges:
            p = self.seg_seg_intersection({'x': A['x'], 'z': A['y']},
                                          {'x': B['x'], 'z': B['y']},
                                          {'x': e[0]['x'], 'z': e[0]['y']},
                                          {'x': e[1]['x'], 'z': e[1]['y']})
            if p:
                ip = {'x': p['x'], 'y': p['z']}
                if not any(math.hypot(q['x'] - ip['x'], q['y'] - ip['y']) < 1e-6 for q in inters):
                    inters.append(ip)
        if len(inters) <= 1:
            return inters

        def paramT(P):
            dx = B['x'] - A['x']
            dy = B['y'] - A['y']
            if abs(dx) >= abs(dy):
                return (P['x'] - A['x']) / (dx or 1e-9)
            return (P['y'] - A['y']) / (dy or 1e-9)

        inters.sort(key=paramT)
        return inters

    def erase_strokes_in_frame(self, frame):
        if not frame:
            return
        rect = self.rect_from_frame_screen(frame)
        newStrokes = []
        for stroke in self.strokes:
            if not stroke or 'points' not in stroke or len(stroke['points']) == 0:
                continue
            ptsWorld = stroke['points']
            ptsScreen = [self.world_to_screen(p['x'], p['z']) for p in ptsWorld]
            currentOutside = []
            outsidePolylines = []

            for i in range(1, len(ptsScreen)):
                A_s = ptsScreen[i - 1]
                B_s = ptsScreen[i]
                A_w = ptsWorld[i - 1]
                B_w = ptsWorld[i]

                A_in = (A_s['x'] >= rect['xMin'] and A_s['x'] <= rect['xMax'] and A_s['y'] >= rect['yMin'] and A_s['y'] <= rect['yMax'])
                B_in = (B_s['x'] >= rect['xMin'] and B_s['x'] <= rect['xMax'] and B_s['y'] >= rect['yMin'] and B_s['y'] <= rect['yMax'])
                inters = self.segment_rect_intersections_screen(A_s, B_s, rect)

                if (not A_in) and (not B_in) and len(inters) == 0:
                    if not currentOutside:
                        currentOutside.append({'x': A_w['x'], 'z': A_w['z']})
                    currentOutside.append({'x': B_w['x'], 'z': B_w['z']})

                elif (not A_in) and (not B_in) and len(inters) == 2:
                    if not currentOutside:
                        currentOutside.append({'x': A_w['x'], 'z': A_w['z']})
                    I1w = self.screen_to_world(inters[0]['x'], inters[0]['y'])
                    I2w = self.screen_to_world(inters[1]['x'], inters[1]['y'])
                    currentOutside.append({'x': I1w['x'], 'z': I1w['z']})
                    outsidePolylines.append(currentOutside)
                    currentOutside = []
                    currentOutside.append({'x': I2w['x'], 'z': I2w['z']})
                    currentOutside.append({'x': B_w['x'], 'z': B_w['z']})

                elif (not A_in) and B_in:
                    if len(inters) >= 1:
                        Iw = self.screen_to_world(inters[0]['x'], inters[0]['y'])
                        if not currentOutside:
                            currentOutside.append({'x': A_w['x'], 'z': A_w['z']})
                        currentOutside.append({'x': Iw['x'], 'z': Iw['z']})
                        outsidePolylines.append(currentOutside)
                        currentOutside = []
                    else:
                        if not currentOutside:
                            currentOutside.append({'x': A_w['x'], 'z': A_w['z']})
                        outsidePolylines.append(currentOutside)
                        currentOutside = []

                elif A_in and (not B_in):
                    if len(inters) >= 1:
                        Iw = self.screen_to_world(inters[0]['x'], inters[0]['y'])
                        currentOutside = [{'x': Iw['x'], 'z': Iw['z']}, {'x': B_w['x'], 'z': B_w['z']}]
                    else:
                        currentOutside = [{'x': B_w['x'], 'z': B_w['z']}]
                else:
                    pass

            if currentOutside:
                outsidePolylines.append(currentOutside)
                currentOutside = []

            for poly in outsidePolylines:
                clean = []
                for p in poly:
                    if not clean:
                        clean.append({'x': p['x'], 'z': p['z']})
                    else:
                        last = clean[-1]
                        if math.hypot(last['x'] - p['x'], last['z'] - p['z']) > 1e-6:
                            clean.append({'x': p['x'], 'z': p['z']})
                if not clean:
                    continue
                if len(clean) == 1:
                    newStrokes.append({'color': stroke['color'], 'size': stroke['size'], 'points': [clean[0]]})
                else:
                    newStrokes.append({'color': stroke['color'], 'size': stroke['size'], 'points': clean})

        self.strokes = newStrokes

    # ---- Export / import ----
    def export_txt(self):
        out = {
            'strokes': [{'color': s['color'], 'size': s['size'],
                         'points': [[p['x'], p['z']] for p in s['points']]} for s in self.strokes],
            'tags': [[t['a']['x'], t['a']['z'], t['b']['x'], t['b']['z'], t['number']] for t in self.tags]
        }
        fn = filedialog.asksaveasfilename(defaultextension='.json', filetypes=[('JSON', '*.json'), ('TXT', '*.txt')])
        if not fn:
            return
        with open(fn, 'w', encoding='utf-8') as f:
            json.dump(out, f, ensure_ascii=False, indent=2)
        messagebox.showinfo('Экспорт', 'Сохранено')

    def import_txt(self):
        fn = filedialog.askopenfilename(filetypes=[('JSON', '*.json'), ('TXT', '*.txt')])
        if not fn:
            return
        with open(fn, 'r', encoding='utf-8') as f:
            try:
                data = json.load(f)
            except Exception:
                messagebox.showerror('Ошибка', 'Не могу прочитать JSON')
                return
        if not isinstance(data, dict) or 'strokes' not in data or 'tags' not in data:
            messagebox.showerror('Ошибка', 'Неверный формат файла')
            return
        if not messagebox.askyesno('Импорт', 'Импортировать файл? Текущие рисунки будут удалены.'):
            return
        self.strokes = []
        self.tags = []
        for s in data.get('strokes', []):
            pts = [{'x': float(p[0]), 'z': float(p[1])} for p in s.get('points', [])]
            self.strokes.append({'color': s.get('color', "#000000"), 'size': float(s.get('size', 1)), 'points': pts})
        for t in data.get('tags', []):
            if not isinstance(t, list) or len(t) < 5:
                continue
            ax, az, bx, bz, num = float(t[0]), float(t[1]), float(t[2]), float(t[3]), float(t[4])
            _id = str(time.time()) + str(random.random())
            si = self.find_stroke_index_containing_segment({'x': ax, 'z': az}, {'x': bx, 'z': bz})
            self.tags.append({'id': _id, 'number': num, 'a': {'x': ax, 'z': az}, 'b': {'x': bx, 'z': bz}, 'strokeIndex': si})
        self.render()

    # ---- Tags assignment helpers ----
    def find_stroke_index_containing_segment(self, A, B):
        for si, s in enumerate(self.strokes):
            if not s or 'points' not in s or len(s['points']) < 2:
                continue
            for i in range(1, len(s['points'])):
                pA = s['points'][i - 1]
                pB = s['points'][i]
                if self.point_on_segment(A, pA, pB, 1e-4) and self.point_on_segment(B, pA, pB, 1e-4):
                    return si
        return None

    def clear_tags(self):
        if not messagebox.askyesno('Очистить метки', 'Очистить все метки?'):
            return
        self.tags = []
        self.render()

    def clear_all(self):
        if not messagebox.askyesno('Очистить всё', 'Очистить все рисунки и метки?'):
            return
        self.strokes = []
        self.tags = []
        self.render()

    # ---- Image handling ----
    def prepare_image_mask(self, pil_img):
        img = pil_img.convert('RGB')
        W, H = img.size
        data = list(img.getdata())
        mask = [0] * (W * H)
        for y in range(H):
            for x in range(W):
                r, g, b = data[y * W + x]
                lum = 0.299 * r + 0.587 * g + 0.114 * b
                mx = max(r, g, b)
                mn = min(r, g, b)
                sat = (mx - mn) / (mx or 1)
                isColor = sat > self.sat_threshold
                isDark = lum < self.reflect_lum_threshold
                mask[y * W + x] = 1 if (isDark or (self.image_reflect_color and isColor)) else 0

        maxPx = max(W, H)
        targetWorldMax = 200.0
        pixelWorld = targetWorldMax / maxPx
        widthWorld = W * pixelWorld
        heightWorld = H * pixelWorld
        rect = {'minX': -widthWorld / 2, 'minZ': -heightWorld / 2, 'maxX': widthWorld / 2, 'maxZ': heightWorld / 2}

        canvas_img = img.resize((W, H))
        self.image_obj = {
            'img': img,
            'mask': mask,
            'w': W,
            'h': H,
            'pixel_world': pixelWorld,
            'world_rect': rect,
            'canvas_img': canvas_img
        }

    def load_image(self):
        fn = filedialog.askopenfilename(filetypes=[('Images', '*.png;*.jpg;*.jpeg;*.bmp')])
        if not fn:
            return
        pil_img = Image.open(fn).convert('RGB')
        self.prepare_image_mask(pil_img)
        self.render()

    def remove_image(self):
        if self.image_obj and not messagebox.askyesno('Удалить изображение', 'Удалить изображение?'):
            return
        self.image_obj = None
        self.render()

    def _on_lum(self, val):
        try:
            self.reflect_lum_threshold = int(float(val))
            if self.image_obj:
                self.prepare_image_mask(self.image_obj['img'])
            self.render()
        except:
            pass

    def _on_sat(self, val):
        try:
            self.sat_threshold = float(val) / 100.0
            if self.image_obj:
                self.prepare_image_mask(self.image_obj['img'])
            self.render()
        except:
            pass

    def _on_image_color_toggle(self):
        self.image_reflect_color = bool(self.image_colorvar.get())
        if self.image_obj:
            self.prepare_image_mask(self.image_obj['img'])
        self.render()

    # ---- Laser controls ----
    def _on_laser_angle(self, val):
        try:
            self.laser_angle_deg = float(val)
            self.render()
        except:
            pass

    def toggle_laser_reflect(self):
        self.laser_reflect = bool(self.laser_reflect_var.get())
        self.render()

    def toggle_laser_unlimited(self):
        self.laser_unlimited = not self.laser_unlimited
        if self.laser_unlimited:
            self.laser_len_entry.config(state='disabled')
        else:
            self.laser_len_entry.config(state='normal')
        self.render()

    def apply_laser_length(self):
        try:
            val = float(self.laser_len_entry.get())
            if val <= 0:
                raise ValueError()
            self.laser_length = val
            if abs(self.laser_length - int(self.laser_length)) < 1e-9:
                self.laser_len_entry.delete(0, 'end')
                self.laser_len_entry.insert(0, str(int(self.laser_length)))
            else:
                self.laser_len_entry.delete(0, 'end')
                self.laser_len_entry.insert(0, str(self.laser_length))
            self.render()
        except Exception:
            messagebox.showerror('Ошибка', 'Введите корректную длину лазера (число > 0).')

    def apply_laser_bounces(self):
        try:
            val = int(float(self.laser_bounces_entry.get()))
            if val < 0:
                raise ValueError()
            self.laser_max_bounces = val
            self.laser_bounces_entry.delete(0, 'end')
            self.laser_bounces_entry.insert(0, str(self.laser_max_bounces))
            self.render()
        except Exception:
            messagebox.showerror('Ошибка', 'Введите корректное количество рикошетов (целое >= 0).')

    # ---- Color / brush ----
    def pick_color(self):
        c = colorchooser.askcolor(color=self.current_color)
        if c and c[1]:
            self.current_color = c[1]
            self.color_preview.config(bg=self.current_color)

    def apply_brush(self):
        try:
            self.brush_size = max(1, int(self.brush_entry.get()))
        except:
            self.brush_size = 1

    # ---- Modes ----
    def toggle_frame_mode(self):
        self.is_framing = not self.is_framing
        self.frame_btn.config(text=f"Режим рамки: {'Вкл' if self.is_framing else 'Выкл'}")
        if self.is_framing:
            self.is_erasing = False
            self.erase_btn.config(text='Ластик')

    def toggle_draw(self):
        self.drawing_enabled = not self.drawing_enabled
        self.draw_btn.config(text=f"Рисование: {'Вкл' if self.drawing_enabled else 'Выкл'}")

    def toggle_eraser(self):
        self.is_erasing = not self.is_erasing
        self.erase_btn.config(text=f"Ластик: {'Вкл' if self.is_erasing else 'Выкл'}")
        if self.is_erasing:
            self.is_framing = False
            self.frame_btn.config(text='Режим рамки: Выкл')

    # ---- Procedural assignment ----
    def procedural_assign_prompt(self):
        if not self.strokes:
            messagebox.showinfo('Нет линий', 'Нет нарисованных линий для распределения меток.')
            return
        s = simpledialog.askstring('Процедурная расстановка', 'Введите количество меток на каждый отрезок (целое >=1).', initialvalue='1')
        if s is None:
            return
        try:
            k = int(s)
            if k < 1:
                raise ValueError()
        except:
            messagebox.showerror('Ошибка', 'Введите целое >=1')
            return
        cnt = self.approx_mark_count(k)
        if not messagebox.askyesno('Подтвердите', f'Будет создано примерно {cnt} меток. Старые метки будут удалены. Продолжить?'):
            return
        self.procedural_assign(k)
        self.render()
        messagebox.showinfo('Готово', 'Процедурная расстановка завершена.')

    def approx_mark_count(self, k):
        cnt = 0
        for s in self.strokes:
            if not s or 'points' not in s:
                continue
            for i in range(1, len(s['points'])):
                cnt += k
        return cnt

    def procedural_assign(self, kPerSegment):
        self.tags = []
        nextNumber = 1
        for si, s in enumerate(self.strokes):
            if not s or 'points' not in s or len(s['points']) < 2:
                continue
            for i in range(1, len(s['points'])):
                A = s['points'][i - 1]
                B = s['points'][i]
                segVec = v_sub(B, A)
                segLen = v_len(segVec)
                if segLen == 0:
                    continue
                segDir = v_norm(segVec)
                epsilon = min(0.0001, segLen * 0.02)
                for m in range(1, kPerSegment + 1):
                    t = m / (kPerSegment + 1)
                    pt = v_add(A, v_scale(segVec, t))
                    _id = str(time.time()) + str(random.random())
                    a = v_add(pt, v_scale(segDir, -epsilon))
                    b = v_add(pt, v_scale(segDir, epsilon))
                    self.tags.append({'id': _id, 'number': nextNumber, 'a': a, 'b': b, 'strokeIndex': si})
                    nextNumber += 1

    # ---- Download ricochets ----
    def download_ricochets(self):
        seq = self._get_ricochet_sequence_for_angle(self.laser_angle_deg)
        if not seq:
            if not messagebox.askyesno('Не найдено', 'Не найдено рикошетов по помеченным отрезкам. Скачать пустой файл?'):
                return
        content = '\n'.join(seq)
        fn = filedialog.asksaveasfilename(defaultextension='.txt', filetypes=[('TXT', '*.txt')])
        if not fn:
            return
        with open(fn, 'w', encoding='utf-8') as f:
            f.write(content)
        messagebox.showinfo('Сохранено', 'Файл сохранён')

    # ---- Search ricochet file ----
    def _normalize_num_str(self, v):
        try:
            f = float(v)
            if abs(f - int(f)) < 1e-9:
                return str(int(f))
            return str(f)
        except:
            return str(v).strip()

    def _get_ricochet_sequence_for_angle(self, angle_deg):
        origin = {'x': 0, 'z': 0}
        angle = math.radians(angle_deg)
        dir_vec = {'x': math.cos(angle), 'z': math.sin(angle)}
        maxB = None if self.laser_unlimited else int(self.laser_max_bounces)
        cast = self.cast_laser(origin, dir_vec, float(self.laser_length), maxB) if self.laser_reflect else {'segments': [{'a': origin, 'b': v_add(origin, v_scale(dir_vec, self.laser_length))}], 'hits': []}
        numbers = []
        for hit in cast['hits']:
            if hit.get('strokeIndex') is None or not self.tags:
                continue
            for t in self.tags:
                if t.get('strokeIndex') != hit.get('strokeIndex'):
                    continue
                if self.point_on_segment(hit['point'], t['a'], t['b'], 1e-4):
                    numbers.append(self._normalize_num_str(t['number']))
                    break
        return numbers

    def search_ricochet_file(self):
        if self._search_running:
            # остановка поиска
            self._search_running = False
            self.search_btn.config(text='Поиск рикошетов')
            return

        fn = filedialog.askopenfilename(filetypes=[('TXT', '*.txt'), ('All', '*.*')])
        if not fn:
            return
        try:
            with open(fn, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception:
            messagebox.showerror('Ошибка', 'Не могу прочитать файл')
            return

        tokens = re.findall(r'[-+]?\d*\.?\d+', content)
        if not tokens:
            messagebox.showerror('Ошибка', 'В файле не найдено чисел')
            return
        target = [self._normalize_num_str(t) for t in tokens]
        self._search_target = target

        # init search
        self._search_running = True
        self._search_initial_angle = float(self.laser_angle_deg) % 360
        self._search_steps_done = 0

        try:
            step = simpledialog.askfloat('Шаг поиска (градусы)', 'Введите шаг вращения в градусах (меньше=медленнее, более точнее):', initialvalue=self._search_step_deg, minvalue=0.01, maxvalue=90.0)
            if step is not None:
                self._search_step_deg = float(step)
        except:
            pass

        self.search_btn.config(text='Отменить поиск')
        self._search_step()

    def _search_step(self):
        if not self._search_running:
            return
        step = self._search_step_deg
        steps_done = self._search_steps_done
        angle = (self._search_initial_angle + steps_done * step) % 360
        self.laser_angle_deg = angle
        try:
            self.rotate_scale.set(angle)
        except:
            pass
        self.render()

        seq = self._get_ricochet_sequence_for_angle(angle)
        if seq == self._search_target:
            self._search_running = False
            self.search_btn.config(text='Поиск рикошетов')
            messagebox.showinfo('Найдено', f'Комбинация найдена при угле {angle:.3f}°')
            return

        self._search_steps_done += 1
        if (self._search_steps_done * step) >= 360 - 1e-9:
            self._search_running = False
            self.search_btn.config(text='Поиск рикошетов')
            messagebox.showinfo('Не найдено', 'Комбинация не найдена за 360° оборот.')
            return

        self.root.after(10, self._search_step)

    # ---- ricochet window ----
    def toggle_show_ricochets(self):
        if self.ricochet_window:
            self._close_ricochet_window()
        else:
            self._open_ricochet_window()

    def _open_ricochet_window(self):
        if self.ricochet_window:
            return
        w = tk.Toplevel(self.root)
        w.title('Рикошеты (в реальном времени)')
        w.geometry('520x110')
        w.transient(self.root)

        entry = ttk.Entry(w, textvariable=self.ricochet_var, font=('Arial', 12))
        entry.pack(fill='x', expand=True, padx=8, pady=(8, 4))
        entry.state(['readonly'])

        bottom = ttk.Frame(w)
        bottom.pack(fill='x', padx=8, pady=(0, 8))
        ttk.Label(bottom, text='Рикошетов:').pack(side='left', padx=(0, 6))
        count_lbl = ttk.Label(bottom, textvariable=self.ricochet_count_var)
        count_lbl.pack(side='left')

        def _copy_to_clipboard():
            txt = self.ricochet_var.get() or ''
            try:
                w.clipboard_clear()
                w.clipboard_append(txt)
            except Exception:
                pass

        ttk.Button(bottom, text='Копировать', command=_copy_to_clipboard).pack(side='right')

        def _select_all(event=None):
            try:
                entry.selection_range(0, 'end')
                return 'break'
            except Exception:
                return None

        entry.bind('<Control-a>', _select_all)
        entry.bind('<Control-A>', _select_all)
        entry.bind('<FocusIn>', lambda e: w.after(1, _select_all))

        def on_close():
            self._close_ricochet_window()
        w.protocol("WM_DELETE_WINDOW", on_close)

        self.ricochet_window = w
        self.show_hits_btn.config(text='Скрыть рикошеты')

        seq = self._get_ricochet_sequence_for_angle(self.laser_angle_deg)
        self.ricochet_var.set(' '.join(seq))
        self.ricochet_count_var.set(str(len(seq)))

        self.render()

    def _close_ricochet_window(self):
        if not self.ricochet_window:
            return
        try:
            self.ricochet_window.destroy()
        except:
            pass
        self.ricochet_window = None
        self.ricochet_var.set('')
        self.ricochet_count_var.set('0')
        self.show_hits_btn.config(text='Показать рикошеты')

    # ---- Helper small wrappers ----
    def goto_cam(self):
        try:
            self.camX = float(self.x_entry.get())
            self.camZ = float(self.z_entry.get())
            self.render()
        except:
            pass

    def apply_partial_params(self):
        # читаем значения из полей и применяем (без включения/выключения)
        try:
            cnt = int(float(self.partial_count_entry.get()))
            if cnt < 1:
                raise ValueError()
            self.partial_load_per_interval = cnt
        except Exception:
            messagebox.showerror('Ошибка', 'Введите корректное количество рикошетов за шаг (целое >=1).')
            return

        try:
            iv = float(self.partial_interval_entry.get())
            if iv <= 0:
                raise ValueError()
            self.partial_load_interval = iv
        except Exception:
            messagebox.showerror('Ошибка', 'Введите корректный интервал в секундах (>0).')
            return

    # если сейчас прогрузка активна — перезапускаем с новыми параметрами
        if self.partial_load_enabled:
            self.start_partial_load()

    def toggle_partial_load(self):
        self.partial_load_enabled = not self.partial_load_enabled
        self.partial_btn.config(text=f"Прогружать частично: {'Вкл' if self.partial_load_enabled else 'Выкл'}")
        if self.partial_load_enabled:
        # стартуем анимацию/пошаговую проливку
            self.start_partial_load()
        else:
        # останавливаем и очищаем кэш
            self.stop_partial_load()
            self.render()

    def start_partial_load(self):
        # отменяем предыдущую задачу, если есть
        if self._partial_task_id:
            try:
                self.root.after_cancel(self._partial_task_id)
            except Exception:
                pass
            self._partial_task_id = None

        # пересчитываем трассу для текущих параметров
        origin = {'x': 0.0, 'z': 0.0}
        angle = math.radians(self.laser_angle_deg)
        dir = {'x': math.cos(angle), 'z': math.sin(angle)}
        maxB = None if self.laser_unlimited else int(self.laser_max_bounces) - 1

        cast = self.cast_laser(origin, dir, float(self.laser_length), maxB) if self.laser_reflect else {'segments': [{'a': origin, 'b': v_add(origin, v_scale(dir, self.laser_length))}], 'hits': []}
        self._partial_cast_cache = cast

        # сбрасываем видимые счётчики: показываем первый сегмент по умолчанию
        self._partial_visible_segments = 1 if cast.get('segments') else 0
        self._partial_visible_hits = 0

        # запускаем шаговый таймер
        self._partial_step()

    def stop_partial_load(self):
        self._partial_cast_cache = None
        self._partial_visible_hits = 0
        self._partial_visible_segments = 0
        if self._partial_task_id:
            try:
                self.root.after_cancel(self._partial_task_id)
            except Exception:
                pass
        self._partial_task_id = None

    def _partial_step(self):
        # раскрываем следующую порцию (partial_load_per_interval) рикошетов и соответствующие сегменты
        if not self.partial_load_enabled:
            self._partial_task_id = None
            return

        if not self._partial_cast_cache:
            # если кэша нет — пересчитать и перезапустить
            self.start_partial_load()
            return

        cast = self._partial_cast_cache
        hits = cast.get('hits', [])
        segments = cast.get('segments', [])

        # раскрываем N hit-ов
        remaining_to_reveal = self.partial_load_per_interval
        while remaining_to_reveal > 0 and self._partial_visible_hits < len(hits):
            self._partial_visible_hits += 1
            remaining_to_reveal -= 1

        # после раскрытия определяем, сколько сегментов показывать:
        # минимально — visible_hits + 1 (чтобы видно было следующий сегмент после попадания)
        self._partial_visible_segments = min(len(segments), self._partial_visible_hits + 1) if len(segments) > 0 else 0

        # если нет хиттов — всё равно показываем первый сегмент, если он есть
        if len(hits) == 0 and len(segments) > 0:
            self._partial_visible_segments = 1

        self.render()

        # если всё показано — не планируем дальше
        if self._partial_visible_hits >= len(hits) and self._partial_visible_segments >= len(segments):
            self._partial_task_id = None
            return

        # иначе — планируем следующий шаг
        try:
            ms = int(self.partial_load_interval * 1000)
            self._partial_task_id = self.root.after(ms, self._partial_step)
        except Exception:
            self._partial_task_id = None


# ---- Main ----
if __name__ == '__main__':
    try:
        root = tk.Tk()
    except NameError:
        from tkinter import Tk as _Tk
        root = _Tk()
    try:
        app = LaserApp(root)
    except Exception as e:
        print('Ошибка при создании приложения:', e)
        raise

    if hasattr(app, 'on_close') and callable(app.on_close):
        root.protocol("WM_DELETE_WINDOW", app.on_close)
    else:
        root.protocol("WM_DELETE_WINDOW", root.destroy)
    try:
        root.mainloop()
    except KeyboardInterrupt:
        try:
            root.destroy()
        except Exception:
            pass
    sys.exit(0)
