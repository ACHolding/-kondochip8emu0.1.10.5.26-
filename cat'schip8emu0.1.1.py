#!/usr/bin/env python3
# =============================================================================
#  Cat's CHIP-8 Emu 0.1.1  --  program.py
#  Single-file CHIP-8 emulator. Desktop shell mirrors mGBA's Qt frontend:
#  native menu bar (File / Emulation / Audio/Video / Tools), black game
#  client, status bar, right-click context menu, dynamic window title.
#
#  FILES = ON    -> File > Load ROM... opens a device file picker (mGBA-style).
#                   Built-in demos remain under File > Load built-in ROM.
#  AUDIO = ON    -> built-in square-wave audio engine (pygame / winsound / bell)
#  60 FPS locked frame loop, 60 Hz timers, configurable CPU speed.
# =============================================================================
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import time
import random
import struct
import wave
import io
import os
import sys

APP_NAME = "Cat's CHIP-8 Emu"
VERSION = "0.1.1"
FILES = True           # FILES = ON  (Load ROM from device)
AUDIO_ENABLED = True   # audio engine = enabled
TARGET_FPS = 60
WINDOW_W = 600
WINDOW_H = 400

# mGBA-like chrome: native system UI + black display surface
DISPLAY_BG = "#000000"
STATUS_BG = "#f0f0f0"
STATUS_FG = "#202020"

PALETTES = {
    "mGBA Blue": ("#02081c", "#7cc4ff"),
    "Phosphor Green": ("#001a00", "#4cff6a"),
    "Paper White": ("#101010", "#f2f2f2"),
    "Amber": ("#1a0f00", "#ffb000"),
}

FONT = bytes([
    0xF0, 0x90, 0x90, 0x90, 0xF0, 0x20, 0x60, 0x20, 0x20, 0x70,
    0xF0, 0x10, 0xF0, 0x80, 0xF0, 0xF0, 0x10, 0xF0, 0x10, 0xF0,
    0x90, 0x90, 0xF0, 0x10, 0x10, 0xF0, 0x80, 0xF0, 0x10, 0xF0,
    0xF0, 0x80, 0xF0, 0x90, 0xF0, 0xF0, 0x10, 0x20, 0x40, 0x40,
    0xF0, 0x90, 0xF0, 0x90, 0xF0, 0xF0, 0x90, 0xF0, 0x10, 0xF0,
    0xF0, 0x90, 0xF0, 0x90, 0x90, 0xE0, 0x90, 0xE0, 0x90, 0xE0,
    0xF0, 0x80, 0x80, 0x80, 0xF0, 0xE0, 0x90, 0x90, 0x90, 0xE0,
    0xF0, 0x80, 0xF0, 0x80, 0xF0, 0xF0, 0x80, 0xF0, 0x80, 0x80,
])
FONT_BASE = 0x50

KEYMAP = {
    "1": 0x1, "2": 0x2, "3": 0x3, "4": 0xC,
    "q": 0x4, "w": 0x5, "e": 0x6, "r": 0xD,
    "a": 0x7, "s": 0x8, "d": 0x9, "f": 0xE,
    "z": 0xA, "x": 0x0, "c": 0xB, "v": 0xF,
}


def words(*ws, tail=b""):
    return b"".join(struct.pack(">H", w) for w in ws) + tail


# ---- embedded ROMs (FILES = OFF) -------------------------------------------
BUILTIN_ROMS = {
    "Cat Splash": words(
        0xA210, 0x6008, 0x610C, 0xD018, 0x7010, 0x3048, 0x1206, 0x120E,
        tail=bytes([0x81, 0xC3, 0xFF, 0xA5, 0xFF, 0xDB, 0x7E, 0x3C])),
    "Key Dot (2/4/6/8 to move)": words(
        0x6020, 0x610F, 0xA226, 0xD014, 0xD014, 0x6202, 0xE2A1, 0x71FF,
        0x6208, 0xE2A1, 0x7101, 0x6204, 0xE2A1, 0x70FF, 0x6206, 0xE2A1,
        0x7001, 0xD014, 0x1208,
        tail=bytes([0xF0, 0xF0, 0xF0, 0xF0])),
    "BCD Counter": words(
        0x6600, 0x00E0, 0xA300, 0xF633, 0xF265, 0x630A, 0x640C, 0xF029,
        0xD345, 0x7306, 0xF129, 0xD345, 0x7306, 0xF229, 0xD345, 0x6A1E,
        0xFA15, 0xFB07, 0x3B00, 0x1222, 0x7601, 0x1202),
    "Audio Test (beep loop)": words(
        0x6A1E, 0xFA18, 0xFA15, 0xFB07, 0x3B00, 0x1206, 0x6A3C, 0xFA15,
        0xFB07, 0x3B00, 0x1210, 0x1200),
}


# =============================================================================
#  CPU
# =============================================================================
class Chip8:
    W, H = 64, 32

    def __init__(self):
        self.q_shift_vy = False    # 8xy6/8xyE shift Vy instead of Vx
        self.q_ldst_inc = False    # Fx55/Fx65 increment I
        self.q_clip = True         # clip sprites at screen edge
        self.q_vf_reset = False    # 8xy1/2/3 reset VF
        self.q_jump_vx = False     # Bnnn -> Bxnn
        self.rom = b""
        self.reset()

    def reset(self):
        self.mem = bytearray(4096)
        self.mem[FONT_BASE:FONT_BASE + len(FONT)] = FONT
        if self.rom:
            self.mem[0x200:0x200 + len(self.rom)] = self.rom
        self.V = [0] * 16
        self.I = 0
        self.pc = 0x200
        self.sp = 0
        self.stack = [0] * 16
        self.dt = 0
        self.st = 0
        self.gfx = bytearray(self.W * self.H)
        self.keys = [0] * 16
        self.wait_reg = None
        self.halted = False
        self.halt_reason = ""
        self.last_op = 0

    def load(self, data):
        self.rom = bytes(data[:4096 - 0x200])
        self.reset()

    def tick_timers(self):
        if self.dt:
            self.dt -= 1
        if self.st:
            self.st -= 1

    def _halt(self, why):
        self.halted = True
        self.halt_reason = why

    def step(self):
        if self.wait_reg is not None or self.halted:
            return
        pc = self.pc
        mem = self.mem
        op = (mem[pc] << 8) | mem[(pc + 1) & 0xFFF]
        self.last_op = op
        self.pc = (pc + 2) & 0xFFF
        n = op >> 12
        x = (op >> 8) & 0xF
        y = (op >> 4) & 0xF
        kk = op & 0xFF
        nnn = op & 0xFFF
        nib = op & 0xF
        V = self.V

        if n == 0x0:
            if op == 0x00E0:
                self.gfx = bytearray(self.W * self.H)
            elif op == 0x00EE:
                if self.sp == 0:
                    self._halt("Stack underflow @%03X" % pc)
                else:
                    self.sp -= 1
                    self.pc = self.stack[self.sp]
        elif n == 0x1:
            self.pc = nnn
        elif n == 0x2:
            if self.sp >= 16:
                self._halt("Stack overflow @%03X" % pc)
            else:
                self.stack[self.sp] = self.pc
                self.sp += 1
                self.pc = nnn
        elif n == 0x3:
            if V[x] == kk:
                self.pc = (self.pc + 2) & 0xFFF
        elif n == 0x4:
            if V[x] != kk:
                self.pc = (self.pc + 2) & 0xFFF
        elif n == 0x5:
            if nib == 0 and V[x] == V[y]:
                self.pc = (self.pc + 2) & 0xFFF
        elif n == 0x6:
            V[x] = kk
        elif n == 0x7:
            V[x] = (V[x] + kk) & 0xFF
        elif n == 0x8:
            if nib == 0x0:
                V[x] = V[y]
            elif nib == 0x1:
                V[x] |= V[y]
                if self.q_vf_reset:
                    V[0xF] = 0
            elif nib == 0x2:
                V[x] &= V[y]
                if self.q_vf_reset:
                    V[0xF] = 0
            elif nib == 0x3:
                V[x] ^= V[y]
                if self.q_vf_reset:
                    V[0xF] = 0
            elif nib == 0x4:
                s = V[x] + V[y]
                V[x] = s & 0xFF
                V[0xF] = 1 if s > 0xFF else 0
            elif nib == 0x5:
                f = 1 if V[x] >= V[y] else 0
                V[x] = (V[x] - V[y]) & 0xFF
                V[0xF] = f
            elif nib == 0x6:
                src = V[y] if self.q_shift_vy else V[x]
                V[x] = src >> 1
                V[0xF] = src & 1
            elif nib == 0x7:
                f = 1 if V[y] >= V[x] else 0
                V[x] = (V[y] - V[x]) & 0xFF
                V[0xF] = f
            elif nib == 0xE:
                src = V[y] if self.q_shift_vy else V[x]
                V[x] = (src << 1) & 0xFF
                V[0xF] = (src >> 7) & 1
        elif n == 0x9:
            if nib == 0 and V[x] != V[y]:
                self.pc = (self.pc + 2) & 0xFFF
        elif n == 0xA:
            self.I = nnn
        elif n == 0xB:
            self.pc = (nnn + (V[x] if self.q_jump_vx else V[0])) & 0xFFF
        elif n == 0xC:
            V[x] = random.getrandbits(8) & kk
        elif n == 0xD:
            self._draw(V[x], V[y], nib)
        elif n == 0xE:
            k = V[x] & 0xF
            if kk == 0x9E:
                if self.keys[k]:
                    self.pc = (self.pc + 2) & 0xFFF
            elif kk == 0xA1:
                if not self.keys[k]:
                    self.pc = (self.pc + 2) & 0xFFF
        elif n == 0xF:
            if kk == 0x07:
                V[x] = self.dt
            elif kk == 0x0A:
                self.wait_reg = x
            elif kk == 0x15:
                self.dt = V[x]
            elif kk == 0x18:
                self.st = V[x]
            elif kk == 0x1E:
                self.I = (self.I + V[x]) & 0xFFF
            elif kk == 0x29:
                self.I = FONT_BASE + (V[x] & 0xF) * 5
            elif kk == 0x33:
                v = V[x]
                i = self.I
                mem[i & 0xFFF] = v // 100
                mem[(i + 1) & 0xFFF] = (v // 10) % 10
                mem[(i + 2) & 0xFFF] = v % 10
            elif kk == 0x55:
                for r in range(x + 1):
                    mem[(self.I + r) & 0xFFF] = V[r]
                if self.q_ldst_inc:
                    self.I = (self.I + x + 1) & 0xFFF
            elif kk == 0x65:
                for r in range(x + 1):
                    V[r] = mem[(self.I + r) & 0xFFF]
                if self.q_ldst_inc:
                    self.I = (self.I + x + 1) & 0xFFF

    def _draw(self, px, py, h):
        W, H = self.W, self.H
        gfx = self.gfx
        mem = self.mem
        vx = px % W
        vy = py % H
        collided = 0
        clip = self.q_clip
        for r in range(h):
            yy = vy + r
            if yy >= H:
                if clip:
                    break
                yy %= H
            row = mem[(self.I + r) & 0xFFF]
            if not row:
                continue
            for c in range(8):
                if row & (0x80 >> c):
                    xx = vx + c
                    if xx >= W:
                        if clip:
                            break
                        xx %= W
                    idx = yy * W + xx
                    if gfx[idx]:
                        collided = 1
                    gfx[idx] ^= 1
        self.V[0xF] = collided

    # ---- savestates (in-memory; no files) ----
    def snapshot(self):
        return (bytes(self.mem), list(self.V), self.I, self.pc, self.sp,
                list(self.stack), self.dt, self.st, bytes(self.gfx),
                self.wait_reg, self.rom)

    def restore(self, s):
        (mem, V, I, pc, sp, stack, dt, st, gfx, wr, rom) = s
        self.mem = bytearray(mem)
        self.V = list(V)
        self.I, self.pc, self.sp = I, pc, sp
        self.stack = list(stack)
        self.dt, self.st = dt, st
        self.gfx = bytearray(gfx)
        self.wait_reg = wr
        self.rom = rom
        self.halted = False
        self.keys = [0] * 16


# =============================================================================
#  Audio engine (square-wave beeper)
# =============================================================================
class AudioEngine:
    RATE = 22050

    def __init__(self, root, enabled=True):
        self.root = root
        self.enabled = enabled
        self.muted = False
        self.volume = 0.25
        self.freq = 440
        self.playing = False
        self.backend = "none"
        self.sound = None
        self.wav = b""
        self._bell_job = None
        self._init_backend()
        self._rebuild()

    def _init_backend(self):
        try:
            os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
            import pygame
            pygame.mixer.pre_init(self.RATE, -16, 1, 512)
            pygame.mixer.init()
            self._pg = pygame
            self.backend = "pygame"
            return
        except Exception:
            pass
        try:
            import winsound
            self._ws = winsound
            self.backend = "winsound"
            return
        except Exception:
            pass
        self.backend = "bell"

    def _make_wav(self):
        period = self.RATE / float(self.freq)
        cycles = max(1, int(round(self.freq * 0.25)))
        n = int(round(period * cycles))
        amp = int(32767 * max(0.0, min(1.0, self.volume)))
        pcm = bytearray()
        for i in range(n):
            pcm += struct.pack("<h", amp if (i % period) < period / 2 else -amp)
        buf = io.BytesIO()
        with wave.open(buf, "wb") as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(self.RATE)
            w.writeframes(bytes(pcm))
        return buf.getvalue()

    def _rebuild(self):
        was = self.playing
        self.stop()
        self.wav = self._make_wav()
        if self.backend == "pygame":
            try:
                self.sound = self._pg.mixer.Sound(file=io.BytesIO(self.wav))
            except Exception:
                self.backend = "bell"
        if was:
            self.start()

    def set_volume(self, v):
        self.volume = v
        self._rebuild()

    def set_freq(self, f):
        self.freq = f
        self._rebuild()

    def start(self):
        if self.playing or not self.enabled or self.muted:
            return
        self.playing = True
        try:
            if self.backend == "pygame" and self.sound:
                self.sound.play(loops=-1)
            elif self.backend == "winsound":
                ws = self._ws
                ws.PlaySound(self.wav, ws.SND_MEMORY | ws.SND_ASYNC | ws.SND_LOOP)
            else:
                self._bell()
        except Exception:
            self.playing = False

    def _bell(self):
        if self.playing:
            try:
                self.root.bell()
            except Exception:
                pass
            self._bell_job = self.root.after(250, self._bell)

    def stop(self):
        if not self.playing:
            return
        self.playing = False
        try:
            if self.backend == "pygame" and self.sound:
                self.sound.stop()
            elif self.backend == "winsound":
                self._ws.PlaySound(None, self._ws.SND_PURGE)
        except Exception:
            pass
        if self._bell_job:
            try:
                self.root.after_cancel(self._bell_job)
            except Exception:
                pass
            self._bell_job = None

    def update(self, want_sound):
        if want_sound and self.enabled and not self.muted:
            self.start()
        else:
            self.stop()


# =============================================================================
#  Application / GUI  (mGBA Qt frontend layout)
# =============================================================================
class App:
    def __init__(self, root):
        self.root = root
        self.cpu = Chip8()
        self.audio = AudioEngine(root, AUDIO_ENABLED)

        self.running = True
        self.cpu_hz = 700
        self.cycle_acc = 0.0
        self.scale = 8          # 512x256 fits inside the 600x400 window
        self.palette = "mGBA Blue"
        self.blend = True
        self.show_fps = True
        self.show_status = True
        self.rom_name = "(none)"
        self.slots = {}
        self._prev = bytes(64 * 32)
        self._shown = None
        self._scaled = None
        self._frames = 0
        self._instr = 0
        self._stat_t = time.perf_counter()
        self._fps = 0.0
        self._ips = 0
        self.dbg = None
        self.keypad = None
        self._dbg_tick = 0
        self._menubar = None
        self._context = None
        self.menu_hidden = False
        self._rom_dir = os.path.expanduser("~")

        root.configure(bg=DISPLAY_BG)
        root.resizable(False, False)

        self._build_menubar()
        self._build_screen()
        self._build_status()
        self._update_title()
        self._place_window()

        root.bind("<KeyPress>", self._key_down)
        root.bind("<KeyRelease>", self._key_up)
        root.protocol("WM_DELETE_WINDOW", self.quit)

        # mGBA starts with no game attached — user picks Load ROM...
        if FILES:
            self.shutdown()
        else:
            self.load_builtin("Cat Splash")
        self.next_t = time.perf_counter()
        self._frame()

    def _place_window(self):
        """Fixed 600x400 window, centered on the primary screen."""
        self.root.update_idletasks()
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = max(0, (sw - WINDOW_W) // 2)
        y = max(0, (sh - WINDOW_H) // 2)
        self.root.geometry("%dx%d+%d+%d" % (WINDOW_W, WINDOW_H, x, y))

    def _update_title(self):
        # mGBA: "mGBA - Title - version" / with fps when Show FPS is on
        if self.rom_name and self.rom_name != "(none)":
            if self.show_fps and self._fps > 0:
                self.root.title("%s - %s (%.1f fps) - %s" % (
                    APP_NAME, self.rom_name, self._fps, VERSION))
            else:
                self.root.title("%s - %s - %s" % (APP_NAME, self.rom_name, VERSION))
        else:
            self.root.title("%s - %s" % (APP_NAME, VERSION))

    # ---------------------------------------------------------------- widgets
    def _menu(self, parent):
        return tk.Menu(parent, tearoff=0)

    def _build_menubar(self):
        # Native menubar like mGBA's QMenuBar — File / Emulation / Audio/Video / Tools
        menubar = self._menu(self.root)
        self._menubar = menubar

        # ---- File  (mGBA: Load ROM... is the primary entry)
        m = self._menu(menubar)
        m.add_command(label="Load ROM...", accelerator="Ctrl+O",
                      command=self.open_rom_file,
                      state="normal" if FILES else "disabled")
        sub = self._menu(m)
        for name in BUILTIN_ROMS:
            sub.add_command(label=name, command=lambda n=name: self.load_builtin(n))
        m.add_cascade(label="Load built-in ROM", menu=sub)
        m.add_command(label="Paste hex ROM...", command=self.paste_hex)
        m.add_separator()
        ql = self._menu(m)
        qs = self._menu(m)
        for i in range(1, 6):
            ql.add_command(label="State %d" % i, accelerator="F%d" % i,
                           command=lambda i=i: self.load_state(i))
            qs.add_command(label="State %d" % i, accelerator="Shift+F%d" % i,
                           command=lambda i=i: self.save_state(i))
            self.root.bind("<F%d>" % i, lambda e, i=i: self.load_state(i))
            self.root.bind("<Shift-F%d>" % i, lambda e, i=i: self.save_state(i))
        m.add_cascade(label="Quick load", menu=ql)
        m.add_cascade(label="Quick save", menu=qs)
        m.add_separator()
        m.add_command(label="About...", command=self.about)
        m.add_separator()
        m.add_command(label="Exit", accelerator="Ctrl+Q", command=self.quit)
        menubar.add_cascade(label="File", menu=m)

        # ---- Emulation
        m = self._menu(menubar)
        m.add_command(label="Reset", accelerator="Ctrl+R", command=self.reset)
        m.add_command(label="Shutdown", command=self.shutdown)
        m.add_separator()
        self.v_pause = tk.BooleanVar(value=False)
        m.add_checkbutton(label="Pause", accelerator="Ctrl+P",
                          variable=self.v_pause, command=self.toggle_pause)
        m.add_command(label="Next frame", accelerator="Ctrl+N",
                      command=self.step_frame)
        m.add_command(label="Step instruction", accelerator="N",
                      command=self.step_once)
        m.add_separator()
        self.v_ff = tk.BooleanVar(value=False)
        m.add_checkbutton(label="Fast forward", variable=self.v_ff,
                          command=self._toggle_ff)
        sp = self._menu(m)
        self.v_hz = tk.IntVar(value=self.cpu_hz)
        for hz in (300, 500, 700, 1000, 2000, 5000, 10000):
            sp.add_radiobutton(label="%d Hz" % hz, variable=self.v_hz, value=hz,
                               command=lambda h=hz: self.set_hz(h))
        m.add_cascade(label="CPU speed", menu=sp)
        q = self._menu(m)
        self.v_q = {}
        for key, label in (("q_shift_vy", "Shift uses Vy"),
                           ("q_ldst_inc", "Fx55/Fx65 increment I"),
                           ("q_clip", "Clip sprites at edges"),
                           ("q_vf_reset", "Logic ops reset VF"),
                           ("q_jump_vx", "Bnnn uses Vx (SCHIP)")):
            v = tk.BooleanVar(value=getattr(self.cpu, key))
            self.v_q[key] = v
            q.add_checkbutton(label=label, variable=v,
                              command=lambda k=key: setattr(self.cpu, k, self.v_q[k].get()))
        m.add_cascade(label="Quirks", menu=q)
        menubar.add_cascade(label="Emulation", menu=m)

        # ---- Audio/Video
        m = self._menu(menubar)
        sc = self._menu(m)
        self.v_scale = tk.IntVar(value=self.scale)
        for s in (1, 2, 3, 4, 5, 6, 7, 8, 9):
            sc.add_radiobutton(label="%d×" % s, variable=self.v_scale, value=s,
                               command=lambda s=s: self.set_scale(s))
        m.add_cascade(label="Frame size", menu=sc)
        m.add_separator()
        self.v_audio = tk.BooleanVar(value=self.audio.enabled)
        m.add_checkbutton(label="Audio enabled", variable=self.v_audio,
                          command=self.toggle_audio)
        self.v_mute = tk.BooleanVar(value=False)
        m.add_checkbutton(label="Mute", accelerator="Ctrl+M", variable=self.v_mute,
                          command=self.toggle_mute)
        vol = self._menu(m)
        self.v_vol = tk.IntVar(value=25)
        for p in (10, 25, 50, 75, 100):
            vol.add_radiobutton(label="%d%%" % p, variable=self.v_vol, value=p,
                                command=lambda p=p: self.audio.set_volume(p / 100.0))
        m.add_cascade(label="Volume", menu=vol)
        tone = self._menu(m)
        self.v_tone = tk.IntVar(value=self.audio.freq)
        for f in (220, 330, 440, 660, 880):
            tone.add_radiobutton(label="%d Hz" % f, variable=self.v_tone, value=f,
                                 command=lambda f=f: self.audio.set_freq(f))
        m.add_cascade(label="Beep tone", menu=tone)
        m.add_separator()
        pal = self._menu(m)
        self.v_pal = tk.StringVar(value=self.palette)
        for name in PALETTES:
            pal.add_radiobutton(label=name, variable=self.v_pal, value=name,
                                command=lambda n=name: self.set_palette(n))
        m.add_cascade(label="Palette", menu=pal)
        self.v_blend = tk.BooleanVar(value=self.blend)
        m.add_checkbutton(label="Interframe blending", variable=self.v_blend,
                          command=self.toggle_blend)
        self.v_fps = tk.BooleanVar(value=self.show_fps)
        m.add_checkbutton(label="Show FPS", variable=self.v_fps,
                          command=self.toggle_fps)
        self.v_status = tk.BooleanVar(value=True)
        m.add_checkbutton(label="Show status bar", variable=self.v_status,
                          command=self.toggle_status)
        m.add_separator()
        m.add_command(label="Hide menu bar", accelerator="Esc",
                      command=self.toggle_menu)
        menubar.add_cascade(label="Audio/Video", menu=m)

        # ---- Tools
        m = self._menu(menubar)
        m.add_command(label="On-screen keypad...", command=self.open_keypad)
        m.add_command(label="Debugger...", command=self.open_debugger)
        m.add_command(label="Keyboard map...", command=self.show_keys)
        menubar.add_cascade(label="Tools", menu=m)

        self.root.config(menu=menubar)
        self._build_context_menu()

        self.root.bind("<Control-o>", lambda e: self.open_rom_file())
        self.root.bind("<Control-r>", lambda e: self.reset())
        self.root.bind("<Control-q>", lambda e: self.quit())
        self.root.bind("<Control-m>", lambda e: self._hotkey_mute())
        self.root.bind("<Control-p>", lambda e: self._hotkey_pause())
        self.root.bind("<Control-n>", lambda e: self.step_frame())
        self.root.bind("<p>", lambda e: self._hotkey_pause())
        self.root.bind("<n>", lambda e: self.step_once())
        self.root.bind("<m>", lambda e: self.step_frame())
        self.root.bind("<Escape>", lambda e: self.toggle_menu())

    def _build_context_menu(self):
        ctx = self._menu(self.root)
        ctx.add_command(label="Load ROM...", command=self.open_rom_file,
                        state="normal" if FILES else "disabled")
        sub = self._menu(ctx)
        for name in BUILTIN_ROMS:
            sub.add_command(label=name, command=lambda n=name: self.load_builtin(n))
        ctx.add_cascade(label="Load built-in ROM", menu=sub)
        ctx.add_separator()
        ctx.add_command(label="Reset", command=self.reset)
        ctx.add_checkbutton(label="Pause", variable=self.v_pause,
                            command=self.toggle_pause)
        ctx.add_command(label="Next frame", command=self.step_frame)
        ctx.add_separator()
        ctx.add_command(label="Debugger...", command=self.open_debugger)
        ctx.add_command(label="Hide menu bar", command=self.toggle_menu)
        self._context = ctx

    def _build_screen(self):
        # mGBA central widget: black client, integer-scaled display centered
        self.screen_frame = tk.Frame(self.root, bg=DISPLAY_BG, bd=0,
                                     highlightthickness=0)
        self.screen_frame.pack(fill="both", expand=True)
        w, h = 64 * self.scale, 32 * self.scale
        self.canvas = tk.Canvas(self.screen_frame, width=w, height=h,
                                bg=PALETTES[self.palette][0],
                                highlightthickness=0, bd=0)
        self.canvas.place(relx=0.5, rely=0.5, anchor="center")
        self.canvas.bind("<Button-3>", self._popup_context)
        self.canvas.bind("<Control-Button-1>", self._popup_context)
        self.screen_frame.bind("<Button-3>", self._popup_context)
        self.img = tk.PhotoImage(width=64, height=32)
        self.cimg = self.canvas.create_image(0, 0, anchor="nw")
        # Idle logo label (mGBA shows branding when no game is attached)
        self.logo = tk.Label(
            self.screen_frame,
            text="%s\n%s" % (APP_NAME, VERSION),
            bg=DISPLAY_BG, fg="#7cc4ff",
            font=("Helvetica", 16), justify="center",
        )

    def _build_status(self):
        # Qt-style status bar under the display
        self.status = tk.Label(
            self.root, text="Ready", bg=STATUS_BG, fg=STATUS_FG, anchor="w",
            font=("Helvetica", 11), padx=8, pady=3,
            relief="sunken", bd=1,
        )
        self.status.pack(fill="x", side="bottom")

    def _popup_context(self, event):
        if self._context:
            try:
                self._context.tk_popup(event.x_root, event.y_root)
            finally:
                self._context.grab_release()

    def toggle_menu(self):
        if self.menu_hidden:
            self.root.config(menu=self._menubar)
            self.menu_hidden = False
        else:
            self.root.config(menu="")
            self.menu_hidden = True

    def toggle_status(self):
        self.show_status = self.v_status.get()
        if self.show_status:
            self.status.pack(fill="x", side="bottom")
        else:
            self.status.pack_forget()

    def shutdown(self):
        self.running = False
        self.v_pause.set(True)
        self.audio.stop()
        self.cpu.reset()
        self.cpu.rom = b""
        self.cpu.reset()
        self.rom_name = "(none)"
        self._force_redraw()
        self.canvas.place_forget()
        self.logo.place(relx=0.5, rely=0.5, anchor="center")
        self._update_title()
        self.status.config(text="No game loaded")

    def _toggle_ff(self):
        # Fast forward ≈ 4× CPU rate while checked
        if self.v_ff.get():
            self.cpu_hz = max(self.v_hz.get(), 700) * 4
        else:
            self.cpu_hz = self.v_hz.get()

    # ---------------------------------------------------------------- actions
    def _attach_display(self):
        try:
            self.logo.place_forget()
        except Exception:
            pass
        self.canvas.place(relx=0.5, rely=0.5, anchor="center")

    def load_builtin(self, name):
        self.cpu.load(BUILTIN_ROMS[name])
        self.rom_name = name
        self.running = True
        self.v_pause.set(False)
        self._attach_display()
        self._force_redraw()
        self._update_title()

    def open_rom_file(self):
        """mGBA-style Load ROM... — pick a file from the device."""
        if not FILES:
            messagebox.showinfo(
                APP_NAME,
                "FILES is OFF. Set FILES = True to load ROMs from disk.",
                parent=self.root,
            )
            return
        p = filedialog.askopenfilename(
            parent=self.root,
            title="Select ROM",
            initialdir=self._rom_dir,
            filetypes=(
                ("CHIP-8 ROMs", ("*.ch8", "*.c8", "*.rom", "*.bin")),
                ("All files", "*.*"),
            ),
        )
        if not p:
            return
        self._load_rom_path(p)

    def _load_rom_path(self, path):
        try:
            with open(path, "rb") as f:
                data = f.read()
        except OSError as exc:
            messagebox.showerror(APP_NAME, "Could not open ROM:\n%s" % exc,
                                 parent=self.root)
            return
        if not data:
            messagebox.showerror(APP_NAME, "ROM file is empty.", parent=self.root)
            return
        if len(data) > 4096 - 0x200:
            messagebox.showerror(
                APP_NAME,
                "ROM is too large for CHIP-8 memory (max %d bytes)."
                % (4096 - 0x200),
                parent=self.root,
            )
            return
        self._rom_dir = os.path.dirname(path) or self._rom_dir
        self.cpu.load(data)
        self.rom_name = os.path.basename(path)
        self.running = True
        self.v_pause.set(False)
        self.cycle_acc = 0.0
        self._attach_display()
        self._force_redraw()
        self._update_title()
        self.status.config(text="Loaded %s (%d bytes)" % (self.rom_name, len(data)))

    def paste_hex(self):
        win = tk.Toplevel(self.root)
        win.title("Paste hex ROM")
        win.transient(self.root)
        ttk.Label(win, text="Paste CHIP-8 bytes as hex (e.g. 6A1E FA18 ...):").pack(
            padx=8, pady=(8, 2), anchor="w")
        t = tk.Text(win, width=56, height=10, font=("Menlo", 11))
        t.pack(padx=8, pady=4)

        def go():
            raw = "".join(ch for ch in t.get("1.0", "end") if ch in "0123456789abcdefABCDEF")
            if len(raw) % 2:
                raw += "0"
            if not raw:
                return
            self.cpu.load(bytes.fromhex(raw))
            self.rom_name = "(pasted hex)"
            self.running = True
            self.v_pause.set(False)
            self._attach_display()
            self._force_redraw()
            self._update_title()
            win.destroy()

        ttk.Button(win, text="Load", command=go).pack(pady=(2, 8))

    def reset(self):
        if not self.cpu.rom:
            return
        self.cpu.reset()
        self.cycle_acc = 0.0
        self.running = True
        self.v_pause.set(False)
        self._attach_display()
        self._force_redraw()

    def toggle_pause(self):
        self.running = not self.v_pause.get()
        if not self.running:
            self.audio.stop()

    def _hotkey_pause(self):
        self.v_pause.set(not self.v_pause.get())
        self.toggle_pause()

    def step_once(self):
        if not self.running:
            self.cpu.step()
            self.cpu.draw_flag = True

    def step_frame(self):
        if not self.running:
            for _ in range(max(1, int(self.cpu_hz / TARGET_FPS))):
                self.cpu.step()
            self.cpu.tick_timers()

    def set_hz(self, hz):
        self.v_hz.set(hz)
        if self.v_ff.get():
            self.cpu_hz = hz * 4
        else:
            self.cpu_hz = hz

    def toggle_audio(self):
        self.audio.enabled = self.v_audio.get()
        if not self.audio.enabled:
            self.audio.stop()

    def toggle_mute(self):
        self.audio.muted = self.v_mute.get()
        if self.audio.muted:
            self.audio.stop()

    def _hotkey_mute(self):
        self.v_mute.set(not self.v_mute.get())
        self.toggle_mute()

    def set_scale(self, s):
        # Keep the outer window 600x400; only resize the integer-scaled display.
        self.scale = min(s, 9)
        self.v_scale.set(self.scale)
        self.canvas.config(width=64 * self.scale, height=32 * self.scale)
        if self.cpu.rom:
            self.canvas.place(relx=0.5, rely=0.5, anchor="center")
        self._force_redraw()
        self._place_window()

    def set_palette(self, name):
        self.palette = name
        self.canvas.config(bg=PALETTES[name][0])
        self._force_redraw()

    def toggle_blend(self):
        self.blend = self.v_blend.get()
        self._force_redraw()

    def toggle_fps(self):
        self.show_fps = self.v_fps.get()
        self._update_title()

    def save_state(self, i):
        self.slots[i] = self.cpu.snapshot()
        self.status.config(text="Saved state to slot %d" % i)

    def load_state(self, i):
        if i in self.slots:
            self.cpu.restore(self.slots[i])
            self._force_redraw()
            self.status.config(text="Loaded state from slot %d" % i)
        else:
            self.status.config(text="Slot %d is empty" % i)

    def _force_redraw(self):
        self._shown = None
        self._prev = bytes(64 * 32)

    # ---------------------------------------------------------------- windows
    def open_keypad(self):
        if self.keypad and self.keypad.winfo_exists():
            self.keypad.lift()
            return
        win = tk.Toplevel(self.root)
        win.title("Keypad")
        win.resizable(False, False)
        win.transient(self.root)
        self.keypad = win
        layout = [[0x1, 0x2, 0x3, 0xC], [0x4, 0x5, 0x6, 0xD],
                  [0x7, 0x8, 0x9, 0xE], [0xA, 0x0, 0xB, 0xF]]
        for r, row in enumerate(layout):
            for c, k in enumerate(row):
                b = ttk.Button(win, text="%X" % k, width=4)
                b.grid(row=r, column=c, padx=3, pady=3)
                b.bind("<ButtonPress-1>", lambda e, k=k: self._pad(k, 1))
                b.bind("<ButtonRelease-1>", lambda e, k=k: self._pad(k, 0))

    def _pad(self, k, down):
        self.cpu.keys[k] = down
        if down and self.cpu.wait_reg is not None:
            self.cpu.V[self.cpu.wait_reg] = k
            self.cpu.wait_reg = None

    def open_debugger(self):
        if self.dbg and self.dbg[0].winfo_exists():
            self.dbg[0].lift()
            return
        win = tk.Toplevel(self.root)
        win.title("Debugger")
        win.transient(self.root)
        txt = tk.Text(win, width=44, height=20, font=("Menlo", 11), state="disabled")
        txt.pack(padx=8, pady=8)
        bar = ttk.Frame(win)
        bar.pack(fill="x", padx=8, pady=(0, 8))
        ttk.Button(bar, text="Step", command=self.step_once).pack(side="left", padx=2)
        ttk.Button(bar, text="Frame", command=self.step_frame).pack(side="left", padx=2)
        ttk.Button(bar, text="Close", command=win.destroy).pack(side="right", padx=2)
        self.dbg = (win, txt)
        self._update_dbg()

    def _update_dbg(self):
        if not self.dbg or not self.dbg[0].winfo_exists():
            return
        c = self.cpu
        lines = ["PC=%03X  OP=%04X  I=%03X  SP=%d" % (c.pc, c.last_op, c.I, c.sp),
                 "DT=%02X  ST=%02X  %s" % (c.dt, c.st,
                                          "[WAIT KEY V%X]" % c.wait_reg
                                          if c.wait_reg is not None else ""),
                 ""]
        for i in range(0, 16, 4):
            lines.append("  ".join("V%X=%02X" % (j, c.V[j]) for j in range(i, i + 4)))
        lines.append("")
        lines.append("Stack: " + " ".join("%03X" % s for s in c.stack[:c.sp]))
        lines.append("Keys:  " + "".join("%X" % k for k in range(16) if c.keys[k]))
        if c.halted:
            lines.append("")
            lines.append("HALTED: " + c.halt_reason)
        txt = self.dbg[1]
        txt.config(state="normal")
        txt.delete("1.0", "end")
        txt.insert("1.0", "\n".join(lines))
        txt.config(state="disabled")

    def show_keys(self):
        messagebox.showinfo(
            "Keyboard map",
            "CHIP-8 keypad  ->  keyboard\n\n"
            "1 2 3 C   ->   1 2 3 4\n"
            "4 5 6 D   ->   Q W E R\n"
            "7 8 9 E   ->   A S D F\n"
            "A 0 B F   ->   Z X C V\n\n"
            "Ctrl+P pause   Ctrl+N next frame   N step\n"
            "F1-F5 quick load   Shift+F1-F5 quick save\n"
            "Ctrl+R reset   Ctrl+M mute   Esc hide menu   Ctrl+Q exit",
            parent=self.root,
        )

    def about(self):
        messagebox.showinfo(
            "About %s" % APP_NAME,
            "%s - %s\n\n"
            "Single-file CHIP-8 emulator\n"
            "Desktop shell modeled on mGBA's Qt frontend\n"
            "(native menus, black game client, status bar).\n\n"
            "FILES: %s\nAudio backend: %s\nFrame rate: %d FPS"
            % (APP_NAME, VERSION, "ON" if FILES else "OFF",
               self.audio.backend, TARGET_FPS),
            parent=self.root,
        )

    # ------------------------------------------------------------------ input
    def _key_down(self, e):
        k = KEYMAP.get(e.keysym.lower())
        if k is not None:
            self.cpu.keys[k] = 1
            if self.cpu.wait_reg is not None:
                self.cpu.V[self.cpu.wait_reg] = k
                self.cpu.wait_reg = None

    def _key_up(self, e):
        k = KEYMAP.get(e.keysym.lower())
        if k is not None:
            self.cpu.keys[k] = 0

    # ------------------------------------------------------------- main loop
    def _render(self):
        cur = bytes(self.cpu.gfx)
        if self.blend:
            prev = self._prev
            shown = bytes(a | b for a, b in zip(cur, prev))
        else:
            shown = cur
        self._prev = cur
        if shown == self._shown:
            return
        self._shown = shown
        off, on = PALETTES[self.palette]
        tbl = (off, on)
        rows = []
        for r in range(32):
            base = r * 64
            rows.append("{" + " ".join([tbl[shown[base + c]] for c in range(64)]) + "}")
        self.img.put(" ".join(rows))
        self._scaled = self.img.zoom(self.scale, self.scale)
        self.canvas.itemconfig(self.cimg, image=self._scaled)

    def _frame(self):
        cpu = self.cpu
        if self.running and not cpu.halted:
            self.cycle_acc += self.cpu_hz / float(TARGET_FPS)
            n = int(self.cycle_acc)
            self.cycle_acc -= n
            step = cpu.step
            for _ in range(n):
                step()
            self._instr += n
            cpu.tick_timers()
        self.audio.update(cpu.st > 0 and self.running and not cpu.halted)
        self._render()

        self._frames += 1
        now = time.perf_counter()
        if now - self._stat_t >= 1.0:
            self._fps = self._frames / (now - self._stat_t)
            self._ips = int(self._instr / (now - self._stat_t))
            self._frames = 0
            self._instr = 0
            self._stat_t = now
            self._update_title()
            if self.show_status:
                state = "HALTED" if cpu.halted else (
                    "Running" if self.running else "Paused")
                if self.show_fps:
                    self.status.config(
                        text="%s  |  %s  |  %.1f fps  |  %d ips  |  %s%s"
                        % (self.rom_name, state, self._fps, self._ips,
                           self.audio.backend,
                           " (muted)" if self.audio.muted else
                           ("" if self.audio.enabled else " (off)")))
                else:
                    self.status.config(text="%s  |  %s" % (self.rom_name, state))

        self._dbg_tick += 1
        if self._dbg_tick >= 6:
            self._dbg_tick = 0
            self._update_dbg()

        # 60 FPS deadline scheduler
        self.next_t += 1.0 / TARGET_FPS
        now = time.perf_counter()
        if self.next_t < now - 0.1:
            self.next_t = now
        delay = max(1, int(round((self.next_t - now) * 1000)))
        self.root.after(delay, self._frame)

    def quit(self):
        self.audio.stop()
        self.root.destroy()


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
