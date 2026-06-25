#!/usr/bin/env python3
"""
PoE2 Strongbox / Runeshape Pricer
──────────────────────────────────────────────────────────────────────────────
• Scarica i prezzi di TUTTI gli item PoE2 da poe.ninja ogni 60 min (cache JSON)
• Monitora lo schermo ogni secondo con OCR
• Quando rileva il pannello "Runeshape Combinations" (o qualsiasi strongbox),
  legge gli item e mostra i prezzi nell'overlay
• Premi F6 per forzare uno scan manuale
• Ricerca manuale integrata nell'overlay

REQUISITI EXTRA:
  pip install mss pillow pytesseract requests
  Tesseract OCR (gratuito):
  https://github.com/UB-Mannheim/tesseract/wiki
  → installa in C:\\Program Files\\Tesseract-OCR\\tesseract.exe
──────────────────────────────────────────────────────────────────────────────
"""

import sys, os, re, time, json, threading, webbrowser, ctypes, ctypes.wintypes as wt, traceback, logging
from pathlib import Path
from datetime import datetime, timedelta

# ── auto-install ───────────────────────────────────────────────────────────────
def _pip(pkg):
    import subprocess
    print(f"[SETUP] Installazione {pkg}...")
    subprocess.check_call([sys.executable, "-m", "pip", "install", pkg],
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

for _pkg, _imp in [("requests","requests"), ("mss","mss"), ("Pillow","PIL")]:
    try: __import__(_imp)
    except ImportError: _pip(_pkg)

import requests, mss, mss.tools
from PIL import Image, ImageEnhance, ImageOps

try:
    import pytesseract
    _TESS_PATHS = [
        r"C:\Program Files\Tesseract-OCR\tesseract.exe",
        r"C:\Program Files (x86)\Tesseract-OCR\tesseract.exe",
    ]
    import shutil
    _tess = shutil.which("tesseract") or next((p for p in _TESS_PATHS if os.path.exists(p)), None)
    if _tess:
        pytesseract.pytesseract.tesseract_cmd = _tess
        _HAS_OCR = True
    else:
        _HAS_OCR = False
except ImportError:
    _pip("pytesseract")
    try:
        import pytesseract; _HAS_OCR = True
    except: _HAS_OCR = False

_OCR_ENGINE = "tesseract" if _HAS_OCR else None
_rapid_ocr  = None
if not _HAS_OCR:
    try:
        from rapidocr_onnxruntime import RapidOCR
        _rapid_ocr  = RapidOCR()
        _HAS_OCR    = True
        _OCR_ENGINE = "rapid"
    except ImportError:
        print("[SETUP] Installazione rapidocr-onnxruntime...")
        _pip("rapidocr-onnxruntime")
        try:
            from rapidocr_onnxruntime import RapidOCR
            _rapid_ocr  = RapidOCR()
            _HAS_OCR    = True
            _OCR_ENGINE = "rapid"
        except Exception as _e:
            print(f"[WARN] RapidOCR non disponibile: {_e}")
    except Exception as _e:
        print(f"[WARN] RapidOCR errore init: {_e}")

import tkinter as tk
from tkinter import ttk

# ── config ─────────────────────────────────────────────────────────────────────
APP_VERSION     = "1.0.0"
GITHUB_REPO     = "edenazord/poe2-strongbox-pricer"
PRICE_TTL_MIN   = 60
if getattr(sys, 'frozen', False):
    _APP_DIR = Path(sys.executable).parent
else:
    _APP_DIR = Path(__file__).parent
CACHE_FILE      = _APP_DIR / "prices_cache.json"
LOG_FILE        = _APP_DIR / "pricer.log"
logging.basicConfig(filename=str(LOG_FILE), level=logging.DEBUG,
                    format="%(asctime)s %(levelname)s %(message)s",
                    encoding="utf-8")
_log = logging.getLogger("poe2pricer")
SCAN_INTERVAL_S = 0.15  # secondi tra ogni scan OCR
# Regione schermo da scansionare (percentuale): lato sinistro dove appare il pannello
SCAN_LEFT_PCT  = 0.00
SCAN_TOP_PCT   = 0.03
SCAN_RIGHT_PCT = 0.62
SCAN_BOT_PCT   = 0.88

LEAGUES_API      = "https://www.pathofexile.com/api/trade2/data/leagues"
TRADE_FETCH_API  = "https://www.pathofexile.com/api/trade2/fetch"
HEADERS_REQ = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/125.0.0.0 Safari/537.36"
    ),
    "Accept": "application/json",
    "Content-Type": "application/json",
}

# ── poe2scout API (pricing source) ─────────────────────────────────────────────
POE2SCOUT_BASE = "https://api.poe2scout.com/poe2"
POE2SCOUT_HDR  = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
POE2SCOUT_CATS = [
    "currency", "fragments", "runes", "essences", "ultimatum",
    "expedition", "ritual", "breach", "abyss", "uncutgems",
    "lineagesupportgems", "delirium", "incursion", "idol",
    "verisium", "vaal", "vaultkeys",
]

# Keyword che indicano che il pannello strongbox/runeshape è aperto
TRIGGER_KW  = ["runeshape", "combinations", "strongbox", "rune", "flux", "scrap",
                "armourer", "lesser", "greater", "chilling", "glacial"]

# Colori UI
BG="#0d0d0d"; BG2="#1a1a1a"; BG3="#111111"; GOLD="#c8a84b"; WHITE="#e8e8e8"
GREEN="#4caf50"; RED="#ef5350"; GRAY="#555"; BORDER="#333"; ORANGE="#ff9800"

# ── WM_CLIPBOARDUPDATE + F6 hotkey (Windows native) ───────────────────────────
user32   = ctypes.windll.user32
kernel32 = ctypes.windll.kernel32
WM_HOTKEY  = 0x0312
WM_DESTROY = 0x0002
VK_F6      = 0x75
MOD_NOREPEAT = 0x4000
HOTKEY_ID    = 2

# ── Price cache ────────────────────────────────────────────────────────────────
class PriceCache:
    """Scarica e mantiene i prezzi da poe2scout (in exalted)."""

    def __init__(self):
        self._data: dict[str, float] = {}   # nome_lower -> price (exalted)
        self._last_update = datetime.min
        self._league = "Standard"
        self._lock = threading.Lock()
        self.on_update = None   # callback(count, league)

    def set_league(self, league: str):
        self._league = league

    def get(self, name: str) -> tuple[float | None, str | None]:
        """Ritorna (prezzo, nome_db) per il nome dato."""
        with self._lock:
            n = name.lower().strip()
            # Ricerca esatta
            if n in self._data:
                return self._data[n], n
            # Per le gem con livello: matchare il livello esatto
            # OCR: "Uncut Spirit Gem Level 20" → db: "uncut spirit gem (level 20)"
            lvl_m = re.search(r'level\s*(\d+)', n)
            if lvl_m:
                lvl_num = lvl_m.group(1)
                base = re.sub(r'\s*level\s*\d+', '', n).strip()
                target = f"{base} (level {lvl_num})"
                if target in self._data:
                    return self._data[target], target
                # Prova senza spazi
                ts = target.replace(" ", "")
                for k, v in self._data.items():
                    if k.replace(" ", "") == ts:
                        return v, k
            # Ricerca parziale:
            # 1) prima prova match esatto senza spazi
            best_price = None
            best_key   = None
            ns = n.replace(" ", "")
            has_level = "level" in ns
            for k, v in self._data.items():
                if "(level" in k and not has_level:
                    continue
                ks = k.replace(" ", "")
                if ns == ks:
                    return v, k
            # 2) substring solo se lunghezze simili (max 4 chars differenza)
            for k, v in self._data.items():
                if "(level" in k and not has_level:
                    continue
                ks = k.replace(" ", "")
                if abs(len(ns) - len(ks)) > 4:
                    continue
                if n in k or k in n or ns in ks or ks in ns:
                    if best_price is None or v > best_price:
                        best_price = v
                        best_key   = k
            return best_price, best_key

    def search(self, query: str) -> list[tuple[str, float]]:
        """Ritorna lista ordinata per prezzo di item che contengono query."""
        q = query.lower().strip()
        with self._lock:
            results = [(k, v) for k, v in self._data.items() if q in k]
        results.sort(key=lambda x: x[1], reverse=True)
        return results

    @property
    def count(self) -> int:
        with self._lock: return len(self._data)

    @property
    def last_update_str(self) -> str:
        if self._last_update == datetime.min: return "mai"
        return self._last_update.strftime("%H:%M")

    def needs_refresh(self) -> bool:
        return datetime.now() - self._last_update > timedelta(minutes=PRICE_TTL_MIN)

    def load_disk_cache(self):
        """Carica cache da disco se fresca e stessa valuta."""
        if not CACHE_FILE.exists(): return
        try:
            with open(CACHE_FILE, encoding="utf-8") as f:
                saved = json.load(f)
            ts = datetime.fromisoformat(saved["ts"])
            if datetime.now() - ts < timedelta(minutes=PRICE_TTL_MIN * 2):
                with self._lock:
                    self._data = {k.lower(): v for k, v in saved["data"].items()}
                    self._last_update = ts
                    if saved.get("league"):
                        self._league = saved["league"]
        except Exception:
            pass

    def refresh(self, force=False):
        if not force and not self.needs_refresh():
            return False
        new_data: dict[str, float] = {}
        errors: list[str] = []

        # ── Risolvi short name della lega su poe2scout ────────────────────────
        short_league = self._league.split()[0].lower() if self._league else "runes"
        try:
            r = requests.get(f"{POE2SCOUT_BASE}/Leagues", headers=POE2SCOUT_HDR, timeout=15)
            if r.ok:
                for lg in r.json():
                    if lg.get("Value", "").lower() == self._league.lower():
                        short_league = lg.get("ShortName", short_league)
                        break
        except Exception as e:
            errors.append(f"leagues: {e}")

        if self.on_update:
            self.on_update(0, f"{self._league} – caricamento ({len(POE2SCOUT_CATS)} categorie)...")

        # ── Scarica prezzi da poe2scout per tutte le categorie ────────────────
        for cat in POE2SCOUT_CATS:
            page = 1
            while True:
                try:
                    url = (f"{POE2SCOUT_BASE}/Leagues/{short_league}/Currencies/ByCategory"
                           f"?Category={cat}&ReferenceCurrency=exalted&SmoothingDays=1"
                           f"&Page={page}&PerPage=200")
                    r = requests.get(url, headers=POE2SCOUT_HDR, timeout=15)
                    if not r.ok:
                        errors.append(f"{cat} HTTP {r.status_code}")
                        break
                    data = r.json()
                    items = data.get("Items", data if isinstance(data, list) else [])
                    for item in items:
                        name  = item.get("Text", "")
                        price = float(item.get("CurrentPrice") or 0)
                        if name and price > 0:
                            new_data[name.lower()] = price
                    if len(items) < 200:
                        break
                    page += 1
                except Exception as e:
                    errors.append(f"{cat}: {e}")
                    break

        self._last_errors = errors

        if new_data:
            with self._lock:
                self._data = new_data
                self._last_update = datetime.now()
            try:
                with open(CACHE_FILE, "w", encoding="utf-8") as f:
                    json.dump({"ts": self._last_update.isoformat(),
                               "league": self._league,
                               "data": dict(new_data)}, f, ensure_ascii=False)
            except Exception:
                pass
            if self.on_update:
                self.on_update(len(new_data), self._league)
            return True
        return False

    def start_auto_refresh(self):
        def _loop():
            while True:
                try: self.refresh()
                except Exception: pass
                time.sleep(600)   # ogni 10 min (allineato a poe2scout)
        threading.Thread(target=_loop, daemon=True).start()


# ── OCR screen monitor ─────────────────────────────────────────────────────────
class ScreenMonitor:
    """Scansiona lo schermo, rileva il pannello strongbox e legge gli item."""

    def __init__(self, price_cache: PriceCache, on_items, on_debug):
        self._cache    = price_cache
        self._on_items = on_items
        self._on_debug = on_debug
        self._running  = False
        self._last_raw = ""

    def start(self):
        self._running = True
        threading.Thread(target=self._loop, daemon=True).start()

    def stop(self): self._running = False

    def scan_now(self):
        """Scan forzato (F6)."""
        threading.Thread(target=self._do_scan, daemon=True).start()

    def _loop(self):
        with mss.MSS() as sct:
            while self._running:
                try:
                    self._do_scan(sct)
                except Exception as e:
                    _log.error(f"Scan error: {e}\n{traceback.format_exc()}")
                    self._on_debug(f"Errore scan: {e}", RED)
                time.sleep(SCAN_INTERVAL_S)

    def _do_scan(self, sct=None):
        own_sct = sct is None
        if own_sct: sct = mss.MSS().__enter__()
        try:
            mon = sct.monitors[1]
            w, h = mon["width"], mon["height"]
            region = {
                "left":   mon["left"] + int(w * SCAN_LEFT_PCT),
                "top":    mon["top"]  + int(h * SCAN_TOP_PCT),
                "width":  int(w * (SCAN_RIGHT_PCT - SCAN_LEFT_PCT)),
                "height": int(h * (SCAN_BOT_PCT   - SCAN_TOP_PCT)),
            }
            shot = sct.grab(region)
            img  = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")

            if not _HAS_OCR:
                self._on_debug("OCR non disponibile – pip install rapidocr-onnxruntime", RED)
                return

            if _OCR_ENGINE == "tesseract":
                img_proc = self._preprocess(img)
                text = pytesseract.image_to_string(img_proc, config="--psm 6 -l eng")
                rapid_result = None
            else:  # RapidOCR – mantiene bounding box per overlay in-game
                import numpy as np
                img_np = np.array(img)
                rapid_result, _ = _rapid_ocr(img_np)
                text = "\n".join(r[1] for r in rapid_result) if rapid_result else ""

            text_l = text.lower()
            if not any(kw in text_l for kw in TRIGGER_KW):
                if self._last_raw:  # era visibile prima → nascondi subito
                    self._last_raw = ""
                    self._on_items([])
                return

            if text.strip() == self._last_raw.strip():
                return
            self._last_raw = text

            if rapid_result is not None:
                items = self._parse_items_rapid(rapid_result, region)
            else:
                items = self._parse_items(text)
            self._on_items(items)
        finally:
            if own_sct:
                try: sct.__exit__(None, None, None)
                except: pass

    @staticmethod
    def _preprocess(img: Image.Image) -> Image.Image:
        img = img.resize((img.width * 2, img.height * 2), Image.LANCZOS)
        img = img.convert("L")
        img = ImageEnhance.Contrast(img).enhance(2.5)
        img = img.point(lambda x: 255 if x > 128 else 0, "1").convert("L")
        return img

    def _parse_items(self, text: str) -> list[dict]:
        items = []
        pat = re.compile(r"^(\d+)\s*[xX×]\s*(.+)$")
        seen = set()
        for line in text.splitlines():
            line = line.strip()
            if len(line) < 4: continue
            m = pat.match(line)
            if not m: continue
            qty  = int(m.group(1))
            name = re.sub(r"[^a-zA-Z0-9 '\-]", "", m.group(2)).strip()
            if not name or name.lower() in seen: continue
            seen.add(name.lower())
            price, db_name = self._cache.get(name)
            display = db_name.title() if db_name else name
            items.append({
                "qty":   qty,
                "name":  display,
                "price": price,
                "total": price * qty if price else None,
            })
        return items

    def _parse_items_rapid(self, result, region: dict) -> list[dict]:
        """Parsa item da RapidOCR includendo posizioni schermo per l'overlay in-game."""
        items = []
        pat   = re.compile(r"^(\d+)\s*[xX×]\s*(.+)$")
        seen  = set()
        for det in result:
            try:
                bbox, text, _score = det
                m = pat.match(text.strip())
                if not m: continue
                qty  = int(m.group(1))
                name = re.sub(r"[^a-zA-Z0-9 '\-]", "", m.group(2)).strip()
                if not name or name.lower() in seen: continue
                seen.add(name.lower())
                # bbox = [[x1,y1], [x2,y2], [x3,y3], [x4,y4]]
                cy = int(sum(p[1] for p in bbox) / 4)    # centro Y
                rx = int(max(p[0] for p in bbox))         # bordo destro X
                price, db_name = self._cache.get(name)
                display = db_name.title() if db_name else name
                items.append({
                    "qty":          qty,
                    "name":         display,
                    "price":        price,
                    "total":        price * qty if price else None,
                    "screen_y":     region["top"]  + cy,
                    "screen_right": region["left"] + rx,
                })
            except Exception:
                pass
        return items


# ── In-game price overlay (trasparente, sempre in primo piano) ─────────────────
class InGamePriceOverlay:
    """Overlay trasparente a tutto schermo che mostra prezzi accanto agli item in gioco."""

    _TRANSP = "#010101"   # chromakey: questo colore diventa trasparente

    def __init__(self, root: tk.Misc):
        self._win = tk.Toplevel(root)
        self._win.overrideredirect(True)            # nessuna barra titolo
        self._win.attributes("-topmost", True)
        self._win.attributes("-transparentcolor", self._TRANSP)
        self._win.config(bg=self._TRANSP)
        sw = self._win.winfo_screenwidth()
        sh = self._win.winfo_screenheight()
        self._win.geometry(f"{sw}x{sh}+0+0")
        self._win.withdraw()
        self._labels: list[tk.Label] = []

    def show(self, items: list[dict], currency_sym: str = "c"):
        """Mostra i prezzi in-game. Items con screen_y e screen_right vengono posizionati."""
        for lbl in self._labels:
            lbl.destroy()
        self._labels.clear()

        positioned = [it for it in items if "screen_y" in it and "screen_right" in it]
        if not positioned:
            self._win.withdraw()
            return

        for it in positioned:
            price = it.get("price")
            qty   = it.get("qty", 1)
            sy    = it["screen_y"]
            sx    = it["screen_right"] + 16   # 16px a destra del testo rilevato
            if price and price > 0:
                total = price * qty
                txt   = f"{total:.1f}{currency_sym}"
                col   = GREEN if total >= 5 else (ORANGE if total >= 1 else RED)
            else:
                txt, col = "?", GRAY
            lbl = tk.Label(self._win, text=txt, bg=self._TRANSP, fg=col,
                           font=("Segoe UI", 13, "bold"),
                           padx=0, pady=0, borderwidth=0, highlightthickness=0)
            lbl.place(x=sx, y=sy - 10)
            self._labels.append(lbl)

        self._win.deiconify()
        self._win.lift()

    def hide(self):
        for lbl in self._labels:
            lbl.destroy()
        self._labels.clear()
        self._win.withdraw()


# ── Overlay GUI ────────────────────────────────────────────────────────────────
class StrongboxOverlay:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("PoE2 Strongbox Pricer")
        self.root.configure(bg=BG)
        self.root.attributes("-topmost", True)
        self.root.attributes("-alpha", 0.95)
        self.root.resizable(True, True)
        self.root.geometry("460x580+30+30")

        self._cache   = PriceCache()
        self._ingame  = InGamePriceOverlay(self.root)
        self._updater = AutoUpdater(self.root,
                                    debug_cb=lambda m, c=GRAY: self._set_debug(m, c))
        self._monitor = ScreenMonitor(
            price_cache=self._cache,
            on_items=lambda items: self.root.after(0, lambda: self._show_items(items)),
            on_debug=lambda msg, col=GRAY: self.root.after(0, lambda: self._set_debug(msg, col)),
        )
        self._cache.on_update = lambda n, lg: self.root.after(0,
            lambda: self._set_status(f"Online — {n} prezzi caricati", GREEN))

        self._dx = self._dy = 0
        self._build_ui()
        self._init_data()

    # ── UI ─────────────────────────────────────────────────────────────────────
    def _build_ui(self):
        r = self.root

        # Barra titolo (draggable)
        bar = tk.Frame(r, bg=BORDER, height=30)
        bar.pack(fill=tk.X)
        bar.bind("<ButtonPress-1>", lambda e: (setattr(self,"_dx",e.x), setattr(self,"_dy",e.y)))
        bar.bind("<B1-Motion>",     lambda e: r.geometry(
            f"+{r.winfo_x()+e.x-self._dx}+{r.winfo_y()+e.y-self._dy}"))
        tk.Label(bar, text=f"  PoE2 Strongbox Pricer v{APP_VERSION}", bg=BORDER, fg=GOLD,
                 font=("Segoe UI",10,"bold")).pack(side=tk.LEFT, pady=5)
        self._lbl_league = tk.Label(bar, text="", bg=BORDER, fg=GRAY, font=("Segoe UI",8))
        self._lbl_league.pack(side=tk.LEFT, padx=6)
        tk.Button(bar, text="x", bg=BORDER, fg=RED, relief=tk.FLAT,
                  font=("Segoe UI",10,"bold"), command=r.destroy,
                  cursor="hand2").pack(side=tk.RIGHT, padx=4)

        # Status
        self._lbl_status = tk.Label(r, text="Avvio...", bg=BG, fg=GRAY,
                                    font=("Segoe UI",8), anchor="w")
        self._lbl_status.pack(fill=tk.X, padx=10, pady=(6,0))

        # ── Ricerca manuale ─────────────────────────────────────────────────
        search_frame = tk.Frame(r, bg=BG2)
        search_frame.pack(fill=tk.X, padx=8, pady=4)
        tk.Label(search_frame, text="Cerca item:", bg=BG2, fg=GRAY,
                 font=("Segoe UI",8)).pack(side=tk.LEFT, padx=6)
        self._search_var = tk.StringVar()
        self._search_var.trace_add("write", lambda *_: self._do_search())
        entry = tk.Entry(search_frame, textvariable=self._search_var,
                         bg="#222", fg=WHITE, insertbackground=WHITE,
                         relief=tk.FLAT, font=("Consolas",10), bd=4)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4, pady=4)
        tk.Button(search_frame, text="X", bg=BG2, fg=GRAY, relief=tk.FLAT,
                  font=("Segoe UI",8), cursor="hand2",
                  command=lambda: self._search_var.set("")).pack(side=tk.RIGHT, padx=4)

        sep = tk.Frame(r, bg=BORDER, height=1)
        sep.pack(fill=tk.X, padx=8, pady=2)

        # ── Etichetta sezione ───────────────────────────────────────────────
        self._lbl_section = tk.Label(r, text="Rilevamento OCR attivo — apri uno Strongbox in PoE2",
                                     bg=BG, fg=GRAY, font=("Segoe UI",8,"italic"), anchor="w")
        self._lbl_section.pack(fill=tk.X, padx=10)

        # ── Lista item ──────────────────────────────────────────────────────
        list_frame = tk.Frame(r, bg=BG)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=4)

        sb = tk.Scrollbar(list_frame, bg=BG2, troughcolor=BG)
        sb.pack(side=tk.RIGHT, fill=tk.Y)

        self._tree = ttk.Treeview(list_frame,
                                  columns=("qty","name","unit_price","total"),
                                  show="headings",
                                  yscrollcommand=sb.set)
        sb.config(command=self._tree.yview)

        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview",
                         background=BG2, fieldbackground=BG2,
                         foreground=WHITE, rowheight=22,
                         font=("Consolas",9))
        style.configure("Treeview.Heading",
                         background=BORDER, foreground=GOLD,
                         font=("Segoe UI",9,"bold"))
        style.map("Treeview", background=[("selected","#2a4a6b")])

        self._tree.heading("qty",        text="Qtà")
        self._tree.heading("name",       text="Item")
        self._tree.heading("unit_price", text="Prezzo/unit (e)")
        self._tree.heading("total",      text="Totale (e)")
        self._tree.column("qty",        width=35,  anchor="center")
        self._tree.column("name",       width=200, anchor="w")
        self._tree.column("unit_price", width=110, anchor="e")
        self._tree.column("total",      width=90,  anchor="e")
        self._tree.pack(fill=tk.BOTH, expand=True)

        # ── Pulsanti ────────────────────────────────────────────────────────
        btn_frame = tk.Frame(r, bg=BG)
        btn_frame.pack(fill=tk.X, padx=8, pady=4)
        tk.Button(btn_frame, text="↻ Aggiorna prezzi", bg="#2a4a6b", fg=WHITE,
                  relief=tk.FLAT, font=("Segoe UI",9), cursor="hand2",
                  command=self._force_refresh).pack(side=tk.LEFT, padx=4)



        # ── Debug ────────────────────────────────────────────────────────────
        tk.Frame(r, bg=BORDER, height=1).pack(fill=tk.X, padx=8)
        self._lbl_debug = tk.Label(r, text="", bg="#0a0a0a", fg=GRAY,
                                   font=("Consolas",7), anchor="w", wraplength=440)
        self._lbl_debug.pack(fill=tk.X, padx=8, pady=(2,4))

    # ── init ───────────────────────────────────────────────────────────────────
    def _init_data(self):
        def _start():
            # 1) Lega – usa poe2scout (stessa API usata per i prezzi)
            league = "Standard"
            try:
                r = requests.get(f"{POE2SCOUT_BASE}/Leagues", headers=POE2SCOUT_HDR, timeout=10)
                if r.ok:
                    leagues = r.json()
                    current = next(
                        (x for x in leagues
                         if x.get("IsCurrent")
                         and "hardcore" not in x.get("ShortName", "").lower()),
                        None
                    )
                    league = current["Value"] if current else (leagues[0]["Value"] if leagues else "Standard")
            except Exception: pass
            self._cache.set_league(league)
            self.root.after(0, lambda: self._lbl_league.config(text=f"lega: {league}", fg=GREEN))

            # 2) Cache disco
            self._cache.load_disk_cache()
            if self._cache.count > 0:
                self.root.after(0, lambda: self._set_status(
                    f"Online — {self._cache.count} prezzi caricati", GREEN))

            # 3) Refresh se necessario
            if self._cache.needs_refresh():
                self.root.after(0, lambda: self._set_status("Aggiornamento prezzi...", ORANGE))
                self._cache.refresh()

            # 4) Auto-refresh ogni 10 min
            self._cache.start_auto_refresh()

            # 5) OCR monitor
            if _HAS_OCR:
                self._monitor.start()
                self.root.after(0, lambda: self._set_debug(
                    "Pronto — apri una Combination in PoE2", GREEN))
            else:
                self.root.after(0, lambda: self._set_debug(
                    "Errore: componente OCR mancante", RED))

            # 6) Check aggiornamenti
            self._updater.check_async()

        threading.Thread(target=_start, daemon=True).start()

    # ── mostra item rilevati ───────────────────────────────────────────────────
    def _show_items(self, items: list[dict]):
        if not items:
            self._ingame.hide()
            return
        self._lbl_section.config(text=f"Rilevati {len(items)} item dallo schermo", fg=GREEN)
        self._populate_tree(items)
        self._ingame.show(items, "e")

    def _populate_tree(self, items: list[dict]):
        for row in self._tree.get_children():
            self._tree.delete(row)

        grand_total = 0.0
        for item in items:
            qty   = item["qty"]
            name  = item["name"]
            price = item["price"]
            total = item["total"]

            # Salta item con prezzo 0 (non quotati) nelle ricerche manuali
            if price == 0.0 and item.get("_search"):
                continue

            unit_str  = f"{price:.1f}e" if price else "N/D"
            total_str = f"{total:.1f}e" if total else "—"

            tag = "known" if price else "unknown"
            self._tree.insert("", tk.END,
                              values=(qty, name, unit_str, total_str),
                              tags=(tag,))
            if total: grand_total += total

        self._tree.tag_configure("known",   foreground=WHITE)
        self._tree.tag_configure("unknown", foreground=GRAY)



    # ── ricerca manuale ────────────────────────────────────────────────────────
    def _do_search(self):
        q = self._search_var.get().strip()
        if len(q) < 2:
            self._lbl_section.config(text="Ricerca: digita almeno 2 caratteri", fg=GRAY)
            for row in self._tree.get_children():
                self._tree.delete(row)
            return

        results = self._cache.search(q)
        # Filtra item senza prezzo reale (price==0)
        results = [(k, v) for k, v in results if v > 0]
        self._lbl_section.config(
            text=f"Risultati ricerca \"{q}\": {len(results)} item trovati", fg=GREEN)

        items = [{"qty": 1, "name": name.title(),
                  "price": price, "total": price, "_search": True}
                 for name, price in results[:80]]
        self._populate_tree(items)

    def _force_refresh(self):
        self._set_status("Aggiornamento prezzi...", ORANGE)
        def _r():
            ok = self._cache.refresh(force=True)
            if ok:
                self.root.after(0, lambda: self._set_status(
                    f"Online — {self._cache.count} prezzi caricati", GREEN))
                self.root.after(0, lambda: self._set_debug("Prezzi aggiornati", GREEN))
            else:
                self.root.after(0, lambda: self._set_status("Offline — impossibile aggiornare", RED))
                self.root.after(0, lambda: self._set_debug("Verifica la connessione internet", RED))
        threading.Thread(target=_r, daemon=True).start()

    # ── helpers ────────────────────────────────────────────────────────────────
    def _set_status(self, msg, color=WHITE):
        self._lbl_status.config(text=msg, fg=color)

    def _set_debug(self, msg, color=GRAY):
        self._lbl_debug.config(text=msg, fg=color)

    def run(self):
        self.root.mainloop()


# ── Auto-updater ───────────────────────────────────────────────────────────────
class AutoUpdater:
    """Controlla GitHub Releases per aggiornamenti e scarica il nuovo exe."""

    RELEASES_API = f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest"

    def __init__(self, root: tk.Tk, debug_cb=None):
        self._root = root
        self._debug = debug_cb or (lambda m, c=GRAY: None)
        self._banner: tk.Frame | None = None

    def check_async(self):
        threading.Thread(target=self._check, daemon=True).start()

    def _check(self):
        try:
            r = requests.get(self.RELEASES_API, headers={"Accept": "application/vnd.github+json"},
                             timeout=10)
            if not r.ok:
                _log.debug(f"Update check HTTP {r.status_code}")
                return
            data = r.json()
            tag = data.get("tag_name", "").lstrip("v")
            if not tag or tag == APP_VERSION:
                return
            # Confronto semplice: se il tag è diverso → aggiornamento disponibile
            if self._version_tuple(tag) <= self._version_tuple(APP_VERSION):
                return
            # Cerca l'asset .exe
            exe_url = None
            exe_name = None
            for asset in data.get("assets", []):
                if asset["name"].lower().endswith(".exe"):
                    exe_url = asset["browser_download_url"]
                    exe_name = asset["name"]
                    break
            if not exe_url:
                return
            self._root.after(0, lambda: self._show_banner(tag, exe_url, exe_name,
                                                          data.get("body", "")))
        except Exception as e:
            _log.debug(f"Update check error: {e}")

    @staticmethod
    def _version_tuple(v: str):
        parts = []
        for p in v.split("."):
            try: parts.append(int(p))
            except ValueError: parts.append(0)
        return tuple(parts)

    def _show_banner(self, version: str, url: str, name: str, notes: str):
        if self._banner:
            return
        self._banner = tk.Frame(self._root, bg="#1a3a1a")
        self._banner.pack(fill=tk.X, padx=8, pady=(4, 0), before=self._root.winfo_children()[1])
        tk.Label(self._banner, text=f"Aggiornamento v{version} disponibile!",
                 bg="#1a3a1a", fg=GREEN, font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT, padx=8)
        tk.Button(self._banner, text="Scarica", bg=GREEN, fg="#000", relief=tk.FLAT,
                  font=("Segoe UI", 8, "bold"), cursor="hand2",
                  command=lambda: self._download(url, name, version)).pack(side=tk.LEFT, padx=4)
        tk.Button(self._banner, text="✕", bg="#1a3a1a", fg=GRAY, relief=tk.FLAT,
                  font=("Segoe UI", 8), cursor="hand2",
                  command=lambda: (self._banner.destroy(), setattr(self, '_banner', None))
                  ).pack(side=tk.RIGHT, padx=4)

    def _download(self, url: str, name: str, version: str):
        self._debug(f"Download v{version} in corso...", ORANGE)
        threading.Thread(target=lambda: self._do_download(url, name, version), daemon=True).start()

    def _do_download(self, url: str, name: str, version: str):
        try:
            r = requests.get(url, stream=True, timeout=120)
            r.raise_for_status()
            if getattr(sys, 'frozen', False):
                exe_path = Path(sys.executable)
                new_path = exe_path.parent / f"{exe_path.stem}_v{version}.exe"
            else:
                new_path = _APP_DIR / name
            with open(new_path, "wb") as f:
                for chunk in r.iter_content(chunk_size=8192):
                    f.write(chunk)
            self._root.after(0, lambda: self._debug(
                f"v{version} scaricata: {new_path.name} — riavvia l'app", GREEN))
            if self._banner:
                self._root.after(0, lambda: self._replace_banner_with_restart(new_path))
        except Exception as e:
            _log.error(f"Download error: {e}")
            self._root.after(0, lambda: self._debug(f"Errore download: {e}", RED))

    def _replace_banner_with_restart(self, new_path: Path):
        if self._banner:
            self._banner.destroy()
        self._banner = tk.Frame(self._root, bg="#1a3a1a")
        self._banner.pack(fill=tk.X, padx=8, pady=(4, 0), before=self._root.winfo_children()[1])
        tk.Label(self._banner, text=f"Aggiornamento scaricato!",
                 bg="#1a3a1a", fg=GREEN, font=("Segoe UI", 9, "bold")).pack(side=tk.LEFT, padx=8)
        if getattr(sys, 'frozen', False):
            tk.Button(self._banner, text="Riavvia ora", bg=GREEN, fg="#000", relief=tk.FLAT,
                      font=("Segoe UI", 8, "bold"), cursor="hand2",
                      command=lambda: self._restart(new_path)).pack(side=tk.LEFT, padx=4)
        else:
            tk.Label(self._banner, text=f"{new_path.name}",
                     bg="#1a3a1a", fg=WHITE, font=("Segoe UI", 8)).pack(side=tk.LEFT, padx=4)

    def _restart(self, new_path: Path):
        """Sostituisce il vecchio exe col nuovo e riavvia."""
        try:
            current = Path(sys.executable)
            backup  = current.with_suffix(".old")
            # Rinomina corrente → .old, nuovo → corrente
            bat = current.parent / "_update.bat"
            bat.write_text(
                f'@echo off\n'
                f'timeout /t 2 /nobreak >nul\n'
                f'del "{current}"\n'
                f'move "{new_path}" "{current}"\n'
                f'start "" "{current}"\n'
                f'del "%~f0"\n',
                encoding="utf-8"
            )
            os.startfile(str(bat))
            self._root.destroy()
        except Exception as e:
            _log.error(f"Restart error: {e}")


# ── entry point ────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    if not _HAS_OCR:
        print("\n[WARN] OCR non disponibile. Per attivarlo:")
        print("  •  pip install rapidocr-onnxruntime  (consigliato, nessun binario extra)")
        print("  •  oppure Tesseract: https://github.com/UB-Mannheim/tesseract/wiki\n")

    app = StrongboxOverlay()
    app.run()
