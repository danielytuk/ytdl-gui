# YTDL GUI - Windows-only (Python 3.12+)
#
# pip deps:
#   pip install PySide6 requests mutagen
#
# Optional:
#   pip install shazamio
#   pip install spotapi
#
# Binaries downloaded at runtime to %TEMP%\YTDL_bin:
#   yt-dlp.exe, ffmpeg.exe, ffprobe.exe, deno.exe

from __future__ import annotations

import asyncio
import ctypes
import html
import json
import os
import re
import shutil
import sys
import tempfile
import time
import traceback
import zipfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import parse_qs, urlparse, urlunparse, urlencode
import threading

import requests
from PySide6 import QtCore, QtGui, QtWidgets

# Platform guard
if sys.platform != "win32":
    raise SystemExit("This application is Windows-only.")


# Single instance (Windows mutex)
class SingleInstance:
    ERROR_ALREADY_EXISTS = 183

    def __init__(self, name: str):
        self.name = name
        self.handle = None

    def acquire(self) -> bool:
        kernel32 = ctypes.windll.kernel32
        kernel32.SetLastError(0)
        self.handle = kernel32.CreateMutexW(None, False, self.name)
        if not self.handle:
            return True
        last = kernel32.GetLastError()
        return last != self.ERROR_ALREADY_EXISTS

    def release(self) -> None:
        if self.handle:
            ctypes.windll.kernel32.CloseHandle(self.handle)
            self.handle = None


# App constants
APP_NAME = "YTDL"
USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"
)

# Valid URL detection (single video / shorts / playlist)
YOUTUBE_RE = re.compile(
    r"(https?://)?(www\.)?"
    r"(youtube\.com/watch\?v=[\w-]{6,}.*|youtu\.be/[\w-]{6,}.*|youtube\.com/shorts/[\w-]{6,}.*|youtube\.com/playlist\?list=[\w-]{6,}.*)",
    re.IGNORECASE,
)

# Toolchain in system temp
BIN_DIR = Path(tempfile.gettempdir()) / f"{APP_NAME}_bin"
BIN_DIR.mkdir(parents=True, exist_ok=True)

YTDLP_URL = "https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp.exe"
YTDLP_PATH = BIN_DIR / "yt-dlp.exe"

FFMPEG_ZIP_URL = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"
FFMPEG_PATH = BIN_DIR / "ffmpeg.exe"
FFPROBE_PATH = BIN_DIR / "ffprobe.exe"

DENO_ZIP_URL = "https://github.com/denoland/deno/releases/latest/download/deno-x86_64-pc-windows-msvc.zip"
DENO_PATH = BIN_DIR / "deno.exe"

TOOL_REFRESH_SECONDS = 2 * 60 * 60  # 2 hours
REQUEST_COOLDOWN_S = 0.8  # metadata politeness (not for binary downloads)

# Internet connectivity check requirement
CONNECT_TEST_URL = "https://am.i.mullvad.net/connected"


# Dark theme (compact, no clipping)
QSS = """
* { background: #121623; font-family: "Segoe UI", "Inter", "Arial"; font-size: 14px; }
QWidget {  color: #E7EAF0; }
QFrame#Card { background: #121623; border: 1px solid #232734; border-radius: 12px; }
QLabel#Title { font-size: 15px; font-weight: 700; }
QLabel#Subtle { color: #AAB1C3; }
QLineEdit {
  background: #0F1320; border: 1px solid #2A3042; border-radius: 10px;
  padding: 12px 10px; selection-background-color: #3B82F6;
}
QCheckBox { spacing: 8px; }
QProgressBar {
  border: 1px solid #2A3042; border-radius: 10px; text-align: center;
  background: #101522; height: 14px;
}
QProgressBar::chunk { background: #3B82F6; border-radius: 10px; }
QComboBox {
  background: #0F1320; border: 1px solid #2A3042; border-radius: 10px;
  padding: 8px 10px;
}
QComboBox QAbstractItemView {
  background: #0F1320; border: 1px solid #2A3042; selection-background-color: #3B82F6;
}
QPushButton {
  background: #1A2031; border: 1px solid #2A3042; border-radius: 10px;
  padding: 10px 12px;
}
QPushButton:hover { background: #20283D; }
"""


# Helpers: filename sanitization
_INVALID_FS_RE = re.compile(r'[<>:"/\\|?*]+')


def sanitize_filename(name: str, max_len: int = 180) -> str:
    s = (name or "").strip()
    s = _INVALID_FS_RE.sub("_", s)
    s = re.sub(r"\s+", " ", s).strip().strip(". ")
    if not s:
        s = "audio"
    if len(s) > max_len:
        s = s[:max_len].rstrip()
    return s


# YouTube title parsing (kept + improved safety)
ALBUM_SUFFIX_RE = re.compile(r"\s*[-–—]\s*(single|ep|album)\s*$", re.IGNORECASE)


def clean_album_name(name: str) -> str:
    return ALBUM_SUFFIX_RE.sub("", (name or "")).strip()


_MARKETING_BAD_WORDS = (
    "official",
    "lyrics",
    "audio",
    "video",
    "music video",
    "visualizer",
    "free download",
    "4k",
    "4k remaster",
    "4k remastered",
)
_MARKETING_BAD_WORDS_SORTED = tuple(sorted(_MARKETING_BAD_WORDS, key=len, reverse=True))
_MARKETING_KEEP_IF_REMIX_WORDS = ("remix", "mix", "edit", "bootleg", "rework", "remaster", "remastered")
_GENERIC_CONNECTORS = {"and", "with", "feat", "featuring", "ft", "vs", "x"}

_BAD_TOKENS = set()
for phrase in _MARKETING_BAD_WORDS:
    for tok in phrase.lower().split():
        _BAD_TOKENS.add(tok)


def _segment_is_marketing(seg: str) -> bool:
    seg_l = seg.lower()
    if any(word in seg_l for word in _MARKETING_KEEP_IF_REMIX_WORDS):
        return False
    tokens = re.findall(r"[a-z0-9']+", seg_l)
    meaningful = [t for t in tokens if t not in _GENERIC_CONNECTORS]
    if not meaningful:
        return False
    return all(t in _BAD_TOKENS for t in meaningful)


def _strip_trailing_marketing(title: str) -> str:
    s = (title or "").strip()
    if not s:
        return s

    while s.endswith((")", "]")):
        close_idx = len(s) - 1
        open_ch = "(" if s.endswith(")") else "["
        open_idx = s.rfind(open_ch)
        if open_idx == -1:
            break
        inside = s[open_idx + 1 : close_idx].strip().lower()
        if any(word in inside for word in _MARKETING_KEEP_IF_REMIX_WORDS):
            break
        if any(word in inside for word in _MARKETING_BAD_WORDS):
            s = s[:open_idx].rstrip()
            continue
        break

    lowered = s.lower()
    for sep in (" - ", " | ", " • "):
        idx = lowered.rfind(sep)
        if idx == -1:
            continue
        right = s[idx + len(sep) :].strip()
        if _segment_is_marketing(right):
            s = s[:idx].rstrip()
            break

    while True:
        lowered = s.lower()
        trimmed = False
        for phrase in _MARKETING_BAD_WORDS_SORTED:
            pl = phrase.lower()
            if lowered.endswith(pl):
                idx = len(s) - len(pl)
                if idx == 0 or s[idx - 1] in " []()-•|":
                    s = s[:idx].rstrip()
                    trimmed = True
                    break
        if not trimmed:
            break

    s = re.sub(r"[\-\|\•\s]+$", "", s)
    return s.strip()


def parse_youtube_title(raw_title: str) -> tuple[str, str]:
    if not raw_title:
        return "", ""
    s = _strip_trailing_marketing(raw_title)
    s = re.sub(r"\s+", " ", s).strip()
    if not s:
        return "", ""

    parts = re.split(r"\s[-–—]\s", s, maxsplit=1)
    if len(parts) == 2:
        artist = parts[0].strip(" -–—")
        title_part = parts[1].strip()
    else:
        artist = ""
        title_part = s

    m = re.match(r"^\[(.+)\]$", title_part)
    if m:
        title_part = m.group(1).strip()

    if (title_part.startswith('"') and title_part.endswith('"')) or (
        title_part.startswith("'") and title_part.endswith("'")
    ):
        title_part = title_part[1:-1].strip()

    return artist, title_part.strip()


# Errors + subprocess wrapper (NO console windows)
class AppError(RuntimeError):
    pass


def _tail(text: str, max_chars: int = 4000) -> str:
    if not text:
        return ""
    return text if len(text) <= max_chars else text[-max_chars:]


def run_cmd(args: List[str], cwd: Optional[Path] = None, timeout: Optional[int] = None) -> Tuple[str, str]:
    """
    Strongest practical Windows "no console flash" subprocess config:
      - CREATE_NO_WINDOW
      - STARTUPINFO w/ SW_HIDE
    """
    import subprocess

    creationflags = 0
    if hasattr(subprocess, "CREATE_NO_WINDOW"):
        creationflags |= subprocess.CREATE_NO_WINDOW  # type: ignore[attr-defined]

    si = subprocess.STARTUPINFO()
    si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    si.wShowWindow = 0  # SW_HIDE

    try:
        p = subprocess.run(
            args,
            cwd=str(cwd) if cwd else None,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
            shell=False,
            startupinfo=si,
            creationflags=creationflags,
            stdin=subprocess.DEVNULL,
        )
    except Exception as e:
        raise AppError(f"Failed to start process:\n{args[0]}\n\n{e}") from e

    out = p.stdout or ""
    err = p.stderr or ""
    if p.returncode != 0:
        raise AppError(
            f"Command failed (exit code {p.returncode}).\n\n"
            f"Command:\n  {' '.join(args)}\n\n"
            f"--- stdout (tail) ---\n{_tail(out)}\n\n"
            f"--- stderr (tail) ---\n{_tail(err)}"
        )
    return out, err


# Requests session with cooldown (metadata APIs)
class CooldownSession:
    def __init__(self, user_agent: str, cooldown_s: float = 0.8):
        self.s = requests.Session()
        self.s.headers.update({"User-Agent": user_agent})
        self.cooldown_s = max(0.0, float(cooldown_s))
        self._last = 0.0

    def _cooldown(self):
        if self.cooldown_s <= 0:
            return
        now = time.time()
        delta = now - self._last
        if delta < self.cooldown_s:
            time.sleep(self.cooldown_s - delta)
        self._last = time.time()

    def get(self, *args, **kwargs):
        self._cooldown()
        return self.s.get(*args, **kwargs)

    def post(self, *args, **kwargs):
        self._cooldown()
        return self.s.post(*args, **kwargs)


# Toolchain manager (temp BIN_DIR)
class Toolchain:
    def __init__(self, user_agent: str):
        self.s = requests.Session()
        self.s.headers.update({"User-Agent": user_agent})

    def ensure_ready(self) -> None:
        BIN_DIR.mkdir(parents=True, exist_ok=True)

        if not (FFMPEG_PATH.exists() and FFPROBE_PATH.exists()):
            self._download_and_extract_ffmpeg()

        self._ensure_fresh_binary(YTDLP_URL, YTDLP_PATH, is_zip=False)
        self._ensure_fresh_binary(DENO_ZIP_URL, DENO_PATH, is_zip=True, zip_member_name="deno.exe")

        os.environ["PATH"] = str(BIN_DIR) + os.pathsep + os.environ.get("PATH", "")

    def _is_stale(self, path: Path, max_age_s: int) -> bool:
        if not path.exists():
            return True
        return (time.time() - path.stat().st_mtime) > max_age_s

    def _download(self, url: str, dest: Path) -> None:
        dest.parent.mkdir(parents=True, exist_ok=True)
        tmp = dest.with_suffix(dest.suffix + ".part")
        with self.s.get(url, stream=True, timeout=90) as r:
            r.raise_for_status()
            with open(tmp, "wb") as f:
                for chunk in r.iter_content(chunk_size=1024 * 256):
                    if chunk:
                        f.write(chunk)
        tmp.replace(dest)

    def _ensure_fresh_binary(self, url: str, dest: Path, is_zip: bool, zip_member_name: Optional[str] = None) -> None:
        if is_zip:
            if not self._is_stale(dest, TOOL_REFRESH_SECONDS):
                return
            zip_path = BIN_DIR / (dest.stem + ".zip")
            self._download(url, zip_path)
            self._extract_zip_member(zip_path, zip_member_name or dest.name, dest)
            try:
                zip_path.unlink(missing_ok=True)
            except Exception:
                pass
        else:
            if not self._is_stale(dest, TOOL_REFRESH_SECONDS):
                return
            self._download(url, dest)

    def _extract_zip_member(self, zip_path: Path, member_name: str, out_path: Path) -> None:
        with zipfile.ZipFile(zip_path, "r") as z:
            candidates = [m for m in z.namelist() if Path(m).name.lower() == member_name.lower()]
            if not candidates:
                raise AppError(f"Zip did not contain {member_name}")
            member = candidates[0]
            tmp = out_path.with_suffix(".part")
            with z.open(member) as src, open(tmp, "wb") as dst:
                shutil.copyfileobj(src, dst)
            tmp.replace(out_path)

    def _download_and_extract_ffmpeg(self) -> None:
        zip_path = BIN_DIR / "ffmpeg-release-essentials.zip"
        self._download(FFMPEG_ZIP_URL, zip_path)

        ffmpeg_member = None
        ffprobe_member = None
        with zipfile.ZipFile(zip_path, "r") as z:
            for name in z.namelist():
                p = Path(name)
                if p.name.lower() == "ffmpeg.exe" and "bin" in p.parts:
                    ffmpeg_member = name
                elif p.name.lower() == "ffprobe.exe" and "bin" in p.parts:
                    ffprobe_member = name

            if not ffmpeg_member or not ffprobe_member:
                raise AppError("Could not locate ffmpeg.exe/ffprobe.exe inside the ffmpeg zip.")

            self._extract_specific_member(z, ffmpeg_member, FFMPEG_PATH)
            self._extract_specific_member(z, ffprobe_member, FFPROBE_PATH)

        try:
            zip_path.unlink(missing_ok=True)
        except Exception:
            pass

    def _extract_specific_member(self, z: zipfile.ZipFile, member: str, out_path: Path) -> None:
        tmp = out_path.with_suffix(".part")
        with z.open(member) as src, open(tmp, "wb") as dst:
            shutil.copyfileobj(src, dst)
        tmp.replace(out_path)


# Metadata structures
@dataclass
class TrackMeta:
    title: str = ""
    artist: str = ""
    album: str = ""
    album_artist: str = ""
    year: str = ""
    genre: str = ""
    track_number: str = ""
    track_total: str = ""
    disc_number: str = ""
    disc_total: str = ""
    isrc: str = ""
    itunes_track_id: str = ""
    artwork_url: str = ""
    artwork_jpeg: bytes = b""
    comment: str = ""  # Source URL
    source: str = ""


# iTunes + song.link helpers
def _norm(s: str) -> str:
    s = (s or "").lower()
    s = re.sub(r"[\(\)\[\]\{\}\-–—_:;,.!/?\\|]+", " ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def _strip_parens_soft(s: str) -> str:
    if not s:
        return ""
    keep_words = ("remix", "edit", "bootleg", "rework", "mix", "cover", "remaster", "remastered")
    if any(w in s.lower() for w in keep_words):
        return s
    return re.sub(r"\s*[\(\[].*?[\)\]]\s*", " ", s).strip()


def _drop_feat_tail(s: str) -> str:
    return re.sub(r"\s*\(?(feat\.|featuring|ft\.)\s+.+?\)?\s*$", "", s, flags=re.IGNORECASE).strip()


def itunes_search_variants(artist: str, title: str) -> List[str]:
    a = (artist or "").strip()
    t = (title or "").strip()
    variants: List[str] = []

    if a and t:
        variants.append(f"{a} {t}")
        variants.append(f"{t} {a}")

    a2 = _strip_parens_soft(a)
    t2 = _strip_parens_soft(t)
    if a2 and t2 and (a2 != a or t2 != t):
        variants.append(f"{a2} {t2}")
        variants.append(f"{t2} {a2}")

    a3 = _drop_feat_tail(a2 or a)
    t3 = _drop_feat_tail(t2 or t)
    if a3 and t3 and (a3 != a or t3 != t):
        variants.append(f"{a3} {t3}")
        variants.append(f"{t3} {a3}")

    out: List[str] = []
    seen = set()
    for v in variants:
        v2 = v.strip()
        if v2 and v2.lower() not in seen:
            seen.add(v2.lower())
            out.append(v2)
    return out[:4]


def itunes_search(cs: CooldownSession, term: str, limit: int = 12) -> Dict[str, Any]:
    url = "https://itunes.apple.com/search"
    params = {"term": term, "media": "music", "entity": "song", "limit": str(limit)}
    r = cs.get(url, params=params, timeout=25)
    r.raise_for_status()
    return r.json()


def itunes_lookup(cs: CooldownSession, track_id: str) -> Dict[str, Any]:
    url = "https://itunes.apple.com/lookup"
    params = {"id": track_id}
    r = cs.get(url, params=params, timeout=25)
    r.raise_for_status()
    return r.json()


def songlink_lookup(cs: CooldownSession, query_url: str) -> Dict[str, Any]:
    url = "https://api.song.link/v1-alpha.1/links"
    params = {"url": query_url}
    r = cs.get(url, params=params, timeout=25)
    r.raise_for_status()
    return r.json()


def songlink_extract_itunes_id(payload: Dict[str, Any]) -> str:
    if not isinstance(payload, dict):
        return ""
    links = payload.get("linksByPlatform") or {}
    candidate_urls = []
    for key in ("appleMusic", "itunes"):
        v = links.get(key)
        if isinstance(v, dict) and v.get("url"):
            candidate_urls.append(v["url"])

    entities = payload.get("entitiesByUniqueId") or {}
    for ent in entities.values():
        if isinstance(ent, dict) and ent.get("platform") in ("appleMusic", "itunes") and ent.get("url"):
            candidate_urls.append(ent["url"])

    for u in candidate_urls:
        m = re.search(r"/id(\d+)", u)
        if m:
            return m.group(1)
        m = re.search(r"[?&]i=(\d+)", u)
        if m:
            return m.group(1)
    return ""


def token_jaccard(a: str, b: str) -> float:
    ta = set(_norm(a).split())
    tb = set(_norm(b).split())
    if not ta and not tb:
        return 1.0
    if not ta or not tb:
        return 0.0
    return len(ta & tb) / max(1, len(ta | tb))


def pick_best_itunes_result(results: List[Dict[str, Any]], want_artist: str, want_title: str) -> Optional[Dict[str, Any]]:
    wa = _norm(want_artist)
    wt = _norm(want_title)

    best = None
    best_score = -999

    for item in results:
        a = _norm(item.get("artistName", ""))
        t = _norm(item.get("trackName", ""))

        title_sim = token_jaccard(want_title, item.get("trackName", "") or "")
        score = 0

        if wt and wt in t:
            score += 6
        if wa and wa in a:
            score += 6
        if wt and t == wt:
            score += 3
        if wa and a == wa:
            score += 3
        if item.get("kind") == "song":
            score += 1
        if "karaoke" in t:
            score -= 2

        if title_sim < 0.20 and wt:
            score -= 8
        elif title_sim < 0.35 and wt:
            score -= 3

        if score > best_score:
            best_score = score
            best = item

    return best


def upgrade_artwork_url(artwork_url: str) -> str:
    if not artwork_url:
        return ""
    return re.sub(r"/\d+x\d+bb\.(jpg|png)$", "/1200x1200bb.jpg", artwork_url, flags=re.IGNORECASE)


def download_artwork(cs: CooldownSession, url: str) -> bytes:
    if not url:
        return b""
    r = cs.get(url, timeout=25)
    r.raise_for_status()
    return r.content


def meta_from_itunes_item(item: Dict[str, Any]) -> TrackMeta:
    m = TrackMeta()
    m.title = item.get("trackName", "") or ""
    m.artist = item.get("artistName", "") or ""
    m.album_artist = m.artist
    m.album = item.get("collectionName", "") or ""
    m.genre = item.get("primaryGenreName", "") or ""

    rel = item.get("releaseDate", "")
    if isinstance(rel, str) and len(rel) >= 4 and rel[:4].isdigit():
        m.year = rel[:4]

    tn = item.get("trackNumber")
    tc = item.get("trackCount")
    if tn is not None:
        m.track_number = str(tn)
    if tc is not None:
        m.track_total = str(tc)

    track_id = item.get("trackId")
    if track_id:
        m.itunes_track_id = str(track_id)

    art = item.get("artworkUrl100") or item.get("artworkUrl60") or ""
    m.artwork_url = upgrade_artwork_url(art) if art else ""
    m.source = "iTunes"
    return m


# JioSaavn API (unofficial, via saavnapi-nine)
def jiosaavn_search(cs: CooldownSession, query: str) -> Optional[TrackMeta]:
    q = (query or "").strip()
    if not q:
        return None
    try:
        url = "https://saavnapi-nine.vercel.app/result/"
        params = {"query": q, "lyrics": "false"}
        r = cs.get(url, params=params, timeout=25)
        r.raise_for_status()
        data = r.json()
    except Exception:
        return None

    items = None
    if isinstance(data, dict):
        if isinstance(data.get("data"), list):
            items = data["data"]
        elif isinstance(data.get("results"), list):
            items = data["results"]
        else:
            songs = data.get("songs")
            if isinstance(songs, dict) and isinstance(songs.get("data"), list):
                items = songs["data"]

    if not items:
        return None

    first = None
    for it in items[:10]:
        if isinstance(it, dict) and (it.get("title") or it.get("song") or it.get("name")):
            first = it
            break
    if not first:
        return None

    m = TrackMeta()
    m.title = (first.get("title") or first.get("song") or first.get("name") or "").strip()
    m.artist = (first.get("singers") or first.get("primaryArtists") or first.get("artist") or "").strip()
    m.album = (first.get("album") or first.get("albumName") or "").strip()
    m.year = str(first.get("year") or "").strip()
    m.artwork_url = (first.get("image_url") or first.get("image") or first.get("imageUrl") or "").strip()
    if m.artwork_url:
        try:
            m.artwork_jpeg = download_artwork(cs, m.artwork_url)
        except Exception:
            m.artwork_jpeg = b""
    m.album = clean_album_name(m.album)
    m.album_artist = m.artist or ""
    m.source = "JioSaavn"
    return m if (m.title or m.artist) else None


# Spotify SpotAPI integration (best-effort)
def spotapi_quick_search(artist: str, title: str) -> Optional[TrackMeta]:
    q_artist = (artist or "").strip()
    q_title = (title or "").strip()
    term = " ".join([x for x in [q_artist, q_title] if x]).strip()
    if not term:
        return None

    try:
        import spotapi  # type: ignore
    except Exception:
        return None

    candidates: List[dict] = []

    for attr in ("Public", "PublicClient", "PublicSearch", "Search", "Song", "PublicSong"):
        try:
            cls = getattr(spotapi, attr, None)
            if cls is None:
                continue
            obj = cls()  # type: ignore
            for meth in ("search", "search_song", "search_track", "query"):
                fn = getattr(obj, meth, None)
                if callable(fn):
                    try:
                        res = fn(term)  # type: ignore
                        if isinstance(res, dict):
                            candidates.append(res)
                        elif isinstance(res, list):
                            candidates.extend([x for x in res if isinstance(x, dict)])
                    except Exception:
                        pass
        except Exception:
            pass

    try:
        from spotapi import public as spot_public  # type: ignore

        for attr in ("Public", "Search", "Song"):
            cls = getattr(spot_public, attr, None)
            if cls:
                try:
                    obj = cls()  # type: ignore
                    for meth in ("search", "search_song", "search_track", "query"):
                        fn = getattr(obj, meth, None)
                        if callable(fn):
                            try:
                                res = fn(term)  # type: ignore
                                if isinstance(res, dict):
                                    candidates.append(res)
                                elif isinstance(res, list):
                                    candidates.extend([x for x in res if isinstance(x, dict)])
                            except Exception:
                                pass
                except Exception:
                    pass
    except Exception:
        pass

    def dig_tracks(x: Any) -> List[dict]:
        out: List[dict] = []
        if isinstance(x, dict):
            for k in ("tracks", "items", "data", "results"):
                v = x.get(k)
                if isinstance(v, list):
                    out.extend([i for i in v if isinstance(i, dict)])
                if isinstance(v, dict):
                    out.extend(dig_tracks(v))
            for v in x.values():
                out.extend(dig_tracks(v))
        elif isinstance(x, list):
            for it in x:
                out.extend(dig_tracks(it))
        return out

    tracks: List[dict] = []
    for c in candidates:
        tracks.extend(dig_tracks(c))

    def score(t: dict) -> int:
        name = _norm(t.get("name") or t.get("title") or "")
        arts = ""
        a = t.get("artists")
        if isinstance(a, list) and a and isinstance(a[0], dict):
            arts = _norm(a[0].get("name") or "")
        elif isinstance(a, str):
            arts = _norm(a)

        want_t = _norm(q_title)
        want_a = _norm(q_artist)
        s = 0
        if want_t and want_t in name:
            s += 6
        if want_a and want_a in arts:
            s += 6
        if want_t and name == want_t:
            s += 3
        if want_a and arts == want_a:
            s += 3

        if want_t:
            ts = token_jaccard(q_title, t.get("name") or t.get("title") or "")
            if ts < 0.20:
                s -= 8
            elif ts < 0.35:
                s -= 3
        return s

    if not tracks:
        return None

    tracks.sort(key=score, reverse=True)
    top = tracks[0]

    m = TrackMeta()
    m.title = (top.get("name") or top.get("title") or "").strip()

    a = top.get("artists")
    if isinstance(a, list) and a:
        names = []
        for it in a:
            if isinstance(it, dict) and it.get("name"):
                names.append(str(it["name"]).strip())
        m.artist = ", ".join([n for n in names if n])
    elif isinstance(a, str):
        m.artist = a.strip()

    alb = top.get("album")
    if isinstance(alb, dict):
        m.album = (alb.get("name") or "").strip()
        imgs = alb.get("images")
        if isinstance(imgs, list) and imgs:
            url = ""
            for im in imgs:
                if isinstance(im, dict) and im.get("url"):
                    url = im["url"]
                    break
            m.artwork_url = url.strip()
    else:
        m.album = (top.get("album") or "").strip()

    rel = ""
    if isinstance(alb, dict):
        rel = alb.get("release_date") or ""
    rel = str(rel)
    if len(rel) >= 4 and rel[:4].isdigit():
        m.year = rel[:4]

    m.album = clean_album_name(m.album)
    m.album_artist = m.artist or ""
    m.source = "SpotAPI"
    return m if (m.title or m.artist) else None


# ffmpeg/ffprobe helpers
def ffprobe_duration_seconds(path: Path) -> float:
    out, _ = run_cmd(
        [
            str(FFPROBE_PATH),
            "-v",
            "error",
            "-show_entries",
            "format=duration",
            "-of",
            "default=noprint_wrappers=1:nokey=1",
            str(path),
        ]
    )
    try:
        return float(out.strip())
    except Exception:
        return 0.0


def wav_slice_normalized(src_wav: Path, dst_wav: Path, start_s: float, dur_s: float = 10.0) -> None:
    run_cmd(
        [
            str(FFMPEG_PATH),
            "-y",
            "-ss",
            f"{start_s:.3f}",
            "-t",
            f"{dur_s:.3f}",
            "-i",
            str(src_wav),
            "-af",
            "loudnorm=I=-16:TP=-1.5:LRA=11",
            "-ac",
            "2",
            "-ar",
            "44100",
            str(dst_wav),
        ]
    )


def wav_to_mp3_high_compat(src_wav: Path, dst_mp3: Path) -> None:
    run_cmd(
        [
            str(FFMPEG_PATH),
            "-y",
            "-i",
            str(src_wav),
            "-vn",
            "-ac",
            "2",
            "-ar",
            "44100",
            "-c:a",
            "libmp3lame",
            "-b:a",
            "128k",
            "-write_id3v2",
            "1",
            "-id3v2_version",
            "3",
            str(dst_mp3),
        ]
    )


def to_wav_for_analysis(src: Path, dst: Path) -> None:
    run_cmd(
        [
            str(FFMPEG_PATH),
            "-y",
            "-i",
            str(src),
            "-vn",
            "-ac",
            "2",
            "-ar",
            "44100",
            "-c:a",
            "pcm_s16le",
            str(dst),
        ]
    )


# Shazam recognition (Advanced pipeline)
def shazam_recognize_wav(wav_path: Path) -> Dict[str, Any]:
    try:
        from shazamio import Shazam
    except Exception as e:
        raise AppError("Advanced Metadata requires 'shazamio'.\n\nInstall it with:\n  pip install shazamio") from e

    async def _do() -> Dict[str, Any]:
        shazam = Shazam()
        if hasattr(shazam, "recognize") and callable(getattr(shazam, "recognize")):
            return await shazam.recognize(str(wav_path))  # type: ignore[attr-defined]
        return await shazam.recognize_song(str(wav_path))  # type: ignore[attr-defined]

    loop = asyncio.new_event_loop()
    try:
        asyncio.set_event_loop(loop)
        return loop.run_until_complete(_do())
    finally:
        try:
            loop.close()
        except Exception:
            pass


def _shazam_extract_track(payload: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    if not isinstance(payload, dict):
        return None
    track = payload.get("track")
    if isinstance(track, dict) and ("title" in track or "subtitle" in track):
        return track
    if "title" in payload and "subtitle" in payload:
        return payload
    return None


def extract_shazam_fields(payload: Dict[str, Any]) -> Tuple[str, str, str]:
    track = payload.get("track") if isinstance(payload, dict) else None
    if not isinstance(track, dict) and isinstance(payload, dict) and "title" in payload:
        track = payload
    if not isinstance(track, dict):
        return "", "", ""

    title = (track.get("title") or "").strip()
    artist = (track.get("subtitle") or "").strip()

    isrc = ""
    sections = track.get("sections")
    if isinstance(sections, list):
        for sec in sections:
            meta = sec.get("metadata") if isinstance(sec, dict) else None
            if isinstance(meta, list):
                for m in meta:
                    if isinstance(m, dict) and (m.get("title") or "").lower() == "isrc":
                        isrc = (m.get("text") or "").strip()
                        break
            if isrc:
                break

    return title, artist, isrc


def shazam_best_guess_from_wav(src_wav: Path, work_dir: Path, progress_cb) -> TrackMeta:
    duration = ffprobe_duration_seconds(src_wav)
    if duration <= 12:
        raise AppError("Audio is too short to recognize reliably.")

    slice_dur = 10.0
    max_start = max(0.0, duration - slice_dur - 0.5)

    candidates = [max(0.0, min(max_start, 8.0))]
    candidates.append(max(0.0, min(max_start, duration * 0.40)))
    candidates.append(max(0.0, min(max_start, duration * 0.70)))

    offsets: List[float] = []
    for t in candidates:
        if not offsets or all(abs(t - o) > 5.0 for o in offsets):
            offsets.append(t)
    offsets = offsets[:3]

    votes: Dict[str, int] = {}
    tracks: Dict[str, Dict[str, Any]] = {}

    def key_for(track: Dict[str, Any]) -> str:
        return f"{_norm(track.get('title',''))} — {_norm(track.get('subtitle',''))}".strip(" —")

    def has_isrc(track: Dict[str, Any]) -> bool:
        _, _, isrc = extract_shazam_fields({"track": track})
        return bool(isrc)

    for i, start_s in enumerate(offsets, 1):
        progress_cb(f"Shazam: slice {i}/{len(offsets)}…")
        slice_wav = work_dir / f"slice_{i}.wav"
        wav_slice_normalized(src_wav, slice_wav, start_s, slice_dur)
        try:
            payload = shazam_recognize_wav(slice_wav)
        finally:
            try:
                slice_wav.unlink(missing_ok=True)
            except Exception:
                pass

        tr = _shazam_extract_track(payload)
        if not tr:
            continue
        k = key_for(tr)
        if not k.strip():
            continue
        tracks.setdefault(k, tr)
        votes[k] = votes.get(k, 0) + 1

    if not votes:
        return TrackMeta()

    items = list(votes.items())
    items.sort(key=lambda kv: (kv[1], has_isrc(tracks[kv[0]])), reverse=True)
    best_key = items[0][0]
    best_track = tracks[best_key]

    stitle, sartist, sisrc = extract_shazam_fields({"track": best_track})
    return TrackMeta(title=stitle, artist=sartist, album_artist=sartist, isrc=sisrc, source="Shazam")


# ID3v2.3 tagging (CD-like)
def write_id3_tags_v23(mp3_path: Path, meta: TrackMeta) -> None:
    try:
        from mutagen.id3 import (
            ID3,
            ID3NoHeaderError,
            TIT2,
            TPE1,
            TPE2,
            TALB,
            TRCK,
            TPOS,
            TCON,
            TYER,
            TSRC,
            COMM,
            APIC,
            TXXX,
        )
    except Exception as e:
        raise AppError("Tag writing requires 'mutagen'.\n\nInstall it with:\n  pip install mutagen") from e

    ENC = 1  # UTF-16 for ID3v2.3

    try:
        tags = ID3(str(mp3_path))
    except ID3NoHeaderError:
        tags = ID3()

    def set_one(frame):
        tags.delall(frame.FrameID)
        tags.add(frame)

    def set_txxx(desc: str, value: str):
        tags.delall(f"TXXX:{desc}")
        if value:
            tags.add(TXXX(encoding=ENC, desc=desc, text=value))

    if meta.title:
        set_one(TIT2(encoding=ENC, text=meta.title))
    if meta.artist:
        set_one(TPE1(encoding=ENC, text=meta.artist))
    if meta.album_artist:
        set_one(TPE2(encoding=ENC, text=meta.album_artist))
    if meta.album:
        set_one(TALB(encoding=ENC, text=meta.album))

    if meta.track_number:
        tr = meta.track_number.strip()
        if meta.track_total and "/" not in tr:
            tr = f"{tr}/{meta.track_total.strip()}"
        set_one(TRCK(encoding=ENC, text=tr))

    if meta.disc_number:
        ds = meta.disc_number.strip()
        if meta.disc_total and "/" not in ds:
            ds = f"{ds}/{meta.disc_total.strip()}"
        set_one(TPOS(encoding=ENC, text=ds))

    if meta.genre:
        set_one(TCON(encoding=ENC, text=meta.genre))

    if meta.year:
        y = meta.year.strip()
        m = re.match(r"^(\d{4})", y)
        if m:
            y = m.group(1)
        set_one(TYER(encoding=ENC, text=y))

    if meta.isrc:
        tags.delall("TSRC")
        tags.add(TSRC(encoding=ENC, text=meta.isrc))

    if meta.comment:
        tags.delall("COMM")
        tags.add(COMM(encoding=ENC, lang="eng", desc="Source", text=meta.comment))

    set_txxx("ARTISTS", meta.artist or "")
    set_txxx("ALBUMARTIST", meta.album_artist or "")
    if meta.isrc:
        set_txxx("ISRC", meta.isrc)
        set_txxx("TSRC", meta.isrc)

    if meta.artwork_jpeg:
        tags.delall("APIC")
        tags.add(
            APIC(
                encoding=ENC,
                mime="image/jpeg",
                type=3,
                desc="Cover",
                data=meta.artwork_jpeg,
            )
        )

    tags.save(str(mp3_path), v2_version=3)


# Enrichment: merge helper
def merge_meta(base: TrackMeta, incoming: TrackMeta, prefer_incoming: bool = True) -> TrackMeta:
    out = TrackMeta(**base.__dict__)
    for field in (
        "title",
        "artist",
        "album",
        "album_artist",
        "year",
        "genre",
        "track_number",
        "track_total",
        "disc_number",
        "disc_total",
        "isrc",
        "itunes_track_id",
        "artwork_url",
        "comment",
    ):
        a = getattr(out, field)
        b = getattr(incoming, field)

        if prefer_incoming:
            # fill empties
            if b and not a:
                setattr(out, field, b)
            # allow "strong" fields to upgrade even when already present
            elif b and a and field in ("album", "year", "genre", "itunes_track_id", "artwork_url", "isrc"):
                setattr(out, field, b)
        else:
            if not a and b:
                setattr(out, field, b)

    if incoming.artwork_jpeg and not out.artwork_jpeg:
        out.artwork_jpeg = incoming.artwork_jpeg

    out.album = clean_album_name(out.album)
    if not out.album_artist:
        out.album_artist = out.artist or ""
    return out


def downloads_dir() -> Path:
    return Path(os.environ.get("USERPROFILE", str(Path.home()))) / "Downloads"


def unique_path(dest_dir: Path, base_name: str) -> Path:
    dest_dir.mkdir(parents=True, exist_ok=True)
    safe = sanitize_filename(base_name)
    dest = dest_dir / f"{safe}.mp3"
    if not dest.exists():
        return dest
    i = 2
    while True:
        cand = dest_dir / f"{safe} ({i}).mp3"
        if not cand.exists():
            return cand
        i += 1


def build_display_filename(meta: TrackMeta, track_prefix: str = "") -> str:
    a = (meta.artist or "").strip()
    t = (meta.title or "").strip()
    core = f"{a} - {t}".strip(" -")
    if not core:
        core = t or a or "audio"
    if track_prefix:
        return f"{track_prefix} {core}".strip()
    return core


# URL helpers: playlist detection + normalization
@dataclass
class UrlIntent:
    url: str
    is_playlist: bool
    has_list_param: bool


def classify_youtube_url(url: str) -> UrlIntent:
    u = (url or "").strip()
    try:
        p = urlparse(u)
    except Exception:
        return UrlIntent(url=u, is_playlist=False, has_list_param=False)

    qs = parse_qs(p.query or "")
    has_list = "list" in qs and bool(qs.get("list", [""])[0])

    is_playlist = False
    if "youtube.com" in (p.netloc or "").lower() and p.path.lower().startswith("/playlist"):
        is_playlist = True
    if has_list:
        is_playlist = True

    return UrlIntent(url=u, is_playlist=is_playlist, has_list_param=has_list)


def strip_playlist_from_watch_url(url: str) -> str:
    p = urlparse(url)
    qs = parse_qs(p.query or "")
    for k in ("list", "index", "start_radio", "radio", "pp"):
        if k in qs:
            qs.pop(k, None)
    new_query = urlencode({k: v[0] for k, v in qs.items() if v}, doseq=False)
    return urlunparse((p.scheme, p.netloc, p.path, p.params, new_query, p.fragment))


def extract_youtube_id(url: str) -> str:
    u = (url or "").strip()
    try:
        p = urlparse(u)
    except Exception:
        return ""
    host = (p.netloc or "").lower()
    if "youtu.be" in host:
        vid = (p.path or "").strip("/").split("/")[0]
        return vid
    qs = parse_qs(p.query or "")
    v = qs.get("v", [""])[0]
    if v:
        return v
    if (p.path or "").lower().startswith("/shorts/"):
        return (p.path or "").split("/shorts/")[-1].split("/")[0]
    return ""


# Connectivity check (hard requirement)
def check_internet_required() -> None:
    try:
        r = requests.get(CONNECT_TEST_URL, timeout=6, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        return
    except Exception as e:
        raise AppError(
            "Internet connection required.\n\n"
            f"Connectivity test failed:\n  {CONNECT_TEST_URL}\n\n"
            f"Details:\n  {e}"
        )


def itunes_candidates(cs: CooldownSession, artist: str, title: str, limit: int = 6) -> List[TrackMeta]:
    out: List[TrackMeta] = []
    terms = itunes_search_variants(artist, title)
    for term in terms[:2]:
        try:
            data = itunes_search(cs, term, limit=limit)
            res = data.get("results") or []
            for item in res:
                if isinstance(item, dict) and item.get("trackName") and item.get("artistName"):
                    tm = meta_from_itunes_item(item)
                    if title and token_jaccard(title, tm.title) < 0.18:
                        continue
                    out.append(tm)
        except Exception:
            continue
        if len(out) >= limit:
            break
    seen = set()
    ded: List[TrackMeta] = []
    for m in out:
        k = f"{_norm(m.artist)}|{_norm(m.title)}|{_norm(m.album)}"
        if k in seen:
            continue
        seen.add(k)
        ded.append(m)
    return ded[:limit]


def ensure_artwork(cs: CooldownSession, m: TrackMeta) -> TrackMeta:
    if m.artwork_jpeg:
        return m
    if m.artwork_url:
        try:
            m.artwork_jpeg = download_artwork(cs, m.artwork_url)
        except Exception:
            m.artwork_jpeg = b""
    return m


def meta_match(a: TrackMeta, b: TrackMeta) -> bool:
    # Strong IDs
    if a.isrc and b.isrc and a.isrc.strip().upper() == b.isrc.strip().upper():
        return True
    if a.itunes_track_id and b.itunes_track_id and a.itunes_track_id == b.itunes_track_id:
        return True

    # Fallback similarity
    ts = token_jaccard(a.title, b.title)
    asim = token_jaccard(a.artist, b.artist) if a.artist and b.artist else 0.6
    return ts >= 0.62 and asim >= 0.55


def format_candidate_label(m: TrackMeta) -> str:
    a = (m.artist or "").strip()
    t = (m.title or "").strip()
    src = (m.source or "").strip() or "Unknown"
    base = f"{a} — {t}".strip(" —")
    if not base:
        base = "Unknown"
    return f"{base} ({src})"


def quick_itunes_enrich(cs: CooldownSession, base: TrackMeta) -> TrackMeta:
    meta = TrackMeta(**base.__dict__)
    chosen: Optional[Dict[str, Any]] = None

    if meta.isrc:
        try:
            data = itunes_search(cs, f"isrc:{meta.isrc}", limit=8)
            res = data.get("results") or []
            if res:
                chosen = res[0]
        except Exception:
            pass

    if not chosen and meta.artist and meta.title:
        terms = itunes_search_variants(meta.artist, meta.title)
        if terms:
            try:
                data = itunes_search(cs, terms[0], limit=10)
                res = data.get("results") or []
                if res:
                    chosen = pick_best_itunes_result(res, meta.artist, meta.title) or res[0]
            except Exception:
                pass

    if chosen:
        filled = meta_from_itunes_item(chosen)
        meta = merge_meta(meta, filled, prefer_incoming=True)
        if meta.itunes_track_id:
            try:
                data = itunes_lookup(cs, meta.itunes_track_id)
                res = data.get("results") or []
                if res:
                    meta = merge_meta(meta, meta_from_itunes_item(res[0]), prefer_incoming=True)
            except Exception:
                pass

        meta = ensure_artwork(cs, meta)

    meta.album = clean_album_name(meta.album)
    if not meta.album_artist:
        meta.album_artist = meta.artist or ""
    meta.source = meta.source or "iTunes"
    return meta


def advanced_enrich_all_sources(
    cs: CooldownSession,
    youtube_url: str,
    base_from_title: TrackMeta,
    wav_path: Path,
    work_dir: Path,
    progress_cb,
) -> Dict[str, TrackMeta]:
    """
    Returns a dict of source metas (best-effort):
      - YouTubeTitle
      - SongLink (just fills itunes_track_id if found)
      - Shazam
      - iTunesBest (search/lookup best)
      - SpotAPI
      - JioSaavn
    """
    sources: Dict[str, TrackMeta] = {}

    base = TrackMeta(**base_from_title.__dict__)
    base.source = "YouTubeTitle"
    sources["YouTubeTitle"] = base

    # song.link
    progress_cb("song.link: resolving…")
    try:
        payload = songlink_lookup(cs, youtube_url)
        it_id = songlink_extract_itunes_id(payload)
        if it_id:
            sl = TrackMeta(**base.__dict__)
            sl.itunes_track_id = it_id
            sl.source = "SongLink"
            sources["SongLink"] = sl
    except Exception:
        pass

    # Shazam
    progress_cb("Shazam: matching…")
    try:
        shz = shazam_best_guess_from_wav(wav_path, work_dir, progress_cb)
        if shz.title or shz.artist or shz.isrc:
            shz.comment = base.comment
            shz.source = "Shazam"
            sources["Shazam"] = shz
    except Exception:
        pass

    # iTunes best (use ISRC if shazam gives it)
    progress_cb("iTunes: searching…")
    it_base = TrackMeta(**base.__dict__)
    if "Shazam" in sources and sources["Shazam"].isrc:
        it_base.isrc = sources["Shazam"].isrc
    if "SongLink" in sources and sources["SongLink"].itunes_track_id:
        it_base.itunes_track_id = sources["SongLink"].itunes_track_id

    it_best = quick_itunes_enrich(cs, it_base)
    if it_best.title or it_best.artist:
        it_best.comment = base.comment
        it_best.source = "iTunes"
        sources["iTunesBest"] = it_best

    # Spotify SpotAPI
    progress_cb("Spotify (SpotAPI): searching…")
    sp = spotapi_quick_search(it_best.artist or base.artist, it_best.title or base.title)
    if sp:
        sp.comment = base.comment
        sp.source = "SpotAPI"
        sources["SpotAPI"] = sp

    # JioSaavn
    progress_cb("JioSaavn: searching…")
    js = jiosaavn_search(cs, f"{it_best.artist or base.artist} {it_best.title or base.title}".strip())
    if js:
        js.comment = base.comment
        js.source = "JioSaavn"
        sources["JioSaavn"] = js

    return sources


def build_review_candidates(
    cs: CooldownSession,
    yt_raw: str,
    yt_artist: str,
    yt_title: str,
    base_current: TrackMeta,
    source_metas: Dict[str, TrackMeta],
    extra_itunes: List[TrackMeta],
) -> List[TrackMeta]:
    """
    Build a deduped list of candidates for the combo box, with artwork prefetched where possible.
    """
    merged: List[TrackMeta] = []

    # Current merged meta first
    cur = TrackMeta(**base_current.__dict__)
    cur.source = cur.source or "Current"
    merged.append(cur)

    # Parsed YT title candidate
    yt_candidate = TrackMeta(
        title=yt_title or (yt_raw or ""),
        artist=yt_artist or "",
        album_artist=yt_artist or "",
        comment=base_current.comment,
        source="YouTubeTitle",
    )
    merged.append(yt_candidate)

    # Add each source meta
    for key in ("iTunesBest", "Shazam", "SpotAPI", "JioSaavn", "SongLink"):
        m = source_metas.get(key)
        if m and (m.title or m.artist or m.itunes_track_id):
            merged.append(TrackMeta(**m.__dict__))

    # Extra iTunes candidates (search results)
    for m in extra_itunes:
        merged.append(TrackMeta(**m.__dict__))

    # Dedup by artist+title+album+source-ish
    seen = set()
    out: List[TrackMeta] = []
    for m in merged:
        k = f"{_norm(m.artist)}|{_norm(m.title)}|{_norm(m.album)}|{_norm(m.source)}"
        if k in seen:
            continue
        seen.add(k)
        out.append(m)

    # Prefetch artwork for top options so dialog can show it instantly
    for m in out[:10]:
        ensure_artwork(cs, m)

    return out[:10]


def enrich_after_user_choice(
    cs: CooldownSession,
    chosen: TrackMeta,
    other_sources: List[TrackMeta],
) -> TrackMeta:
    """
    Anchor to chosen, then enrich + dedupe:
      - if iTunes ID exists: lookup
      - else: iTunes search
      - SpotAPI + JioSaavn
      - merge matching sources to avoid unrelated overwrites
    """
    anchor = TrackMeta(**chosen.__dict__)

    # Strong: iTunes lookup/search using anchor
    it = quick_itunes_enrich(cs, anchor)
    it.comment = anchor.comment
    anchor = merge_meta(anchor, it, prefer_incoming=True)

    # Try Spot/Jio based on anchor
    sp = spotapi_quick_search(anchor.artist, anchor.title)
    if sp:
        sp.comment = anchor.comment
        anchor = merge_meta(anchor, sp, prefer_incoming=False)

    js = jiosaavn_search(cs, f"{anchor.artist} {anchor.title}".strip())
    if js:
        js.comment = anchor.comment
        anchor = merge_meta(anchor, js, prefer_incoming=False)

    # Merge in other sources if they look like the same track
    for m in other_sources:
        if not (m.title or m.artist or m.isrc or m.itunes_track_id):
            continue
        if meta_match(anchor, m):
            anchor = merge_meta(anchor, m, prefer_incoming=False)

    # Final artwork ensure
    ensure_artwork(cs, anchor)

    anchor.album = clean_album_name(anchor.album)
    if not anchor.album_artist:
        anchor.album_artist = anchor.artist or ""
    return anchor


# Worker: download + tag
class PipelineWorker(QtCore.QObject):
    progress_text = QtCore.Signal(str)
    progress_value = QtCore.Signal(int)
    error = QtCore.Signal(str)
    finished = QtCore.Signal(list)  # list of saved output paths (strings)

    # Metadata review request to UI thread
    review_needed = QtCore.Signal(dict)  # payload includes request_id + candidates details

    def __init__(self, url: str, advanced: bool, playlist_mode: str):
        super().__init__()
        self.url = url
        self.advanced = bool(advanced)
        self.playlist_mode = playlist_mode  # "single" or "playlist"
        self.cs = CooldownSession(USER_AGENT, cooldown_s=REQUEST_COOLDOWN_S)
        self.run_root = Path(tempfile.mkdtemp(prefix=f"{APP_NAME}_run_"))

        # Review coordination
        self._review_lock = threading.Lock()
        self._review_event: Optional[threading.Event] = None
        self._review_selected_index: int = 0
        self._review_request_id: str = ""

        # Store candidates for current review request
        self._review_candidates: List[TrackMeta] = []

    def _set(self, pct: int, text: str):
        self.progress_value.emit(int(max(0, min(100, pct))))
        self.progress_text.emit(text)

    def _set_playlist_progress(self, total: int, idx: int, stage_pct: int, msg: str):
        per = 100.0 / max(1, total)
        overall = int((idx - 1) * per + (stage_pct / 100.0) * per)
        overall = max(0, min(100, overall))
        self._set(overall, f"Track {idx}/{total}: {msg}")

    @QtCore.Slot(str, str, object)
    def receive_review_result(self, request_id: str, chosen_key: str, _unused: object = None):
        # IMPORTANT: This must run even while worker thread is "busy".
        # We connect via DirectConnection in the UI to avoid deadlock.
        with self._review_lock:
            if not self._review_event or request_id != self._review_request_id:
                return
            try:
                self._review_selected_index = int(chosen_key)
            except Exception:
                self._review_selected_index = 0
            self._review_event.set()

    def _request_review_blocking(
        self,
        yt_raw: str,
        yt_artist: str,
        yt_title: str,
        candidates: List[TrackMeta],
    ) -> TrackMeta:
        request_id = f"rev_{int(time.time()*1000)}_{os.getpid()}"
        evt = threading.Event()

        with self._review_lock:
            self._review_request_id = request_id
            self._review_event = evt
            self._review_selected_index = 0
            self._review_candidates = candidates

        # Build payload with detail fields for UI
        payload_candidates = []
        for i, m in enumerate(candidates):
            payload_candidates.append(
                {
                    "idx": i,
                    "label": format_candidate_label(m),
                    "title": m.title,
                    "artist": m.artist,
                    "album": m.album,
                    "year": m.year,
                    "source": m.source,
                    "artwork_jpeg": m.artwork_jpeg,  # raw bytes (Qt can load)
                }
            )

        payload = {
            "request_id": request_id,
            "yt_raw": yt_raw or "",
            "yt_parsed": f"{(yt_artist or '').strip()} — {(yt_title or '').strip()}".strip(" —"),
            "candidates": payload_candidates,
        }
        self.review_needed.emit(payload)

        evt.wait()  # safe now (DirectConnection sets event without needing worker event loop)

        with self._review_lock:
            sel = max(0, min(len(candidates) - 1, self._review_selected_index))
            self._review_event = None
            self._review_request_id = ""
            chosen = candidates[sel]

        return chosen

    @QtCore.Slot()
    def run(self):
        try:
            outs = self._run_impl()
            self.finished.emit([str(p) for p in outs])
        except AppError as e:
            self.error.emit(str(e))
        except Exception:
            self.error.emit("An unexpected error occurred.\n\n" + traceback.format_exc())
        finally:
            try:
                shutil.rmtree(self.run_root, ignore_errors=True)
            except Exception:
                pass

    def _run_impl(self) -> List[Path]:
        self._set(2, "Checking internet…")
        check_internet_required()

        self._set(6, "Preparing tools…")
        Toolchain(USER_AGENT).ensure_ready()

        if self.playlist_mode == "playlist":
            self._set(10, "Reading playlist…")
            pl_title, entries = self._ytdlp_list_playlist(self.url)

            pl_title_line = sanitize_filename(pl_title or "") or "Playlist"
            folder = downloads_dir() / pl_title_line
            folder.mkdir(parents=True, exist_ok=True)

            saved: List[Path] = []
            total = max(1, len(entries))
            folder_maybe_generic = (pl_title_line.strip().lower() == "playlist")

            for idx, vid_url in enumerate(entries, 1):
                self._set_playlist_progress(total, idx, 0, "Starting…")
                out_path, final_meta = self._process_single_video(
                    vid_url,
                    out_dir=folder,
                    allow_playlist=False,
                    playlist_index=idx,
                    playlist_total=total,
                    progress_mapper=lambda sp, msg, _idx=idx: self._set_playlist_progress(total, _idx, sp, msg),
                )
                saved.append(out_path)

                if folder_maybe_generic and idx == 1:
                    alb = sanitize_filename(final_meta.album or "")
                    if alb and alb.lower() != "playlist":
                        desired = downloads_dir() / alb
                        if desired != folder:
                            try:
                                desired.mkdir(parents=True, exist_ok=True)
                                for item in folder.iterdir():
                                    shutil.move(str(item), str(desired / item.name))
                                try:
                                    folder.rmdir()
                                except Exception:
                                    pass
                                folder = desired
                            except Exception:
                                pass
                        folder_maybe_generic = False

            self._set(100, "Done.")
            return saved

        out_path, _meta = self._process_single_video(
            self.url,
            out_dir=downloads_dir(),
            allow_playlist=False,
            playlist_index=0,
            playlist_total=0,
            progress_mapper=None,
        )
        self._set(100, "Done.")
        return [out_path]

    def _process_single_video(
        self,
        url: str,
        out_dir: Path,
        allow_playlist: bool,
        playlist_index: int,
        playlist_total: int,
        progress_mapper,
    ) -> Tuple[Path, TrackMeta]:
        work = self.run_root / f"job_{int(time.time()*1000)}"
        dl_dir = work / "dl"
        tmp_dir = work / "tmp"
        dl_dir.mkdir(parents=True, exist_ok=True)
        tmp_dir.mkdir(parents=True, exist_ok=True)

        def set_stage(stage_pct: int, msg: str):
            if progress_mapper:
                progress_mapper(stage_pct, msg)
            else:
                self._set(stage_pct, msg)

        set_stage(8, "Fetching title…")
        yt_title, yt_channel = self._ytdlp_get_title_and_uploader(url, allow_playlist=allow_playlist)

        set_stage(25, "Downloading audio…")
        downloaded = self._download_audio_with_fallbacks(url, dl_dir, allow_playlist=allow_playlist)

        set_stage(45, "Converting to WAV…")
        wav_path = tmp_dir / "audio.wav"
        to_wav_for_analysis(downloaded, wav_path)

        fa, ft = parse_youtube_title(yt_title)
        fa = (fa or "").strip()
        ft = (ft or "").strip()

        if not fa:
            fa = (yt_channel or "").strip()

        base = TrackMeta(
            title=ft or yt_title or "",
            artist=fa or "",
            album_artist=fa or "",
            comment=url,
            source="YouTubeTitle",
        )

        if playlist_total > 0 and playlist_index > 0:
            base.track_number = str(playlist_index)
            base.track_total = str(playlist_total)

        # --------- Fetch ALL metadata sources first ----------
        set_stage(60, "Metadata: fetching sources…")

        sources: Dict[str, TrackMeta] = {}
        shz_meta: Optional[TrackMeta] = None

        if not self.advanced:
            # Quick pipeline: iTunes + SpotAPI + JioSaavn
            it = quick_itunes_enrich(self.cs, base)
            it.comment = base.comment
            sources["iTunesBest"] = it

            sp = spotapi_quick_search(it.artist or base.artist, it.title or base.title)
            if sp:
                sp.comment = base.comment
                sources["SpotAPI"] = sp

            js = jiosaavn_search(self.cs, f"{it.artist or base.artist} {it.title or base.title}".strip())
            if js:
                js.comment = base.comment
                sources["JioSaavn"] = js

            sources["YouTubeTitle"] = base
            current_merged = TrackMeta(**base.__dict__)
            current_merged = merge_meta(current_merged, it, prefer_incoming=True)
            if sp:
                current_merged = merge_meta(current_merged, sp, prefer_incoming=False)
            if js:
                current_merged = merge_meta(current_merged, js, prefer_incoming=False)
        else:
            def cb(msg: str):
                if playlist_total > 0 and playlist_index > 0:
                    self.progress_text.emit(f"Track {playlist_index}/{playlist_total}: {msg}")
                else:
                    self.progress_text.emit(msg)

            sources = advanced_enrich_all_sources(
                self.cs,
                youtube_url=url,
                base_from_title=base,
                wav_path=wav_path,
                work_dir=tmp_dir,
                progress_cb=cb,
            )
            if "Shazam" in sources:
                shz_meta = sources["Shazam"]

            # merge into a current suggestion
            current_merged = TrackMeta(**base.__dict__)
            for k in ("SongLink", "Shazam", "iTunesBest", "SpotAPI", "JioSaavn"):
                if k in sources:
                    current_merged = merge_meta(current_merged, sources[k], prefer_incoming=True if k in ("iTunesBest", "Shazam") else False)

        current_merged.album = clean_album_name(current_merged.album)
        if not current_merged.album_artist:
            current_merged.album_artist = current_merged.artist or ""

        if playlist_total > 0 and playlist_index > 0:
            current_merged.track_number = str(playlist_index)
            current_merged.track_total = str(playlist_total)

        # Extra iTunes candidates keyed to what user saw on YouTube
        set_stage(70, "Metadata: preparing review…")
        want_artist = fa or current_merged.artist
        want_title = ft or current_merged.title
        extra_it = itunes_candidates(self.cs, want_artist, want_title, limit=6)
        for m in extra_it:
            m.comment = base.comment
            m.source = "iTunes"

        # Build candidates list (deduped, with artwork prefetched)
        candidates = build_review_candidates(
            self.cs,
            yt_raw=yt_title,
            yt_artist=fa,
            yt_title=ft or yt_title,
            base_current=current_merged,
            source_metas=sources,
            extra_itunes=extra_it,
        )

        # --------- Review dialog AFTER fetching ----------
        set_stage(72, "Review Metadata…")
        chosen = self._request_review_blocking(
            yt_raw=yt_title,
            yt_artist=fa,
            yt_title=ft or yt_title,
            candidates=candidates,
        )
        chosen.comment = base.comment

        # --------- Post-selection: match & enrich, dedupe ----------
        set_stage(78, "Metadata: applying selection…")
        others: List[TrackMeta] = []
        for m in candidates:
            if m is chosen:
                continue
            others.append(m)
        for m in sources.values():
            others.append(m)

        final_meta = enrich_after_user_choice(self.cs, chosen, others)

        if playlist_total > 0 and playlist_index > 0:
            final_meta.track_number = str(playlist_index)
            final_meta.track_total = str(playlist_total)

        # ---------- Encode / Save ----------
        set_stage(82, "Encoding MP3…")
        mp3_tmp = tmp_dir / "final.mp3"
        wav_to_mp3_high_compat(wav_path, mp3_tmp)

        set_stage(92, "Saving…")

        track_prefix = ""
        if playlist_total > 0 and playlist_index > 0:
            width = max(2, len(str(playlist_total)))
            track_prefix = str(playlist_index).zfill(width)

        base_name = build_display_filename(final_meta, track_prefix=track_prefix)
        dest_path = unique_path(out_dir, base_name)

        shutil.copy2(mp3_tmp, dest_path)
        write_id3_tags_v23(dest_path, final_meta)

        set_stage(100, "Done.")
        return dest_path, final_meta

    # ----- yt-dlp helpers -----

    def _ytdlp_common_base_args(self) -> List[str]:
        return [
            str(YTDLP_PATH),
            "--no-warnings",
            "--retries",
            "10",
            "--fragment-retries",
            "10",
            "--extractor-retries",
            "5",
            "--socket-timeout",
            "20",
            "--http-chunk-size",
            "10M",
            "--newline",
        ]

    def _ytdlp_get_title_and_uploader(self, url: str, allow_playlist: bool) -> Tuple[str, str]:
        tries: List[List[str]] = []

        def add_try(extra: Optional[List[str]] = None, use_js: bool = True):
            args = [
                str(YTDLP_PATH),
                "--skip-download",
                "--print",
                "%(title)s",
                "--print",
                "%(uploader)s",
                "--no-warnings",
            ]
            if not allow_playlist:
                args.append("--no-playlist")
            if use_js and DENO_PATH.exists():
                args.extend(["--js-runtime", str(DENO_PATH)])
            if extra:
                args.extend(extra)
            args.append(url)
            tries.append(args)

        add_try(extra=None, use_js=True)
        add_try(extra=None, use_js=False)

        for c in ("android", "ios", "tv", "web,android"):
            add_try(extra=["--extractor-args", f"youtube:player_client={c}"], use_js=True)
            add_try(extra=["--extractor-args", f"youtube:player_client={c}"], use_js=False)

        last_err = None
        for args in tries:
            try:
                out, _ = run_cmd(args, cwd=self.run_root, timeout=90)
                lines = [ln.strip() for ln in (out or "").splitlines() if ln.strip()]
                title = lines[0] if len(lines) >= 1 else (out or "").strip()
                uploader = lines[1].replace(" - Topic", "") if len(lines) >= 2 else ""
                return title, uploader
            except Exception as e:
                last_err = e
                continue

        raise AppError(f"Failed to fetch YouTube title/channel.\n\n{last_err}")

    def _ytdlp_download_audio(
        self,
        url: str,
        dl_dir: Path,
        allow_playlist: bool,
        extra_args: Optional[List[str]] = None,
        use_js_runtime: bool = True,
    ) -> Path:
        tmpl = str(dl_dir / "%(id)s.%(ext)s")
        args = self._ytdlp_common_base_args() + [
            url,
            "-f",
            "bestaudio/best",
            "-o",
            tmpl,
        ]
        if not allow_playlist:
            args.append("--no-playlist")

        if use_js_runtime and DENO_PATH.exists():
            args.extend(["--js-runtime", str(DENO_PATH)])

        if extra_args:
            args.extend(extra_args)

        run_cmd(args, cwd=self.run_root, timeout=300)

        files = list(dl_dir.glob("*.*"))
        if not files:
            raise AppError("yt-dlp finished but no audio file was found.")
        files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
        return files[0]

    def _looks_like_ytdlp_botwall_or_403(self, msg: str) -> bool:
        m = (msg or "").lower()
        return (
            ("not a bot" in m)
            or ("sign in to confirm" in m)
            or ("http error 403" in m)
            or ("status code: 403" in m)
            or ("forbidden" in m)
            or ("too many requests" in m)
            or ("http error 429" in m)
            or ("status code: 429" in m)
        )

    def _download_audio_with_fallbacks(self, url: str, dl_dir: Path, allow_playlist: bool) -> Path:
        def clear_dir():
            for f in dl_dir.glob("*"):
                try:
                    f.unlink()
                except Exception:
                    pass

        try:
            return self._ytdlp_download_audio(url, dl_dir, allow_playlist=allow_playlist, use_js_runtime=True)
        except AppError as e:
            first_msg = str(e)
        except Exception as e:
            first_msg = str(e)

        try:
            clear_dir()
            return self._ytdlp_download_audio(url, dl_dir, allow_playlist=allow_playlist, use_js_runtime=False)
        except AppError:
            pass

        client_variants = [
            ["--extractor-args", "youtube:player_client=android"],
            ["--extractor-args", "youtube:player_client=ios"],
            ["--extractor-args", "youtube:player_client=tv"],
            ["--extractor-args", "youtube:player_client=web,android"],
        ]
        for extra in client_variants:
            for use_js in (True, False):
                try:
                    clear_dir()
                    return self._ytdlp_download_audio(
                        url, dl_dir, allow_playlist=allow_playlist, extra_args=extra, use_js_runtime=use_js
                    )
                except AppError:
                    continue

        net_toggles = ["--force-ipv4", "--geo-bypass", "--no-check-certificate"]
        for extra in client_variants + [None]:
            for use_js in (True, False):
                try:
                    clear_dir()
                    eargs = []
                    eargs.extend(net_toggles)
                    if extra:
                        eargs.extend(extra)
                    return self._ytdlp_download_audio(
                        url, dl_dir, allow_playlist=allow_playlist, extra_args=eargs, use_js_runtime=use_js
                    )
                except AppError:
                    continue

        if self._looks_like_ytdlp_botwall_or_403(first_msg):
            vid = extract_youtube_id(url)
            if not vid:
                raise AppError("Download failed (YouTube rate-limits)")

            try:
                p = self._piped_pick_audio_url(vid)
                if p:
                    return self._download_direct_stream(p, dl_dir, vid, suffix=".m4a")
            except Exception:
                pass

            try:
                inv = self._invidious_pick_audio_url(vid)
                if inv:
                    return self._download_direct_stream(inv, dl_dir, vid, suffix=".m4a")
            except Exception:
                pass

        raise AppError(
            "Download failed after multiple fallbacks.\n\n"
            "Common causes:\n"
            "  • Temporary YouTube rate-limits / bot checks (403/429)\n"
            "  • Network/TLS interception (VPN, corporate proxy)\n"
            "  • YouTube-side changes\n\n"
            "What you can try:\n"
            "  • Try again later (sorry)"
        )

    def _download_direct_stream(self, stream_url: str, dl_dir: Path, vid: str, suffix: str = ".m4a") -> Path:
        dl_dir.mkdir(parents=True, exist_ok=True)
        out = dl_dir / f"{sanitize_filename(vid)}{suffix}"
        tmp = out.with_suffix(out.suffix + ".part")
        headers = {"User-Agent": USER_AGENT, "Referer": "https://www.youtube.com/"}
        with requests.get(stream_url, stream=True, timeout=60, headers=headers) as r:
            r.raise_for_status()
            with open(tmp, "wb") as f:
                for chunk in r.iter_content(chunk_size=1024 * 256):
                    if chunk:
                        f.write(chunk)
        tmp.replace(out)
        return out

    def _piped_pick_audio_url(self, vid: str) -> str:
        api = f"https://piped.video/api/v1/streams/{vid}"
        r = requests.get(api, timeout=15, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        data = r.json()
        streams = data.get("audioStreams") or data.get("adaptiveFormats") or []
        best_url = ""
        best_score = -1
        for s in streams:
            if not isinstance(s, dict):
                continue
            u = s.get("url") or ""
            mime = (s.get("mimeType") or s.get("mime") or "").lower()
            u = (u or "").strip()
            if not u:
                continue
            if "audio" not in mime and not any(x in u for x in ("mime=audio", "audio")):
                continue
            br = s.get("bitrate") or s.get("averageBitrate") or 0
            try:
                br_i = int(br)
            except Exception:
                br_i = 0
            if br_i > best_score:
                best_score = br_i
                best_url = u
        return best_url

    def _invidious_pick_audio_url(self, vid: str) -> str:
        api = f"https://yewtu.be/api/v1/videos/{vid}"
        r = requests.get(api, timeout=15, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        data = r.json()
        fmts = data.get("adaptiveFormats") or data.get("formatStreams") or []
        best_url = ""
        best_score = -1
        for f in fmts:
            if not isinstance(f, dict):
                continue
            u = (f.get("url") or "").strip()
            mime = (f.get("type") or f.get("mimeType") or "").lower()
            if not u:
                continue
            if "audio" not in mime:
                continue
            br = f.get("bitrate") or 0
            try:
                br_i = int(br)
            except Exception:
                br_i = 0
            if br_i > best_score:
                best_score = br_i
                best_url = u
        return best_url

    def _ytdlp_list_playlist(self, url: str) -> Tuple[str, List[str]]:
        try:
            out, _ = run_cmd(
                [
                    str(YTDLP_PATH),
                    "-J",
                    "--flat-playlist",
                    "--no-warnings",
                    url,
                ],
                cwd=self.run_root,
                timeout=180,
            )
            data = json.loads(out or "{}")
        except Exception as e:
            raise AppError(f"Failed to read playlist metadata.\n\n{e}") from e

        title = (data.get("title") or data.get("playlist_title") or data.get("playlist") or "").strip()
        if not title:
            title = "Playlist"

        entries = data.get("entries") or []
        urls: List[str] = []
        for ent in entries:
            if isinstance(ent, dict):
                u = (ent.get("url") or ent.get("webpage_url") or ent.get("original_url") or "").strip()
                if u and u.startswith("http"):
                    urls.append(u)
                    continue
                vid = (ent.get("id") or "").strip()
                if vid:
                    urls.append(f"https://www.youtube.com/watch?v={vid}")
            elif isinstance(ent, str) and ent.strip():
                s = ent.strip()
                if s.startswith("http"):
                    urls.append(s)
                elif re.fullmatch(r"[\w-]{6,}", s):
                    urls.append(f"https://www.youtube.com/watch?v={s}")

        if not urls:
            raise AppError("Playlist detected, but no entries could be extracted.")

        return title, urls


# -------- Metadata Review Dialog --------
class ReviewDialog(QtWidgets.QDialog):
    def __init__(self, parent: QtWidgets.QWidget, payload: dict):
        super().__init__(parent)
        self.setWindowTitle(f"{APP_NAME} — Review Metadata")
        self.setModal(True)

        self._request_id = payload.get("request_id", "")
        self._candidates = payload.get("candidates", []) or []
        yt_raw = payload.get("yt_raw", "")
        yt_parsed = payload.get("yt_parsed", "")

        root = QtWidgets.QVBoxLayout(self)
        root.setContentsMargins(14, 14, 14, 14)
        root.setSpacing(10)

        lbl = QtWidgets.QLabel("Please confirm the correct track (details update when you change selection):")
        lbl.setWordWrap(True)

        yt1 = QtWidgets.QLabel(f"<b>Original YouTube title:</b><br>{html.escape(yt_raw)}")
        yt1.setWordWrap(True)
        yt2 = QtWidgets.QLabel(f"<b>Parsed title:</b><br>{html.escape(yt_parsed)}")
        yt2.setWordWrap(True)

        self.combo = QtWidgets.QComboBox()
        for item in self._candidates:
            self.combo.addItem(item.get("label", "Unknown"), userData=str(item.get("idx", 0)))

        # Preview area
        preview = QtWidgets.QHBoxLayout()
        preview.setSpacing(12)

        self.art = QtWidgets.QLabel()
        self.art.setFixedSize(96, 96)
        self.art.setScaledContents(True)
        self.art.setStyleSheet("border: 1px solid #2A3042; border-radius: 10px; background: #0F1320;")

        info_col = QtWidgets.QVBoxLayout()
        info_col.setSpacing(4)

        self.info_title = QtWidgets.QLabel("")
        self.info_artist = QtWidgets.QLabel("")
        self.info_album = QtWidgets.QLabel("")
        self.info_year = QtWidgets.QLabel("")
        self.info_source = QtWidgets.QLabel("")
        for w in (self.info_title, self.info_artist, self.info_album, self.info_year, self.info_source):
            w.setWordWrap(True)

        info_col.addWidget(self.info_title)
        info_col.addWidget(self.info_artist)
        info_col.addWidget(self.info_album)
        info_col.addWidget(self.info_year)
        info_col.addWidget(self.info_source)
        info_col.addStretch(1)

        preview.addWidget(self.art)
        preview.addLayout(info_col)

        btns = QtWidgets.QHBoxLayout()
        btns.addStretch(1)
        ok = QtWidgets.QPushButton("Use Selection")
        cancel = QtWidgets.QPushButton("Cancel (keep first)")
        btns.addWidget(cancel)
        btns.addWidget(ok)

        ok.clicked.connect(self.accept)
        cancel.clicked.connect(self._cancel_keep_first)

        self.combo.currentIndexChanged.connect(self._update_preview)

        root.addWidget(lbl)
        root.addWidget(yt1)
        root.addWidget(yt2)
        root.addWidget(QtWidgets.QLabel("<b>Choose match:</b>"))
        root.addWidget(self.combo)
        root.addLayout(preview)
        root.addLayout(btns)

        if self.combo.count() > 0:
            self.combo.setCurrentIndex(0)
        self._chosen_key = "0"
        self._update_preview()

    def _candidate_at_current(self) -> dict:
        idx = self.combo.currentIndex()
        if idx < 0 or idx >= len(self._candidates):
            return {}
        return self._candidates[idx]

    def _update_preview(self):
        c = self._candidate_at_current()
        title = (c.get("title") or "").strip()
        artist = (c.get("artist") or "").strip()
        album = (c.get("album") or "").strip()
        year = (c.get("year") or "").strip()
        source = (c.get("source") or "").strip()

        self.info_title.setText(f"<b>Title:</b> {html.escape(title) if title else '—'}")
        self.info_artist.setText(f"<b>Artist:</b> {html.escape(artist) if artist else '—'}")
        self.info_album.setText(f"<b>Album:</b> {html.escape(album) if album else '—'}")
        self.info_year.setText(f"<b>Release:</b> {html.escape(year) if year else '—'}")
        self.info_source.setText(f"<b>Source:</b> {html.escape(source) if source else '—'}")

        art_bytes = c.get("artwork_jpeg") or b""
        if isinstance(art_bytes, (bytes, bytearray)) and art_bytes:
            pix = QtGui.QPixmap()
            pix.loadFromData(bytes(art_bytes))
            if not pix.isNull():
                self.art.setPixmap(pix)
                return
        self.art.setPixmap(QtGui.QPixmap())  # clear

    def _cancel_keep_first(self):
        self._chosen_key = "0"
        self.reject()

    def accept(self):
        data = self.combo.currentData()
        self._chosen_key = str(data) if data is not None else "0"
        super().accept()

    @property
    def request_id(self) -> str:
        return self._request_id

    @property
    def chosen_key(self) -> str:
        return self._chosen_key


# UI: compact single-screen widget
class MainWidget(QtWidgets.QWidget):
    review_result = QtCore.Signal(str, str, object)  # request_id, chosen_key, unused

    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.setAcceptDrops(True)

        flags = (
            QtCore.Qt.Window
            | QtCore.Qt.CustomizeWindowHint
            | QtCore.Qt.WindowTitleHint
            | QtCore.Qt.WindowSystemMenuHint
            | QtCore.Qt.WindowMinimizeButtonHint
            | QtCore.Qt.WindowCloseButtonHint
        )
        self.setWindowFlags(flags)

        root = QtWidgets.QVBoxLayout(self)
        root.setContentsMargins(14, 14, 14, 14)
        root.setSpacing(10)

        card = QtWidgets.QFrame()
        card.setObjectName("Card")
        lay = QtWidgets.QVBoxLayout(card)
        lay.setContentsMargins(14, 14, 14, 14)
        lay.setSpacing(10)

        title = QtWidgets.QLabel("YouTube to MP3")
        title.setObjectName("Title")

        sub = QtWidgets.QLabel("Paste a YouTube link & it'll start downloading.")
        sub.setObjectName("Subtle")
        sub.setWordWrap(True)

        self.edit = QtWidgets.QLineEdit()
        self.edit.setPlaceholderText("https://www.youtube.com/watch?v=…")
        self.edit.setClearButtonEnabled(True)

        self.adv_cb = QtWidgets.QCheckBox("Advanced Metadata (slower, better matches)")
        self.adv_cb.setChecked(False)

        self.status = QtWidgets.QLabel("")
        self.status.setObjectName("Subtle")
        self.status.setWordWrap(True)

        self.progress = QtWidgets.QProgressBar()
        self.progress.setRange(0, 100)
        self.progress.setValue(0)

        lay.addWidget(title)
        lay.addWidget(sub)
        lay.addWidget(self.edit)
        lay.addWidget(self.adv_cb)
        lay.addWidget(self.status)
        lay.addWidget(self.progress)

        root.addWidget(card)

        self._thread: Optional[QtCore.QThread] = None
        self._worker: Optional[PipelineWorker] = None
        self._running = False

        self._debounce = QtCore.QTimer(self)
        self._debounce.setSingleShot(True)
        self._debounce.timeout.connect(self._maybe_start_from_text)

        self.edit.textChanged.connect(self._on_text_changed)

        self._size_locked = False
        self._set_running(False)
        self.status.setText("")

    def showEvent(self, event: QtGui.QShowEvent):
        if not self._size_locked:
            self._lock_size()
            self._size_locked = True
        super().showEvent(event)

    def _lock_size(self):
        lay = self.layout()
        if lay:
            lay.activate()

        min_w = 380
        max_w = 560
        step = 10

        best_w = max_w
        best_h = 99999
        best_area = 10**18

        self.setMinimumSize(0, 0)
        self.setMaximumSize(16777215, 16777215)

        for w in range(min_w, max_w + 1, step):
            self.resize(w, 10)
            self.setFixedWidth(w)
            if lay:
                lay.activate()
            hint = self.sizeHint()
            h = int(hint.height() + 2)
            area = int(w * h)
            if area < best_area or (area == best_area and w < best_w):
                best_area = area
                best_w = w
                best_h = h

        self.setFixedSize(int(best_w), int(best_h))

    def _valid_url(self, text: str) -> bool:
        return bool(YOUTUBE_RE.search(text or ""))

    def _set_running(self, running: bool):
        self._running = running
        self.edit.setEnabled(not running)
        self.adv_cb.setEnabled(not running)

    def _on_text_changed(self, _text: str):
        if self._running:
            return
        self._debounce.start(250)

    def _maybe_start_from_text(self):
        if self._running:
            return
        url = self.edit.text().strip()
        if not self._valid_url(url):
            self.status.setText("")
            self.progress.setValue(0)
            return

        intent = classify_youtube_url(url)
        playlist_mode = "single"
        final_url = url

        if intent.is_playlist:
            choice = self._playlist_prompt(url)
            if choice == "cancel":
                self.status.setText("Cancelled.")
                self.progress.setValue(0)
                return
            if choice == "single":
                playlist_mode = "single"
                final_url = strip_playlist_from_watch_url(url)
            elif choice == "playlist":
                playlist_mode = "playlist"
                final_url = url

        self._start(final_url, playlist_mode)

    def _playlist_prompt(self, url: str) -> str:
        box = QtWidgets.QMessageBox(self)
        box.setWindowTitle(APP_NAME)
        box.setIcon(QtWidgets.QMessageBox.Question)
        box.setText("Playlist link detected.")
        box.setInformativeText("Do you want to download the full playlist, or just the single video?")

        btn_playlist = box.addButton("Download Playlist", QtWidgets.QMessageBox.AcceptRole)
        btn_single = box.addButton("Single Video Only", QtWidgets.QMessageBox.DestructiveRole)
        btn_cancel = box.addButton("Cancel", QtWidgets.QMessageBox.RejectRole)

        box.setDefaultButton(btn_single)
        box.exec()

        clicked = box.clickedButton()
        if clicked == btn_playlist:
            return "playlist"
        if clicked == btn_single:
            return "single"
        return "cancel"

    # Drag & drop
    def dragEnterEvent(self, event: QtGui.QDragEnterEvent):
        if event.mimeData().hasText():
            event.acceptProposedAction()

    def dropEvent(self, event: QtGui.QDropEvent):
        text = (event.mimeData().text() or "").strip()
        if text and not self._running:
            self.edit.setText(text)

    def _start(self, url: str, playlist_mode: str):
        self._set_running(True)
        self.progress.setValue(0)
        self.status.setText("Starting…")

        advanced = bool(self.adv_cb.isChecked())

        self._thread = QtCore.QThread(self)
        self._worker = PipelineWorker(url=url, advanced=advanced, playlist_mode=playlist_mode)
        self._worker.moveToThread(self._thread)

        self._thread.started.connect(self._worker.run)
        self._worker.progress_text.connect(self.status.setText)
        self._worker.progress_value.connect(self.progress.setValue)
        self._worker.error.connect(self._on_error)
        self._worker.finished.connect(self._on_finished)

        self._worker.review_needed.connect(self._on_review_needed)

        # ✅ CRITICAL FIX: DirectConnection prevents deadlock (worker has no Qt event loop while running)
        self.review_result.connect(self._worker.receive_review_result, QtCore.Qt.DirectConnection)

        self._thread.start()

    def _on_review_needed(self, payload: dict):
        dlg = ReviewDialog(self, payload)
        dlg.exec()
        self.review_result.emit(dlg.request_id, dlg.chosen_key, None)

    def _cleanup_thread(self):
        if self._thread:
            self._thread.quit()
            self._thread.wait(8000)
            self._thread.deleteLater()
        self._thread = None
        if self._worker:
            self._worker.deleteLater()
        self._worker = None

    def _on_error(self, msg: str):
        self._cleanup_thread()
        self._set_running(False)
        self.progress.setValue(0)
        self.status.setText("")
        QtWidgets.QMessageBox.critical(self, APP_NAME, msg)

    def _on_finished(self, paths: List[str]):
        self._cleanup_thread()
        self._set_running(False)
        self.progress.setValue(100)

        if not paths:
            QtWidgets.QMessageBox.information(self, APP_NAME, "Done.")
        elif len(paths) == 1:
            QtWidgets.QMessageBox.information(self, APP_NAME, f"Saved:\n{paths[0]}")
        else:
            folder = str(Path(paths[0]).parent)
            QtWidgets.QMessageBox.information(self, APP_NAME, f"Saved {len(paths)} files to:\n{folder}")

        self.edit.setText("")
        self.status.setText("")
        self.progress.setValue(0)


# App icon helpers (optional)
def resource_path(relative: str) -> str:
    base_path = getattr(sys, "_MEIPASS", None)
    if base_path:
        return str(Path(base_path) / relative)
    return str(Path(__file__).resolve().parent / relative)


def set_app_icon(app: QtWidgets.QApplication):
    try:
        ico_path = Path(resource_path("icon.ico"))
        if ico_path.exists():
            app.setWindowIcon(QtGui.QIcon(str(ico_path)))
    except Exception:
        pass


# Main
def main():
    mutex = SingleInstance(r"Global\YTDL_SINGLE_INSTANCE_MUTEX_v4")
    if not mutex.acquire():
        app = QtWidgets.QApplication(sys.argv)
        app.setStyleSheet(QSS)
        QtWidgets.QMessageBox.information(None, APP_NAME, "YTDL is already running.")
        return

    try:
        QtCore.QCoreApplication.setApplicationName(APP_NAME)
        app = QtWidgets.QApplication(sys.argv)
        app.setStyleSheet(QSS)
        set_app_icon(app)

        w = MainWidget()
        w.show()

        app.exec()
    finally:
        mutex.release()


if __name__ == "__main__":
    main()
