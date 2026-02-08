# YTDL GUI - Windows-only (Python 3.12+)
# PROVIDED AS-IS WITH NO SUPPORT (sorry x)
#
# pip deps:
# pip install PySide6 requests mutagen
#
# pip install shazamio (Optional / Advanced metadata)
# pip install spotapi (Optional / Spotify)
#
# Binaries downloaded at runtime to %TEMP%\YTDL_bin:
# yt-dlp.exe, ffmpeg.exe, ffprobe.exe, deno.exe

from __future__ import annotations

import asyncio
import ctypes
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
"""


# Helpers: filename sanitization
_INVALID_FS_CHARS = r'<>:"/\\|?*'
_INVALID_FS_RE = re.compile(r'[<>:"/\\|?*]+')


def sanitize_filename(name: str, max_len: int = 180) -> str:
    s = (name or "").strip()
    s = _INVALID_FS_RE.sub("_", s)
    s = re.sub(r"\s+", " ", s).strip().strip(". ")
    if not s:
        s = "audio"
    # Windows path component length safety
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

    # Remove trailing (...) or [...] if it looks like marketing
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
    import subprocess

    # Strong hide on Windows: CREATE_NO_WINDOW + STARTUPINFO(SW_HIDE)
    creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
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
    # Optional extra (debug / provenance)
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


def pick_best_itunes_result(results: List[Dict[str, Any]], want_artist: str, want_title: str) -> Optional[Dict[str, Any]]:
    wa = _norm(want_artist)
    wt = _norm(want_title)

    best = None
    best_score = -999

    for item in results:
        a = _norm(item.get("artistName", ""))
        t = _norm(item.get("trackName", ""))
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
        if score > best_score:
            best_score = score
            best = item

    return best


def upgrade_artwork_url(artwork_url: str) -> str:
    if not artwork_url:
        return ""
    return re.sub(r"/\d+x\d+bb\.(jpg|png)$", "/1000x1000bb.jpg", artwork_url, flags=re.IGNORECASE)


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
    return m


# JioSaavn API (unofficial, via saavnapi-nine)
def jiosaavn_search(cs: CooldownSession, query: str) -> Optional[TrackMeta]:
    """
    Best-effort: use saavnapi-nine.vercel.app 'result' endpoint to search by query string.
    """
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

    # The API returns a structure that can vary by deployment; handle loosely.
    # Prefer first item that looks like a song.
    items = None
    if isinstance(data, dict):
        # common patterns: {"data": [...]}, {"results": [...]}, {"songs": {"data":[...]}}
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
    """
    Best-effort SpotAPI integration.
    SpotAPI upstream focuses on public+private Spotify APIs, and some usages require auth/cookies/solver.
    This function tries safe import + a few likely public search calls; if not possible, returns None.
    """
    q_artist = (artist or "").strip()
    q_title = (title or "").strip()
    term = " ".join([x for x in [q_artist, q_title] if x]).strip()
    if not term:
        return None

    try:
        import spotapi  # type: ignore
    except Exception:
        return None

    # We don't know exact public search surface in the user's installed version.
    # Try multiple patterns defensively.
    candidates: List[dict] = []

    # Pattern A: spotapi.Public / PublicSearch / PublicClient etc.
    for attr in ("Public", "PublicClient", "PublicSearch", "Search", "Song", "PublicSong"):
        try:
            cls = getattr(spotapi, attr, None)
            if cls is None:
                continue
            obj = cls()  # some accept no args for public calls
            # Try common method names
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

    # Pattern B: look under spotapi.public module
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

    # Parse a likely track from whatever we got
    def dig_tracks(x: Any) -> List[dict]:
        out: List[dict] = []
        if isinstance(x, dict):
            # Spotify-like shapes
            for k in ("tracks", "items", "data", "results"):
                v = x.get(k)
                if isinstance(v, list):
                    out.extend([i for i in v if isinstance(i, dict)])
                if isinstance(v, dict):
                    out.extend(dig_tracks(v))
            # Search endpoint often returns {"tracks":{"items":[...]}}
            for v in x.values():
                out.extend(dig_tracks(v))
        elif isinstance(x, list):
            for it in x:
                out.extend(dig_tracks(it))
        return out

    tracks: List[dict] = []
    for c in candidates:
        tracks.extend(dig_tracks(c))

    # Pick something plausible
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
        return s

    if not tracks:
        return None

    tracks.sort(key=score, reverse=True)
    top = tracks[0]

    m = TrackMeta()
    m.title = (top.get("name") or top.get("title") or "").strip()

    # artists
    a = top.get("artists")
    if isinstance(a, list) and a:
        names = []
        for it in a:
            if isinstance(it, dict) and it.get("name"):
                names.append(str(it["name"]).strip())
        m.artist = ", ".join([n for n in names if n])
    elif isinstance(a, str):
        m.artist = a.strip()

    # album
    alb = top.get("album")
    if isinstance(alb, dict):
        m.album = (alb.get("name") or "").strip()
        imgs = alb.get("images")
        if isinstance(imgs, list) and imgs:
            # pick highest-ish
            url = ""
            for im in imgs:
                if isinstance(im, dict) and im.get("url"):
                    url = im["url"]
                    break
            m.artwork_url = url.strip()
    else:
        m.album = (top.get("album") or "").strip()

    # year
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


def wav_slice_normalized(src_wav: Path, dst_wav: Path, start_s: float, dur_s: float = 30.0) -> None:
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

    loop = asyncio.new_event_loop()
    try:
        asyncio.set_event_loop(loop)
        shazam = Shazam()
        return loop.run_until_complete(shazam.recognize_song(str(wav_path)))
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
    if duration <= 10:
        raise AppError("Audio is too short to recognize reliably.")

    offsets: List[float] = []
    base = 30.0
    if duration > base + 31:
        offsets.append(base)
    for frac in (0.25, 0.45, 0.65, 0.80):
        t = min(max(0.0, duration * frac), max(0.0, duration - 31.0))
        if not offsets or all(abs(t - o) > 10 for o in offsets):
            offsets.append(t)
    offsets = offsets[:5]

    # vote-based
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
        wav_slice_normalized(src_wav, slice_wav, start_s, 30.0)
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

    # pick highest votes, tie-break ISRC
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

    # Extra compatibility frames
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
            if b and not a:
                setattr(out, field, b)
            elif b and a and field in ("album", "year", "genre", "itunes_track_id", "artwork_url"):
                # For these fields, incoming typically higher confidence
                setattr(out, field, b)
        else:
            if not a and b:
                setattr(out, field, b)

    # artwork bytes
    if incoming.artwork_jpeg and not out.artwork_jpeg:
        out.artwork_jpeg = incoming.artwork_jpeg

    if not out.album:
        out.album = clean_album_name(out.album)
    if not out.album_artist:
        out.album_artist = out.artist or ""
    return out


# Metadata pipelines
def quick_itunes_enrich(cs: CooldownSession, base: TrackMeta) -> TrackMeta:
    """
    Basic mode iTunes: minimal requests for speed.
    - If ISRC exists: itunes search isrc:...
    - else: first variant only
    - then optional lookup for richer fields if we got trackId
    """
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

        if meta.artwork_url and not meta.artwork_jpeg:
            try:
                meta.artwork_jpeg = download_artwork(cs, meta.artwork_url)
            except Exception:
                meta.artwork_jpeg = b""

    meta.album = clean_album_name(meta.album)
    if not meta.album_artist:
        meta.album_artist = meta.artist or ""
    meta.source = meta.source or "iTunes"
    return meta


def advanced_enrich(
    cs: CooldownSession,
    youtube_url: str,
    base_from_title: TrackMeta,
    wav_path: Path,
    work_dir: Path,
    progress_cb,
) -> TrackMeta:
    """
    Advanced pipeline order:
      parse youtube title -> song.link -> Shazam Recognition -> iTunes Search -> song.link -> SpotAPI -> iTunes Lookup
    """
    meta = TrackMeta(**base_from_title.__dict__)

    # 1) song.link
    progress_cb("song.link: resolving…")
    it_id = ""
    try:
        payload = songlink_lookup(cs, youtube_url)
        it_id = songlink_extract_itunes_id(payload)
        if it_id:
            meta.itunes_track_id = it_id
    except Exception:
        pass

    # 2) Shazam
    progress_cb("Shazam: matching…")
    shz = shazam_best_guess_from_wav(wav_path, work_dir, progress_cb)
    if shz.title or shz.artist or shz.isrc:
        shz.comment = meta.comment
        meta = merge_meta(meta, shz, prefer_incoming=True)

    # 3) iTunes search (more aggressive)
    progress_cb("iTunes: searching…")
    chosen: Optional[Dict[str, Any]] = None
    if meta.isrc:
        try:
            data = itunes_search(cs, f"isrc:{meta.isrc}", limit=10)
            res = data.get("results") or []
            if res:
                chosen = res[0]
        except Exception:
            pass

    if not chosen and meta.artist and meta.title:
        for term in itunes_search_variants(meta.artist, meta.title):
            try:
                data = itunes_search(cs, term, limit=15)
                res = data.get("results") or []
                if not res:
                    continue
                picked = pick_best_itunes_result(res, meta.artist, meta.title)
                if picked:
                    chosen = picked
                    break
            except Exception:
                continue

    if chosen:
        meta = merge_meta(meta, meta_from_itunes_item(chosen), prefer_incoming=True)
        if meta.artwork_url and not meta.artwork_jpeg:
            try:
                meta.artwork_jpeg = download_artwork(cs, meta.artwork_url)
            except Exception:
                meta.artwork_jpeg = b""

    # 4) song.link again (per spec; can fill itunes ID after metadata changed)
    progress_cb("song.link: confirming…")
    try:
        payload = songlink_lookup(cs, youtube_url)
        it2 = songlink_extract_itunes_id(payload)
        if it2:
            meta.itunes_track_id = it2
    except Exception:
        pass

    # 5) SpotAPI
    progress_cb("Spotify (SpotAPI): searching…")
    sp = spotapi_quick_search(meta.artist, meta.title)
    if sp:
        sp.comment = meta.comment
        meta = merge_meta(meta, sp, prefer_incoming=False)  # don't override strong iTunes fields

    # 6) iTunes lookup (final)
    progress_cb("iTunes: lookup…")
    if meta.itunes_track_id:
        try:
            data = itunes_lookup(cs, meta.itunes_track_id)
            res = data.get("results") or []
            if res:
                meta = merge_meta(meta, meta_from_itunes_item(res[0]), prefer_incoming=True)
        except Exception:
            pass

    # Bonus: JioSaavn (new integration) - best-effort extra artwork/album/year if missing
    progress_cb("JioSaavn: searching…")
    js = jiosaavn_search(cs, f"{meta.artist} {meta.title}".strip())
    if js:
        js.comment = meta.comment
        meta = merge_meta(meta, js, prefer_incoming=False)

    meta.album = clean_album_name(meta.album)
    if not meta.album_artist:
        meta.album_artist = meta.artist or ""
    return meta


# Copy/save helpers
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


def build_display_filename(meta: TrackMeta) -> str:
    # Required format: Artist - Title (cover/remix etc)
    # We preserve parentheses from the parsed/enriched title; just sanitize later.
    a = (meta.artist or "").strip()
    t = (meta.title or "").strip()
    if a and t:
        return f"{a} - {t}"
    return t or a or "audio"


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
    # Remove list param and related playlist indices
    p = urlparse(url)
    qs = parse_qs(p.query or "")
    for k in ("list", "index", "start_radio", "radio", "pp"):
        if k in qs:
            qs.pop(k, None)
    new_query = urlencode({k: v[0] for k, v in qs.items() if v}, doseq=False)
    return urlunparse((p.scheme, p.netloc, p.path, p.params, new_query, p.fragment))


# Connectivity check (hard requirement)
def check_internet_required() -> None:
    try:
        r = requests.get(CONNECT_TEST_URL, timeout=6, headers={"User-Agent": USER_AGENT})
        r.raise_for_status()
        # "resolves successfully" requirement: we treat HTTP 200 as success.
        return
    except Exception as e:
        raise AppError(
            "Internet connection required.\n\n"
            f"Connectivity test failed:\n  {CONNECT_TEST_URL}\n\n"
            f"Details:\n  {e}"
        )


# Progress plan
@dataclass
class ProgressPlan:
    tools: int = 5
    title: int = 14
    download: int = 48
    to_wav: int = 62
    meta: int = 84
    to_mp3: int = 94
    save: int = 98
    done: int = 100


# Worker: download + tag
class PipelineWorker(QtCore.QObject):
    progress_text = QtCore.Signal(str)
    progress_value = QtCore.Signal(int)
    error = QtCore.Signal(str)
    finished = QtCore.Signal(list)  # list of saved output paths (strings)

    def __init__(self, url: str, advanced: bool, playlist_mode: str):
        super().__init__()
        self.url = url
        self.advanced = bool(advanced)
        self.playlist_mode = playlist_mode  # "single" or "playlist"
        self.cs = CooldownSession(USER_AGENT, cooldown_s=REQUEST_COOLDOWN_S)
        self.plan = ProgressPlan()
        self.run_root = Path(tempfile.mkdtemp(prefix=f"{APP_NAME}_run_"))

    def _set(self, pct: int, text: str):
        self.progress_value.emit(int(max(0, min(100, pct))))
        self.progress_text.emit(text)

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
        # Connectivity gate (required)
        self._set(2, "Checking internet…")
        check_internet_required()

        self._set(self.plan.tools, "Preparing tools…")
        Toolchain(USER_AGENT).ensure_ready()

        # Playlist expansion if needed
        if self.playlist_mode == "playlist":
            self._set(8, "Reading playlist…")
            pl_title, entries = self._ytdlp_list_playlist(self.url)
            folder = downloads_dir() / sanitize_filename(pl_title or "Playlist")
            saved: List[Path] = []
            total = max(1, len(entries))
            for idx, vid_url in enumerate(entries, 1):
                # Scale progress across playlist items (still deterministic-ish)
                base = 10 + int((idx - 1) * 88 / total)
                self._set(base, f"Playlist item {idx}/{total}…")
                saved.append(self._process_single_video(vid_url, out_dir=folder, allow_playlist=False))
            self._set(100, "Done.")
            return saved

        # Single video
        out = self._process_single_video(self.url, out_dir=downloads_dir(), allow_playlist=False)
        self._set(self.plan.done, "Done.")
        return [out]

    def _process_single_video(self, url: str, out_dir: Path, allow_playlist: bool) -> Path:
        work = self.run_root / f"job_{int(time.time()*1000)}"
        dl_dir = work / "dl"
        tmp_dir = work / "tmp"
        dl_dir.mkdir(parents=True, exist_ok=True)
        tmp_dir.mkdir(parents=True, exist_ok=True)

        self._set(self.plan.title, "Fetching title…")
        yt_title = self._ytdlp_get_title(url, allow_playlist=allow_playlist)

        self._set(self.plan.download, "Downloading audio…")
        downloaded = self._ytdlp_download_audio(url, dl_dir, allow_playlist=allow_playlist)

        self._set(self.plan.to_wav, "Converting to WAV…")
        wav_path = tmp_dir / "audio.wav"
        to_wav_for_analysis(downloaded, wav_path)

        # Base meta from YouTube title
        fa, ft = parse_youtube_title(yt_title)
        base = TrackMeta(
            title=ft or yt_title or "",
            artist=fa or "",
            album_artist=fa or "",
            comment=url,
            source="YouTubeTitle",
        )

        # Metadata pipeline selection
        self._set(self.plan.meta, "Metadata: basic…")
        final_meta = TrackMeta(**base.__dict__)

        if not self.advanced:
            # Basic: parse title -> quick iTunes lookup / Spotify -> save
            enriched = quick_itunes_enrich(self.cs, final_meta)
            final_meta = merge_meta(final_meta, enriched, prefer_incoming=True)

            # Spotify quick add (SpotAPI) if it can help fill gaps
            sp = spotapi_quick_search(final_meta.artist, final_meta.title)
            if sp:
                sp.comment = final_meta.comment
                final_meta = merge_meta(final_meta, sp, prefer_incoming=False)

        else:
            # Advanced: parse title -> song.link -> Shazam -> iTunes Search -> song.link -> SpotAPI -> iTunes Lookup
            def cb(msg: str):
                # keep within the same stage, user sees granular steps
                self.progress_text.emit(msg)

            final_meta = advanced_enrich(
                self.cs,
                youtube_url=url,
                base_from_title=final_meta,
                wav_path=wav_path,
                work_dir=tmp_dir,
                progress_cb=cb,
            )

        # Ensure album cleaned
        final_meta.album = clean_album_name(final_meta.album)
        if not final_meta.album_artist:
            final_meta.album_artist = final_meta.artist or ""

        # Build MP3
        self._set(self.plan.to_mp3, "Encoding MP3…")
        mp3_tmp = tmp_dir / "final.mp3"
        wav_to_mp3_high_compat(wav_path, mp3_tmp)

        # Build filename + save
        self._set(self.plan.save, "Saving…")
        base_name = build_display_filename(final_meta)
        dest_path = unique_path(out_dir, base_name)

        shutil.copy2(mp3_tmp, dest_path)
        write_id3_tags_v23(dest_path, final_meta)
        return dest_path

    # ----- yt-dlp helpers -----
    def _ytdlp_get_title(self, url: str, allow_playlist: bool) -> str:
        args = [
            str(YTDLP_PATH),
            "--skip-download",
            "--print",
            "%(title)s",
            "--no-warnings",
        ]
        if not allow_playlist:
            args.append("--no-playlist")
        args.append(url)
        out, _ = run_cmd(args, cwd=self.run_root)
        return (out or "").strip()

    def _ytdlp_download_audio(self, url: str, dl_dir: Path, allow_playlist: bool) -> Path:
        tmpl = str(dl_dir / "%(id)s.%(ext)s")
        args = [
            str(YTDLP_PATH),
            url,
            "-f",
            "bestaudio/best",
            "--no-warnings",
            "--retries",
            "10",
            "--fragment-retries",
            "10",
            "--concurrent-fragments",
            "8",
            "--extractor-retries",
            "5",
            "--socket-timeout",
            "20",
            "--http-chunk-size",
            "10M",
            "--newline",
            "-o",
            tmpl,
            "--js-runtime",
            str(DENO_PATH),
        ]
        if not allow_playlist:
            args.append("--no-playlist")

        run_cmd(args, cwd=self.run_root)

        files = list(dl_dir.glob("*.*"))
        if not files:
            raise AppError("yt-dlp finished but no audio file was found.")
        files.sort(key=lambda p: p.stat().st_mtime, reverse=True)
        return files[0]

    def _ytdlp_list_playlist(self, url: str) -> Tuple[str, List[str]]:
        """
        Returns (playlist_title, entry_urls)
        """
        # playlist title (best-effort)
        title = ""
        try:
            out, _ = run_cmd(
                [
                    str(YTDLP_PATH),
                    "--skip-download",
                    "--print",
                    "%(playlist_title)s",
                    "--no-warnings",
                    url,
                ],
                cwd=self.run_root,
                timeout=60,
            )
            title = (out or "").strip()
        except Exception:
            title = "Playlist"

        # entries
        # Use --flat-playlist for speed, print original_url for each entry
        try:
            out, _ = run_cmd(
                [
                    str(YTDLP_PATH),
                    "--flat-playlist",
                    "--print",
                    "%(original_url)s",
                    "--no-warnings",
                    url,
                ],
                cwd=self.run_root,
                timeout=120,
            )
        except AppError as e:
            raise AppError(f"Failed to read playlist.\n\n{e}") from e

        lines = [ln.strip() for ln in (out or "").splitlines() if ln.strip()]
        # Filter obviously non-urls
        urls = [ln for ln in lines if ln.startswith("http")]
        if not urls:
            # fallback: try video ids
            urls = []
            for ln in lines:
                if re.fullmatch(r"[\w-]{6,}", ln):
                    urls.append(f"https://www.youtube.com/watch?v={ln}")

        if not urls:
            raise AppError("Playlist detected, but no entries could be extracted.")

        return title or "Playlist", urls


# UI: compact single-screen widget
class MainWidget(QtWidgets.QWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.setAcceptDrops(True)
        
        # Force only: minimize + close (no maximize)
        flags = (
            QtCore.Qt.Window
            | QtCore.Qt.CustomizeWindowHint
            | QtCore.Qt.WindowTitleHint
            | QtCore.Qt.WindowSystemMenuHint
            | QtCore.Qt.WindowMinimizeButtonHint
            | QtCore.Qt.WindowCloseButtonHint
        )
        self.setWindowFlags(flags)
        
        # UI
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

        # threading
        self._thread: Optional[QtCore.QThread] = None
        self._worker: Optional[PipelineWorker] = None
        self._running = False

        # debounce auto-start
        self._debounce = QtCore.QTimer(self)
        self._debounce.setSingleShot(True)
        self._debounce.timeout.connect(self._maybe_start_from_text)

        self.edit.textChanged.connect(self._on_text_changed)

        # fixed size: compact but safe (no clipping) — computed after fonts/style are applied
        self._size_locked = False

        self._set_running(False)
        self.status.setText("")

    def showEvent(self, event: QtGui.QShowEvent):
        # Lock the size once, after Qt has polished the widget with the final font/style/DPI.
        if not self._size_locked:
            self._lock_size()
            self._size_locked = True
        super().showEvent(event)

    def _lock_size(self):
        """
        Explicitly fixed, compact window size with a guarantee that all widgets fit:
        - Picks the smallest width in a safe range that yields the smallest overall sizeHint()
          (after word-wrapped labels settle), then fixes the window to that exact size.
        - Avoids clipping/overflow across common DPI settings because this is based on Qt's own layout metrics.
        """
        # Force layout to exist and be up-to-date
        lay = self.layout()
        if lay:
            lay.activate()

        # Range chosen to stay "small/compact" while still preventing pathological wraps.
        # (Qt uses device-independent pixels; this remains stable across DPI scaling.)
        min_w = 380
        max_w = 520
        step = 10

        best_w = max_w
        best_h = 99999
        best_area = 10**18

        # Temporarily allow resizing during measurement
        self.setMinimumSize(0, 0)
        self.setMaximumSize(16777215, 16777215)

        for w in range(min_w, max_w + 1, step):
            # Fix width, let layout compute height
            self.resize(w, 10)
            self.setFixedWidth(w)
            if lay:
                lay.activate()
            hint = self.sizeHint()

            # Add a tiny safety pad to absorb fractional rounding at some DPIs/styles.
            h = int(hint.height() + 2)
            area = int(w * h)

            # Prefer smallest area; tie-breaker: smaller width
            if area < best_area or (area == best_area and w < best_w):
                best_area = area
                best_w = w
                best_h = h

        # Apply final fixed size
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
        # debounce so pasting large URL doesn't trigger twice
        self._debounce.start(250)

    def _maybe_start_from_text(self):
        if self._running:
            return
        url = self.edit.text().strip()
        if not self._valid_url(url):
            self.status.setText("")
            self.progress.setValue(0)
            return

        # playlist prompt logic
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
                # if it's a watch URL with list=..., strip playlist params
                final_url = strip_playlist_from_watch_url(url)
            elif choice == "playlist":
                playlist_mode = "playlist"
                final_url = url

        self._start(final_url, playlist_mode)

    def _playlist_prompt(self, url: str) -> str:
        """
        Returns: "playlist" | "single" | "cancel"
        """
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

        self._thread.start()

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
            # Playlist: keep it concise
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
    mutex = SingleInstance(r"Global\YTDL_SINGLE_INSTANCE_MUTEX_v2")
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
