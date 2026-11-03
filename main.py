import csv
import ctypes
import hashlib
import heapq
import json
import os
import queue
import re
import shutil
import stat
import subprocess
import sys
import threading
import time
import tkinter as tk
from datetime import datetime
from tkinter import ttk, filedialog, messagebox

try:
    from send2trash import send2trash as _send2trash
except ImportError:  # the Recycle Bin needs:  pip install send2trash
    _send2trash = None

CHECKED = "☑"
UNCHECKED = "☐"
COVERED = "▣"  # inside a folder that is already selected in the same list

COPY_COLOR = "#2f7de1"    # progress bar while copying and verifying
DELETE_COLOR = "#d32f2f"  # progress bar while deleting
CONFIRM_WORD = "DELETE"   # what must be typed to confirm risky deletions


def parse_recycle_info(data):
    """Read a Windows '$I' Recycle Bin record: returns (original path, deleted-at unix time)."""
    if len(data) < 28:
        return None
    version = int.from_bytes(data[0:8], "little")
    filetime = int.from_bytes(data[16:24], "little")
    when = (filetime - 116444736000000000) / 10_000_000
    if version == 2:
        length = int.from_bytes(data[24:28], "little")
        raw = data[28:28 + 2 * length]
    elif version == 1:
        raw = data[24:24 + 520]
    else:
        return None
    return raw.decode("utf-16-le", errors="ignore").split("\0")[0], when



# ----------------------------------------------------------------------
# Storage analyzer: scanning and suggestions (no window code in here)
# ----------------------------------------------------------------------
MB = 1024 * 1024
DAY = 86400

CATEGORY_EXTENSIONS = {
    "Videos": (".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".webm", ".m4v", ".mpg", ".mpeg"),
    "Pictures": (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tif", ".tiff", ".heic", ".webp", ".raw", ".cr2", ".nef", ".psd"),
    "Music": (".mp3", ".wav", ".flac", ".aac", ".ogg", ".m4a", ".wma"),
    "Documents": (".pdf", ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".txt", ".rtf", ".odt", ".csv"),
    "Archives": (".zip", ".rar", ".7z", ".tar", ".gz", ".bz2", ".xz", ".tgz"),
    "Programs & disk images": (".exe", ".msi", ".msix", ".iso", ".img", ".dmg", ".pkg", ".apk", ".cab", ".wim", ".vhd", ".vhdx"),
}
EXTENSION_CATEGORY = {ext: name for name, exts in CATEGORY_EXTENSIONS.items() for ext in exts}
INSTALLER_EXTENSIONS = {".exe", ".msi", ".msix", ".iso", ".img", ".dmg", ".pkg", ".apk"}
INSTALLER_WORDS = ("setup", "install", "update", "redist")
ARCHIVE_CATEGORIES = {"Videos", "Pictures", "Archives", "Programs & disk images"}
SYSTEM_FILE_NAMES = {"pagefile.sys", "hiberfil.sys", "swapfile.sys"}
LAUNCHER_FOLDERS = {"steamapps", "epic games", "xboxgames", "riot games", "gog games"}
APP_CACHE_FOLDERS = {"cache", "code cache", "gpucache", "cache_data", "shadercache"}

# Thresholds for suggestions (they move into the Settings screen later).
INSTALLER_MIN_SIZE = 5 * MB
INSTALLER_MIN_AGE_DAYS = 30
STALE_FILE_MIN_SIZE = 500 * MB
STALE_FILE_MIN_AGE_DAYS = 180
HUGE_FILE_SIZE = 1024 * MB
STALE_FOLDER_MIN_SIZE = 500 * MB
STALE_FOLDER_MIN_AGE_DAYS = 365
JUNK_MIN_SIZE = 1 * MB
MAX_SUGGESTIONS = 300


def human_size(size):
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if size < 1024:
            return f"{size:.2f} {unit}"
        size /= 1024
    return f"{size:.2f} PB"


def age_text(days):
    days = int(days)
    if days >= 730:
        return f"{days // 365} years"
    if days >= 60:
        return f"{days // 30} months"
    return f"{days} days"


def path_inside(child, parent):
    """True if child is parent or lies inside it (case-insensitive on Windows)."""
    child = os.path.normcase(os.path.abspath(child))
    parent = os.path.normcase(os.path.abspath(parent))
    try:
        return os.path.commonpath([child, parent]) == parent
    except ValueError:
        return False


def temp_folder_paths():
    found = set()
    for variable in ("TEMP", "TMP"):
        value = os.environ.get(variable)
        if value:
            found.add(os.path.normcase(os.path.abspath(value)))
    local = os.environ.get("LOCALAPPDATA")
    if local:
        found.add(os.path.normcase(os.path.abspath(os.path.join(local, "Temp"))))
    return found


class ScanJob:
    """Progress of a running scan; the scan thread writes it, the window reads it."""

    def __init__(self, root):
        self.root = root
        self.cancel = threading.Event()
        self.files = 0
        self.bytes = 0
        self.current = ""
        self.result = None
        self.error = None
        self.finished = False


class ScanResult:
    def __init__(self, root):
        self.root = root
        self.file_count = 0
        self.folder_count = 0
        self.total_bytes = 0
        self.unreadable = 0
        self.seconds = 0.0
        self.cancelled = False
        self.direct = {}          # folder -> bytes of files directly inside it
        self.newest = {}          # folder -> newest modified time of files directly inside it
        self.exes = {}            # folder -> number of .exe files directly inside it
        self.children = {}        # folder -> subfolders that were scanned
        self.sizes = {}           # folder -> total bytes including everything below it
        self.newest_all = {}      # folder -> newest modified time anywhere below it
        self.exe_counts = {}      # folder -> number of .exe files anywhere below it
        self.categories = {}      # type name -> [file count, bytes]
        self.top_files = []       # the largest files: (size, path, modified)
        self.big_files = []       # files of 50 MB or more, for the suggestion rules
        self.installers = []      # installers/disk images found in Downloads folders
        self.junk = []            # (path, group, action, level, reason)
        self.launchers = []       # game library folders (Steam, Epic, ...)


def push_largest(heap, limit, item):
    if len(heap) < limit:
        heapq.heappush(heap, item)
    elif item > heap[0]:
        heapq.heapreplace(heap, item)


def scan_folder(root, cancel, progress=None):
    """Walk a folder tree and total it up. Symbolic links and junctions are never followed.

    Runs in a background thread. Unreadable folders are counted and skipped.
    """
    root = os.path.abspath(root)
    result = ScanResult(root)
    started = time.time()
    temp_paths = temp_folder_paths()
    stack = [root]

    while stack:
        if cancel.is_set():
            result.cancelled = True
            break
        folder = stack.pop()
        try:
            with os.scandir(folder) as scan:
                entries = list(scan)
        except OSError:
            result.unreadable += 1
            continue

        result.folder_count += 1
        folder_parts = folder.lower().split(os.sep)
        in_downloads = folder_parts[-1] == "downloads"   # directly inside Downloads, not in an unpacked subfolder
        in_appdata = "appdata" in folder_parts
        direct = exe_count = 0
        newest = 0.0
        children = []

        for entry in entries:
            try:
                if entry.is_symlink():
                    continue
                info = entry.stat(follow_symlinks=False)
                if getattr(info, "st_file_attributes", 0) & 0x400:
                    continue  # junctions and other reparse points
                name = entry.name.lower()

                if entry.is_dir(follow_symlinks=False):
                    children.append(entry.path)
                    if os.path.normcase(entry.path) in temp_paths:
                        result.junk.append((
                            entry.path, "Temporary files", "info", "info",
                            "Windows temporary files. Clear them with Settings > System > Storage > "
                            "Temporary files; that is safer than deleting the folder yourself."))
                    elif name == "__pycache__":
                        result.junk.append((
                            entry.path, "Python caches", "delete", "safe",
                            "Python rebuilds this cache automatically."))
                    elif name == "node_modules":
                        result.junk.append((
                            entry.path, "Developer files", "delete", "check",
                            "Re-created by 'npm install'. Only delete it if you don't need to work on the project offline."))
                    elif name in APP_CACHE_FOLDERS and in_appdata:
                        result.junk.append((
                            entry.path, "App caches", "delete", "check",
                            "Apps rebuild their cache automatically. Close the app before deleting it."))
                    if name in LAUNCHER_FOLDERS:
                        result.launchers.append(entry.path)
                    continue

                size, modified = info.st_size, info.st_mtime
                extension = os.path.splitext(name)[1]
                category = EXTENSION_CATEGORY.get(extension, "Other")
                slot = result.categories.setdefault(category, [0, 0])
                slot[0] += 1
                slot[1] += size
                result.file_count += 1
                result.total_bytes += size
                direct += size
                newest = max(newest, modified)
                if extension == ".exe":
                    exe_count += 1
                push_largest(result.top_files, 300, (size, entry.path, modified))
                if size >= 50 * MB:
                    push_largest(result.big_files, 1500, (size, entry.path, modified))
                if (in_downloads and extension in INSTALLER_EXTENSIONS
                        and size >= INSTALLER_MIN_SIZE and len(result.installers) < 3000):
                    result.installers.append((size, entry.path, modified))
            except OSError:
                result.unreadable += 1

        result.direct[folder] = direct
        result.newest[folder] = newest
        result.exes[folder] = exe_count
        result.children[folder] = children
        stack.extend(children)
        if progress is not None:
            progress.files = result.file_count
            progress.bytes = result.total_bytes
            progress.current = folder

    # Roll the totals up so every folder knows its full size (deepest folders first).
    result.sizes = dict(result.direct)
    result.newest_all = dict(result.newest)
    result.exe_counts = dict(result.exes)
    for folder in sorted(result.direct, key=len, reverse=True):
        if folder == root:
            continue
        parent = os.path.dirname(folder)
        if parent in result.sizes:
            result.sizes[parent] += result.sizes[folder]
            result.newest_all[parent] = max(result.newest_all[parent], result.newest_all[folder])
            result.exe_counts[parent] += result.exe_counts[folder]
    result.children = {
        folder: [child for child in kids if child in result.direct]
        for folder, kids in result.children.items()
    }
    result.seconds = time.time() - started
    return result


def build_suggestions(result, now, protection_for):
    """Turn a scan into a ranked list of simple, explainable suggestions.

    Every suggestion carries the reason it was made. Nothing here deletes or copies
    anything; the person still has to mark items and confirm.
    """
    found = []
    launcher_roots = list(result.launchers)

    def add(path, size, action, level, group, reason):
        found.append({"path": path, "size": size, "action": action,
                      "level": level, "group": group, "reason": reason})

    def blocked(path):
        risk = protection_for(path)
        return bool(risk and risk[0] == "block")

    def in_launcher(path):
        return any(path_inside(path, root) for root in launcher_roots)

    # 1. Junk that comes back by itself (caches, temp files)
    for path, group, action, level, reason in result.junk:
        size = result.sizes.get(path, 0)
        if size < JUNK_MIN_SIZE or blocked(path) or in_launcher(path):
            continue
        add(path, size, action, level, group, reason)

    # 2. Old installers and disk images sitting in Downloads
    for size, path, modified in result.installers:
        age = (now - modified) / DAY
        if age < INSTALLER_MIN_AGE_DAYS or protection_for(path) or in_launcher(path):
            continue
        name = os.path.basename(path).lower()
        if os.path.splitext(name)[1] != ".exe" or any(word in name for word in INSTALLER_WORDS):
            add(path, size, "delete", "check", "Old installers",
                f"Installer or disk image in Downloads, {age_text(age)} old. It can be downloaded again.")
        else:
            add(path, size, "delete", "review", "Old downloaded programs",
                f"Program file in Downloads, {age_text(age)} old. It may be an installer, or a portable app "
                "you still use, so check before deleting it.")

    # 3. Big files nobody has touched, and very large files in general
    for size, path, modified in result.big_files:
        name = os.path.basename(path).lower()
        if name in SYSTEM_FILE_NAMES or protection_for(path) or in_launcher(path):
            continue
        extension = os.path.splitext(name)[1]
        category = EXTENSION_CATEGORY.get(extension, "Other")
        age = (now - modified) / DAY
        if (category in ARCHIVE_CATEGORIES and extension != ".exe"
                and size >= STALE_FILE_MIN_SIZE and age >= STALE_FILE_MIN_AGE_DAYS):
            add(path, size, "usb", "check", "Large old files",
                f"Large file ({extension or 'no extension'}), not modified in {age_text(age)}. "
                "A good candidate to keep on your USB drive instead.")
        elif size >= HUGE_FILE_SIZE:
            add(path, size, "review", "review", "Very large files",
                f"Very large file, last modified {age_text(age)} ago. "
                "Move it to USB or delete it if you no longer need it here.")

    # 4. Whole folders nothing has touched for a long time
    for folder, size in result.sizes.items():
        if folder == result.root or size < STALE_FOLDER_MIN_SIZE:
            continue
        newest = result.newest_all.get(folder, 0)
        if not newest:
            continue
        age = (now - newest) / DAY
        if age < STALE_FOLDER_MIN_AGE_DAYS:
            continue
        if (protection_for(folder) or in_launcher(folder)
                or any(path_inside(root, folder) for root in launcher_roots)):
            continue
        if result.exe_counts.get(folder, 0) > 0:
            add(folder, size, "usb", "review", "Untouched folders",
                f"Nothing here has changed in {age_text(age)}. It contains programs (.exe), "
                "which may stop working if moved, so check before archiving it.")
        else:
            add(folder, size, "usb", "check", "Untouched folders",
                f"Nothing in this folder has changed in {age_text(age)}. "
                "A good candidate to archive on your USB drive.")

    # 5. Game libraries: managed by their launcher, never by hand
    for root in launcher_roots:
        size = result.sizes.get(root, 0)
        if size >= HUGE_FILE_SIZE and not blocked(root):
            add(root, size, "launcher", "info", "Game libraries",
                "Game library. Move or uninstall games from inside the launcher (Steam, Epic, Xbox...); "
                "copying or deleting the folder by hand can break them. The Games & Apps window lists each game.")

    # Keep only the outermost suggestion where they overlap, then rank them.
    found.sort(key=lambda item: len(item["path"]))
    kept = []
    for item in found:
        if any(path_inside(item["path"], other["path"]) for other in kept):
            continue
        kept.append(item)
    order = {"safe": 0, "check": 1, "review": 2, "info": 3}
    kept.sort(key=lambda item: (order[item["level"]], -item["size"]))
    return kept[:MAX_SUGGESTIONS]



# ----------------------------------------------------------------------
# Duplicate finder (no window code in here)
# ----------------------------------------------------------------------
DUPLICATE_MIN_SIZE = 1 * MB
# Program files are never treated as duplicates: apps often ship identical copies on purpose.
PROGRAM_EXTENSIONS = {".exe", ".dll", ".sys", ".msi", ".msix", ".pyd", ".so", ".dylib", ".drv", ".ocx", ".jar"}
# Folders where identical files are normal and deleting one breaks something.
SKIP_DUPLICATE_DIRS = {".git", "node_modules", "site-packages", ".venv", "venv",
                       "$recycle.bin", "system volume information", "windows.old", "winsxs"}


def file_sha256(path, on_bytes=None, cancel=None, chunk_size=1024 * 1024):
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        while True:
            if cancel is not None and cancel.is_set():
                raise TransferCancelled()
            block = handle.read(chunk_size)
            if not block:
                break
            digest.update(block)
            if on_bytes:
                on_bytes(len(block))
    return digest.hexdigest()


def sample_sha256(path, size, span=64 * 1024):
    """A cheap fingerprint from the start and end of a file, used to rule out most non-matches."""
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        digest.update(handle.read(span))
        if size > span * 2:
            handle.seek(size - span)
            digest.update(handle.read(span))
    return digest.hexdigest()


class DuplicateJob:
    """Progress of a running duplicate scan; the scan thread writes it, the window reads it."""

    def __init__(self, root):
        self.root = root
        self.cancel = threading.Event()
        self.text = "Starting..."
        self.fraction = 0.0
        self.files = 0
        self.result = None
        self.error = None
        self.finished = False


class DuplicateResult:
    def __init__(self, root):
        self.root = root
        self.groups = []          # {"size", "hash", "files": [{"path", "mtime", "app"}]}, biggest waste first
        self.files_checked = 0    # files that were big enough to be considered
        self.unreadable = 0
        self.hardlinks = 0        # extra names for the same file, which are not duplicates
        self.cancelled = False
        self.seconds = 0.0

    @property
    def wasted_bytes(self):
        return sum(group["size"] * (len(group["files"]) - 1) for group in self.groups)


def find_duplicates(root, cancel, job=None, min_size=DUPLICATE_MIN_SIZE, skip_dir=None):
    """Find files with identical contents under root.

    Files are grouped by size, then by a fingerprint of their start and end, and only the
    survivors are read in full and compared by SHA-256. Symbolic links, junctions, empty files,
    program files and folders where duplicates are normal are ignored. Runs in a background thread.
    """
    started = time.time()
    root = os.path.abspath(root)
    result = DuplicateResult(root)
    min_size = max(min_size, 1)

    def report(text=None, fraction=None, files=None):
        if job is None:
            return
        if text is not None:
            job.text = text
        if fraction is not None:
            job.fraction = fraction
        if files is not None:
            job.files = files

    # 1. Walk the folders and group candidate files by size.
    by_size = {}
    stack = [root]
    while stack and not result.cancelled:
        if cancel.is_set():
            result.cancelled = True
            break
        folder = stack.pop()
        try:
            with os.scandir(folder) as scan:
                entries = list(scan)
        except OSError:
            result.unreadable += 1
            continue
        found = []
        has_program = False
        for entry in entries:
            try:
                if entry.is_symlink():
                    continue
                info = entry.stat(follow_symlinks=False)
                attributes = getattr(info, "st_file_attributes", 0)
                if attributes & 0x400:
                    continue  # junctions and other reparse points
                if entry.is_dir(follow_symlinks=False):
                    name = entry.name.lower()
                    if name in SKIP_DUPLICATE_DIRS or name in LAUNCHER_FOLDERS:
                        continue
                    if skip_dir is not None and skip_dir(entry.path):
                        continue
                    stack.append(entry.path)
                    continue
                if os.path.splitext(entry.name)[1].lower() in PROGRAM_EXTENSIONS:
                    has_program = True
                    continue
                if attributes & 0x4:
                    continue  # Windows system files
                if info.st_size >= min_size:
                    found.append((entry.path, info.st_size, info.st_mtime))
            except OSError:
                result.unreadable += 1
        for path, size, modified in found:
            by_size.setdefault(size, []).append((path, modified, has_program))
            result.files_checked += 1
        report(text=f"Looking at files... {result.files_checked:,} found", files=result.files_checked)

    # 2. Same size only; names that point at the very same file (hard links) are not duplicates.
    candidates = []
    if not result.cancelled:
        for size, files in by_size.items():
            if len(files) < 2:
                continue
            seen_ids, kept = set(), []
            for path, modified, app in files:
                try:
                    info = os.stat(path)
                except OSError:
                    result.unreadable += 1
                    continue
                identity = (info.st_dev, info.st_ino)
                if info.st_ino and identity in seen_ids:
                    result.hardlinks += 1
                    continue
                seen_ids.add(identity)
                kept.append((path, modified, app))
            if len(kept) >= 2:
                candidates.append((size, kept))

    # 3. Cheap fingerprint from the start and end of each file.
    buckets = []
    total_files = sum(len(files) for _, files in candidates) or 1
    done_files = 0
    if not result.cancelled:
        for size, files in candidates:
            by_sample = {}
            for path, modified, app in files:
                if cancel.is_set():
                    result.cancelled = True
                    break
                done_files += 1
                report(text=f"Comparing: {os.path.basename(path)}", fraction=0.1 * done_files / total_files)
                try:
                    key = sample_sha256(path, size)
                except OSError:
                    result.unreadable += 1
                    continue
                by_sample.setdefault(key, []).append((path, modified, app))
            if result.cancelled:
                break
            buckets += [(size, group) for group in by_sample.values() if len(group) >= 2]

    # 4. Read the survivors in full and compare their contents.
    if not result.cancelled:
        total_bytes = sum(size * len(group) for size, group in buckets) or 1
        state = {"done": 0}

        def progressed(amount):
            state["done"] += amount
            report(fraction=0.1 + 0.9 * min(state["done"] / total_bytes, 1.0))

        try:
            for size, group in buckets:
                by_hash = {}
                for path, modified, app in group:
                    report(text=f"Reading: {path}")
                    try:
                        digest = file_sha256(path, on_bytes=progressed, cancel=cancel)
                    except OSError:
                        result.unreadable += 1
                        continue
                    by_hash.setdefault(digest, []).append(
                        {"path": path, "mtime": modified, "app": app})
                for digest, files in by_hash.items():
                    if len(files) >= 2:
                        result.groups.append({"size": size, "hash": digest, "files": files})
        except TransferCancelled:
            result.cancelled = True

    result.groups.sort(key=lambda g: g["size"] * (len(g["files"]) - 1), reverse=True)
    report(fraction=1.0 if not result.cancelled else None)
    result.seconds = time.time() - started
    return result


def choose_keepers(groups, strategy="oldest"):
    """Decide which copy in each group to keep. Returns {path: 'keep' or 'delete'}.

    At least one copy is always kept. Copies sitting in a program's folder are always kept,
    and only copies outside program folders are offered for deletion.
    """
    actions = {}
    for group in groups:
        files = group["files"]
        program_copies = [f for f in files if f["app"]]
        if program_copies:
            for f in files:
                actions[f["path"]] = "keep" if f["app"] else "delete"
            continue
        if strategy == "newest":
            ordered = sorted(files, key=lambda f: (-f["mtime"], len(f["path"]), f["path"]))
        elif strategy == "shortest":
            ordered = sorted(files, key=lambda f: (len(f["path"]), f["mtime"], f["path"]))
        else:
            ordered = sorted(files, key=lambda f: (f["mtime"], len(f["path"]), f["path"]))
        actions[ordered[0]["path"]] = "keep"
        for f in ordered[1:]:
            actions[f["path"]] = "delete"
    return actions



# ----------------------------------------------------------------------
# Game and application detection (no window code in here)
# ----------------------------------------------------------------------
GAME_LARGE_SIZE = 20 * 1024 * MB      # games at least this big are highlighted
GAME_IDLE_DAYS = 180                  # "not played in" threshold
APP_MIN_SIZE = 100 * MB               # smaller programs are left out of the list
SKIP_STEAM_TOOLS = ("steamworks common redistributables", "steam linux runtime", "proton ")
# Folders (relative to a drive) that hold one sub-folder per installed game.
KNOWN_GAME_ROOTS = (
    ("XboxGames", "Xbox app"), ("Riot Games", "Riot Games"), ("GOG Games", "GOG"),
    ("EA Games", "EA app"), ("Origin Games", "EA app"),
    ("Program Files\\EA Games", "EA app"), ("Program Files (x86)\\Origin Games", "EA app"),
    ("Program Files (x86)\\Ubisoft\\Ubisoft Game Launcher\\games", "Ubisoft Connect"),
)
NO_HAND_MOVES = ("Don't move or delete the game's folder by hand: the launcher won't know, "
                 "and the game can show as installed but fail to start.")
LAUNCHER_HELP = {
    "Steam": (
        "To MOVE it: in Steam, first add the destination drive as a library folder (Steam > Settings > Storage; "
        "older versions: Settings > Downloads > Steam Library Folders). Then right-click the game > Properties > "
        "Installed Files (called Local Files in older versions) > Move install folder. Steam moves one game at a time.\n"
        "To REMOVE it: right-click the game in your Steam library > Manage > Uninstall."),
    "Epic Games": (
        "To MOVE it: Epic publishes a support article for this, titled 'How to move an installed game from the "
        "Epic Games Launcher to another directory on your computer'. Follow its steps rather than just moving the folder.\n"
        "To REMOVE it: in the Epic Games Launcher, open your Library, use the game's menu and choose Uninstall."),
    "GOG": (
        "To MOVE it: GOG has no one-click move. Back up your saves, copy the game's folder to the new drive, uninstall "
        "the game in GOG Galaxy, then use Galaxy's Settings > 'Scan folders for GOG Games' and pick the new folder. "
        "Galaxy should repair and register the game (if not, use Manage installation > Verify / Repair). "
        "Reinstalling to the new drive also works.\n"
        "To REMOVE it: in GOG Galaxy choose Manage installation > Uninstall."),
    "Xbox app": (
        "To MOVE it: Windows Settings > Apps > Installed apps > find the game > Move (not every game supports it; "
        "the destination should be an NTFS drive with enough free space).\n"
        "To REMOVE it: uninstall it from the same Installed apps list."),
}
DEFAULT_HELP = (
    "Move or remove it from inside its own launcher, or from Windows Settings > Apps > Installed apps. "
    "If the launcher has no move option, uninstalling and reinstalling on the other drive is the safe route.")
PROGRAM_HELP = (
    "To REMOVE it: Windows Settings > Apps > Installed apps > Uninstall (or the program's own uninstaller). "
    "Deleting a program's folder by hand leaves it half-installed. To MOVE it, the usual route is to uninstall it "
    "and reinstall it on the other drive.")


def to_int(value):
    try:
        return int(value)
    except (TypeError, ValueError):
        return 0


def read_text(path):
    with open(path, encoding="utf-8", errors="replace") as handle:
        return handle.read()


def in_game_library(path):
    """True if the path is inside a launcher's game library folder (steamapps, XboxGames, ...)."""
    return any(part.lower() in LAUNCHER_FOLDERS for part in os.path.abspath(path).split(os.sep))


def parse_vdf(text):
    """Parse Valve's KeyValues text format (Steam's .vdf / .acf files) into nested dicts.

    Keys are lower-cased. Malformed input gives whatever could be read, never an error.
    """
    tokens = []
    for match in re.finditer(r'"((?:[^"\\]|\\.)*)"|([{}])', text):
        if match.group(2):
            tokens.append(match.group(2))
        else:
            tokens.append(("s", re.sub(r"\\(.)", r"\1", match.group(1))))
    position = 0

    def block():
        nonlocal position
        found = {}
        while position < len(tokens):
            token = tokens[position]
            position += 1
            if token == "}":
                return found
            if token == "{":
                continue
            key = token[1].lower()
            if position >= len(tokens):
                break
            following = tokens[position]
            if following == "{":
                position += 1
                found[key] = block()
            elif following == "}":
                found[key] = ""
            else:
                found[key] = following[1]
                position += 1
        return found

    return block()


def make_game(title, launcher, path, size=None, when=None, when_kind=None):
    return {"name": title, "launcher": launcher, "path": os.path.abspath(path),
            "size": size or None, "when": when or None, "when_kind": when_kind if when else None}


def steam_library_paths(steam_dir):
    """Every Steam library folder for one Steam install (the install itself plus libraries on other drives)."""
    paths = [os.path.abspath(steam_dir)]
    for relative in (("config", "libraryfolders.vdf"), ("steamapps", "libraryfolders.vdf")):
        try:
            data = parse_vdf(read_text(os.path.join(steam_dir, *relative)))
        except OSError:
            continue
        for key, value in data.get("libraryfolders", data).items():
            path = value.get("path") if isinstance(value, dict) else value   # old files list the path directly
            if key.isdigit() and isinstance(path, str) and path and os.path.isdir(path):
                paths.append(os.path.abspath(path))
    unique, seen = [], set()
    for path in paths:
        if os.path.normcase(path) not in seen:
            seen.add(os.path.normcase(path))
            unique.append(path)
    return unique


def steam_games(library):
    games = []
    apps = os.path.join(library, "steamapps")
    try:
        names = sorted(os.listdir(apps))
    except OSError:
        return games
    for name in names:
        if not (name.startswith("appmanifest_") and name.endswith(".acf")):
            continue
        try:
            data = parse_vdf(read_text(os.path.join(apps, name))).get("appstate", {})
        except OSError:
            continue
        title, installdir = data.get("name"), data.get("installdir")
        if not title or not installdir or title.lower().startswith(SKIP_STEAM_TOOLS):
            continue
        path = os.path.join(apps, "common", installdir)
        if not os.path.isdir(path):
            continue  # a manifest left behind after the game was removed
        played, updated = to_int(data.get("lastplayed")), to_int(data.get("lastupdated"))
        games.append(make_game(title, "Steam", path, to_int(data.get("sizeondisk")),
                               played or updated, "played" if played else "updated"))
    return games


def epic_games(manifest_dir):
    games = []
    try:
        names = sorted(os.listdir(manifest_dir))
    except OSError:
        return games
    for name in names:
        if not name.endswith(".item"):
            continue
        try:
            with open(os.path.join(manifest_dir, name), encoding="utf-8", errors="replace") as handle:
                data = json.load(handle)
        except (OSError, ValueError):
            continue
        if not isinstance(data, dict):
            continue
        title, path = data.get("DisplayName"), data.get("InstallLocation")
        main, app = data.get("MainGameAppName"), data.get("AppName")
        if not title or not path or not os.path.isdir(path) or (main and app and main != app):
            continue  # unreadable, removed, or an add-on rather than a game
        games.append(make_game(title, "Epic Games", path, to_int(data.get("InstallSize"))))
    return games


def games_in_root(root, launcher):
    """Games stored one-per-folder inside a launcher's own games folder."""
    games = []
    try:
        with os.scandir(root) as scan:
            for entry in scan:
                if entry.is_dir(follow_symlinks=False) and not entry.is_symlink():
                    games.append(make_game(entry.name, launcher, entry.path))
    except OSError:
        pass
    return games


def detect_games(steam_dirs=(), epic_dir=None, gog_entries=(), game_roots=()):
    """Collect installed games from every source, without duplicates, biggest first."""
    found = []
    for steam_dir in steam_dirs:
        for library in steam_library_paths(steam_dir):
            found += steam_games(library)
    if epic_dir:
        found += epic_games(epic_dir)
    for entry in gog_entries:
        if entry.get("name") and entry.get("path") and os.path.isdir(entry["path"]):
            found.append(make_game(entry["name"], "GOG", entry["path"]))
    for root, launcher in game_roots:
        found += games_in_root(root, launcher)
    unique, seen = [], set()
    for game in found:
        key = os.path.normcase(game["path"])
        if key not in seen:
            seen.add(key)
            unique.append(game)
    unique.sort(key=lambda game: game["size"] or 0, reverse=True)
    return unique


def game_flags(game, now):
    """(is it large, is it idle, short note) for highlighting a game."""
    size = game.get("size") or 0
    large = size >= GAME_LARGE_SIZE
    age = (now - game["when"]) / DAY if game.get("when") else 0
    idle = game.get("when_kind") == "played" and age >= GAME_IDLE_DAYS
    notes = []
    if large:
        notes.append("Large")
    if idle:
        notes.append(f"Not played in {age_text(age)}")
    elif game.get("when_kind") == "updated" and age >= 365:
        notes.append(f"Last updated {age_text(age)} ago")
    return large, idle, ", ".join(notes)


def game_guidance(game):
    return LAUNCHER_HELP.get(game["launcher"], DEFAULT_HELP) + "\n" + NO_HAND_MOVES


# --- the Windows-only parts: kept small, and quiet when not on Windows --------
def registry_hive(name):
    import winreg
    return {"HKLM": winreg.HKEY_LOCAL_MACHINE, "HKCU": winreg.HKEY_CURRENT_USER}[name]


def registry_subkeys(hive, path):
    try:
        import winreg
        names = []
        with winreg.OpenKey(registry_hive(hive), path) as key:
            while True:
                try:
                    names.append(winreg.EnumKey(key, len(names)))
                except OSError:
                    return names
    except (ImportError, OSError):
        return []


def registry_values(hive, path, names):
    """The named values of one registry key; anything missing comes back as None."""
    found = {name: None for name in names}
    try:
        import winreg
        with winreg.OpenKey(registry_hive(hive), path) as key:
            for name in names:
                try:
                    found[name] = winreg.QueryValueEx(key, name)[0]
                except OSError:
                    pass
    except (ImportError, OSError):
        pass
    return found


def discover_game_sources():
    """Where this computer keeps its game libraries: arguments for detect_games()."""
    sources = {"steam_dirs": [], "epic_dir": None, "gog_entries": [], "game_roots": []}
    home = os.path.expanduser("~")
    if os.name != "nt":
        for path in (os.path.join(home, ".steam", "steam"), os.path.join(home, ".local", "share", "Steam")):
            if os.path.isdir(path):
                sources["steam_dirs"].append(path)
        return sources

    steam = [registry_values("HKCU", r"SOFTWARE\Valve\Steam", ["SteamPath"])["SteamPath"],
             registry_values("HKLM", r"SOFTWARE\WOW6432Node\Valve\Steam", ["InstallPath"])["InstallPath"],
             os.path.join(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"), "Steam")]
    seen = set()
    for path in steam:
        if path and os.path.isdir(path) and os.path.normcase(os.path.abspath(path)) not in seen:
            seen.add(os.path.normcase(os.path.abspath(path)))
            sources["steam_dirs"].append(os.path.abspath(path))

    program_data = os.environ.get("ProgramData", r"C:\ProgramData")
    sources["epic_dir"] = os.path.join(program_data, "Epic", "EpicGamesLauncher", "Data", "Manifests")

    gog_base = r"SOFTWARE\WOW6432Node\GOG.com\Games"
    for sub in registry_subkeys("HKLM", gog_base):
        values = registry_values("HKLM", gog_base + "\\" + sub, ["gameName", "path"])
        if values["gameName"] and values["path"]:
            sources["gog_entries"].append({"name": values["gameName"], "path": values["path"]})

    try:
        mask = ctypes.windll.kernel32.GetLogicalDrives()
    except Exception:
        mask = 0
    for index in range(26):
        if mask & (1 << index):
            drive = chr(ord("A") + index) + ":\\"
            for relative, launcher in KNOWN_GAME_ROOTS:
                folder = os.path.join(drive, *relative.split("\\"))
                if os.path.isdir(folder):
                    sources["game_roots"].append((folder, launcher))
    return sources


UNINSTALL_KEYS = (
    ("HKLM", r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall"),
    ("HKLM", r"SOFTWARE\WOW6432Node\Microsoft\Windows\CurrentVersion\Uninstall"),
    ("HKCU", r"SOFTWARE\Microsoft\Windows\CurrentVersion\Uninstall"),
)


def read_installed_programs():
    """Programs listed in Windows' Installed apps (empty on other systems)."""
    if os.name != "nt":
        return []
    programs = {}
    wanted = ["DisplayName", "Publisher", "DisplayVersion", "EstimatedSize", "InstallLocation",
              "SystemComponent", "ParentKeyName"]
    for hive, base in UNINSTALL_KEYS:
        for sub in registry_subkeys(hive, base):
            values = registry_values(hive, base + "\\" + sub, wanted)
            name = values["DisplayName"]
            if not name or values["SystemComponent"] == 1 or values["ParentKeyName"]:
                continue
            lowered = name.lower()
            if lowered.startswith("steam app ") or "update for" in lowered or lowered.startswith("security update"):
                continue
            estimate = values["EstimatedSize"]
            programs[lowered] = {
                "name": name, "publisher": values["Publisher"] or "", "version": values["DisplayVersion"] or "",
                "size": estimate * 1024 if isinstance(estimate, int) and estimate > 0 else None,
                "path": (values["InstallLocation"] or "").strip().strip('"'),
            }
    return list(programs.values())


def filter_programs(programs, game_paths, min_size=APP_MIN_SIZE):
    """Keep the big programs that aren't already shown as games.

    A program with an unknown size but a real install folder is kept for now; its folder gets measured.
    """
    kept = []
    for program in programs:
        path = program["path"]
        if path and any(path_inside(path, game) or path_inside(game, path) for game in game_paths):
            continue
        folder_known = bool(path) and os.path.isdir(path)
        if program["size"] is None and not folder_known:
            continue
        if program["size"] is not None and program["size"] < min_size:
            continue
        kept.append(dict(program, path=path if folder_known else ""))
    kept.sort(key=lambda program: program["size"] or 0, reverse=True)
    return kept


class GameJob:
    """A running detection; the worker thread fills it in and the window reads it."""

    def __init__(self):
        self.games = []
        self.programs = []
        self.error = None
        self.finished = False


class TransferCancelled(Exception):
    pass


class ProgressBar(tk.Canvas):
    """A simple progress bar whose colour we control.

    The native Windows progress bar ignores colour settings, so this one is
    drawn by hand and can turn red while deleting.
    """

    TROUGH = "#e3e3e3"

    def __init__(self, parent, height=22, color=COPY_COLOR):
        super().__init__(parent, height=height, highlightthickness=0, bd=0, bg=self.TROUGH)
        self.fraction = 0.0
        self.color = color
        self.bind("<Configure>", lambda event: self.redraw())

    def set(self, fraction, color=None):
        self.fraction = max(0.0, min(1.0, fraction))
        if color is not None:
            self.color = color
        self.redraw()

    def redraw(self):
        self.delete("fill")
        filled = int(self.winfo_width() * self.fraction)
        if filled > 0:
            self.create_rectangle(
                0, 0, filled, self.winfo_height(),
                fill=self.color, width=0, tags="fill"
            )


class JobState:
    """Progress shared between a background job (copy or delete) and the window.

    The job thread only writes to this object and never touches the widgets;
    the window reads it a few times a second and draws the progress bar.
    """

    def __init__(self, item_count, total_bytes, total_units):
        self.item_count = item_count
        self.total_bytes = total_bytes
        self.total_units = max(total_units, 1)
        self.done_units = 0
        self.text = "Starting..."
        self.item_index = 0
        self.cancel = threading.Event()
        self.cancelled = False
        self.finished = False
        self.failed = []
        self.partial = None
        self.started = time.time()
        self.thread = None

    def add_units(self, amount):
        self.done_units += amount


class TransferState(JobState):
    color = COPY_COLOR
    title = "Transfer in progress"

    def __init__(self, sources, usb_root, total_bytes):
        # Each byte is copied once, then read twice (original + copy) to verify.
        super().__init__(len(sources), total_bytes, total_bytes * 3)
        self.sources = sources
        self.usb_root = usb_root
        self.successful = []
        self.copies = {}              # original path -> verified copy on the USB


class DeleteState(JobState):
    color = DELETE_COLOR
    title = "Deleting"

    def __init__(self, items, mode):
        total = sum(item["size"] for item in items)
        super().__init__(len(items), total, total)
        self.items = items
        self.mode = mode              # "recycle" or "permanent"
        self.recycled = []            # (path, size) confirmed in the Recycle Bin
        self.permanent = []           # (path, size) deleted for good, as asked
        self.unconfirmed = []         # (path, size) sent to the bin but not seen there
        self.skipped = []             # (path, reason) left untouched
        self.log_ok = True


class DriveOrganizer:
    def __init__(self, root):
        self.root = root
        self.root.title("Drive Organizer")
        self.root.geometry("1150x720")
        self.root.minsize(850, 550)

        self.current_folder = None
        self.back_stack = []
        self.forward_stack = []
        self.entries = []            # items in the current folder
        self.usb_sel = set()         # paths marked for USB transfer
        self.del_sel = set()         # paths marked for deletion
        self.usb_path = None
        self.usb_free = None
        self.job = None              # the copy or delete that is running, if any
        self.analyzer = None         # the Storage Analyzer window, when open
        self.scan_job = None
        self.scan_root = None
        self.analysis = None
        self.suggestions = []
        self.suggestion_lookup = {}
        self.dup_window = None       # the Duplicate Finder window, when open
        self.dup_job = None
        self.dup_root = None
        self.dup_result = None
        self.dup_groups = []
        self.dup_files = {}
        self.dup_group_of = {}
        self.dup_actions = {}
        self.games_window = None     # the Games & Apps window, when open
        self.game_job = None
        self.games = []
        self.programs = []
        self.game_items = {}
        self.game_iid = {}
        self.freed_bytes = 0         # deleted for good this session
        self.binned_bytes = 0        # sent to the Recycle Bin this session
        self.log_path = self.default_log_path()
        self.block_rules, self.warn_rules = self.build_protection_rules()

        self.sort_col = "name"
        self.sort_reverse = False

        # Folder sizes are calculated in the background so the window never freezes.
        self.size_cache = {}
        self.size_pending = set()
        self.job_queue = queue.Queue()
        self.result_queue = queue.Queue()
        threading.Thread(target=self._size_worker, daemon=True).start()

        tk.Label(
            root, text="Drive Organizer",
            font=("Segoe UI", 23, "bold")
        ).pack(pady=(15, 3))

        tk.Label(
            root, text="Organize your files and free up storage",
            font=("Segoe UI", 10)
        ).pack()

        toolbar = tk.Frame(root)
        toolbar.pack(fill="x", padx=15, pady=12)

        tk.Button(toolbar, text="Choose Folder", command=self.choose_folder).pack(side="left", padx=4)
        tk.Button(toolbar, text="Back", command=self.go_back).pack(side="left", padx=4)
        tk.Button(toolbar, text="Forward", command=self.go_forward).pack(side="left", padx=4)
        self.usb_button = tk.Button(toolbar, text="Choose USB", command=self.choose_usb)
        self.usb_button.pack(side="left", padx=4)
        tk.Button(toolbar, text="Clear Selection", command=self.clear_selection).pack(side="left", padx=4)
        tk.Button(toolbar, text="Analyze Storage", command=self.open_analyzer).pack(side="left", padx=4)
        tk.Button(toolbar, text="Find Duplicates", command=self.open_duplicates).pack(side="left", padx=4)
        tk.Button(toolbar, text="Games & Apps", command=self.open_games).pack(side="left", padx=4)
        tk.Button(toolbar, text="Deletion Log", command=self.open_log).pack(side="right", padx=4)
        tk.Button(toolbar, text="Open Recycle Bin", command=self.open_recycle_bin).pack(side="right", padx=4)

        self.location = tk.Label(root, text="No folder selected", anchor="w")
        self.location.pack(fill="x", padx=20, pady=4)

        summary = tk.LabelFrame(root, text="Storage Summary", padx=10, pady=8)
        summary.pack(fill="x", padx=15, pady=8)

        self.usb_total_label = tk.Label(summary, text="To USB: 0.00 B (0 items)")
        self.usb_total_label.pack(side="left", padx=10)

        self.delete_total_label = tk.Label(summary, text="Will free: 0.00 B (0 items)")
        self.delete_total_label.pack(side="left", padx=20)

        self.usb_label = tk.Label(summary, text="USB: Not selected")
        self.usb_label.pack(side="left", padx=20)

        self.recovered_label = tk.Label(summary, text="Freed this session: 0.00 B")
        self.recovered_label.pack(side="left", padx=20)

        main = tk.Frame(root)
        main.pack(fill="both", expand=True, padx=15, pady=8)

        left = tk.Frame(main)
        left.pack(side="left", fill="both", expand=True, padx=5)

        right = tk.Frame(main)
        right.pack(side="left", fill="both", expand=True, padx=5)

        tk.Label(left, text="Folders", font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=5)

        self.folder_table = ttk.Treeview(
            left, columns=("usb", "delete", "name"), show="headings"
        )
        self.folder_table.heading("usb", text="USB")
        self.folder_table.heading("delete", text="Delete")
        self.folder_table.heading("name", text="Folder Name")
        self.folder_table.column("usb", width=45, anchor="center", stretch=False)
        self.folder_table.column("delete", width=55, anchor="center", stretch=False)
        self.folder_table.column("name", width=200)
        self.folder_table.pack(fill="both", expand=True)

        tk.Label(right, text="Contents & Paths", font=("Segoe UI", 12, "bold")).pack(anchor="w", pady=5)

        self.contents_table = ttk.Treeview(
            right,
            columns=("usb", "delete", "name", "type", "size", "path"),
            show="headings"
        )
        self.contents_table.heading("usb", text="USB")
        self.contents_table.heading("delete", text="Delete")
        self.contents_table.heading("path", text="Full Path")
        self.contents_table.column("usb", width=45, anchor="center", stretch=False)
        self.contents_table.column("delete", width=55, anchor="center", stretch=False)
        self.contents_table.column("name", width=125)
        self.contents_table.column("type", width=60)
        self.contents_table.column("size", width=95)
        self.contents_table.column("path", width=240)
        self.contents_table.pack(fill="both", expand=True)
        self.update_headings()

        self.folder_table.bind("<Button-1>", lambda event: self.toggle_click(event, self.folder_table))
        self.contents_table.bind("<Button-1>", lambda event: self.toggle_click(event, self.contents_table))
        self.folder_table.bind("<Double-1>", lambda event: self.open_row(event, self.folder_table))
        self.contents_table.bind("<Double-1>", lambda event: self.open_row(event, self.contents_table))

        self.bottom = tk.Frame(root)
        self.bottom.pack(fill="x", padx=15, pady=12)

        self.copy_button = tk.Button(
            self.bottom, text="Copy USB-Marked Items to USB",
            command=self.transfer_files,
            font=("Segoe UI", 10, "bold")
        )
        self.copy_button.pack(side="right", padx=5)

        self.delete_button = tk.Button(
            self.bottom, text="Delete Marked Items",
            command=self.delete_marked,
            font=("Segoe UI", 10, "bold"), fg=DELETE_COLOR
        )
        self.delete_button.pack(side="right", padx=5)

        self.status = tk.Label(self.bottom, text="Choose a folder to get started.", anchor="w")
        self.status.pack(side="left")

        # Progress panel: created now, shown only while a copy or delete is running.
        self.progress_frame = tk.LabelFrame(root, text="Transfer in progress", padx=10, pady=8)
        self.progress_action = tk.Label(self.progress_frame, text="", anchor="w")
        self.progress_action.pack(fill="x")
        self.progress_bar = ProgressBar(self.progress_frame)
        self.progress_bar.pack(fill="x", pady=6)
        progress_row = tk.Frame(self.progress_frame)
        progress_row.pack(fill="x")
        self.cancel_button = tk.Button(progress_row, text="Cancel", command=self.cancel_transfer)
        self.cancel_button.pack(side="right")
        self.progress_detail = tk.Label(progress_row, text="", anchor="w")
        self.progress_detail.pack(side="left")

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(150, self.poll_results)

    # ------------------------------------------------------------------
    # Sizes
    # ------------------------------------------------------------------
    def format_size(self, size):
        for unit in ("B", "KB", "MB", "GB", "TB"):
            if size < 1024:
                return f"{size:.2f} {unit}"
            size /= 1024
        return f"{size:.2f} PB"

    def get_size(self, path):
        """Return total file size. Symbolic links are not followed."""
        try:
            if os.path.islink(path):
                return 0
            if os.path.isfile(path):
                return os.path.getsize(path)
        except OSError:
            return 0

        total = 0
        for current, folders, filenames in os.walk(path, followlinks=False):
            folders[:] = [
                folder for folder in folders
                if not os.path.islink(os.path.join(current, folder))
            ]
            for filename in filenames:
                file_path = os.path.join(current, filename)
                try:
                    if not os.path.islink(file_path):
                        total += os.path.getsize(file_path)
                except OSError:
                    pass
        return total

    def _size_worker(self):
        while True:
            path = self.job_queue.get()
            try:
                size = self.get_size(path)
            except Exception:
                size = 0
            self.result_queue.put((path, size))

    def request_size(self, path):
        if path in self.size_cache or path in self.size_pending:
            return
        self.size_pending.add(path)
        self.job_queue.put(path)

    def size_text(self, path):
        size = self.size_cache.get(path)
        return "calculating..." if size is None else self.format_size(size)

    def poll_results(self):
        changed = False
        try:
            while True:
                path, size = self.result_queue.get_nowait()
                self.size_cache[path] = size
                self.size_pending.discard(path)
                if self.contents_table.exists(path):
                    self.contents_table.set(path, "size", self.format_size(size))
                changed = True
        except queue.Empty:
            pass

        if changed:
            self.update_summary()
            if self.sort_col == "size":
                self.apply_sort()
        self.root.after(150, self.poll_results)

    # ------------------------------------------------------------------
    # Choosing locations
    # ------------------------------------------------------------------
    def choose_folder(self):
        folder = filedialog.askdirectory(title="Choose a folder to browse")
        if folder:
            # Drop stale sizes, but keep sizes for anything that is selected.
            keep = self.usb_sel | self.del_sel
            self.size_cache = {p: s for p, s in self.size_cache.items() if p in keep}
            self.current_folder = os.path.abspath(folder)
            self.back_stack.clear()
            self.forward_stack.clear()
            self.refresh()

    def choose_usb(self):
        folder = filedialog.askdirectory(title="Choose the USB drive (select its top-level folder)")
        if folder:
            self.usb_path = os.path.abspath(folder)
            folder = self.usb_path
            try:
                self.usb_free = shutil.disk_usage(folder).free
                self.usb_label.config(text=f"USB free: {self.format_size(self.usb_free)}")
                self.status.config(text=f"USB destination: {folder}")
                self.update_summary()
            except OSError as error:
                self.usb_path = None
                self.usb_free = None
                messagebox.showerror("USB error", f"Could not read drive space:\n{error}")

    # ------------------------------------------------------------------
    # Showing the current folder
    # ------------------------------------------------------------------
    def refresh(self):
        if not self.current_folder:
            return

        self.location.config(text=f"Location: {self.current_folder}")
        self.folder_table.delete(*self.folder_table.get_children())
        self.contents_table.delete(*self.contents_table.get_children())
        self.entries = []

        try:
            with os.scandir(self.current_folder) as scan:
                items = list(scan)
        except PermissionError:
            self.status.config(text="Access denied: cannot open this folder.")
            return
        except OSError as error:
            self.status.config(text=f"Error: {error}")
            return

        folder_count = 0
        file_count = 0
        for item in items:
            path = item.path
            try:
                if item.is_symlink():
                    continue
                is_folder = item.is_dir(follow_symlinks=False)
                if is_folder:
                    self.request_size(path)
                    folder_count += 1
                else:
                    self.size_cache[path] = item.stat(follow_symlinks=False).st_size
                    file_count += 1
            except OSError:
                continue
            self.entries.append({"path": path, "name": item.name, "is_folder": is_folder})

        folders = sorted(
            (e for e in self.entries if e["is_folder"]),
            key=lambda e: e["name"].lower()
        )
        for entry in folders:
            self.folder_table.insert(
                "", "end", iid=entry["path"],
                values=(self.mark(entry["path"], self.usb_sel),
                        self.mark(entry["path"], self.del_sel),
                        entry["name"])
            )

        for entry in self.entries:
            self.contents_table.insert(
                "", "end", iid=entry["path"],
                values=(self.mark(entry["path"], self.usb_sel),
                        self.mark(entry["path"], self.del_sel),
                        entry["name"],
                        "Folder" if entry["is_folder"] else "File",
                        self.size_text(entry["path"]),
                        entry["path"])
            )

        self.apply_sort()
        self.update_summary()
        self.status.config(text=f"{folder_count} folders | {file_count} files")

    # ------------------------------------------------------------------
    # Sorting
    # ------------------------------------------------------------------
    def update_headings(self):
        labels = {"name": "Name", "type": "Type", "size": "Size"}
        for column, label in labels.items():
            arrow = ""
            if column == self.sort_col:
                arrow = " ▼" if self.sort_reverse else " ▲"
            self.contents_table.heading(
                column, text=label + arrow,
                command=lambda c=column: self.sort_by(c)
            )

    def sort_by(self, column):
        if column == self.sort_col:
            self.sort_reverse = not self.sort_reverse
        else:
            self.sort_col = column
            self.sort_reverse = (column == "size")  # biggest first by default
        self.update_headings()
        self.apply_sort()

    def apply_sort(self):
        """Reorder the existing rows so scrolling and highlighting are kept."""
        if self.sort_col == "size":
            order = sorted(
                self.entries,
                key=lambda e: (self.size_cache.get(e["path"], -1), e["name"].lower()),
                reverse=self.sort_reverse
            )
        elif self.sort_col == "type":
            order = sorted(
                self.entries,
                key=lambda e: (not e["is_folder"], e["name"].lower()),
                reverse=self.sort_reverse
            )
        else:
            by_name = sorted(
                self.entries,
                key=lambda e: e["name"].lower(),
                reverse=self.sort_reverse
            )
            # Folders stay on top whichever direction the names go.
            order = [e for e in by_name if e["is_folder"]] + [e for e in by_name if not e["is_folder"]]

        for index, entry in enumerate(order):
            if self.contents_table.exists(entry["path"]):
                self.contents_table.move(entry["path"], "", index)

    # ------------------------------------------------------------------
    # Selection (USB and Delete)
    # ------------------------------------------------------------------
    def is_inside(self, child, parent):
        child = os.path.normcase(os.path.abspath(child))
        parent = os.path.normcase(os.path.abspath(parent))
        try:
            return os.path.commonpath([child, parent]) == parent
        except ValueError:
            return False

    def mark(self, path, selection):
        if path in selection:
            return CHECKED
        for existing in selection:
            if self.is_inside(path, existing):
                return COVERED
        return UNCHECKED

    def refresh_marks(self):
        """Update the checkboxes in place without rebuilding the tables."""
        for table in (self.folder_table, self.contents_table):
            for path in table.get_children():
                table.set(path, "usb", self.mark(path, self.usb_sel))
                table.set(path, "delete", self.mark(path, self.del_sel))

    def toggle_click(self, event, table):
        region = table.identify_region(event.x, event.y)
        column = table.identify_column(event.x)
        item = table.identify_row(event.y)
        if region == "cell" and item and column in ("#1", "#2"):
            self.toggle_item(item, "usb" if column == "#1" else "delete")
            return "break"

    def toggle_item(self, path, kind):
        if kind == "usb":
            own, other = self.usb_sel, self.del_sel
            own_name, other_name = "USB", "Delete"
        else:
            own, other = self.del_sel, self.usb_sel
            own_name, other_name = "Delete", "USB"

        if path in own:
            own.discard(path)
        else:
            # An item can't be both transferred and deleted, and a folder
            # can't be handled one way while something inside it is handled another.
            for existing in other:
                if self.is_inside(path, existing) or self.is_inside(existing, path):
                    self.status.config(
                        text=f"Can't mark for {own_name}: it overlaps {existing}, which is marked for {other_name}."
                    )
                    return

            # Don't count both a folder and something inside that folder.
            for existing in own:
                if self.is_inside(path, existing):
                    self.status.config(text="That item is already included in a selected folder.")
                    return
            for existing in list(own):
                if self.is_inside(existing, path):
                    own.discard(existing)

            own.add(path)
            self.request_size(path)

        self.refresh_marks()
        self.update_summary()

    def selection_total(self, selection):
        total = 0
        waiting = False
        for path in selection:
            size = self.size_cache.get(path)
            if size is None:
                waiting = True
                self.request_size(path)
            else:
                total += size
        return total, waiting

    def update_summary(self):
        usb_total, usb_waiting = self.selection_total(self.usb_sel)
        del_total, del_waiting = self.selection_total(self.del_sel)

        usb_text = f"To USB: {self.format_size(usb_total)} ({len(self.usb_sel)} items)"
        if usb_waiting:
            usb_text += " ..."
        elif self.usb_free is not None and usb_total > self.usb_free:
            usb_text += "  ⚠ won't fit"
        self.usb_total_label.config(text=usb_text)

        del_text = f"Will free: {self.format_size(del_total)} ({len(self.del_sel)} items)"
        if del_waiting:
            del_text += " ..."
        self.delete_total_label.config(text=del_text)

    def clear_selection(self):
        self.usb_sel.clear()
        self.del_sel.clear()
        self.refresh_marks()
        self.update_summary()
        self.status.config(text="Selection cleared.")

    # ------------------------------------------------------------------
    # Navigation
    # ------------------------------------------------------------------
    def navigate(self, path):
        if os.path.isdir(path) and not os.path.islink(path):
            if self.current_folder:
                self.back_stack.append(self.current_folder)
            self.forward_stack.clear()
            self.current_folder = path
            self.refresh()

    def open_row(self, event, table):
        if table.identify_region(event.x, event.y) != "cell":
            return
        if table.identify_column(event.x) in ("#1", "#2"):
            return  # double-clicking a checkbox shouldn't open the folder
        path = table.identify_row(event.y)
        if path and os.path.isdir(path) and not os.path.islink(path):
            self.navigate(path)

    def go_back(self):
        if self.back_stack:
            self.forward_stack.append(self.current_folder)
            self.current_folder = self.back_stack.pop()
            self.refresh()

    def go_forward(self):
        if self.forward_stack:
            self.back_stack.append(self.current_folder)
            self.current_folder = self.forward_stack.pop()
            self.refresh()

    # ------------------------------------------------------------------
    # Copying to the USB drive
    # ------------------------------------------------------------------
    def unique_destination(self, source, root=None):
        root = root or self.usb_path
        name = os.path.basename(os.path.normpath(source))
        destination = os.path.join(root, name)
        if not os.path.lexists(destination):
            return destination

        if os.path.isdir(source):
            base, extension = name, ""
        else:
            base, extension = os.path.splitext(name)
        number = 1
        while True:
            candidate = os.path.join(root, f"{base} ({number}){extension}")
            if not os.path.lexists(candidate):
                return candidate
            number += 1

    # ------------------------------------------------------------------
    # Verifying copies
    # ------------------------------------------------------------------
    def hash_file(self, path, chunk_size=1024 * 1024, on_bytes=None, cancel=None):
        return file_sha256(path, on_bytes=on_bytes, cancel=cancel, chunk_size=chunk_size)

    def snapshot(self, path):
        """Map every item under path (relative name -> 'file', 'dir' or 'link').

        Symbolic links are recorded but never followed. A single file or link
        is described as {".": kind}. Unreadable folders raise an error instead
        of being skipped, so a copy can't pass verification by accident.
        """
        if os.path.islink(path):
            return {".": "link"}
        if os.path.isfile(path):
            return {".": "file"}

        def fail(error):
            raise error

        found = {}
        for current, folders, filenames in os.walk(path, followlinks=False, onerror=fail):
            for name in folders + filenames:
                full = os.path.join(current, name)
                relative = os.path.relpath(full, path)
                if os.path.islink(full):
                    found[relative] = "link"
                elif os.path.isdir(full):
                    found[relative] = "dir"
                else:
                    found[relative] = "file"
        return found

    def verify_copy(self, source, destination, progress=None, on_bytes=None, cancel=None):
        """Check that destination is an exact copy of source.

        Compares the list of files and folders, then the size and SHA-256 hash
        of every file. Returns None when everything matches, otherwise a
        sentence describing the first problem found.
        """
        def label(relative):
            return os.path.basename(os.path.normpath(source)) if relative == "." else relative

        try:
            original = self.snapshot(source)
            copied = self.snapshot(destination)

            missing = sorted(set(original) - set(copied))
            if missing:
                return f"{len(missing)} item(s) missing from the copy, for example: {label(missing[0])}"
            extra = sorted(set(copied) - set(original))
            if extra:
                return f"{len(extra)} unexpected item(s) in the copy, for example: {label(extra[0])}"

            for relative, kind in sorted(original.items()):
                if copied[relative] != kind:
                    return f"{label(relative)} is a different kind of item in the copy."

            for relative, kind in sorted(original.items()):
                src = source if relative == "." else os.path.join(source, relative)
                dst = destination if relative == "." else os.path.join(destination, relative)
                if kind == "link":
                    if os.readlink(src) != os.readlink(dst):
                        return f"The link {label(relative)} points somewhere different in the copy."
                elif kind == "file":
                    if progress:
                        progress(f"Verifying: {label(relative)}")
                    if os.path.getsize(src) != os.path.getsize(dst):
                        return f"{label(relative)} has a different size in the copy."
                    if (self.hash_file(src, on_bytes=on_bytes, cancel=cancel)
                            != self.hash_file(dst, on_bytes=on_bytes, cancel=cancel)):
                        return f"{label(relative)} has different contents in the copy."
        except OSError as error:
            return f"Could not finish checking the copy: {error}"
        return None

    # ------------------------------------------------------------------
    # Copying (runs in a background thread so the window stays responsive)
    # ------------------------------------------------------------------
    def copy_file(self, source, destination, state, label=None):
        state.text = f"Copying: {label or os.path.basename(source)}"
        # "xb" refuses to overwrite, so an existing file on the USB is never replaced.
        with open(source, "rb") as reader, open(destination, "xb") as writer:
            while True:
                if state.cancel.is_set():
                    raise TransferCancelled()
                block = reader.read(1024 * 1024)
                if not block:
                    break
                writer.write(block)
                state.add_units(len(block))
        try:
            shutil.copystat(source, destination)  # keep dates and attributes
        except OSError:
            pass

    def copy_link(self, source, destination):
        os.symlink(os.readlink(source), destination, target_is_directory=os.path.isdir(source))

    def copy_item(self, source, destination, state):
        """Copy a file, link or whole folder. Symbolic links are copied as links."""
        if os.path.islink(source):
            self.copy_link(source, destination)
            return
        if os.path.isfile(source):
            self.copy_file(source, destination, state)
            return

        def fail(error):
            raise error

        item_name = os.path.basename(os.path.normpath(source))
        os.makedirs(destination)
        made = [(source, destination)]
        for current, folders, filenames in os.walk(source, followlinks=False, onerror=fail):
            target_dir = destination if current == source else os.path.join(
                destination, os.path.relpath(current, source))
            for name in folders:
                src_path = os.path.join(current, name)
                dst_path = os.path.join(target_dir, name)
                if os.path.islink(src_path):
                    self.copy_link(src_path, dst_path)
                else:
                    os.makedirs(dst_path)
                    made.append((src_path, dst_path))
            for name in filenames:
                if state.cancel.is_set():
                    raise TransferCancelled()
                src_path = os.path.join(current, name)
                dst_path = os.path.join(target_dir, name)
                if os.path.islink(src_path):
                    self.copy_link(src_path, dst_path)
                else:
                    label = os.path.join(item_name, os.path.relpath(src_path, source))
                    self.copy_file(src_path, dst_path, state, label)

        for src_dir, dst_dir in reversed(made):  # folder dates last, deepest first
            try:
                shutil.copystat(src_dir, dst_dir)
            except OSError:
                pass

    def transfer_files(self):
        if self.job:
            return
        if not self.usb_sel:
            messagebox.showwarning("Nothing selected", "Mark files or folders in the USB column first.")
            return
        if not self.usb_path:
            messagebox.showwarning("No USB selected", "Choose your USB drive first.")
            return

        sources = sorted(self.usb_sel)
        for source in sources:
            if self.is_inside(self.usb_path, source):
                messagebox.showerror(
                    "Invalid destination",
                    "The USB destination cannot be inside a selected source folder."
                )
                return

        total_size, waiting = self.selection_total(self.usb_sel)
        if waiting:
            messagebox.showinfo(
                "Still measuring",
                "Drive Organizer is still measuring the size of your selected folders.\n"
                "Try again in a moment."
            )
            return

        try:
            free_space = shutil.disk_usage(self.usb_path).free
        except OSError as error:
            messagebox.showerror("USB error", str(error))
            return

        if total_size > free_space:
            messagebox.showerror(
                "Not enough space",
                f"Selected: {self.format_size(total_size)}\nUSB free: {self.format_size(free_space)}"
            )
            return

        confirmed = messagebox.askyesno(
            "Confirm Copy",
            f"Copy {len(sources)} selected item(s) to the USB?\n\n"
            f"Estimated total: {self.format_size(total_size)}\n\n"
            "Every copy is checked file-by-file against the original. "
            "This reads everything twice, so large transfers take a while.\n\n"
            "Original files will NOT be deleted by this version."
        )
        if not confirmed:
            return

        self.start_job(TransferState(sources, self.usb_path, total_size), self._transfer_worker)

    def start_job(self, state, worker):
        """Show the progress panel and run worker(state) in a background thread."""
        self.job = state
        self.copy_button.config(state="disabled")
        self.delete_button.config(state="disabled")
        self.usb_button.config(state="disabled")
        self.cancel_button.config(state="normal", text="Cancel")
        self.progress_frame.config(text=state.title)
        self.progress_bar.set(0, state.color)
        self.progress_frame.pack(fill="x", padx=15, pady=(0, 8), before=self.bottom)

        state.thread = threading.Thread(target=worker, args=(state,))
        state.thread.start()
        self.poll_job()

    def end_job(self):
        self.job = None
        self.progress_frame.pack_forget()
        self.copy_button.config(state="normal")
        self.delete_button.config(state="normal")
        self.usb_button.config(state="normal")

    def _transfer_worker(self, state):
        """Runs in a background thread. Never touches the window directly."""
        def say(text):
            state.text = text

        try:
            for index, source in enumerate(state.sources, start=1):
                if state.cancel.is_set():
                    state.cancelled = True
                    break
                state.item_index = index
                destination = None
                try:
                    say(f"Copying: {os.path.basename(source)}")
                    if not os.path.lexists(source):
                        raise FileNotFoundError(source)

                    destination = self.unique_destination(source, state.usb_root)
                    self.copy_item(source, destination, state)

                    # Strict verification: same files and folders, same size, same SHA-256.
                    problem = self.verify_copy(
                        source, destination, progress=say,
                        on_bytes=state.add_units, cancel=state.cancel
                    )
                    if problem:
                        raise IOError(problem)
                    state.copies[source] = destination
                    state.successful.append(source)
                except TransferCancelled:
                    state.cancelled = True
                    if destination and os.path.lexists(destination):
                        state.partial = destination
                    break
                except Exception as error:
                    message = str(error)
                    if destination and os.path.lexists(destination):
                        message += f"\nThe incomplete copy was left at: {destination}"
                    state.failed.append((source, message))
        except Exception as error:  # safety net: never leave the window waiting forever
            state.failed.append(("(transfer)", str(error)))
        finally:
            state.finished = True

    def poll_job(self):
        state = self.job
        if not state:
            return
        self.update_progress_display(state)
        if state.finished:
            if isinstance(state, DeleteState):
                self.finish_delete(state)
            else:
                self.finish_transfer(state)
        else:
            self.root.after(100, self.poll_job)

    def update_progress_display(self, state):
        total = max(state.total_units, 1)
        done = min(state.done_units, total)
        fraction = done / total
        self.progress_bar.set(fraction, state.color)   # blue while copying, red while deleting
        self.progress_action.config(text=self.shorten(state.text))

        parts = [
            f"{fraction * 100:.0f}%",
            f"item {max(1, min(state.item_index, state.item_count))} of {state.item_count}",
            f"{self.format_size(state.total_bytes)} total",
        ]
        elapsed = time.time() - state.started
        if elapsed >= 2 and done > 0:
            rate = done / elapsed
            parts.append(f"{self.format_size(rate)}/s")
            parts.append(f"about {self.format_duration((total - done) / rate)} left")
        else:
            parts.append("estimating time...")
        self.progress_detail.config(text="   •   ".join(parts))

    def cancel_transfer(self):
        state = self.job
        if state and not state.finished:
            state.cancel.set()
            self.cancel_button.config(state="disabled", text="Cancelling...")
            state.text = "Cancelling... finishing the current step"

    def finish_transfer(self, state):
        self.end_job()

        lines = [
            f"Copied and verified (contents compared): {len(state.successful)} item(s).",
            f"Failed: {len(state.failed)} item(s).",
        ]
        if state.cancelled:
            title = "Transfer cancelled"
            lines.insert(0, "The transfer was cancelled.")
            if state.partial:
                lines.append(f"\nThe item being copied may be incomplete or unverified on the USB:\n{state.partial}")
            self.status.config(text="Transfer cancelled. Original files were not deleted.")
        else:
            title = "Copy finished"
            self.status.config(text="Copy process finished. Original files were not deleted.")
        lines.append("\nOriginal files were left in place.")
        if state.failed:
            lines.append("\nFirst error:\n" + state.failed[0][1])
        messagebox.showinfo(title, "\n".join(lines))

        try:
            self.usb_free = shutil.disk_usage(state.usb_root).free
            self.usb_label.config(text=f"USB free: {self.format_size(self.usb_free)}")
            self.update_summary()
        except OSError:
            pass

        # Only items that passed full verification may be offered for deletion.
        if state.successful and messagebox.askyesno(
            "Delete the originals?",
            f"{len(state.successful)} item(s) were copied to the USB and verified.\n\n"
            "Do you want to delete the originals from this computer now?\n"
            "You will see the full list and choose how to delete before anything happens."
        ):
            self.begin_deletion(state.successful, state.copies)

    def on_close(self):
        state = self.job
        if state and not state.finished:
            if not messagebox.askyesno(
                "Job in progress",
                "A copy or delete is still running. Cancel it and exit?\n\n"
                "An unfinished copy may be left on the USB drive, and a folder "
                "being deleted may be only partly deleted."
            ):
                return
            state.cancel.set()
            if state.thread:
                state.thread.join(timeout=10)
        self.root.destroy()

    # ------------------------------------------------------------------
    # Deleting (Recycle Bin or permanent) - runs in a background thread
    # ------------------------------------------------------------------
    def default_log_path(self):
        if os.name == "nt":
            base = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
            return os.path.join(base, "DriveOrganizer", "deletion_log.csv")
        return os.path.join(os.path.expanduser("~"), ".drive_organizer", "deletion_log.csv")

    def log_deletion(self, action, size, path, note=""):
        """Append one line to the deletion log. Returns False if it can't be written."""
        try:
            os.makedirs(os.path.dirname(self.log_path), exist_ok=True)
            is_new = not os.path.exists(self.log_path)
            with open(self.log_path, "a", newline="", encoding="utf-8") as handle:
                writer = csv.writer(handle)
                if is_new:
                    writer.writerow(["time", "action", "size_bytes", "path", "note"])
                writer.writerow([datetime.now().isoformat(timespec="seconds"), action, size, path, note])
            return True
        except OSError:
            return False

    def build_protection_rules(self):
        """Folders that must never be deleted (block) or need extra care (warn).

        Each rule is (path, reason, include_everything_inside).
        """
        env = os.environ.get
        block, warn = [], []
        profile = os.path.expanduser("~")

        if os.name == "nt":
            windir = env("SystemRoot") or r"C:\Windows"
            system_drive = os.path.splitdrive(windir)[0] + os.sep
            block.append((windir, "the Windows system folder", True))
            for name in ("System Volume Information", "$Recycle.Bin", "Recovery"):
                block.append((os.path.join(system_drive, name), f"the system folder '{name}'", True))
            for name in ("pagefile.sys", "hiberfil.sys", "swapfile.sys"):
                block.append((os.path.join(system_drive, name), f"the Windows system file '{name}'", False))
            for variable, label in (("ProgramFiles", "Program Files"),
                                    ("ProgramFiles(x86)", "Program Files (x86)"),
                                    ("ProgramData", "ProgramData")):
                folder = env(variable)
                if folder:
                    block.append((folder, f"the {label} folder itself", False))
                    warn.append((folder, f"it is inside {label}, which holds installed programs", True))
            warn.append((os.path.join(profile, "AppData"), "it is inside AppData, where programs keep their settings", True))
        else:
            for folder in ("/usr", "/etc", "/bin", "/sbin", "/lib", "/boot", "/dev", "/proc", "/sys"):
                block.append((folder, "a system folder", True))
            block.append(("/", "the root of the drive", False))

        block.append((profile, "your user profile folder", False))
        block.append((os.path.dirname(profile), "the folder that holds all user profiles", False))
        block.append((os.path.dirname(os.path.abspath(__file__)), "Drive Organizer's own folder", True))
        for name in ("Desktop", "Documents", "Downloads", "Pictures", "Music", "Videos"):
            warn.append((os.path.join(profile, name), f"it is your {name} folder itself", False))
        return block, warn

    def protection_for(self, path):
        """Return ('block' or 'warn', reason) for a risky path, or None."""
        path = os.path.abspath(path)
        if os.path.dirname(path) == path:
            return "block", "a whole drive"
        for rule, reason, include_inside in self.block_rules:
            if os.path.normcase(os.path.abspath(rule)) == os.path.normcase(path):
                return "block", reason
            if self.is_inside(rule, path):                       # deleting it would take the rule's folder too
                return "block", f"it contains {reason}"
            if include_inside and self.is_inside(path, rule):
                return "block", f"it is inside {reason}"
        for rule, reason, include_inside in self.warn_rules:
            if os.path.normcase(os.path.abspath(rule)) == os.path.normcase(path):
                return "warn", reason
            if include_inside and self.is_inside(path, rule):
                return "warn", reason
        if in_game_library(path):
            return "warn", "it is inside a game library; uninstall games from their launcher instead"
        return None

    # --- Windows Recycle Bin helpers (the parts that need Windows are kept small) ---
    def drive_kind(self, path):
        if os.name != "nt":
            return "fixed"
        drive = os.path.splitdrive(os.path.abspath(path))[0]
        if drive.startswith("\\\\"):
            return "network"
        kinds = {2: "removable", 3: "fixed", 4: "network", 5: "cdrom", 6: "ramdisk"}
        return kinds.get(ctypes.windll.kernel32.GetDriveTypeW(drive + "\\"), "unknown")

    def bin_settings(self, path):
        """(max size in bytes or None, bin turned off?) for the drive holding path."""
        try:
            import winreg
            root = os.path.splitdrive(os.path.abspath(path))[0] + "\\"
            buffer = ctypes.create_unicode_buffer(100)
            if not ctypes.windll.kernel32.GetVolumeNameForVolumeMountPointW(root, buffer, 100):
                return None, False
            name = buffer.value
            guid = name[name.index("{"): name.index("}") + 1]
            key = winreg.OpenKey(
                winreg.HKEY_CURRENT_USER,
                r"Software\Microsoft\Windows\CurrentVersion\Explorer\BitBucket\Volume" + "\\" + guid
            )
            maximum, nuke = None, False
            try:
                maximum = winreg.QueryValueEx(key, "MaxCapacity")[0] * 1024 * 1024
            except OSError:
                pass
            try:
                nuke = bool(winreg.QueryValueEx(key, "NukeOnDelete")[0])
            except OSError:
                pass
            return maximum, nuke
        except Exception:
            return None, False

    def recycle_problem(self, path, size):
        """Why this item can't safely go to the Recycle Bin, or None if it can."""
        if os.name != "nt":
            return None
        if self.drive_kind(path) != "fixed":
            return "this drive has no Recycle Bin (Windows would delete it permanently)"
        maximum, turned_off = self.bin_settings(path)
        if turned_off:
            return "the Recycle Bin is turned off for this drive (files are deleted permanently)"
        if maximum is not None:
            if size > maximum:
                return f"bigger than the Recycle Bin's size limit ({self.format_size(maximum)})"
        else:
            try:
                total = shutil.disk_usage(os.path.splitdrive(os.path.abspath(path))[0] + "\\").total
            except OSError:
                total = 0
            if total and size > total * 0.10:
                return "it might be too big for the Recycle Bin (its size limit couldn't be read)"
        return None

    def recycle(self, path):
        _send2trash(os.path.abspath(path))

    def in_recycle_bin(self, path, since):
        """True/False if the item is in the Recycle Bin, None if that can't be checked."""
        if os.name != "nt":
            return None
        try:
            bin_root = os.path.splitdrive(os.path.abspath(path))[0] + "\\$Recycle.Bin"
            wanted = os.path.normcase(os.path.abspath(path))
            scanned = False
            for owner in os.listdir(bin_root):
                try:
                    names = os.listdir(os.path.join(bin_root, owner))
                except OSError:
                    continue
                scanned = True
                for name in names:
                    if not name.startswith("$I"):
                        continue
                    try:
                        with open(os.path.join(bin_root, owner, name), "rb") as handle:
                            info = parse_recycle_info(handle.read(1024))
                    except OSError:
                        continue
                    if info and os.path.normcase(info[0]) == wanted and info[1] >= since - 10:
                        return True
            return False if scanned else None
        except OSError:
            return None

    def open_target(self, target):
        try:
            if os.name == "nt":
                os.startfile(target)
            elif sys.platform == "darwin":
                subprocess.run(["open", target], check=False)
            else:
                subprocess.run(["xdg-open", target], check=False)
        except Exception as error:
            messagebox.showerror("Could not open", str(error))

    def open_log(self):
        if os.path.exists(self.log_path):
            self.open_target(self.log_path)
        else:
            messagebox.showinfo("Deletion log", "Nothing has been deleted yet, so there is no log.")

    def open_recycle_bin(self):
        if os.name == "nt":
            self.open_target("shell:RecycleBinFolder")
        else:
            messagebox.showinfo("Recycle Bin", "Open your system's Trash to see recycled items.")

    # --- choosing what to delete ---
    def delete_marked(self):
        if self.job:
            return
        if not self.del_sel:
            messagebox.showwarning("Nothing selected", "Mark files or folders in the Delete column first.")
            return
        _, waiting = self.selection_total(self.del_sel)
        if waiting:
            messagebox.showinfo(
                "Still measuring",
                "Drive Organizer is still measuring the size of your selected folders.\n"
                "Try again in a moment."
            )
            return
        self.begin_deletion(sorted(self.del_sel))

    def build_delete_items(self, paths, copies=None):
        items = []
        for path in paths:
            size = self.size_cache.get(path, 0)
            item = {
                "path": path, "size": size,
                "copy": (copies or {}).get(path),
                "block": None, "warn": None, "recycle_problem": None,
            }
            risk = self.protection_for(path)
            if risk:
                item[risk[0]] = risk[1]
            if self.usb_path and (os.path.normcase(os.path.abspath(path)) == os.path.normcase(os.path.abspath(self.usb_path))
                                  or self.is_inside(self.usb_path, path)):
                item["block"] = "the USB destination is inside it"
            if not item["block"]:
                item["recycle_problem"] = self.recycle_problem(path, size)
            items.append(item)
        return items

    def begin_deletion(self, paths, copies=None):
        items = self.build_delete_items(paths, copies)
        blocked = [item for item in items if item["block"]]
        if blocked:
            lines = [f"• {item['path']}\n    ({item['block']})" for item in blocked[:8]]
            if len(blocked) > 8:
                lines.append(f"...and {len(blocked) - 8} more")
            messagebox.showerror(
                "Protected items",
                "These items are protected and will not be deleted:\n\n" + "\n".join(lines)
            )
            items = [item for item in items if not item["block"]]
        if not items:
            return

        mode = self.ask_delete_options(items)
        if mode is None:
            self.status.config(text="Deletion cancelled. Nothing was deleted.")
            return
        self.start_job(DeleteState(items, mode), self._delete_worker)

    def ask_delete_options(self, items):
        """Show the confirmation window. Returns 'recycle', 'permanent' or None."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Confirm deletion")
        dialog.transient(self.root)
        dialog.grab_set()

        total = sum(item["size"] for item in items)
        tk.Label(
            dialog, text=f"Delete {len(items)} item(s)  •  {self.format_size(total)}",
            font=("Segoe UI", 12, "bold")
        ).pack(anchor="w", padx=15, pady=(15, 5))

        frame = tk.Frame(dialog)
        frame.pack(fill="both", expand=True, padx=15)
        listbox = tk.Listbox(frame, height=min(max(len(items), 3), 10), width=95, font=("Consolas", 9))
        scrollbar = tk.Scrollbar(frame, command=listbox.yview)
        listbox.config(yscrollcommand=scrollbar.set)
        listbox.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        for item in items:
            text = f"{self.format_size(item['size']):>11}   {item['path']}"
            if item["copy"]:
                text += "   [verified copy kept]"
            if item["warn"]:
                text += f"   [CAUTION: {item['warn']}]"
            listbox.insert("end", text)

        recycle_available = _send2trash is not None
        mode_var = tk.StringVar(value="recycle" if recycle_available else "permanent")
        tk.Radiobutton(
            dialog, variable=mode_var, value="recycle",
            text="Send to the Recycle Bin (you can restore them)",
            state="normal" if recycle_available else "disabled"
        ).pack(anchor="w", padx=15, pady=(10, 0))
        tk.Radiobutton(
            dialog, variable=mode_var, value="permanent",
            text="Delete permanently (cannot be undone)"
        ).pack(anchor="w", padx=15)

        note = tk.Label(dialog, text="", justify="left", wraplength=640, anchor="w")
        note.pack(fill="x", padx=15, pady=8)

        typing_row = tk.Frame(dialog)
        typing_row.pack(fill="x", padx=15)
        typing_label = tk.Label(typing_row, text=f"Type {CONFIRM_WORD} to confirm:")
        typing_label.pack(side="left")
        typed = tk.StringVar()
        entry = tk.Entry(typing_row, textvariable=typed, width=14)
        entry.pack(side="left", padx=8)

        result = {"mode": None}
        buttons = tk.Frame(dialog)
        buttons.pack(fill="x", padx=15, pady=15)
        delete_button = tk.Button(
            buttons, text="Delete", fg=DELETE_COLOR, font=("Segoe UI", 10, "bold"),
            command=lambda: (result.update(mode=mode_var.get()), dialog.destroy())
        )
        delete_button.pack(side="right", padx=5)
        tk.Button(buttons, text="Cancel", command=dialog.destroy).pack(side="right", padx=5)

        def update(*_):
            mode = mode_var.get()
            skipped = [item for item in items if item["recycle_problem"]]
            lines = []
            if mode == "recycle":
                lines.append("Items in the Recycle Bin still use disk space until you empty it.")
                if not recycle_available:
                    lines.append("The Recycle Bin option needs the 'send2trash' package (pip install send2trash).")
                if skipped:
                    lines.append(
                        f"{len(skipped)} item(s) can't safely go to the Recycle Bin and will be SKIPPED "
                        "(choose 'Delete permanently' to remove them):"
                    )
                    lines += [f"  • {os.path.basename(item['path'])}: {item['recycle_problem']}" for item in skipped[:4]]
                    if len(skipped) > 4:
                        lines.append(f"  ...and {len(skipped) - 4} more")
            else:
                lines.append("PERMANENT: these items will be erased and cannot be recovered.")
            note.config(text="\n".join(lines), fg=DELETE_COLOR if mode == "permanent" else "black")

            needs_typing = mode == "permanent" or any(item["warn"] for item in items)
            entry.config(state="normal" if needs_typing else "disabled")
            typing_label.config(fg="black" if needs_typing else "gray")
            nothing_to_do = mode == "recycle" and (not recycle_available or all(item["recycle_problem"] for item in items))
            confirmed = (not needs_typing) or typed.get().strip().upper() == CONFIRM_WORD
            delete_button.config(state="normal" if confirmed and not nothing_to_do else "disabled")

        mode_var.trace_add("write", update)
        typed.trace_add("write", update)
        update()

        dialog.protocol("WM_DELETE_WINDOW", dialog.destroy)
        dialog.update_idletasks()
        x = self.root.winfo_rootx() + (self.root.winfo_width() - dialog.winfo_width()) // 2
        y = self.root.winfo_rooty() + (self.root.winfo_height() - dialog.winfo_height()) // 3
        dialog.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        self.root.wait_window(dialog)
        return result["mode"]

    # --- the deleting itself ---
    def is_link_like(self, path):
        """Symbolic links and Windows junctions: removed as links, never entered."""
        try:
            if os.path.islink(path):
                return True
            attributes = getattr(os.lstat(path), "st_file_attributes", 0)
            return bool(attributes & 0x400)  # FILE_ATTRIBUTE_REPARSE_POINT
        except OSError:
            return False

    def remove_file(self, path):
        try:
            os.unlink(path)
        except PermissionError:
            os.chmod(path, stat.S_IWRITE)  # read-only files need this on Windows
            os.unlink(path)

    def remove_link(self, path):
        try:
            os.unlink(path)
        except OSError:
            os.rmdir(path)  # directory links and junctions on Windows

    def remove_empty_dir(self, path):
        try:
            os.rmdir(path)
        except PermissionError:
            os.chmod(path, stat.S_IWRITE)
            os.rmdir(path)

    def delete_tree(self, path, state):
        """Permanently delete a folder one file at a time, so progress and Cancel work."""
        with os.scandir(path) as scan:
            entries = list(scan)
        for entry in entries:
            if state.cancel.is_set():
                raise TransferCancelled()
            if self.is_link_like(entry.path):
                self.remove_link(entry.path)
            elif entry.is_dir(follow_symlinks=False):
                self.delete_tree(entry.path, state)
            else:
                try:
                    size = entry.stat(follow_symlinks=False).st_size
                except OSError:
                    size = 0
                state.text = f"Deleting: {entry.path}"
                self.remove_file(entry.path)
                state.add_units(size)
        self.remove_empty_dir(path)

    def delete_permanently(self, path, state):
        if self.is_link_like(path):
            self.remove_link(path)
        elif os.path.isdir(path):
            self.delete_tree(path, state)
        else:
            self.remove_file(path)

    def copy_still_present(self, source, copy):
        """Cheap re-check, just before deleting an original, that its USB copy is still there."""
        try:
            original = self.snapshot(source)
            if original != self.snapshot(copy):
                return False
            for relative, kind in original.items():
                if kind == "file":
                    src = source if relative == "." else os.path.join(source, relative)
                    dst = copy if relative == "." else os.path.join(copy, relative)
                    if os.path.getsize(src) != os.path.getsize(dst):
                        return False
            return True
        except OSError:
            return False

    def _delete_worker(self, state):
        """Runs in a background thread. Never touches the window directly."""
        try:
            for index, item in enumerate(state.items, start=1):
                if state.cancel.is_set():
                    state.cancelled = True
                    break
                state.item_index = index
                path, size = item["path"], item["size"]
                state.text = f"Deleting: {path}"

                def skip(reason):
                    state.skipped.append((path, reason))
                    if not self.log_deletion("skipped", size, path, reason):
                        state.log_ok = False

                if not os.path.lexists(path):
                    skip("it no longer exists")
                    state.add_units(size)
                    continue
                if item["copy"] and not self.copy_still_present(path, item["copy"]):
                    skip("its verified copy is missing or no longer matches, so this one was kept")
                    state.add_units(size)
                    continue
                if state.mode == "recycle" and item["recycle_problem"]:
                    skip(f"not sent to the Recycle Bin: {item['recycle_problem']}")
                    state.add_units(size)
                    continue

                try:
                    if state.mode == "recycle":
                        started = time.time()
                        self.recycle(path)
                        if os.path.lexists(path):
                            raise OSError("The item is still there after being sent to the Recycle Bin.")
                        state.add_units(size)
                        if self.in_recycle_bin(path, started) is False:
                            state.unconfirmed.append((path, size))
                            action, note = "unconfirmed", "removed but not found in the Recycle Bin; it may have been deleted permanently"
                        else:
                            state.recycled.append((path, size))
                            action, note = "recycled", ""
                    else:
                        self.delete_permanently(path, state)
                        state.permanent.append((path, size))
                        action, note = "permanent", ""
                    if item["copy"]:
                        note = (note + " " if note else "") + f"verified copy: {item['copy']}"
                    if not self.log_deletion(action, size, path, note):
                        state.log_ok = False
                except TransferCancelled:
                    state.cancelled = True
                    state.partial = path
                    self.log_deletion("cancelled", size, path, "cancelled part-way; the item may be partly deleted")
                    break
                except Exception as error:
                    state.failed.append((path, str(error)))
                    if not self.log_deletion("failed", size, path, str(error)):
                        state.log_ok = False
        except Exception as error:  # safety net: never leave the window waiting forever
            state.failed.append(("(delete)", str(error)))
        finally:
            if not state.cancelled:
                state.done_units = state.total_units
            state.finished = True

    def finish_delete(self, state):
        self.end_job()

        gone = [path for path, _ in state.recycled + state.permanent + state.unconfirmed]
        self.freed_bytes += sum(size for _, size in state.permanent)
        self.binned_bytes += sum(size for _, size in state.recycled)
        self.recovered_label.config(
            text=f"Freed this session: {self.format_size(self.freed_bytes)}"
                 f"  •  In Recycle Bin: {self.format_size(self.binned_bytes)}"
        )

        # Forget anything that is gone, then redraw.
        for path in gone:
            for selection in (self.usb_sel, self.del_sel):
                for chosen in list(selection):
                    if chosen == path or self.is_inside(chosen, path):
                        selection.discard(chosen)
            for cached in list(self.size_cache):
                if cached == path or self.is_inside(cached, path):
                    del self.size_cache[cached]
        self.analyzer_forget(gone)
        self.duplicates_forget(gone)
        self.back_stack = [folder for folder in self.back_stack if folder and os.path.isdir(folder)]
        self.forward_stack = [folder for folder in self.forward_stack if os.path.isdir(folder)]
        while self.current_folder and not os.path.isdir(self.current_folder):
            parent = os.path.dirname(self.current_folder)
            if parent == self.current_folder:
                break
            self.current_folder = parent
        self.refresh()
        self.update_summary()

        lines = []
        if state.cancelled:
            lines.append("The deletion was cancelled.\n")
        if state.recycled:
            lines.append(
                f"Moved to the Recycle Bin: {len(state.recycled)} item(s), "
                f"{self.format_size(sum(size for _, size in state.recycled))}.\n"
                "Empty the Recycle Bin to actually free that space."
            )
        if state.permanent:
            lines.append(
                f"Deleted permanently: {len(state.permanent)} item(s), "
                f"{self.format_size(sum(size for _, size in state.permanent))} freed."
            )
        if state.unconfirmed:
            lines.append(
                f"\nWARNING: {len(state.unconfirmed)} item(s) were removed but could not be found in the Recycle Bin. "
                "They may have been deleted permanently, for example because they were too big for the bin:\n"
                + "\n".join(f"  • {path}" for path, _ in state.unconfirmed[:5])
            )
        if state.skipped:
            lines.append(f"\nSkipped (left untouched): {len(state.skipped)} item(s).")
            lines += [f"  • {os.path.basename(path)}: {reason}" for path, reason in state.skipped[:4]]
        if state.failed:
            lines.append(f"\nFailed: {len(state.failed)} item(s). First error:\n{state.failed[0][1]}")
        if state.partial:
            lines.append(f"\nThis item may be PARTLY deleted because you cancelled:\n{state.partial}")
        if not (state.recycled or state.permanent or state.unconfirmed):
            lines.append("Nothing was deleted.")
        lines.append(
            "\nEverything above is recorded in the deletion log."
            if state.log_ok else
            "\nNote: the deletion log could not be written."
        )
        self.status.config(text="Deletion finished." if not state.cancelled else "Deletion cancelled.")
        messagebox.showinfo("Deletion finished" if not state.cancelled else "Deletion cancelled", "\n".join(lines))

    # ------------------------------------------------------------------
    # Storage analyzer window
    # ------------------------------------------------------------------
    ACTION_LABELS = {"delete": "Delete", "usb": "Move to USB", "review": "Review",
                     "launcher": "Use launcher", "info": "Info"}
    LEVEL_LABELS = {"safe": "Safe", "check": "Check first", "review": "Review", "info": "Info"}

    def make_tree(self, parent, columns, selectmode="extended", show="headings"):
        """A Treeview with a scrollbar. columns: [(id, heading, width, anchor), ...]"""
        frame = tk.Frame(parent)
        frame.pack(fill="both", expand=True)
        tree = ttk.Treeview(frame, columns=[c[0] for c in columns], show=show, selectmode=selectmode)
        for column_id, heading, width, anchor in columns:
            tree.heading(column_id, text=heading)
            tree.column(column_id, width=width, anchor=anchor)
        scrollbar = ttk.Scrollbar(frame, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        tree.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        return tree

    def open_analyzer(self):
        if self.analyzer is not None:
            try:
                if self.analyzer.winfo_exists():
                    self.analyzer.lift()
                    return
            except tk.TclError:
                pass

        window = tk.Toplevel(self.root)
        window.title("Storage Analyzer")
        window.geometry("1020x680")
        window.minsize(780, 480)
        window.protocol("WM_DELETE_WINDOW", self.close_analyzer)
        self.analyzer = window

        top = tk.Frame(window)
        top.pack(fill="x", padx=12, pady=(12, 4))
        self.an_root_label = tk.Label(
            top, anchor="w",
            text=f"Scan: {self.scan_root or self.current_folder or '(choose a folder)'}"
        )
        self.an_root_label.pack(side="left", fill="x", expand=True)
        self.an_scan_button = tk.Button(top, text="Scan", font=("Segoe UI", 10, "bold"), command=self.start_scan)
        self.an_scan_button.pack(side="right", padx=4)
        self.an_cancel_button = tk.Button(top, text="Cancel Scan", state="disabled", command=self.cancel_scan)
        self.an_cancel_button.pack(side="right", padx=4)
        tk.Button(top, text="Choose Folder...", command=self.choose_scan_folder).pack(side="right", padx=4)

        self.an_status = tk.Label(
            window, anchor="w", justify="left", wraplength=980,
            text="Pick what to scan and press Scan. A whole drive can take a few minutes; "
                 "you can keep using the main window meanwhile."
        )
        self.an_status.pack(fill="x", padx=12, pady=(0, 6))

        notebook = ttk.Notebook(window)
        notebook.pack(fill="both", expand=True, padx=12, pady=4)
        self.an_notebook = notebook
        overview, suggestions, folders, files = (tk.Frame(notebook) for _ in range(4))
        notebook.add(overview, text="Overview")
        notebook.add(suggestions, text="Suggestions")
        notebook.add(folders, text="Largest Folders")
        notebook.add(files, text="Largest Files")

        # Overview
        self.an_overview = tk.Label(overview, anchor="w", justify="left", font=("Segoe UI", 10), text="No scan yet.")
        self.an_overview.pack(fill="x", padx=10, pady=(10, 4))
        self.an_drive_bar = ProgressBar(overview, height=16)
        self.an_drive_bar.pack(fill="x", padx=10, pady=(0, 10))
        self.an_types = self.make_tree(overview, [
            ("type", "File type", 220, "w"), ("files", "Files", 90, "e"),
            ("size", "Size", 120, "e"), ("share", "Share of scan", 110, "e"),
        ])

        # Suggestions
        self.an_suggest_note = tk.Label(
            suggestions, anchor="w", justify="left", wraplength=960,
            text="Suggestions come from simple rules (age, size and folder type). Nothing is deleted or "
                 "copied until you mark items and confirm in the main window."
        )
        self.an_suggest_note.pack(fill="x", padx=6, pady=6)
        self.an_suggestions = self.make_tree(suggestions, [
            ("action", "Suggested", 95, "w"), ("level", "Confidence", 85, "w"),
            ("size", "Size", 85, "e"), ("group", "Why", 130, "w"),
            ("reason", "Reason", 330, "w"), ("path", "Path", 300, "w"),
        ])

        # Largest folders: a tree you can open level by level
        self.an_folders = self.make_tree(folders, [
            ("size", "Size", 110, "e"), ("share", "Share", 80, "e"),
        ], show="tree headings")
        self.an_folders.heading("#0", text="Folder")
        self.an_folders.column("#0", width=560)
        self.an_folders.bind("<<TreeviewOpen>>", lambda event: self.fill_folder_children(self.an_folders.focus()))

        # Largest files
        self.an_files = self.make_tree(files, [
            ("size", "Size", 90, "e"), ("modified", "Modified", 90, "w"),
            ("type", "Type", 150, "w"), ("path", "Path", 600, "w"),
        ])

        for tree in (self.an_suggestions, self.an_folders, self.an_files):
            tree.bind("<Double-1>", lambda event: self.analyzer_show())

        bar = tk.Frame(window)
        bar.pack(fill="x", padx=12, pady=10)
        tk.Button(bar, text="Mark Selected for USB", command=lambda: self.analyzer_mark("usb")).pack(side="left", padx=4)
        tk.Button(bar, text="Mark Selected for Delete", fg=DELETE_COLOR,
                  command=lambda: self.analyzer_mark("delete")).pack(side="left", padx=4)
        tk.Button(bar, text="Mark All Suggestions", command=self.analyzer_mark_recommended).pack(side="left", padx=14)
        tk.Button(bar, text="Show in Main Window", command=self.analyzer_show).pack(side="right", padx=4)

        if self.analysis:
            self.show_analysis(self.analysis)

    def close_analyzer(self):
        if self.scan_job:
            self.scan_job.cancel.set()
        window, self.analyzer = self.analyzer, None
        try:
            window.destroy()
        except Exception:
            pass

    def choose_scan_folder(self):
        folder = filedialog.askdirectory(title="Choose a folder or drive to analyze", parent=self.analyzer)
        if folder:
            self.scan_root = os.path.abspath(folder)
            self.an_root_label.config(text=f"Scan: {self.scan_root}")

    def start_scan(self):
        if self.scan_job and not self.scan_job.finished:
            return
        root = self.scan_root or self.current_folder
        if not root:
            self.choose_scan_folder()
            root = self.scan_root
            if not root:
                return
        root = os.path.abspath(root)
        if not os.path.isdir(root):
            messagebox.showerror("Can't scan", f"This folder doesn't exist:\n{root}", parent=self.analyzer)
            return
        self.scan_root = root
        self.an_root_label.config(text=f"Scan: {root}")

        job = ScanJob(root)
        self.scan_job = job
        self.an_scan_button.config(state="disabled")
        self.an_cancel_button.config(state="normal")
        threading.Thread(target=self._scan_worker, args=(job,), daemon=True).start()
        self.poll_scan()

    def _scan_worker(self, job):
        """Runs in a background thread. Never touches the window directly."""
        try:
            job.result = scan_folder(job.root, job.cancel, job)
        except Exception as error:
            job.error = str(error)
        finally:
            job.finished = True

    def poll_scan(self):
        job = self.scan_job
        if not job:
            return
        if self.analyzer is None:
            job.cancel.set()  # the window was closed
        if job.finished:
            self.finish_scan(job)
            return
        if self.analyzer is not None:
            self.an_status.config(
                text=f"Scanning... {job.files:,} files, {self.format_size(job.bytes)} so far  •  "
                     f"{self.shorten(job.current, 70)}"
            )
        self.root.after(200, self.poll_scan)

    def cancel_scan(self):
        if self.scan_job and not self.scan_job.finished:
            self.scan_job.cancel.set()
            self.an_cancel_button.config(state="disabled")
            self.an_status.config(text="Cancelling the scan...")

    def finish_scan(self, job):
        self.scan_job = None
        if self.analyzer is None:
            return
        self.an_scan_button.config(state="normal")
        self.an_cancel_button.config(state="disabled")
        if job.error:
            self.an_status.config(text=f"The scan failed: {job.error}")
            return

        result = job.result
        self.analysis = result
        self.suggestions = build_suggestions(result, time.time(), self.protection_for)
        self.suggestion_lookup = {item["path"]: item for item in self.suggestions}
        self.show_analysis(result)

        text = (f"Scanned {result.file_count:,} files in {result.folder_count:,} folders "
                f"({self.format_size(result.total_bytes)}) in {result.seconds:.0f} sec.")
        if result.unreadable:
            text += f" {result.unreadable:,} items could not be read and were skipped."
        if result.cancelled:
            text += "  PARTIAL RESULTS: the scan was cancelled before it finished."
        self.an_status.config(text=text)
        self.an_notebook.select(1 if self.suggestions else 0)

    def show_analysis(self, result):
        # Overview
        lines = [f"Scanned: {result.root}",
                 f"{result.file_count:,} files in {result.folder_count:,} folders, "
                 f"{self.format_size(result.total_bytes)} in total"]
        fraction, color = 0.0, COPY_COLOR
        try:
            usage = shutil.disk_usage(result.root)
            fraction = usage.used / usage.total if usage.total else 0.0
            color = "#e08a00" if fraction >= 0.9 else COPY_COLOR
            lines.append(f"Whole drive: {self.format_size(usage.total)} total  •  "
                         f"{self.format_size(usage.used)} used ({fraction * 100:.0f}%)  •  "
                         f"{self.format_size(usage.free)} free")
        except OSError:
            pass
        self.an_overview.config(text="\n".join(lines))
        self.an_drive_bar.set(fraction, color)

        self.an_types.delete(*self.an_types.get_children())
        total = max(result.total_bytes, 1)
        for name, (count, size) in sorted(result.categories.items(), key=lambda kv: kv[1][1], reverse=True):
            self.an_types.insert("", "end", values=(name, f"{count:,}", self.format_size(size), f"{size / total * 100:.1f}%"))

        # Suggestions
        self.an_suggestions.delete(*self.an_suggestions.get_children())
        to_delete = sum(s["size"] for s in self.suggestions if s["action"] == "delete")
        to_usb = sum(s["size"] for s in self.suggestions if s["action"] == "usb")
        self.an_suggest_note.config(
            text=f"{len(self.suggestions)} suggestions: up to {self.format_size(to_delete)} could be deleted and "
                 f"{self.format_size(to_usb)} could move to your USB drive. Nothing is deleted or copied until "
                 "you mark items and confirm in the main window."
        )
        for item in self.suggestions:
            self.an_suggestions.insert("", "end", iid=item["path"], values=(
                self.ACTION_LABELS[item["action"]], self.LEVEL_LABELS[item["level"]],
                self.format_size(item["size"]), item["group"], item["reason"], item["path"]))

        # Largest folders
        self.an_folders.delete(*self.an_folders.get_children())
        root_size = result.sizes.get(result.root, 0)
        self.an_folders.insert("", "end", iid=result.root, text=result.root, open=False,
                               values=(self.format_size(root_size), "100%"))
        if result.children.get(result.root):
            self.an_folders.insert(result.root, "end", iid=result.root + "\x00")
        self.an_folders.item(result.root, open=True)
        self.fill_folder_children(result.root)

        # Largest files
        self.an_files.delete(*self.an_files.get_children())
        for size, path, modified in sorted(result.top_files, reverse=True)[:200]:
            category = EXTENSION_CATEGORY.get(os.path.splitext(path)[1].lower(), "Other")
            when = datetime.fromtimestamp(modified).strftime("%Y-%m-%d")
            self.an_files.insert("", "end", iid=path, values=(self.format_size(size), when, category, path))

    def fill_folder_children(self, parent):
        """Fill a folder's children the first time it is opened (biggest first)."""
        tree, result = self.an_folders, self.analysis
        if not parent or not result:
            return
        kids = tree.get_children(parent)
        if len(kids) != 1 or not kids[0].endswith("\x00"):
            return
        tree.delete(kids[0])
        total = max(result.sizes.get(result.root, 0), 1)
        ranked = sorted(result.children.get(parent, []), key=lambda c: result.sizes.get(c, 0), reverse=True)
        for child in ranked[:200]:
            size = result.sizes.get(child, 0)
            tree.insert(parent, "end", iid=child, text=os.path.basename(child), open=False,
                        values=(self.format_size(size), f"{size / total * 100:.1f}%"))
            if result.children.get(child):
                tree.insert(child, "end", iid=child + "\x00")

    # --- acting on what the analyzer found ---
    def analyzer_tree(self):
        index = self.an_notebook.index(self.an_notebook.select())
        return {1: self.an_suggestions, 2: self.an_folders, 3: self.an_files}.get(index)

    def selected_analyzer_paths(self):
        tree = self.analyzer_tree()
        if tree is None:
            return None
        return [path for path in tree.selection() if not path.endswith("\x00")]

    def mark_paths(self, paths, kind):
        """Mark paths for USB or Delete using the same conflict rules as the checkboxes."""
        own = self.usb_sel if kind == "usb" else self.del_sel
        outcome = {"marked": [], "already": [], "refused": []}
        for path in paths:
            if path in own:
                outcome["already"].append(path)
                continue
            risk = self.protection_for(path)
            if risk and risk[0] == "block":
                outcome["refused"].append((path, f"protected: {risk[1]}"))
                continue
            self.toggle_item(path, kind)
            if path in own:
                outcome["marked"].append(path)
            else:
                outcome["refused"].append((path, self.status.cget("text")))
        return outcome

    def report_marking(self, outcome, kind):
        label = "USB" if kind == "usb" else "Delete"
        parts = [f"Marked {len(outcome['marked'])} item(s) for {label}"]
        if outcome["already"]:
            parts.append(f"{len(outcome['already'])} were already marked")
        if outcome["refused"]:
            parts.append(f"{len(outcome['refused'])} skipped ({outcome['refused'][0][1]})")
        text = ". ".join(parts) + ". Review and confirm in the main window."
        self.status.config(text=text)
        if self.analyzer is not None:
            self.an_status.config(text=text)

    def analyzer_mark(self, kind):
        paths = self.selected_analyzer_paths()
        if paths is None:
            self.an_status.config(text="Open the Suggestions, Largest Folders or Largest Files tab and select items first.")
            return
        if not paths:
            self.an_status.config(text="Select one or more items in the list first.")
            return
        skipped = [p for p in paths if self.suggestion_lookup.get(p, {}).get("action") in ("launcher", "info")]
        paths = [p for p in paths if p not in skipped]
        outcome = self.mark_paths(paths, kind)
        if skipped:
            outcome["refused"] += [(p, "managed outside this app; see the reason in the list") for p in skipped]
        self.report_marking(outcome, kind)

    def analyzer_mark_recommended(self):
        usb = [s["path"] for s in self.suggestions if s["action"] == "usb"]
        delete = [s["path"] for s in self.suggestions if s["action"] == "delete"]
        if not usb and not delete:
            self.an_status.config(text="There are no suggestions to mark.")
            return
        first = self.mark_paths(usb, "usb")
        second = self.mark_paths(delete, "delete")
        text = (f"Marked {len(first['marked'])} item(s) for USB and {len(second['marked'])} for Delete "
                f"({len(first['refused']) + len(second['refused'])} skipped). "
                "Review and confirm in the main window.")
        self.status.config(text=text)
        self.an_status.config(text=text)

    def browse_to(self, path):
        if not os.path.isdir(path):
            path = os.path.dirname(path)
        if os.path.isdir(path):
            self.navigate(path)
            self.root.lift()

    def analyzer_show(self):
        paths = self.selected_analyzer_paths()
        if paths:
            self.browse_to(paths[0])

    def analyzer_forget(self, gone):
        """Drop rows for things that were just deleted."""
        if self.analyzer is None or not gone:
            return
        try:
            for tree in (self.an_suggestions, self.an_files):
                for iid in tree.get_children():
                    if any(path_inside(iid, path) for path in gone):
                        tree.delete(iid)
            for path in gone:
                if self.an_folders.exists(path):
                    self.an_folders.delete(path)
            self.an_status.config(text="Items were deleted since the scan, so these numbers are out of date. Scan again for fresh totals.")
        except tk.TclError:
            pass

    # ------------------------------------------------------------------
    # Duplicate finder window
    # ------------------------------------------------------------------
    DUP_SIZE_CHOICES = {"Any size": 1, "100 KB": 100 * 1024, "1 MB": 1 * MB, "10 MB": 10 * MB, "100 MB": 100 * MB}
    DUP_RULE_CHOICES = {
        "Keep the oldest copy": "oldest",
        "Keep the newest copy": "newest",
        "Keep the copy with the shortest path": "shortest",
    }
    MAX_DUP_GROUPS_SHOWN = 2000

    def in_protected_tree(self, path):
        """True for folders whose whole contents are off limits (Windows, Program Files, AppData...)."""
        return any(include_inside and path_inside(path, rule)
                   for rule, _reason, include_inside in self.block_rules + self.warn_rules)

    def open_duplicates(self):
        if self.dup_window is not None:
            try:
                if self.dup_window.winfo_exists():
                    self.dup_window.lift()
                    return
            except tk.TclError:
                pass

        window = tk.Toplevel(self.root)
        window.title("Duplicate Finder")
        window.geometry("1020x680")
        window.minsize(780, 480)
        window.protocol("WM_DELETE_WINDOW", self.close_duplicates)
        self.dup_window = window

        top = tk.Frame(window)
        top.pack(fill="x", padx=12, pady=(12, 4))
        self.dup_root_label = tk.Label(
            top, anchor="w", text=f"Scan: {self.dup_root or self.current_folder or '(choose a folder)'}")
        self.dup_root_label.pack(side="left", fill="x", expand=True)
        self.dup_scan_button = tk.Button(top, text="Scan", font=("Segoe UI", 10, "bold"), command=self.start_dup_scan)
        self.dup_scan_button.pack(side="right", padx=4)
        self.dup_cancel_button = tk.Button(top, text="Cancel Scan", state="disabled", command=self.cancel_dup_scan)
        self.dup_cancel_button.pack(side="right", padx=4)
        self.dup_size_box = ttk.Combobox(top, values=list(self.DUP_SIZE_CHOICES), width=9, state="readonly")
        self.dup_size_box.set("1 MB")
        self.dup_size_box.pack(side="right", padx=4)
        tk.Label(top, text="Ignore files smaller than:").pack(side="right")
        tk.Button(top, text="Choose Folder...", command=self.choose_dup_folder).pack(side="right", padx=8)

        self.dup_status = tk.Label(
            window, anchor="w", justify="left", wraplength=980,
            text="Pick a folder or drive and press Scan. Files are compared by their actual contents, "
                 "not their names. Program files and folders such as Windows, Program Files, game libraries "
                 "and .git are never included."
        )
        self.dup_status.pack(fill="x", padx=12, pady=(0, 4))
        self.dup_bar = ProgressBar(window, height=12)
        self.dup_bar.pack(fill="x", padx=12, pady=(0, 6))

        self.dup_tree = self.make_tree(window, [
            ("action", "Action", 80, "w"), ("size", "Size", 90, "e"),
            ("modified", "Modified", 90, "w"), ("note", "Note", 220, "w"),
        ], show="tree headings")
        self.dup_tree.heading("#0", text="Files (identical copies are grouped together)")
        self.dup_tree.column("#0", width=520)
        self.dup_tree.tag_configure("delete", foreground=DELETE_COLOR)
        self.dup_tree.bind("<Double-1>", self.dup_toggle)

        rule_row = tk.Frame(window)
        rule_row.pack(fill="x", padx=12, pady=(8, 0))
        self.dup_rule_box = ttk.Combobox(rule_row, values=list(self.DUP_RULE_CHOICES), width=34, state="readonly")
        self.dup_rule_box.set("Keep the oldest copy")
        self.dup_rule_box.pack(side="left")
        tk.Button(rule_row, text="Apply to All Groups", command=self.apply_dup_rule).pack(side="left", padx=6)
        tk.Button(rule_row, text="Toggle Keep / Delete on Selected", command=self.dup_toggle).pack(side="left", padx=6)
        tk.Button(rule_row, text="Show in Main Window", command=self.dup_show).pack(side="right", padx=4)

        bottom = tk.Frame(window)
        bottom.pack(fill="x", padx=12, pady=10)
        self.dup_summary = tk.Label(bottom, anchor="w", text="")
        self.dup_summary.pack(side="left", fill="x", expand=True)
        self.dup_delete_button = tk.Button(
            bottom, text="Delete Marked Copies...", fg=DELETE_COLOR,
            font=("Segoe UI", 10, "bold"), command=self.dup_delete)
        self.dup_delete_button.pack(side="right", padx=4)

        if self.dup_groups:
            self.show_duplicates(self.dup_result)

    def close_duplicates(self):
        if self.dup_job:
            self.dup_job.cancel.set()
        window, self.dup_window = self.dup_window, None
        try:
            window.destroy()
        except Exception:
            pass

    def choose_dup_folder(self):
        folder = filedialog.askdirectory(title="Choose a folder or drive to search for duplicates", parent=self.dup_window)
        if folder:
            self.dup_root = os.path.abspath(folder)
            self.dup_root_label.config(text=f"Scan: {self.dup_root}")

    def start_dup_scan(self):
        if self.dup_job and not self.dup_job.finished:
            return
        root = self.dup_root or self.current_folder
        if not root:
            self.choose_dup_folder()
            root = self.dup_root
            if not root:
                return
        root = os.path.abspath(root)
        if not os.path.isdir(root):
            messagebox.showerror("Can't scan", f"This folder doesn't exist:\n{root}", parent=self.dup_window)
            return
        self.dup_root = root
        self.dup_root_label.config(text=f"Scan: {root}")
        min_size = self.DUP_SIZE_CHOICES.get(self.dup_size_box.get(), DUPLICATE_MIN_SIZE)

        job = DuplicateJob(root)
        self.dup_job = job
        self.dup_scan_button.config(state="disabled")
        self.dup_cancel_button.config(state="normal")
        self.dup_bar.set(0.0, COPY_COLOR)
        threading.Thread(target=self._dup_worker, args=(job, min_size), daemon=True).start()
        self.poll_dup_scan()

    def _dup_worker(self, job, min_size):
        """Runs in a background thread. Never touches the window directly."""
        try:
            job.result = find_duplicates(job.root, job.cancel, job, min_size, skip_dir=self.in_protected_tree)
        except Exception as error:
            job.error = str(error)
        finally:
            job.finished = True

    def poll_dup_scan(self):
        job = self.dup_job
        if not job:
            return
        if self.dup_window is None:
            job.cancel.set()
        if job.finished:
            self.finish_dup_scan(job)
            return
        if self.dup_window is not None:
            self.dup_status.config(text=self.shorten(job.text, 120))
            self.dup_bar.set(job.fraction, COPY_COLOR)
        self.root.after(200, self.poll_dup_scan)

    def cancel_dup_scan(self):
        if self.dup_job and not self.dup_job.finished:
            self.dup_job.cancel.set()
            self.dup_cancel_button.config(state="disabled")
            self.dup_status.config(text="Cancelling the scan...")

    def finish_dup_scan(self, job):
        self.dup_job = None
        if self.dup_window is None:
            return
        self.dup_scan_button.config(state="normal")
        self.dup_cancel_button.config(state="disabled")
        if job.error:
            self.dup_status.config(text=f"The scan failed: {job.error}")
            return
        result = job.result
        self.dup_result = result
        self.dup_bar.set(0.0 if result.cancelled else 1.0, COPY_COLOR)
        self.show_duplicates(result)

        if result.groups:
            text = (f"Compared {result.files_checked:,} files and found {len(result.groups):,} groups of identical files. "
                    f"The extra copies use {self.format_size(result.wasted_bytes)}.")
        else:
            text = f"Compared {result.files_checked:,} files. No duplicates were found."
        if len(result.groups) > self.MAX_DUP_GROUPS_SHOWN:
            text += f" Showing the {self.MAX_DUP_GROUPS_SHOWN:,} biggest groups."
        if result.hardlinks:
            text += f" {result.hardlinks:,} extra names for the same file (hard links) were ignored."
        if result.unreadable:
            text += f" {result.unreadable:,} items could not be read."
        if result.cancelled:
            text += "  PARTIAL RESULTS: the scan was cancelled before it finished."
        self.dup_status.config(text=text)

    def show_duplicates(self, result):
        groups = result.groups[:self.MAX_DUP_GROUPS_SHOWN]
        self.dup_groups = groups
        self.dup_files = {f["path"]: f for g in groups for f in g["files"]}
        self.dup_group_of = {f["path"]: i for i, g in enumerate(groups) for f in g["files"]}
        rule = self.DUP_RULE_CHOICES.get(self.dup_rule_box.get(), "oldest")
        self.dup_actions = choose_keepers(groups, rule)

        self.dup_tree.delete(*self.dup_tree.get_children())
        for index, group in enumerate(groups):
            wasted = group["size"] * (len(group["files"]) - 1)
            node = f"group:{index}"
            self.dup_tree.insert(
                "", "end", iid=node, open=True,
                text=f"{len(group['files'])} identical files  •  {self.format_size(group['size'])} each  •  "
                     f"{self.format_size(wasted)} could be freed",
                values=("", self.format_size(group["size"]), "", ""))
            for file in group["files"]:
                self.dup_tree.insert(
                    node, "end", iid=file["path"], text=file["path"],
                    values=self.dup_row_values(file), tags=(self.dup_actions[file["path"]],))
        self.update_dup_summary()

    def dup_row_values(self, file):
        action = self.dup_actions.get(file["path"], "keep")
        note = "Inside a program's folder, kept for safety" if file["app"] else ""
        when = datetime.fromtimestamp(file["mtime"]).strftime("%Y-%m-%d")
        group = self.dup_groups[self.dup_group_of[file["path"]]]
        return ("Keep" if action == "keep" else "Delete", self.format_size(group["size"]), when, note)

    def set_dup_action(self, path, action):
        self.dup_actions[path] = action
        values = self.dup_row_values(self.dup_files[path])
        self.dup_tree.item(path, values=values, tags=(action,))

    def update_dup_summary(self):
        doomed = [p for p, a in self.dup_actions.items() if a == "delete"]
        size = sum(self.dup_groups[self.dup_group_of[p]]["size"] for p in doomed)
        self.dup_summary.config(
            text=f"{len(doomed):,} copies marked for deletion, freeing {self.format_size(size)}. "
                 "Every group keeps at least one copy." if self.dup_groups else "")

    def apply_dup_rule(self):
        if not self.dup_groups:
            return
        rule = self.DUP_RULE_CHOICES.get(self.dup_rule_box.get(), "oldest")
        for path, action in choose_keepers(self.dup_groups, rule).items():
            self.set_dup_action(path, action)
        self.update_dup_summary()

    def dup_toggle(self, event=None):
        """Flip Keep/Delete on the selected files, never leaving a group without a kept copy."""
        paths = [p for p in self.dup_tree.selection() if p in self.dup_files]
        if event is not None and not paths:
            return
        refused = 0
        for path in paths:
            if self.dup_actions.get(path) == "keep":
                group = self.dup_groups[self.dup_group_of[path]]
                kept = [f for f in group["files"] if self.dup_actions.get(f["path"]) == "keep"]
                if len(kept) <= 1:
                    refused += 1
                    continue
                self.set_dup_action(path, "delete")
            else:
                self.set_dup_action(path, "keep")
        self.update_dup_summary()
        if refused:
            self.dup_status.config(text="At least one copy in each group must be kept, so that change was skipped.")
        return "break" if event is not None else None

    def dup_show(self):
        paths = [p for p in self.dup_tree.selection() if p in self.dup_files]
        if paths:
            self.browse_to(paths[0])

    def dup_delete(self):
        if self.job:
            messagebox.showinfo("Busy", "Wait for the current copy or delete to finish first.", parent=self.dup_window)
            return
        paths, copies = [], {}
        for path, action in self.dup_actions.items():
            if action != "delete" or not os.path.lexists(path):
                continue
            group = self.dup_groups[self.dup_group_of[path]]
            keeper = next((f["path"] for f in group["files"]
                           if self.dup_actions.get(f["path"]) == "keep" and os.path.lexists(f["path"])), None)
            if keeper:
                paths.append(path)
                copies[path] = keeper
                self.size_cache[path] = group["size"]
        if not paths:
            messagebox.showinfo("Nothing to delete", "No copies are marked for deletion.", parent=self.dup_window)
            return
        self.begin_deletion(sorted(paths), copies)

    def duplicates_forget(self, gone):
        """Drop rows for copies that were just deleted, and any group left with a single file."""
        if self.dup_window is None or not self.dup_files:
            return
        try:
            removed = [p for p in self.dup_files if any(path_inside(p, g) for g in gone) and not os.path.lexists(p)]
            for path in removed:
                if self.dup_tree.exists(path):
                    self.dup_tree.delete(path)
                self.dup_actions.pop(path, None)
                self.dup_files.pop(path, None)
            for index, group in enumerate(self.dup_groups):
                left = [f for f in group["files"] if f["path"] in self.dup_files]
                if len(left) < 2:
                    node = f"group:{index}"
                    if self.dup_tree.exists(node):
                        self.dup_tree.delete(node)
                    for f in left:
                        self.dup_files.pop(f["path"], None)
                        self.dup_actions.pop(f["path"], None)
            self.update_dup_summary()
            self.dup_status.config(text="Deleted copies were removed from the list. Scan again for fresh results.")
        except tk.TclError:
            pass

    # ------------------------------------------------------------------
    # Games & Apps window
    # ------------------------------------------------------------------
    def open_games(self):
        if self.games_window is not None:
            try:
                if self.games_window.winfo_exists():
                    self.games_window.lift()
                    return
            except tk.TclError:
                pass

        window = tk.Toplevel(self.root)
        window.title("Games & Apps")
        window.geometry("1020x680")
        window.minsize(780, 480)
        window.protocol("WM_DELETE_WINDOW", self.close_games)
        self.games_window = window

        top = tk.Frame(window)
        top.pack(fill="x", padx=12, pady=(12, 4))
        self.games_summary = tk.Label(top, anchor="w", text="Looking for installed games...")
        self.games_summary.pack(side="left", fill="x", expand=True)
        self.games_refresh_button = tk.Button(top, text="Refresh", command=self.start_game_detect)
        self.games_refresh_button.pack(side="right", padx=4)

        notebook = ttk.Notebook(window)
        notebook.pack(fill="both", expand=True, padx=12, pady=4)
        self.games_notebook = notebook
        games_tab, programs_tab = tk.Frame(notebook), tk.Frame(notebook)
        notebook.add(games_tab, text="Games")
        notebook.add(programs_tab, text="Programs")

        self.games_tree = self.make_tree(games_tab, [
            ("name", "Game", 230, "w"), ("launcher", "Launcher", 110, "w"), ("size", "Size", 95, "e"),
            ("note", "Notes", 190, "w"), ("path", "Location", 360, "w"),
        ], selectmode="browse")
        self.programs_tree = self.make_tree(programs_tab, [
            ("name", "Program", 260, "w"), ("publisher", "Publisher", 170, "w"), ("size", "Size", 95, "e"),
            ("version", "Version", 100, "w"), ("path", "Location", 340, "w"),
        ], selectmode="browse")
        for tree in (self.games_tree, self.programs_tree):
            tree.tag_configure("large", foreground="#c26a00")
            tree.tag_configure("idle", foreground="#777777")
            tree.bind("<<TreeviewSelect>>", self.games_select)
            tree.bind("<Double-1>", lambda event: self.games_show())

        help_box = tk.LabelFrame(window, text="How to move or remove it safely", padx=10, pady=6)
        help_box.pack(fill="x", padx=12, pady=(6, 0))
        self.games_help = tk.Label(
            help_box, anchor="w", justify="left", wraplength=960,
            text="Select a game or program to see how to move or uninstall it. Games and programs should be moved "
                 "or removed through their launcher or Windows, not by copying or deleting their folders.")
        self.games_help.pack(fill="x")

        bar = tk.Frame(window)
        bar.pack(fill="x", padx=12, pady=10)
        tk.Button(bar, text="Open in File Explorer", command=self.games_open_explorer).pack(side="left", padx=4)
        tk.Button(bar, text="Show in Main Window", command=self.games_show).pack(side="left", padx=4)
        tk.Button(bar, text="Open Windows Installed Apps", command=self.games_open_settings).pack(side="left", padx=14)

        self.start_game_detect()

    def close_games(self):
        window, self.games_window = self.games_window, None
        try:
            window.destroy()
        except Exception:
            pass

    def start_game_detect(self):
        if self.game_job and not self.game_job.finished:
            return
        job = GameJob()
        self.game_job = job
        self.games_refresh_button.config(state="disabled")
        self.games_summary.config(text="Looking for installed games...")
        threading.Thread(target=self._game_worker, args=(job,), daemon=True).start()
        self.poll_game_detect()

    def _game_worker(self, job):
        """Runs in a background thread. Never touches the window directly."""
        try:
            job.games = detect_games(**discover_game_sources())
            job.programs = filter_programs(read_installed_programs(), [game["path"] for game in job.games])
        except Exception as error:
            job.error = str(error)
        finally:
            job.finished = True

    def poll_game_detect(self):
        job = self.game_job
        if not job:
            return
        if not job.finished:
            self.root.after(150, self.poll_game_detect)
            return
        self.game_job = None
        if self.games_window is None:
            return
        self.games_refresh_button.config(state="normal")
        if job.error:
            self.games_summary.config(text=f"Detection failed: {job.error}")
            return
        self.games, self.programs = job.games, job.programs
        for item in self.games + self.programs:
            if item["size"] is None and item["path"]:
                self.request_size(item["path"])
        self.fill_game_tables()
        self.poll_game_sizes()

    def item_size(self, item):
        if item["size"] is None and item["path"] in self.size_cache:
            item["size"] = self.size_cache[item["path"]]
        return item["size"]

    def poll_game_sizes(self):
        """Folder sizes arrive in the background; fill them in, then re-sort once they are all known."""
        if self.games_window is None:
            return
        pending = [i for i in self.games + self.programs if i["path"] and self.item_size(i) is None]
        if pending:
            for item in self.games + self.programs:
                iid = self.game_iid.get(id(item))
                size = self.item_size(item)
                if iid and size is not None:
                    tree = self.games_tree if iid.startswith("g") else self.programs_tree
                    tree.set(iid, "size", self.format_size(size))
            self.root.after(500, self.poll_game_sizes)
            return
        # everything is measured: drop small programs and sort by size
        self.programs = [p for p in self.programs if p["size"] is None or p["size"] >= APP_MIN_SIZE]
        self.fill_game_tables()

    def fill_game_tables(self):
        now = time.time()
        self.game_items, self.game_iid = {}, {}
        self.games.sort(key=lambda g: self.item_size(g) or 0, reverse=True)
        self.programs.sort(key=lambda p: self.item_size(p) or 0, reverse=True)
        self.games_tree.delete(*self.games_tree.get_children())
        self.programs_tree.delete(*self.programs_tree.get_children())

        large_count = idle_count = 0
        idle_bytes = 0
        for index, game in enumerate(self.games):
            large, idle, note = game_flags(dict(game, size=self.item_size(game)), now)
            large_count += large
            if idle:
                idle_count += 1
                idle_bytes += self.item_size(game) or 0
            size = self.item_size(game)
            iid = f"g{index}"
            self.game_items[iid], self.game_iid[id(game)] = game, iid
            self.games_tree.insert("", "end", iid=iid, values=(
                game["name"], game["launcher"], "measuring..." if size is None else self.format_size(size),
                note, game["path"]), tags=tuple(t for t, on in (("large", large), ("idle", idle)) if on))
        for index, program in enumerate(self.programs):
            size = self.item_size(program)
            iid = f"a{index}"
            self.game_items[iid], self.game_iid[id(program)] = program, iid
            self.programs_tree.insert("", "end", iid=iid, values=(
                program["name"], program["publisher"], "measuring..." if size is None else self.format_size(size),
                program["version"], program["path"]))

        total = sum(self.item_size(g) or 0 for g in self.games)
        if self.games:
            text = f"{len(self.games)} games use {self.format_size(total)}."
            if large_count:
                text += f" {large_count} are large ({self.format_size(GAME_LARGE_SIZE)} or more, shown in orange)."
            if idle_count:
                text += (f" {idle_count} haven't been played for {GAME_IDLE_DAYS // 30}+ months "
                         f"({self.format_size(idle_bytes)}, shown in grey).")
        else:
            text = "No games were found."
        text += f"  {len(self.programs)} large programs on the Programs tab."
        self.games_summary.config(text=text)

    def selected_game_item(self):
        tree = self.games_tree if self.games_notebook.index(self.games_notebook.select()) == 0 else self.programs_tree
        picked = tree.selection()
        return self.game_items.get(picked[0]) if picked else None

    def games_select(self, event=None):
        item = self.selected_game_item()
        if not item:
            return
        if "launcher" in item:
            text = f"{item['name']} ({item['launcher']})\n{game_guidance(item)}"
            large, idle, note = game_flags(dict(item, size=self.item_size(item)), time.time())
            if idle and self.item_size(item):
                text += f"\nIt hasn't been played in a while; uninstalling it would free {self.format_size(self.item_size(item))}."
        else:
            text = f"{item['name']}\n{PROGRAM_HELP}"
        self.games_help.config(text=text)

    def games_show(self):
        item = self.selected_game_item()
        if item and item["path"]:
            self.browse_to(item["path"])

    def games_open_explorer(self):
        item = self.selected_game_item()
        if item and item["path"] and os.path.isdir(item["path"]):
            self.open_target(item["path"])

    def games_open_settings(self):
        if os.name == "nt":
            self.open_target("ms-settings:appsfeatures")
        else:
            messagebox.showinfo("Installed apps", "Open your system's app settings to uninstall programs.",
                                parent=self.games_window)

    def format_duration(self, seconds):
        seconds = int(round(seconds))
        if seconds < 60:
            return f"{seconds} sec"
        minutes, seconds = divmod(seconds, 60)
        if minutes < 60:
            return f"{minutes} min {seconds} sec"
        hours, minutes = divmod(minutes, 60)
        return f"{hours} hr {minutes} min"

    def shorten(self, text, limit=90):
        if len(text) <= limit:
            return text
        keep = limit - 3
        head = keep // 2
        return text[:head] + "..." + text[-(keep - head):]


if __name__ == "__main__":
    root = tk.Tk()
    app = DriveOrganizer(root)
    root.mainloop()
