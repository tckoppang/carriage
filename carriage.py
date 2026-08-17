#!/usr/bin/env python3
"""
Carriage - A prose-first Markdown editor for the terminal.

Carriage is a focused full-screen Markdown editor built with prompt_toolkit. It
is designed for drafting and revising prose while leaving the document as
ordinary, portable Markdown that remains readable outside Carriage.

Ordinary paragraphs soft-wrap visually within a configurable prose width
without inserting source line breaks. ATX heading and list markers can hang in
the left margin, blockquotes use a display-only gutter, and Markdown hard
breaks made with two trailing spaces can display a visible ↵ marker. These are
editing conventions only and never add Carriage-specific markup to the file.

Carriage deliberately handles a conservative Markdown subset. It can reformat
ordinary paragraphs, simple flat lists, and simple single-level blockquotes.
Fenced or indented code, YAML front matter, raw block HTML, reference
definitions, complex containers, and unfamiliar or ambiguous structures are
preserved rather than repaired or reinterpreted.

Edit > Convert for Carriage normalizes valid Markdown where Carriage can do so
safely. It converts supported Setext headings to ATX, renumbers straightforward
ordered lists, changes straightforward underscore emphasis to asterisks, joins
supported hard-wrapped prose into logical source lines, and folds supported pipe
tables and prose footnotes into editing objects. Export > Hard-Wrapped Markdown
creates a separate wrapped Markdown copy without modifying the working file.

Supported pipe tables appear in the prose view as references such as
`[[Table 1: Movement Rates]]`. Pandoc-style prose footnote definitions fold out
of the prose view and references display as sequential numbers. Tab opens the
associated table or footnote editor. On Save and export, both object types are
materialized as standard Markdown. Unsupported tables and structurally complex footnotes
remain ordinary source.

Carriage includes selection-based italic and bold toggles, interactive Find / Replace,
prose-aware word counting, lightweight visual highlighting, mouse support, desktop
clipboard integration with an automatic internal fallback, direct and sequential
section navigation, configurable terminal spell checking, and Pandoc export to PDF, DOCX,
ODT, HTML, and custom formats.

The Markdown file changes only through explicit Save or Save As. Unsaved work
is protected separately in a private recovery journal. Saves use durable atomic
replacement, detect external changes, preserve supported file metadata, and
refuse unsafe replacement of hard-linked files. Files larger than 8 MiB require
confirmation before loading. Input line endings are normalized to LF.

Untitled documents use the first recognized ATX heading for the suggested `.md`
filename. The visible title before a subtitle colon is preferred, Markdown
formatting is removed, unsafe filename characters are neutralized, and long
suggestions are shortened at a useful word boundary.

Persistent settings are read at startup from `config.toml` in the user's XDG
configuration directory. Carriage has no Preferences dialog. Invalid settings
are ignored with a warning while valid neighboring settings continue to load.

Requires:
  Python 3.10 or newer
  prompt_toolkit>=3.0.52,<3.0.54

Optional:
  pandoc, for document export (or configure another Pandoc executable)
  aspell and an appropriate dictionary package, the default spell checker

Usage:
  carriage [FILE]
  carriage --help
  carriage --version
  carriage -- -filename-starting-with-a-dash.md
"""

import argparse
import asyncio
import codecs
import copy
import errno
from functools import lru_cache
from bisect import bisect_right
import hashlib
import json
import inspect
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
import stat
import string
from html import unescape as _html_unescape
from html.parser import HTMLParser
from dataclasses import dataclass, field

APP_NAME = "Carriage"
APP_VERSION = "1.178"


def _build_command_line_parser():
    """Build Carriage's intentionally small command-line parser."""
    parser = argparse.ArgumentParser(
        prog="carriage",
        description="A prose-first Markdown editor for the terminal.",
        epilog=(
            "With no FILE, Carriage opens an untitled document. "
            "If FILE does not exist, it becomes the path used on first save. "
            "Use -- before a filename beginning with '-'."
        ),
    )
    parser.add_argument(
        "file",
        nargs="?",
        metavar="FILE",
        help="Markdown file to open, or path to use for a new document",
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"%(prog)s {APP_VERSION}",
    )
    return parser


def _parse_command_line(argv=None):
    return _build_command_line_parser().parse_args(argv)


def _is_carriage_command_invocation():
    """Return whether this import belongs to Carriage's executable command.

    A packaging console script imports ``carriage:main`` before it can call
    ``main``. Detect that import by the installed command name so metadata
    options can exit before prompt_toolkit is imported, while ordinary library
    or test imports retain normal module semantics.
    """
    if __name__ == "__main__":
        return True
    command = os.path.basename(sys.argv[0] or "").lower()
    return command in {"carriage", "carriage.exe"}


def _exit_for_early_cli_metadata():
    """Handle package and script --help/--version before prompt_toolkit import."""
    if not _is_carriage_command_invocation():
        return
    arguments = sys.argv[1:]
    if any(argument in {"-h", "--help", "--version"} for argument in arguments):
        _parse_command_line(arguments)


# Console entry points import their target module before calling it. Handle
# metadata commands now, using only the Python standard library, so ``carriage
# --help`` and ``carriage --version`` remain usable even when prompt_toolkit is
# missing or outside the supported range.
_exit_for_early_cli_metadata()


import prompt_toolkit
from prompt_toolkit.application import Application, in_terminal
from prompt_toolkit.cursor_shapes import CursorShape, SimpleCursorShapeConfig
from prompt_toolkit.output.color_depth import ColorDepth
from prompt_toolkit.application.current import get_app
from prompt_toolkit.buffer import Buffer
from prompt_toolkit.clipboard.base import Clipboard, ClipboardData
from prompt_toolkit.clipboard.in_memory import InMemoryClipboard
from prompt_toolkit.document import Document
from prompt_toolkit.data_structures import Point
from prompt_toolkit.filters import Condition, has_completions, has_focus
from prompt_toolkit.filters.app import buffer_has_focus
from prompt_toolkit.key_binding import KeyBindings
from prompt_toolkit.key_binding.bindings.focus import focus_next, focus_previous
from prompt_toolkit.lexers import Lexer
from prompt_toolkit.layout.containers import (
    Float,
    FloatContainer,
    HSplit,
    ConditionalContainer,
    Window,
    WindowAlign,
    WindowRenderInfo,
    VSplit,
)
from prompt_toolkit.layout.controls import BufferControl, FormattedTextControl
from prompt_toolkit.layout.processors import Processor, Transformation
from prompt_toolkit.layout.utils import explode_text_fragments
from prompt_toolkit.layout.dimension import D
from prompt_toolkit.layout.layout import Layout
from prompt_toolkit.layout.margins import Margin
from prompt_toolkit.layout.screen import Char
from prompt_toolkit.mouse_events import MouseButton, MouseEvent, MouseEventType
from prompt_toolkit.selection import SelectionType
from prompt_toolkit.styles import Style
from prompt_toolkit.utils import get_cwidth
from prompt_toolkit.widgets import (
    Box,
    Button,
    Dialog,
    Frame,
    Label,
    MenuContainer,
    MenuItem,
    Shadow,
    TextArea,
)


DEFAULT_WRAP_COLUMN = 80
DEFAULT_SCROLLBAR_VISIBLE = True
DEFAULT_STATUSBAR_VISIBLE = True
DEFAULT_MOUSE_ENABLED = True
DEFAULT_HARD_BREAK_MARKER_VISIBLE = True
DEFAULT_PANDOC_EXECUTABLE = "pandoc"

# Carriage deliberately relies on several prompt_toolkit implementation
# details for cursor geometry, mouse handling, scrolling, and unified undo.
# v1.125 was audited against 3.0.52 and 3.0.53; keep the initial public
# compatibility window deliberately narrow until newer releases pass the same
# editor-behavior regression suite.
PROMPT_TOOLKIT_MIN_VERSION = (3, 0, 52)
PROMPT_TOOLKIT_MAX_VERSION = (3, 0, 54)  # exclusive
PROMPT_TOOLKIT_REQUIREMENT = "prompt_toolkit>=3.0.52,<3.0.54"


def _prompt_toolkit_version_tuple(version_text):
    """Return the numeric release prefix from a prompt_toolkit version."""
    match = re.match(r"^(\d+)\.(\d+)\.(\d+)", str(version_text))
    if match is None:
        return None
    return tuple(int(part) for part in match.groups())


def _check_prompt_toolkit_compatibility():
    """Raise RuntimeError when prompt_toolkit is outside the audited window."""
    installed_text = getattr(prompt_toolkit, "__version__", "unknown")
    installed = _prompt_toolkit_version_tuple(installed_text)
    if (
        installed is None
        or installed < PROMPT_TOOLKIT_MIN_VERSION
        or installed >= PROMPT_TOOLKIT_MAX_VERSION
    ):
        raise RuntimeError(
            "Carriage requires "
            f"{PROMPT_TOOLKIT_REQUIREMENT}; found prompt_toolkit {installed_text}."
        )


def _window_render_info_contract_missing():
    """Return private WindowRenderInfo constructor fields Carriage requires."""
    try:
        parameters = inspect.signature(WindowRenderInfo.__init__).parameters
    except (TypeError, ValueError):
        return ["WindowRenderInfo constructor signature"]
    required = {
        "visible_line_to_row_col",
        "rowcol_to_yx",
        "x_offset",
        "y_offset",
    }
    return sorted(required - set(parameters))


def _check_prompt_toolkit_preconstruction_contract():
    """Validate the audited prompt_toolkit contract before building the UI.

    Carriage promotes and customizes prompt_toolkit widgets at module load. A
    version or private-contract failure therefore has to be detected before the
    first TextArea is constructed, not later in ``main()`` after those private
    surfaces have already been touched.
    """
    _check_prompt_toolkit_compatibility()

    # Probe the same instance-only state Carriage relies on without creating a
    # full TextArea, Layout, or Application. These constructors are terminal-
    # independent and make distro-patched builds fail at a controlled boundary.
    probe_buffer = Buffer()
    probe_control = BufferControl(buffer=probe_buffer)
    probe_window = Window(content=probe_control)
    required = [
        (probe_buffer, "_undo_stack", "Buffer undo stack"),
        (probe_buffer, "_redo_stack", "Buffer redo stack"),
        (probe_window, "_write_to_screen_at_index", "Window screen writer"),
        (probe_window, "_scroll", "Window scrolling hook"),
        (probe_window, "_get_margin_width", "Window margin geometry"),
        (probe_window, "_mouse_handler", "Window mouse fallback"),
        (probe_control, "_last_click_timestamp", "BufferControl click state"),
        (
            probe_control,
            "_last_get_processed_line",
            "BufferControl processed-line cache",
        ),
    ]
    missing = [label for obj, name, label in required if not hasattr(obj, name)]
    missing.extend(
        f"WindowRenderInfo.{name}" for name in _window_render_info_contract_missing()
    )
    if missing:
        details = ", ".join(missing)
        raise RuntimeError(
            "This prompt_toolkit build is missing private interfaces required "
            f"by Carriage: {details}. Reinstall {PROMPT_TOOLKIT_REQUIREMENT}."
        )


# Reject incompatible/private-API builds before the first prompt_toolkit widget
# is constructed. Script and installed-console launches receive one controlled
# stderr line; ordinary imports retain a RuntimeError for their caller.
try:
    _check_prompt_toolkit_preconstruction_contract()
except RuntimeError as _prompt_toolkit_startup_error:
    if _is_carriage_command_invocation():
        print(f"carriage: {_prompt_toolkit_startup_error}", file=sys.stderr)
        raise SystemExit(2)
    raise


class _CommandClipboardBackend:
    """Plain-text clipboard backend implemented by platform helper commands."""

    def __init__(self, name, copy_command, paste_command):
        self.name = name
        self.copy_command = tuple(copy_command)
        self.paste_command = tuple(paste_command)

    def set_text(self, text):
        result = subprocess.run(
            self.copy_command,
            input=text,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.DEVNULL,
            # wl-copy normally forks a background clipboard owner. Capturing
            # stderr here can leave the pipe inherited by that process and make
            # subprocess.run() wait until Carriage's timeout even though Copy
            # succeeded. Writes therefore discard helper diagnostics and rely
            # on the command's immediate return code.
            stderr=subprocess.DEVNULL,
            timeout=2,
            check=False,
        )
        if result.returncode != 0:
            raise OSError(f"{self.name} clipboard write failed")

    def get_text(self):
        result = subprocess.run(
            self.paste_command,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=2,
            check=False,
        )
        if result.returncode != 0:
            detail = (result.stderr or "").strip()
            raise OSError(detail or f"{self.name} clipboard read failed")
        return result.stdout


class _WindowsClipboardBackend:
    """Native Win32 Unicode clipboard support without third-party packages."""

    CF_UNICODETEXT = 13
    GMEM_MOVEABLE = 0x0002

    def __init__(self):
        import ctypes
        from ctypes import wintypes

        self.name = "Windows"
        self._ctypes = ctypes
        self._wintypes = wintypes
        self.user32 = ctypes.WinDLL("user32", use_last_error=True)
        self.kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

        self.user32.OpenClipboard.argtypes = [wintypes.HWND]
        self.user32.OpenClipboard.restype = wintypes.BOOL
        self.user32.CloseClipboard.argtypes = []
        self.user32.CloseClipboard.restype = wintypes.BOOL
        self.user32.EmptyClipboard.argtypes = []
        self.user32.EmptyClipboard.restype = wintypes.BOOL
        self.user32.IsClipboardFormatAvailable.argtypes = [wintypes.UINT]
        self.user32.IsClipboardFormatAvailable.restype = wintypes.BOOL
        self.user32.GetClipboardData.argtypes = [wintypes.UINT]
        self.user32.GetClipboardData.restype = wintypes.HANDLE
        self.user32.SetClipboardData.argtypes = [wintypes.UINT, wintypes.HANDLE]
        self.user32.SetClipboardData.restype = wintypes.HANDLE

        self.kernel32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]
        self.kernel32.GlobalAlloc.restype = wintypes.HGLOBAL
        self.kernel32.GlobalLock.argtypes = [wintypes.HGLOBAL]
        self.kernel32.GlobalLock.restype = ctypes.c_void_p
        self.kernel32.GlobalUnlock.argtypes = [wintypes.HGLOBAL]
        self.kernel32.GlobalUnlock.restype = wintypes.BOOL
        self.kernel32.GlobalFree.argtypes = [wintypes.HGLOBAL]
        self.kernel32.GlobalFree.restype = wintypes.HGLOBAL
        self.kernel32.GetConsoleWindow.argtypes = []
        self.kernel32.GetConsoleWindow.restype = wintypes.HWND

    def _raise_last_error(self, action):
        error = self._ctypes.get_last_error()
        if error:
            raise OSError(error, f"Windows clipboard {action} failed")
        raise OSError(f"Windows clipboard {action} failed")

    def _open(self):
        # EmptyClipboard() requires an owning window if SetClipboardData() is to
        # succeed. A console/pseudoconsole handle is sufficient for ownership;
        # if Windows cannot provide one, fail before touching the desktop
        # clipboard so Carriage can use its internal fallback safely.
        owner = self.kernel32.GetConsoleWindow()
        if not owner:
            raise OSError("Windows clipboard owner window is unavailable")

        # Another desktop process may briefly own the clipboard. A few short
        # retries keep ordinary copy/paste reliable without noticeably blocking
        # Carriage's UI thread.
        for _attempt in range(8):
            if self.user32.OpenClipboard(owner):
                return
            time.sleep(0.01)
        self._raise_last_error("open")

    @staticmethod
    def _windows_text(text):
        normalized = str(text).replace("\r\n", "\n").replace("\r", "\n")
        return normalized.replace("\n", "\r\n")

    def set_text(self, text):
        payload = (self._windows_text(text) + "\0").encode("utf-16-le")
        handle = self.kernel32.GlobalAlloc(self.GMEM_MOVEABLE, len(payload))
        if not handle:
            self._raise_last_error("allocation")

        transferred = False
        try:
            pointer = self.kernel32.GlobalLock(handle)
            if not pointer:
                self._raise_last_error("memory lock")
            try:
                self._ctypes.memmove(pointer, payload, len(payload))
            finally:
                self.kernel32.GlobalUnlock(handle)

            self._open()
            try:
                if not self.user32.EmptyClipboard():
                    self._raise_last_error("clear")
                if not self.user32.SetClipboardData(self.CF_UNICODETEXT, handle):
                    self._raise_last_error("write")
                # SetClipboardData owns the HGLOBAL after a successful call.
                transferred = True
            finally:
                self.user32.CloseClipboard()
        finally:
            if not transferred:
                self.kernel32.GlobalFree(handle)

    def get_text(self):
        if not self.user32.IsClipboardFormatAvailable(self.CF_UNICODETEXT):
            return None

        self._open()
        try:
            handle = self.user32.GetClipboardData(self.CF_UNICODETEXT)
            if not handle:
                self._raise_last_error("read")
            pointer = self.kernel32.GlobalLock(handle)
            if not pointer:
                self._raise_last_error("memory lock")
            try:
                return self._ctypes.wstring_at(pointer)
            finally:
                self.kernel32.GlobalUnlock(handle)
        finally:
            self.user32.CloseClipboard()


def _detect_system_clipboard_backend():
    """Return the best available plain-text desktop clipboard backend."""
    if os.name == "nt":
        try:
            return _WindowsClipboardBackend()
        except (OSError, AttributeError):
            return None

    if sys.platform == "darwin":
        pbcopy = shutil.which("pbcopy")
        pbpaste = shutil.which("pbpaste")
        if pbcopy and pbpaste:
            return _CommandClipboardBackend(
                "macOS", (pbcopy,), (pbpaste,)
            )
        return None

    # Wayland first, then the conventional X11 clipboard helpers. These tools
    # remain optional: a headless/minimal Linux install simply uses Carriage's
    # in-memory fallback.
    wl_copy = shutil.which("wl-copy")
    wl_paste = shutil.which("wl-paste")
    if wl_copy and wl_paste and os.environ.get("WAYLAND_DISPLAY"):
        return _CommandClipboardBackend(
            "Wayland",
            (wl_copy, "--type", "text/plain;charset=utf-8"),
            (wl_paste, "--no-newline", "--type", "text"),
        )

    xclip = shutil.which("xclip")
    if xclip and os.environ.get("DISPLAY"):
        return _CommandClipboardBackend(
            "X11",
            (xclip, "-selection", "clipboard", "-in"),
            (xclip, "-selection", "clipboard", "-out"),
        )

    xsel = shutil.which("xsel")
    if xsel and os.environ.get("DISPLAY"):
        return _CommandClipboardBackend(
            "X11",
            (xsel, "--clipboard", "--input"),
            (xsel, "--clipboard", "--output"),
        )

    return None


def _normalize_clipboard_text(text):
    """Normalize external clipboard line endings to Carriage's LF convention."""
    return str(text).replace("\r\n", "\n").replace("\r", "\n")


def _normalized_clipboard_data(data):
    """Return plain clipboard data with LF-normalized text."""
    if not isinstance(data, ClipboardData):
        return ClipboardData()
    return ClipboardData(_normalize_clipboard_text(data.text), data.type)


class CarriageClipboard(Clipboard):
    """Desktop clipboard with a conservative in-memory fallback.

    Every Carriage Copy/Cut records plain text internally first, then mirrors it
    to the desktop when possible. A failed desktop write makes that internal
    copy authoritative so a subsequent Paste cannot resurrect stale desktop
    text. When the desktop state observed after the failure is known, Carriage
    can also detect a later external Copy and resume normal desktop-first Paste.
    """

    _UNKNOWN_DESKTOP = object()

    def __init__(self, backend=None):
        self._memory = InMemoryClipboard()
        self._backend = backend if backend is not None else _detect_system_clipboard_backend()
        self._fallback_notice_shown = False
        self._desktop_out_of_sync = False
        self._stale_desktop_text = self._UNKNOWN_DESKTOP

    @property
    def backend_name(self):
        return getattr(self._backend, "name", None)

    def _notice_fallback(self):
        if self._fallback_notice_shown:
            return
        self._fallback_notice_shown = True
        notice = globals().get("show_transient_status")
        if callable(notice):
            try:
                notice(
                    "System clipboard unavailable; using Carriage clipboard.",
                    duration=4.0,
                )
            except Exception:
                pass

    def _snapshot_desktop_after_failed_write(self):
        if self._backend is None:
            return self._UNKNOWN_DESKTOP
        try:
            return self._backend.get_text()
        except (OSError, subprocess.SubprocessError, UnicodeError):
            return self._UNKNOWN_DESKTOP

    def _desktop_changed_since_failed_write(self):
        """Return new desktop text when a later external Copy can be proven."""
        if self._backend is None or self._stale_desktop_text is self._UNKNOWN_DESKTOP:
            return self._UNKNOWN_DESKTOP
        try:
            current = self._backend.get_text()
        except (OSError, subprocess.SubprocessError, UnicodeError):
            return self._UNKNOWN_DESKTOP
        if current == self._stale_desktop_text:
            return self._UNKNOWN_DESKTOP
        return current

    def set_data(self, data):
        normalized = _normalized_clipboard_data(data)
        self._memory.set_data(normalized)
        if self._backend is None:
            self._desktop_out_of_sync = True
            self._stale_desktop_text = self._UNKNOWN_DESKTOP
            self._notice_fallback()
            return
        try:
            self._backend.set_text(normalized.text)
        except (OSError, subprocess.SubprocessError, UnicodeError):
            # The desktop may still contain an older value—or a helper may have
            # partially cleared it. Record whatever is readable now so a later
            # external Copy can be distinguished from that stale state.
            self._desktop_out_of_sync = True
            self._stale_desktop_text = self._snapshot_desktop_after_failed_write()
            self._notice_fallback()
            return

        self._desktop_out_of_sync = False
        self._stale_desktop_text = self._UNKNOWN_DESKTOP
        # Recovery should make a later, separate outage visible again.
        self._fallback_notice_shown = False

    def get_data(self):
        if self._backend is None:
            self._notice_fallback()
            return _normalized_clipboard_data(self._memory.get_data())

        if self._desktop_out_of_sync:
            changed = self._desktop_changed_since_failed_write()
            if changed is not self._UNKNOWN_DESKTOP:
                self._desktop_out_of_sync = False
                self._stale_desktop_text = self._UNKNOWN_DESKTOP
                data = ClipboardData(
                    _normalize_clipboard_text(changed or ""),
                    SelectionType.CHARACTERS,
                )
                self._memory.set_data(data)
                return data
            return _normalized_clipboard_data(self._memory.get_data())

        try:
            text = self._backend.get_text()
        except (OSError, subprocess.SubprocessError, UnicodeError):
            # When the desktop clipboard was synchronized before the read, an
            # unreadable/non-text clipboard is not evidence that an older
            # Carriage copy is current. Paste therefore becomes a no-op.
            return ClipboardData()

        if text is None:
            return ClipboardData()

        data = ClipboardData(
            _normalize_clipboard_text(text), SelectionType.CHARACTERS
        )
        self._memory.set_data(data)
        return data

    def rotate(self):
        self._memory.rotate()


@lru_cache(maxsize=4096)
def _display_char_width(char):
    """Return the terminal-cell width prompt_toolkit will actually render.

    ``get_cwidth`` reports control characters such as a literal tab as zero
    width, while prompt_toolkit's ``Char`` screen object displays them using a
    printable control-character mapping (a tab becomes ``^I``). Cursor geometry
    must use the rendered width or visual navigation can drift from the screen.
    """
    if not char:
        return 0
    rendered = Char.display_mappings.get(char, char)
    return max(0, get_cwidth(rendered))


def _display_text_width(text):
    """Return rendered terminal-cell width using prompt_toolkit semantics."""
    width_of = _display_char_width
    total = 0
    for char in text or "":
        total += width_of(char)
    return total


DEFAULT_SPELLCHECK_COMMAND = ["aspell", "--mode=markdown", "check", "{file}"]
MIN_WRAP_COLUMN = 40
MAX_WRAP_COLUMN = 160


def _config_directory():
    """Return Carriage's per-user configuration directory."""
    config_home = os.environ.get("XDG_CONFIG_HOME")
    if not config_home:
        config_home = os.path.join(os.path.expanduser("~"), ".config")
    return os.path.join(config_home, "carriage")


def _config_path():
    """Return the XDG-style TOML configuration path."""
    return os.path.join(_config_directory(), "config.toml")



def _default_config():
    return {
        "prose_width": DEFAULT_WRAP_COLUMN,
        "scrollbar": DEFAULT_SCROLLBAR_VISIBLE,
        "statusbar": DEFAULT_STATUSBAR_VISIBLE,
        "mouse": DEFAULT_MOUSE_ENABLED,
        "hard_break_marker": DEFAULT_HARD_BREAK_MARKER_VISIBLE,
        "pandoc": DEFAULT_PANDOC_EXECUTABLE,
        "spellcheck_command": list(DEFAULT_SPELLCHECK_COMMAND),
    }


def _fallback_parse_toml(text):
    """Parse the small TOML subset used by Carriage when tomllib is unavailable.

    Carriage itself writes only tables, booleans, integers, quoted strings, and
    arrays of quoted strings. This fallback keeps Python 3.10 usable without a
    new dependency; Python 3.11+ uses the standard-library TOML parser below.
    """
    result = {}
    current = result
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            name = line[1:-1].strip()
            if not name or "." in name:
                raise ValueError("unsupported TOML table")
            current = result.setdefault(name, {})
            if not isinstance(current, dict):
                raise ValueError("invalid TOML table")
            continue
        if "=" not in line:
            raise ValueError("invalid TOML assignment")
        key, value = (part.strip() for part in line.split("=", 1))
        # Carriage's generated file keeps comments on their own lines. The
        # fallback intentionally accepts that documented subset only.
        if value == "true":
            parsed = True
        elif value == "false":
            parsed = False
        elif re.fullmatch(r"[+-]?\d+", value):
            parsed = int(value)
        elif value.startswith('"'):
            parsed = json.loads(value)
        elif value.startswith("[") and value.endswith("]"):
            parsed = json.loads(value)
        else:
            raise ValueError("unsupported TOML value")
        current[key] = parsed
    return result


class _ConfigTomlError(ValueError):
    """Configuration parse error with enough context for a useful warning."""

    def __init__(self, message, *, fallback_parser=False):
        super().__init__(message)
        self.fallback_parser = bool(fallback_parser)


def _read_toml_file(path):
    with open(path, "rb") as f:
        data = f.read()
    text = data.decode("utf-8")

    try:
        import tomllib
    except ImportError:
        try:
            import tomli as tomllib
        except ImportError:
            tomllib = None

    if tomllib is not None:
        try:
            return tomllib.loads(text)
        except ValueError as e:
            raise _ConfigTomlError(str(e)) from e

    try:
        return _fallback_parse_toml(text)
    except (ValueError, json.JSONDecodeError) as e:
        raise _ConfigTomlError(
            "The configuration uses TOML syntax that Carriage's built-in "
            "Python 3.10 fallback parser cannot read. Install the optional "
            "'tomli' package or use the syntax produced by Carriage's generated "
            f"config.toml. Parser detail: {e}",
            fallback_parser=True,
        ) from e


def _config_diagnostic(diagnostics, message):
    if diagnostics is not None:
        diagnostics.append(str(message))


def _validate_config(raw, diagnostics=None):
    """Return valid settings and report only values that were ignored.

    Missing settings remain defaults without a warning. A syntactically valid
    configuration can therefore contain one bad value without discarding the
    other valid settings.
    """
    cfg = _default_config()
    if not isinstance(raw, dict):
        _config_diagnostic(
            diagnostics,
            "The configuration root is not a TOML table; all settings use defaults.",
        )
        return cfg

    known_tables = {"editor", "interface", "tools"}
    for key in raw:
        if key not in known_tables:
            _config_diagnostic(
                diagnostics,
                f"Unrecognized top-level setting or table {key!r} was ignored.",
            )

    sections = {}
    for section_name in ("editor", "interface", "tools"):
        section = raw.get(section_name, {})
        if isinstance(section, dict):
            sections[section_name] = section
        else:
            sections[section_name] = {}
            if section_name in raw:
                _config_diagnostic(
                    diagnostics,
                    f"[{section_name}] must be a TOML table; that section was ignored.",
                )

    editor = sections["editor"]
    interface = sections["interface"]
    tools = sections["tools"]

    known_editor = {"prose_width"}
    known_interface = {"scrollbar", "statusbar", "mouse", "hard_break_marker"}
    known_tools = {"pandoc", "spellcheck_command"}
    for section_name, section, known in (
        ("editor", editor, known_editor),
        ("interface", interface, known_interface),
        ("tools", tools, known_tools),
    ):
        for key in section:
            if key not in known:
                _config_diagnostic(
                    diagnostics,
                    f"Unrecognized setting {section_name}.{key} was ignored.",
                )

    if "prose_width" in editor:
        width = editor["prose_width"]
        if (
            isinstance(width, int)
            and not isinstance(width, bool)
            and MIN_WRAP_COLUMN <= width <= MAX_WRAP_COLUMN
        ):
            cfg["prose_width"] = width
        else:
            _config_diagnostic(
                diagnostics,
                f"editor.prose_width must be an integer from {MIN_WRAP_COLUMN} "
                f"to {MAX_WRAP_COLUMN}; using {cfg['prose_width']}.",
            )

    for key in ("scrollbar", "statusbar", "mouse", "hard_break_marker"):
        if key not in interface:
            continue
        value = interface[key]
        if isinstance(value, bool):
            cfg[key] = value
        else:
            _config_diagnostic(
                diagnostics,
                f"interface.{key} must be true or false; using {cfg[key]!r}.",
            )

    if "pandoc" in tools:
        pandoc = tools["pandoc"]
        if isinstance(pandoc, str) and pandoc.strip():
            cfg["pandoc"] = pandoc.strip()
        else:
            _config_diagnostic(
                diagnostics,
                f"tools.pandoc must be a non-empty string; using {cfg['pandoc']!r}.",
            )

    if "spellcheck_command" in tools:
        spellcheck = tools["spellcheck_command"]
        if (
            isinstance(spellcheck, list)
            and spellcheck
            and all(isinstance(arg, str) and arg for arg in spellcheck)
            and "{file}" not in spellcheck[0]
            and any("{file}" in arg for arg in spellcheck)
        ):
            cfg["spellcheck_command"] = list(spellcheck)
        else:
            _config_diagnostic(
                diagnostics,
                "tools.spellcheck_command must be a non-empty array of non-empty "
                "strings, with {file} in an argument after the executable; using "
                "the default spell-check command.",
            )

    return cfg


def _load_config():
    """Load configuration and retain diagnostics for one startup warning."""
    diagnostics = []
    path = _config_path()
    try:
        raw = _read_toml_file(path)
    except FileNotFoundError:
        return _default_config(), diagnostics
    except UnicodeError as e:
        diagnostics.append(
            f"The configuration is not valid UTF-8 ({e}); all settings use defaults."
        )
        return _default_config(), diagnostics
    except _ConfigTomlError as e:
        diagnostics.append(f"Could not parse config.toml: {e}")
        diagnostics.append("Because the TOML could not be parsed safely, all settings use defaults.")
        return _default_config(), diagnostics
    except OSError as e:
        diagnostics.append(
            f"Could not read config.toml ({e}); all settings use defaults."
        )
        return _default_config(), diagnostics

    return _validate_config(raw, diagnostics), diagnostics


def _toml_string(value):
    """Return a TOML basic string using JSON-compatible escaping."""
    return json.dumps(str(value), ensure_ascii=False)


def _serialize_config_toml(config):
    spell = ", ".join(_toml_string(arg) for arg in config["spellcheck_command"])
    return (
        "# Carriage configuration\n"
        "# Persistent settings are read at startup.\n"
        "# Edit this file manually; Carriage has no Preferences dialog.\n"
        "# Unsaved working state is protected automatically and is not configurable.\n\n"
        "[editor]\n"
        f"prose_width = {int(config['prose_width'])}\n\n"
        "[interface]\n"
        f"scrollbar = {str(bool(config['scrollbar'])).lower()}\n\n"
        "# Advanced: startup/default interface behavior. The status bar can be\n"
        "# toggled for the current session from the Edit menu.\n"
        f"statusbar = {str(bool(config['statusbar'])).lower()}\n"
        f"mouse = {str(bool(config['mouse'])).lower()}\n"
        f"hard_break_marker = {str(bool(config['hard_break_marker'])).lower()}\n\n"
        "[tools]\n"
        "# Advanced: executable used for all Pandoc exports.\n"
        f"pandoc = {_toml_string(config['pandoc'])}\n\n"
        "# Advanced: interactive terminal spell checker. The command must edit the\n"
        "# open file in place and exit when finished. {file} is replaced by the path.\n"
        f"spellcheck_command = [{spell}]\n"
    )


def _validate_flat_config(config, diagnostics=None):
    """Validate Carriage's flat in-memory configuration representation.

    ``_validate_config`` consumes the nested tables produced by TOML parsing,
    while the rest of Carriage stores validated settings in one flat mapping.
    Convert that internal representation back to the parser shape so writing a
    non-default in-memory configuration preserves its values instead of silently
    replacing them with defaults.
    """
    if not isinstance(config, dict):
        return _validate_config(config, diagnostics)

    raw = {
        "editor": {},
        "interface": {},
        "tools": {},
    }
    destinations = {
        "prose_width": ("editor", "prose_width"),
        "scrollbar": ("interface", "scrollbar"),
        "statusbar": ("interface", "statusbar"),
        "mouse": ("interface", "mouse"),
        "hard_break_marker": ("interface", "hard_break_marker"),
        "pandoc": ("tools", "pandoc"),
        "spellcheck_command": ("tools", "spellcheck_command"),
    }

    for key, value in config.items():
        destination = destinations.get(key)
        if destination is None:
            _config_diagnostic(
                diagnostics,
                f"Unrecognized in-memory setting {key!r} was ignored.",
            )
            continue
        section_name, setting_name = destination
        raw[section_name][setting_name] = value

    return _validate_config(raw, diagnostics)


def _write_config(config):
    """Durably write a complete validated Carriage configuration."""
    path = _config_path()
    directory = os.path.dirname(path)
    os.makedirs(directory, exist_ok=True)
    payload = _serialize_config_toml(_validate_flat_config(config))

    def write_staged(temp_path):
        with open(temp_path, "w", encoding="utf-8", newline="\n") as f:
            f.write(payload)
            f.flush()

    _durable_atomic_replace(
        path,
        write_staged,
        temp_prefix=".config-",
        temp_suffix=".tmp",
        new_file_mode=_new_file_mode_from_umask(),
        preserve_existing_metadata=True,
        reject_hardlinks=True,
    )


_CONFIG, _CONFIG_DIAGNOSTICS = _load_config()
WRAP_COLUMN = _CONFIG["prose_width"]
SCROLLBAR_VISIBLE = _CONFIG["scrollbar"]
STATUSBAR_DEFAULT_VISIBLE = _CONFIG["statusbar"]
MOUSE_ENABLED = _CONFIG["mouse"]
HARD_BREAK_MARKER_VISIBLE = _CONFIG["hard_break_marker"]
PANDOC_EXECUTABLE = _CONFIG["pandoc"]
SPELLCHECK_COMMAND = tuple(_CONFIG["spellcheck_command"])

STRUCTURE_GUTTER_WIDTH = 8
TAB_WIDTH = 4
HARD_BREAK_DISPLAY_CHAR = "↵"
WORKING_STATE_IDLE_SECONDS = 2.0
WORKING_STATE_MAX_LATENCY_SECONDS = 10.0
WORKING_STATE_POLL_SECONDS = 0.25
LARGE_FILE_WARNING_BYTES = 8 * 1024 * 1024
FILE_READ_CHUNK_BYTES = 1024 * 1024
RECOVERY_FORMAT_VERSION = 4
TABLE_SENTINEL = "\u2063"  # zero-width INVISIBLE SEPARATOR; never written to disk
FOOTNOTE_SENTINEL = "\u2064"  # zero-width INVISIBLE PLUS; never written to disk
TABLE_PLACEHOLDER_RE = re.compile(
    rf"^\[\[Table (\d+)(?:: (.*?))?\]\]{TABLE_SENTINEL}$"
)
FOOTNOTE_PLACEHOLDER_RE = re.compile(
    rf"^\[\[Footnote: ([^\]]+)\]\]{FOOTNOTE_SENTINEL}$"
)
_FOOTNOTE_REFERENCE_RE = re.compile(r"\[\^([^\]\n]+)\](?!:)")
_SPACED_DASH_STANDIN_RE = re.compile(
    r"(?P<left>\S+)(?P<gap1>[ \t]+)(?P<dash>-{2,})(?P<gap2>[ \t]+)(?P<right>\S+)"
)

# Status-bar word count is intentionally prose-oriented rather than a count of
# Markdown lexical tokens.  Hyphenated compounds and apostrophe contractions
# count as one word; dash stand-ins such as ``word---word`` still count the two
# prose words on either side.
_PROSE_WORD_RE = re.compile(
    r"(?:\d+(?:[.,]\d+)+|"
    r"[^\W_]+(?:[’'][^\W_]+)*(?:-[^\W_]+(?:[’'][^\W_]+)*)*)",
    re.UNICODE,
)
_BARE_URL_OR_EMAIL_RE = re.compile(
    r"(?i)(?:\bhttps?://[^\s<>]+|\bwww\.[^\s<>]+|"
    r"\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b)"
)
_AUTOLINK_RE = re.compile(
    r"(?i)<(?:https?://[^<>\s]+|[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,})>"
)


def _markdown_char_is_escaped(text, index):
    """Return True when the character at index is escaped by an odd \\ run."""
    backslashes = 0
    index -= 1
    while index >= 0 and text[index] == "\\":
        backslashes += 1
        index -= 1
    return bool(backslashes % 2)


_RANGE_BISECT_SENTINEL = float("inf")


def _range_contains(ranges, position):
    """Return True when position lies inside sorted, non-overlapping ranges."""
    if not ranges:
        return False
    index = bisect_right(ranges, (position, _RANGE_BISECT_SENTINEL)) - 1
    return index >= 0 and position < ranges[index][1]


def _merge_source_ranges(ranges):
    """Return sorted, non-overlapping source ranges."""
    merged = []
    for start, end in sorted(ranges):
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return merged


@lru_cache(maxsize=8)
def _inline_code_span_ranges(full_text):
    """Return source ranges occupied by original-Markdown inline code spans.

    Markdown.pl permits arbitrary-length backtick delimiters and code-span
    content may cross physical source lines.  These ranges are shared by
    footnote recognition and hard-break handling so literal code is never
    reinterpreted as either extension syntax or a two-space line break.
    """
    ranges = []
    n = len(full_text)
    i = 0
    while i < n:
        if full_text[i] != "`" or _markdown_char_is_escaped(full_text, i):
            i += 1
            continue
        run_end = i + 1
        while run_end < n and full_text[run_end] == "`":
            run_end += 1
        marker = full_text[i:run_end]
        search = run_end
        close = None
        while True:
            found = full_text.find(marker, search)
            if found < 0:
                break
            before_tick = found > 0 and full_text[found - 1] == "`"
            after = found + len(marker)
            after_tick = after < n and full_text[after] == "`"
            if not before_tick and not after_tick:
                close = after
                break
            search = found + len(marker)
        if close is not None:
            ranges.append((i, close))
            i = close
        else:
            i = run_end
    return tuple(ranges)


@lru_cache(maxsize=8)
def _source_lines(full_text):
    """Return physical source lines once per document text generation."""
    return tuple(full_text.split("\n"))


@lru_cache(maxsize=8)
def _source_line_offsets(full_text):
    """Return global source offsets for the start of every physical line."""
    offsets = []
    position = 0
    lines = full_text.split("\n")
    for index, line in enumerate(lines):
        offsets.append(position)
        position += len(line)
        if index < len(lines) - 1:
            position += 1
    return tuple(offsets)


def _escaped_source_positions(text):
    """Return indexes whose character is escaped by an odd backslash run.

    Several inline recognizers need the same escape test while scanning the
    document. Computing the relevant positions once keeps those scans linear
    even on source containing very long backslash runs.
    """
    escaped = set()
    backslashes = 0
    for index, char in enumerate(text):
        if char == "\\":
            backslashes += 1
            continue
        if backslashes % 2:
            escaped.add(index)
        backslashes = 0
    return frozenset(escaped)


def _angle_inline_ranges(full_text, code_ranges, escaped_positions):
    """Return complete single-line ``<...>`` inline ranges in one pass.

    Carriage intentionally recognizes these constructs only as literal source
    regions for footnote exclusion; it does not parse or normalize their
    contents. A failed candidate advances to the next physical line, avoiding
    the old repeated suffix scan for every unmatched ``<``.
    """
    ranges = []
    n = len(full_text)
    code_index = 0
    i = 0

    while i < n:
        while code_index < len(code_ranges) and code_ranges[code_index][1] <= i:
            code_index += 1
        if code_index < len(code_ranges):
            start, end = code_ranges[code_index]
            if start <= i < end:
                i = end
                continue

        char = full_text[i]
        if char != "<" or i in escaped_positions:
            i += 1
            continue

        quote = None
        j = i + 1
        while j < n and full_text[j] != "\n":
            current = full_text[j]
            if j in escaped_positions:
                j += 1
                continue
            if quote is not None:
                if current == quote:
                    quote = None
            elif current in {'"', "'"}:
                quote = current
            elif current == ">":
                ranges.append((i, j + 1))
                i = j + 1
                break
            j += 1
        else:
            # No unquoted closer exists for this candidate before the physical
            # line ends. Under Carriage's valid-Markdown input contract, later
            # '<' characters on the same malformed line cannot establish a
            # construct that needs footnote protection, so skip the remainder
            # of the line instead of rescanning the same suffix repeatedly.
            newline = full_text.find("\n", i)
            i = n if newline < 0 else newline + 1

    return ranges


def _scan_inline_link_destination(text, start, escaped_positions):
    """Return the end of a complete ``(...)`` destination, or ``None``."""
    depth = 1
    quote = None
    j = start + 1
    n = len(text)
    while j < n:
        char = text[j]
        if j in escaped_positions:
            j += 1
            continue
        if quote is not None:
            if char == quote:
                quote = None
        elif char in {'"', "'"}:
            quote = char
        elif char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return None


def _scan_reference_label(text, start, escaped_positions):
    """Return the end of a complete single-line ``[...]`` label, or None."""
    j = start + 1
    n = len(text)
    while j < n and text[j] != "\n":
        if text[j] == "]" and j not in escaped_positions:
            return j + 1
        j += 1
    return None


@lru_cache(maxsize=8)
def _inline_footnote_literal_ranges(full_text):
    """Return inline ranges where ``[^id]`` must remain literal.

    Footnotes are an extension layered on original Markdown. Their reference
    syntax loses special meaning inside original-Markdown code spans,
    autolinks/inline HTML, inline link/image destinations, and the second label
    of reference-style links/images.

    Recognition is deliberately a forward scan. The previous implementation
    searched backward from every ``]`` and repeatedly rescanned the remainder
    of a line from every unmatched ``<``, producing quadratic behavior on
    otherwise harmless source text.
    """
    n = len(full_text)
    code_ranges = list(_inline_code_span_ranges(full_text))
    escaped_positions = _escaped_source_positions(full_text)
    angle_ranges = _angle_inline_ranges(
        full_text, code_ranges, escaped_positions
    )
    protected = _merge_source_ranges(code_ranges + angle_ranges)

    link_ranges = []
    bracket_stack = []
    protected_index = 0
    i = 0

    while i < n:
        while (
            protected_index < len(protected)
            and protected[protected_index][1] <= i
        ):
            protected_index += 1
        if protected_index < len(protected):
            start, end = protected[protected_index]
            if start <= i < end:
                if full_text.find("\n", i, end) >= 0:
                    bracket_stack.clear()
                i = end
                continue

        char = full_text[i]
        if char == "\n":
            # Footnote exclusion deliberately keeps link labels on one physical
            # source line. This matches Carriage's prior conservative contract.
            bracket_stack.clear()
            i += 1
            continue

        if i in escaped_positions:
            i += 1
            continue

        if char == "[":
            bracket_stack.append(i)
            i += 1
            continue

        if char != "]" or not bracket_stack:
            i += 1
            continue

        # The top stack entry is the same balanced opening label that the old
        # backward depth scan would find, but it is obtained in O(1).
        label_start = bracket_stack.pop()
        next_index = i + 1
        completed_label_is_footnote = (
            label_start + 2 < i
            and full_text[label_start + 1] == "^"
            and not (
                label_start > 0
                and full_text[label_start - 1] == "!"
                and label_start - 1 not in escaped_positions
            )
        )

        if next_index < n and full_text[next_index] == "(":
            destination_end = _scan_inline_link_destination(
                full_text, next_index, escaped_positions
            )
            if destination_end is not None:
                link_ranges.append((next_index, destination_end))
                i = destination_end
                continue

        reference_start = next_index
        while reference_start < n and full_text[reference_start] in " \t":
            reference_start += 1
        if (
            not completed_label_is_footnote
            and reference_start < n
            and full_text[reference_start] == "["
            and reference_start not in escaped_positions
        ):
            reference_end = _scan_reference_label(
                full_text, reference_start, escaped_positions
            )
            if reference_end is not None:
                link_ranges.append((reference_start, reference_end))
                i = reference_end
                continue

        i += 1

    return tuple(_merge_source_ranges(protected + link_ranges))

@lru_cache(maxsize=8)
def _footnote_reference_spans(full_text):
    """Return real inline footnote references as global source spans."""
    protected = _inline_footnote_literal_ranges(full_text)
    lines = full_text.split("\n")
    excluded_rows = set()
    skip_kinds = {
        "front-matter",
        "code",
        "block-html",
        "table",
        "reference-definition",
        "footnote-placeholder",
        "opaque-extension",
    }
    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        if block.kind in skip_kinds:
            excluded_rows.update(range(block.start, block.end))

    spans = []
    offset = 0
    range_index = 0
    for row, line in enumerate(lines):
        if row not in excluded_rows:
            for match in _FOOTNOTE_REFERENCE_RE.finditer(line):
                start = offset + match.start()
                end = offset + match.end()
                if _markdown_char_is_escaped(full_text, start):
                    continue
                while range_index < len(protected) and protected[range_index][1] <= start:
                    range_index += 1
                if range_index < len(protected):
                    p_start, p_end = protected[range_index]
                    if p_start < end and start < p_end:
                        continue
                identifier = match.group(1).strip()
                if identifier:
                    spans.append((start, end, identifier, row, match.start(), match.end()))
        offset += len(line) + 1
    return tuple(spans)


@lru_cache(maxsize=8)
def _footnote_reference_rows(full_text):
    rows = [[] for _ in full_text.split("\n")]
    for _start, _end, identifier, row, start_col, end_col in _footnote_reference_spans(full_text):
        if 0 <= row < len(rows):
            rows[row].append((start_col, end_col, identifier))
    return tuple(tuple(row) for row in rows)


def _footnote_references_on_row(full_text, row):
    rows = _footnote_reference_rows(full_text)
    if 0 <= row < len(rows):
        return rows[row]
    return ()
_FOOTNOTE_DEFINITION_RE = re.compile(
    r"^\s{0,3}\[\^([^\]]+)\]:[ \t]*(.*)$"
)
_TABLE_CAPTION_RE = re.compile(r"^\s*(?:Table:|table:|:)\s*(?P<title>\S.*)\s*$")
MAX_TABLE_EDITOR_COLUMNS = 6
MAX_TABLE_INSERT_ROWS = 60


@dataclass
class TableData:
    """In-memory representation of one folded pipe table."""

    headers: list[str]
    rows: list[list[str]]
    title: str = ""
    alignments: list[str] = field(default_factory=list)
    original_lines: list[str] | None = None
    caption_position: str | None = None
    dirty: bool = False

    @property
    def column_count(self):
        return len(self.headers)


@dataclass
class TableEditorSession:
    table_number: int
    working: TableData
    selected_row: int = 0  # 0 is the header row; data rows start at 1.
    selected_col: int = 0
    cell_editor: object | None = None
    title_editor: object | None = None
    grid_control: object | None = None
    cell_label: object | None = None
    mode_label: object | None = None
    grid_window: object | None = None
    dialog_float: object | None = None
    editing: bool = False
    # Display-only table geometry/wrapping cache. The key includes the current
    # working cell contents and terminal width, so both height measurement and
    # fragment generation consume one computed layout without stale edits.
    grid_layout_key: object | None = None
    grid_layout_cache: object | None = None
    # Which edge of the selected row should be kept visible in the table
    # viewport. Moving downward anchors the row's bottom; moving upward anchors
    # its top. This matters for prose-heavy rows that span several screen lines.
    scroll_anchor: str = "top"


@dataclass
class FootnoteData:
    """One folded prose footnote definition, possibly with several paragraphs."""

    identifier: str
    text: str
    original_lines: list[str] | None = None
    dirty: bool = False


@dataclass
class FootnoteEditorSession:
    identifier: str
    working: FootnoteData
    editor: object | None = None
    dialog_float: object | None = None


@dataclass
class FindReplaceSession:
    """Ephemeral status-line Find/Replace state; never written to the document."""

    active: bool = False
    mode: str = "find"
    query: str = ""
    replacement: str = ""
    search_anchor: int = 0
    origin_cursor: int = 0
    origin_selection: object | None = None
    current_match: tuple[int, int] | None = None
    match_index: int = -1
    match_count: int = 0
    wrapped: bool = False
    case_sensitive: bool = False
    whole_word: bool = False
    changed: bool = False
    suppress_input_events: bool = False


# ---------------------------------------------------------------------------
# Editor state
# ---------------------------------------------------------------------------

class EditorState:
    def __init__(self):
        self.path = None
        self.statusbar_visible = STATUSBAR_DEFAULT_VISIBLE
        # Transient notices always occupy the status-line position. When the
        # ordinary status bar is hidden, a one-row overlay appears there only
        # for the lifetime of the notice, so editor geometry never jumps.
        self.transient_status_message = None
        self.transient_status_expires_at = 0.0
        self.transient_status_generation = 0
        # F6 toggles a portable Extend Selection mode. This is session state,
        # not a preference, and any document edit returns to normal movement.
        self.extend_selection_mode = False
        self.saved_text = ""
        # Fingerprint of the exact on-disk bytes last opened or successfully
        # written by Carriage. A save must still see this same version before
        # it is allowed to replace the file.
        self.disk_snapshot = None
        # Pandoc exports run in a worker thread so the editor remains responsive.
        # Only one Pandoc export may own the destination/export state at a time.
        self.pandoc_export_running = False
        # Hidden durable working-state protection. The recovery journal tracks
        # unsaved named and untitled documents, including in-progress table and
        # footnote drafts, without changing the Markdown source file. It is
        # removed after a successful explicit Save, New, Open, or clean discard.
        self.recovery_path = None
        self.recovery_epoch = 0
        self.recovery_committed_revision = 0
        self.recovery_error = False
        self.recovery_error_reported = False
        self.recovery_error_message = None
        self.recovery_error_kind = None
        # Recovery write failures mean current unsaved work is not durably
        # journaled. Cleanup failures are different: the document may already
        # be saved/discarded, but an obsolete journal could not be removed or
        # safely marked retired. Keep the two failure classes separate so a
        # later successful checkpoint cannot accidentally hide a cleanup issue.
        self.recovery_write_error_message = None
        self.recovery_cleanup_failures = {}
        self.recovery_cleanup_retry_at = 0.0
        self.working_state_revision = 0
        self.working_state_persisted_revision = 0
        self.working_state_first_dirty_at = None
        self.working_state_last_change_at = None
        self.tables = {}
        self.footnotes = {}

    def is_modified(self, current_text):
        try:
            source_text = _materialize_objects(current_text)
        except ValueError:
            return True
        return source_text != self.saved_text


state = EditorState()
find_replace = FindReplaceSession()

def _working_state_changed(_buffer=None, *, immediate=False):
    """Mark unsaved working state for near-continuous durable protection."""
    now = time.monotonic()
    state.working_state_revision += 1
    if immediate:
        # Meaningful object commits and draft cancellation boundaries should be
        # journaled on the next scheduler tick rather than waiting for idle.
        state.working_state_first_dirty_at = now - WORKING_STATE_MAX_LATENCY_SECONDS
        state.working_state_last_change_at = now - WORKING_STATE_IDLE_SECONDS
        return
    if state.working_state_first_dirty_at is None:
        state.working_state_first_dirty_at = now
    state.working_state_last_change_at = now


def _reset_working_state_tracking():
    """Mark the current in-memory state as fully accounted for on disk/journal."""
    state.working_state_persisted_revision = state.working_state_revision
    state.working_state_first_dirty_at = None
    state.working_state_last_change_at = None


@dataclass(frozen=True)
class _CarriageUndoState:
    """One complete committed-document state for Undo/Redo.

    The table/footnote dictionaries are persistent snapshots: committed object
    changes use copy-on-write, so ordinary prose edits can share these mappings
    across many undo entries without deep-copying object data on every keypress.
    """

    text: str
    cursor_position: int
    tables: dict[int, TableData]
    footnotes: dict[str, FootnoteData]


class CarriageBuffer(Buffer):
    """Buffer whose undo history includes Carriage's folded document objects."""

    def _carriage_state(self):
        return _CarriageUndoState(
            text=self.text,
            cursor_position=self.cursor_position,
            tables=state.tables,
            footnotes=state.footnotes,
        )

    @staticmethod
    def _same_content(first, second):
        return (
            first.text == second.text
            and first.tables is second.tables
            and first.footnotes is second.footnotes
        )

    def reset(self, document=None, append_to_history=False):
        super().reset(document=document, append_to_history=append_to_history)
        # Buffer.reset() creates ordinary tuple stacks. Replace them with the
        # unified Carriage state stacks every time a document is loaded/newed.
        self._undo_stack = []
        self._redo_stack = []

    def save_to_undo_stack(self, clear_redo_stack=True):
        current = self._carriage_state()

        # Match prompt_toolkit's normal behavior: if the content at the top of
        # the stack is unchanged, only refresh its cursor position. Object-only
        # changes count as content changes even when visible text is identical.
        if self._undo_stack and self._same_content(self._undo_stack[-1], current):
            previous = self._undo_stack[-1]
            self._undo_stack[-1] = _CarriageUndoState(
                text=previous.text,
                cursor_position=current.cursor_position,
                tables=previous.tables,
                footnotes=previous.footnotes,
            )
        else:
            self._undo_stack.append(current)

        if clear_redo_stack:
            self._redo_stack = []

    def _restore_carriage_state(self, snapshot):
        # Dictionaries and committed object values are persistent. Future
        # object changes replace a mapping rather than mutating one captured by
        # history, so restoring these references is safe and inexpensive.
        state.tables = snapshot.tables
        state.footnotes = snapshot.footnotes
        self.set_document(
            Document(snapshot.text, cursor_position=snapshot.cursor_position),
            bypass_readonly=True,
        )
        _working_state_changed()

    def undo(self):
        current = self._carriage_state()
        while self._undo_stack:
            snapshot = self._undo_stack.pop()
            if not self._same_content(snapshot, current):
                self._redo_stack.append(current)
                self._restore_carriage_state(snapshot)
                break

    def redo(self):
        if self._redo_stack:
            self.save_to_undo_stack(clear_redo_stack=False)
            snapshot = self._redo_stack.pop()
            self._restore_carriage_state(snapshot)

    # Folded tables and footnote definitions are editor objects, not ordinary
    # text. Keep all character-level Buffer mutations from entering an object
    # or deleting either newline that keeps it on its own source line. Program
    # transformations use set_document()/document directly and are therefore
    # unaffected by these user-edit guards.
    def insert_text(self, data, overwrite=False, move_cursor=True, fire_event=True):
        if _buffer_folded_edit_locked(self, insertion=True):
            return
        return super().insert_text(
            data, overwrite=overwrite, move_cursor=move_cursor, fire_event=fire_event
        )

    def delete_before_cursor(self, count=1):
        start = max(0, self.cursor_position - max(0, count))
        if _folded_edit_range_intersects(self.text, start, self.cursor_position):
            return ""
        return super().delete_before_cursor(count)

    def delete(self, count=1):
        end = min(len(self.text), self.cursor_position + max(0, count))
        if _folded_edit_range_intersects(self.text, self.cursor_position, end):
            return ""
        return super().delete(count)

    def copy_selection(self, _cut=False):
        if _selection_intersects_folded_object(self):
            return ClipboardData("")
        return super().copy_selection(_cut=_cut)

    def cut_selection(self):
        if _selection_intersects_folded_object(self):
            return ClipboardData("")
        return super().cut_selection()

    def paste_clipboard_data(self, data, paste_mode=None, count=1):
        if _buffer_folded_edit_locked(self, insertion=True):
            return
        if paste_mode is None:
            return super().paste_clipboard_data(data, count=count)
        return super().paste_clipboard_data(data, paste_mode=paste_mode, count=count)




def _prose_layout_widths(columns):
    """Return left padding, structural gutter, and right padding.

    The configured prose body stays centered exactly where it did before the
    hanging-gutter display was introduced. On sufficiently wide terminals, up
    to STRUCTURE_GUTTER_WIDTH cells immediately to the left of that prose body
    are borrowed from the existing left-side breathing room. List markers,
    canonical list continuation indentation, and ATX heading markers occupy
    that borrowed area visually; ordinary prose receives display-only padding
    there so every prose body begins at the same screen column.

    One additional content cell remains reserved after the prose body for the
    insertion point at column 80. Narrow terminals gracefully reduce or remove
    the hanging gutter rather than taking space away from prose.
    """
    scrollbar_width = 1 if SCROLLBAR_VISIBLE else 0
    available = max(1, columns - scrollbar_width)
    if available <= WRAP_COLUMN:
        return 0, 0, 0

    prose_left = max(0, (available - WRAP_COLUMN) // 2)
    gutter = min(STRUCTURE_GUTTER_WIDTH, prose_left)
    left = prose_left - gutter
    content_width = gutter + WRAP_COLUMN + 1
    right = max(0, available - left - content_width)
    return left, gutter, right


def _center_padding_widths(columns):
    """Return only the transparent outer padding used by TextArea margins."""
    left, _gutter, right = _prose_layout_widths(columns)
    return left, right


class CenterPaddingMargin(Margin):
    """Transparent dynamic padding used to center the prose column."""

    def __init__(self, side):
        self.side = side

    def get_width(self, get_ui_content):
        try:
            columns = get_app().output.get_size().columns
        except Exception:
            columns = WRAP_COLUMN + 1
        left, right = _center_padding_widths(columns)
        return left if self.side == "left" else right

    def create_margin(self, window_render_info, width, height):
        if width <= 0 or height <= 0:
            return []
        fragments = []
        for row in range(height):
            fragments.append(("class:editor", " " * width))
            if row < height - 1:
                fragments.append(("", "\n"))
        return fragments


def _last_mapped_content_y(yx_to_rowcol, x_min, x_max, y_min, y_max):
    """Return the last rendered source row inside a Window content rectangle."""
    mapped = (
        y
        for y, x in yx_to_rowcol
        if y_min <= y < y_max and x_min <= x < x_max
    )
    return max(mapped, default=y_min)


def _clamp_content_mouse_y(requested_y, y_min, y_max, last_content_y):
    """Clamp a viewport mouse row to the final rendered source row."""
    y = max(y_min, min(y_max - 1, requested_y))
    return min(y, last_content_y)


def _calculate_scrollbar_thumb_geometry(
    track_height,
    viewport_height,
    total_height,
    rendered_top,
    force_bottom=False,
):
    """Return ``(thumb_top, thumb_height)`` in scrollbar-track rows.

    The track excludes optional arrow rows.  ``rendered_top`` and the height
    values are measured in actual soft-wrapped display rows.  Keeping this
    arithmetic in one pure helper makes the two endpoint invariants explicit:

    * at the top, the first thumb row is the first track row;
    * at the bottom, the final thumb row is the final track row.
    """
    track_height = max(0, int(track_height))
    if track_height <= 0:
        return 0, 0

    viewport_height = max(1, int(viewport_height))
    total_height = max(0, int(total_height))
    rendered_top = max(0, int(rendered_top))

    if total_height <= viewport_height:
        return 0, track_height

    # Keep a long-document thumb visible without making it visually dominant.
    min_thumb_height = 2 if track_height >= 2 else 1
    proportional = int(round(track_height * viewport_height / float(total_height)))
    thumb_height = max(min_thumb_height, min(track_height, proportional))

    max_document_top = max(0, total_height - viewport_height)
    max_thumb_top = max(0, track_height - thumb_height)
    if max_thumb_top <= 0:
        return 0, thumb_height

    if force_bottom or rendered_top >= max_document_top:
        return max_thumb_top, thumb_height

    thumb_top = int(round(
        max_thumb_top * min(rendered_top, max_document_top) / float(max_document_top)
    ))
    return max(0, min(max_thumb_top, thumb_top)), thumb_height


class RenderedScrollbarMargin(Margin):
    """Scrollbar whose thumb reflects actual soft-wrapped screen rows.

    prompt_toolkit's stock scrollbar measures logical source lines, so a single
    long paragraph can fill many screen rows while the thumb still appears to
    represent one line. Carriage uses the same cached rendered-row geometry for
    drawing, wheel scrolling, clicking, and dragging.
    """

    def __init__(self, window_getter, display_arrows=True, up_arrow_symbol="^", down_arrow_symbol="v"):
        self.window_getter = window_getter
        self.display_arrows = display_arrows
        self.up_arrow_symbol = up_arrow_symbol
        self.down_arrow_symbol = down_arrow_symbol

    def get_width(self, get_ui_content):
        return 1

    def _force_bottom(self, window, rendered_top, max_document_top):
        """Whether the thumb must be drawn flush with the bottom of its track.

        In manual-scroll mode the viewport, not the insertion cursor, owns the
        scrollbar, so only the rendered viewport position can establish the
        bottom.  In normal editing mode prompt_toolkit keeps the insertion
        cursor visible.  Therefore a cursor at the final source insertion point
        is definitive evidence that Carriage is at the document end; no
        reconstructed source/display mapping is needed.
        """
        if rendered_top >= max_document_top:
            return True
        if getattr(window, "manual_scroll_active", False):
            return False
        try:
            buffer = window.content.buffer
            return buffer.cursor_position == len(buffer.text)
        except (AttributeError, TypeError):
            return False

    def create_margin(self, window_render_info, width, height):
        if width <= 0 or height <= 0:
            return []

        display_arrows = bool(self.display_arrows)
        track_height = height - 2 if display_arrows else height
        if track_height <= 0:
            return []

        window = self.window_getter()
        heights, prefix = window._rendered_height_geometry(
            ui_content=window_render_info.ui_content,
            width=window_render_info.window_width,
        )
        total_height = prefix[-1] if heights and prefix else 0
        viewport_height = max(1, window_render_info.window_height)
        rendered_top = (
            window._absolute_rendered_scroll(heights, prefix)
            if heights and prefix
            else 0
        )
        max_document_top = max(0, total_height - viewport_height)
        force_bottom = self._force_bottom(
            window, rendered_top, max_document_top
        )
        thumb_top, thumb_height = _calculate_scrollbar_thumb_geometry(
            track_height=track_height,
            viewport_height=viewport_height,
            total_height=total_height,
            rendered_top=rendered_top,
            force_bottom=force_bottom,
        )

        result = []
        if display_arrows:
            result.extend([
                ("class:scrollbar.arrow", self.up_arrow_symbol),
                ("class:scrollbar", "\n"),
            ])

        thumb_end = thumb_top + thumb_height
        for row in range(track_height):
            # Use one unambiguous style for every cell in each region.  The
            # previous compound end/start styles were unnecessary and made the
            # final painted thumb cell harder to reason about and test.
            style = (
                "class:scrollbar.button"
                if thumb_top <= row < thumb_end
                else "class:scrollbar.background"
            )
            result.append((style, " "))
            if row < track_height - 1 or display_arrows:
                result.append(("", "\n"))

        if display_arrows:
            result.append(("class:scrollbar.arrow", self.down_arrow_symbol))

        return result


class ScrollableWindow(Window):
    """
    Window subclass that keeps mouse-wheel and scrollbar scrolling independent
    from the editing cursor.

    prompt_toolkit normally keeps the cursor inside the viewport whenever a
    Window is rendered. Its stock wheel-scrolling implementation therefore
    moves the buffer cursor when the viewport would otherwise scroll away from
    it. In a prose editor that is dangerous: simply reading elsewhere in the
    document can silently relocate the insertion point.

    Carriage instead enters a temporary manual-scroll mode for wheel and
    scrollbar interactions. In that mode, ``vertical_scroll`` and
    ``vertical_scroll_2`` describe an absolute rendered-row viewport position,
    independent of the buffer cursor. The cursor itself never moves and is
    hidden until editing/cursor movement resumes. A text or cursor change exits
    manual-scroll mode, at which point prompt_toolkit's normal keep-cursor-
    visible behavior takes over again.

    Tracking rendered rows also keeps scrolling smooth through soft-wrapped
    logical lines, including lines taller than the viewport.
    """

    on_scrollbar_interact = None
    manual_scroll_active = False
    # Up/Down owns a separate cursor-visible viewport mode. prompt_toolkit's
    # stock wrapped-line scroller works in logical source lines and can therefore
    # jump an entire paragraph when a visual-row cursor move crosses the viewport
    # edge. Carriage keeps the keyboard viewport in rendered-row coordinates.
    keyboard_scroll_active = False

    def invalidate_rendered_height_cache(self):
        """Invalidate document geometry while retaining reusable line heights.

        Text edits can alter structural interpretation beyond the edited row
        (for example lazy blockquotes, list runs, or footnote numbering), so
        Carriage deliberately rebuilds the cheap height/prefix arrays after a
        change.  The expensive prompt_toolkit line measurement is retained in a
        dependency-keyed cache and reused only when every width-affecting input
        for that logical row is unchanged.
        """
        self._height_cache_generation = getattr(self, "_height_cache_generation", 0) + 1
        self._height_cache_key = None
        self._height_cache_heights = None
        self._height_cache_prefix = None

    def _height_cache_columns(self):
        """Return terminal columns that can affect continuation-prefix width."""
        try:
            return get_app().output.get_size().columns
        except Exception:
            return None

    def _rendered_height_line_key(self, full_text, row, width, columns):
        """Return all known inputs that can change one logical row's height.

        Styling alone is intentionally absent: color/bold/italic do not change
        terminal cell width.  Structural layout, compact footnote labels, hard-
        break display substitution, source text, viewport width, and terminal
        columns do.  Full-document parsing may therefore change this key for an
        untouched source line, which is how dependent rows are invalidated
        without assuming that an edit affects only one physical line.
        """
        lines = _source_lines(full_text)
        line = lines[row] if 0 <= row < len(lines) else ""
        row_layout = _display_row_layout(full_text, row)
        footnote_spans = tuple(_footnote_display_spans(full_text, row))
        hard_break_span = _hard_break_display_span(full_text, row)
        return (
            line,
            int(width),
            columns,
            row_layout,
            footnote_spans,
            hard_break_span,
        )

    def _rendered_height_geometry(self, ui_content=None, width=None):
        """Return cached ``(heights, prefix)`` for the current soft layout.

        Whole-document geometry is rebuilt after text/layout changes, but line
        heights are reused from the previous rendered geometry whenever their
        complete render-dependency key is unchanged.  This keeps structural
        invalidation conservative while avoiding a prompt_toolkit transformation
        pass for every unaffected line after each keystroke.
        """
        info = self.render_info
        if ui_content is None:
            if info is None:
                return None, None
            ui_content = info.ui_content
        if width is None:
            if info is None or info.window_width <= 0:
                return None, None
            width = info.window_width
        if width <= 0:
            return None, None

        generation = getattr(self, "_height_cache_generation", 0)
        columns = self._height_cache_columns()
        key = (generation, width, columns, ui_content.line_count)
        if (
            getattr(self, "_height_cache_key", None) == key
            and getattr(self, "_height_cache_heights", None) is not None
            and getattr(self, "_height_cache_prefix", None) is not None
        ):
            return self._height_cache_heights, self._height_cache_prefix

        try:
            full_text = self.content.buffer.text
        except (AttributeError, TypeError):
            full_text = text_area.buffer.text

        previous_line_heights = getattr(self, "_height_line_cache", None) or {}
        current_line_heights = {}
        heights = []
        for row in range(ui_content.line_count):
            line_key = self._rendered_height_line_key(
                full_text, row, width, columns
            )
            line_height = current_line_heights.get(line_key)
            if line_height is None:
                line_height = previous_line_heights.get(line_key)
            if line_height is None:
                line_height = max(
                    1,
                    ui_content.get_height_for_line(
                        row, width, self.get_line_prefix
                    ),
                )
            current_line_heights[line_key] = line_height
            heights.append(line_height)

        prefix = [0]
        total = 0
        for line_height in heights:
            total += line_height
            prefix.append(total)

        # Retain only keys used by the current geometry.  This gives edits one
        # generation of reuse without accumulating stale source lines forever.
        self._height_line_cache = current_line_heights
        self._height_cache_key = key
        self._height_cache_heights = heights
        self._height_cache_prefix = prefix
        return heights, prefix

    def _absolute_rendered_scroll(self, heights=None, prefix=None):
        """Return the current viewport top as an absolute rendered-row index."""
        if heights is None or prefix is None:
            cached_heights, cached_prefix = self._rendered_height_geometry()
            heights = cached_heights if heights is None else heights
            prefix = cached_prefix if prefix is None else prefix
        if not heights:
            return 0
        if prefix is None or len(prefix) != len(heights) + 1:
            prefix = [0]
            for line_height in heights:
                prefix.append(prefix[-1] + line_height)
        row = max(0, min(len(heights) - 1, self.vertical_scroll))
        inside = max(0, min(heights[row] - 1, self.vertical_scroll_2))
        return prefix[row] + inside

    def _set_rendered_scroll(
        self, rendered_row, heights=None, prefix=None, window_height=None
    ):
        """Set a cursor-independent viewport top from a rendered-row index."""
        # Mouse-wheel/scrollbar viewport ownership supersedes keyboard vertical
        # navigation. Manual mode hides the caret until editing resumes.
        self.keyboard_scroll_active = False
        # Any explicit viewport scroll cancels a section-navigation top anchor.
        # Otherwise ending a manual scroll while the caret remained on the
        # heading could unexpectedly snap the heading back to the top.
        self._section_top_anchor_row = None
        info = self.render_info
        if heights is None or prefix is None:
            cached_heights, cached_prefix = self._rendered_height_geometry()
            heights = cached_heights if heights is None else heights
            prefix = cached_prefix if prefix is None else prefix
        if not heights:
            self.vertical_scroll = 0
            self.vertical_scroll_2 = 0
            self.manual_scroll_active = False
            return
        if prefix is None or len(prefix) != len(heights) + 1:
            prefix = [0]
            for line_height in heights:
                prefix.append(prefix[-1] + line_height)

        if window_height is None:
            window_height = info.window_height if info is not None else 1
        current = self._absolute_rendered_scroll(heights, prefix)
        total_height = prefix[-1]
        max_top = max(0, total_height - max(1, window_height))
        target = max(0, min(max_top, int(rendered_row)))

        # prefix is monotonically increasing because every logical line has a
        # rendered height of at least one row. Binary search maps an absolute
        # rendered row back to its logical line without scanning the document.
        target_row = max(0, min(len(heights) - 1, bisect_right(prefix, target) - 1))
        wrapped_offset = target - prefix[target_row]

        self.vertical_scroll = target_row
        self.vertical_scroll_2 = wrapped_offset
        # Do not hide the caret merely because the user spun the wheel at an
        # already-reached edge or in a document shorter than the viewport.
        # Once manual browsing is active, however, keep it active at the edge
        # until the user resumes editing/cursor movement.
        self.manual_scroll_active = self.manual_scroll_active or target != current

    def end_manual_scroll(self):
        """Return viewport ownership to prompt_toolkit without moving the cursor."""
        self.manual_scroll_active = False

    def _set_keyboard_rendered_scroll(
        self, rendered_row, heights, prefix, window_height
    ):
        """Keep a keyboard-driven viewport at one rendered-row position.

        Unlike manual wheel/scrollbar browsing, the insertion cursor remains
        visible. The explicit top survives repaints until a nonvertical cursor
        move or an edit returns scrolling to prompt_toolkit.
        """
        if not heights or prefix is None or len(prefix) != len(heights) + 1:
            self.keyboard_scroll_active = False
            return

        total_height = prefix[-1]
        max_top = max(0, total_height - max(1, int(window_height)))
        target = max(0, min(max_top, int(rendered_row)))
        target_row = max(
            0, min(len(heights) - 1, bisect_right(prefix, target) - 1)
        )
        self.vertical_scroll = target_row
        self.vertical_scroll_2 = target - prefix[target_row]
        self.keyboard_scroll_active = True

    def _scroll(self, ui_content, width, height):
        """Honor rendered-row viewport modes and section-heading alignment."""
        if not self.manual_scroll_active and not self.keyboard_scroll_active:
            anchor = getattr(self, "_section_top_anchor_row", None)
            if (
                anchor is not None
                and 0 <= anchor < ui_content.line_count
                and ui_content.cursor_position.y == anchor
            ):
                # Section navigation is deliberately stronger than
                # prompt_toolkit's normal keep-cursor-visible behavior: the
                # target ATX heading belongs on the first visible editor row,
                # even near EOF where that leaves blank rows below it. Keep
                # the anchor active until some other cursor/edit/scroll action
                # cancels it, otherwise a later repaint would clamp the view
                # back upward to keep the bottom of the document filled.
                self.horizontal_scroll = 0
                self.vertical_scroll = anchor
                self.vertical_scroll_2 = 0
                return
            return super()._scroll(ui_content, width, height)

        # Manual browsing and keyboard vertical navigation both preserve an
        # explicit rendered-row viewport top. Only manual browsing hides the
        # cursor; keyboard mode keeps the caret visible.
        self.horizontal_scroll = 0
        heights, prefix = self._rendered_height_geometry(
            ui_content=ui_content, width=width
        )
        if not heights:
            self.vertical_scroll = 0
            self.vertical_scroll_2 = 0
            return

        # Re-map the stored logical-row/inside-line position to a valid absolute
        # rendered-row position. Width/terminal geometry is part of the cache
        # key, so resizing transparently rebuilds the soft-wrap measurements.
        row = max(0, min(len(heights) - 1, self.vertical_scroll))
        requested = prefix[row] + max(0, self.vertical_scroll_2)
        total_height = prefix[-1]
        max_top = max(0, total_height - max(1, height))
        target = max(0, min(max_top, requested))

        logical_row = max(
            0, min(len(heights) - 1, bisect_right(prefix, target) - 1)
        )
        self.vertical_scroll = logical_row
        self.vertical_scroll_2 = target - prefix[logical_row]

    def _scroll_up(self):
        heights, prefix = self._rendered_height_geometry()
        info = self.render_info
        if not heights or info is None:
            return
        current = self._absolute_rendered_scroll(heights, prefix)
        self._set_rendered_scroll(
            current - 1, heights=heights, prefix=prefix, window_height=info.window_height
        )

    def _scroll_down(self):
        heights, prefix = self._rendered_height_geometry()
        info = self.render_info
        if not heights or info is None:
            return
        current = self._absolute_rendered_scroll(heights, prefix)
        self._set_rendered_scroll(
            current + 1, heights=heights, prefix=prefix, window_height=info.window_height
        )

    def _write_to_screen_at_index(
        self, screen, mouse_handlers, write_position, parent_style, erase_bg
    ):
        super()._write_to_screen_at_index(
            screen, mouse_handlers, write_position, parent_style, erase_bg
        )

        # prompt_toolkit 3.0.52 shortens a Window's content mouse-handler range
        # by the *left* margin width as well as the right margin width. With
        # Carriage's centered prose margin, that made the final ~left-margin
        # number of text columns unclickable. Reinstall the content handler over
        # the actual rendered content rectangle using WindowRenderInfo's exact
        # coordinates and source/display map.
        info = self.render_info
        if info is not None:
            yx_to_rowcol = {v: k for k, v in info._rowcol_to_yx.items()}
            content_x_min = info._x_offset
            content_x_max = info._x_offset + info.window_width
            content_y_min = write_position.ypos
            content_y_max = write_position.ypos + write_position.height

            last_content_y = _last_mapped_content_y(
                yx_to_rowcol,
                content_x_min,
                content_x_max,
                content_y_min,
                content_y_max,
            )

            def click_viewport_snapshot():
                """Capture the exact rendered top used by this mouse map."""
                heights, prefix = self._rendered_height_geometry(
                    ui_content=info.ui_content, width=info.window_width
                )
                if not heights or prefix is None:
                    return None
                return (
                    self._absolute_rendered_scroll(heights, prefix),
                    heights,
                    prefix,
                    max(1, info.window_height),
                )

            def restore_click_viewport(snapshot):
                """Keep a positioning click from shifting the visible text."""
                if snapshot is None:
                    self.end_manual_scroll()
                    return
                rendered_top, heights, prefix, window_height = snapshot
                # Moving the buffer cursor fires _resume_editor_view(), which
                # intentionally ends wheel/manual scrolling. Reinstall the same
                # rendered top afterward in cursor-visible mode. A subsequent
                # nonvertical cursor move or edit releases this ownership in the
                # normal way.
                self.end_manual_scroll()
                self._set_keyboard_rendered_scroll(
                    rendered_top, heights, prefix, window_height
                )

            def content_handler(mouse_event):
                y = _clamp_content_mouse_y(
                    mouse_event.position.y,
                    content_y_min,
                    content_y_max,
                    last_content_y,
                )
                x = mouse_event.position.x

                # Blank rows below EOF are part of the editor viewport, not a
                # dead mouse zone. The y coordinate above is clamped to the
                # final rendered content row before horizontal source lookup.

                # A positioning click must use the render map that was actually
                # clicked and keep that same viewport afterward. Ending manual
                # wheel scrolling *before* the cursor move lets prompt_toolkit
                # re-clamp/recenter the window around the new caret, which makes
                # the text jump a few rendered rows. Snapshot the current top and
                # restore it after BufferControl has placed the caret instead.
                #
                # When Mouse Down begins while wheel/manual scrolling owns the
                # viewport, retain that same snapshot for the complete drag
                # gesture. Cursor changes during Mouse Move fire the ordinary
                # cursor callback, which otherwise releases Carriage's explicit
                # rendered-row top and lets prompt_toolkit snap the view while a
                # selection is being extended. A normal drag that did not begin
                # from a manually scrolled viewport keeps prompt_toolkit's usual
                # behavior, including edge autoscroll.
                if mouse_event.event_type == MouseEventType.MOUSE_DOWN:
                    click_snapshot = click_viewport_snapshot()
                    self._carriage_drag_viewport_snapshot = (
                        click_snapshot if self.manual_scroll_active else None
                    )
                elif (
                    mouse_event.event_type == MouseEventType.MOUSE_MOVE
                    and mouse_event.button != MouseButton.NONE
                ):
                    click_snapshot = getattr(
                        self, "_carriage_drag_viewport_snapshot", None
                    )
                elif mouse_event.event_type == MouseEventType.MOUSE_UP:
                    click_snapshot = getattr(
                        self, "_carriage_drag_viewport_snapshot", None
                    )
                else:
                    click_snapshot = None

                def finish_mouse_event(result):
                    if click_snapshot is not None:
                        restore_click_viewport(click_snapshot)
                    elif mouse_event.event_type == MouseEventType.MOUSE_DOWN:
                        # v1.176 behavior: even an ordinary positioning click
                        # keeps the viewport used by the click itself stable.
                        restore_click_viewport(click_viewport_snapshot())
                    if mouse_event.event_type == MouseEventType.MOUSE_UP:
                        self._carriage_drag_viewport_snapshot = None
                    return result

                # Search left from blank cells to the nearest rendered source
                # position, matching prompt_toolkit's normal click behavior.
                while x >= content_x_min:
                    rowcol = yx_to_rowcol.get((y, x))
                    if rowcol is not None:
                        row, col = rowcol
                        result = self.content.mouse_handler(
                            MouseEvent(
                                position=Point(x=col, y=row),
                                event_type=mouse_event.event_type,
                                button=mouse_event.button,
                                modifiers=mouse_event.modifiers,
                            )
                        )
                        if result == NotImplemented:
                            result = self._mouse_handler(mouse_event)
                        return finish_mouse_event(result)
                    x -= 1

                result = self._mouse_handler(mouse_event)
                return finish_mouse_event(result)

            mouse_handlers.set_mouse_handler_for_range(
                x_min=content_x_min,
                x_max=content_x_max,
                y_min=content_y_min,
                y_max=content_y_max,
                handler=content_handler,
            )

            def gutter_boundary_target(screen_y, end=False):
                """Map an outer-margin click to this displayed row's boundary."""
                y = _clamp_content_mouse_y(
                    screen_y,
                    content_y_min,
                    content_y_max,
                    last_content_y,
                )

                # Find any processed display column actually painted on this
                # screen row. Its logical row plus visual-wrap number are enough
                # to reuse the exact Home/End boundary resolver.
                painted = [
                    (x, row, col)
                    for (row, col), (mapped_y, x) in info._rowcol_to_yx.items()
                    if mapped_y == y
                    and content_x_min <= x < content_x_max
                ]
                if painted:
                    _x, row, display_col = min(painted)
                    positions = _visual_display_positions(row, info)
                    if positions:
                        display_col = max(0, min(display_col, len(positions) - 1))
                        wrap_row = positions[display_col][0]
                        return _visual_row_boundary_source_index(
                            row, wrap_row, end=end, info=info
                        )

                # Empty lines may have no painted input cell. WindowRenderInfo
                # still records which logical line owns every visible row.
                visible_y = y - info._y_offset
                rowcol = info.visible_line_to_row_col.get(visible_y)
                if rowcol is not None:
                    row, display_col = rowcol
                    positions = _visual_display_positions(row, info)
                    wrap_row = 0
                    if positions:
                        display_col = max(0, min(display_col, len(positions) - 1))
                        wrap_row = positions[display_col][0]
                    return _visual_row_boundary_source_index(
                        row, wrap_row, end=end, info=info
                    )
                return None

            def make_gutter_handler(end=False):
                def gutter_handler(mouse_event):
                    if mouse_event.event_type == MouseEventType.SCROLL_UP:
                        self._scroll_up()
                        return None
                    if mouse_event.event_type == MouseEventType.SCROLL_DOWN:
                        self._scroll_down()
                        return None
                    if mouse_event.event_type != MouseEventType.MOUSE_DOWN:
                        # A gutter click is a positioning gesture, not a
                        # double/triple-click or drag-selection surface.
                        return None

                    target = gutter_boundary_target(mouse_event.position.y, end=end)
                    if target is None:
                        return None

                    click_snapshot = click_viewport_snapshot()
                    app = get_app()
                    if app.layout.current_control is not self.content:
                        app.layout.current_control = self.content
                    buffer = self.content.buffer
                    buffer.exit_selection()
                    buffer.cursor_position = max(0, min(len(buffer.text), target))
                    restore_click_viewport(click_snapshot)
                    reset_clicks = getattr(
                        self.content, "_reset_carriage_click_sequence", None
                    )
                    if reset_clicks is not None:
                        reset_clicks()
                    app.invalidate()
                    return None

                return gutter_handler

            left_padding_width = max(0, content_x_min - write_position.xpos)
            if left_padding_width > 0:
                mouse_handlers.set_mouse_handler_for_range(
                    x_min=write_position.xpos,
                    x_max=content_x_min,
                    y_min=content_y_min,
                    y_max=content_y_max,
                    handler=make_gutter_handler(end=False),
                )

            # The first right margin is Carriage's transparent centering
            # padding. The optional final right margin is the scrollbar and is
            # deliberately excluded from gutter-click behavior.
            right_padding_width = 0
            if self.right_margins:
                right_padding_width = self._get_margin_width(self.right_margins[0])
            if right_padding_width > 0:
                mouse_handlers.set_mouse_handler_for_range(
                    x_min=content_x_max,
                    x_max=content_x_max + right_padding_width,
                    y_min=content_y_min,
                    y_max=content_y_max,
                    handler=make_gutter_handler(end=True),
                )

        if (
            self.on_scrollbar_interact is None
            or not self.right_margins
            or not isinstance(self.right_margins[-1], RenderedScrollbarMargin)
        ):
            return

        # The prose-centering spacer is also a right margin, but only an actual
        # RenderedScrollbarMargin owns scrollbar interaction. When the scrollbar
        # scrollbar is disabled, the right centering margin remains a clickable prose
        # gutter rather than silently behaving like a hidden scrollbar.
        scrollbar_width = self._get_margin_width(self.right_margins[-1])
        if scrollbar_width <= 0:
            return

        x_min = write_position.xpos + write_position.width - scrollbar_width
        x_max = write_position.xpos + write_position.width
        y_min = write_position.ypos
        height = write_position.height
        on_interact = self.on_scrollbar_interact

        def handler(mouse_event):
            if mouse_event.event_type == MouseEventType.MOUSE_DOWN:
                on_interact(mouse_event.position.y - y_min, height)
                return None
            if (
                mouse_event.event_type == MouseEventType.MOUSE_MOVE
                and mouse_event.button != MouseButton.NONE
            ):
                on_interact(mouse_event.position.y - y_min, height)
                return None
            if mouse_event.event_type == MouseEventType.SCROLL_UP:
                self._scroll_up()
                return None
            if mouse_event.event_type == MouseEventType.SCROLL_DOWN:
                self._scroll_down()
                return None
            return NotImplemented

        mouse_handlers.set_mouse_handler_for_range(
            x_min=x_min,
            x_max=x_max,
            y_min=y_min,
            y_max=y_min + height,
            handler=handler,
        )


SCROLLBAR_STEP_ROWS = 3


def _scrollbar_rendered_geometry():
    """Return cached rendered heights/prefix sums from the last layout."""
    info = text_area.window.render_info
    if info is None:
        return None, None
    return text_area.window._rendered_height_geometry(
        ui_content=info.ui_content, width=info.window_width
    )


def _move_to_rendered_position(rendered_row):
    """Scroll the viewport to the nearest absolute rendered-row position."""
    info = text_area.window.render_info
    heights, prefix = _scrollbar_rendered_geometry()
    if info is None or not heights:
        return

    # The scrollbar controls the viewport, not the editing caret. Manual-scroll
    # mode can start within any soft-wrapped logical line; there is no need to
    # relocate the buffer cursor just to satisfy prompt_toolkit's normal
    # keep-cursor-visible scrolling rules.
    text_area.window._set_rendered_scroll(
        rendered_row,
        heights=heights,
        prefix=prefix,
        window_height=info.window_height,
    )


def _on_scrollbar_interact(row_in_window, window_height):
    # TextArea's scrollbar has arrow rows at the top and bottom; clicks there
    # move by a few rendered rows. The track maps proportionally across the
    # document's rendered height, so tall soft-wrapped lines get proper weight.
    heights, prefix = _scrollbar_rendered_geometry()
    if not heights:
        return

    info = text_area.window.render_info
    total_height = prefix[-1]
    if row_in_window <= 0:
        # Arrow clicks should always cause visible movement when movement is
        # possible. Mapping an absolute rendered-row target back onto a short
        # wrapped logical line can collapse to that line's start and become a
        # no-op, so use the window's incremental scrolling path for arrows.
        for _ in range(SCROLLBAR_STEP_ROWS):
            before = (
                text_area.window.vertical_scroll,
                text_area.window.vertical_scroll_2,
            )
            text_area.window._scroll_up()
            after = (
                text_area.window.vertical_scroll,
                text_area.window.vertical_scroll_2,
            )
            if after == before:
                break
        return
    if row_in_window >= window_height - 1:
        for _ in range(SCROLLBAR_STEP_ROWS):
            before = (
                text_area.window.vertical_scroll,
                text_area.window.vertical_scroll_2,
            )
            text_area.window._scroll_down()
            after = (
                text_area.window.vertical_scroll,
                text_area.window.vertical_scroll_2,
            )
            if after == before:
                break
        return

    body_height = max(1, window_height - 2)
    fraction = (row_in_window - 1) / max(1, body_height - 1)
    max_top = max(0, total_height - (info.window_height if info else 1))
    _move_to_rendered_position(round(fraction * max_top))


# ---------------------------------------------------------------------------
# Lightweight Markdown highlighting
# ---------------------------------------------------------------------------

# Highlighting is deliberately narrower than Carriage's editing logic. It is
# visual only: ATX headings and inline bold/italic emphasis get styled, while
# the underlying buffer remains untouched. Fenced code blocks are left
# unhighlighted so prose markers inside code do not masquerade as Markdown.
_HIGHLIGHT_ATX_RE = re.compile(r"^#{1,6}(?!#)(?=.*\S)")
_HIGHLIGHT_FENCE_RE = re.compile(r"^\s{0,3}(`{3,}|~{3,})")

# Inline emphasis highlighting uses the same conservative delimiter/flanking
# scanner as Carriage's emphasis-editing logic. Keeping one bounded scanner
# avoids catastrophic regex backtracking and prevents the display layer from
# inventing a second, subtly different emphasis grammar.

_HIGHLIGHT_LIST_ITEM_RE = re.compile(r"^\s{0,3}(?:[-*+]|\d+\.)\s+")
_HIGHLIGHT_THEMATIC_BREAK_RE = re.compile(
    r"^\s{0,3}(?:(?:\*[ \t]*){3,}|(?:_[ \t]*){3,}|(?:-[ \t]*){3,})$"
)


def _highlight_fenced_lines(lines):
    """Return line indexes belonging to fenced code blocks."""
    protected = set()
    fence_char = None
    fence_len = 0

    for row, line in enumerate(lines):
        if fence_char is None:
            match = _HIGHLIGHT_FENCE_RE.match(line)
            if match:
                marker = match.group(1)
                fence_char = marker[0]
                fence_len = len(marker)
                protected.add(row)
        else:
            protected.add(row)
            if re.match(
                rf"^\s{{0,3}}{re.escape(fence_char)}{{{fence_len},}}\s*$",
                line,
            ):
                fence_char = None
                fence_len = 0

    return protected


def _highlight_emphasis_spans(text):
    """Return non-overlapping emphasis spans as ``(start, end, style)``.

    The shared emphasis scanner can return nested spans. prompt_toolkit's lexer
    consumes one flat fragment stream, so highlight the outermost span and skip
    nested overlaps, matching the old lexer's non-overlapping presentation while
    handling valid nested delimiters deterministically.
    """
    candidates = _emphasis_spans_in_range(text, 0, len(text))
    if not candidates:
        return ()

    styled = []
    occupied_end = -1
    for open_start, _open_end, _close_start, close_end, _marker, count in candidates:
        if open_start < occupied_end:
            continue
        style = {
            3: "class:markdown.bold-italic",
            2: "class:markdown.bold",
            1: "class:markdown.italic",
        }.get(count)
        if style is None:
            continue
        styled.append((open_start, close_end, style))
        occupied_end = close_end
    return tuple(styled)



def _highlight_inline_markdown_block(block_lines):
    """Highlight emphasis across physical wraps inside one prose block.

    prompt_toolkit lexers return fragments one physical line at a time, but
    Markdown emphasis may legitimately span the newlines Carriage inserts when
    hard-wrapping prose. Join one logical prose block for matching, then project
    the resulting style spans back onto the original physical lines.
    """
    if not block_lines:
        return []

    combined = "\n".join(block_lines)
    spans = list(_highlight_emphasis_spans(combined))

    rendered = []
    offset = 0
    span_index = 0

    for line in block_lines:
        line_start = offset
        line_end = line_start + len(line)

        if not line:
            rendered.append([("", "")])
            offset = line_end + 1
            continue

        # Discard matches that ended before this physical line. A match that
        # spans a hard wrap remains active and is projected onto each line it
        # intersects.
        while span_index < len(spans) and spans[span_index][1] <= line_start:
            span_index += 1

        fragments = []
        cursor = 0
        scan_index = span_index

        while scan_index < len(spans):
            start, end, style_name = spans[scan_index]
            if start >= line_end:
                break

            local_start = max(start, line_start) - line_start
            local_end = min(end, line_end) - line_start

            if local_start > cursor:
                fragments.append(("", line[cursor:local_start]))

            if local_end > local_start:
                fragment_text = line[local_start:local_end]
                # The old character-style map naturally coalesced adjacent
                # matches with the same style. Preserve that exact fragment
                # behavior without allocating one style entry per character.
                if fragments and fragments[-1][0] == style_name:
                    fragments[-1] = (
                        style_name,
                        fragments[-1][1] + fragment_text,
                    )
                else:
                    fragments.append((style_name, fragment_text))
                cursor = local_end

            scan_index += 1

        if cursor < len(line):
            fragment_text = line[cursor:]
            if fragments and fragments[-1][0] == "":
                fragments[-1] = ("", fragments[-1][1] + fragment_text)
            else:
                fragments.append(("", fragment_text))

        rendered.append(fragments or [("", line)])
        offset = line_end + 1

    return rendered

def _highlight_special_line(line, row, fenced_lines):
    """Return fixed fragments for structural lines, or None for prose."""
    if row in fenced_lines:
        return [("", line)]
    if TABLE_PLACEHOLDER_RE.match(line):
        return [("class:markdown.table-ref", line)]
    if FOOTNOTE_PLACEHOLDER_RE.match(line):
        return [("class:markdown.footnote-ref", line)]
    if _HIGHLIGHT_ATX_RE.match(line):
        return [("class:markdown.heading", line)]
    if not line.strip() or _HIGHLIGHT_THEMATIC_BREAK_RE.match(line):
        return [("", line)]
    return None


class ProseMarkdownLexer(Lexer):
    """Minimal, non-destructive highlighting for prose-oriented Markdown."""

    def lex_document(self, document):
        lines = document.lines
        fenced_lines = _highlight_fenced_lines(lines)
        rendered = [None] * len(lines)
        row = 0

        while row < len(lines):
            fixed = _highlight_special_line(lines[row], row, fenced_lines)
            if fixed is not None:
                rendered[row] = fixed
                row += 1
                continue

            start = row
            row += 1

            # A hard-wrapped paragraph is one highlighting block. A list item
            # and its continuation lines are also one block, but the next list
            # marker starts a new block so unmatched emphasis cannot leak from
            # one item into another.
            while row < len(lines):
                if _highlight_special_line(lines[row], row, fenced_lines) is not None:
                    break
                if _HIGHLIGHT_LIST_ITEM_RE.match(lines[row]):
                    break
                row += 1

            block_fragments = _highlight_inline_markdown_block(lines[start:row])
            for index, fragments in enumerate(block_fragments, start=start):
                rendered[index] = fragments

        def get_line(lineno):
            if lineno < 0 or lineno >= len(lines):
                return []
            return rendered[lineno] or [("", lines[lineno])]

        return get_line


@lru_cache(maxsize=8)
def _footnote_number_map(full_text):
    """Return display numbers by first reference order for defined notes only."""
    numbers = {}
    next_number = 1
    lines = full_text.split("\n")
    blocks = _analyze_document_layout(full_text, WRAP_COLUMN)

    defined = set()
    for block in blocks:
        if block.kind == "footnote-placeholder" and block.source_lines:
            match = FOOTNOTE_PLACEHOLDER_RE.match(block.source_lines[0])
            if match:
                defined.add(match.group(1))
        elif block.kind == "reference-definition" and block.source_lines:
            match = _FOOTNOTE_DEFINITION_RE.match(block.source_lines[0])
            if match:
                defined.add(match.group(1).strip())

    skip_kinds = {
        "front-matter",
        "code",
        "block-html",
        "table",
        "reference-definition",
        "footnote-placeholder",
        "opaque-extension",
    }
    for block in blocks:
        if block.kind in skip_kinds:
            continue
        for row in range(block.start, block.end):
            if not (0 <= row < len(lines)):
                continue
            for _start, _end, identifier in _footnote_references_on_row(full_text, row):
                if identifier in defined and identifier not in numbers:
                    numbers[identifier] = next_number
                    next_number += 1
    return numbers


def _footnote_display_spans(full_text, row):
    """Return source spans replaced by compact footnote UI on one row."""
    lines = _source_lines(full_text)
    if not (0 <= row < len(lines)):
        return []
    line = lines[row]
    numbers = _footnote_number_map(full_text)

    placeholder = FOOTNOTE_PLACEHOLDER_RE.match(line)
    if placeholder:
        identifier = placeholder.group(1)
        number = numbers.get(identifier)
        label = f"[[Footnote {number}]]" if number is not None else "[[Footnote ?]]"
        return [(0, len(line), label, identifier, True)]

    # Do not reinterpret literal source inside block-level carve-outs.  The
    # owning block is already projected into the cached row map, so this stays
    # O(1) even when prompt_toolkit transforms every row during geometry rebuild.
    block_kind = _display_row_layout(full_text, row).block_kind
    if block_kind in {
        "front-matter",
        "code",
        "block-html",
        "table",
        "reference-definition",
        "footnote-placeholder",
        "opaque-extension",
    }:
        return []

    spans = []
    for start, end, identifier in _footnote_references_on_row(full_text, row):
        number = numbers.get(identifier)
        if identifier and number is not None:
            spans.append((start, end, f"[{number}]", identifier, False))
    return spans


def _strip_blockquote_container_prefixes(line):
    """Return content after any explicit nested blockquote markers."""
    content = line
    while True:
        match = _BLOCKQUOTE_LINE_RE.match(content)
        if match is None:
            return content
        content = match.group(1)


@lru_cache(maxsize=8)
def _footnote_content_row_kinds(full_text):
    """Return display-only text/code classification for complex footnote rows.

    A single forward pass replaces the old per-row backward walk. Blank rows do
    not themselves carry a kind, but they keep an indented footnote continuation
    open so a later continuation row is still classified correctly.
    """
    lines = _source_lines(full_text)
    result = [None] * len(lines)
    active = False

    for row, line in enumerate(lines):
        if _FOOTNOTE_DEFINITION_RE.match(line):
            result[row] = "text"
            active = True
            continue

        if not active:
            continue

        if not line.strip():
            continue

        if line.startswith("\t"):
            result[row] = "text"
            continue

        spaces = len(line) - len(line.lstrip(" "))
        if spaces >= 8:
            result[row] = "code"
            continue
        if spaces >= 4:
            result[row] = "text"
            continue

        active = False

    return tuple(result)


def _footnote_content_row_kind(full_text, row):
    """Return ``text``/``code`` for a visible complex footnote row, or None."""
    kinds = _footnote_content_row_kinds(full_text)
    if 0 <= row < len(kinds):
        return kinds[row]
    return None


def _hard_break_display_span(full_text, row):
    """Return the display-only marker for a real original-Markdown hard break.

    Two or more trailing spaces are a hard break only in prose-bearing source.
    Spaces inside a multiline inline-code span, block code, raw HTML, tables,
    headings, and reference definitions are literal and never receive the
    marker. Nested blockquotes, nested/complex lists, and complex footnotes are
    included when the physical row itself is prose rather than contained code.
    """
    if not HARD_BREAK_MARKER_VISIBLE:
        return None

    lines = _source_lines(full_text)
    if not (0 <= row < len(lines)):
        return None

    line = lines[row]
    if not line.strip() or _hard_break_marker(line) is None:
        return None

    # If the final trailing space is inside an inline code span that crosses a
    # physical line boundary, it is literal code whitespace, not break syntax.
    offsets = _source_line_offsets(full_text)
    final_space = offsets[row] + len(line) - 1
    if _range_contains(_inline_code_span_ranges(full_text), final_space):
        return None

    block_kind = _display_row_layout(full_text, row).block_kind

    if block_kind in {"prose", "list", "list-run", "blockquote"}:
        pass
    elif block_kind == "complex-blockquote":
        inner = _strip_blockquote_container_prefixes(line)
        if _is_indented_code(inner):
            return None
    elif block_kind == "complex-list":
        # Four spaces are ordinary list continuation indentation. Eight or more
        # spaces (or a tab) are the original-Markdown code-block level within a
        # top-level list item.
        if line.startswith("\t"):
            return None
        leading = len(line) - len(line.lstrip(" "))
        if leading >= 8:
            return None
    elif block_kind == "reference-definition":
        # Link reference definitions are opaque. A complex footnote definition
        # uses the same leading syntax, but its prose still benefits from the
        # hard-break indicator.
        if _footnote_content_row_kind(full_text, row) != "text":
            return None
    elif block_kind == "code":
        # A four-space row may actually be a continuation of a complex folded-
        # out footnote. Reclassify only when we can prove that ownership.
        if _footnote_content_row_kind(full_text, row) != "text":
            return None
    else:
        return None

    start = len(line) - 1
    return start, len(line), HARD_BREAK_DISPLAY_CHAR


@lru_cache(maxsize=4096)
def _dash_standin_glue_positions(line, prefix_width, body_width):
    """Return source-space positions that should not be soft-wrap breakpoints.

    Writers commonly draft an em dash as either ``word---word`` or
    ``word -- word``.  The unspaced spelling is already one ordinary wrap token;
    the spaced spelling would normally expose two whitespace breakpoints and can
    strand ``--`` at a visual line edge.  Treat the whole ``word -- word`` group
    as one visual prose unit when that group can fit on a line by gluing only the
    whitespace surrounding a run of two or more hyphens.

    The returned positions refer to the original source line.  Nothing is
    inserted into or removed from the Markdown source, and groups wider than the
    available prose width deliberately fall back to ordinary whitespace wrapping.
    """
    prefix_width = max(0, min(int(prefix_width or 0), len(line)))
    body_width = max(1, int(body_width or 1))
    body = line[prefix_width:]
    glued = set()

    # A dash stand-in must be a punctuation token between two non-whitespace
    # tokens.  Two or more hyphens covers the common spaced ``--`` spelling as
    # well as writers who use ``---`` with spaces.  A single hyphen remains an
    # ordinary Markdown/list punctuation character.
    for match in _SPACED_DASH_STANDIN_RE.finditer(body):
        group = match.group(0)
        if _display_text_width(group) > body_width:
            continue
        for name in ("gap1", "gap2"):
            start, end = match.span(name)
            glued.update(prefix_width + pos for pos in range(start, end))

    return frozenset(glued)


class ProseLayoutProcessor(Processor):
    """Render Carriage's hanging gutter and configured-width soft wrapping.

    Source lines remain authoritative and are never changed by this processor.
    For a physical line wider than its prose budget, display-only padding is
    inserted at word boundaries so prompt_toolkit wraps it cleanly inside the
    configured writing area. Structural Markdown prefixes use metadata from the
    shared block analysis and hang into the left gutter.
    """

    def apply_transformation(self, ti):
        gutter = max(0, min(STRUCTURE_GUTTER_WIDTH, ti.width - (WRAP_COLUMN + 1)))
        row_layout = _display_row_layout(ti.document.text, ti.lineno)
        prefix_width = row_layout.structural_prefix_width
        quote_depth = row_layout.blockquote_depth
        quote_marker = _blockquote_gutter_text(quote_depth, gutter)
        if prefix_width > gutter:
            prefix_width = 0

        quote_marker_width = _display_text_width(quote_marker)
        padding = max(0, gutter - prefix_width)

        fragments = explode_text_fragments(ti.fragments)
        source_length = len(fragments)

        spans = _footnote_display_spans(ti.document.text, ti.lineno)
        span_by_start = {span[0]: span for span in spans}
        hard_break_span = _hard_break_display_span(ti.document.text, ti.lineno)
        units = []
        source_pos = 0
        while source_pos < source_length:
            if hard_break_span is not None and source_pos == hard_break_span[0]:
                start, end, display_text = hard_break_span
                units.append(("class:markdown.hard-break", display_text, start, end))
                source_pos = end
                continue
            span = span_by_start.get(source_pos)
            if span is not None:
                start, end, display_text, _identifier, _placeholder = span
                units.append(("class:markdown.footnote-ref", display_text, start, end))
                source_pos = end
                continue
            style, char = fragments[source_pos][0], fragments[source_pos][1]
            if quote_depth > 0 and source_pos < prefix_width and char == ">":
                style = "class:markdown.blockquote-gutter"
            units.append((style, char, source_pos, source_pos + 1))
            source_pos += 1

        result = []
        source_to_display_map = {}
        display_to_source_map = {}
        display_pos = 0

        # The first rendered row receives the same canonical quote gutter as
        # every soft-wrap continuation. Explicit source markers are replaced by
        # a display-only marker unit below; lazy continuation rows synthesize the
        # marker entirely inside the gutter and leave source column 0 untouched.
        if quote_depth > 0 and prefix_width == 0 and quote_marker:
            quote_padding = max(0, gutter - quote_marker_width)
            for _ in range(quote_padding):
                result.append(("", " "))
                display_to_source_map[display_pos] = 0
                display_pos += 1
            result.append(("class:markdown.blockquote-gutter", quote_marker))
            for offset in range(len(quote_marker)):
                display_to_source_map[display_pos + offset] = 0
            display_pos += len(quote_marker)
        else:
            for _ in range(padding):
                result.append(("", " "))
                display_to_source_map[display_pos] = 0
                display_pos += 1

        body_width = max(1, min(WRAP_COLUMN, ti.width - gutter - 1))
        source_line = ti.document.lines[ti.lineno]
        dash_glue_positions = _dash_standin_glue_positions(
            source_line, prefix_width, body_width
        )
        measured_parts = []
        for unit_style, text, src_start, _src_end in units:
            if src_start >= prefix_width:
                measured_parts.append(
                    "" if unit_style == "class:markdown.hard-break" else text
                )
        measured_body = _wrap_measure_text("".join(measured_parts))
        fallback_wrap = _display_text_width(measured_body) > body_width

        def append_display_padding(count, src_anchor):
            nonlocal display_pos
            for _ in range(max(0, count)):
                result.append(("", " "))
                display_to_source_map[display_pos] = src_anchor
                display_pos += 1

        def next_wrap_unit_width(unit_index):
            """Measure the next visual prose unit, including glued dash gaps."""
            width = 0
            found = False
            for index in range(unit_index, len(units)):
                _style, text, src_start, src_end = units[index]
                for offset, char in enumerate(text):
                    source_index = min(
                        src_start + offset,
                        max(src_start, src_end - 1),
                    )
                    if char.isspace():
                        if not found:
                            continue
                        if source_index in dash_glue_positions:
                            width += _display_char_width(char)
                            continue
                        return width
                    found = True
                    width += _display_char_width(char)
            return width

        body_col = 0
        for unit_index, (style, text, src_start, src_end) in enumerate(units):
            in_body = src_start >= prefix_width
            first_char = text[:1]
            if (
                fallback_wrap
                and in_body
                and first_char
                and not first_char.isspace()
                and body_col >= body_width
            ):
                fill = max(0, (body_width + 1) - body_col)
                append_display_padding(fill, src_start)
                body_col = 0

            for pos in range(src_start, src_end):
                source_to_display_map.setdefault(pos, display_pos)

            result.append((style, text))
            for offset in range(len(text)):
                display_to_source_map[display_pos + offset] = src_start
            display_pos += len(text)
            source_to_display_map[src_end] = display_pos

            if not in_body:
                continue

            if style != "class:markdown.hard-break":
                body_col += _display_text_width(text)

            if fallback_wrap and text.isspace():
                # The spaces around a drafted dash stand-in are visual glue,
                # not line-break opportunities.  The whitespace before the
                # left-hand word sees the entire ``word -- word`` phrase as the
                # next unit and moves that phrase together when necessary.
                if any(
                    pos in dash_glue_positions
                    for pos in range(src_start, src_end)
                ):
                    continue
                unit_width = next_wrap_unit_width(unit_index + 1)
                if 0 < unit_width <= body_width and body_col + unit_width > body_width:
                    fill = max(0, (body_width + 1) - body_col)
                    append_display_padding(
                        fill, src_end - 1 if src_end > src_start else src_start
                    )
                    # The source cursor position after this whitespace is also
                    # the position immediately before the first word on the
                    # new visual row.  Map it to that new-row boundary rather
                    # than leaving the earlier mapping at the end of the
                    # previous row.  Otherwise Left from ``N|either`` appears
                    # to jump over ``|Neither`` to the preceding wrapped row.
                    source_to_display_map[src_end] = display_pos
                    body_col = 0

        source_to_display_map[source_length] = display_pos
        display_to_source_map[display_pos] = source_length

        # A folded footnote definition is displayed as one atomic compact
        # label even though its source contains the hidden identifier plus a
        # trailing sentinel. Make the canonical visible end (immediately before
        # that sentinel) map to the end of the displayed label. This keeps the
        # cursor out of hidden source while still giving the object two normal
        # visual boundaries for Left/Right, Home/End, and vertical navigation.
        if (
            source_line.endswith(FOOTNOTE_SENTINEL)
            and any(len(span) >= 5 and span[4] for span in spans)
        ):
            visible_end = max(0, source_length - 1)
            source_to_display_map[visible_end] = display_pos
            display_to_source_map[display_pos] = visible_end

        def source_to_display(position):
            position = max(0, min(position, source_length))
            return source_to_display_map.get(position, display_pos)

        def display_to_source(position):
            position = max(0, min(position, display_pos))
            while position >= 0:
                if position in display_to_source_map:
                    return display_to_source_map[position]
                position -= 1
            return 0

        return Transformation(
            result,
            source_to_display=source_to_display,
            display_to_source=display_to_source,
        )


def _soft_wrap_line_prefix(lineno, wrap_count):
    """Render the structural gutter on visual soft-wrap continuations."""
    if wrap_count <= 0:
        return []
    try:
        columns = get_app().output.get_size().columns
    except Exception:
        columns = WRAP_COLUMN + 1
    _left, gutter, _right = _prose_layout_widths(columns)
    if gutter <= 0:
        return []

    try:
        row_layout = _display_row_layout(text_area.buffer.text, lineno)
        quote_marker = _blockquote_gutter_text(
            row_layout.blockquote_depth, gutter
        )
    except Exception:
        quote_marker = ""

    if not quote_marker:
        return [("class:editor", " " * gutter)]

    marker_width = _display_text_width(quote_marker)
    padding = max(0, gutter - marker_width)
    fragments = []
    if padding:
        fragments.append(("class:editor", " " * padding))
    fragments.append(("class:markdown.blockquote-gutter", quote_marker))
    return fragments


_MULTI_CLICK_SECONDS = 0.40
_MULTI_CLICK_INDEX_TOLERANCE = 1


def _inline_footnote_global_span_at_position(full_text, position, direction=0):
    """Return a compact inline-footnote source span touching ``position``.

    ``direction`` controls which boundary counts as belonging to the object:
    moving right treats the opening boundary as part of the object, moving left
    treats the closing boundary as part of it, and zero accepts either edge.
    This keeps hidden identifiers such as ``[^smith]`` atomic even though the
    prose view displays only a compact reference such as ``[1]``.
    """
    position = max(0, min(len(full_text), int(position)))
    compact_identifiers = _footnote_number_map(full_text)
    for (
        start, end, identifier, _row, _start_col, _end_col
    ) in _footnote_reference_spans(full_text):
        if identifier not in compact_identifiers:
            continue
        if start < position < end:
            return start, end, identifier
        if direction >= 0 and position == start:
            return start, end, identifier
        if direction <= 0 and position == end:
            return start, end, identifier
    return None


def _normalize_word_target(full_text, origin, target, direction):
    """Keep word navigation from landing inside compact footnote source."""
    span = _inline_footnote_global_span_at_position(full_text, origin, direction)
    if span is not None:
        start, end, _identifier = span
        return end if direction > 0 else start

    # A stock prompt_toolkit word boundary can point at the hidden identifier.
    # Snap such a result to the far visible edge in the direction of travel.
    compact_identifiers = _footnote_number_map(full_text)
    for (
        start, end, identifier, _row, _start_col, _end_col
    ) in _footnote_reference_spans(full_text):
        if identifier not in compact_identifiers:
            continue
        if direction > 0 and origin < end and start <= target < end:
            return end
        if direction < 0 and origin > start and start < target <= end:
            return start
    return target


def _word_navigation_target(document, direction):
    """Return the next visible word-navigation target for the prose editor."""
    origin = document.cursor_position

    # Folded table/footnote labels are one visible object even though their
    # internal placeholder text contains several source words plus a sentinel.
    folded = _folded_placeholder_at_cursor(document)
    if folded is not None:
        row = document.cursor_position_row
        col = document.cursor_position_col
        line = document.current_line
        visible_end = (
            len(line) - 1
            if line.endswith((TABLE_SENTINEL, FOOTNOTE_SENTINEL))
            else len(line)
        )
        row_start = document.translate_row_col_to_index(row, 0)
        if direction > 0 and col < visible_end:
            return row_start + visible_end
        if direction < 0 and col > 0:
            return row_start
        # At the right visible edge, begin the stock search after the hidden
        # sentinel so Ctrl+Right cannot stop on its zero-width source position.
        if direction > 0 and col >= visible_end and len(line) > visible_end:
            origin = row_start + len(line)
            document = Document(document.text, cursor_position=origin)

    if direction < 0:
        amount = document.find_previous_word_beginning()
        if amount is None:
            return None
    else:
        amount = document.find_next_word_beginning()
        if amount is None:
            if origin >= len(document.text):
                return None
            amount = len(document.text) - origin
    target = max(0, min(len(document.text), origin + amount))
    target = _normalize_word_target(document.text, origin, target, direction)
    return _clamp_source_position_out_of_gutter(document.text, target)


def _word_selection_range(full_text, cursor_position):
    """Return the source range for the visible word/object at the cursor."""
    cursor_position = max(0, min(len(full_text), cursor_position))
    footnote_span = _inline_footnote_global_span_at_position(full_text, cursor_position, 1)
    if footnote_span is not None:
        start, end, _identifier = footnote_span
        return start, end

    line_start, line_end = _line_bounds_at_position(full_text, cursor_position)
    line = full_text[line_start:line_end]
    if _folded_object_line(line):
        visible_end = line_end
        if line.endswith((TABLE_SENTINEL, FOOTNOTE_SENTINEL)):
            visible_end -= 1
        if line_start <= cursor_position <= visible_end:
            return line_start, visible_end

    document = Document(full_text, cursor_position=cursor_position)
    start_delta, end_delta = document.find_boundaries_of_current_word()
    start = cursor_position + start_delta
    end = cursor_position + end_delta
    if end <= start:
        return None
    return start, end


def _paragraph_selection_range(full_text, cursor_position):
    """Return the logical Markdown paragraph/block range at the cursor.

    Prose and blockquotes select their full logical block. Inside a supported
    flat list, triple-click selects only the list item under the pointer rather
    than the entire adjacent run. Other nonblank Markdown constructs select
    their own source block. Blank rows do not create a selection.
    """
    if not full_text:
        return None

    cursor_position = max(0, min(len(full_text), cursor_position))
    document = Document(full_text, cursor_position=cursor_position)
    row = document.cursor_position_row
    lines = full_text.split("\n")

    target_start = target_end = None
    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        if not (block.start <= row < block.end):
            continue
        if block.kind == "blank":
            return None

        if block.kind == "list-run" and block.list_items:
            for item in block.list_items:
                if item.start <= row < item.end:
                    target_start, target_end = item.start, item.end
                    break
        else:
            target_start, target_end = block.start, block.end
        break

    if target_start is None or target_end is None or target_end <= target_start:
        return None

    start = document.translate_row_col_to_index(target_start, 0)
    last_row = target_end - 1
    end = document.translate_row_col_to_index(last_row, len(lines[last_row]))
    if end <= start:
        return None
    return start, end


def _select_source_range(buffer, source_range):
    """Apply one ordinary character selection to ``buffer``."""
    if source_range is None:
        return False
    start, end = source_range
    start = max(0, min(len(buffer.text), start))
    end = max(start, min(len(buffer.text), end))
    if end <= start:
        return False

    buffer.exit_selection()
    buffer.cursor_position = start
    buffer.start_selection(selection_type=SelectionType.CHARACTERS)
    buffer.cursor_position = end
    return True


class FullWidthSafeBufferControl(BufferControl):
    """Focus, position, and implement Carriage's prose mouse semantics."""

    def _reset_carriage_click_sequence(self):
        self._carriage_click_count = 0
        self._carriage_last_click_time = 0.0
        self._carriage_last_click_index = None

    def mouse_handler(self, mouse_event):
        buffer = self.buffer

        if mouse_event.event_type == MouseEventType.MOUSE_DOWN:
            app = get_app()
            if app.layout.current_control is not self:
                app.layout.current_control = self

            self._carriage_mouse_dragged = False
            result = super().mouse_handler(mouse_event)
            # BufferControl translates transformed gutter glyphs back to source
            # positions too. They are not navigable editor space, so normalize
            # a click on structural Markdown to the visible prose boundary.
            _clamp_buffer_cursor_out_of_gutter(buffer)
            self._carriage_mouse_down_index = buffer.cursor_position
            if find_replace.active:
                _find_replace_refocus_input()
            return result

        if (
            mouse_event.event_type == MouseEventType.MOUSE_MOVE
            and mouse_event.button != MouseButton.NONE
        ):
            self._carriage_mouse_dragged = True
            self._reset_carriage_click_sequence()
            result = super().mouse_handler(mouse_event)
            _clamp_buffer_cursor_out_of_gutter(buffer)
            if find_replace.active:
                _find_replace_refocus_input()
            return result
        if mouse_event.event_type == MouseEventType.MOUSE_UP:
            # Disable prompt_toolkit's private timestamp-only double-click
            # heuristic. Carriage owns the complete multi-click policy so a
            # rapid click elsewhere cannot accidentally count as a double-click.
            self._last_click_timestamp = None

            dragged = getattr(self, "_carriage_mouse_dragged", False)
            if dragged:
                # Real drag selection still belongs to BufferControl. Mouse-move
                # events establish/update the selection, and Mouse Up finalizes
                # the release position.
                result = super().mouse_handler(mouse_event)
                _clamp_buffer_cursor_out_of_gutter(buffer)
                if find_replace.active:
                    anchor = buffer.cursor_position
                    self._reset_carriage_click_sequence()
                    _find_replace_reanchor_after_document_mouse(anchor)
                    return result
                self._reset_carriage_click_sequence()
                return result

            # A plain click is complete on Mouse Down: that event focused the
            # editor, cleared any old selection, and positioned the insertion
            # point using the render map that was actually clicked. Do not pass
            # the matching Mouse Up through BufferControl. Ending Carriage's
            # wheel-scroll mode on Mouse Down can repaint the viewport before
            # Mouse Up arrives; prompt_toolkit would then map the same screen
            # coordinate through the new viewport and interpret the difference
            # as a drag selection. Carriage handles multi-click selection below.
            result = None
            _clamp_buffer_cursor_out_of_gutter(buffer)
            if find_replace.active:
                anchor = buffer.cursor_position
                self._reset_carriage_click_sequence()
                _find_replace_reanchor_after_document_mouse(anchor)
                return result

            click_index = getattr(
                self, "_carriage_mouse_down_index", buffer.cursor_position
            )
            now = time.monotonic()
            previous_time = getattr(self, "_carriage_last_click_time", 0.0)
            previous_index = getattr(self, "_carriage_last_click_index", None)
            previous_count = getattr(self, "_carriage_click_count", 0)

            same_spot = (
                previous_index is not None
                and abs(click_index - previous_index)
                <= _MULTI_CLICK_INDEX_TOLERANCE
            )
            if same_spot and now - previous_time <= _MULTI_CLICK_SECONDS:
                click_count = previous_count + 1
            else:
                click_count = 1

            self._carriage_click_count = click_count
            self._carriage_last_click_time = now
            self._carriage_last_click_index = click_index

            if click_count == 2:
                _select_source_range(
                    buffer,
                    _word_selection_range(buffer.text, click_index),
                )
            elif click_count >= 3:
                _select_source_range(
                    buffer,
                    _paragraph_selection_range(buffer.text, click_index),
                )
                # A fourth click begins a new sequence rather than repeatedly
                # cycling word/paragraph selections.
                self._reset_carriage_click_sequence()

            return result

        return super().mouse_handler(mouse_event)


text_area = TextArea(
    text="",
    lexer=ProseMarkdownLexer(),
    wrap_lines=True,
    scrollbar=False,
    focus_on_click=True,
    input_processors=[ProseLayoutProcessor()],
    style="class:editor",
)
# TextArea constructs a normal prompt_toolkit Buffer internally. Promote only
# the main prose buffer to CarriageBuffer; dialog/cell editors keep their local
# prompt_toolkit undo histories. No state exists yet in these stacks, so the
# class promotion is safe immediately after construction.
text_area.buffer.__class__ = CarriageBuffer
text_area.buffer._undo_stack = []
text_area.buffer._redo_stack = []
text_area.control.__class__ = FullWidthSafeBufferControl
text_area.window.__class__ = ScrollableWindow
text_area.window._height_cache_generation = 0
text_area.window._height_cache_key = None
text_area.window._height_cache_heights = None
text_area.window._height_cache_prefix = None
text_area.window._height_line_cache = {}
# Preferred rendered-screen column for repeated Up/Down navigation. Unlike
# Buffer.preferred_column, this is measured in visual cells after Carriage's
# display transformations and soft wrapping.
text_area.window._vertical_preferred_x = None
text_area.window._visual_vertical_move_in_progress = False
text_area.window.keyboard_scroll_active = False
# Visual cursor geometry is expensive on very long logical paragraphs. Cache
# only rows actually visited by navigation; text edits clear these caches.
text_area.window._visual_positions_cache = {}
text_area.window._visual_candidates_cache = {}
# Alt+Up/Alt+Down can pin a target heading to the first visible editor row.
# The anchor survives repaints but is cleared by any subsequent ordinary
# cursor movement, edit, or manual viewport scroll.
text_area.window._section_top_anchor_row = None
text_area.window.on_scrollbar_interact = _on_scrollbar_interact


def _check_prompt_toolkit_private_contract():
    """Recheck the promoted main-editor instances before Application creation."""
    required = [
        (text_area.buffer, "_undo_stack", "Buffer undo stack"),
        (text_area.buffer, "_redo_stack", "Buffer redo stack"),
        (text_area.window, "_write_to_screen_at_index", "Window screen writer"),
        (text_area.window, "_scroll", "Window scrolling hook"),
        (text_area.window, "_get_margin_width", "Window margin geometry"),
        (text_area.window, "_mouse_handler", "Window mouse fallback"),
        (text_area.control, "_last_click_timestamp", "BufferControl click state"),
        (
            text_area.control,
            "_last_get_processed_line",
            "BufferControl processed-line cache",
        ),
    ]
    missing = [label for obj, name, label in required if not hasattr(obj, name)]
    missing.extend(
        f"WindowRenderInfo.{name}" for name in _window_render_info_contract_missing()
    )
    if missing:
        details = ", ".join(missing)
        raise RuntimeError(
            "This prompt_toolkit build is missing private interfaces required "
            f"by Carriage: {details}. Reinstall {PROMPT_TOOLKIT_REQUIREMENT}."
        )

# Wheel/scrollbar scrolling is allowed to move the viewport away from the
# insertion point. Hide the screen cursor during that read-only navigation;
# any actual edit or cursor movement exits manual-scroll mode and restores it.
text_area.window.always_hide_cursor = Condition(
    lambda: text_area.window.manual_scroll_active
)
# Keep display-only continuations aligned with the prose column. The layout
# processor performs visual word wrapping only; it never inserts source
# newlines during ordinary editing.
text_area.window.get_line_prefix = _soft_wrap_line_prefix
# Keep the prose body at the configured display width on wide terminals. The
# ProseLayoutProcessor borrows part of the existing left-side breathing room as
# a hanging structural gutter, with one spare cursor cell after the prose body.
# The Window remains full-width so the scrollbar stays flush right.
_scrollbar_margin = RenderedScrollbarMargin(lambda: text_area.window, display_arrows=True)
text_area.window.left_margins = [CenterPaddingMargin("left")]
text_area.window.right_margins = [CenterPaddingMargin("right")] + (
    [_scrollbar_margin] if SCROLLBAR_VISIBLE else []
)


def _resume_editor_view(_buffer=None):
    """Exit manual scrolling and keep the prose caret out of the gutter."""
    buffer = _buffer or text_area.buffer
    _clamp_buffer_cursor_out_of_gutter(buffer)
    text_area.window.end_manual_scroll()
    # Ordinary cursor movement releases any Alt+Up/Alt+Down viewport anchor.
    # Section navigation installs a fresh anchor after moving the cursor.
    text_area.window._section_top_anchor_row = None
    # Repeated Up/Down presses preserve both the rendered-screen column and
    # Carriage's rendered-row viewport ownership. Any other cursor movement
    # returns viewport scrolling to prompt_toolkit.
    if not text_area.window._visual_vertical_move_in_progress:
        text_area.window._vertical_preferred_x = None
        text_area.window.keyboard_scroll_active = False


def _editor_text_changed(_buffer=None):
    """Reset viewport ownership, invalidate layout, and protect changed work."""
    state.extend_selection_mode = False
    text_area.window.end_manual_scroll()
    text_area.window.keyboard_scroll_active = False
    text_area.window._section_top_anchor_row = None
    text_area.window._vertical_preferred_x = None
    text_area.window.invalidate_rendered_height_cache()
    text_area.window._visual_positions_cache.clear()
    text_area.window._visual_candidates_cache.clear()
    _working_state_changed()


text_area.buffer.on_cursor_position_changed += _resume_editor_view
text_area.buffer.on_text_changed += _editor_text_changed

floats = []
dialog_stack = []
current_float = None
current_table_editor = None
current_footnote_editor = None


# ---------------------------------------------------------------------------
# Dialog helpers
# ---------------------------------------------------------------------------

def show_dialog(dialog, focus=None, on_close=None):
    """Show a modal dialog, preserving any dialog already underneath it."""
    global current_float
    # Find/Replace and a modal dialog must never own focus simultaneously.
    if find_replace.active:
        _close_find_replace()
    dialog_float = Float(content=dialog)
    focus_target = focus if focus is not None else dialog
    floats.append(dialog_float)
    dialog_stack.append((dialog_float, focus_target, on_close))
    current_float = dialog_float

    app = get_app()
    app.layout.focus(focus_target)
    app.invalidate()
    return dialog_float


def close_dialog():
    """Close the top dialog and restore focus to the dialog beneath it."""
    global current_float, current_table_editor, current_footnote_editor

    closed_float = None
    on_close = None
    if dialog_stack:
        dialog_float, _, on_close = dialog_stack.pop()
        closed_float = dialog_float
        if dialog_float in floats:
            floats.remove(dialog_float)

    closed_object_editor = False
    if (
        current_table_editor is not None
        and closed_float is current_table_editor.dialog_float
    ):
        current_table_editor = None
        closed_object_editor = True
    if (
        current_footnote_editor is not None
        and closed_float is current_footnote_editor.dialog_float
    ):
        current_footnote_editor = None
        closed_object_editor = True

    # An active object-editor draft participates in the protected working-state
    # journal. Closing that editor, whether by Save or Cancel, changes what the
    # next recovery should contain even when the main prose buffer is unchanged.
    if closed_object_editor:
        if _has_recoverable_changes():
            _working_state_changed(immediate=True)
        else:
            _clear_recovery_file()
            _reset_working_state_tracking()

    app = get_app()
    if dialog_stack:
        current_float, focus_target, _ = dialog_stack[-1]
        app.layout.focus(focus_target)
    else:
        current_float = None
        app.layout.focus(text_area)
    app.invalidate()

    if on_close is not None:
        on_close()


class SingleLineBuffer(Buffer):
    """Buffer that never permits CR/LF source inside a one-line control."""

    @staticmethod
    def _single_line_text(data):
        return str(data).replace("\r\n", " ").replace("\r", " ").replace("\n", " ")

    def insert_text(self, data, overwrite=False, move_cursor=True, fire_event=True):
        return super().insert_text(
            self._single_line_text(data),
            overwrite=overwrite,
            move_cursor=move_cursor,
            fire_event=fire_event,
        )


class SingleLineInput:
    """Minimal one-line dialog input without TextArea scrolling chrome."""

    def __init__(self, text="", *, style="class:input-field", width=None):
        clean = SingleLineBuffer._single_line_text(text)
        self.buffer = SingleLineBuffer(
            document=Document(clean, cursor_position=len(clean)),
            multiline=False,
        )
        clipboard_kb = KeyBindings()

        @clipboard_kb.add("c-x", eager=True)
        def _cut(event):
            _dialog_buffer_cut(event.current_buffer)

        @clipboard_kb.add("c-c")
        def _copy(event):
            _dialog_buffer_copy(event.current_buffer)

        @clipboard_kb.add("c-v")
        def _paste(event):
            _dialog_buffer_paste(event.current_buffer)

        self.control = BufferControl(
            buffer=self.buffer,
            focusable=True,
            focus_on_click=True,
            key_bindings=clipboard_kb,
        )
        self.window = Window(
            content=self.control,
            height=D.exact(1),
            width=width,
            dont_extend_height=True,
            dont_extend_width=width is not None,
            wrap_lines=False,
            style=style,
        )

    @property
    def text(self):
        return self.buffer.text

    def __pt_container__(self):
        return self.window


def _rebalance_wrapped_lines(lines, width):
    """Reduce very short final lines in dialog/help wrapping."""
    if len(lines) < 2:
        return lines
    balanced = list(lines)
    min_last = max(12, int(width * 0.35))
    while len(balanced) >= 2:
        last = balanced[-1]
        prev = balanced[-2]
        if len(last.strip()) >= min_last:
            break
        prev_words = prev.split()
        if len(prev_words) < 2:
            break
        candidate_prev = " ".join(prev_words[:-1])
        candidate_last = prev_words[-1] + (" " + last if last else "")
        if len(candidate_prev) > width or len(candidate_last) > width:
            break
        balanced[-2] = candidate_prev
        balanced[-1] = candidate_last
    return balanced


def _wrap_dialog_paragraph(text, width=64, initial_indent="", subsequent_indent=""):
    """Wrap one dialog/help paragraph with light widow control."""
    wrapper = textwrap.TextWrapper(
        width=width,
        initial_indent=initial_indent,
        subsequent_indent=subsequent_indent,
        break_long_words=False,
        break_on_hyphens=False,
    )
    wrapped = wrapper.wrap(text)
    return _rebalance_wrapped_lines(wrapped or [""], width)


def _wrap_dialog_prose(text, width=64):
    """Word-wrap dialog prose while preserving intentional line breaks."""
    rendered = []
    for line in str(text).splitlines():
        if not line:
            rendered.append("")
            continue
        rendered.extend(_wrap_dialog_paragraph(line, width=width))
    return "\n".join(rendered)


def _dialog_prose(text, width=64):
    """Return a consistently word-wrapped explanatory label for dialogs."""
    return Label(
        text=_wrap_dialog_prose(text, width),
        wrap_lines=True,
        width=D(preferred=width, max=width),
    )


def _current_transient_status_message():
    """Return the active transient status-line notice, if any."""
    message = state.transient_status_message
    if message is None:
        return None
    if time.monotonic() < state.transient_status_expires_at:
        return message
    state.transient_status_message = None
    state.transient_status_expires_at = 0.0
    return None


def _clear_transient_status_message(generation=None):
    """Clear one transient notice without erasing a newer replacement."""
    if (
        generation is not None
        and generation != state.transient_status_generation
    ):
        return
    state.transient_status_message = None
    state.transient_status_expires_at = 0.0
    try:
        get_app().invalidate()
    except Exception:
        pass


def show_transient_status(message, duration=3.0):
    """Show a nonmodal full-width notice on the status-bar line."""
    state.transient_status_generation += 1
    generation = state.transient_status_generation
    effective_duration = max(0.1, float(duration))
    state.transient_status_message = str(message)
    state.transient_status_expires_at = time.monotonic() + effective_duration

    try:
        get_app().invalidate()
    except Exception:
        pass

    # Keyboard/menu handlers run inside prompt_toolkit's asyncio loop. Schedule
    # one invalidation at expiry so a notice disappears even when the writer
    # pauses without pressing another key. The generation guard prevents an
    # older timer from clearing a newer message.
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        return
    loop.call_later(
        effective_duration, _clear_transient_status_message, generation
    )


def show_message(title, text, on_close=None):
    ok_button = Button(text="OK", handler=close_dialog)
    dialog = Dialog(
        title=title,
        body=_dialog_prose(text, width=64),
        buttons=[ok_button],
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=ok_button, on_close=on_close)


def show_input_dialog(title, label_text, default, callback):
    input_field = SingleLineInput(text=default)

    def ok_handler():
        value = input_field.text
        close_dialog()
        callback(value)

    dialog = Dialog(
        title=title,
        body=HSplit([_dialog_prose(label_text, width=64), input_field]),
        buttons=[
            Button(text="OK", handler=ok_handler),
            Button(text="Cancel", handler=close_dialog),
        ],
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=input_field)


def confirm(title, text, on_yes):
    yes_button = Button(text="Yes", handler=lambda: (close_dialog(), on_yes()))
    cancel_button = Button(text="Cancel", handler=close_dialog)
    dialog = Dialog(
        title=title,
        body=_dialog_prose(text, width=64),
        buttons=[yes_button, cancel_button],
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=cancel_button)


def with_unsaved_changes_check(action):
    """
    Wrap an action (New/Open/Quit) so that if there are unsaved changes, it
    offers to save first rather than just discard-or-cancel. Saving (when
    the file has never been saved) goes through the Save As dialog, and
    `action` only runs once that genuinely succeeds - cancelling Save As,
    or a failed write, aborts the whole thing rather than proceeding.
    """

    def wrapper():
        if not state.is_modified(text_area.text):
            action()
            return

        save_button = Button(text="Save", handler=lambda: (close_dialog(), do_save(on_saved=action)))
        discard_button = Button(text="Don't Save", handler=lambda: (close_dialog(), action()))
        cancel_button = Button(text="Cancel", handler=close_dialog)

        dialog = Dialog(
            title="Unsaved changes",
            body=_dialog_prose("Save changes before continuing?", width=64),
            buttons=[save_button, discard_button, cancel_button],
            width=D(preferred=70),
        )
        show_dialog(dialog, focus=save_button)

    return wrapper


# ---------------------------------------------------------------------------
# File operations
# ---------------------------------------------------------------------------

_MISSING_DISK_SNAPSHOT = ("missing", None)
_SAVE_OK = "ok"
_SAVE_CONFLICT = "conflict"
_SAVE_ERROR = "error"
_SAVE_READ_ONLY = "read_only"
_SAVE_DURABILITY_ERROR = "durability_error"


def _canonical_path(path):
    """Return the concrete path Carriage will read from or replace."""
    return os.path.realpath(os.path.abspath(path))


def _fsync_directory(directory):
    """Flush directory metadata after a POSIX namespace change.

    Windows does not expose the POSIX open-directory/fsync sequence through
    ``os.open``. Durable Windows replacements instead use MoveFileExW with
    MOVEFILE_WRITE_THROUGH in ``_replace_file_durably`` below. The remaining
    direct caller is recovery-journal cleanup, where a lost unlink is harmless
    because the journal is file-fsynced with a retired marker before deletion.
    """
    if os.name == "nt":
        return

    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    dir_fd = os.open(directory, flags)
    try:
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)


def _windows_replace_file_write_through(source_path, target_path):
    """Atomically replace one Windows file and request write-through durability."""
    import ctypes
    from ctypes import wintypes

    movefile_replace_existing = 0x00000001
    movefile_write_through = 0x00000008

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    move_file_ex = kernel32.MoveFileExW
    move_file_ex.argtypes = [wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.DWORD]
    move_file_ex.restype = wintypes.BOOL

    flags = movefile_replace_existing | movefile_write_through
    if not move_file_ex(source_path, target_path, flags):
        error = ctypes.get_last_error()
        raise OSError(
            error,
            f"Windows durable file replacement failed (WinError {error})",
            target_path,
        )


def _replace_file_durably(source_path, target_path):
    """Replace a same-directory file and durably commit the namespace change."""
    if os.name == "nt":
        _windows_replace_file_write_through(source_path, target_path)
        return

    os.replace(source_path, target_path)
    _fsync_directory(os.path.dirname(target_path) or ".")


def _same_document_path(first, second):
    """Return True when two pathnames identify the same source file."""
    if not first or not second:
        return False

    first_real = _canonical_path(first)
    second_real = _canonical_path(second)
    if os.path.normcase(first_real) == os.path.normcase(second_real):
        return True

    # realpath catches symlink aliases. samefile also catches hard links when
    # both directory entries currently exist.
    try:
        return os.path.samefile(first_real, second_real)
    except (FileNotFoundError, OSError):
        return False


def _snapshot_bytes(raw_bytes):
    return ("file", hashlib.sha256(raw_bytes).hexdigest())


def _disk_snapshot(path):
    """Fingerprint the exact bytes currently stored at path.

    A missing path is a meaningful version: it lets a first save detect that
    another program created the destination after Carriage chose it.
    """
    target_path = _canonical_path(path)
    try:
        file_stat = os.stat(target_path)
    except FileNotFoundError:
        return _MISSING_DISK_SNAPSHOT

    if not stat.S_ISREG(file_stat.st_mode):
        raise OSError(f"Not a regular file: {target_path}")

    digest = hashlib.sha256()
    with open(target_path, "rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            digest.update(chunk)
    return ("file", digest.hexdigest())


class _LargeFileConfirmationRequired(Exception):
    """Raised before loading an unusually large regular file into memory."""

    def __init__(self, size_bytes):
        self.size_bytes = max(0, int(size_bytes))
        super().__init__(f"Large file confirmation required: {self.size_bytes} bytes")


def _format_file_size(size_bytes):
    """Return a compact human-readable binary file size."""
    size = max(0, int(size_bytes))
    if size < 1024:
        return f"{size} byte{'s' if size != 1 else ''}"
    value = float(size)
    for unit in ("KiB", "MiB", "GiB", "TiB"):
        value /= 1024.0
        if value < 1024.0 or unit == "TiB":
            return f"{value:.1f} {unit}"
    return f"{size} bytes"


def _large_file_prompt_text(path, size_bytes):
    """Return the warning shown before an unusually large file is loaded."""
    return (
        f'The file "{os.path.basename(path) or path}" is {_format_file_size(size_bytes)}. '
        "Carriage is designed for prose documents, and a file this large can "
        "use substantial memory and may respond slowly.\n\nOpen it anyway?"
    )


def _read_utf8_file_with_snapshot(path, *, allow_large=False):
    """Read one regular UTF-8 file and fingerprint exactly the bytes read.

    Open the path nonblocking where the platform supports it, then validate
    the opened descriptor with fstat() before reading. Files above Carriage's
    generous prose-oriented warning threshold require explicit approval before
    their contents are allocated. Reading itself is chunked and rechecks the
    threshold so a file that grows after open cannot bypass the warning.
    """
    target_path = _canonical_path(path)
    flags = os.O_RDONLY
    if hasattr(os, "O_NONBLOCK"):
        flags |= os.O_NONBLOCK

    fd = os.open(target_path, flags)
    try:
        file_stat = os.fstat(fd)
        if not stat.S_ISREG(file_stat.st_mode):
            raise OSError(f"Not a regular file: {target_path}")
        if not allow_large and file_stat.st_size > LARGE_FILE_WARNING_BYTES:
            raise _LargeFileConfirmationRequired(file_stat.st_size)

        digest = hashlib.sha256()
        decoder = codecs.getincrementaldecoder("utf-8")()
        decoded_parts = []
        total_bytes = 0

        with os.fdopen(fd, "rb") as f:
            fd = None  # fdopen owns and closes the descriptor now.
            while True:
                chunk = f.read(FILE_READ_CHUNK_BYTES)
                if not chunk:
                    break
                total_bytes += len(chunk)
                if not allow_large and total_bytes > LARGE_FILE_WARNING_BYTES:
                    raise _LargeFileConfirmationRequired(total_bytes)
                digest.update(chunk)
                decoded_parts.append(decoder.decode(chunk))
            decoded_parts.append(decoder.decode(b"", final=True))
    finally:
        if fd is not None:
            os.close(fd)

    content = "".join(decoded_parts)
    # Match the universal-newline behavior Carriage used before v1.03 while
    # keeping the fingerprint tied to the exact source bytes.
    content = content.replace("\r\n", "\n").replace("\r", "\n")
    return content, ("file", digest.hexdigest())


def _path_is_read_only(path):
    """Return True when an existing regular file should not be replaced.

    Check the mode bits as well as os.access(). The explicit mode-bit test is
    important when Carriage is run by a privileged account: a 0444 document is
    still intentionally read-only even if that account could technically
    replace it through the containing directory.
    """
    target_path = _canonical_path(path)
    try:
        file_stat = os.stat(target_path)
    except FileNotFoundError:
        return False

    if not stat.S_ISREG(file_stat.st_mode):
        raise OSError(f"Not a regular file: {target_path}")

    write_bits = stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH
    return not bool(file_stat.st_mode & write_bits) or not os.access(target_path, os.W_OK)


def _read_extended_attributes(path):
    """Return readable extended attributes for an existing regular file.

    Atomic replacement creates a new inode, so xattrs that belong to the old
    inode must be copied deliberately. Platforms without the standard xattr
    APIs simply return an empty mapping. Unsupported filesystems are treated
    the same way; other errors are surfaced rather than silently discarding
    metadata that Carriage knows is present.
    """
    if not all(hasattr(os, name) for name in ("listxattr", "getxattr", "setxattr")):
        return {}

    unsupported = {
        value
        for name in ("ENOTSUP", "EOPNOTSUPP", "EINVAL")
        if (value := getattr(errno, name, None)) is not None
    }
    try:
        names = os.listxattr(path)
    except OSError as e:
        if e.errno in unsupported:
            return {}
        raise OSError(f"Could not read file metadata for {path}: {e}") from e

    attributes = {}
    for name in names:
        try:
            attributes[name] = os.getxattr(path, name)
        except OSError as e:
            # An attribute can disappear between listxattr() and getxattr().
            # That is harmless; any other readable-metadata failure must stop
            # the save rather than knowingly replace the inode without it.
            if e.errno == getattr(errno, "ENODATA", None):
                continue
            raise OSError(
                f"Could not read extended attribute {name!r} from {path}: {e}"
            ) from e
    return attributes


def _set_open_file_mode(fd, path, mode):
    """Set mode on an open file across Carriage's supported Python versions.

    ``os.fchmod`` is unavailable on Windows before Python 3.13. The staged
    files Carriage adjusts always have a private pathname of their own, so use
    path-based ``os.chmod`` only when descriptor-based chmod is unavailable.
    POSIX and Windows 3.13+ retain the descriptor-based operation.
    """
    fchmod = getattr(os, "fchmod", None)
    if callable(fchmod):
        fchmod(fd, mode)
    else:
        os.chmod(path, mode)


def _apply_replacement_metadata(fd, path, source_stat, source_xattrs):
    """Apply preservable metadata from the old inode to a temporary file.

    Ownership/group, permission bits, and every readable extended attribute are
    preserved before the temporary file can replace the source. System-managed
    attributes that the filesystem already assigned identically need no write.
    If known metadata cannot be reproduced, abort the save instead of silently
    dropping it.
    """
    temp_stat = os.fstat(fd)
    source_uid = getattr(source_stat, "st_uid", None)
    source_gid = getattr(source_stat, "st_gid", None)
    temp_uid = getattr(temp_stat, "st_uid", source_uid)
    temp_gid = getattr(temp_stat, "st_gid", source_gid)

    if (temp_uid, temp_gid) != (source_uid, source_gid):
        if not hasattr(os, "fchown"):
            raise OSError(
                "Carriage cannot preserve this file's owner/group on this platform during atomic replacement."
            )
        try:
            os.fchown(fd, source_uid, source_gid)
        except OSError as e:
            raise OSError(
                "Carriage cannot preserve this file's owner/group during atomic replacement."
            ) from e

    _set_open_file_mode(fd, path, stat.S_IMODE(source_stat.st_mode))

    for name, value in source_xattrs.items():
        try:
            current = os.getxattr(fd, name)
        except OSError:
            current = None
        if current == value:
            continue
        try:
            os.setxattr(fd, name, value)
        except OSError as e:
            raise OSError(
                f"Carriage cannot preserve extended attribute {name!r} during atomic replacement."
            ) from e


class _AtomicReplaceCancelled(Exception):
    """Internal signal that a staged replacement failed final validation."""

    def __init__(self, result):
        super().__init__(str(result))
        self.result = result


class _AtomicReplaceDurabilityError(OSError):
    """The replacement is visible, but durable completion could not be confirmed."""

    def __init__(self, target_path, error):
        super().__init__(str(error))
        self.target_path = target_path
        self.original_error = error


class _AtomicReplaceHardLinkError(OSError):
    """Atomic replacement would sever an existing hard-link relationship."""


def _durable_atomic_replace(
    target_path,
    write_staged,
    *,
    temp_prefix=None,
    temp_suffix=".tmp",
    new_file_mode,
    preserve_existing_metadata=True,
    reject_hardlinks=False,
    validate_before_replace=None,
):
    """Write ``target_path`` through one durable same-directory replacement.

    ``write_staged`` receives a private temporary pathname and must completely
    produce the replacement contents there. Carriage then applies the final
    destination metadata, fsyncs the staged inode, performs any caller-supplied
    last-moment validation, and atomically replaces the destination. POSIX then
    fsyncs the containing directory; Windows performs the replacement with the
    documented MoveFileExW write-through flag.

    Callers retain policy decisions such as conflict/read-only messages and
    recovery behavior. This helper owns only the filesystem replacement
    invariant so Save, exports, and config writes cannot quietly drift apart.
    Recovery journals deliberately keep their separate generation/locking path.
    """
    target_path = _canonical_path(target_path)
    directory = os.path.dirname(target_path) or "."
    basename = os.path.basename(target_path)
    prefix = temp_prefix if temp_prefix is not None else f".{basename}."
    temp_path = None
    fd = None

    try:
        fd, temp_path = tempfile.mkstemp(
            prefix=prefix,
            suffix=temp_suffix,
            dir=directory,
        )
        # The writer should see a normal private staging pathname. Close the
        # descriptor returned by mkstemp first; the 0600 inode remains in place.
        os.close(fd)
        fd = None
        write_staged(temp_path)

        try:
            existing_stat = os.stat(target_path)
        except FileNotFoundError:
            existing_stat = None

        existing_xattrs = {}
        if existing_stat is not None:
            if not stat.S_ISREG(existing_stat.st_mode):
                raise OSError(f"Not a regular file: {target_path}")
            if reject_hardlinks and existing_stat.st_nlink > 1:
                raise _AtomicReplaceHardLinkError(
                    "Atomic replacement would break an existing hard-link relationship."
                )
            if preserve_existing_metadata:
                existing_xattrs = _read_extended_attributes(target_path)

        # Apply final metadata only after the staged contents are complete.
        # This keeps the temporary inode private while a writer such as Pandoc
        # is still using it, even when the destination's final mode is read-only.
        with open(temp_path, "rb") as staged:
            if existing_stat is not None and preserve_existing_metadata:
                _apply_replacement_metadata(
                    staged.fileno(), temp_path, existing_stat, existing_xattrs
                )
            elif existing_stat is not None:
                _set_open_file_mode(
                    staged.fileno(), temp_path, stat.S_IMODE(existing_stat.st_mode)
                )
            else:
                _set_open_file_mode(staged.fileno(), temp_path, new_file_mode)
            os.fsync(staged.fileno())

        if validate_before_replace is not None:
            validation_result = validate_before_replace()
            if validation_result is not None:
                raise _AtomicReplaceCancelled(validation_result)

        try:
            _replace_file_durably(temp_path, target_path)
            temp_path = None
        except OSError as e:
            # On POSIX, the rename may already be visible when directory fsync
            # fails. On Windows, MoveFileExW with WRITE_THROUGH reports the
            # replacement and its durability as one operation. Preserve the
            # existing post-replacement error class when the target already
            # contains the staged inode; otherwise let the ordinary write error
            # path report a replacement that did not complete.
            if not os.path.exists(temp_path) and os.path.exists(target_path):
                temp_path = None
                raise _AtomicReplaceDurabilityError(target_path, e) from e
            raise
    finally:
        if fd is not None:
            try:
                os.close(fd)
            except OSError:
                pass
        if temp_path is not None:
            try:
                os.unlink(temp_path)
            except OSError:
                pass


def _recovery_directory():
    """Return the per-user directory used for protected working-state journals."""
    base = os.environ.get("XDG_STATE_HOME")
    if not base:
        base = os.path.join(os.path.expanduser("~"), ".local", "state")
    return os.path.join(base, "carriage", "recovery")


def _table_recovery_record(table):
    return {
        "headers": list(table.headers),
        "rows": [list(row) for row in table.rows],
        "title": table.title,
        "alignments": list(table.alignments),
        "original_lines": None if table.original_lines is None else list(table.original_lines),
        "caption_position": table.caption_position,
        "dirty": bool(table.dirty),
    }


def _recovery_string_list(value, label, *, allow_none=False):
    """Return a validated recovery list of strings.

    Recovery data is untrusted crash-state input.  Keep every schema failure a
    controlled ValueError so discovery/restoration can skip a corrupt journal
    without allowing incidental TypeError/AttributeError exceptions to escape.
    """
    if value is None and allow_none:
        return None
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"Recovery file contains invalid {label}.")
    return list(value)


def _table_from_recovery_record(raw_table):
    if not isinstance(raw_table, dict):
        raise ValueError("Recovery file contains invalid table data.")

    headers = _recovery_string_list(raw_table.get("headers"), "table headers")
    # MAX_TABLE_EDITOR_COLUMNS is a UI limit for creating/editing basic tables,
    # not a document-format limit. Carriage intentionally folds and preserves
    # wider imported Markdown tables, so their recovery records remain valid as
    # long as every row and alignment entry has the same nonzero width.
    if not headers:
        raise ValueError("Recovery file contains a table without headers.")

    raw_rows = raw_table.get("rows")
    if not isinstance(raw_rows, list):
        raise ValueError("Recovery file contains invalid table rows.")
    rows = []
    for raw_row in raw_rows:
        row = _recovery_string_list(raw_row, "table row")
        if len(row) != len(headers):
            raise ValueError("Recovery file contains a table row with the wrong width.")
        rows.append(row)

    title = raw_table.get("title")
    if not isinstance(title, str):
        raise ValueError("Recovery file contains an invalid table title.")

    alignments = _recovery_string_list(
        raw_table.get("alignments"), "table alignments"
    )
    if len(alignments) != len(headers) or any(
        alignment not in {"default", "left", "center", "right"}
        for alignment in alignments
    ):
        raise ValueError("Recovery file contains invalid table alignments.")

    original_lines = _recovery_string_list(
        raw_table.get("original_lines"), "original table source", allow_none=True
    )
    caption_position = raw_table.get("caption_position")
    if caption_position not in {None, "before", "after"}:
        raise ValueError("Recovery file contains an invalid table caption position.")
    dirty = raw_table.get("dirty")
    if not isinstance(dirty, bool):
        raise ValueError("Recovery file contains an invalid table dirty flag.")

    return TableData(
        headers=headers,
        rows=rows,
        title=title,
        alignments=alignments,
        original_lines=original_lines,
        caption_position=caption_position,
        dirty=dirty,
    )


def _table_content_key(table):
    """Return the editable table content, excluding bookkeeping metadata."""
    return (
        table.title,
        tuple(table.headers),
        tuple(tuple(row) for row in table.rows),
        tuple(table.alignments),
    )


def _footnote_recovery_record(note):
    return {
        "identifier": note.identifier,
        "text": note.text,
        "original_lines": None if note.original_lines is None else list(note.original_lines),
        "dirty": bool(note.dirty),
    }


def _footnote_from_recovery_record(raw_note):
    if not isinstance(raw_note, dict):
        raise ValueError("Recovery file contains invalid footnote data.")
    identifier = raw_note.get("identifier")
    if (
        not isinstance(identifier, str)
        or not identifier.strip()
        or identifier != identifier.strip()
        or "]" in identifier
        or "\n" in identifier
        or "\r" in identifier
    ):
        raise ValueError("Recovery file contains an invalid footnote identifier.")
    text = raw_note.get("text")
    if not isinstance(text, str):
        raise ValueError("Recovery file contains invalid footnote text.")
    original_lines = _recovery_string_list(
        raw_note.get("original_lines"), "original footnote source", allow_none=True
    )
    dirty = raw_note.get("dirty")
    if not isinstance(dirty, bool):
        raise ValueError("Recovery file contains an invalid footnote dirty flag.")
    return FootnoteData(
        identifier=identifier,
        text=text,
        original_lines=original_lines,
        dirty=dirty,
    )


def _footnote_content_key(note):
    return note.text


def _active_footnote_draft():
    session = current_footnote_editor
    if session is None:
        return None
    working = copy.deepcopy(session.working)
    if session.editor is not None:
        working.text = _normalize_footnote_text(session.editor.text)
    return session.identifier, working


def _active_table_draft():
    """Return a snapshot of the active table editor without committing it.

    The text currently present in an actively edited cell is folded into the
    snapshot using the same newline normalization as a real cell commit. The
    live table-editor session is never mutated by working-state recovery.
    """
    session = current_table_editor
    if session is None:
        return None

    working = copy.deepcopy(session.working)
    if session.title_editor is not None:
        working.title = " ".join(session.title_editor.text.splitlines()).strip()
    if session.editing and session.cell_editor is not None:
        rows = [working.headers] + working.rows
        if (
            0 <= session.selected_row < len(rows)
            and 0 <= session.selected_col < working.column_count
        ):
            rows[session.selected_row][session.selected_col] = " ".join(
                session.cell_editor.text.splitlines()
            )
    return session.table_number, working


def _has_recoverable_changes():
    """Return True when RAM contains work newer than the saved document."""
    if state.is_modified(text_area.text):
        return True

    draft = _active_table_draft()
    if draft is not None:
        table_number, working = draft
        committed = state.tables.get(table_number)
        if committed is None or _table_content_key(working) != _table_content_key(committed):
            return True

    footnote_draft = _active_footnote_draft()
    if footnote_draft is not None:
        identifier, working = footnote_draft
        committed = state.footnotes.get(identifier)
        if committed is None or _footnote_content_key(working) != _footnote_content_key(committed):
            return True
    return False


def _linux_boot_id():
    """Return the current Linux boot identifier when /proc exposes it."""
    try:
        with open("/proc/sys/kernel/random/boot_id", "r", encoding="ascii") as f:
            value = f.read().strip()
    except (OSError, UnicodeError):
        return None
    return value or None


def _linux_process_start_ticks(pid):
    """Return Linux /proc start-time ticks for pid, or None when unavailable.

    /proc/<pid>/stat field 22 is the process start time in clock ticks since
    boot. The comm field is parenthesized and may contain spaces or ')' chars,
    so split only after its final closing parenthesis.
    """
    if not isinstance(pid, int) or pid <= 0:
        return None
    try:
        with open(f"/proc/{pid}/stat", "r", encoding="utf-8") as f:
            stat_line = f.read().strip()
    except (OSError, UnicodeError):
        return None

    close_paren = stat_line.rfind(")")
    if close_paren < 0:
        return None
    fields = stat_line[close_paren + 1 :].strip().split()
    # fields[0] is field 3 (state), so field 22 is index 19 here.
    if len(fields) <= 19:
        return None
    start_ticks = fields[19]
    return start_ticks if start_ticks.isdigit() else None


def _posix_process_start_stamp(pid):
    """Return a stable ps start stamp for pid on POSIX systems as fallback."""
    if os.name != "posix" or not isinstance(pid, int) or pid <= 0:
        return None
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    try:
        result = subprocess.run(
            ["ps", "-o", "lstart=", "-p", str(pid)],
            check=False,
            capture_output=True,
            text=True,
            timeout=1,
            env=env,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    value = " ".join(result.stdout.split())
    return value or None


def _process_start_identity(pid):
    """Return a stable identity for one incarnation of pid when possible."""
    start_ticks = _linux_process_start_ticks(pid)
    if start_ticks is not None:
        # Start ticks are unique only within a boot, so include the boot ID when
        # available. Keeping the prefix makes future formats unambiguous.
        boot_id = _linux_boot_id()
        if boot_id is not None:
            return f"linux:{boot_id}:{start_ticks}"
        return f"linux-start:{start_ticks}"

    stamp = _posix_process_start_stamp(pid)
    if stamp is not None:
        return f"ps:{stamp}"
    return None


_RECOVERY_OWNER_PID = os.getpid()
_RECOVERY_OWNER_BOOT_ID = _linux_boot_id()
_RECOVERY_OWNER_START_ID = _process_start_identity(_RECOVERY_OWNER_PID)
_RECOVERY_IO_LOCK = threading.Lock()


def _recovery_payload():
    """Capture recoverable editor state, including active object-editor drafts."""
    tables = {
        str(number): _table_recovery_record(table)
        for number, table in state.tables.items()
    }

    draft = _active_table_draft()
    had_table_draft = False
    if draft is not None:
        table_number, working = draft
        committed = state.tables.get(table_number)
        if committed is None or _table_content_key(working) != _table_content_key(committed):
            working.dirty = True
            tables[str(table_number)] = _table_recovery_record(working)
            had_table_draft = True

    footnotes = {
        identifier: _footnote_recovery_record(note)
        for identifier, note in state.footnotes.items()
    }
    footnote_draft = _active_footnote_draft()
    had_footnote_draft = False
    if footnote_draft is not None:
        identifier, working = footnote_draft
        committed = state.footnotes.get(identifier)
        if committed is None or _footnote_content_key(working) != _footnote_content_key(committed):
            working.dirty = True
            footnotes[identifier] = _footnote_recovery_record(working)
            had_footnote_draft = True

    source_path = _canonical_path(state.path) if state.path is not None else None
    disk_snapshot = None if state.disk_snapshot is None else list(state.disk_snapshot)

    return {
        "format": RECOVERY_FORMAT_VERSION,
        "pid": _RECOVERY_OWNER_PID,
        "boot_id": _RECOVERY_OWNER_BOOT_ID,
        "process_start_id": _RECOVERY_OWNER_START_ID,
        "source_path": source_path,
        "saved_text": state.saved_text,
        "disk_snapshot": disk_snapshot,
        "cursor_position": text_area.buffer.cursor_position,
        "visible_text": text_area.text,
        "tables": tables,
        "footnotes": footnotes,
        "had_table_draft": had_table_draft,
        "had_footnote_draft": had_footnote_draft,
        "retired": False,
    }


def _ensure_recovery_target():
    """Return the active recovery path and its generation token."""
    directory = _recovery_directory()
    with _RECOVERY_IO_LOCK:
        if state.recovery_path is None:
            token = os.urandom(6).hex()
            state.recovery_path = os.path.join(
                directory, f"recovery-{os.getpid()}-{token}.json"
            )
            state.recovery_epoch += 1
            state.recovery_committed_revision = 0
        return state.recovery_path, state.recovery_epoch


def _claim_recovery_path(path):
    """Claim an existing recovery journal for this process generation."""
    with _RECOVERY_IO_LOCK:
        state.recovery_path = path
        state.recovery_epoch += 1
        state.recovery_committed_revision = 0
        return state.recovery_epoch


def _recovery_snapshot_data():
    """Capture one immutable working-state payload on the UI thread."""
    recovery_path, epoch = _ensure_recovery_target()
    payload = json.dumps(
        _recovery_payload(),
        ensure_ascii=False,
        separators=(",", ":"),
    )
    return recovery_path, epoch, payload, state.working_state_revision


def _write_recovery_payload_atomic(recovery_path, epoch, payload, revision):
    """Durably commit a captured journal unless its generation was retired.

    The potentially slow temporary-file write and file fsync happen outside the
    lock. Only the final durable replacement is serialized with journal clearing.
    If an explicit Save/New/Open retires this recovery generation
    while the background write is underway, the stale temporary file is simply
    discarded and can never recreate the old journal afterward.
    """
    directory = os.path.dirname(recovery_path)
    os.makedirs(directory, mode=0o700, exist_ok=True)
    try:
        os.chmod(directory, 0o700)
    except OSError:
        pass

    temp_path = None
    fd = None
    try:
        fd, temp_path = tempfile.mkstemp(
            prefix=".recovery-",
            suffix=".tmp",
            dir=directory,
            text=True,
        )
        _set_open_file_mode(fd, temp_path, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
            fd = None
            f.write(payload)
            f.flush()
            os.fsync(f.fileno())

        with _RECOVERY_IO_LOCK:
            if (
                state.recovery_path != recovery_path
                or state.recovery_epoch != epoch
                or revision < state.recovery_committed_revision
            ):
                return False
            _replace_file_durably(temp_path, recovery_path)
            temp_path = None
            state.recovery_committed_revision = revision
        return True
    finally:
        if fd is not None:
            os.close(fd)
        if temp_path is not None:
            try:
                os.unlink(temp_path)
            except OSError:
                pass


def _refresh_recovery_error_state():
    """Project recovery write/cleanup failures into the user-visible status."""
    previous = (
        state.recovery_error,
        state.recovery_error_kind,
        state.recovery_error_message,
    )

    if state.recovery_write_error_message:
        state.recovery_error = True
        state.recovery_error_kind = "write"
        state.recovery_error_message = state.recovery_write_error_message
    elif state.recovery_cleanup_failures:
        state.recovery_error = True
        state.recovery_error_kind = "cleanup"
        path, detail = next(iter(state.recovery_cleanup_failures.items()))
        state.recovery_error_message = (
            f"Could not safely retire obsolete recovery journal {path!r}: {detail}"
        )
    else:
        state.recovery_error = False
        state.recovery_error_kind = None
        state.recovery_error_message = None

    current = (
        state.recovery_error,
        state.recovery_error_kind,
        state.recovery_error_message,
    )
    if current != previous:
        state.recovery_error_reported = False


def _record_recovery_success(revision):
    state.working_state_persisted_revision = max(
        state.working_state_persisted_revision, revision
    )
    if state.working_state_revision == revision:
        state.working_state_first_dirty_at = None
        state.working_state_last_change_at = None
    state.recovery_write_error_message = None
    _refresh_recovery_error_state()


def _record_recovery_failure(error, *, immediate_retry=False):
    """Record a checkpoint failure and leave the current RAM state retryable."""
    detail = str(error).strip() or error.__class__.__name__
    state.recovery_write_error_message = detail
    _refresh_recovery_error_state()

    # A restored journal can fail before Buffer.reset has advanced the normal
    # mutation revision (for example under a fault-injected framework failure).
    # Keep the recovered RAM state strictly newer than the last accounted-for
    # revision so the background loop cannot silently consider it protected.
    if state.working_state_revision <= state.working_state_persisted_revision:
        state.working_state_revision = state.working_state_persisted_revision + 1

    now = time.monotonic()
    if immediate_retry:
        state.working_state_first_dirty_at = now - WORKING_STATE_MAX_LATENCY_SECONDS
        state.working_state_last_change_at = now - WORKING_STATE_IDLE_SECONDS
    else:
        state.working_state_first_dirty_at = now
        state.working_state_last_change_at = now

    try:
        get_app().invalidate()
    except Exception:
        pass


def _write_recovery_snapshot():
    """Synchronously persist the current protected working state.

    Normal editing uses the asynchronous scheduler below. This synchronous path
    is retained for rare boundary operations such as claiming a restored journal
    or preserving work after a save-durability warning.
    """
    if not _has_recoverable_changes():
        _clear_recovery_file()
        _reset_working_state_tracking()
        return

    recovery_path, epoch, payload, revision = _recovery_snapshot_data()
    committed = _write_recovery_payload_atomic(recovery_path, epoch, payload, revision)
    if committed:
        _record_recovery_success(revision)


def _mark_recovery_retired(path):
    """Durably mark an obsolete journal so it can never be offered as recovery.

    Directory permissions can occasionally prevent unlinking a journal even
    though the journal itself remains writable. In that case overwrite the
    obsolete journal in place with a retired marker. This is intentionally a
    fallback for data that no longer needs recovery; even interruption during
    this rewrite can only leave an unreadable file, which stale-recovery
    discovery already ignores rather than restoring.
    """
    try:
        with open(path, "r+", encoding="utf-8") as f:
            try:
                payload = json.load(f)
            except (ValueError, json.JSONDecodeError):
                payload = {}
            if not isinstance(payload, dict):
                payload = {}

            # Keep enough structure for normal recovery-file validation and
            # manual diagnosis while making the retirement state explicit.
            payload.setdefault("format", RECOVERY_FORMAT_VERSION)
            payload.setdefault("pid", _RECOVERY_OWNER_PID)
            payload.setdefault("boot_id", _RECOVERY_OWNER_BOOT_ID)
            payload.setdefault("process_start_id", _RECOVERY_OWNER_START_ID)
            payload.setdefault("source_path", None)
            payload.setdefault("saved_text", "")
            payload.setdefault("disk_snapshot", None)
            payload.setdefault("cursor_position", 0)
            payload.setdefault("visible_text", "")
            payload.setdefault("tables", {})
            payload.setdefault("footnotes", {})
            payload.setdefault("had_table_draft", False)
            payload.setdefault("had_footnote_draft", False)
            payload["retired"] = True
            payload["retired_at"] = time.time()
            payload["retired_by_pid"] = _RECOVERY_OWNER_PID

            f.seek(0)
            json.dump(payload, f, ensure_ascii=False, separators=(",", ":"))
            f.truncate()
            f.flush()
            os.fsync(f.fileno())
        return True, None
    except FileNotFoundError:
        return True, None
    except (OSError, UnicodeError, TypeError, ValueError) as e:
        return False, str(e)


def _cleanup_recovery_path(path, *, already_retired=False):
    """Durably make one obsolete journal harmless, then remove it if possible.

    Retirement deliberately precedes unlink.  If a crash loses the directory
    update and resurrects the old name, the file contents already carry a
    file-fsynced retired marker and stale discovery will never offer it.  A
    On POSIX, a directory fsync is still attempted after successful unlink so
    ordinary cleanup itself is durable as well. Windows does not require the
    unlink to be durable for recovery safety because retirement came first.
    """
    if not path:
        return True

    if not already_retired:
        retired, retire_error = _mark_recovery_retired(path)
        if not retired:
            state.recovery_cleanup_failures[path] = (
                f"retirement failed before unlink: {retire_error}"
            )
            return False

    try:
        os.unlink(path)
    except FileNotFoundError:
        state.recovery_cleanup_failures.pop(path, None)
        return True
    except OSError:
        # A physically retained journal is nevertheless safe once its retired
        # marker is durable.  Later boundary operations can try removal again,
        # but destructive document transitions need not be blocked.
        state.recovery_cleanup_failures.pop(path, None)
        return True

    try:
        _fsync_directory(os.path.dirname(path) or ".")
    except OSError:
        # The unlink may be lost in a power failure, but retirement was already
        # file-fsynced before it.  A resurrected name therefore remains harmless.
        pass

    state.recovery_cleanup_failures.pop(path, None)
    return True


def _retry_failed_recovery_cleanup():
    """Retry journals that previously could neither be removed nor retired."""
    if not state.recovery_cleanup_failures:
        return True
    for path in list(state.recovery_cleanup_failures):
        _cleanup_recovery_path(path)
    _refresh_recovery_error_state()
    return not state.recovery_cleanup_failures


def _clear_recovery_file():
    """Retire the active journal generation and make obsolete recovery harmless.

    Return True when every obsolete journal is either deleted or durably marked
    retired. False means at least one old journal could still be mistaken for a
    crash recovery on a future launch; callers performing destructive state
    transitions can then stop rather than creating that ambiguity.
    """
    with _RECOVERY_IO_LOCK:
        recovery_path = state.recovery_path
        # Retire this generation before touching the file. A background writer
        # that is still preparing a temporary snapshot will see the epoch/path
        # mismatch at commit time and cannot recreate the retired journal.
        state.recovery_path = None
        state.recovery_epoch += 1
        state.recovery_committed_revision = 0

    if recovery_path is not None:
        _cleanup_recovery_path(recovery_path)

    # A later boundary operation is also an opportunity to retry any older
    # cleanup failure after permissions/filesystem conditions have changed.
    _retry_failed_recovery_cleanup()
    state.recovery_write_error_message = None
    _refresh_recovery_error_state()
    return not state.recovery_cleanup_failures

def _validate_recovery_object_correspondence(visible_text, tables, footnotes):
    """Validate the one-to-one folded-label/object relationship in a journal."""
    seen_tables = set()
    seen_footnotes = set()
    for line in visible_text.split("\n"):
        table_match = TABLE_PLACEHOLDER_RE.match(line)
        if table_match is not None:
            number = int(table_match.group(1))
            if number in seen_tables:
                raise ValueError(
                    f"Recovery file contains more than one placeholder for Table {number}."
                )
            if number not in tables:
                raise ValueError(
                    f"Recovery file contains a placeholder for missing Table {number}."
                )
            seen_tables.add(number)
            continue

        footnote_match = FOOTNOTE_PLACEHOLDER_RE.match(line)
        if footnote_match is not None:
            identifier = footnote_match.group(1)
            if identifier in seen_footnotes:
                raise ValueError(
                    "Recovery file contains more than one placeholder for "
                    f"footnote {identifier!r}."
                )
            if identifier not in footnotes:
                raise ValueError(
                    f"Recovery file contains a placeholder for missing footnote {identifier!r}."
                )
            seen_footnotes.add(identifier)

    missing_tables = sorted(set(tables) - seen_tables)
    if missing_tables:
        raise ValueError(
            "Recovery file contains table data without a folded placeholder."
        )
    missing_footnotes = sorted(set(footnotes) - seen_footnotes)
    if missing_footnotes:
        raise ValueError(
            "Recovery file contains footnote data without a folded placeholder."
        )


def _read_recovery_payload(path):
    """Read and strictly validate the current recovery-journal schema.

    This function deliberately converts every malformed schema shape into
    ValueError.  Callers can therefore preserve and skip corrupt journals for
    manual inspection without startup or restoration being interrupted by an
    incidental AttributeError, TypeError, or conversion exception.
    """
    with open(path, "r", encoding="utf-8") as f:
        payload = json.load(f)

    if not isinstance(payload, dict):
        raise ValueError("Recovery file root must be a JSON object.")
    format_version = payload.get("format")
    if type(format_version) is not int or format_version != RECOVERY_FORMAT_VERSION:
        raise ValueError("Unsupported Carriage recovery format.")

    pid = payload.get("pid")
    if type(pid) is not int or pid <= 0:
        raise ValueError("Recovery file contains an invalid process identifier.")
    for key, label in (
        ("boot_id", "boot identifier"),
        ("process_start_id", "process-start identifier"),
        ("source_path", "source path"),
    ):
        value = payload.get(key)
        if value is not None and not isinstance(value, str):
            raise ValueError(f"Recovery file contains an invalid {label}.")

    for key, label in (
        ("saved_text", "saved document text"),
        ("visible_text", "visible document text"),
    ):
        if not isinstance(payload.get(key), str):
            raise ValueError(f"Recovery file does not contain valid {label}.")

    cursor_position = payload.get("cursor_position")
    if type(cursor_position) is not int or cursor_position < 0:
        raise ValueError("Recovery file contains an invalid cursor position.")

    raw_snapshot = payload.get("disk_snapshot")
    if raw_snapshot is not None:
        if (
            not isinstance(raw_snapshot, list)
            or len(raw_snapshot) != 2
            or raw_snapshot[0] not in {"file", "missing"}
            or (
                raw_snapshot[0] == "file"
                and not isinstance(raw_snapshot[1], str)
            )
            or (raw_snapshot[0] == "missing" and raw_snapshot[1] is not None)
        ):
            raise ValueError("Recovery file contains an invalid disk snapshot.")

    for key, label in (
        ("had_table_draft", "table-draft flag"),
        ("had_footnote_draft", "footnote-draft flag"),
        ("retired", "retirement flag"),
    ):
        if not isinstance(payload.get(key), bool):
            raise ValueError(f"Recovery file contains an invalid {label}.")

    raw_tables = payload.get("tables")
    if not isinstance(raw_tables, dict):
        raise ValueError("Recovery file contains invalid table data.")
    tables = {}
    for raw_number, raw_table in raw_tables.items():
        if not isinstance(raw_number, str) or not raw_number.isdigit():
            raise ValueError("Recovery file contains an invalid table number.")
        number = int(raw_number)
        if number <= 0 or str(number) != raw_number or number in tables:
            raise ValueError("Recovery file contains an invalid table number.")
        tables[number] = _table_from_recovery_record(raw_table)

    raw_footnotes = payload.get("footnotes")
    if not isinstance(raw_footnotes, dict):
        raise ValueError("Recovery file contains invalid footnote data.")
    footnotes = {}
    for raw_identifier, raw_note in raw_footnotes.items():
        if not isinstance(raw_identifier, str):
            raise ValueError("Recovery file contains an invalid footnote key.")
        note = _footnote_from_recovery_record(raw_note)
        if raw_identifier != note.identifier or raw_identifier in footnotes:
            raise ValueError("Recovery file contains inconsistent footnote data.")
        footnotes[raw_identifier] = note

    _validate_recovery_object_correspondence(
        payload["visible_text"], tables, footnotes
    )
    return payload

def _windows_process_is_running(pid):
    """Probe one Windows PID without sending a signal or terminating it.

    A process object is nonsignaled while the process is running and becomes
    signaled when it terminates. Open only SYNCHRONIZE access and perform a
    zero-time wait. If Windows refuses the probe for a reason other than an
    invalid PID, treat the owner as live conservatively so Carriage never offers
    a recovery journal that may still belong to another running process.
    """
    import ctypes
    from ctypes import wintypes

    SYNCHRONIZE = 0x00100000
    WAIT_OBJECT_0 = 0x00000000
    WAIT_TIMEOUT = 0x00000102
    ERROR_INVALID_PARAMETER = 87

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    kernel32.WaitForSingleObject.restype = wintypes.DWORD
    kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel32.CloseHandle.restype = wintypes.BOOL

    handle = kernel32.OpenProcess(SYNCHRONIZE, False, pid)
    if not handle:
        if ctypes.get_last_error() == ERROR_INVALID_PARAMETER:
            return False
        return True

    try:
        result = kernel32.WaitForSingleObject(handle, 0)
    finally:
        kernel32.CloseHandle(handle)

    if result == WAIT_OBJECT_0:
        return False
    if result == WAIT_TIMEOUT:
        return True
    return True


def _process_is_running(pid):
    if not isinstance(pid, int) or pid <= 0:
        return False
    if os.name == "nt":
        return _windows_process_is_running(pid)
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False
    return True


def _recovery_owner_is_live(payload):
    """Return True only when a recovery still belongs to its live creator.

    Recovery journals bind the PID to the creator's process-start identity and,
    on Linux, boot identity. If identity cannot be re-read for a live PID, keep
    the journal suppressed rather than risk offering recovery for a document
    that may still be open in another Carriage process.
    """
    pid = payload.get("pid")
    if not _process_is_running(pid):
        return False

    stored_start_id = payload.get("process_start_id")
    stored_boot_id = payload.get("boot_id")

    if stored_boot_id:
        current_boot_id = _linux_boot_id()
        if current_boot_id is not None and current_boot_id != stored_boot_id:
            return False

    if stored_start_id:
        live_start_id = _process_start_identity(pid)
        if live_start_id is not None:
            return live_start_id == stored_start_id
        # Identity was recorded but cannot currently be verified. Do not fall
        # back to treating the PID alone as positive proof; suppress the journal
        # conservatively until the process is gone.
        return True

    # A boot ID alone can prove staleness after reboot, but cannot distinguish
    # PID reuse within the same boot. New Carriage journals normally also carry
    # process_start_id; this branch is a conservative fallback.
    return True


def _stale_recovery_files(source_path=None):
    """Return newest-first recoveries whose creating process is gone.

    When source_path is supplied, return only journals for that named document.
    A normal bare launch leaves source_path unset and can offer any recovery.
    """
    directory = _recovery_directory()
    try:
        names = os.listdir(directory)
    except FileNotFoundError:
        return []
    except OSError:
        return []

    expected_source = _canonical_path(source_path) if source_path else None
    stale = []
    for name in names:
        if not (name.startswith("recovery-") and name.endswith(".json")):
            continue
        path = os.path.join(directory, name)
        try:
            payload = _read_recovery_payload(path)
            if payload.get("retired") is True:
                # An intentional Save/New/Open/Quit cleanup may have left a
                # durably retired journal physically present. Never offer it;
                # opportunistically remove it through the same directory-syncing
                # cleanup path without requiring another in-place rewrite.
                _cleanup_recovery_path(path, already_retired=True)
                continue
            if _recovery_owner_is_live(payload):
                continue

            recovery_source = payload.get("source_path")
            if expected_source is not None:
                if not recovery_source:
                    continue
                if os.path.normcase(_canonical_path(recovery_source)) != os.path.normcase(expected_source):
                    continue

            modified = os.stat(path).st_mtime
        except (OSError, ValueError, json.JSONDecodeError):
            # Corrupt recovery files are left untouched rather than deleted
            # automatically; they may still be useful for manual inspection.
            continue
        stale.append((modified, path))
    stale.sort(reverse=True)
    return [path for _, path in stale]


def _restore_recovery_file(path):
    """Restore one validated journal and immediately reclaim its protection.

    The recovered document remains available if the claim write fails, but it
    is explicitly marked unprotected and scheduled for an immediate retry. The
    caller can then report the precise state instead of implying restoration
    failed or silently leaving the old dead-process journal identity in place.
    Return True when protection was claimed successfully, False otherwise.
    """
    payload = _read_recovery_payload(path)
    if payload.get("retired") is True:
        raise ValueError("This recovery journal was intentionally retired.")
    restored_tables = {}
    for raw_number, raw_table in payload["tables"].items():
        number = int(raw_number)
        restored_tables[number] = _table_from_recovery_record(raw_table)

    restored_footnotes = {}
    for raw_identifier, raw_note in payload.get("footnotes", {}).items():
        note = _footnote_from_recovery_record(raw_note)
        restored_footnotes[str(raw_identifier)] = note

    recovered_visible_text = payload["visible_text"]
    cursor_position = payload.get("cursor_position", len(recovered_visible_text))
    cursor_position = max(0, min(len(recovered_visible_text), cursor_position))

    # A crash may capture an in-progress table-title draft in the object state
    # before the prose placeholder has been refreshed. Derive folded labels
    # from the recovered table objects so screen and save state agree. Preserve
    # the logical cursor row/column as closely as possible if a label changes.
    old_doc = Document(text=recovered_visible_text, cursor_position=cursor_position)
    visible_text = _canonicalize_table_placeholders(
        recovered_visible_text, restored_tables
    )
    new_doc = Document(text=visible_text)
    cursor_row = min(old_doc.cursor_position_row, new_doc.line_count - 1)
    cursor_col = min(old_doc.cursor_position_col, len(new_doc.lines[cursor_row]))
    cursor_position = new_doc.translate_row_col_to_index(cursor_row, cursor_col)

    source_path = payload.get("source_path")
    saved_text = payload.get("saved_text", "")
    raw_snapshot = payload.get("disk_snapshot")
    disk_snapshot = None if raw_snapshot is None else tuple(raw_snapshot)

    # Commit the fully parsed local state together. No recovery input is allowed
    # to mutate the live editor before all schema/object validation has passed.
    # The shared installer also normalizes a legacy or otherwise invalid saved
    # cursor out of hidden structural Markdown while preserving valid logical
    # positions elsewhere in the recovered document.
    _install_editor_document(
        visible_text,
        cursor_position=cursor_position,
        path=source_path,
        saved_text=saved_text,
        disk_snapshot=disk_snapshot,
        tables=restored_tables,
        footnotes=restored_footnotes,
        reset_working_state=False,
    )

    _claim_recovery_path(path)
    state.recovery_write_error_message = None
    _refresh_recovery_error_state()

    # Claim the restored journal for this process immediately so a second
    # concurrently running Carriage instance will not offer it as stale.
    try:
        _write_recovery_snapshot()
    except Exception as e:
        _record_recovery_failure(e, immediate_retry=True)
        return False
    return True


def _offer_stale_recovery(source_path=None):
    recoveries = _stale_recovery_files(source_path)
    if not recoveries:
        return

    recovery_path = recoveries[0]
    try:
        payload = _read_recovery_payload(recovery_path)
    except (OSError, ValueError, json.JSONDecodeError):
        return

    recovery_source = payload.get("source_path")
    if recovery_source:
        document_label = os.path.basename(recovery_source) or recovery_source
        description = (
            f'Carriage found protected unsaved work for "{document_label}" from an earlier '
            "session that did not close normally. Restore it?"
        )
    else:
        description = (
            "Carriage found protected unsaved work for an untitled document from an earlier "
            "session that did not close normally. Restore it?"
        )

    if payload.get("had_table_draft"):
        description += "\n\nThe recovery includes an in-progress table edit."
    if payload.get("had_footnote_draft"):
        description += "\n\nThe recovery includes an in-progress footnote edit."

    extra = len(recoveries) - 1
    if extra:
        description += (
            f"\n\n{extra} older recovery file{'s' if extra != 1 else ''} "
            "will remain available."
        )

    def restore_handler():
        close_dialog()
        try:
            protected = _restore_recovery_file(recovery_path)
        except (OSError, ValueError, json.JSONDecodeError) as e:
            show_message("Recovery error", str(e))
            return
        if not protected:
            show_message(
                "Recovery protection warning",
                "The recovered document is open, but Carriage could not yet "
                "reclaim its working-state journal for this process. The "
                "document remains marked unprotected and Carriage will retry "
                "automatically. Save the document to commit it manually.\n\n"
                f"{state.recovery_error_message or 'Unknown recovery error.'}",
            )

    def discard_handler():
        close_dialog()
        if not _cleanup_recovery_path(recovery_path):
            show_message(
                "Recovery error",
                state.recovery_error_message
                or state.recovery_cleanup_failures.get(
                    recovery_path, "Could not safely discard the recovery journal."
                ),
            )
            return
        _refresh_recovery_error_state()
        _offer_stale_recovery(source_path)

    restore_button = Button(text="Restore", handler=restore_handler)
    discard_button = Button(text="Discard", handler=discard_handler)
    later_button = Button(text="Later", handler=close_dialog)
    dialog = Dialog(
        title="Recover document?",
        body=_dialog_prose(description, width=72),
        buttons=[restore_button, discard_button, later_button],
        width=D(preferred=78),
    )
    show_dialog(dialog, focus=restore_button)

def _show_read_only_save(on_saved=None):
    """Route a normal Save away from a source marked read-only."""

    def save_as_handler():
        close_dialog()
        do_save_as(on_saved)

    save_as_button = Button(text="Save As...", handler=save_as_handler)
    cancel_button = Button(text="Cancel", handler=close_dialog)
    dialog = Dialog(
        title="Read-only file",
        body=_dialog_prose(
            "The current file is marked read-only. Carriage will not replace it.\n\n"
            "Use Save As to write your changes to a different file.",
            width=70,
        ),
        buttons=[save_as_button, cancel_button],
        width=D(preferred=76),
    )
    show_dialog(dialog, focus=save_as_button)


def _show_save_conflict(disk_snapshot, on_saved=None):
    """Offer safe choices when the current file changed outside Carriage."""

    def save_as_handler():
        close_dialog()
        do_save_as(on_saved)

    def overwrite_handler():
        close_dialog()
        result = _write_file(state.path, expected_snapshot=disk_snapshot)
        if result == _SAVE_OK and on_saved:
            on_saved()

    save_as_button = Button(text="Save As...", handler=save_as_handler)
    overwrite_button = Button(text="Overwrite", handler=overwrite_handler)
    cancel_button = Button(text="Cancel", handler=close_dialog)
    dialog = Dialog(
        title="File changed on disk",
        body=_dialog_prose(
            "This file has been changed, replaced, or deleted outside Carriage "
            "since it was opened or last saved.\n\n"
            "Save As keeps both versions. Overwrite replaces the current disk "
            "version with the text in Carriage.",
            width=72,
        ),
        buttons=[save_as_button, overwrite_button, cancel_button],
        width=D(preferred=78),
    )
    show_dialog(dialog, focus=cancel_button)


def _confirm_replace(title, text, on_replace):
    replace_button = Button(
        text="Replace", handler=lambda: (close_dialog(), on_replace())
    )
    cancel_button = Button(text="Cancel", handler=close_dialog)
    dialog = Dialog(
        title=title,
        body=_dialog_prose(text, width=68),
        buttons=[replace_button, cancel_button],
        width=D(preferred=74),
    )
    show_dialog(dialog, focus=cancel_button)



def _reprotect_after_blocked_cleanup():
    """Re-journal unsaved RAM state when a destructive transition is blocked.

    New/Open/Quit retire the current journal before changing document state. If
    cleanup proves unsafe and the transition is therefore cancelled, the old
    document remains in RAM and must immediately receive a fresh active journal
    generation rather than relying on the retired/failed path.
    """
    if not _has_recoverable_changes():
        return
    _working_state_changed(immediate=True)
    try:
        _write_recovery_snapshot()
    except (OSError, UnicodeError, TypeError, ValueError) as e:
        state.recovery_write_error_message = str(e)
        _refresh_recovery_error_state()


def do_new():
    if not _clear_recovery_file():
        cleanup_detail = state.recovery_error_message or "Unknown recovery cleanup error."
        _reprotect_after_blocked_cleanup()
        show_message(
            "Recovery cleanup error",
            "Carriage could not safely retire the previous recovery journal, "
            "so the current document has been left open and re-protected. Fix "
            "the recovery storage problem and try New again.\n\n"
            f"{cleanup_detail}",
        )
        return
    text_area.buffer.reset(Document(text=""))
    state.path = None
    state.saved_text = ""
    state.disk_snapshot = None
    state.tables = {}
    state.footnotes = {}
    _reset_working_state_tracking()


def _normalized_installed_cursor_position(visible_text, cursor_position=0):
    """Return one stable visible insertion position for an installed document.

    Loading can happen before a real prompt_toolkit application is running, so
    terminal-width-dependent gutter detection is not reliable here.  The
    document's structural analysis is the source of truth for the hidden ATX,
    list, and blockquote prefix.  Compact footnote/folded-object interiors are
    normalized through the same visible-boundary rules used by navigation.
    """
    cursor_position = max(0, min(len(visible_text), int(cursor_position)))
    document = Document(visible_text, cursor_position=cursor_position)
    row = document.cursor_position_row
    row_layout = _display_row_layout(visible_text, row)
    source_col = _normalize_visual_source_col(
        document,
        row,
        document.cursor_position_col,
        structural_body_col=row_layout.structural_prefix_width,
    )
    return document.translate_row_col_to_index(row, source_col)


def _install_editor_document(
    visible_text,
    *,
    cursor_position=0,
    path,
    saved_text,
    disk_snapshot,
    tables,
    footnotes,
    reset_working_state=True,
):
    """Install one complete visible document/object state consistently.

    File-menu opening, command-line startup, and recovery restoration must all
    preserve the same cursor invariants.  Set the object maps before resetting
    the Buffer so any synchronous document callbacks observe a coherent folded
    state, then install the normalized document and its disk baseline together.
    """
    normalized_cursor = _normalized_installed_cursor_position(
        visible_text, cursor_position
    )
    state.tables = tables
    state.footnotes = footnotes
    text_area.buffer.reset(
        Document(text=visible_text, cursor_position=normalized_cursor)
    )
    state.path = path
    state.saved_text = saved_text
    state.disk_snapshot = disk_snapshot
    if reset_working_state:
        _reset_working_state_tracking()


def _install_open_document(path, content, disk_snapshot):
    """Replace the editor document with one successfully read source file."""
    visible = _collapse_objects_from_source(content)
    _install_editor_document(
        visible,
        cursor_position=0,
        path=path,
        saved_text=content,
        disk_snapshot=disk_snapshot,
        tables=state.tables,
        footnotes=state.footnotes,
    )


def do_open():
    def load_path(path, *, allow_large=False):
        try:
            content, disk_snapshot = _read_utf8_file_with_snapshot(
                path, allow_large=allow_large
            )
        except _LargeFileConfirmationRequired as e:
            confirm(
                "Large file",
                _large_file_prompt_text(path, e.size_bytes),
                lambda: load_path(path, allow_large=True),
            )
            return
        except (OSError, UnicodeError) as e:
            show_message("Error opening file", str(e))
            return

        if not _clear_recovery_file():
            cleanup_detail = state.recovery_error_message or "Unknown recovery cleanup error."
            _reprotect_after_blocked_cleanup()
            show_message(
                "Recovery cleanup error",
                "Carriage could not safely retire the current recovery journal, "
                "so the requested file was not opened. The current document has "
                "been re-protected; fix the recovery storage problem and try "
                "Open again.\n\n"
                f"{cleanup_detail}",
            )
            return
        _install_open_document(path, content, disk_snapshot)

    def cb(raw_path):
        path = os.path.expanduser(raw_path.strip())
        if not path:
            return
        if not os.path.exists(path):
            show_message("Not found", f"No such file:\n{path}")
            return
        load_path(path)

    show_input_dialog("Open File", "Path:", state.path or "", cb)


def _write_file(path, expected_snapshot, report_conflict=True, report_read_only=True):
    """Atomically save only if the destination is still the expected version."""
    try:
        content = _materialize_objects(text_area.text)
    except ValueError as e:
        show_message("Document object error", str(e))
        return _SAVE_ERROR

    content_bytes = content.encode("utf-8")
    target_path = _canonical_path(path)

    try:
        current_snapshot = _disk_snapshot(target_path)
        if current_snapshot != expected_snapshot:
            if report_conflict:
                show_message(
                    "File changed on disk",
                    "The destination changed before Carriage could save it. "
                    "Nothing was overwritten. Try Save again and choose how "
                    "to resolve the conflict.",
                )
            return _SAVE_CONFLICT

        if (
            current_snapshot != _MISSING_DISK_SNAPSHOT
            and _path_is_read_only(target_path)
        ):
            if report_read_only:
                show_message(
                    "Read-only file",
                    "The destination is marked read-only. Nothing was overwritten. "
                    "Choose Save As and use a different filename.",
                )
            return _SAVE_READ_ONLY

        if current_snapshot != _MISSING_DISK_SNAPSHOT:
            existing_stat = os.stat(target_path)
            if existing_stat.st_nlink > 1:
                show_message(
                    "Linked file",
                    "This file has multiple hard links. Carriage's atomic Save would "
                    "break that link relationship, so nothing was overwritten. "
                    "Use Save As to write a separate file instead.",
                )
                return _SAVE_ERROR

        def write_staged(temp_path):
            with open(temp_path, "w", encoding="utf-8", newline="") as f:
                f.write(content)
                f.flush()

        def validate_before_replace():
            # Recheck after the staged file is complete and its metadata has
            # been prepared. If another program changed the destination while
            # Save was in progress, the shared helper discards the stage.
            if _disk_snapshot(target_path) != expected_snapshot:
                if report_conflict:
                    show_message(
                        "File changed on disk",
                        "The destination changed while Carriage was saving. "
                        "Nothing was overwritten. Try Save again and choose "
                        "how to resolve the conflict.",
                    )
                return _SAVE_CONFLICT

            if (
                expected_snapshot != _MISSING_DISK_SNAPSHOT
                and _path_is_read_only(target_path)
            ):
                if report_read_only:
                    show_message(
                        "Read-only file",
                        "The destination became read-only while Carriage was saving. "
                        "Nothing was overwritten. Choose Save As and use a different filename.",
                    )
                return _SAVE_READ_ONLY
            return None

        try:
            _durable_atomic_replace(
                target_path,
                write_staged,
                temp_suffix=".tmp",
                new_file_mode=_new_file_mode_from_umask(),
                preserve_existing_metadata=True,
                reject_hardlinks=True,
                validate_before_replace=validate_before_replace,
            )
        except _AtomicReplaceCancelled as cancelled:
            return cancelled.result
        except _AtomicReplaceHardLinkError:
            show_message(
                "Linked file",
                "This file acquired multiple hard links while Carriage was saving. "
                "Nothing was overwritten. Use Save As to write a separate file instead.",
            )
            return _SAVE_ERROR
        except _AtomicReplaceDurabilityError as durability_error:
            state.path = path
            state.disk_snapshot = _snapshot_bytes(content_bytes)

            recovery_detail = (
                "The new file is visible on disk, but Carriage could not "
                "confirm that the directory update is durable. The document "
                "will remain marked modified and Save can be tried again."
            )
            try:
                _write_recovery_snapshot()
            except (OSError, UnicodeError, TypeError, ValueError) as recovery_error:
                state.recovery_write_error_message = str(recovery_error)
                _refresh_recovery_error_state()
                recovery_detail += (
                    "\n\nCarriage also could not update working-state recovery: "
                    f"{recovery_error}"
                )
            else:
                state.recovery_write_error_message = None
                _refresh_recovery_error_state()
                recovery_detail += "\n\nWorking-state recovery has been retained."

            show_message(
                "Save durability warning",
                f"{recovery_detail}\n\nDirectory flush error: "
                f"{durability_error.original_error}",
            )
            return _SAVE_DURABILITY_ERROR

        state.saved_text = content
        state.path = path
        state.disk_snapshot = _snapshot_bytes(content_bytes)
        _clear_recovery_file()
        _reset_working_state_tracking()
        return _SAVE_OK
    except (OSError, UnicodeError) as e:
        show_message("Error saving file", str(e))
        return _SAVE_ERROR

def do_save(on_saved=None):
    if state.path is None:
        do_save_as(on_saved)
        return

    try:
        disk_snapshot = _disk_snapshot(state.path)
    except OSError as e:
        show_message("Error checking file", str(e))
        return

    if state.disk_snapshot is None:
        # This can only occur for an unusual state created by older code or a
        # future caller. Fail safe by treating the version visible right now
        # as the one that must remain unchanged during this save.
        state.disk_snapshot = disk_snapshot

    # Conflict detection always comes before the unchanged fast path. Pressing
    # Save must never silently bless an externally changed file merely because
    # the in-memory document itself has not changed.
    if disk_snapshot != state.disk_snapshot:
        _show_save_conflict(disk_snapshot, on_saved)
        return

    # A verified unchanged document is already saved. Do not replace the inode,
    # touch mtime, disturb hard links, or expose file metadata to an unnecessary
    # atomic replacement. A read-only file is also fine here because no write is
    # required.
    if not state.is_modified(text_area.text):
        if not _has_recoverable_changes():
            _clear_recovery_file()
            _reset_working_state_tracking()
        if on_saved:
            on_saved()
        return

    try:
        if _path_is_read_only(state.path):
            _show_read_only_save(on_saved)
            return
    except OSError as e:
        show_message("Error checking file", str(e))
        return

    result = _write_file(state.path, expected_snapshot=state.disk_snapshot)
    if result == _SAVE_OK and on_saved:
        on_saved()


_PORTABLE_FILENAME_INVALID_RE = re.compile(r'[<>:"/\\|?*\x00-\x1f\x7f]+')
_WINDOWS_RESERVED_FILENAME_RE = re.compile(
    r"^(?:CON|PRN|AUX|NUL|COM[1-9]|LPT[1-9])(?:\.|$)", re.IGNORECASE
)
_MARKDOWN_ESCAPABLE_PUNCTUATION = frozenset(string.punctuation)
_FILENAME_COMPONENT_MAX_BYTES = 240
_FILENAME_NOUN_ENDING_LOOKBACK_WORDS = 8
_FILENAME_LOW_INFORMATION_END_WORDS = frozenset(
    """
    a an the and or but nor for so yet as at by from in into of off on onto per
    than through to toward towards under with within without about above after
    before behind below between beyond during over across around this that these
    those my your his her its our their some any each every either neither no not
    is are was were am be been being do does did have has had can could may might
    must shall should will would very more most less least much many few several
    such other another
    """.split()
)
_FILENAME_COMMON_MODIFIER_END_WORDS = frozenset(
    """
    new old great little large small long short high low early late current recent
    final first second third last next previous important possible available
    different similar general specific major minor primary secondary national
    international local federal private military political economic social legal
    technical historical historic modern northern southern eastern western central
    middle upper lower inner outer former latter main overall additional extra
    further entire whole single multiple various particular common basic advanced
    simple complex complete partial detailed broad narrow
    """.split()
)
_FILENAME_NOUNISH_SUFFIXES = (
    "tion", "sion", "ment", "ness", "ity", "ism", "ist", "ship",
    "ance", "ence", "hood", "dom", "age", "ery", "ure", "graphy",
    "logy", "ics",
)
_FILENAME_MODIFIERISH_SUFFIXES = (
    "ly", "ous", "ive", "able", "ible", "ful", "less", "ish", "ical",
)


def _remove_source_ranges(text, ranges):
    """Delete sorted/overlapping source ranges without disturbing other text."""
    merged = _merge_source_ranges(ranges)
    if not merged:
        return text
    result = []
    cursor = 0
    for start, end in merged:
        start = max(cursor, max(0, start))
        end = max(start, min(len(text), end))
        result.append(text[cursor:start])
        cursor = end
    result.append(text[cursor:])
    return "".join(result)


def _strip_explicit_link_markup(text):
    """Return inline source with explicit link/image syntax reduced to labels.

    Only constructs that prove they are links/images by carrying an inline
    destination or second reference label are changed. Plain bracketed prose is
    kept byte-for-byte because Carriage does not resolve shortcut references
    merely to propose a filename.
    """
    if "[" not in text or "]" not in text:
        return text

    escaped = _escaped_source_positions(text)
    code_ranges = _inline_code_span_ranges(text)
    remove = []
    stack = []
    code_index = 0
    i = 0
    n = len(text)

    while i < n:
        while code_index < len(code_ranges) and code_ranges[code_index][1] <= i:
            code_index += 1
        if code_index < len(code_ranges):
            range_start, range_end = code_ranges[code_index]
            if range_start <= i < range_end:
                i = range_end
                continue

        if i in escaped:
            i += 1
            continue

        char = text[i]
        if char == "[":
            stack.append(i)
            i += 1
            continue
        if char != "]" or not stack:
            i += 1
            continue

        open_index = stack.pop()
        next_index = i + 1
        destination_end = None
        reference_end = None

        if next_index < n and text[next_index] == "(":
            destination_end = _scan_inline_link_destination(
                text, next_index, escaped
            )
        else:
            probe = next_index
            while probe < n and text[probe] in " \t":
                probe += 1
            if probe < n and text[probe] == "[" and probe not in escaped:
                reference_end = _scan_reference_label(text, probe, escaped)

        if destination_end is None and reference_end is None:
            i += 1
            continue

        remove.extend(((open_index, open_index + 1), (i, i + 1)))
        if (
            open_index > 0
            and text[open_index - 1] == "!"
            and open_index - 1 not in escaped
        ):
            remove.append((open_index - 1, open_index))
        if destination_end is not None:
            remove.append((next_index, destination_end))
            i = destination_end
        else:
            # The optional whitespace and second reference label are syntax,
            # not visible heading text.
            remove.append((next_index, reference_end))
            i = reference_end

    return _remove_source_ranges(text, remove)


def _strip_emphasis_markup(text):
    """Remove recognized emphasis delimiters while preserving their content."""
    if "*" not in text and "_" not in text:
        return text
    protected = _inline_code_span_ranges(text)
    spans = _emphasis_spans_in_range(text, 0, len(text), protected=protected)
    remove = []
    for open_start, open_end, close_start, close_end, _marker, _count in spans:
        remove.extend(((open_start, open_end), (close_start, close_end)))
    return _remove_source_ranges(text, remove)


def _render_inline_code_plain(text):
    """Replace complete Markdown code spans with the text they display."""
    ranges = _inline_code_span_ranges(text)
    if not ranges:
        return text
    result = []
    cursor = 0
    for start, end in ranges:
        result.append(text[cursor:start])
        marker_end = start + 1
        while marker_end < end and text[marker_end] == "`":
            marker_end += 1
        marker_len = marker_end - start
        content = text[marker_end:end - marker_len]
        content = re.sub(r"[ \t\n]+", " ", content)
        if (
            len(content) >= 2
            and content.startswith(" ")
            and content.endswith(" ")
            and content.strip()
        ):
            content = content[1:-1]
        result.append(content)
        cursor = end
    result.append(text[cursor:])
    return "".join(result)


def _unescape_markdown_punctuation(text):
    """Remove Markdown backslash escaping for punctuation visible in headings."""
    result = []
    i = 0
    while i < len(text):
        if (
            text[i] == "\\"
            and i + 1 < len(text)
            and text[i + 1] in _MARKDOWN_ESCAPABLE_PUNCTUATION
        ):
            result.append(text[i + 1])
            i += 2
            continue
        result.append(text[i])
        i += 1
    return "".join(result)


def _plain_heading_text(title):
    """Return conservative human-visible text for one ATX heading title."""
    text = _strip_explicit_link_markup(str(title))
    text = _strip_emphasis_markup(text)
    text = _render_inline_code_plain(text)

    # Autolinks display their destination without angle brackets. Raw inline
    # HTML tags themselves are not visible; their text content remains.
    text = _AUTOLINK_RE.sub(lambda match: match.group(0)[1:-1], text)
    text = re.sub(r"</?[A-Za-z][^>\n]*>", "", text)
    text = _unescape_markdown_punctuation(text)
    text = _html_unescape(text)
    return " ".join(text.split()).strip()


def _subtitle_colon_index(text):
    """Return the first visible title/subtitle colon, ignoring URL schemes."""
    for index, char in enumerate(text):
        if char != ":":
            continue

        # A visible autolink can legitimately contribute ``https://...`` to a
        # heading. Do not mistake that URI-scheme colon for a title/subtitle
        # separator. Other colons follow the filename policy: the text before
        # the first one is the title used for Save As.
        token_start = index
        while token_start > 0 and not text[token_start - 1].isspace():
            token_start -= 1
        scheme = text[token_start:index]
        if (
            text[index + 1:index + 3] == "//"
            and re.fullmatch(r"[A-Za-z][A-Za-z0-9+.-]*", scheme)
        ):
            continue
        return index
    return None


def _filename_terminal_word_score(token):
    """Return a small heuristic score for a descriptive truncation endpoint.

    Carriage intentionally does not add a part-of-speech dependency merely to
    suggest a filename. Instead, favor words that are likely nouns/content
    words, strongly favor common noun-forming suffixes, and avoid ending on
    articles, prepositions, auxiliaries, adverbs, or obvious modifiers.
    """
    word = token.strip(" \t\r\n.,;!?()[]{}'\"-_–—")
    if not word or not any(char.isalnum() for char in word):
        return 0
    lowered = word.casefold()
    if lowered in _FILENAME_LOW_INFORMATION_END_WORDS:
        return 0
    if lowered in _FILENAME_COMMON_MODIFIER_END_WORDS:
        return 1
    if lowered.endswith(_FILENAME_NOUNISH_SUFFIXES):
        return 4
    if lowered.endswith(_FILENAME_MODIFIERISH_SUFFIXES):
        return 1
    # Gerunds/participles can themselves be nouns ("writing", "building"),
    # so keep them preferable to a function word without calling them strong
    # noun candidates.
    if lowered.endswith(("ing", "ed")):
        return 2
    return 3


def _truncate_filename_stem(
    stem, extension, max_bytes=_FILENAME_COMPONENT_MAX_BYTES
):
    """Truncate at a useful word boundary while preserving the extension.

    Prefer the nearest noun-like/content-word endpoint among the last few words
    that fit. This keeps long generated names descriptive and, for ordinary
    spaced prose, guarantees truncation never cuts through a word. A pathological
    single token longer than the entire filesystem component budget falls back
    to UTF-8-safe character truncation because no word boundary exists.
    """
    budget = max(1, int(max_bytes) - len(extension.encode("utf-8")))
    if len(stem.encode("utf-8")) <= budget:
        return stem

    candidates = []
    for match in re.finditer(r"\S+", stem):
        end = match.end()
        if len(stem[:end].encode("utf-8")) > budget:
            break
        candidates.append((end, _filename_terminal_word_score(match.group(0))))

    if candidates:
        window = candidates[-_FILENAME_NOUN_ENDING_LOOKBACK_WORDS:]
        chosen_end = candidates[-1][0]
        # Prefer the latest noun-like/content-word endpoint so the filename
        # keeps as much of the title as possible. If none is available nearby,
        # a gerund/participle is still preferable to ending on a function word
        # or obvious modifier.
        match = next(
            (end for end, score in reversed(window) if score >= 3),
            None,
        )
        if match is None:
            match = next(
                (end for end, score in reversed(window) if score >= 2),
                None,
            )
        if match is not None:
            chosen_end = match
        return stem[:chosen_end].rstrip(" .,-;_–—")

    # Extremely long unbroken tokens have no meaningful word boundary to use.
    # Preserve as much UTF-8-safe text as the component limit permits.
    return stem.encode("utf-8")[:budget].decode("utf-8", errors="ignore").rstrip(" .")


def _portable_markdown_filename(title):
    """Return a human-readable portable Markdown filename for heading text."""
    filename = _plain_heading_text(title)
    colon_index = _subtitle_colon_index(filename)
    if colon_index is not None and filename[:colon_index].strip():
        filename = filename[:colon_index].rstrip()
    filename = _PORTABLE_FILENAME_INVALID_RE.sub("-", filename)
    filename = " ".join(filename.split()).strip().rstrip(" .")
    if not filename or filename in {".", ".."}:
        return ""

    if filename.lower().endswith(".md"):
        stem, extension = filename[:-3], filename[-3:]
    else:
        stem, extension = filename, ".md"

    stem = stem.rstrip(" .")
    if not stem:
        return ""
    stem = _truncate_filename_stem(stem, extension)
    if not stem:
        return ""

    candidate = stem + extension
    if _WINDOWS_RESERVED_FILENAME_RE.match(candidate):
        candidate = "_" + candidate
    return candidate


def _suggested_new_document_filename():
    """Return a portable filename suggestion from the first real ATX heading.

    The shared block classifier excludes apparent headings inside YAML, code,
    raw HTML, blockquotes, and other non-heading blocks. Inline Markdown is
    reduced conservatively to the text a reader sees, then only filename-unsafe
    characters are neutralized; the title is not slugified.
    """
    if state.path is not None:
        return state.path

    for block in _analyze_document_layout(text_area.text, WRAP_COLUMN):
        if block.kind != "heading" or not block.source_lines:
            continue
        title = _heading_title(block.source_lines[0])
        if not title:
            continue
        return _portable_markdown_filename(title)

    return ""


def do_save_as(on_saved=None):
    def cb(raw_path):
        path = os.path.expanduser(raw_path.strip())
        if not path:
            return

        # Entering the current document's pathname should use ordinary Save,
        # including its external-change conflict handling.
        if state.path is not None and _same_document_path(path, state.path):
            do_save(on_saved)
            return

        try:
            destination_snapshot = _disk_snapshot(path)
            if (
                destination_snapshot != _MISSING_DISK_SNAPSHOT
                and _path_is_read_only(path)
            ):
                show_message(
                    "Read-only destination",
                    "That file is marked read-only, so Carriage will not replace it. "
                    "Choose a different Save As filename.",
                )
                return
        except OSError as e:
            show_message("Error checking destination", str(e))
            return

        def write_destination():
            result = _write_file(path, expected_snapshot=destination_snapshot)
            if result == _SAVE_OK and on_saved:
                on_saved()

        if destination_snapshot != _MISSING_DISK_SNAPSHOT:
            _confirm_replace(
                "Replace existing file?",
                f"A file already exists at:\n{path}\n\nReplace it with the current document?",
                write_destination,
            )
        else:
            write_destination()

    show_input_dialog("Save As", "Path:", state.path or _suggested_new_document_filename(), cb)


def do_quit():
    if state.pandoc_export_running:
        show_message(
            "Export in progress",
            "Pandoc is still exporting. Finish the export before quitting Carriage.",
        )
        return
    if not _clear_recovery_file():
        cleanup_detail = state.recovery_error_message or "Unknown recovery cleanup error."
        _reprotect_after_blocked_cleanup()
        show_message(
            "Recovery cleanup error",
            "Carriage could not safely retire the recovery journal, so it has "
            "not quit. Unsaved work has been re-protected; fix the recovery "
            "storage problem and try Quit again.\n\n"
            f"{cleanup_detail}",
        )
        return
    get_app().exit()


# ---------------------------------------------------------------------------
# Prose layout, conversion, and hard-wrap export
# ---------------------------------------------------------------------------

# Normal editing is soft-wrapped and never reformats source automatically.
# This section implements the hard-wrapped Markdown export formatter and the
# shared Markdown structure metadata used by the display layer. Hard-wrap export
# preserves only the short set of line-sensitive constructs defined below.

_ATX_HEADING_RE = re.compile(r"^#{1,6}(?!#)(?=.*\S)")
_SETEXT_H1_RE = re.compile(r"^=+[ \t]*$")
_SETEXT_H2_RE = re.compile(r"^-+[ \t]*$")
_LIST_ITEM_RE = re.compile(r"^(\s{0,3}(?:[-*+]|\d+\.)\s+)")
_REFERENCE_DEF_RE = re.compile(r"^\s{0,3}\[[^\]]+\]:\s*\S")
_REFERENCE_TITLE_START_RE = re.compile(r"^\s{0,3}(?P<delim>[\"'(])")
_FENCE_OPEN_RE = re.compile(r"^\s{0,3}(`{3,}|~{3,})")
_YAML_OPEN_RE = re.compile(r"^---\s*$")
_YAML_CLOSE_RE = re.compile(r"^(?:---|\.\.\.)\s*$")
_RAW_HTML_TAG_RE = re.compile(
    r"^\s{0,3}<(?P<tag>script|pre|style|textarea)(?:\s|>|$)", re.IGNORECASE
)
_BLOCK_HTML_TAG_RE = re.compile(
    r"^\s{0,3}</?(?P<tag>address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?:\s|/?>|$)",
    re.IGNORECASE,
)


def _fence_marker(line):
    match = _FENCE_OPEN_RE.match(line)
    if not match:
        return None
    marker = match.group(1)
    return marker[0], len(marker)


def _is_fence_close(line, fence_char, minimum_length):
    pattern = rf"^\s{{0,3}}{re.escape(fence_char)}{{{minimum_length},}}\s*$"
    return bool(re.match(pattern, line))


def _yaml_front_matter_end(lines):
    """Return the index after a complete leading YAML block, or None."""
    if not lines or not _YAML_OPEN_RE.match(lines[0]):
        return None
    for index in range(1, len(lines)):
        if _YAML_CLOSE_RE.match(lines[index]):
            return index + 1
    return None


def _prose_contains_multiline_inline_code(source_lines):
    """Return True when an inline code span crosses a physical source newline.

    Convert for Carriage deliberately leaves such prose source unchanged.  A
    newline and any adjacent spaces inside an original-Markdown code span are
    literal code content, so treating that physical boundary as wrapping (or as
    a two-space hard break) would rewrite the code span itself.
    """
    if len(source_lines) < 2:
        return False
    text = "\n".join(source_lines)
    for start, end in _inline_code_span_ranges(text):
        if "\n" in text[start:end]:
            return True
    return False


def _hard_break_marker(line):
    """Return the original-Markdown hard-break marker at line end, if present.

    Carriage's conversion contract follows the original Markdown syntax here:
    two or more trailing spaces create a hard line break. A trailing backslash
    is treated as ordinary source text rather than as alternate break syntax.
    """
    trailing_spaces = len(line) - len(line.rstrip(" "))
    return "  " if trailing_spaces >= 2 else None


def _strip_hard_break_marker(line, marker):
    if marker == "  ":
        return line.rstrip(" ")
    return line


def _prose_heading_guard(line):
    """Return leading whitespace that keeps a literal # line from becoming ATX.

    Original Markdown ATX headings begin in column zero. Convert for Carriage
    normally removes incidental wrapping indentation, but it must retain the
    one-to-three leading spaces that are semantically preventing an ordinary
    prose line from becoming a heading.
    """
    match = re.match(r"^(?P<indent>[ \t]{1,3})#", line)
    return match.group("indent") if match is not None else ""


def _wrap_markdown_prose(source_lines, width, initial_indent="", subsequent_indent=""):
    """Wrap prose while preserving explicit Markdown hard line breaks."""
    if _prose_contains_multiline_inline_code(source_lines):
        return list(source_lines)

    segments = []
    current = []
    current_guard = ""

    for raw_line in source_lines:
        if not current:
            current_guard = _prose_heading_guard(raw_line)
        marker = _hard_break_marker(raw_line)
        text = _strip_hard_break_marker(raw_line, marker)
        current.append(text.strip())
        if marker is not None:
            segments.append((" ".join(part for part in current if part), marker, current_guard))
            current = []
            current_guard = ""

    if current or not segments:
        segments.append((" ".join(part for part in current if part), None, current_guard))

    rendered = []
    for segment_text, marker, guard in segments:
        base_indent = initial_indent if not rendered else subsequent_indent
        first_indent = base_indent + guard
        wrapped = textwrap.wrap(
            segment_text,
            width=width,
            initial_indent=first_indent,
            subsequent_indent=subsequent_indent,
            break_long_words=False,
            break_on_hyphens=False,
        ) or [first_indent.rstrip()]
        if marker is not None:
            wrapped[-1] += marker
        rendered.extend(wrapped)

    return rendered


def _is_thematic_break(line):
    stripped = line.strip()
    if not stripped:
        return False
    compact = stripped.replace(" ", "").replace("\t", "")
    return (
        len(compact) >= 3
        and len(set(compact)) == 1
        and compact[0] in "-*_"
    )


def _is_indented_code(line):
    return line.startswith("    ") or line.startswith("\t")


def _is_strong_html_start(line):
    """
    Recognize only unmistakable block-level raw HTML.

    Inline tags and autolinks such as <em> or <https://example.com> remain
    ordinary prose. We deliberately avoid generic HTML-tag recognition here.
    """
    stripped = line.lstrip()
    return bool(
        _RAW_HTML_TAG_RE.match(line)
        or _BLOCK_HTML_TAG_RE.match(line)
        or stripped.startswith(("<!--", "<?", "<![CDATA["))
        or re.match(r"<![A-Z]", stripped)
    )


def _contains_unescaped_pipe(line):
    escaped = False
    for char in line:
        if char == "\\":
            escaped = not escaped
            continue
        if char == "|" and not escaped:
            return True
        escaped = False
    return False


def _split_unescaped_pipes(line):
    cells = []
    current = []
    escaped = False
    for char in line:
        if char == "\\":
            current.append(char)
            escaped = not escaped
            continue
        if char == "|" and not escaped:
            cells.append("".join(current))
            current = []
        else:
            current.append(char)
        escaped = False
    cells.append("".join(current))
    return cells


def _is_pipe_table_separator(line):
    if not _contains_unescaped_pipe(line):
        return False
    stripped = line.strip()
    cells = _split_unescaped_pipes(stripped)
    if stripped.startswith("|"):
        cells = cells[1:]
    if stripped.endswith("|"):
        cells = cells[:-1]
    return len(cells) >= 2 and all(
        re.fullmatch(r"\s*:?-{3,}:?\s*", cell) for cell in cells
    )


def _is_pipe_table_start(lines, index):
    return (
        index + 1 < len(lines)
        and _contains_unescaped_pipe(lines[index])
        and _is_pipe_table_separator(lines[index + 1])
    )


def _nonblank_run_end(lines, index):
    i = index
    while i < len(lines) and lines[i].strip():
        i += 1
    return i


def _collect_fenced_block(lines, index):
    """Collect a fenced block, preserving source if the caller is mistaken.

    Normal callers establish ``_fence_marker(lines[index])`` first.  Keep this
    helper defensive anyway: if parser assumptions ever diverge, treating the
    current line as an opaque one-line block is safer than raising from
    ``*marker`` and interrupting conversion/opening of an otherwise readable
    document.
    """
    marker = _fence_marker(lines[index])
    if marker is None:
        return [lines[index]], index + 1

    block = [lines[index]]
    index += 1
    while index < len(lines):
        block.append(lines[index])
        if _is_fence_close(lines[index], *marker):
            index += 1
            break
        index += 1
    return block, index


def _collect_html_block(lines, index):
    """Collect unmistakable raw HTML verbatim; do not reflow its contents.

    Block-level elements are tracked through the matching close of the outer
    element, including nested elements with the same tag name. This is still
    boundary detection rather than HTML formatting: Carriage preserves the
    collected source text exactly as written.
    """
    first = lines[index]
    raw_match = _RAW_HTML_TAG_RE.match(first)
    if raw_match:
        tag = raw_match.group("tag")
        close_re = re.compile(rf"</{re.escape(tag)}\s*>", re.IGNORECASE)
        block = [first]
        index += 1
        if close_re.search(first):
            return block, index
        while index < len(lines):
            block.append(lines[index])
            if close_re.search(lines[index]):
                index += 1
                break
            index += 1
        return block, index

    stripped = first.lstrip()
    terminator = None
    if stripped.startswith("<!--"):
        terminator = "-->"
    elif stripped.startswith("<?"):
        terminator = "?>"
    elif stripped.startswith("<![CDATA["):
        terminator = "]]>"
    elif re.match(r"<![A-Z]", stripped):
        terminator = ">"

    if terminator is not None:
        block = [first]
        index += 1
        if terminator in first:
            return block, index
        while index < len(lines):
            block.append(lines[index])
            if terminator in lines[index]:
                index += 1
                break
            index += 1
        return block, index

    block_match = _BLOCK_HTML_TAG_RE.match(first)
    if block_match:
        stripped_first = first.lstrip()
        tag = block_match.group("tag").lower()
        void_tags = {"base", "basefont", "col", "frame", "hr", "link", "param", "track"}
        if (
            stripped_first.startswith("</")
            or tag in void_tags
            or re.search(r"/\s*>\s*$", first)
        ):
            return [first], index + 1

        class _OuterTagTracker(HTMLParser):
            def __init__(self, target_tag):
                super().__init__(convert_charrefs=False)
                self.target_tag = target_tag
                self.depth = 0
                self.seen_start = False

            def handle_starttag(self, found_tag, attrs):
                if found_tag.lower() == self.target_tag:
                    self.seen_start = True
                    self.depth += 1

            def handle_startendtag(self, found_tag, attrs):
                # A self-closing nested tag does not change the outer depth.
                pass

            def handle_endtag(self, found_tag):
                if found_tag.lower() == self.target_tag and self.seen_start:
                    self.depth = max(0, self.depth - 1)

        tracker = _OuterTagTracker(tag)
        block = []
        while index < len(lines):
            line = lines[index]
            block.append(line)
            try:
                # Feed incrementally so quoted attributes, comments, and tags
                # split across source lines are handled by the stdlib parser.
                tracker.feed(line + "\n")
            except Exception:
                # Malformed HTML should be preserved rather than exposed to
                # prose reflow. Treat the remainder of the document as opaque.
                block.extend(lines[index + 1:])
                return block, len(lines)
            index += 1
            if tracker.seen_start and tracker.depth == 0:
                break
        return block, index

    return [first], index + 1


def _collect_pipe_table(lines, index):
    block = [lines[index], lines[index + 1]]
    index += 2
    while index < len(lines):
        line = lines[index]
        if not line.strip() or not _contains_unescaped_pipe(line):
            break
        block.append(line)
        index += 1
    return block, index


def _table_caption_title(line):
    """Return a single-line Pandoc table caption without its marker."""
    match = _TABLE_CAPTION_RE.match(line)
    return match.group("title").strip() if match else None


def _captioned_pipe_table_at(lines, index):
    """Return a pipe table plus an optional adjacent Pandoc caption.

    Carriage accepts a one-line caption beginning with ``Table:``, ``table:``,
    or ``:`` immediately before or after a pipe table, with at most one blank
    line between the caption and table. The complete original region is kept
    so an untouched table round-trips byte-for-byte.
    """
    if not (0 <= index < len(lines)):
        return None

    full_start = index
    table_index = index
    title = None
    caption_position = None

    possible_title = _table_caption_title(lines[index])
    if possible_title is not None:
        table_index = index + 1
        if table_index < len(lines) and not lines[table_index].strip():
            table_index += 1
        if table_index >= len(lines) or not _is_pipe_table_start(lines, table_index):
            return None
        title = possible_title
        caption_position = "before"
    elif not _is_pipe_table_start(lines, index):
        return None

    table_lines, table_end = _collect_pipe_table(lines, table_index)
    full_end = table_end

    if caption_position is None:
        caption_index = table_end
        if caption_index < len(lines) and not lines[caption_index].strip():
            caption_index += 1
        if caption_index < len(lines):
            possible_title = _table_caption_title(lines[caption_index])
            if possible_title is not None:
                title = possible_title
                caption_position = "after"
                full_end = caption_index + 1

    return {
        "table_lines": table_lines,
        "title": title or "",
        "caption_position": caption_position,
        "original_lines": list(lines[full_start:full_end]),
        "end": full_end,
    }


# ---------------------------------------------------------------------------
# Folded table objects
# ---------------------------------------------------------------------------

def _table_placeholder(table_number, title=""):
    """Return the editor-buffer representation of a folded table."""
    clean_title = " ".join(str(title).splitlines()).strip()
    if clean_title:
        return f"[[Table {table_number}: {clean_title}]]{TABLE_SENTINEL}"
    return f"[[Table {table_number}]]{TABLE_SENTINEL}"


def _unescape_markdown_table_cell(text):
    """Decode only the pipe-escaping scheme used by Carriage tables.

    An escaped literal pipe is encoded with an odd run of backslashes. Carriage
    uses 2n+1 backslashes to represent n literal backslashes immediately before
    a literal pipe. Backslashes elsewhere remain source text and are never
    normalized, so Markdown escapes such as ``\\*`` keep their meaning.
    """
    result = []
    i = 0
    while i < len(text):
        if text[i] != "\\":
            result.append(text[i])
            i += 1
            continue

        j = i
        while j < len(text) and text[j] == "\\":
            j += 1
        count = j - i
        if j < len(text) and text[j] == "|" and count % 2 == 1:
            result.append("\\" * ((count - 1) // 2))
            result.append("|")
            i = j + 1
        else:
            result.append("\\" * count)
            i = j
    return "".join(result)


def _table_cells_from_line(line):
    """Split one pipe-table row into trimmed, decoded cells."""
    stripped = line.strip()
    cells = _split_unescaped_pipes(stripped)
    if stripped.startswith("|"):
        cells = cells[1:]
    if stripped.endswith("|"):
        cells = cells[:-1]
    return [_unescape_markdown_table_cell(cell.strip()) for cell in cells]


def _alignment_from_separator_cell(cell):
    stripped = cell.strip()
    left = stripped.startswith(":")
    right = stripped.endswith(":")
    if left and right:
        return "center"
    if right:
        return "right"
    if left:
        return "left"
    return "default"


_GRID_TABLE_BORDER_RE = re.compile(r"^\s*\+(?:[-=:]{3,}\+){2,}\s*$")
_SIMPLE_TABLE_SEPARATOR_RE = re.compile(
    r"^\s*:?-{3,}:?(?:[ \t]{2,}:?-{3,}:?)+\s*$"
)
_FENCED_DIV_RE = re.compile(r"^\s{0,3}(?P<fence>:{3,})(?P<tail>[ \t].*)?$")
_DEFINITION_LIST_MARKER_RE = re.compile(r"^\s{0,3}[:~][ \t]+\S")


def _pipe_row_shape(line):
    """Return lightweight shape data for one plausible pipe-table row."""
    if not line.strip() or not _contains_unescaped_pipe(line):
        return None
    stripped = line.strip()
    cells = _split_unescaped_pipes(stripped)
    if stripped.startswith("|"):
        cells = cells[1:]
    if stripped.endswith("|"):
        cells = cells[:-1]
    if len(cells) < 2:
        return None
    delimiter_count = len(_split_unescaped_pipes(stripped)) - 1
    outer_bar = stripped.startswith("|") or stripped.endswith("|")
    return len(cells), delimiter_count, outer_bar


def _unsupported_pipe_table_end(lines, index):
    """Return the end of a headerless/unsupported pipe-row run, if plausible.

    Standard header/separator pipe tables are handled by Carriage's real table
    parser. This recognizer exists only to keep consecutive table-shaped rows
    line-sensitive under Convert/Hard-Wrapped export. A lone prose line that
    happens to contain a pipe remains ordinary prose.
    """
    if not (0 <= index < len(lines)) or _is_pipe_table_start(lines, index):
        return None

    if _pipe_row_shape(lines[index]) is None:
        return None

    end = index
    while end < len(lines) and lines[end].strip():
        if _pipe_row_shape(lines[end]) is None:
            break
        end += 1

    return end if end - index >= 2 else None


def _grid_table_end(lines, index):
    """Return the end of a Pandoc-style grid table beginning at ``index``."""
    if not (0 <= index < len(lines)) or not _GRID_TABLE_BORDER_RE.match(lines[index]):
        return None

    end = index + 1
    saw_content = False
    while end < len(lines) and lines[end].strip():
        stripped = lines[end].strip()
        if _GRID_TABLE_BORDER_RE.match(lines[end]):
            pass
        elif stripped.startswith("|") and stripped.endswith("|"):
            saw_content = True
        else:
            break
        end += 1

    if not saw_content or end - index < 2:
        return None
    # Preserve even an incomplete grid table. Convert is deliberately
    # conservative around table-shaped extension syntax and should never repair
    # or flatten a malformed source block merely because its closing border is
    # missing.
    return end


def _simple_table_end(lines, index):
    """Return the end of a Pandoc-style simple table, with or without a header."""
    if not (0 <= index < len(lines)):
        return None

    if _SIMPLE_TABLE_SEPARATOR_RE.match(lines[index]):
        opening_separator = index
    elif (
        index + 1 < len(lines)
        and lines[index].strip()
        and _SIMPLE_TABLE_SEPARATOR_RE.match(lines[index + 1])
    ):
        opening_separator = index + 1
    else:
        return None

    i = opening_separator + 1
    while i < len(lines) and lines[i].strip():
        if _SIMPLE_TABLE_SEPARATOR_RE.match(lines[i]):
            # Require at least one data row between the opening and closing
            # separator. This avoids treating two adjacent dashed rulers as a
            # table.
            return i + 1 if i > opening_separator + 1 else None
        i += 1

    # A recognized opening separator plus at least one data row is sufficient
    # preservation evidence even if the closing ruler is missing.
    return i if i > opening_separator + 1 else None


def _fenced_div_end(lines, index):
    """Return the end of a Pandoc fenced-div/container block, if present."""
    if not (0 <= index < len(lines)):
        return None
    match = _FENCED_DIV_RE.match(lines[index])
    if match is None:
        return None

    minimum = len(match.group("fence"))
    depth = 1
    i = index + 1
    while i < len(lines):
        candidate = _FENCED_DIV_RE.match(lines[i])
        if candidate is not None and len(candidate.group("fence")) >= minimum:
            if candidate.group("tail") is None:
                depth -= 1
                i += 1
                if depth == 0:
                    return i
                continue
            depth += 1
        i += 1

    # Match fenced-code behavior: if the extension fence is unclosed, preserve
    # the remainder rather than reflowing unknown container contents.
    return len(lines)


def _definition_list_end(lines, index):
    """Return a conservative nonblank definition-list run beginning at a term."""
    if not (0 <= index + 1 < len(lines)) or not lines[index].strip():
        return None
    if _DEFINITION_LIST_MARKER_RE.match(lines[index + 1]) is None:
        return None
    return _nonblank_run_end(lines, index)


def _unsupported_line_sensitive_block_at(lines, index):
    """Preserve recognized extension-like structures Carriage does not edit.

    These are deliberately lightweight recognizers, not parsers. Their only
    purpose is to stop Convert for Carriage and Hard-Wrapped Markdown from
    joining physical lines whose layout is likely structural.
    """
    pipe_end = _unsupported_pipe_table_end(lines, index)
    if pipe_end is not None:
        return _WrapBlock(
            "table", index, pipe_end, list(lines[index:pipe_end]), wrappable=False
        )

    grid_end = _grid_table_end(lines, index)
    if grid_end is not None:
        return _WrapBlock(
            "table", index, grid_end, list(lines[index:grid_end]), wrappable=False
        )

    simple_end = _simple_table_end(lines, index)
    if simple_end is not None:
        return _WrapBlock(
            "table", index, simple_end, list(lines[index:simple_end]), wrappable=False
        )

    fenced_div_end = _fenced_div_end(lines, index)
    if fenced_div_end is not None:
        return _WrapBlock(
            "opaque-extension",
            index,
            fenced_div_end,
            list(lines[index:fenced_div_end]),
            wrappable=False,
        )

    definition_end = _definition_list_end(lines, index)
    if definition_end is not None:
        return _WrapBlock(
            "opaque-extension",
            index,
            definition_end,
            list(lines[index:definition_end]),
            wrappable=False,
        )

    return None


def _parse_pipe_table(block_lines):
    """Parse one supported pipe table, or return None if it is unsuitable."""
    if len(block_lines) < 2 or not _is_pipe_table_separator(block_lines[1]):
        return None

    headers = _table_cells_from_line(block_lines[0])
    separators = _table_cells_from_line(block_lines[1])
    if len(headers) < 2 or len(headers) != len(separators):
        return None

    rows = []
    for line in block_lines[2:]:
        cells = _table_cells_from_line(line)
        if len(cells) != len(headers):
            return None
        rows.append(cells)

    alignments = [_alignment_from_separator_cell(cell) for cell in separators]
    return TableData(
        headers=headers,
        rows=rows,
        title="",
        alignments=alignments,
        original_lines=list(block_lines),
        dirty=False,
    )


def _markdown_cell_text(text):
    """Serialize a cell while preserving literal backslashes and pipes."""
    compact = " ".join(str(text).splitlines()).strip()
    result = []
    i = 0
    while i < len(compact):
        if compact[i] == "\\":
            j = i
            while j < len(compact) and compact[j] == "\\":
                j += 1
            count = j - i
            if j < len(compact) and compact[j] == "|":
                # 2n+1 is always odd, so the following pipe cannot become a
                # table delimiter, and the parser can recover exactly n
                # literal backslashes before it.
                result.append("\\" * (2 * count + 1))
                result.append("|")
                i = j + 1
            else:
                result.append("\\" * count)
                i = j
            continue
        if compact[i] == "|":
            result.append("\\|")
        else:
            result.append(compact[i])
        i += 1
    return "".join(result)

def _separator_for_alignment(alignment):
    return {
        "left": ":---",
        "center": ":---:",
        "right": "---:",
    }.get(alignment, "---")


def _serialize_table(table):
    """Serialize a TableData object to compact, portable pipe Markdown."""
    if not table.dirty and table.original_lines is not None:
        return "\n".join(table.original_lines)

    column_count = table.column_count
    alignments = list(table.alignments[:column_count])
    alignments.extend(["default"] * (column_count - len(alignments)))

    def row_text(cells):
        normalized = list(cells[:column_count])
        normalized.extend([""] * (column_count - len(normalized)))
        return "| " + " | ".join(_markdown_cell_text(cell) for cell in normalized) + " |"

    lines = [row_text(table.headers)]
    lines.append("| " + " | ".join(_separator_for_alignment(a) for a in alignments) + " |")
    lines.extend(row_text(row) for row in table.rows)

    title = " ".join(table.title.splitlines()).strip()
    if title:
        caption = f": {title}"
        if table.caption_position == "before":
            lines = [caption, ""] + lines
        else:
            lines = lines + ["", caption]
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Folded prose footnotes
# ---------------------------------------------------------------------------

def _footnote_placeholder(identifier):
    """Return the editor-buffer representation of a folded footnote."""
    return f"[[Footnote: {identifier}]]{FOOTNOTE_SENTINEL}"


def _footnote_fragment_is_simple(text):
    """Return True for prose-only content suitable for the footnote editor."""
    if not text.strip():
        return True
    stripped = text.lstrip()
    return not (
        _ATX_HEADING_RE.match(text)
        or _LIST_ITEM_RE.match(text)
        or stripped.startswith(">")
        or _fence_marker(text)
        or _is_indented_code(text)
        or _is_strong_html_start(text)
        or _REFERENCE_DEF_RE.match(text)
        or _is_thematic_break(text)
        or stripped.startswith("|")
    )


def _footnote_continuation_text(line):
    """Return a canonical indented footnote continuation, or None."""
    if line.startswith("\t"):
        return line[1:]
    spaces = len(line) - len(line.lstrip(" "))
    if spaces >= 4:
        return line[4:]
    return None


def _normalize_footnote_text(text):
    """Return prose footnote text as logical paragraphs separated by blank lines.

    The note editor is multiline, but Carriage's source convention remains one
    physical source line per logical prose paragraph. A single editor newline is
    therefore treated like soft-wrapped prose and joined with a space; one or
    more blank editor lines separate paragraphs.
    """
    source = str(text).replace("\r\n", "\n").replace("\r", "\n")
    paragraphs = []
    current = []

    def finish_paragraph():
        if not current:
            return
        paragraph = " ".join(part.strip() for part in current if part.strip()).strip()
        if paragraph:
            paragraphs.append(paragraph)
        current.clear()

    for line in source.split("\n"):
        if line.strip():
            current.append(line)
        else:
            finish_paragraph()
    finish_paragraph()
    return "\n\n".join(paragraphs)


def _simple_footnote_definition_at(lines, index):
    """Return one foldable prose footnote definition, if present.

    Single- and multi-paragraph prose notes are folded. Structural footnote
    content such as lists, blockquotes, code, raw HTML, reference definitions,
    tables, or explicit Markdown hard breaks remains ordinary source.
    """
    if not (0 <= index < len(lines)):
        return None
    match = _FOOTNOTE_DEFINITION_RE.match(lines[index])
    if match is None:
        return None

    identifier = match.group(1).strip()
    first_body = match.group(2)
    if (
        not identifier
        or not _footnote_fragment_is_simple(first_body)
        or _hard_break_marker(lines[index]) is not None
    ):
        return None

    original = [lines[index]]
    paragraphs = []
    current = [first_body.strip()] if first_body.strip() else []
    i = index + 1

    def finish_paragraph():
        if not current:
            return
        paragraph = " ".join(part for part in current if part).strip()
        if paragraph:
            paragraphs.append(paragraph)
        current.clear()

    while i < len(lines):
        line = lines[i]
        if line.strip():
            continuation = _footnote_continuation_text(line)
            if continuation is None:
                break
            if (
                not _footnote_fragment_is_simple(continuation)
                or _hard_break_marker(line) is not None
            ):
                return None
            original.append(line)
            if continuation.strip():
                current.append(continuation.strip())
            i += 1
            continue

        # Blank source lines belong to this footnote only when another indented
        # continuation follows them. Otherwise leave the trailing separator in
        # the main document instead of swallowing it into the folded object.
        j = i
        while j < len(lines) and not lines[j].strip():
            j += 1
        if j >= len(lines):
            break
        continuation = _footnote_continuation_text(lines[j])
        if continuation is None:
            break
        if (
            not _footnote_fragment_is_simple(continuation)
            or _hard_break_marker(lines[j]) is not None
        ):
            return None

        finish_paragraph()
        original.extend(lines[i:j])
        i = j

    finish_paragraph()
    return {
        "identifier": identifier,
        "text": "\n\n".join(paragraphs),
        "original_lines": original,
        "end": i,
    }


def _serialize_footnote(note):
    """Serialize a folded prose FootnoteData object to standard Markdown."""
    if not note.dirty and note.original_lines is not None:
        return "\n".join(note.original_lines)

    text = _normalize_footnote_text(note.text)
    if not text:
        return f"[^{note.identifier}]:"

    paragraphs = text.split("\n\n")
    rendered = [f"[^{note.identifier}]: {paragraphs[0]}"]
    for paragraph in paragraphs[1:]:
        rendered.extend(["", f"    {paragraph}"])
    return "\n".join(rendered)


def _collapse_objects_from_source(source_text):
    """Fold supported tables and prose footnote definitions in the editor."""
    state.tables = {}
    state.footnotes = {}
    lines = source_text.split("\n")
    visible = []
    i = 0
    table_number = 1

    yaml_end = _yaml_front_matter_end(lines)
    if yaml_end is not None:
        visible.extend(lines[:yaml_end])
        i = yaml_end

    while i < len(lines):
        # Object-looking text inside code or raw HTML remains literal source.
        if _fence_marker(lines[i]):
            block, end = _collect_fenced_block(lines, i)
            visible.extend(block)
            i = end
            continue
        if _is_strong_html_start(lines[i]):
            block, end = _collect_html_block(lines, i)
            visible.extend(block)
            i = end
            continue
        if _is_indented_code(lines[i]):
            visible.append(lines[i])
            i += 1
            continue

        captioned = _captioned_pipe_table_at(lines, i)
        if captioned is not None:
            parsed = _parse_pipe_table(captioned["table_lines"])
            if parsed is not None:
                parsed.title = captioned["title"]
                parsed.caption_position = captioned["caption_position"]
                parsed.original_lines = captioned["original_lines"]
                state.tables[table_number] = parsed
                visible.append(_table_placeholder(table_number, parsed.title))
                table_number += 1
                i = captioned["end"]
                continue

        footnote = _simple_footnote_definition_at(lines, i)
        if footnote is not None and footnote["identifier"] not in state.footnotes:
            identifier = footnote["identifier"]
            state.footnotes[identifier] = FootnoteData(
                identifier=identifier,
                text=footnote["text"],
                original_lines=footnote["original_lines"],
                dirty=False,
            )
            visible.append(_footnote_placeholder(identifier))
            i = footnote["end"]
            continue

        visible.append(lines[i])
        i += 1

    return "\n".join(visible)

def _canonicalize_table_placeholders(visible_text, tables=None):
    """Return visible text with folded table labels derived from table data.

    The table object is the single source of truth for a folded table title.
    This is used when restoring working-state recovery so an in-progress title draft
    cannot leave an older placeholder label on screen.
    """
    table_map = state.tables if tables is None else tables
    rendered = []
    for line in visible_text.split("\n"):
        match = TABLE_PLACEHOLDER_RE.match(line)
        if match:
            number = int(match.group(1))
            table = table_map.get(number)
            if table is not None:
                line = _table_placeholder(number, table.title)
        rendered.append(line)
    return "\n".join(rendered)


def _materialize_objects(visible_text):
    """Expand folded tables and prose footnotes for saving/exporting."""
    rendered = []
    seen_tables = set()
    seen_footnotes = set()

    for line in visible_text.split("\n"):
        table_match = TABLE_PLACEHOLDER_RE.match(line)
        if table_match:
            table_number = int(table_match.group(1))
            if table_number in seen_tables:
                raise ValueError(
                    f"Table {table_number} appears more than once in the document. "
                    "Use one folded reference per table."
                )
            table = state.tables.get(table_number)
            if table is None:
                raise ValueError(
                    f"Table {table_number} no longer has table data attached to it."
                )
            expected_placeholder = _table_placeholder(table_number, table.title)
            if line != expected_placeholder:
                raise ValueError(
                    f"Table {table_number}'s folded reference was edited directly. "
                    "Use the table editor to change its title."
                )
            rendered.extend(_serialize_table(table).split("\n"))
            seen_tables.add(table_number)
            continue

        footnote_match = FOOTNOTE_PLACEHOLDER_RE.match(line)
        if footnote_match:
            identifier = footnote_match.group(1)
            if identifier in seen_footnotes:
                raise ValueError(
                    f"Footnote {identifier!r} appears more than once in the document. "
                    "Use one folded definition per footnote."
                )
            note = state.footnotes.get(identifier)
            if note is None:
                raise ValueError(
                    f"Footnote {identifier!r} no longer has definition data attached to it."
                )
            rendered.extend(_serialize_footnote(note).split("\n"))
            seen_footnotes.add(identifier)
            continue

        rendered.append(line)

    missing_tables = sorted(set(state.tables) - seen_tables)
    if missing_tables:
        label = ", ".join(f"Table {number}" for number in missing_tables)
        raise ValueError(
            f"{label} no longer has a folded reference in the document. "
            "Undo the deletion before saving."
        )

    missing_footnotes = sorted(set(state.footnotes) - seen_footnotes)
    if missing_footnotes:
        referenced = {
            identifier
            for _start, _end, identifier, _row, _start_col, _end_col
            in _footnote_reference_spans(visible_text)
        }
        protected_missing = [
            identifier
            for identifier in missing_footnotes
            if (
                state.footnotes[identifier].original_lines is not None
                or identifier in referenced
            )
        ]
        if protected_missing:
            label = ", ".join(repr(identifier) for identifier in protected_missing)
            raise ValueError(
                f"Footnote definition {label} no longer has a folded placeholder in the document. "
                "Undo the deletion before saving."
            )
        # A newly created footnote whose reference and placeholder were both
        # undone/deleted has no source representation to preserve. Keep its
        # in-memory object available for Redo, but omit it from materialization.

    return "\n".join(rendered)

def _folded_object_line(line):
    return bool(TABLE_PLACEHOLDER_RE.match(line) or FOOTNOTE_PLACEHOLDER_RE.match(line))


def _line_bounds_at_position(text, position):
    position = max(0, min(len(text), position))
    start = text.rfind("\n", 0, position) + 1
    end = text.find("\n", position)
    if end < 0:
        end = len(text)
    return start, end


def _folded_edit_range_intersects(text, start, end):
    """Return True when deleting [start,end) would damage a folded object.

    This is intentionally local rather than a whole-document scan because it
    runs on ordinary Backspace/Delete operations. Besides object text itself,
    the newline immediately before/after an object is protected so prose can
    never be merged onto its placeholder line.
    """
    start = max(0, min(len(text), start))
    end = max(start, min(len(text), end))
    if end <= start:
        return False

    # If either edge lies on an object line, even a one-character edit is an
    # object edit. This catches partial placeholder deletion before the hidden
    # sentinel would otherwise be reached.
    for probe in {start, max(start, end - 1)}:
        line_start, line_end = _line_bounds_at_position(text, probe)
        if _folded_object_line(text[line_start:line_end]):
            return True

    # For every deleted newline, inspect the line on each side. A newline is
    # structural when either neighbor is a folded object.
    newline = text.find("\n", start, end)
    while newline >= 0:
        prev_start = text.rfind("\n", 0, newline) + 1
        prev_line = text[prev_start:newline]
        next_end = text.find("\n", newline + 1)
        if next_end < 0:
            next_end = len(text)
        next_line = text[newline + 1:next_end]
        if _folded_object_line(prev_line) or _folded_object_line(next_line):
            return True
        newline = text.find("\n", newline + 1, end)

    return False


def _folded_insertion_locked(text, position):
    """Return True when inserting at position would edit a folded label."""
    start, end = _line_bounds_at_position(text, position)
    return _folded_object_line(text[start:end])


def _selection_intersects_folded_object(buffer):
    if buffer.selection_state is None:
        return False
    for start, end in buffer.document.selection_ranges():
        if _folded_edit_range_intersects(buffer.text, start, end):
            return True
    return False


def _buffer_folded_edit_locked(buffer, insertion=False):
    if _selection_intersects_folded_object(buffer):
        return True
    if insertion:
        return _folded_insertion_locked(buffer.text, buffer.cursor_position)
    return False


def _folded_placeholder_at_cursor(document=None):
    doc = document or text_area.buffer.document
    table_match = TABLE_PLACEHOLDER_RE.match(doc.current_line)
    if table_match:
        return "table", int(table_match.group(1))
    footnote_match = FOOTNOTE_PLACEHOLDER_RE.match(doc.current_line)
    if footnote_match:
        return "footnote", footnote_match.group(1)
    return None


def _table_number_at_cursor():
    folded = _folded_placeholder_at_cursor()
    return folded[1] if folded is not None and folded[0] == "table" else None


def _folded_placeholder_locked():
    """Return True while the caret is on a folded table/footnote object."""
    return _folded_placeholder_at_cursor() is not None


# prompt_toolkit's standard insertion/deletion bindings honor Buffer.read_only.
# Folded tables and footnote definitions are atomic labels: navigation and
# object commands remain available, while direct character edits are blocked.
text_area.buffer.read_only = Condition(
    lambda: _folded_placeholder_locked() or find_replace.active
)


def _replace_buffer_document(buffer, document):
    """Apply an internal document transformation regardless of UI read-only state.

    Folded objects deliberately make the main Buffer read-only while the caret
    is on their compact labels.  Programmatic transformations are structural
    editor operations, not character edits, so they must not depend on where
    the caret happens to be or on a caller remembering a particular guard.
    """
    buffer.set_document(document, bypass_readonly=True)


_UNCHANGED_OBJECT_MAP = object()
_UNCHANGED_SELECTION = object()
_WORKING_STATE_TRACKING_FIELDS = (
    "working_state_revision",
    "working_state_persisted_revision",
    "working_state_first_dirty_at",
    "working_state_last_change_at",
)


def _commit_folded_object_transaction(
    buffer,
    document,
    *,
    tables=_UNCHANGED_OBJECT_MAP,
    footnotes=_UNCHANGED_OBJECT_MAP,
    selection=_UNCHANGED_SELECTION,
):
    """Commit folded-object mappings and their visible document atomically.

    The object dictionaries and compact Markdown placeholders form one logical
    document state.  Build the replacement values before calling this helper;
    it captures undo/recovery bookkeeping, installs both halves, and restores
    the exact prior state if prompt_toolkit raises during document replacement.
    """
    old_document = buffer.document
    old_selection = buffer.selection_state
    old_tables = state.tables
    old_footnotes = state.footnotes
    old_undo_stack = list(buffer._undo_stack)
    old_redo_stack = list(buffer._redo_stack)
    old_tracking = {
        name: getattr(state, name) for name in _WORKING_STATE_TRACKING_FIELDS
    }

    object_changed = (
        tables is not _UNCHANGED_OBJECT_MAP and tables is not old_tables
    ) or (
        footnotes is not _UNCHANGED_OBJECT_MAP and footnotes is not old_footnotes
    )
    document_changed = (
        document.text != old_document.text
        or document.cursor_position != old_document.cursor_position
    )

    rollback_error = None
    try:
        buffer.save_to_undo_stack()
        if tables is not _UNCHANGED_OBJECT_MAP:
            state.tables = tables
        if footnotes is not _UNCHANGED_OBJECT_MAP:
            state.footnotes = footnotes
        if document_changed:
            _replace_buffer_document(buffer, document)
        if selection is not _UNCHANGED_SELECTION:
            buffer.selection_state = selection
        # Object-only edits do not fire the main buffer's text-change callback.
        # Mark them only after both object and document state have committed.
        if object_changed and document.text == old_document.text:
            _working_state_changed(immediate=True)
    except BaseException as error:
        state.tables = old_tables
        state.footnotes = old_footnotes
        buffer.selection_state = old_selection
        try:
            current = buffer.document
            if (
                current.text != old_document.text
                or current.cursor_position != old_document.cursor_position
            ):
                # Bypass the replace helper during rollback so a fault-injected
                # helper failure cannot prevent restoration of the old document.
                buffer.set_document(old_document, bypass_readonly=True)
        except BaseException as restore_error:
            rollback_error = restore_error
        finally:
            buffer._undo_stack = old_undo_stack
            buffer._redo_stack = old_redo_stack
            for name, value in old_tracking.items():
                setattr(state, name, value)

        if rollback_error is not None:
            raise RuntimeError(
                "Folded-object transaction failed and its document rollback "
                "also failed."
            ) from error
        raise


def _table_state_for_placeholders(document):
    """Validate table-object/placeholder correspondence before renumbering.

    Renumbering is one of the few operations that rewrites both the object
    mapping and several folded labels at once, so detect any pre-existing drift
    *before* mutating either side of that relationship. Success has no payload;
    invalid state raises ValueError before any mutation begins.
    """
    seen = set()
    for line in document.lines:
        match = TABLE_PLACEHOLDER_RE.match(line)
        if match is None:
            continue
        number = int(match.group(1))
        if number in seen:
            raise ValueError(
                f"Table {number} appears more than once in the folded document."
            )
        if number not in state.tables:
            raise ValueError(
                f"Table {number} has a folded reference but no table data."
            )
        seen.add(number)

    missing = sorted(set(state.tables) - seen)
    if missing:
        label = ", ".join(f"Table {number}" for number in missing)
        raise ValueError(
            f"{label} has table data but no folded reference in the document."
        )


def _shifted_table_state_for_insert(insert_number, document):
    """Return renumbered table objects/document without mutating editor state."""
    _table_state_for_placeholders(document)

    shifted_tables = {}
    for number, table in state.tables.items():
        target = number + 1 if number >= insert_number else number
        shifted_tables[target] = table

    row = document.cursor_position_row
    col = document.cursor_position_col
    changed = False
    new_lines = []
    for line in document.lines:
        match = TABLE_PLACEHOLDER_RE.match(line)
        if match and int(match.group(1)) >= insert_number:
            old_number = int(match.group(1))
            new_number = old_number + 1
            table = state.tables[old_number]  # validated above
            line = _table_placeholder(new_number, table.title)
            changed = True
        new_lines.append(line)

    if not changed:
        return shifted_tables, document

    new_text = "\n".join(new_lines)
    tmp = Document(text=new_text)
    new_row = min(row, tmp.line_count - 1)
    new_cursor = tmp.translate_row_col_to_index(
        new_row, min(col, len(tmp.lines[new_row]))
    )
    return shifted_tables, Document(new_text, cursor_position=new_cursor)



def _document_with_inserted_table_placeholder(table_number, table, document):
    """Return ``document`` with one folded table block inserted at its cursor."""
    before = document.current_line_before_cursor
    after = document.current_line_after_cursor

    prefix = ""
    suffix = ""
    if before.strip():
        prefix = "\n\n"
    elif (
        document.cursor_position_row > 0
        and document.lines[document.cursor_position_row - 1].strip()
    ):
        prefix = "\n"

    if after.strip():
        suffix = "\n\n"
    elif (
        document.cursor_position_row + 1 < document.line_count
        and document.lines[document.cursor_position_row + 1].strip()
    ):
        suffix = "\n"

    insertion = prefix + _table_placeholder(table_number, table.title) + suffix
    position = document.cursor_position
    return Document(
        document.text[:position] + insertion + document.text[position:],
        cursor_position=position + len(insertion),
    )



def _commit_new_table_at_cursor(insert_number, table):
    """Insert and renumber a table through one document/object transaction."""
    document = text_area.buffer.document
    try:
        shifted_tables, shifted_document = _shifted_table_state_for_insert(
            insert_number, document
        )
    except ValueError as error:
        show_message(
            "Document object error",
            f"Carriage cannot insert a table because its folded table state is "
            f"inconsistent.\n\n{error}",
        )
        return False

    updated_tables = dict(shifted_tables)
    updated_tables[insert_number] = table
    final_document = _document_with_inserted_table_placeholder(
        insert_number, table, shifted_document
    )
    _commit_folded_object_transaction(
        text_area.buffer,
        final_document,
        tables=updated_tables,
    )
    return True


def _document_with_refreshed_table_placeholder(table_number, table, document):
    """Return document with one folded table label refreshed, without mutation."""
    row = document.cursor_position_row
    col = document.cursor_position_col
    lines = list(document.lines)
    changed = False
    for index, line in enumerate(lines):
        match = TABLE_PLACEHOLDER_RE.match(line)
        if match and int(match.group(1)) == table_number:
            replacement = _table_placeholder(table_number, table.title)
            if replacement != line:
                lines[index] = replacement
                changed = True
            break

    if not changed:
        return document

    new_text = "\n".join(lines)
    tmp = Document(text=new_text)
    new_row = min(row, tmp.line_count - 1)
    new_col = min(col, len(tmp.lines[new_row]))
    return Document(
        text=new_text,
        cursor_position=tmp.translate_row_col_to_index(new_row, new_col),
    )


def _remove_folded_object_line(lines, row):
    """Remove one object line and one now-redundant separator blank."""
    lines = list(lines)
    if not (0 <= row < len(lines)):
        return lines or [""], 0
    del lines[row]
    if not lines:
        return [""], 0

    # Object insertion/collapse normally leaves a blank separator around a
    # block. If deleting the object makes two separator blanks touch, keep one.
    if 0 < row < len(lines) and not lines[row - 1].strip() and not lines[row].strip():
        del lines[row]
    elif row == 0 and len(lines) > 1 and not lines[0].strip():
        del lines[0]
    elif row >= len(lines) and len(lines) > 1 and not lines[-1].strip():
        del lines[-1]

    if not lines:
        lines = [""]
    return lines, min(row, len(lines) - 1)


def _delete_table_object(table_number):
    """Delete one folded table and renumber later table labels atomically."""
    if table_number not in state.tables:
        return False

    buf = text_area.buffer
    doc = buf.document
    target_row = None
    for row, line in enumerate(doc.lines):
        match = TABLE_PLACEHOLDER_RE.match(line)
        if match and int(match.group(1)) == table_number:
            target_row = row
            break
    if target_row is None:
        return False

    updated = {}
    for number in sorted(state.tables):
        if number == table_number:
            continue
        new_number = number - 1 if number > table_number else number
        updated[new_number] = state.tables[number]

    lines, cursor_row = _remove_folded_object_line(doc.lines, target_row)
    for row, line in enumerate(lines):
        match = TABLE_PLACEHOLDER_RE.match(line)
        if match:
            old_number = int(match.group(1))
            if old_number > table_number:
                new_number = old_number - 1
                table = updated.get(new_number)
                if table is not None:
                    lines[row] = _table_placeholder(new_number, table.title)

    new_text = "\n".join(lines)
    tmp = Document(new_text)
    cursor_row = min(cursor_row, tmp.line_count - 1)
    cursor_col = min(doc.cursor_position_col, len(tmp.lines[cursor_row]))
    _commit_folded_object_transaction(
        buf,
        Document(new_text, tmp.translate_row_col_to_index(cursor_row, cursor_col)),
        tables=updated,
    )
    return True


def do_delete_table_at_cursor():
    table_number = _table_number_at_cursor()
    if table_number is None:
        show_message("No table", "Place the cursor on a folded table first.")
        return
    confirm(
        "Delete table",
        f"Delete Table {table_number} from the document? This can be undone with Ctrl+Z.",
        lambda: _delete_table_object(table_number),
    )


def _new_table_data(columns, rows, title=""):
    return TableData(
        headers=[""] * columns,
        rows=[[""] * columns for _ in range(rows)],
        title=" ".join(str(title).splitlines()).strip(),
        alignments=["default"] * columns,
        original_lines=None,
        caption_position="after" if str(title).strip() else None,
        dirty=True,
    )


@dataclass
class _WrapBlock:
    """One logical Markdown block in Carriage's wrapping model.

    ``wrappable`` describes eligibility for hard-wrapped Markdown export
    command. Normal editing does not rewrite any of these blocks. False is
    reserved for constructs whose physical source layout is content: code,
    tables, front matter, raw block HTML, and atomic block lines such as ATX
    headings, thematic breaks, and reference definitions.
    """

    kind: str
    start: int
    end: int
    source_lines: list[str]
    marker: str | None = None
    body_lines: list[str] | None = None
    wrap_width: int | None = None
    list_items: list["_WrapBlock"] | None = None
    wrappable: bool = True


@dataclass(frozen=True)
class _LayoutRow:
    """Display metadata for one existing physical source row.

    ``block_kind`` is projected once from the shared block analysis so display
    processors can classify a source row in O(1) time.  ``blockquote_depth``
    records the visual quote container independently of the literal source
    prefix, allowing lazy continuations and soft-wrapped rows to receive the
    same display-only gutter without changing Markdown on disk.
    """

    role: str = "text"
    structural_prefix_width: int = 0
    block_kind: str = ""
    blockquote_depth: int = 0


_ATX_DISPLAY_PREFIX_RE = re.compile(r"^#{1,6}(?!#)(?=.*\S)[ \t]*")
_BLOCKQUOTE_LINE_RE = re.compile(r"^\s{0,3}>[ \t]?(.*)$")


def _blockquote_prefix_info(line):
    """Return ``(depth, source_prefix_width)`` for explicit quote markers.

    The parser deliberately follows the same one-marker-at-a-time rule used by
    Carriage's blockquote handling.  The exact source spelling (``>>``, ``> >``,
    optional spaces) remains untouched; the display layer can replace it with a
    consistent gutter while still mapping cursor positions back to the source.
    """
    depth = 0
    consumed = 0
    remainder = line
    while True:
        match = _BLOCKQUOTE_LINE_RE.match(remainder)
        if match is None:
            break
        content = match.group(1)
        prefix_width = len(remainder) - len(content)
        if prefix_width <= 0:
            break
        depth += 1
        consumed += prefix_width
        remainder = content
    return depth, consumed


def _blockquote_gutter_text(depth, gutter_width):
    """Return a compact canonical quote marker that fits the visual gutter."""
    depth = max(0, int(depth or 0))
    gutter_width = max(0, int(gutter_width or 0))
    if depth <= 0 or gutter_width <= 0:
        return ""

    spaced = "> " * depth
    if len(spaced) <= gutter_width:
        return spaced

    # Deep nesting should never steal columns from the configured prose body.
    # Compress only the display marker when the fixed gutter is exhausted.
    marker_count = min(depth, max(1, gutter_width - 1))
    compact = ">" * marker_count
    if len(compact) < gutter_width:
        compact += " "
    return compact[:gutter_width]


def _simple_list_fragment_is_safe(text):
    """Return True when ``text`` is ordinary prose inside a simple list item.

    This is intentionally much narrower than the old ambiguity filter. A list
    item becomes complex only when its body explicitly starts another Markdown
    block that Carriage handles separately. Unknown extension-like syntax is
    not protected merely because it looks structural.
    """
    if not text.strip():
        return True

    stripped = text.lstrip()
    return not (
        TABLE_PLACEHOLDER_RE.match(text)
        or FOOTNOTE_PLACEHOLDER_RE.match(text)
        or _ATX_HEADING_RE.match(text)
        or _LIST_ITEM_RE.match(text)
        or stripped.startswith(">")
        or _fence_marker(text)
        or _is_indented_code(text)
        or _is_strong_html_start(text)
        or _REFERENCE_DEF_RE.match(text)
        or _is_thematic_break(text)
    )


def _simple_list_continuation_prefix_width(line, marker_prefix):
    """Return source indentation consumed by a simple-list continuation.

    ``None`` means the line is not safe continuation prose for Carriage's flat
    list model.  The accepted forms cover original Markdown's lazy continuation
    and the common aligned/four-space source styles without swallowing deeper
    nested/block content.
    """
    marker_indent = len(marker_prefix)
    base_indent = len(marker_prefix) - len(marker_prefix.lstrip(" "))
    leading_spaces = len(line) - len(line.lstrip(" "))

    if leading_spaces == marker_indent:
        return marker_indent

    standard_indent = base_indent + 4
    if leading_spaces == standard_indent:
        return standard_indent

    if leading_spaces <= 3:
        return leading_spaces

    return None


def _simple_list_continuation(line, marker_prefix):
    """Return prose content for one simple-list continuation, or None.

    Original Markdown permits a list item's paragraph to continue lazily on a
    following nonblank line without repeating the marker's indentation. Older
    hard-wrapped files therefore commonly contain lazy, body-aligned, and
    four-space continuation forms. Convert for Carriage accepts those ordinary
    prose forms and collapses them back to the item's logical source line.
    """
    prefix_width = _simple_list_continuation_prefix_width(line, marker_prefix)
    if prefix_width is None:
        return None
    return line[prefix_width:]


def _unlist_simple_list_item(block):
    """Return a simple list item as ordinary Carriage prose.

    Removing the marker is a structural edit, not merely character deletion.
    Ordinary hard-wrapped continuation lines collapse to the same logical prose
    representation produced by Convert for Carriage. Explicit two-space hard
    breaks remain physical boundaries. Multiline inline code keeps its physical
    newlines because those newlines are literal code content.
    """
    if block.marker is None:
        return list(block.source_lines)

    if not _prose_contains_multiline_inline_code(block.body_lines or []):
        return _convert_markdown_prose(block.body_lines or [""])

    marker_width = len(block.marker)
    converted = []
    for offset, line in enumerate(block.source_lines):
        if offset == 0:
            converted.append(line[marker_width:])
            continue

        continuation_width = _simple_list_continuation_prefix_width(
            line, block.marker
        )
        if continuation_width is None:
            # Defensive fallback: preserve source rather than risk deleting
            # literal code content if parser assumptions ever diverge.
            converted.append(line)
        else:
            converted.append(line[continuation_width:])
    return converted


def _parse_simple_list_item(lines, index, limit=None):
    """Parse one supported flat list item into the shared wrapping model."""
    if not (0 <= index < len(lines)):
        return None

    match = _LIST_ITEM_RE.match(lines[index])
    if match is None:
        return None

    base_indent = len(lines[index]) - len(lines[index].lstrip(" "))
    marker = match.group(1)
    first_body = lines[index][len(marker):]
    if not _simple_list_fragment_is_safe(first_body):
        return None

    end_limit = len(lines) if limit is None else min(limit, len(lines))
    body = [first_body]
    i = index + 1

    while i < end_limit and lines[i].strip():
        next_item = _LIST_ITEM_RE.match(lines[i])
        if next_item is not None:
            next_indent = len(lines[i]) - len(lines[i].lstrip(" "))
            if next_indent == base_indent:
                break
            return None

        continuation = _simple_list_continuation(lines[i], marker)
        if continuation is None or not _simple_list_fragment_is_safe(continuation):
            return None
        body.append(continuation)
        i += 1

    return _WrapBlock(
        kind="list",
        start=index,
        end=i,
        source_lines=list(lines[index:i]),
        marker=marker,
        body_lines=body,
    )


def _list_marker_family(marker_prefix):
    """Return a conservative family key for one supported list marker."""
    marker_text = marker_prefix.strip()
    if marker_text and marker_text[0].isdigit():
        return ("ordered", marker_text[-1])
    return ("unordered", marker_text[:1])


def _list_run_marker_budget(lines, index, limit, base_indent, family):
    """Return the widest top-level marker in the surrounding flat list run."""
    budget = 0
    i = index
    while i < limit and lines[i].strip():
        match = _LIST_ITEM_RE.match(lines[i])
        if match is not None:
            indent = len(lines[i]) - len(lines[i].lstrip(" "))
            if indent == base_indent:
                marker = match.group(1)
                if _list_marker_family(marker) != family:
                    break
                budget = max(budget, len(marker))
        i += 1
    return budget


def _parse_simple_list_run(lines, index, limit=None, width=None):
    """Parse the longest supported flat-list prefix beginning at ``index``."""
    if width is None:
        width = WRAP_COLUMN
    if not (0 <= index < len(lines)):
        return None

    first_match = _LIST_ITEM_RE.match(lines[index])
    if first_match is None:
        return None

    end_limit = len(lines) if limit is None else min(limit, len(lines))
    base_indent = len(lines[index]) - len(lines[index].lstrip(" "))
    family = _list_marker_family(first_match.group(1))
    marker_budget = _list_run_marker_budget(
        lines, index, end_limit, base_indent, family
    )

    items = []
    i = index
    while i < end_limit and lines[i].strip():
        match = _LIST_ITEM_RE.match(lines[i])
        if match is None:
            break
        if len(lines[i]) - len(lines[i].lstrip(" ")) != base_indent:
            break
        if _list_marker_family(match.group(1)) != family:
            break

        item = _parse_simple_list_item(lines, i, limit=end_limit)
        if item is None or item.end <= i:
            break
        items.append(item)
        i = item.end

    if not items:
        return None

    if marker_budget <= 0:
        marker_budget = max(len(item.marker or "") for item in items)
    body_width = max(10, width - marker_budget)
    for item in items:
        item.wrap_width = body_width

    return _WrapBlock(
        kind="list-run",
        start=index,
        end=i,
        source_lines=list(lines[index:i]),
        wrap_width=body_width,
        list_items=items,
    )


def _parse_blockquote_run(lines, index):
    """Parse one supported single-level prose blockquote run.

    Original Markdown permits lazy blockquote continuation: once an explicit
    ``>`` line has opened a quoted paragraph, following nonblank prose lines may
    omit the marker.  Treat those lines as part of the same quote immediately,
    rather than exposing them to top-level parsing on the first conversion
    pass.  That keeps Convert for Carriage idempotent and, more importantly,
    preserves the original blockquote interpretation.

    Carriage still keeps its deliberately narrow *simple quote* model.  If a
    nonblank continuation introduces block structure that would require
    recursive quote parsing (lists, thematic breaks, code, HTML, reference
    definitions, etc.), return ``None`` so the caller preserves the whole
    nonblank quote region as ``complex-blockquote``.  A column-zero ATX heading
    is different: original Markdown lets it interrupt a lazy quoted paragraph,
    so it ends this quote run and remains a top-level block.
    """
    if not (0 <= index < len(lines)) or not lines[index].lstrip().startswith(">"):
        return None

    end = index
    inner = []

    while end < len(lines) and lines[end].strip():
        line = lines[end]
        if line.lstrip().startswith(">"):
            match = _BLOCKQUOTE_LINE_RE.match(line)
            if match is None:
                return None
            content = match.group(1)
            # Nested quotes are valid Markdown but outside Carriage's simple
            # single-level conversion model. Preserve the whole region.
            if re.match(r"^\s{0,3}>", content):
                return None
            if content and not _simple_list_fragment_is_safe(content):
                return None
            inner.append(content)
            end += 1
            continue

        # A real ATX heading at column zero interrupts lazy quote continuation.
        # Do not absorb it into the quoted paragraph.
        if _ATX_HEADING_RE.match(line):
            break

        # Ordinary lazy prose is part of the quote.  If it looks like another
        # block construct, preserving the complete nonblank quote region is
        # safer than partially converting it and allowing a later pass to
        # reinterpret the remainder (the former blockquote/Setext bug).
        if not _simple_list_fragment_is_safe(line):
            return None

        inner.append(line)
        end += 1

    return _WrapBlock(
        kind="blockquote",
        start=index,
        end=end,
        source_lines=list(lines[index:end]),
        marker="> ",
        body_lines=inner,
    )


def _make_plain_prose_block(lines, start, end):
    if not (0 <= start < end <= len(lines)):
        return None
    return _WrapBlock(
        kind="prose",
        start=start,
        end=end,
        source_lines=list(lines[start:end]),
    )


def _render_blockquote(block, width):
    """Render a supported blockquote through the shared prose wrapper."""
    if _prose_contains_multiline_inline_code(block.body_lines or []):
        return list(block.source_lines)
    body_width = max(10, width - 2)
    rendered = []
    paragraph = []
    body_lines = block.body_lines or []

    def flush_paragraph():
        if not paragraph:
            return
        wrapped = _wrap_markdown_prose(paragraph, width=body_width)
        rendered.extend(f"> {line}" if line else ">" for line in wrapped)
        paragraph.clear()

    for content in body_lines:
        if content.strip():
            paragraph.append(content)
        else:
            flush_paragraph()
            if not rendered or rendered[-1] != ">":
                rendered.append(">")
    flush_paragraph()
    return rendered or [">"]


def _render_wrap_block(block, width=None):
    """Render one logical block according to Carriage's source policy."""
    if width is None:
        width = WRAP_COLUMN
    if not block.wrappable:
        return list(block.source_lines)

    if block.kind == "prose":
        return _wrap_markdown_prose(block.source_lines, width=width)

    if block.kind == "list" and block.marker is not None:
        if _prose_contains_multiline_inline_code(block.body_lines or []):
            return list(block.source_lines)
        body_width = block.wrap_width
        if body_width is None:
            body_width = max(10, width - len(block.marker))
        marker_width = len(block.marker)
        wrapped_body = _wrap_markdown_prose(
            block.body_lines or [""], width=body_width
        )
        return [
            (block.marker if i == 0 else " " * marker_width) + line
            for i, line in enumerate(wrapped_body)
        ]

    if block.kind == "list-run" and block.list_items is not None:
        rendered = []
        for item in block.list_items:
            item.wrap_width = block.wrap_width
            rendered.extend(_render_wrap_block(item, width=width))
        return rendered

    if block.kind == "blockquote":
        return _render_blockquote(block, width)

    return list(block.source_lines)


def _wrap_measure_text(line):
    """Return text that counts toward a configured-width wrap decision."""
    marker = _hard_break_marker(line)
    text = _strip_hard_break_marker(line, marker)
    if marker is None and text.endswith(" "):
        text = text.rstrip(" ")
    return text



def _line_has_unescaped_closer(text, closer):
    escaped = False
    for char in text:
        if escaped:
            escaped = False
            continue
        if char == "\\":
            escaped = True
            continue
        if char == closer:
            return True
    return False


def _collect_reference_definition(lines, index):
    """Collect a reference definition, including a continuation title.

    CommonMark permits the optional title to begin on the following line. The
    title may itself span physical lines, so once a quoted/parenthesized title
    starts, preserve through its matching delimiter rather than exposing its
    continuation to prose normalization.
    """
    block = [lines[index]]
    i = index + 1
    if i >= len(lines) or not lines[i].strip():
        return block, i

    match = _REFERENCE_TITLE_START_RE.match(lines[i])
    if match is None:
        return block, i

    opener = match.group("delim")
    closer = ")" if opener == "(" else opener
    block.append(lines[i])
    stripped = lines[i].lstrip()
    after_open = stripped[1:]
    if _line_has_unescaped_closer(after_open, closer):
        return block, i + 1

    i += 1
    while i < len(lines) and lines[i].strip():
        block.append(lines[i])
        if _line_has_unescaped_closer(lines[i], closer):
            i += 1
            break
        i += 1
    return block, i


def _preserved_block_at(lines, index, yaml_end=None, allow_indented_code=True):
    """Return an explicit source-preservation block beginning at ``index``.

    There is deliberately no catch-all ambiguity branch here. Fast prefix
    checks keep ordinary prose cheap; only a plausible carve-out pays for its
    full recognizer.
    """
    if yaml_end is not None and index == 0:
        return _WrapBlock(
            kind="front-matter",
            start=0,
            end=yaml_end,
            source_lines=list(lines[:yaml_end]),
            wrappable=False,
        )

    line = lines[index]
    if allow_indented_code and _is_indented_code(line):
        return _WrapBlock("code", index, index + 1, [line], wrappable=False)

    stripped = line.lstrip()
    first = stripped[:1]

    if first in {"`", "~"} and _fence_marker(line):
        source, end = _collect_fenced_block(lines, index)
        return _WrapBlock("code", index, end, source, wrappable=False)

    if first == "<" and _is_strong_html_start(line):
        source, end = _collect_html_block(lines, index)
        return _WrapBlock("block-html", index, end, source, wrappable=False)

    if "|" in line and _is_pipe_table_start(lines, index):
        source, end = _collect_pipe_table(lines, index)
        return _WrapBlock("table", index, end, source, wrappable=False)

    unsupported = _unsupported_line_sensitive_block_at(lines, index)
    if unsupported is not None:
        return unsupported

    if first == "[":
        if line.startswith("[[Table ") and TABLE_PLACEHOLDER_RE.match(line):
            return _WrapBlock("table", index, index + 1, [line], wrappable=False)
        if line.startswith("[[Footnote: ") and FOOTNOTE_PLACEHOLDER_RE.match(line):
            return _WrapBlock(
                "footnote-placeholder", index, index + 1, [line], wrappable=False
            )
        if _REFERENCE_DEF_RE.match(line):
            source, end = _collect_reference_definition(lines, index)
            return _WrapBlock(
                "reference-definition", index, end, source, wrappable=False
            )

    if first == "#" and _ATX_HEADING_RE.match(line):
        return _WrapBlock("heading", index, index + 1, [line], wrappable=False)

    if first in {"-", "*", "_"} and _is_thematic_break(line):
        return _WrapBlock(
            "thematic-break", index, index + 1, [line], wrappable=False
        )

    return None


def _setext_heading_at(lines, index):
    """Return a Setext heading block beginning at ``index``, if present.

    Original Markdown resolves Setext headings before ATX headings, thematic
    breaks, lists, indented code, and blockquotes.  Therefore a nonblank title
    line is allowed to *look* like any of those constructs when the following
    line is a Setext underline.  Carriage-specific preserved structures that
    must remain opaque (folded objects, fenced code, raw block HTML, reference
    definitions, and pipe tables) are still excluded here.
    """
    if not (0 <= index + 1 < len(lines)):
        return None

    title_line = lines[index]
    if not title_line.strip():
        return None

    # These structures are intentionally opaque to Convert for Carriage (or,
    # for HTML/reference definitions, are handled before block headings in the
    # original Markdown pipeline).  Do not reinterpret their first line as a
    # Setext title merely because a dash/equal line happens to follow it.
    if (
        (title_line.startswith("[[Table ") and TABLE_PLACEHOLDER_RE.match(title_line))
        or (title_line.startswith("[[Footnote: ") and FOOTNOTE_PLACEHOLDER_RE.match(title_line))
        or _REFERENCE_DEF_RE.match(title_line)
        or _is_strong_html_start(title_line)
        or _fence_marker(title_line)
        or _is_pipe_table_start(lines, index)
        or _unsupported_line_sensitive_block_at(lines, index) is not None
    ):
        return None

    underline = lines[index + 1]
    if _SETEXT_H1_RE.match(underline):
        marker = "#"
    elif _SETEXT_H2_RE.match(underline):
        marker = "##"
    else:
        return None

    return _WrapBlock(
        kind="setext-heading",
        start=index,
        end=index + 2,
        source_lines=list(lines[index:index + 2]),
        marker=marker,
        wrappable=True,
    )


def _block_starts_at(
    lines, index, yaml_end=None, width=None, allow_indented_code=True, allow_list=True
):
    """Return a recognized non-prose block beginning at ``index``, if any."""
    if width is None:
        width = WRAP_COLUMN
    # Front matter is a Carriage preservation extension and must remain opaque
    # even when its first two lines could superficially form a Setext heading.
    if yaml_end is not None and index == 0:
        preserved = _preserved_block_at(
            lines, index, yaml_end=yaml_end, allow_indented_code=allow_indented_code
        )
        if preserved is not None:
            return preserved

    # Original Markdown's block pipeline resolves Setext headings before ATX
    # headings, thematic breaks, lists, indented code, and blockquotes.  Doing
    # the same here also makes conversion idempotent: normalization cannot
    # manufacture a Setext heading that appears only on a second pass.
    setext = _setext_heading_at(lines, index)
    if setext is not None:
        return setext

    preserved = _preserved_block_at(
        lines, index, yaml_end=None, allow_indented_code=allow_indented_code
    )
    if preserved is not None:
        return preserved

    stripped = lines[index].lstrip()
    if allow_list and stripped[:1] in "-*+0123456789" and _LIST_ITEM_RE.match(lines[index]):
        run_end = _nonblank_run_end(lines, index)
        list_run = _parse_simple_list_run(lines, index, limit=run_end, width=width)
        if list_run is not None:
            return list_run
        # Original Markdown permits list content that is more complex than
        # Carriage's intentionally flat list model. Preserve that nonblank
        # list region unchanged rather than flattening its indentation.
        return _WrapBlock(
            "complex-list",
            index,
            run_end,
            list(lines[index:run_end]),
            wrappable=False,
        )

    if stripped.startswith(">"):
        quote = _parse_blockquote_run(lines, index)
        if quote is not None:
            return quote
        # Nested or otherwise complex original-Markdown blockquotes remain
        # valid source. Carriage does not recursively convert them yet.
        run_end = _nonblank_run_end(lines, index)
        return _WrapBlock(
            "complex-blockquote",
            index,
            run_end,
            list(lines[index:run_end]),
            wrappable=False,
        )

    return None


def _layout_rows_for_block(block):
    """Return structural display metadata from the shared block model.

    Source-format width belongs to the hard-wrap exporter. Display width is
    calculated later from the actual viewport, so list markers never reduce
    the configured visual prose area merely because they count toward exported
    source width.
    """
    rows = [_LayoutRow() for _ in block.source_lines]

    if block.kind == "heading" and block.source_lines:
        match = _ATX_DISPLAY_PREFIX_RE.match(block.source_lines[0])
        if match is not None:
            rows[0] = _LayoutRow("heading", len(match.group(0)))
        return rows

    if block.kind in {"blockquote", "complex-blockquote"}:
        current_depth = 0
        for offset, source_line in enumerate(block.source_lines):
            depth, prefix_width = _blockquote_prefix_info(source_line)
            if depth > 0:
                current_depth = depth
                rows[offset] = _LayoutRow(
                    "blockquote", prefix_width, "", current_depth
                )
            elif source_line.strip() and current_depth > 0:
                # Complex blockquotes can contain lazy paragraph continuation
                # lines that omit the literal `>` marker. Keep their visual
                # container depth without inventing source characters.
                rows[offset] = _LayoutRow(
                    "blockquote-lazy", 0, "", current_depth
                )
            else:
                current_depth = 0
        return rows

    if block.kind == "list-run" and block.list_items is not None:
        for item in block.list_items:
            marker_width = len(item.marker or "")
            relative_start = item.start - block.start
            for offset, source_line in enumerate(item.source_lines):
                if offset == 0:
                    rows[relative_start + offset] = _LayoutRow(
                        "list-marker", marker_width
                    )
                else:
                    # A lazy continuation may have no source indentation at
                    # all.  Only hide indentation that actually exists; the
                    # display processor supplies the remaining gutter padding
                    # so the prose still aligns with the list item's body.
                    source_indent = _simple_list_continuation_prefix_width(
                        source_line, item.marker or ""
                    )
                    rows[relative_start + offset] = _LayoutRow(
                        "list-continuation", source_indent or 0
                    )
        return rows

    if block.kind == "list" and block.marker is not None:
        marker_width = len(block.marker)
        for offset, source_line in enumerate(block.source_lines):
            if offset == 0:
                rows[offset] = _LayoutRow("list-marker", marker_width)
            else:
                source_indent = _simple_list_continuation_prefix_width(
                    source_line, block.marker
                )
                rows[offset] = _LayoutRow(
                    "list-continuation", source_indent or 0
                )

    return rows



@lru_cache(maxsize=8)
def _analyze_document_layout(full_text, width=None):
    """Return the shared logical block layout for the current source text.

    Classification is intentionally cheap: it establishes block boundaries,
    wrap budgets, and structural roles without re-rendering every prose block.
    Hard-wrapped Markdown export feeds these blocks into ``_render_wrap_block()`` when it needs
    physical output lines. The display layer consumes the same classification
    and row metadata without changing the source.
    """
    if width is None:
        width = WRAP_COLUMN
    lines = full_text.split("\n")
    blocks = []
    i = 0
    yaml_end = _yaml_front_matter_end(lines)

    while i < len(lines):
        if not lines[i].strip():
            blocks.append(
                _WrapBlock(
                    kind="blank",
                    start=i,
                    end=i + 1,
                    source_lines=[lines[i]],
                    wrappable=False,
                )
            )
            i += 1
            continue

        block = _block_starts_at(lines, i, yaml_end=yaml_end, width=width)
        if block is not None:
            blocks.append(block)
            i = block.end
            continue

        # Default path: prose continues until a blank line or an explicitly
        # recognized block begins. A small set of table/container/definition-list
        # signatures above is preserved even though Carriage does not edit those
        # extensions; everything else remains ordinary prose. Indentation cannot
        # interrupt an existing paragraph merely by looking like indented code.
        start = i
        i += 1
        while i < len(lines) and lines[i].strip():
            if _block_starts_at(
                lines, i, yaml_end=None, width=width, allow_indented_code=False, allow_list=False
            ) is not None:
                break
            i += 1
        blocks.append(_make_plain_prose_block(lines, start, i))

    return tuple(blocks)




@lru_cache(maxsize=8)
def _layout_row_map(full_text):
    """Return per-source-row metadata from the shared block layout.

    The map includes the owning block kind as well as gutter metadata.  Building
    it is linear in the document size and every later row lookup is constant
    time, including the repeated transformations used to measure wrapped line
    heights after an edit.
    """
    lines = _source_lines(full_text)
    result = [_LayoutRow() for _ in lines]
    blocks = _analyze_document_layout(full_text, WRAP_COLUMN)
    for block in blocks:
        for offset, row_info in enumerate(_layout_rows_for_block(block)):
            row = block.start + offset
            if 0 <= row < len(result):
                result[row] = _LayoutRow(
                    row_info.role,
                    row_info.structural_prefix_width,
                    block.kind,
                    row_info.blockquote_depth,
                )

    # Original Markdown permits lazy blockquote continuation: after an explicit
    # quote marker, ordinary paragraph lines may omit `>` until a blank line or
    # another block interrupts the paragraph. The converter now recognizes the
    # same ordinary lazy continuations; this projection also covers preserved
    # complex quote regions so the editor draws a continuous quote gutter.
    active_quote_depth = 0
    for row, line in enumerate(lines):
        info = result[row]
        explicit_depth, _prefix_width = _blockquote_prefix_info(line)
        if explicit_depth > 0 and info.block_kind in {
            "blockquote",
            "complex-blockquote",
        }:
            active_quote_depth = explicit_depth
            continue

        if not line.strip():
            active_quote_depth = 0
            continue

        if info.blockquote_depth > 0:
            active_quote_depth = info.blockquote_depth
            continue

        if active_quote_depth > 0 and info.block_kind == "prose":
            result[row] = _LayoutRow(
                "blockquote-lazy",
                info.structural_prefix_width,
                info.block_kind,
                active_quote_depth,
            )
            continue

        active_quote_depth = 0

    return tuple(result)


def _display_row_layout(full_text, row):
    rows = _layout_row_map(full_text)
    if 0 <= row < len(rows):
        return rows[row]
    return _LayoutRow()


def _active_structural_prefix_width(document, row, role=None, columns=None):
    """Return a prefix width only when it is actually hidden in the gutter."""
    info = _display_row_layout(document.text, row)
    if not info.structural_prefix_width or (role is not None and info.role != role):
        return None
    if columns is None:
        try:
            columns = get_app().output.get_size().columns
        except Exception:
            columns = WRAP_COLUMN + STRUCTURE_GUTTER_WIDTH + 2
    _left, gutter, _right = _prose_layout_widths(columns)
    return (
        info.structural_prefix_width
        if 0 < info.structural_prefix_width <= gutter
        else None
    )


def _hidden_structural_body_col(document, row):
    """Return the first navigable source column for a guttered source row.

    Structural Markdown that Carriage has moved into the hanging gutter remains
    part of the source file, but it is presentation rather than ordinary cursor
    space.  Navigation therefore begins at the first visible prose column.
    """
    prefix_width = _active_structural_prefix_width(document, row)
    return 0 if prefix_width is None else prefix_width


def _clamp_source_position_out_of_gutter(full_text, position):
    """Snap a source insertion point out of any hidden structural prefix."""
    position = max(0, min(len(full_text), int(position)))
    document = Document(full_text, cursor_position=position)
    row = document.cursor_position_row
    body_col = _hidden_structural_body_col(document, row)
    if document.cursor_position_col < body_col:
        return document.translate_row_col_to_index(row, body_col)
    return position


def _clamp_buffer_cursor_out_of_gutter(buffer):
    """Keep the main prose caret out of display-only structural gutter text."""
    target = _clamp_source_position_out_of_gutter(
        buffer.text, buffer.cursor_position
    )
    if target == buffer.cursor_position:
        return False
    if getattr(buffer, "_carriage_gutter_clamp_active", False):
        return False
    buffer._carriage_gutter_clamp_active = True
    try:
        buffer.cursor_position = target
    finally:
        buffer._carriage_gutter_clamp_active = False
    return True


def _list_continuation_prefix_width(document, row):
    return _active_structural_prefix_width(
        document, row, role="list-continuation"
    )


def _hard_wrap_export_text(full_text, width=None):
    """Hard-wrap a derived Markdown export using the explicit carve-outs."""
    if width is None:
        width = WRAP_COLUMN
    rendered = []
    for block in _analyze_document_layout(full_text, width):
        rendered.extend(_render_wrap_block(block, width=width))
    return "\n".join(rendered)


def _source_range_intersects(ranges, start, end):
    """Return True when [start, end) overlaps any sorted source range."""
    if end <= start:
        return False
    for range_start, range_end in ranges:
        if range_end <= start:
            continue
        if range_start >= end:
            break
        return True
    return False


def _markdown_delimiter_flanking(text, start, end, marker):
    """Return conservative CommonMark-style open/close flags for a run."""
    before = text[start - 1] if start > 0 else "\n"
    after = text[end] if end < len(text) else "\n"
    before_ws = before.isspace()
    after_ws = after.isspace()
    # For emphasis recognition, treating any non-word, non-space character as
    # punctuation is slightly more conservative than the Markdown definition
    # and prevents Carriage from inventing emphasis in uncertain constructs.
    before_punct = not before_ws and not before.isalnum()
    after_punct = not after_ws and not after.isalnum()

    left_flanking = (not after_ws) and (
        not after_punct or before_ws or before_punct
    )
    right_flanking = (not before_ws) and (
        not before_punct or after_ws or after_punct
    )

    if marker == "_":
        can_open = left_flanking and (not right_flanking or before_punct)
        can_close = right_flanking and (not left_flanking or after_punct)
    else:
        can_open = left_flanking
        can_close = right_flanking
    return can_open, can_close


def _emphasis_run_at(text, index):
    """Return (marker, run_end, run_length) for one unescaped emphasis run."""
    if not (0 <= index < len(text)) or text[index] not in "*_":
        return None
    if _markdown_char_is_escaped(text, index):
        return None
    marker = text[index]
    end = index + 1
    while end < len(text) and text[end] == marker:
        end += 1
    return marker, end, end - index


def _range_has_emphasis_delimiter(text, start, end, protected=()):
    """Return True when a range contains emphasis-like delimiter syntax."""
    i = max(0, start)
    end = min(len(text), end)
    while i < end:
        if text[i] not in "*_" or _range_contains(protected, i):
            i += 1
            continue
        run = _emphasis_run_at(text, i)
        if run is None:
            i += 1
            continue
        marker, run_end, _count = run
        run_end = min(run_end, end)
        can_open, can_close = _markdown_delimiter_flanking(
            text, i, run_end, marker
        )
        if can_open or can_close:
            return True
        i = run_end
    return False


def _emphasis_spans_in_range(text, start, end, protected=()):
    """Return conservative matched emphasis spans within one source range.

    Runs of one, two, or three matching markers are treated as Carriage's four
    supported emphasis states. A small stack is enough for the straightforward
    valid Markdown Carriage promises to manipulate, while still recognizing
    nested/mixed emphasis so partial selections can be rejected safely.
    """
    stack = []
    spans = []
    i = max(0, start)
    end = min(len(text), end)
    while i < end:
        if text[i] not in "*_" or _range_contains(protected, i):
            i += 1
            continue
        run = _emphasis_run_at(text, i)
        if run is None:
            i += 1
            continue
        marker, run_end, count = run
        if run_end > end:
            break
        if count not in {1, 2, 3}:
            i = run_end
            continue
        can_open, can_close = _markdown_delimiter_flanking(
            text, i, run_end, marker
        )

        if can_close and stack and stack[-1][0] == marker and stack[-1][1] == count:
            _marker, _count, open_start, open_end = stack.pop()
            spans.append((open_start, open_end, i, run_end, marker, count))
        elif can_open:
            stack.append((marker, count, i, run_end))
        i = run_end

    return tuple(sorted(spans))


def _normalize_underscore_emphasis_inline(text):
    """Normalize only straightforward underscore emphasis to asterisks.

    Code spans, inline HTML/autolinks, link destinations/reference labels,
    escaped delimiters, intraword underscores, nested emphasis, and ambiguous
    underscore runs are left byte-identical. Replacing a delimiter never
    changes source length, which also keeps conversion cursor mapping stable.
    """
    if "_" not in text:
        return text

    protected = _merge_source_ranges(
        list(_inline_footnote_literal_ranges(text))
        + [(match.start(), match.end()) for match in _BARE_URL_OR_EMAIL_RE.finditer(text)]
    )
    spans = _emphasis_spans_in_range(text, 0, len(text), protected=protected)
    if not spans:
        return text

    chars = list(text)
    for span in spans:
        open_start, open_end, close_start, close_end, marker, count = span
        if marker != "_" or count not in {1, 2, 3}:
            continue

        # Convert only a standalone emphasis span. If it contains another
        # emphasis span or sits inside one, preserving the entire nested/mixed
        # construct is safer than partially changing its delimiter family.
        nested = False
        for other in spans:
            if other is span:
                continue
            other_start, _other_open_end, _other_close_start, other_end, _other_marker, _other_count = other
            if other_end <= open_start or other_start >= close_end:
                continue
            nested = True
            break
        if nested:
            continue

        inner = text[open_end:close_start]
        if not inner or inner[0].isspace() or inner[-1].isspace():
            continue
        if _range_has_emphasis_delimiter(
            text, open_end, close_start, protected=protected
        ):
            continue

        for pos in range(open_start, open_end):
            chars[pos] = "*"
        for pos in range(close_start, close_end):
            chars[pos] = "*"

    return "".join(chars)


def _convert_markdown_prose(source_lines):
    """Collapse wrapping whitespace while preserving explicit hard breaks.

    Each returned line is one logical prose segment. A Markdown hard-break
    marker ends the current segment and is retained at the end of that line.
    Multiline inline code spans are left byte-identical because their physical
    newlines and surrounding spaces are literal code content.
    """
    if _prose_contains_multiline_inline_code(source_lines):
        return list(source_lines)

    rendered = []
    current = []
    current_guard = ""

    for raw_line in source_lines:
        if not current:
            current_guard = _prose_heading_guard(raw_line)
        marker = _hard_break_marker(raw_line)
        text = _strip_hard_break_marker(raw_line, marker)
        stripped = text.strip()
        if stripped:
            current.append(stripped)

        if marker is not None:
            joined = _normalize_underscore_emphasis_inline(" ".join(current))
            rendered.append(current_guard + joined + marker)
            current = []
            current_guard = ""

    if current or not rendered:
        joined = _normalize_underscore_emphasis_inline(" ".join(current))
        rendered.append(current_guard + joined)

    return rendered


def _atx_heading_parts(line):
    """Return ``(marker, title)`` for an original-Markdown ATX heading.

    Original Markdown ATX headings begin at column zero and may omit
    whitespace after the opening marker. Convert for Carriage emits one canonical form: the marker,
    exactly one space, and the title. A trailing run of ``#`` characters is
    closing syntax only when whitespace separates it from preceding title text;
    hashes attached directly to the title remain literal text.
    """
    match = re.match(r"^(#{1,6})(?!#)(?=.*\S)(.*)$", line)
    if match is None:
        return None

    marker = match.group(1)
    title = _canonical_heading_title(match.group(2).lstrip(" \t"))
    return marker, title


def _canonical_heading_title(title):
    """Return heading text with Carriage's closing-hash rule applied."""
    title = title.strip()
    closing = re.match(r"^(.*\S)[ \t]+#+[ \t]*$", title)
    if closing is not None:
        title = closing.group(1).rstrip(" \t")
    return title


def _canonical_atx_heading(marker, title):
    """Render one ATX heading in Carriage's canonical source form."""
    title = _normalize_underscore_emphasis_inline(_canonical_heading_title(title))
    return f"{marker} {title}" if title else marker


def _setext_title_for_atx(title):
    """Return a Setext title safe to emit inside an ATX heading.

    Hashes at the end of a Setext title are always literal title text.  In
    Carriage's ATX syntax, however, a whitespace-separated trailing hash run is
    closing syntax.  Escape only that ambiguous run so Setext -> ATX conversion
    preserves the title exactly instead of silently deleting literal hashes.
    """
    title = title.strip()
    closing_like = re.match(r"^(.*\S)([ \t]+)(#+)$", title)
    if closing_like is None:
        return title
    hashes = closing_like.group(3)
    escaped = "".join("\\#" for _ in hashes)
    return closing_like.group(1) + closing_like.group(2) + escaped


def _canonical_setext_atx_heading(marker, title):
    """Render a Setext heading as semantics-preserving canonical ATX."""
    title = _normalize_underscore_emphasis_inline(_setext_title_for_atx(title))
    return f"{marker} {title}" if title else marker


_ORDERED_LIST_MARKER_PARTS_RE = re.compile(
    r"^(?P<indent>[ \t]{0,3})(?P<number>\d+)\.(?P<spacing>[ \t]+)$"
)


def _convert_list_item(block, marker=None):
    """Convert one simple list item, optionally replacing its source marker."""
    marker = block.marker if marker is None else marker
    if marker is None:
        return list(block.source_lines)
    if _prose_contains_multiline_inline_code(block.body_lines or []):
        source = list(block.source_lines)
        if source and block.marker is not None and marker != block.marker:
            source[0] = marker + source[0][len(block.marker):]
        return source
    segments = _convert_markdown_prose(block.body_lines or [""])
    marker_width = len(marker)
    return [
        (marker if index == 0 else " " * marker_width) + segment
        for index, segment in enumerate(segments)
    ]


def _renumbered_ordered_list_markers(items):
    """Return consecutive markers for a simple ordered-list run, or None.

    Convert for Carriage preserves the first item's starting number and makes
    every following item consecutive. Existing indentation and whitespace after
    the period are retained; only the numeric source label changes. The parsed
    list blocks themselves are never mutated because the layout analysis is
    cached and shared by display/export code.
    """
    if not items or items[0].marker is None:
        return None

    first = _ORDERED_LIST_MARKER_PARTS_RE.match(items[0].marker)
    if first is None:
        return None

    start = int(first.group("number"))
    markers = []
    for offset, item in enumerate(items):
        if item.marker is None:
            return None
        match = _ORDERED_LIST_MARKER_PARTS_RE.match(item.marker)
        if match is None:
            return None
        markers.append(
            f'{match.group("indent")}{start + offset}.{match.group("spacing")}'
        )
    return markers


def _ordered_list_run_info(block):
    """Return ``(indent, first_number)`` for a simple ordered-list run."""
    if block.kind != "list-run" or not block.list_items:
        return None
    first_marker = block.list_items[0].marker
    if first_marker is None:
        return None
    match = _ORDERED_LIST_MARKER_PARTS_RE.match(first_marker)
    if match is None:
        return None
    # Every item in the run must be an ordered marker at the same indentation.
    indent = match.group("indent")
    for item in block.list_items:
        if item.marker is None:
            return None
        item_match = _ORDERED_LIST_MARKER_PARTS_RE.match(item.marker)
        if item_match is None or item_match.group("indent") != indent:
            return None
    return indent, int(match.group("number"))


def _ordered_list_marker_overrides(blocks):
    """Return canonical marker lists for ordered runs, including loose lists.

    Blank physical lines do not end an original-Markdown ordered list when the
    next block is another same-indentation ordered-list run.  The shared block
    analyzer intentionally keeps blank rows as separate blocks; this conversion
    plan reconnects those adjacent runs for numbering while preserving every
    blank row in the source layout.
    """
    overrides = {}
    i = 0
    while i < len(blocks):
        info = _ordered_list_run_info(blocks[i])
        if info is None:
            i += 1
            continue

        indent, start_number = info
        run_indexes = [i]
        search = i + 1
        while search < len(blocks):
            blank_start = search
            while search < len(blocks) and blocks[search].kind == "blank":
                search += 1
            # A loose-list continuation requires at least one intervening blank
            # row. Adjacent list items are already part of the same list-run.
            if search == blank_start or search >= len(blocks):
                break
            next_info = _ordered_list_run_info(blocks[search])
            if next_info is None or next_info[0] != indent:
                break
            run_indexes.append(search)
            search += 1

        number = start_number
        for block_index in run_indexes:
            block = blocks[block_index]
            markers = []
            for item in block.list_items or []:
                match = _ORDERED_LIST_MARKER_PARTS_RE.match(item.marker or "")
                if match is None:
                    markers = []
                    break
                markers.append(
                    f'{match.group("indent")}{number}.{match.group("spacing")}'
                )
                number += 1
            if markers:
                overrides[block.start] = tuple(markers)

        i = run_indexes[-1] + 1
    return overrides


def _ordered_list_group_at_row(blocks, row):
    """Return block indexes for the ordered list containing ``row``.

    Carriage's existing conversion model treats same-indentation ordered-list
    runs separated only by blank rows as one loose list. Reuse that exact model
    here so Renumber List and Convert for Carriage agree about list boundaries.
    A blank row counts as part of the list only when another compatible ordered
    run follows it.
    """
    i = 0
    while i < len(blocks):
        info = _ordered_list_run_info(blocks[i])
        if info is None:
            i += 1
            continue

        indent, _start_number = info
        run_indexes = [i]
        group_start = blocks[i].start
        group_end = blocks[i].end
        search = i + 1

        while search < len(blocks):
            blank_start = search
            while search < len(blocks) and blocks[search].kind == "blank":
                search += 1

            # Loose-list continuation requires at least one blank row followed
            # by another ordered run at the same source indentation.
            if search == blank_start or search >= len(blocks):
                break

            next_info = _ordered_list_run_info(blocks[search])
            if next_info is None or next_info[0] != indent:
                break

            run_indexes.append(search)
            group_end = blocks[search].end
            search += 1

        if group_start <= row < group_end:
            return tuple(run_indexes)

        i = run_indexes[-1] + 1

    return ()


def _renumber_list_item_source(lines, item, new_marker, cursor_row, cursor_col):
    """Rewrite one item's marker and marker-aligned continuation indentation.

    Only source indentation that exactly follows the old marker width changes.
    Standard four-space and lazy continuations remain untouched. This keeps a
    simple list valid when, for example, ``9.`` becomes ``10.`` without
    normalizing or reflowing the item's prose.
    """
    old_marker = item.marker or ""
    if not old_marker or not item.source_lines:
        return cursor_col

    first_row = item.start
    if lines[first_row].startswith(old_marker):
        lines[first_row] = new_marker + lines[first_row][len(old_marker):]
        if cursor_row == first_row:
            if cursor_col >= len(old_marker):
                cursor_col += len(new_marker) - len(old_marker)
            else:
                cursor_col = min(cursor_col, len(new_marker))

    if len(new_marker) == len(old_marker):
        return cursor_col

    for offset, source_line in enumerate(item.source_lines[1:], start=1):
        row = first_row + offset
        prefix_width = _simple_list_continuation_prefix_width(
            source_line, old_marker
        )
        if prefix_width != len(old_marker):
            continue

        # This branch is reached only for body-aligned space indentation.
        # Replace that indentation with the new marker width and preserve the
        # continuation text byte-for-byte.
        lines[row] = (" " * len(new_marker)) + source_line[prefix_width:]
        if cursor_row == row:
            if cursor_col >= prefix_width:
                cursor_col += len(new_marker) - prefix_width
            else:
                cursor_col = min(cursor_col, len(new_marker))

    return cursor_col


def renumber_ordered_list_with_cursor(full_text, cursor_position):
    """Renumber only the ordered list containing the cursor.

    The first item's number is authoritative, matching Markdown semantics and
    Convert for Carriage. Item text, blank rows, and non-list Markdown remain
    untouched. Returns ``(text, cursor, found)`` where ``found`` is False when
    the cursor is not inside a supported ordered list.
    """
    cursor_position = max(0, min(len(full_text), cursor_position))
    source_document = Document(full_text, cursor_position=cursor_position)
    cursor_row = source_document.cursor_position_row
    cursor_col = source_document.cursor_position_col

    blocks = _analyze_document_layout(full_text, WRAP_COLUMN)
    group_indexes = _ordered_list_group_at_row(blocks, cursor_row)
    if not group_indexes:
        return full_text, cursor_position, False

    first_block = blocks[group_indexes[0]]
    first_info = _ordered_list_run_info(first_block)
    if first_info is None:
        return full_text, cursor_position, False

    _indent, number = first_info
    lines = full_text.split("\n")

    for block_index in group_indexes:
        block = blocks[block_index]
        for item in block.list_items or []:
            match = _ORDERED_LIST_MARKER_PARTS_RE.match(item.marker or "")
            if match is None:
                return full_text, cursor_position, False

            new_marker = (
                f'{match.group("indent")}{number}.{match.group("spacing")}'
            )
            cursor_col = _renumber_list_item_source(
                lines,
                item,
                new_marker,
                cursor_row,
                cursor_col,
            )
            number += 1

    new_text = "\n".join(lines)
    if new_text == full_text:
        return full_text, cursor_position, True

    new_document = Document(new_text)
    new_row = min(cursor_row, new_document.line_count - 1)
    new_col = min(cursor_col, len(new_document.lines[new_row]))
    new_cursor = new_document.translate_row_col_to_index(new_row, new_col)
    return new_text, new_cursor, True


def _convert_wrap_block(block, ordered_markers=None):
    """Convert one block into Carriage's preferred Markdown representation."""
    if block.kind == "setext-heading" and block.source_lines:
        level = block.marker or "#"
        title = block.source_lines[0].strip()
        return [_canonical_setext_atx_heading(level, title)]

    if block.kind == "heading" and block.source_lines:
        parsed = _atx_heading_parts(block.source_lines[0])
        if parsed is not None:
            return [_canonical_atx_heading(*parsed)]

    if not block.wrappable:
        return list(block.source_lines)

    if block.kind == "prose":
        return _convert_markdown_prose(block.source_lines)

    if block.kind == "list" and block.marker is not None:
        return _convert_list_item(block)

    if block.kind == "list-run" and block.list_items is not None:
        rendered = []
        markers = ordered_markers
        if markers is None:
            markers = _renumbered_ordered_list_markers(block.list_items)
        if markers is not None:
            for item, marker in zip(block.list_items, markers):
                rendered.extend(_convert_list_item(item, marker=marker))
        else:
            for item in block.list_items:
                rendered.extend(_convert_list_item(item))
        return rendered

    if block.kind == "blockquote":
        if _prose_contains_multiline_inline_code(block.body_lines or []):
            return list(block.source_lines)
        rendered = []
        paragraph = []

        def flush_paragraph():
            if not paragraph:
                return
            for segment in _convert_markdown_prose(paragraph):
                rendered.append(f"> {segment}" if segment else ">")
            paragraph.clear()

        for content in block.body_lines or []:
            if content.strip():
                paragraph.append(content)
            else:
                flush_paragraph()
                if not rendered or rendered[-1] != ">":
                    rendered.append(">")
        flush_paragraph()
        return rendered or [">"]

    return list(block.source_lines)


def _conversion_needs_blank_after_setext(previous_block, previous_lines, current_lines):
    """Return True when Setext -> ATX would create a new Setext pair.

    A Setext heading consumes two physical source lines but converts to one ATX
    line. If the immediately following block begins with another ``---`` or
    ``===`` line, simply concatenating the converted blocks would make that line
    become an underline for the new ATX line on the next conversion pass. Insert
    one blank source line to preserve the original block boundary and make Convert
    for Carriage idempotent.
    """
    if previous_block is None or previous_block.kind != "setext-heading":
        return False
    if not previous_lines or not current_lines:
        return False
    if not previous_lines[-1].strip():
        return False
    first = current_lines[0]
    return bool(_SETEXT_H1_RE.match(first) or _SETEXT_H2_RE.match(first))


def convert_for_carriage_text(full_text):
    """Convert valid Markdown into Carriage's preferred source representation.

    The conversion targets original Markdown plus Carriage's pipe-table and
    footnote extensions. Setext H1/H2 headings become ATX headings; simple
    ordered-list runs are renumbered consecutively from their first item; ordinary
    hard-wrapped prose becomes one physical line per logical segment; original
    Markdown hard breaks made with two trailing spaces remain physical line
    boundaries; straightforward underscore emphasis is normalized to Carriage's
    preferred asterisk form. Line-sensitive structural blocks are preserved when Carriage
    does not have a safe compatibility transformation for them.
    """
    blocks = _analyze_document_layout(full_text, WRAP_COLUMN)
    marker_overrides = _ordered_list_marker_overrides(blocks)
    rendered = []
    previous_block = None
    previous_lines = None
    for block in blocks:
        target_lines = _convert_wrap_block(
            block, ordered_markers=marker_overrides.get(block.start)
        )
        if _conversion_needs_blank_after_setext(
            previous_block, previous_lines, target_lines
        ):
            rendered.append("")
        rendered.extend(target_lines)
        previous_block = block
        previous_lines = target_lines
    return "\n".join(rendered)


def _local_cursor_anchor(text, cursor_position):
    """Return a whitespace-stable anchor within one converted logical block."""
    cursor_position = max(0, min(len(text), cursor_position))
    units = sum(not char.isspace() for char in text[:cursor_position])
    seek_next = cursor_position < len(text) and not text[cursor_position].isspace()
    return units, seek_next


def _cursor_from_local_anchor(text, units, seek_next):
    """Resolve a local anchor without letting changes in earlier blocks matter."""
    if units <= 0:
        position = 0
    else:
        seen = 0
        position = len(text)
        for index, char in enumerate(text):
            if not char.isspace():
                seen += 1
                if seen >= units:
                    position = index + 1
                    break

    if seek_next:
        while position < len(text) and text[position].isspace():
            position += 1
    return position


def _line_offsets(lines):
    """Return character offsets for the beginning of each line in joined text."""
    offsets = []
    position = 0
    for index, line in enumerate(lines):
        offsets.append(position)
        position += len(line)
        if index < len(lines) - 1:
            position += 1
    return offsets


def _row_col_to_local_offset(lines, row, col):
    if not lines:
        return 0
    row = max(0, min(len(lines) - 1, row))
    col = max(0, min(len(lines[row]), col))
    return _line_offsets(lines)[row] + col


def _local_offset_to_row_col(lines, position):
    text = "\n".join(lines)
    position = max(0, min(len(text), position))
    document = Document(text=text, cursor_position=position)
    return document.cursor_position_row, document.cursor_position_col


def _map_local_text_cursor(source_text, target_text, source_position):
    """Map a cursor through one local normalization, ignoring prior blocks."""
    if source_text == target_text:
        return max(0, min(len(target_text), source_position))
    units, seek_next = _local_cursor_anchor(source_text, source_position)
    return _cursor_from_local_anchor(target_text, units, seek_next)


def _atx_heading_source_span(line):
    """Return source coordinates for an ATX marker and its semantic title."""
    match = re.match(r"^(#{1,6})(?!#)(?=.*\S)(.*)$", line)
    if match is None:
        return None

    marker = match.group(1)
    rest = match.group(2)
    leading = len(rest) - len(rest.lstrip(" \t"))
    title_start = match.start(2) + leading
    candidate = rest[leading:].rstrip(" \t")

    closing = re.match(r"^(.*\S)[ \t]+#+$", candidate)
    semantic = closing.group(1).rstrip(" \t") if closing is not None else candidate
    title_end = title_start + len(semantic)
    title = _canonical_heading_title(rest.lstrip(" \t"))
    return marker, title, match.start(1), match.end(1), title_start, title_end


def _map_heading_cursor(block, target_lines, source_row, source_col):
    target = target_lines[0] if target_lines else ""

    if block.kind == "setext-heading":
        if source_row > 0:
            return len(target)
        source = block.source_lines[0]
        stripped = source.strip()
        leading = len(source) - len(source.lstrip())
        title_start = leading
        title_end = title_start + len(stripped)
        target_prefix = len(block.marker or "#") + 1
        if source_col <= title_start:
            return target_prefix
        if source_col >= title_end:
            return len(target)

        # Setext trailing hashes may gain one escaping backslash per hash when
        # emitted as ATX.  Preserve the caret's semantic position around those
        # inserted characters rather than mapping by raw target width.
        local_col = max(0, min(len(stripped), source_col - title_start))
        closing_like = re.match(r"^(.*\S)([ \t]+)(#+)$", stripped)
        if closing_like is not None:
            hash_start = closing_like.start(3)
            if local_col > hash_start:
                local_col += min(local_col, len(stripped)) - hash_start
        return min(len(target), target_prefix + local_col)

    parsed = _atx_heading_source_span(block.source_lines[0])
    if parsed is None:
        return min(len(target), source_col)

    marker, _title, indent_start, marker_end, title_start, title_end = parsed
    target_prefix = len(marker) + 1
    if source_col <= indent_start:
        return 0
    if source_col <= marker_end:
        return min(len(marker), source_col - indent_start)
    if source_col < title_start:
        return target_prefix
    if source_col <= title_end:
        return min(len(target), target_prefix + (source_col - title_start))
    return len(target)


def _map_list_item_cursor(item, target_lines, target_marker, source_row, source_col):
    """Map within one list item so renumbering elsewhere cannot shift the caret."""
    marker = item.marker or ""
    relative_row = max(0, min(len(item.source_lines) - 1, source_row - item.start))

    if relative_row == 0 and source_col < len(marker):
        return min(len(target_marker), source_col)

    body_lines = item.body_lines or [""]
    body_row = max(0, min(len(body_lines) - 1, relative_row))
    if relative_row == 0:
        source_prefix_width = len(marker)
    else:
        source_prefix_width = _simple_list_continuation_prefix_width(
            item.source_lines[relative_row], marker
        ) or 0
    body_col = max(0, source_col - source_prefix_width)
    source_body_position = _row_col_to_local_offset(body_lines, body_row, body_col)
    target_body_lines = _convert_markdown_prose(body_lines)
    target_body_text = "\n".join(target_body_lines)
    source_body_text = "\n".join(body_lines)
    target_body_position = _map_local_text_cursor(
        source_body_text, target_body_text, source_body_position
    )
    target_row, target_col = _local_offset_to_row_col(
        target_body_lines, target_body_position
    )
    target_row = max(0, min(len(target_lines) - 1, target_row))
    prefix_width = len(target_marker)
    return _row_col_to_local_offset(
        target_lines, target_row, prefix_width + target_col
    )


def _map_blockquote_cursor(block, target_lines, source_row, source_col):
    body_lines = block.body_lines or [""]
    relative_row = max(0, min(len(body_lines) - 1, source_row - block.start))
    source_line = block.source_lines[relative_row]
    match = _BLOCKQUOTE_LINE_RE.match(source_line)
    prefix_width = match.start(1) if match is not None else 0
    body_col = max(0, source_col - prefix_width)
    source_position = _row_col_to_local_offset(body_lines, relative_row, body_col)

    target_body_lines = []
    for line in target_lines:
        if line == ">":
            target_body_lines.append("")
        elif line.startswith("> "):
            target_body_lines.append(line[2:])
        else:
            target_body_lines.append(line)

    target_position = _map_local_text_cursor(
        "\n".join(body_lines), "\n".join(target_body_lines), source_position
    )
    target_row, target_col = _local_offset_to_row_col(
        target_body_lines, target_position
    )
    target_row = max(0, min(len(target_lines) - 1, target_row))
    target_prefix = 1 if target_lines[target_row] == ">" else 2
    return _row_col_to_local_offset(
        target_lines, target_row, target_prefix + target_col
    )


def _map_cursor_in_converted_block(
    block, target_lines, source_row, source_col, ordered_markers=None
):
    """Map the caret only through the block whose source actually changed."""
    source_text = "\n".join(block.source_lines)
    target_text = "\n".join(target_lines)
    relative_row = max(0, min(len(block.source_lines) - 1, source_row - block.start))
    source_position = _row_col_to_local_offset(
        block.source_lines, relative_row, source_col
    )

    if source_text == target_text:
        return min(len(target_text), source_position)

    if block.kind in {"heading", "setext-heading"}:
        return _map_heading_cursor(block, target_lines, relative_row, source_col)

    if block.kind == "list" and block.marker is not None:
        return _map_list_item_cursor(
            block, target_lines, block.marker, source_row, source_col
        )

    if block.kind == "list-run" and block.list_items:
        markers = ordered_markers
        if markers is None:
            markers = _renumbered_ordered_list_markers(block.list_items)
        converted_prefix = 0
        for index, item in enumerate(block.list_items):
            marker = (
                markers[index]
                if markers is not None
                else (item.marker or "")
            )
            item_lines = _convert_list_item(item, marker=marker)
            if item.start <= source_row < item.end:
                return converted_prefix + _map_list_item_cursor(
                    item, item_lines, marker, source_row, source_col
                )
            converted_prefix += len("\n".join(item_lines)) + 1
        return min(len(target_text), source_position)

    if block.kind == "blockquote":
        return _map_blockquote_cursor(block, target_lines, source_row, source_col)

    return _map_local_text_cursor(source_text, target_text, source_position)


def convert_for_carriage_with_cursor(full_text, cursor_position):
    """Convert text and map the cursor through the affected logical block.

    Earlier block transformations never influence the cursor anchor. This is
    important for Setext-to-ATX conversion and list renumbering, both of which
    can add or remove non-whitespace source characters before the caret.
    """
    cursor_position = max(0, min(len(full_text), cursor_position))
    if cursor_position == len(full_text):
        return convert_for_carriage_text(full_text), None

    source_document = Document(text=full_text, cursor_position=cursor_position)
    source_row = source_document.cursor_position_row
    source_col = source_document.cursor_position_col

    blocks = _analyze_document_layout(full_text, WRAP_COLUMN)
    marker_overrides = _ordered_list_marker_overrides(blocks)
    rendered = []
    rendered_length = 0
    mapped_cursor = None
    previous_block = None
    previous_lines = None

    for block in blocks:
        ordered_markers = marker_overrides.get(block.start)
        target_lines = _convert_wrap_block(block, ordered_markers=ordered_markers)
        insert_boundary_blank = _conversion_needs_blank_after_setext(
            previous_block, previous_lines, target_lines
        )
        if insert_boundary_blank:
            if rendered:
                rendered_length += 1  # newline before inserted blank row
            rendered.append("")
            # The join between the inserted blank row and this block is counted
            # below by the normal ``if rendered`` separator path.

        block_start = rendered_length + (1 if rendered else 0)

        if block.start <= source_row < block.end:
            mapped_cursor = block_start + _map_cursor_in_converted_block(
                block, target_lines, source_row, source_col,
                ordered_markers=ordered_markers,
            )

        if rendered:
            rendered_length += 1
        rendered.extend(target_lines)
        rendered_length += sum(len(line) for line in target_lines)
        rendered_length += max(0, len(target_lines) - 1)
        previous_block = block
        previous_lines = target_lines

    new_text = "\n".join(rendered)
    if mapped_cursor is None:
        mapped_cursor = len(new_text)
    return new_text, max(0, min(len(new_text), mapped_cursor))


def _emphasis_run_ending_at(text, index):
    """Return (marker, run_start, run_length) for a run ending at index."""
    if index <= 0 or text[index - 1] not in "*_":
        return None
    marker = text[index - 1]
    start = index - 1
    while start > 0 and text[start - 1] == marker:
        start -= 1
    if _markdown_char_is_escaped(text, start):
        return None
    return marker, start, index - start


def _emphasis_wrapper_inside_selection(text, start, end, protected):
    """Recognize a complete 1/2/3-marker wrapper included in a selection."""
    opening = _emphasis_run_at(text, start)
    closing = _emphasis_run_ending_at(text, end)
    if opening is None or closing is None:
        return None

    marker, open_end, count = opening
    close_marker, close_start, close_count = closing
    if (
        marker != close_marker
        or count != close_count
        or count not in {1, 2, 3}
        or open_end >= close_start
    ):
        return None
    # The selected edges must contain complete delimiter runs, not slices of a
    # longer run that happens to look like emphasis after selection.
    if (start > 0 and text[start - 1] == marker) or (
        end < len(text) and text[end] == marker
    ):
        return None
    if _source_range_intersects(protected, start, open_end) or _source_range_intersects(
        protected, close_start, end
    ):
        return None

    can_open, _ = _markdown_delimiter_flanking(text, start, open_end, marker)
    _, can_close = _markdown_delimiter_flanking(text, close_start, end, marker)
    if not (can_open and can_close):
        return None

    return marker, count, open_end, close_start, start, end


def _emphasis_wrapper_around_selection(text, start, end, protected):
    """Recognize a complete 1/2/3-marker wrapper immediately outside a selection."""
    opening = _emphasis_run_ending_at(text, start)
    closing = _emphasis_run_at(text, end)
    if opening is None or closing is None:
        return None

    marker, open_start, count = opening
    close_marker, close_end, close_count = closing
    if marker != close_marker or count != close_count or count not in {1, 2, 3}:
        return None
    if _source_range_intersects(protected, open_start, start) or _source_range_intersects(
        protected, end, close_end
    ):
        return None

    can_open, _ = _markdown_delimiter_flanking(text, open_start, start, marker)
    _, can_close = _markdown_delimiter_flanking(text, end, close_end, marker)
    if not (can_open and can_close):
        return None

    return marker, count, start, end, open_start, close_end


def _formatting_selection_bounds(full_text, start, end):
    """Trim whitespace and hidden structural syntax from one-line selection."""
    start = max(0, min(len(full_text), start))
    end = max(start, min(len(full_text), end))
    if end <= start:
        return None, "selection contains no text"
    if "\n" in full_text[start:end]:
        return None, "selection crosses a source line boundary"

    document = Document(full_text, cursor_position=start)
    row = document.cursor_position_row
    line_start, line_end = _line_bounds_at_position(full_text, start)

    # Triple-click and some keyboard selections can include structural source
    # that Carriage displays in the hanging gutter. Formatting applies to the
    # visible prose, never to the hidden heading/list/blockquote marker.
    row_layout = _layout_row_map(full_text)[row]
    body_col = row_layout.structural_prefix_width
    start = max(start, line_start + body_col)

    # A legacy ATX heading may still contain optional closing hashes. If a
    # whole-line selection reaches them, keep that structural syntax outside
    # the emphasis operation just as we keep the opening marker outside it.
    line = full_text[line_start:line_end]
    heading = _atx_heading_source_span(line)
    if heading is not None:
        _marker, _title, _mstart, _mend, title_start, title_end = heading
        start = max(start, line_start + title_start)
        end = min(end, line_start + title_end)

    while start < end and full_text[start].isspace():
        start += 1
    while end > start and full_text[end - 1].isspace():
        end -= 1
    if end <= start:
        return None, "selection contains no text"
    return (start, end), None


def _toggle_emphasis_transform(full_text, start, end, kind):
    """Return one safe emphasis toggle transformation for [start, end).

    ``kind`` is ``italic`` or ``bold``. The result is
    ``(new_text, selection_start, selection_end, error)``. On uncertainty the
    original source is returned unchanged and ``error`` explains the no-op.
    """
    label = "italic" if kind == "italic" else "bold"
    bounds, error = _formatting_selection_bounds(full_text, start, end)
    if bounds is None:
        return full_text, start, end, f"Cannot toggle {label}: {error}"
    start, end = bounds

    if TABLE_SENTINEL in full_text[start:end] or FOOTNOTE_SENTINEL in full_text[start:end]:
        return full_text, start, end, f"Cannot toggle {label}: selection includes a folded object"

    protected = _inline_footnote_literal_ranges(full_text)
    if _source_range_intersects(protected, start, end):
        return full_text, start, end, f"Cannot toggle {label}: selection includes protected Markdown syntax"

    footnote_ranges = tuple((item[0], item[1]) for item in _footnote_reference_spans(full_text))
    if _source_range_intersects(footnote_ranges, start, end):
        return full_text, start, end, f"Cannot toggle {label}: selection includes a footnote reference"

    wrapper = _emphasis_wrapper_inside_selection(full_text, start, end, protected)
    if wrapper is None:
        wrapper = _emphasis_wrapper_around_selection(full_text, start, end, protected)

    if wrapper is not None:
        marker, count, content_start, content_end, replace_start, replace_end = wrapper
    else:
        # If a marker is immediately attached to either edge but does not form
        # one complete recognized wrapper, adding more syntax would be a guess.
        left_attached = start > 0 and full_text[start - 1] in "*_"
        right_attached = end < len(full_text) and full_text[end] in "*_"
        if left_attached or right_attached:
            return full_text, start, end, f"Cannot toggle {label}: ambiguous existing emphasis"
        marker = "*"
        count = 0
        content_start, content_end = start, end
        replace_start, replace_end = start, end

    # A selection may sit inside a larger emphasis span without touching its
    # delimiters (for example, selecting only `tal` in `*italic*`). Never add
    # markers in that case. The recognized wrapper is allowed only when it is
    # exactly the matched span being toggled; any additional containing/nested
    # span makes the operation heterogeneous and therefore a no-op.
    line_start, line_end = _line_bounds_at_position(full_text, content_start)
    recognized_span = (replace_start, replace_end) if count else None
    for open_start, _open_end, _close_start, close_end, _family, _run_count in _emphasis_spans_in_range(
        full_text, line_start, line_end, protected=protected
    ):
        if close_end <= start or open_start >= end:
            continue
        if recognized_span == (open_start, close_end):
            continue
        return full_text, start, end, f"Cannot toggle {label}: selection overlaps existing emphasis"

    if recognized_span is not None:
        left_nested = (
            replace_start > line_start
            and full_text[replace_start - 1] in "*_"
            and not _markdown_char_is_escaped(full_text, replace_start - 1)
        )
        right_nested = (
            replace_end < line_end
            and full_text[replace_end] in "*_"
            and not _markdown_char_is_escaped(full_text, replace_end)
        )
        if left_nested or right_nested:
            return full_text, start, end, f"Cannot toggle {label}: ambiguous nested emphasis"

    if content_end <= content_start:
        return full_text, start, end, f"Cannot toggle {label}: selection contains no text"
    if full_text[content_start].isspace() or full_text[content_end - 1].isspace():
        return full_text, start, end, f"Cannot toggle {label}: ambiguous emphasis boundaries"
    if _range_has_emphasis_delimiter(
        full_text, content_start, content_end, protected=protected
    ):
        return full_text, start, end, f"Cannot toggle {label}: selection contains mixed emphasis"

    italic_on = count in {1, 3}
    bold_on = count in {2, 3}
    if kind == "italic":
        italic_on = not italic_on
    else:
        bold_on = not bold_on
    new_count = (1 if italic_on else 0) + (2 if bold_on else 0)

    content = full_text[content_start:content_end]
    delimiter = marker * new_count
    replacement = delimiter + content + delimiter
    new_text = full_text[:replace_start] + replacement + full_text[replace_end:]
    new_selection_start = replace_start + new_count
    new_selection_end = new_selection_start + len(content)
    return new_text, new_selection_start, new_selection_end, None


def _toggle_selected_emphasis(kind):
    """Toggle one emphasis attribute on the main editor's active selection."""
    buf = text_area.buffer
    label = "italic" if kind == "italic" else "bold"
    if buf.selection_state is None:
        show_transient_status(f"Select text to toggle {label}.")
        return
    ranges = list(buf.document.selection_ranges())
    if len(ranges) != 1:
        show_transient_status(f"Cannot toggle {label}: unsupported selection shape")
        return
    if _selection_intersects_folded_object(buf):
        show_transient_status(f"Cannot toggle {label}: selection includes a folded object")
        return

    start, end = ranges[0]
    new_text, new_start, new_end, error = _toggle_emphasis_transform(
        buf.text, start, end, kind
    )
    if error is not None:
        show_transient_status(error)
        return
    if new_text == buf.text:
        return

    buf.save_to_undo_stack()
    buf.set_document(
        Document(text=new_text, cursor_position=new_end),
        bypass_readonly=True,
    )
    _select_source_range(buf, (new_start, new_end))
    get_app().invalidate()


def do_toggle_italic():
    _toggle_selected_emphasis("italic")


def do_toggle_bold():
    _toggle_selected_emphasis("bold")


def do_renumber_list():
    """Renumber the ordered list containing the cursor, preserving its start."""
    buf = text_area.buffer
    new_text, new_cursor, found = renumber_ordered_list_with_cursor(
        buf.text, buf.cursor_position
    )
    if not found:
        show_message(
            "No numbered list",
            "Place the cursor inside a supported numbered list first.",
        )
        return
    if new_text == buf.text:
        return

    buf.save_to_undo_stack()
    buf.set_document(
        Document(text=new_text, cursor_position=new_cursor),
        bypass_readonly=True,
    )


def _normalize_footnote_source_lines(note):
    """Normalize emphasis only in a folded footnote's body source."""
    if note.original_lines is None:
        return None
    rendered = []
    for index, line in enumerate(note.original_lines):
        if index == 0:
            match = _FOOTNOTE_DEFINITION_RE.match(line)
            if match is None:
                rendered.append(line)
                continue
            body_start = match.start(2)
            rendered.append(
                line[:body_start]
                + _normalize_underscore_emphasis_inline(line[body_start:])
            )
            continue

        continuation = _footnote_continuation_text(line)
        if continuation is None:
            rendered.append(line)
            continue
        prefix_width = len(line) - len(continuation)
        rendered.append(
            line[:prefix_width]
            + _normalize_underscore_emphasis_inline(continuation)
        )
    return rendered


def _normalize_folded_object_emphasis():
    """Return copy-on-write table/footnote mappings normalized for Convert."""
    tables = state.tables
    footnotes = state.footnotes
    tables_changed = False
    footnotes_changed = False

    updated_tables = dict(tables)
    for number, table in tables.items():
        headers = [_normalize_underscore_emphasis_inline(value) for value in table.headers]
        rows = [
            [_normalize_underscore_emphasis_inline(value) for value in row]
            for row in table.rows
        ]
        title = _normalize_underscore_emphasis_inline(table.title)
        original_lines = (
            None
            if table.original_lines is None
            else [
                _normalize_underscore_emphasis_inline(line)
                for line in table.original_lines
            ]
        )
        if (
            headers != table.headers
            or rows != table.rows
            or title != table.title
            or original_lines != table.original_lines
        ):
            updated_tables[number] = TableData(
                headers=headers,
                rows=rows,
                title=title,
                alignments=list(table.alignments),
                original_lines=original_lines,
                caption_position=table.caption_position,
                dirty=table.dirty,
            )
            tables_changed = True

    updated_footnotes = dict(footnotes)
    for identifier, note in footnotes.items():
        text = _normalize_underscore_emphasis_inline(note.text)
        original_lines = _normalize_footnote_source_lines(note)
        if text != note.text or original_lines != note.original_lines:
            updated_footnotes[identifier] = FootnoteData(
                identifier=note.identifier,
                text=text,
                original_lines=original_lines,
                dirty=note.dirty,
            )
            footnotes_changed = True

    return (
        updated_tables if tables_changed else tables,
        updated_footnotes if footnotes_changed else footnotes,
        tables_changed or footnotes_changed,
    )


def do_convert_for_carriage():
    """Convert the working document to Carriage's preferred Markdown form."""
    buf = text_area.buffer
    old_text = buf.text
    old_cursor = buf.cursor_position
    new_text, new_cursor = convert_for_carriage_with_cursor(old_text, old_cursor)
    new_tables, new_footnotes, objects_changed = _normalize_folded_object_emphasis()

    # A table title is part of its folded prose placeholder. Underscore to
    # asterisk normalization is length-preserving, so refreshing those labels
    # cannot disturb the cursor mapping produced above.
    if new_tables is not state.tables:
        new_text = _canonicalize_table_placeholders(new_text, new_tables)

    if new_text == old_text and not objects_changed:
        return

    if new_cursor is None:
        new_cursor = len(new_text)
    _commit_folded_object_transaction(
        buf,
        Document(text=new_text, cursor_position=new_cursor),
        tables=new_tables,
        footnotes=new_footnotes,
    )


def do_undo():
    text_area.buffer.undo()


def do_redo():
    text_area.buffer.redo()


# ---------------------------------------------------------------------------
# Find / Replace
# ---------------------------------------------------------------------------

def _find_replace_word_char(char):
    """Return whether char participates in Carriage's whole-word boundary."""
    return bool(char) and (char.isalnum() or char == "_")


def _find_replace_matches(text, query, *, case_sensitive=False, whole_word=False):
    """Return literal, editable match spans in source order.

    Search is deliberately literal rather than regular-expression based. Folded
    table/footnote placeholders are presentation objects, so their source labels
    are excluded from search and replacement just as direct editing excludes them.
    """
    if not query:
        return ()

    pattern = re.escape(query)
    if whole_word:
        if _find_replace_word_char(query[0]):
            pattern = r"(?<!\w)" + pattern
        if _find_replace_word_char(query[-1]):
            pattern = pattern + r"(?!\w)"
    flags = 0 if case_sensitive else re.IGNORECASE
    return tuple(
        (match.start(), match.end())
        for match in re.finditer(pattern, text, flags)
        if not _folded_edit_range_intersects(text, match.start(), match.end())
    )


def _set_find_replace_input(control, text, *, cursor_position=None):
    if cursor_position is None:
        cursor_position = len(text)
    cursor_position = max(0, min(len(text), cursor_position))
    control.buffer.set_document(
        Document(text=text, cursor_position=cursor_position), bypass_readonly=True
    )


def _find_replace_single_line_text(text):
    """Normalize pasted CR/LF sequences so status-line inputs stay one line."""
    return text.replace("\r\n", "\n").replace("\r", "\n").replace("\n", " ")


def _find_replace_sanitize_input(control):
    """Return a one-line value, repairing pasted newlines without event recursion."""
    raw = control.text
    clean = _find_replace_single_line_text(raw)
    if clean == raw:
        return clean

    raw_cursor = control.buffer.cursor_position
    clean_cursor = len(_find_replace_single_line_text(raw[:raw_cursor]))
    session = find_replace
    was_suppressed = session.suppress_input_events
    session.suppress_input_events = True
    try:
        _set_find_replace_input(control, clean, cursor_position=clean_cursor)
    finally:
        session.suppress_input_events = was_suppressed
    return clean


def _find_replace_refocus_input():
    """Return keyboard focus to the active Find/Replace field."""
    if not find_replace.active:
        return
    target = replace_input if find_replace.mode == "replace" else find_input
    get_app().layout.focus(target)
    get_app().invalidate()


def _find_replace_reanchor_after_document_mouse(anchor):
    """Use a prose click as a new search origin without surrendering input focus."""
    session = find_replace
    if not session.active:
        return
    buf = text_area.buffer
    anchor = max(0, min(len(buf.text), anchor))
    session.search_anchor = anchor
    session.current_match = None
    session.match_index = -1
    session.wrapped = False

    spans = _find_replace_matches(
        buf.text,
        session.query,
        case_sensitive=session.case_sensitive,
        whole_word=session.whole_word,
    )
    session.match_count = len(spans)
    if not spans:
        _find_replace_clear_match(cursor_position=anchor)
    else:
        hit = next(
            (i for i, (start, end) in enumerate(spans) if start <= anchor < end),
            None,
        )
        if hit is not None:
            _find_replace_select_match(spans, hit, wrapped=False)
        else:
            _find_replace_refresh_from_anchor(anchor=anchor)
    _find_replace_refocus_input()


def _find_replace_clear_match(*, cursor_position=None):
    buf = text_area.buffer
    buf.exit_selection()
    if cursor_position is not None:
        buf.cursor_position = max(0, min(len(buf.text), cursor_position))
    find_replace.current_match = None
    find_replace.match_index = -1


def _find_replace_select_match(spans, index, *, wrapped=False):
    buf = text_area.buffer
    start, end = spans[index]
    buf.exit_selection()
    buf.cursor_position = start
    buf.start_selection(selection_type=SelectionType.CHARACTERS)
    buf.cursor_position = end
    find_replace.current_match = (start, end)
    find_replace.match_index = index
    find_replace.match_count = len(spans)
    find_replace.wrapped = bool(wrapped)
    text_area.window.end_manual_scroll()
    get_app().invalidate()


def _find_replace_refresh_from_anchor(anchor=None, direction=1):
    """Select the first match from anchor, wrapping once when necessary."""
    session = find_replace
    buf = text_area.buffer
    spans = _find_replace_matches(
        buf.text,
        session.query,
        case_sensitive=session.case_sensitive,
        whole_word=session.whole_word,
    )
    session.match_count = len(spans)
    session.wrapped = False
    position = session.search_anchor if anchor is None else anchor
    position = max(0, min(len(buf.text), position))
    if not spans:
        _find_replace_clear_match(cursor_position=position)
        get_app().invalidate()
        return False

    wrapped = False
    if direction >= 0:
        index = next((i for i, (start, _end) in enumerate(spans) if start >= position), None)
        if index is None:
            index = 0
            wrapped = True
    else:
        eligible = [i for i, (_start, end) in enumerate(spans) if end <= position]
        if eligible:
            index = eligible[-1]
        else:
            index = len(spans) - 1
            wrapped = True
    _find_replace_select_match(spans, index, wrapped=wrapped)
    return True


def _find_replace_step(direction):
    """Move to the next/previous current-query match with wraparound."""
    session = find_replace
    buf = text_area.buffer
    spans = _find_replace_matches(
        buf.text,
        session.query,
        case_sensitive=session.case_sensitive,
        whole_word=session.whole_word,
    )
    session.match_count = len(spans)
    if not spans:
        _find_replace_clear_match(cursor_position=session.search_anchor)
        session.wrapped = False
        get_app().invalidate()
        return False

    current = session.current_match
    if current in spans:
        index = spans.index(current)
        new_index = index + (1 if direction >= 0 else -1)
        wrapped = not (0 <= new_index < len(spans))
        new_index %= len(spans)
    else:
        position = buf.cursor_position
        if direction >= 0:
            new_index = next(
                (i for i, (start, _end) in enumerate(spans) if start >= position),
                0,
            )
            wrapped = all(start < position for start, _end in spans)
        else:
            eligible = [i for i, (_start, end) in enumerate(spans) if end <= position]
            if eligible:
                new_index = eligible[-1]
                wrapped = False
            else:
                new_index = len(spans) - 1
                wrapped = True

    _find_replace_select_match(spans, new_index, wrapped=wrapped)
    return True


def _find_replace_query_changed(_buffer=None):
    session = find_replace
    if not session.active or session.suppress_input_events:
        return
    session.query = _find_replace_sanitize_input(find_input)
    session.current_match = None
    session.match_index = -1
    _find_replace_refresh_from_anchor()


def _find_replace_replacement_changed(_buffer=None):
    if find_replace.active and not find_replace.suppress_input_events:
        find_replace.replacement = _find_replace_sanitize_input(replace_input)
        get_app().invalidate()


def _find_replace_toggle_case():
    session = find_replace
    anchor = session.current_match[0] if session.current_match is not None else session.search_anchor
    session.case_sensitive = not session.case_sensitive
    session.current_match = None
    _find_replace_refresh_from_anchor(anchor=anchor)


def _find_replace_toggle_whole_word():
    session = find_replace
    anchor = session.current_match[0] if session.current_match is not None else session.search_anchor
    session.whole_word = not session.whole_word
    session.current_match = None
    _find_replace_refresh_from_anchor(anchor=anchor)


def _find_replace_show_replace():
    if not find_replace.active:
        return
    find_replace.mode = "replace"
    get_app().layout.focus(replace_input)
    get_app().invalidate()


def _find_replace_show_find():
    if not find_replace.active:
        return
    find_replace.mode = "find"
    get_app().layout.focus(find_input)
    get_app().invalidate()


def _find_replace_current_span():
    session = find_replace
    spans = _find_replace_matches(
        text_area.buffer.text,
        session.query,
        case_sensitive=session.case_sensitive,
        whole_word=session.whole_word,
    )
    if session.current_match in spans:
        return session.current_match
    if not spans:
        session.match_count = 0
        return None
    _find_replace_refresh_from_anchor(anchor=text_area.buffer.cursor_position)
    return session.current_match


def _find_replace_replace_current():
    """Replace the selected occurrence as one normal undoable editor change."""
    session = find_replace
    buf = text_area.buffer
    session.replacement = replace_input.text
    span = _find_replace_current_span()
    if span is None:
        get_app().invalidate()
        return

    start, end = span
    old_text = buf.text
    new_text = old_text[:start] + session.replacement + old_text[end:]
    next_anchor = start + len(session.replacement)
    session.current_match = None
    session.match_index = -1
    session.search_anchor = next_anchor

    if new_text != old_text:
        _commit_folded_object_transaction(
            buf,
            Document(text=new_text, cursor_position=next_anchor),
            selection=None,
        )
        session.changed = True
    else:
        buf.exit_selection()
        buf.cursor_position = next_anchor

    _find_replace_refresh_from_anchor(anchor=next_anchor)
    get_app().layout.focus(replace_input)


def _find_replace_replace_all():
    """Replace every editable match in one document transaction / Undo step."""
    session = find_replace
    buf = text_area.buffer
    session.replacement = replace_input.text
    spans = _find_replace_matches(
        buf.text,
        session.query,
        case_sensitive=session.case_sensitive,
        whole_word=session.whole_word,
    )
    if not spans:
        session.match_count = 0
        get_app().invalidate()
        return

    pieces = []
    last = 0
    for start, end in spans:
        pieces.append(buf.text[last:start])
        pieces.append(session.replacement)
        last = end
    pieces.append(buf.text[last:])
    new_text = "".join(pieces)
    changed_count = sum(
        1
        for start, end in spans
        if buf.text[start:end] != session.replacement
    )
    first_end = spans[0][0] + len(session.replacement)

    if new_text == buf.text:
        # Matching text was found, but applying the requested replacement would
        # not alter the document. Do not create an undo transaction or claim
        # that replacements were made. Leave the writer at the current match.
        _close_find_replace(message="No changes made.")
        return

    _commit_folded_object_transaction(
        buf,
        Document(text=new_text, cursor_position=first_end),
        selection=None,
    )
    session.changed = True

    _close_find_replace(
        cursor_position=first_end,
        message=(
            f"Replaced {changed_count} "
            f"occurrence{'s' if changed_count != 1 else ''}."
        ),
    )


def _close_find_replace(*, cursor_position=None, message=None):
    """Leave the one-line Find/Replace UI and return focus to prose."""
    session = find_replace
    if not session.active:
        return
    buf = text_area.buffer
    current = session.current_match
    session.active = False
    buf.exit_selection()

    if cursor_position is not None:
        buf.cursor_position = max(0, min(len(buf.text), cursor_position))
    elif current is not None:
        # The selection cursor sits at the end of the match; keep the writer at
        # the location they chose when Find closes.
        buf.cursor_position = min(len(buf.text), current[1])
    elif not session.changed:
        buf.cursor_position = max(0, min(len(buf.text), session.origin_cursor))
        if session.origin_selection is not None:
            buf.selection_state = copy.copy(session.origin_selection)

    session.mode = "find"
    session.current_match = None
    session.match_index = -1
    session.match_count = 0
    session.wrapped = False
    session.suppress_input_events = False
    get_app().layout.focus(text_area)
    if message:
        show_transient_status(message)
    get_app().invalidate()


def do_find_replace():
    """Open Carriage's status-line literal Find/Replace interface."""
    if current_float is not None:
        return
    session = find_replace
    buf = text_area.buffer

    if session.active:
        _find_replace_show_find()
        return

    session.origin_cursor = buf.cursor_position
    session.origin_selection = copy.copy(buf.selection_state)
    session.search_anchor = buf.cursor_position
    state.extend_selection_mode = False
    prefill = ""
    if buf.selection_state is not None:
        start, end = buf.document.selection_range()
        candidate = buf.text[start:end]
        # The status-line input is intentionally single-line. Never expose the
        # hidden source representation of a folded object as a search term.
        if (
            candidate
            and "\n" not in candidate
            and not _folded_edit_range_intersects(buf.text, start, end)
        ):
            prefill = candidate
            session.search_anchor = start

    buf.exit_selection()
    session.active = True
    session.mode = "find"
    session.query = prefill
    session.replacement = ""
    session.current_match = None
    session.match_index = -1
    session.match_count = 0
    session.wrapped = False
    session.changed = False
    session.suppress_input_events = True
    try:
        _set_find_replace_input(find_input, prefill)
        _set_find_replace_input(replace_input, "")
    finally:
        session.suppress_input_events = False

    if prefill:
        _find_replace_refresh_from_anchor()
    else:
        _find_replace_clear_match(cursor_position=session.search_anchor)

    _clear_transient_status_message()
    get_app().layout.focus(find_input)
    get_app().invalidate()


def _find_replace_progress_text():
    session = find_replace
    if not session.query:
        return "type to search"
    if session.match_count <= 0 or session.match_index < 0:
        return "no matches"
    label = f"{session.match_index + 1}/{session.match_count}"
    return label + (" wrap" if session.wrapped else "")


def _find_replace_hint_text():
    """Keep the command legend useful without starving the editable field."""
    try:
        columns = get_app().output.get_size().columns
    except Exception:
        columns = 80
    progress = _find_replace_progress_text()
    session = find_replace

    if session.mode == "replace":
        if columns >= 105:
            return f" {progress}  Enter replace  ↓ skip  ↑ previous  Alt+A all  Tab find  Esc done "
        if columns >= 75:
            return f" {progress}  Enter repl  ↓ skip  ↑ prev  Alt+A all  Tab find  Esc "
        return f" {progress}  Enter repl  ↓/↑  Alt+A all  Esc "

    case = "on" if session.case_sensitive else "off"
    word = "on" if session.whole_word else "off"
    if columns >= 110:
        return f" {progress}  Enter/↓ next  ↑ previous  Tab replace  Alt+C case:{case}  Alt+W word:{word}  Esc done "
    if columns >= 78:
        return f" {progress}  Enter/↓ next  ↑ prev  Tab repl  C:{case} W:{word}  Esc "
    return f" {progress}  Enter/↓  ↑  Tab repl  Esc "


def _folded_edit_warning():
    show_message(
        "Folded object",
        "Tables and folded footnote definitions are atomic objects. "
        "Use their Tools menu commands to edit or delete them.",
    )


def _leave_extend_selection_mode():
    """Return F6 selection movement to ordinary editor navigation."""
    state.extend_selection_mode = False


def do_cut():
    buf = text_area.buffer
    if buf.selection_state is None:
        _leave_extend_selection_mode()
        return
    if _folded_placeholder_locked() or _selection_intersects_folded_object(buf):
        _folded_edit_warning()
        return
    # Menu commands do not receive prompt_toolkit's keybinding-time automatic
    # Undo snapshot. Save explicitly; keyboard invocation safely deduplicates.
    buf.save_to_undo_stack()
    data = buf.cut_selection()
    get_app().clipboard.set_data(data)
    _leave_extend_selection_mode()


def do_copy():
    buf = text_area.buffer
    if buf.selection_state is None:
        _leave_extend_selection_mode()
        return
    # Do not leak Carriage's invisible object sentinels into the clipboard or
    # create pasted pseudo-objects that have no attached object data.
    if _selection_intersects_folded_object(buf):
        _folded_edit_warning()
        return
    data = buf.copy_selection()
    get_app().clipboard.set_data(data)
    _leave_extend_selection_mode()


def do_paste():
    buf = text_area.buffer
    if _folded_placeholder_locked() or _selection_intersects_folded_object(buf):
        _folded_edit_warning()
        return

    # Read first: an empty/non-text clipboard must never delete an active
    # selection merely because Paste was invoked.
    data = _normalized_clipboard_data(get_app().clipboard.get_data())
    if not data.text:
        _leave_extend_selection_mode()
        return

    # Menu commands need the same unified Undo snapshot as Ctrl+V.
    buf.save_to_undo_stack()
    if buf.selection_state is not None:
        buf.cut_selection()
    buf.paste_clipboard_data(data)
    _leave_extend_selection_mode()


def _dialog_buffer_cut(buf):
    """Cut an active selection from a simple dialog editor to the clipboard."""
    if buf.selection_state is not None:
        get_app().clipboard.set_data(buf.cut_selection())


def _dialog_buffer_copy(buf):
    """Copy an active selection from a simple dialog editor to the clipboard."""
    if buf.selection_state is not None:
        get_app().clipboard.set_data(buf.copy_selection())


def _dialog_buffer_paste(buf):
    """Paste into a simple dialog editor, replacing any active selection."""
    data = _normalized_clipboard_data(get_app().clipboard.get_data())
    if not data.text:
        return
    if buf.selection_state is not None:
        buf.cut_selection()
    buf.paste_clipboard_data(data)



def _ensure_config_file():
    """Create config.toml on first launch and return a warning on failure."""
    path = _config_path()
    if os.path.exists(path):
        return None
    try:
        _write_config(_CONFIG)
    except OSError as e:
        # A read-only or unavailable config home must never prevent startup,
        # but the writer should know that preferences cannot be persisted.
        return f"Could not create config.toml ({e}). Settings will not persist."
    return None


def do_toggle_statusbar():
    """Toggle the status bar for this session only."""
    state.statusbar_visible = not state.statusbar_visible
    get_app().invalidate()


# ---------------------------------------------------------------------------
# Dedicated table editor
# ---------------------------------------------------------------------------

def _table_rows(session):
    return [session.working.headers] + session.working.rows


def _table_cell_label(session):
    return (
        f"Header · column {session.selected_col + 1}"
        if session.selected_row == 0
        else f"Row {session.selected_row} · column {session.selected_col + 1}"
    )


def _table_mode_hint(session):
    if session.editing:
        return "Edit: Enter commit · Esc discard · ^S save table"
    return "←↑↓→ move · Enter edit · R row · C col · ^S save · Esc cancel"


def _update_table_editor_ui(session):
    if session.cell_label is not None:
        session.cell_label.text = _table_cell_label(session)
    if session.mode_label is not None:
        session.mode_label.text = _table_mode_hint(session)
    get_app().invalidate()


def _commit_table_editor_cell(session):
    if session.cell_editor is None:
        return
    rows = _table_rows(session)
    rows[session.selected_row][session.selected_col] = " ".join(
        session.cell_editor.text.splitlines()
    )


def _commit_table_editor_title(session):
    if session.title_editor is None:
        return
    title = " ".join(session.title_editor.text.splitlines()).strip()
    if title != session.working.title:
        session.working.title = title
        if title and session.working.caption_position is None:
            session.working.caption_position = "after"
        if not title:
            session.working.caption_position = None
        session.working.dirty = True


def _load_table_editor_cell(session):
    rows = _table_rows(session)
    value = rows[session.selected_row][session.selected_col]
    if session.cell_editor is not None:
        session.cell_editor.buffer.reset(
            Document(text=value, cursor_position=len(value))
        )
    _update_table_editor_ui(session)


def _focus_table_navigation(session):
    if session.grid_window is not None:
        get_app().layout.focus(session.grid_window)
    _update_table_editor_ui(session)


def _focus_table_title(session):
    """Move focus from table navigation into the title editor."""
    if session.title_editor is not None:
        get_app().layout.focus(session.title_editor)
        session.title_editor.buffer.cursor_position = len(session.title_editor.text)
    _update_table_editor_ui(session)


def _begin_table_cell_edit():
    session = current_table_editor
    if session is None or session.cell_editor is None:
        return
    _load_table_editor_cell(session)
    session.editing = True
    _update_table_editor_ui(session)
    get_app().layout.focus(session.cell_editor)


def _finish_table_cell_edit():
    session = current_table_editor
    if session is None:
        return
    _commit_table_editor_cell(session)
    session.editing = False
    _focus_table_navigation(session)


def _cancel_table_cell_edit():
    session = current_table_editor
    if session is None:
        return
    # The working table is not changed until a cell is committed, so reload
    # the stored value and return to navigation mode without altering it.
    session.editing = False
    _load_table_editor_cell(session)
    _focus_table_navigation(session)


def _move_table_editor_cell(delta):
    """Move sequentially through cells; used by Tab/Shift+Tab in navigation."""
    session = current_table_editor
    if session is None or session.editing:
        return
    rows = _table_rows(session)
    columns = session.working.column_count
    total = len(rows) * columns
    current = session.selected_row * columns + session.selected_col
    target = max(0, min(total - 1, current + delta))
    old_row = session.selected_row
    session.selected_row, session.selected_col = divmod(target, columns)
    if session.selected_row > old_row:
        session.scroll_anchor = "bottom"
    elif session.selected_row < old_row:
        session.scroll_anchor = "top"
    _load_table_editor_cell(session)


def _move_table_editor_col(delta):
    """Move left/right in navigation mode without wrapping to another row."""
    session = current_table_editor
    if session is None or session.editing:
        return
    session.selected_col = max(
        0,
        min(session.working.column_count - 1, session.selected_col + delta),
    )
    _load_table_editor_cell(session)


def _move_table_editor_row(delta):
    """Move up/down in navigation mode while staying in the same column."""
    session = current_table_editor
    if session is None or session.editing:
        return
    rows = _table_rows(session)
    old_row = session.selected_row
    session.selected_row = max(0, min(len(rows) - 1, session.selected_row + delta))
    if session.selected_row > old_row:
        session.scroll_anchor = "bottom"
    elif session.selected_row < old_row:
        session.scroll_anchor = "top"
    _load_table_editor_cell(session)


def _insert_table_editor_row(where):
    """Insert a blank data row above or below the selected data row."""
    session = current_table_editor
    if session is None:
        return

    _commit_table_editor_cell(session)
    columns = session.working.column_count

    if where == "above":
        if session.selected_row == 0:
            show_message(
                "Header row",
                "The header must remain the first row. Use Insert Below to add the first data row.",
            )
            return
        insert_at = session.selected_row - 1
        session.working.rows.insert(insert_at, [""] * columns)
        # The inserted row occupies the selected visual row.
    elif where == "below":
        if session.selected_row == 0:
            insert_at = 0
            session.working.rows.insert(insert_at, [""] * columns)
            session.selected_row = 1
        else:
            insert_at = session.selected_row
            session.working.rows.insert(insert_at, [""] * columns)
            session.selected_row += 1
    else:
        return

    session.working.dirty = True
    _working_state_changed()
    _load_table_editor_cell(session)


def _delete_table_editor_row():
    """Delete the selected data row; the header row is never deletable."""
    session = current_table_editor
    if session is None:
        return

    _commit_table_editor_cell(session)
    if session.selected_row == 0:
        show_message("Header row", "The table header cannot be deleted.")
        return

    del session.working.rows[session.selected_row - 1]
    session.selected_row = min(session.selected_row, len(session.working.rows))
    session.working.dirty = True
    _working_state_changed()
    _load_table_editor_cell(session)


def _insert_table_editor_column(where):
    """Insert a blank column to the left or right of the selected column."""
    session = current_table_editor
    if session is None:
        return

    _commit_table_editor_cell(session)
    if session.working.column_count >= MAX_TABLE_EDITOR_COLUMNS:
        show_message(
            "Table too wide",
            f"The basic table editor supports at most {MAX_TABLE_EDITOR_COLUMNS} columns.",
        )
        return

    if where == "left":
        insert_at = session.selected_col
    elif where == "right":
        insert_at = session.selected_col + 1
    else:
        return

    session.working.headers.insert(insert_at, "")
    for row in session.working.rows:
        row.insert(insert_at, "")
    session.working.alignments.insert(insert_at, "default")
    session.selected_col = insert_at
    session.working.dirty = True
    _working_state_changed()
    _load_table_editor_cell(session)


def _delete_table_editor_column():
    """Delete the selected column, while keeping at least two columns."""
    session = current_table_editor
    if session is None:
        return

    _commit_table_editor_cell(session)
    if session.working.column_count <= 2:
        show_message(
            "Minimum columns",
            "A table must contain at least two columns.",
        )
        return

    delete_at = session.selected_col
    del session.working.headers[delete_at]
    for row in session.working.rows:
        del row[delete_at]
    if delete_at < len(session.working.alignments):
        del session.working.alignments[delete_at]
    session.selected_col = min(delete_at, session.working.column_count - 1)
    session.working.dirty = True
    _working_state_changed()
    _load_table_editor_cell(session)


def _run_table_editor_command(action):
    """Close a row/column command popup, then apply its table operation."""
    close_dialog()
    action()


def _table_command_button(text, handler):
    """Create a table command button wide enough to show its full caption.

    prompt_toolkit's Button defaults to 12 columns, which clips longer table
    commands such as ``Insert Above`` and ``Delete Column`` (usually losing
    the right ``>`` and sometimes caption characters).  Size these submenu
    buttons from their rendered cell width instead.
    """
    return Button(
        text=text,
        handler=handler,
        width=max(12, get_cwidth(text) + 4),
    )


def _show_table_command_dialog(title, message, buttons, width, focus=None):
    """Show a fully opaque table row/column command popup.

    The stock prompt_toolkit Dialog leaves portions of narrow rows effectively
    transparent in this table-editor context, allowing underlying grid lines to
    show through and visually cut the right frame border. Build these small
    popups with explicit filler windows so the message row and button row paint
    their entire width using the dialog background.
    """
    buttons_kb = KeyBindings()
    if len(buttons) > 1:
        first_selected = has_focus(buttons[0])
        last_selected = has_focus(buttons[-1])
        buttons_kb.add("left", filter=~first_selected)(focus_previous)
        buttons_kb.add("right", filter=~last_selected)(focus_next)

    kb = KeyBindings()
    kb.add("tab", filter=~has_completions)(focus_next)
    kb.add("s-tab", filter=~has_completions)(focus_previous)

    body_row = VSplit(
        [
            _dialog_prose(message, width=52),
            Window(style="class:dialog.body"),
        ]
    )
    buttons_row = VSplit(
        [*buttons, Window(style="class:dialog.body")],
        padding=1,
        key_bindings=buttons_kb,
    )
    frame_body = HSplit(
        [
            Box(
                body=body_row,
                padding=D(preferred=1, max=1),
                padding_bottom=0,
                style="class:dialog.body",
            ),
            Box(
                body=buttons_row,
                height=D(min=1, max=3, preferred=3),
                style="class:dialog.body",
            ),
        ],
        style="class:dialog.body",
    )
    dialog = Shadow(
        body=Frame(
            title=title,
            body=frame_body,
            style="class:dialog.body",
            width=width,
            key_bindings=kb,
            modal=True,
        )
    )
    show_dialog(dialog, focus=focus if focus is not None else buttons[0])

def _show_table_row_menu():
    session = current_table_editor
    if session is None:
        return
    if session.editing:
        _commit_table_editor_cell(session)
        session.editing = False
        _update_table_editor_ui(session)

    above = _table_command_button(
        "Insert Above",
        lambda: _run_table_editor_command(lambda: _insert_table_editor_row("above")),
    )
    below = _table_command_button(
        "Insert Below",
        lambda: _run_table_editor_command(lambda: _insert_table_editor_row("below")),
    )
    delete = _table_command_button(
        "Delete Row",
        lambda: _run_table_editor_command(_delete_table_editor_row),
    )
    cancel = _table_command_button("Cancel", close_dialog)
    _show_table_command_dialog(
        title="Row",
        message="Change the selected table row.",
        buttons=[above, below, delete, cancel],
        width=D(preferred=70),
        focus=below if session.selected_row == 0 else above,
    )


def _show_table_column_menu():
    session = current_table_editor
    if session is None:
        return
    if session.editing:
        _commit_table_editor_cell(session)
        session.editing = False
        _update_table_editor_ui(session)

    left = _table_command_button(
        "Insert Left",
        lambda: _run_table_editor_command(lambda: _insert_table_editor_column("left")),
    )
    right = _table_command_button(
        "Insert Right",
        lambda: _run_table_editor_command(lambda: _insert_table_editor_column("right")),
    )
    delete = _table_command_button(
        "Delete Column",
        lambda: _run_table_editor_command(_delete_table_editor_column),
    )
    cancel = _table_command_button("Cancel", close_dialog)
    _show_table_command_dialog(
        title="Column",
        message="Change the selected table column.",
        buttons=[left, right, delete, cancel],
        width=D(preferred=76),
        focus=right,
    )


def _table_grid_cell_width(columns, terminal_width):
    """Return a cell width that keeps the complete table grid on screen.

    The grid needs three non-content cells per column (two cell-padding spaces
    plus one vertical border) and one final outer border.  Earlier versions
    forced an eight-character minimum even when the terminal could not contain
    that grid, so a six-column table clipped on narrow screens.  Shrink the
    display-only cells as far as one character when necessary; source table
    contents are never changed.
    """
    columns = max(1, int(columns))
    terminal_width = max(1, int(terminal_width))
    available = min(120, max(1, terminal_width - 12))
    border_and_padding = (3 * columns) + 1
    return max(1, (available - border_and_padding) // columns)


def _minimum_table_editor_terminal_width(columns):
    """Return the narrowest terminal that can represent every grid column."""
    columns = max(1, int(columns))
    minimum_grid_width = (4 * columns) + 1  # one content cell + frame/padding
    return minimum_grid_width + 12


def _wrap_table_grid_cell(text, width):
    """Wrap display-only table text so a long token cannot widen the grid."""
    return textwrap.wrap(
        str(text),
        width=max(1, int(width)),
        break_long_words=True,
        break_on_hyphens=False,
        replace_whitespace=False,
    ) or [""]


@dataclass(frozen=True)
class _TableGridLayout:
    """One terminal-width-specific display layout for the basic table editor."""

    columns: int
    cell_width: int
    top: str
    middle: str
    bottom: str
    wrapped_rows: tuple
    row_heights: tuple
    natural_body_height: int


def _table_grid_layout(session):
    """Return cached geometry and wrapped cells for the current working table."""
    columns = session.working.column_count
    try:
        terminal_width = get_app().output.get_size().columns
    except Exception:
        terminal_width = 100

    rows = _table_rows(session)
    content_key = tuple(tuple(str(cell) for cell in row) for row in rows)
    key = (terminal_width, columns, content_key)
    if session.grid_layout_key == key and session.grid_layout_cache is not None:
        return session.grid_layout_cache

    cell_width = _table_grid_cell_width(columns, terminal_width)
    span = "─" * (cell_width + 2)
    wrapped_rows = tuple(
        tuple(tuple(_wrap_table_grid_cell(cell, cell_width)) for cell in row)
        for row in rows
    )
    row_heights = tuple(
        max((len(parts) for parts in row), default=1) for row in wrapped_rows
    )
    natural_height = max(1, len(rows) - 1) + sum(row_heights)
    layout = _TableGridLayout(
        columns=columns,
        cell_width=cell_width,
        top="┌" + "┬".join(span for _ in range(columns)) + "┐",
        middle="├" + "┼".join(span for _ in range(columns)) + "┤",
        bottom="└" + "┴".join(span for _ in range(columns)) + "┘",
        wrapped_rows=wrapped_rows,
        row_heights=row_heights,
        natural_body_height=natural_height,
    )
    session.grid_layout_key = key
    session.grid_layout_cache = layout
    return layout


def _table_grid_outer_border_fragments(session, edge):
    """Render one fixed outer border outside the scrolling table viewport."""
    layout = _table_grid_layout(session)
    return [("class:table.border", getattr(layout, edge))]


def _table_grid_body_height(session):
    """Return the natural rendered height of the scrollable table body."""
    layout = _table_grid_layout(session)
    viewport_height = min(layout.natural_body_height, 18)
    # Give HSplit permission to shrink on unusually short terminals, while the
    # preferred/max pair prevents spare blank rows on ordinary layouts.
    return D(min=1, preferred=viewport_height, max=viewport_height)


def _table_grid_fragments(session):
    """Render the scrollable table body from the shared computed grid layout."""
    layout = _table_grid_layout(session)
    rows = layout.wrapped_rows
    columns = layout.columns
    cell_width = layout.cell_width
    border = layout.middle

    fragments = []
    for row_number, wrapped_cells in enumerate(rows):
        row_height = layout.row_heights[row_number]
        selected_row = row_number == session.selected_row
        # Anchor downward navigation (and always the final row) at the row's
        # last rendered line so the bottom of a tall row can enter the viewport.
        cursor_visual_line = 0
        if selected_row and (
            session.scroll_anchor == "bottom" or row_number == len(rows) - 1
        ):
            cursor_visual_line = row_height - 1

        for visual_line in range(row_height):
            fragments.append(("class:table.border", "│"))
            for col in range(columns):
                cell_text = (
                    wrapped_cells[col][visual_line]
                    if visual_line < len(wrapped_cells[col])
                    else ""
                ).ljust(cell_width)
                selected = selected_row and col == session.selected_col
                if selected and visual_line == cursor_visual_line:
                    fragments.append(("[SetCursorPosition]", ""))
                if selected:
                    style_name = "class:table.cell.selected"
                elif row_number == 0:
                    style_name = "class:table.header"
                else:
                    style_name = "class:table.cell"
                fragments.append((style_name, f" {cell_text} "))
                fragments.append(("class:table.border", "│"))
            fragments.append(("", "\n"))

        if row_number != len(rows) - 1:
            fragments.append(("class:table.border", border + "\n"))

    return fragments

def _save_table_editor():
    session = current_table_editor
    if session is None:
        return
    _commit_table_editor_cell(session)
    _commit_table_editor_title(session)

    # Preserve the exact source representation of an untouched table.  The
    # editor works on a deep copy, and some UI operations may temporarily mark
    # that copy dirty even when the user ultimately returns it to the committed
    # content.  Only replace the committed object when its editable content
    # actually differs.  This keeps original spacing, alignment syntax, caption
    # placement, and hard wrapping byte-for-byte until a real table edit occurs.
    committed = state.tables.get(session.table_number)
    changed = (
        committed is None
        or _table_content_key(session.working) != _table_content_key(committed)
    )
    if changed:
        # One table save is one logical document edit. Build the object map and
        # refreshed folded label first, then commit both through one rollback-
        # protected transaction.
        session.working.dirty = True
        updated_tables = dict(state.tables)
        updated_tables[session.table_number] = session.working
        new_document = _document_with_refreshed_table_placeholder(
            session.table_number,
            session.working,
            text_area.buffer.document,
        )
        _commit_folded_object_transaction(
            text_area.buffer,
            new_document,
            tables=updated_tables,
        )

    close_dialog()
    get_app().invalidate()


def open_table_editor(table_number):
    global current_table_editor

    table = state.tables.get(table_number)
    if table is None:
        show_message("Table not found", f"Table {table_number} has no attached table data.")
        return
    if table.column_count > MAX_TABLE_EDITOR_COLUMNS:
        show_message(
            "Table too wide",
            f"The basic table editor currently supports up to {MAX_TABLE_EDITOR_COLUMNS} columns. "
            "This table will remain folded and unchanged.",
        )
        return

    try:
        terminal_width = get_app().output.get_size().columns
    except Exception:
        terminal_width = 100
    minimum_width = _minimum_table_editor_terminal_width(table.column_count)
    if terminal_width < minimum_width:
        show_message(
            "Terminal too narrow",
            f"This {table.column_count}-column table needs a terminal at least "
            f"{minimum_width} columns wide to show every column safely. "
            "Widen the terminal and reopen the table editor.",
        )
        return

    session = TableEditorSession(
        table_number=table_number,
        working=copy.deepcopy(table),
    )
    current_table_editor = session

    table_nav_kb = KeyBindings()

    @table_nav_kb.add("left")
    def _nav_left(event):
        _move_table_editor_col(-1)

    @table_nav_kb.add("right")
    def _nav_right(event):
        _move_table_editor_col(1)

    @table_nav_kb.add("up")
    def _nav_up(event):
        _move_table_editor_row(-1)

    @table_nav_kb.add("down")
    def _nav_down(event):
        _move_table_editor_row(1)

    @table_nav_kb.add("enter")
    def _nav_edit(event):
        _begin_table_cell_edit()

    @table_nav_kb.add("tab")
    def _nav_next(event):
        _move_table_editor_cell(1)

    @table_nav_kb.add("s-tab")
    def _nav_previous(event):
        if session.selected_row == 0 and session.selected_col == 0:
            _focus_table_title(session)
        else:
            _move_table_editor_cell(-1)

    @table_nav_kb.add("r")
    def _nav_row_commands(event):
        _show_table_row_menu()

    @table_nav_kb.add("c")
    def _nav_column_commands(event):
        _show_table_column_menu()

    @table_nav_kb.add("c-s")
    def _nav_save(event):
        _save_table_editor()

    @table_nav_kb.add("escape")
    def _nav_cancel(event):
        close_dialog()

    grid_control = FormattedTextControl(
        text=lambda: _table_grid_fragments(session),
        focusable=True,
        key_bindings=table_nav_kb,
        show_cursor=False,
    )
    grid_window = Window(
        content=grid_control,
        height=lambda: _table_grid_body_height(session),
        dont_extend_height=True,
    )
    grid_top_border = Window(
        content=FormattedTextControl(
            text=lambda: _table_grid_outer_border_fragments(session, "top")
        ),
        height=1,
        dont_extend_height=True,
    )
    grid_bottom_border = Window(
        content=FormattedTextControl(
            text=lambda: _table_grid_outer_border_fragments(session, "bottom")
        ),
        height=1,
        dont_extend_height=True,
    )
    # Keep the table grid itself centered within the table editor. The title,
    # hints, and command buttons retain the dialog's normal full-width layout.
    # Constrain the grid stack to its actual rendered width, then let equal
    # flexible windows on either side absorb the remaining dialog space.
    grid_stack = Box(
        body=HSplit([grid_top_border, grid_window, grid_bottom_border]),
        width=lambda: get_cwidth(_table_grid_layout(session).top),
        padding=0,
    )
    centered_grid = VSplit(
        [
            Window(),
            grid_stack,
            Window(),
        ]
    )
    cell_label = Label(text=_table_cell_label(session))
    mode_label = Label(text=_table_mode_hint(session))
    title_editor = SingleLineInput(
        text=session.working.title,
        style="class:input-field",
    )
    cell_editor = TextArea(
        text=session.working.headers[0],
        multiline=False,
        wrap_lines=True,
        height=D(preferred=3),
        style="class:table.cell-editor",
    )
    cell_editor.buffer.__class__ = SingleLineBuffer
    title_editor.buffer.on_text_changed += _working_state_changed
    cell_editor.buffer.on_text_changed += _working_state_changed

    # Cell editing is intentionally separate from table navigation. Arrow keys
    # retain normal caret behavior here. Enter commits the cell and hands
    # focus back to the grid; Escape discards only the uncommitted cell edit.
    table_cell_kb = KeyBindings()

    @table_cell_kb.add("enter")
    def _finish_cell_edit(event):
        _finish_table_cell_edit()

    @table_cell_kb.add("escape")
    def _cancel_cell_edit(event):
        _cancel_table_cell_edit()

    @table_cell_kb.add("c-s")
    def _save_from_cell(event):
        _finish_table_cell_edit()
        _save_table_editor()

    @table_cell_kb.add("c-x", eager=True)
    def _cut_from_cell(event):
        _dialog_buffer_cut(event.current_buffer)

    @table_cell_kb.add("c-c")
    def _copy_from_cell(event):
        _dialog_buffer_copy(event.current_buffer)

    @table_cell_kb.add("c-v")
    def _paste_into_cell(event):
        _dialog_buffer_paste(event.current_buffer)

    cell_editor.control.key_bindings = table_cell_kb

    table_title_kb = KeyBindings()

    @table_title_kb.add("enter")
    @table_title_kb.add("tab")
    def _finish_title_edit(event):
        _commit_table_editor_title(session)
        _focus_table_navigation(session)

    @table_title_kb.add("c-s")
    def _save_from_title(event):
        _commit_table_editor_title(session)
        _save_table_editor()

    @table_title_kb.add("c-x", eager=True)
    def _cut_from_title(event):
        _dialog_buffer_cut(event.current_buffer)

    @table_title_kb.add("c-c")
    def _copy_from_title(event):
        _dialog_buffer_copy(event.current_buffer)

    @table_title_kb.add("c-v")
    def _paste_into_title(event):
        _dialog_buffer_paste(event.current_buffer)

    title_editor.control.key_bindings = table_title_kb

    session.grid_control = grid_control
    session.grid_window = grid_window
    session.title_editor = title_editor
    session.cell_label = cell_label
    session.mode_label = mode_label
    session.cell_editor = cell_editor

    dialog = Dialog(
        title=f"Table {table_number}",
        body=HSplit(
            [
                Label(text="Title (optional; Shift+Tab from first cell):"),
                title_editor,
                Window(height=1, char="─", style="class:divider"),
                centered_grid,
                Window(height=1, char="─", style="class:divider"),
                cell_label,
                ConditionalContainer(
                    content=cell_editor,
                    filter=Condition(lambda: session.editing),
                ),
                mode_label,
            ]
        ),
        buttons=[
            Button(text="Row...", handler=_show_table_row_menu),
            Button(text="Column...", handler=_show_table_column_menu),
            Button(text="Save", handler=_save_table_editor),
            Button(text="Cancel", handler=close_dialog),
        ],
        width=D(preferred=110),
    )
    session.dialog_float = show_dialog(dialog, focus=grid_window)


def do_edit_table_at_cursor():
    table_number = _table_number_at_cursor()
    if table_number is None:
        show_message("No table", "Place the cursor on a [[Table N]] or [[Table N: Title]] reference first.")
        return
    open_table_editor(table_number)


def do_insert_table():
    if _folded_placeholder_locked():
        show_message(
            "Folded object",
            "Move the cursor off the folded table or footnote before inserting another table.",
        )
        return
    title_field = SingleLineInput(text="")
    columns_field = SingleLineInput(text="3")
    rows_field = SingleLineInput(text="2")

    def insert_handler():
        try:
            columns = int(columns_field.text.strip())
            rows = int(rows_field.text.strip())
        except ValueError:
            show_message("Invalid table size", "Columns and data rows must be whole numbers.")
            return

        if not 2 <= columns <= MAX_TABLE_EDITOR_COLUMNS:
            show_message(
                "Invalid table size",
                f"Choose between 2 and {MAX_TABLE_EDITOR_COLUMNS} columns for the basic table editor.",
            )
            return
        if not 1 <= rows <= MAX_TABLE_INSERT_ROWS:
            show_message(
                "Invalid table size",
                f"Choose between 1 and {MAX_TABLE_INSERT_ROWS} data rows.",
            )
            return

        # Number tables by document order. Existing tables at or after the
        # insertion point shift upward by one.
        current_row = text_area.buffer.document.cursor_position_row
        insert_number = 1
        for line in text_area.buffer.document.lines[:current_row + 1]:
            if TABLE_PLACEHOLDER_RE.match(line):
                insert_number += 1

        title = " ".join(title_field.text.splitlines()).strip()
        close_dialog()

        # Renumbering, the new object, and its folded placeholder form one
        # logical document edit. Build all three before committing any of them.
        table = _new_table_data(columns, rows, title=title)
        if not _commit_new_table_at_cursor(insert_number, table):
            return
        open_table_editor(insert_number)

    dialog = Dialog(
        title="Insert Table",
        body=HSplit(
            [
                Label(text="Title (optional):"),
                title_field,
                Label(text="Columns (2–6):"),
                columns_field,
                Label(text=f"Data rows (1–{MAX_TABLE_INSERT_ROWS}):"),
                rows_field,
            ]
        ),
        buttons=[
            Button(text="Insert", handler=insert_handler),
            Button(text="Cancel", handler=close_dialog),
        ],
        width=D(preferred=50),
    )
    show_dialog(dialog, focus=title_field)


# ---------------------------------------------------------------------------
# Prose footnote editor
# ---------------------------------------------------------------------------

def _footnote_source_span_at_cursor(document=None, direction=0):
    """Return the inline-footnote source span touching the cursor.

    Adjacent compact references share a source boundary: in ``[^a][^b]`` the
    end of the first reference is also the start of the second.  Directional
    operations must resolve that position according to the user's intent:
    rightward movement/Delete/Tab prefer the reference beginning there, while
    leftward movement/Backspace prefer the reference ending there.  A zero
    direction retains the ordinary containing-span behavior and, at a shared
    edge, prefers the following reference so object commands never enter its
    hidden source.
    """
    doc = document or text_area.buffer.document
    col = doc.cursor_position_col
    spans = _footnote_references_on_row(doc.text, doc.cursor_position_row)

    # A strict interior belongs unambiguously to one compact object.
    for start, end, identifier in spans:
        if start < col < end:
            return start, end, identifier

    starts = [span for span in spans if span[0] == col]
    ends = [span for span in spans if span[1] == col]
    if direction < 0:
        if ends:
            return ends[-1]
        if starts:
            return starts[0]
    else:
        # Rightward and neutral object commands prefer the object that starts
        # at a shared boundary.  At a non-shared closing edge, retain the
        # preceding object so Tab/menu editing still works at its visible end.
        if starts:
            return starts[0]
        if ends:
            return ends[-1]
    return None


def _footnote_identifier_at_cursor():
    """Return the folded prose footnote under the cursor, if any."""
    doc = text_area.buffer.document
    placeholder = FOOTNOTE_PLACEHOLDER_RE.match(doc.current_line)
    if placeholder:
        return placeholder.group(1)

    span = _footnote_source_span_at_cursor(doc, direction=1)
    return span[2] if span is not None else None


def _next_footnote_identifier(source_text=None):
    """Return a stable generated identifier that does not renumber older notes."""
    highest = 0
    pattern = re.compile(r"^fn-(\d+)$")
    identifiers = set(state.footnotes)
    if source_text is None:
        source_text = text_area.text
    for _start, _end, identifier, _row, _start_col, _end_col in _footnote_reference_spans(source_text):
        identifiers.add(identifier)
    for identifier in identifiers:
        match = pattern.match(identifier)
        if match:
            highest = max(highest, int(match.group(1)))
    candidate = highest + 1
    while f"fn-{candidate}" in identifiers:
        candidate += 1
    return f"fn-{candidate}"


def _document_with_appended_footnote_placeholder(
    identifier, document, cursor_position
):
    """Return a document with one folded definition appended to its source."""
    text = document.text
    placeholder = _footnote_placeholder(identifier)
    if not text:
        new_text = placeholder
    elif text.endswith("\n\n"):
        new_text = text + placeholder
    elif text.endswith("\n"):
        new_text = text + "\n" + placeholder
    else:
        new_text = text + "\n\n" + placeholder
    return Document(text=new_text, cursor_position=cursor_position)



def _save_footnote_editor():
    session = current_footnote_editor
    if session is None or session.editor is None:
        return

    normalized_text = _normalize_footnote_text(session.editor.text)
    invalid_paragraph = next(
        (
            paragraph
            for paragraph in normalized_text.split("\n\n")
            if not _footnote_fragment_is_simple(paragraph)
        ),
        None,
    )
    if invalid_paragraph is not None:
        show_message(
            "Footnote contains structural Markdown",
            "The folded footnote editor supports prose paragraphs only. "
            "A paragraph begins with Markdown structure such as a heading, list, "
            "blockquote, code block, reference definition, thematic break, or table.\n\n"
            "Remove that structure before saving. Structurally complex footnotes "
            "remain ordinary Markdown source when imported.",
        )
        return

    session.working.text = normalized_text

    # As with tables, an unchanged folded footnote must keep its original source
    # lines.  Merely opening the note editor and pressing Save should never
    # collapse an existing hard-wrapped definition or otherwise canonicalize it.
    committed = state.footnotes.get(session.identifier)
    changed = (
        committed is None
        or _footnote_content_key(session.working) != _footnote_content_key(committed)
    )
    if changed:
        # Footnote text is document content even though its folded placeholder
        # does not change. Commit the object-only edit through the same rollback
        # boundary as mixed document/object operations so recovery bookkeeping
        # cannot leave a partially installed note.
        session.working.dirty = True
        updated_footnotes = dict(state.footnotes)
        updated_footnotes[session.identifier] = session.working
        _commit_folded_object_transaction(
            text_area.buffer,
            text_area.buffer.document,
            footnotes=updated_footnotes,
        )

    close_dialog()
    get_app().invalidate()


def open_footnote_editor(identifier):
    """Open the dedicated multiline editor for one folded prose footnote."""
    global current_footnote_editor

    note = state.footnotes.get(identifier)
    if note is None:
        show_message(
            "Footnote source",
            "This reference does not point to a folded prose footnote. "
            "Structurally complex or unresolved footnotes remain ordinary Markdown source.",
        )
        return

    session = FootnoteEditorSession(identifier=identifier, working=copy.deepcopy(note))
    current_footnote_editor = session
    editor = TextArea(
        text=session.working.text,
        multiline=True,
        wrap_lines=True,
        scrollbar=True,
        height=D(preferred=10, max=18),
        style="class:footnote.editor",
    )
    editor.buffer.on_text_changed += _working_state_changed
    session.editor = editor

    note_kb = KeyBindings()

    @note_kb.add("enter")
    def _newline_note(event):
        event.current_buffer.insert_text("\n")

    @note_kb.add("c-s")
    def _save_note(event):
        _save_footnote_editor()

    @note_kb.add("c-x", eager=True)
    def _cut_from_note(event):
        _dialog_buffer_cut(event.current_buffer)

    @note_kb.add("c-c")
    def _copy_from_note(event):
        _dialog_buffer_copy(event.current_buffer)

    @note_kb.add("c-v")
    def _paste_into_note(event):
        _dialog_buffer_paste(event.current_buffer)

    @note_kb.add("escape")
    def _cancel_note(event):
        close_dialog()

    editor.control.key_bindings = note_kb

    number = _footnote_number_map(text_area.text).get(identifier)
    label = f"Footnote {number}" if number is not None else "Footnote"
    dialog = Dialog(
        title=label,
        body=HSplit(
            [
                Label(text=f"Source ID: {identifier}"),
                editor,
                Label(text="Enter inserts line break · blank line starts paragraph"),
                Label(text="Ctrl+S saves · Ctrl+X/C/V cut/copy/paste · Esc cancels"),
            ]
        ),
        buttons=[
            Button(text="Save", handler=_save_footnote_editor),
            Button(text="Cancel", handler=close_dialog),
        ],
        width=D(preferred=78),
    )
    session.dialog_float = show_dialog(dialog, focus=editor)


def do_edit_footnote_at_cursor():
    identifier = _footnote_identifier_at_cursor()
    if identifier is None:
        show_message("No footnote", "Place the cursor on a footnote reference or folded footnote first.")
        return
    open_footnote_editor(identifier)


def _commit_new_footnote_at_cursor():
    """Insert a reference, definition object, and placeholder transactionally."""
    buf = text_area.buffer
    base_document = buf.document
    if base_document.selection is not None:
        base_document, _clipboard_data = base_document.cut_selection()

    identifier = _next_footnote_identifier(base_document.text)
    reference = f"[^{identifier}]"
    position = base_document.cursor_position
    reference_document = Document(
        base_document.text[:position]
        + reference
        + base_document.text[position:],
        cursor_position=position + len(reference),
    )
    final_document = _document_with_appended_footnote_placeholder(
        identifier,
        reference_document,
        reference_document.cursor_position,
    )

    updated_footnotes = dict(state.footnotes)
    updated_footnotes[identifier] = FootnoteData(
        identifier=identifier,
        text="",
        original_lines=None,
        dirty=True,
    )
    _commit_folded_object_transaction(
        buf,
        final_document,
        footnotes=updated_footnotes,
        selection=None,
    )
    return identifier


def do_insert_footnote():
    """Insert a stable reference and append its folded prose definition object."""
    if _folded_placeholder_locked():
        show_message(
            "Folded object",
            "Move the cursor off the folded table or footnote before inserting a footnote.",
        )
        return
    buf = text_area.buffer
    if _selection_intersects_folded_object(buf):
        _folded_edit_warning()
        return

    identifier = _commit_new_footnote_at_cursor()
    open_footnote_editor(identifier)


def _delete_footnote_object(identifier):
    """Delete one folded footnote definition and all of its references."""
    if identifier not in state.footnotes:
        return False

    buf = text_area.buffer
    old_text = buf.text
    old_cursor = buf.cursor_position
    ranges = [
        (start, end)
        for start, end, ref_id, _row, _start_col, _end_col
        in _footnote_reference_spans(old_text)
        if ref_id == identifier
    ]

    # Remove references first, right-to-left, while maintaining an approximate
    # prose cursor position. The folded definition is then removed as a block.
    new_text = old_text
    new_cursor = old_cursor
    for start, end in sorted(ranges, reverse=True):
        if start < new_cursor:
            new_cursor -= min(end, new_cursor) - start
        new_text = new_text[:start] + new_text[end:]

    doc = Document(new_text, cursor_position=max(0, min(len(new_text), new_cursor)))
    target_row = None
    for row, line in enumerate(doc.lines):
        match = FOOTNOTE_PLACEHOLDER_RE.match(line)
        if match and match.group(1) == identifier:
            target_row = row
            break
    if target_row is None:
        return False

    updated = dict(state.footnotes)
    del updated[identifier]

    lines, cursor_row = _remove_folded_object_line(doc.lines, target_row)
    result = "\n".join(lines)
    tmp = Document(result)
    # If the original caret was on the definition, use its replacement row;
    # otherwise retain the cursor after reference removal as closely as possible.
    original_row = buf.document.cursor_position_row
    if original_row == target_row:
        final_cursor = tmp.translate_row_col_to_index(
            min(cursor_row, tmp.line_count - 1), 0
        )
    else:
        final_cursor = max(0, min(len(result), new_cursor))
    _commit_folded_object_transaction(
        buf,
        Document(result, final_cursor),
        footnotes=updated,
    )
    return True


def do_delete_footnote_at_cursor():
    identifier = _footnote_identifier_at_cursor()
    if identifier is None or identifier not in state.footnotes:
        show_message(
            "No footnote",
            "Place the cursor on a folded footnote or one of its references first.",
        )
        return
    number = _footnote_number_map(text_area.text).get(identifier)
    label = f"Footnote {number}" if number is not None else f"Footnote {identifier!r}"
    confirm(
        "Delete footnote",
        f"Delete {label}, including all of its inline references? This can be undone with Ctrl+Z.",
        lambda: _delete_footnote_object(identifier),
    )


async def _working_state_iteration():
    """Run one recovery maintenance/checkpoint iteration."""
    # Cleanup failures are normally rare and often transient (for example,
    # permissions changed while Carriage was running). Retry at a low rate
    # without making the normal 250 ms checkpoint poll perform filesystem work
    # on every iteration.
    now = time.monotonic()
    if (
        state.recovery_cleanup_failures
        and now >= state.recovery_cleanup_retry_at
    ):
        state.recovery_cleanup_retry_at = now + 5.0
        _retry_failed_recovery_cleanup()

    # A failed checkpoint/cleanup is visible in the status bar immediately.
    # The modal warning waits until no other dialog is open so it never stacks
    # on top of an unrelated user decision.
    if (
        state.recovery_error
        and not state.recovery_error_reported
        and current_float is None
    ):
        state.recovery_error_reported = True
        detail = state.recovery_error_message or "Unknown recovery error."
        if state.recovery_error_kind == "cleanup":
            show_message(
                "Recovery cleanup error",
                "Carriage could not remove or safely retire an obsolete "
                "working-state journal. Your Markdown file is unaffected, "
                "but Carriage will block destructive document transitions "
                f"until the journal can be made harmless.\n\n{detail}",
            )
        else:
            show_message(
                "Recovery unavailable",
                "Carriage could not update the protected working-state journal. "
                "Your Markdown file has not been changed; use Save to commit work "
                f"manually.\n\n{detail}",
            )

    # Every main-buffer/object-draft mutation advances the revision. If the
    # current revision has already been reconciled with disk/journal, there is
    # nothing to materialize or compare.
    if state.working_state_revision <= state.working_state_persisted_revision:
        return

    if not _has_recoverable_changes():
        _clear_recovery_file()
        _reset_working_state_tracking()
        return

    now = time.monotonic()
    if state.working_state_first_dirty_at is None:
        state.working_state_first_dirty_at = now
    if state.working_state_last_change_at is None:
        state.working_state_last_change_at = now

    idle_due = (
        now - state.working_state_last_change_at >= WORKING_STATE_IDLE_SECONDS
    )
    max_due = (
        now - state.working_state_first_dirty_at
        >= WORKING_STATE_MAX_LATENCY_SECONDS
    )
    if not (idle_due or max_due):
        return

    # Payload capture is intentionally inside the outer loop's exception
    # boundary as serialization/state errors can occur before the worker call.
    recovery_path, epoch, payload, revision = _recovery_snapshot_data()
    try:
        committed = await asyncio.to_thread(
            _write_recovery_payload_atomic,
            recovery_path,
            epoch,
            payload,
            revision,
        )
    except (OSError, UnicodeError, TypeError, ValueError) as e:
        _record_recovery_failure(e)
        return

    if committed:
        _record_recovery_success(revision)
        get_app().invalidate()


async def _working_state_loop():
    """Persist unsaved working state without allowing one failure to kill it."""
    while True:
        await asyncio.sleep(WORKING_STATE_POLL_SECONDS)
        try:
            await _working_state_iteration()
        except asyncio.CancelledError:
            raise
        except Exception as e:
            _record_recovery_failure(
                RuntimeError(f"Unexpected recovery checkpoint error: {e}")
            )



# ---------------------------------------------------------------------------
# Pandoc export
# ---------------------------------------------------------------------------

def _resolve_executable(executable):
    """Resolve a configured executable name/path, or return None."""
    candidate = os.path.expanduser(os.path.expandvars(str(executable).strip()))
    if not candidate:
        return None
    if os.path.sep in candidate:
        return candidate if os.path.isfile(candidate) and os.access(candidate, os.X_OK) else None
    return shutil.which(candidate)


def _configured_pandoc():
    return _resolve_executable(PANDOC_EXECUTABLE)


def _default_export_path(ext):
    base = os.path.splitext(state.path)[0] if state.path else "untitled"
    return base + "." + ext


def _default_wrapped_markdown_path():
    base = os.path.splitext(state.path)[0] if state.path else "untitled"
    return base + "-wrapped.md"


def _perform_text_export(out_path, content, expected_snapshot):
    """Durably write a text export without touching the working document."""
    target_path = _canonical_path(out_path)

    try:
        if _disk_snapshot(target_path) != expected_snapshot:
            show_message(
                "Export destination changed",
                "The output file changed before export began. Nothing was overwritten. "
                "Choose the export path again to review the current destination.",
            )
            return False

        if (
            expected_snapshot != _MISSING_DISK_SNAPSHOT
            and _path_is_read_only(target_path)
        ):
            show_message(
                "Read-only export destination",
                "The export destination is marked read-only. Nothing was overwritten. "
                "Choose a different filename.",
            )
            return False

        def write_staged(temp_path):
            with open(temp_path, "w", encoding="utf-8", newline="") as f:
                f.write(content)
                f.flush()

        def validate_before_replace():
            if _disk_snapshot(target_path) != expected_snapshot:
                return (
                    "changed",
                    "The output file changed while Carriage was exporting. The newer file "
                    "was left untouched; the staged export was discarded.",
                )
            if (
                expected_snapshot != _MISSING_DISK_SNAPSHOT
                and _path_is_read_only(target_path)
            ):
                return (
                    "read_only",
                    "The export destination became read-only while Carriage was exporting. "
                    "Nothing was overwritten.",
                )
            return None

        try:
            _durable_atomic_replace(
                target_path,
                write_staged,
                temp_suffix=".tmp",
                new_file_mode=_new_file_mode_from_umask(),
                preserve_existing_metadata=True,
                reject_hardlinks=True,
                validate_before_replace=validate_before_replace,
            )
        except _AtomicReplaceCancelled as cancelled:
            kind, message = cancelled.result
            if kind == "changed":
                show_message("Export destination changed", message)
            else:
                show_message("Read-only export destination", message)
            return False
        except _AtomicReplaceHardLinkError:
            show_message(
                "Linked export destination",
                "The export destination has multiple hard links. Atomic replacement would "
                "break that link relationship, so nothing was overwritten. Choose a "
                "different export filename.",
            )
            return False
        except _AtomicReplaceDurabilityError as e:
            show_message(
                "Export durability warning",
                "The exported file is visible on disk, but Carriage could not confirm "
                "that the directory update is durable. A sudden system crash could lose "
                f"the rename.\n\nDirectory flush error: {e.original_error}",
            )
            return False

        show_message("Export complete", f"Wrote {out_path}")
        return True
    except (OSError, UnicodeError) as e:
        show_message("Export error", str(e))
        return False

def _request_text_export(out_path, content):
    """Validate and confirm a text export destination before writing it."""
    if state.path is not None and _same_document_path(out_path, state.path):
        show_message(
            "Unsafe export path",
            "The export destination is the Markdown file currently open in Carriage. "
            "Choose a different filename so the working document cannot be replaced.",
        )
        return

    try:
        destination_snapshot = _disk_snapshot(out_path)
        if (
            destination_snapshot != _MISSING_DISK_SNAPSHOT
            and _path_is_read_only(out_path)
        ):
            show_message(
                "Read-only export destination",
                "That file is marked read-only, so Carriage will not replace it. "
                "Choose a different export filename.",
            )
            return
    except OSError as e:
        show_message("Error checking export destination", str(e))
        return

    def perform():
        _perform_text_export(out_path, content, expected_snapshot=destination_snapshot)

    if destination_snapshot != _MISSING_DISK_SNAPSHOT:
        _confirm_replace(
            "Replace existing export?",
            f"A file already exists at:\n{out_path}\n\nReplace it with this export?",
            perform,
        )
    else:
        perform()


def do_export_hard_wrapped_markdown():
    """Write a separate hard-wrapped Markdown copy at the configured width."""
    def do_export(raw_path):
        out_path = os.path.expanduser(raw_path.strip())
        if not out_path:
            return
        try:
            source_text = _materialize_objects(text_area.text)
        except ValueError as e:
            show_message("Document object error", str(e))
            return
        wrapped_text = _hard_wrap_export_text(source_text, width=WRAP_COLUMN)
        _request_text_export(out_path, wrapped_text)

    show_input_dialog(
        "Export Hard-Wrapped Markdown",
        "Output path:",
        _default_wrapped_markdown_path(),
        do_export,
    )


def _split_windows_command_arguments(text):
    """Split a Windows command-line fragment using CRT-compatible quoting rules.

    ``shlex`` implements Unix-shell syntax, where a backslash escapes the next
    character. That corrupts ordinary unquoted Windows paths such as
    ``C:\\Users\\Name``. Windows command lines instead treat backslashes
    literally except when they immediately precede a double quote. This parser
    mirrors the quoting convention Python uses when it converts an argv list to
    a Windows command line for ``subprocess``.
    """
    arguments = []
    source = str(text)
    length = len(source)
    index = 0

    while True:
        while index < length and source[index] in " \t":
            index += 1
        if index >= length:
            break

        argument = []
        in_quotes = False
        while index < length:
            char = source[index]
            if char in " \t" and not in_quotes:
                break

            if char == "\\":
                slash_start = index
                while index < length and source[index] == "\\":
                    index += 1
                slash_count = index - slash_start

                if index < length and source[index] == '"':
                    argument.extend("\\" * (slash_count // 2))
                    if slash_count % 2:
                        argument.append('"')
                        index += 1
                    else:
                        # Inside a quoted argument, a doubled quote represents
                        # one literal quote rather than ending the quoted span.
                        if (
                            in_quotes
                            and index + 1 < length
                            and source[index + 1] == '"'
                        ):
                            argument.append('"')
                            index += 2
                        else:
                            in_quotes = not in_quotes
                            index += 1
                else:
                    argument.extend("\\" * slash_count)
                continue

            if char == '"':
                if (
                    in_quotes
                    and index + 1 < length
                    and source[index + 1] == '"'
                ):
                    argument.append('"')
                    index += 2
                else:
                    in_quotes = not in_quotes
                    index += 1
                continue

            argument.append(char)
            index += 1

        if in_quotes:
            raise ValueError("No closing quotation")

        arguments.append("".join(argument))
        while index < length and source[index] in " \t":
            index += 1

    return arguments


def _split_custom_pandoc_arguments(text):
    """Split Custom Export arguments according to the host platform."""
    if os.name == "nt":
        return _split_windows_command_arguments(text)
    return shlex.split(text)


def _pandoc_args_define_output(args):
    """Return True if custom arguments try to choose their own output path."""
    for arg in args:
        if arg == "--output" or arg.startswith("--output="):
            return True
        if arg == "-o" or (arg.startswith("-o") and len(arg) > 2):
            return True
    return False


def _new_file_mode_from_umask():
    """Return the normal 0666-based creation mode on the UI thread.

    ``os.umask`` is process-global, so Pandoc's worker thread must never toggle
    it while the editor may be saving or doing other filesystem work. Capture
    the intended mode before the background task starts and pass it in instead.
    """
    current_umask = os.umask(0)
    os.umask(current_umask)
    return 0o666 & ~current_umask


def _perform_pandoc_export_worker(
    out_path, source_text, extra_args, expected_snapshot, new_file_mode
):
    """Run one Pandoc export without touching prompt_toolkit UI state.

    This function is deliberately safe to execute in a worker thread. It works
    only from immutable call arguments plus filesystem state and returns a
    ``(status, message)`` tuple for the UI coroutine to present afterward.
    ``source_text`` is the materialized document snapshot captured before the
    export was requested, so edits made while Pandoc runs cannot change the
    bytes being exported.
    """
    target_path = _canonical_path(out_path)
    basename = os.path.basename(target_path)
    stem, extension = os.path.splitext(basename)

    try:
        # Confirmation is tied to a specific destination version. If it
        # changed while the user was deciding, do not overwrite the new one.
        if _disk_snapshot(target_path) != expected_snapshot:
            return (
                "destination_changed_before",
                "The output file changed before export began. Nothing was overwritten. "
                "Choose the export path again to review the current destination.",
            )

        if (
            expected_snapshot != _MISSING_DISK_SNAPSHOT
            and _path_is_read_only(target_path)
        ):
            return (
                "read_only_before",
                "The export destination is marked read-only. Nothing was overwritten. "
                "Choose a different filename.",
            )

        pandoc = _configured_pandoc()
        if pandoc is None:
            return (
                "pandoc_error",
                f"Configured Pandoc executable not found: {PANDOC_EXECUTABLE}",
            )

        def write_staged(temp_path):
            # Keep the real destination out of Pandoc's hands entirely. The
            # staging filename retains the requested extension so Pandoc can
            # infer PDF/DOCX/ODT/HTML/plain output exactly as before.
            cmd = [pandoc, "-f", "markdown"] + list(extra_args or []) + ["-o", temp_path]
            subprocess.run(
                cmd,
                input=source_text,
                check=True,
                capture_output=True,
                text=True,
            )

        def validate_before_replace():
            # Recheck immediately before replacement. This cannot eliminate the
            # tiny OS-level interval between check and rename, but it prevents
            # the practical race where a destination changes during a long export.
            if _disk_snapshot(target_path) != expected_snapshot:
                return (
                    "destination_changed_during",
                    "The output file changed while Pandoc was running. The newer file was "
                    "left untouched; the staged export was discarded.",
                )
            if (
                expected_snapshot != _MISSING_DISK_SNAPSHOT
                and _path_is_read_only(target_path)
            ):
                return (
                    "read_only_during",
                    "The export destination became read-only while Pandoc was running. "
                    "Nothing was overwritten.",
                )
            return None

        try:
            _durable_atomic_replace(
                target_path,
                write_staged,
                temp_prefix=f".{stem or basename}.",
                temp_suffix=extension or ".tmp",
                new_file_mode=new_file_mode,
                preserve_existing_metadata=True,
                reject_hardlinks=True,
                validate_before_replace=validate_before_replace,
            )
        except subprocess.CalledProcessError as e:
            return ("pandoc_error", (e.stderr or str(e)).strip())
        except _AtomicReplaceCancelled as cancelled:
            return cancelled.result
        except _AtomicReplaceHardLinkError:
            return (
                "linked_destination",
                "The export destination has multiple hard links. Atomic replacement would "
                "break that link relationship, so nothing was overwritten. Choose a "
                "different output filename.",
            )
        except _AtomicReplaceDurabilityError as e:
            return (
                "durability_error",
                "The exported file is visible on disk, but Carriage could not confirm "
                "that the directory update is durable. A sudden system crash could lose "
                f"the rename.\n\nDirectory flush error: {e.original_error}",
            )

        return ("ok", f"Wrote {out_path}")
    except (OSError, UnicodeError) as e:
        return ("pandoc_error", str(e))


async def _perform_pandoc_export_async(
    out_path, source_text, extra_args, expected_snapshot, new_file_mode
):
    """Run the blocking Pandoc/filesystem work without blocking the UI loop."""
    return await asyncio.to_thread(
        _perform_pandoc_export_worker,
        out_path,
        source_text,
        tuple(extra_args or ()),
        expected_snapshot,
        new_file_mode,
    )


def _show_pandoc_export_result(status, message):
    """Present one worker result on the prompt_toolkit/UI thread."""
    if status == "ok":
        show_message("Export complete", message)
    elif status in {"destination_changed_before", "destination_changed_during"}:
        show_message("Export destination changed", message)
    elif status in {"read_only_before", "read_only_during"}:
        show_message("Read-only export destination", message)
    elif status == "linked_destination":
        show_message("Linked export destination", message)
    elif status == "durability_error":
        show_message("Export durability warning", message)
    else:
        show_message("Pandoc error", message)


def _start_pandoc_export(
    out_path, source_text, extra_args, expected_snapshot, new_file_mode
):
    """Schedule one already-validated immutable Pandoc export snapshot."""
    if state.pandoc_export_running:
        show_message(
            "Export already running",
            "A Pandoc export is already in progress. Wait for it to finish before "
            "starting another Pandoc export.",
        )
        return False

    # Claim the export slot synchronously before scheduling the coroutine. This
    # closes the same-loop race where two menu actions could otherwise both
    # schedule a task before either task had a chance to set the flag.
    state.pandoc_export_running = True
    get_app().invalidate()

    async def run_export():
        try:
            status, message = await _perform_pandoc_export_async(
                out_path,
                source_text,
                extra_args,
                expected_snapshot,
                new_file_mode,
            )
        except Exception as e:
            status, message = "pandoc_error", str(e)
        finally:
            state.pandoc_export_running = False
            try:
                get_app().invalidate()
            except Exception:
                pass

        _show_pandoc_export_result(status, message)

    get_app().create_background_task(run_export())
    return True


def _request_pandoc_export(out_path, source_text, extra_args=None):
    """Validate/confirm an export destination before Pandoc is run."""
    if state.pandoc_export_running:
        show_message(
            "Export already running",
            "A Pandoc export is already in progress. Wait for it to finish before "
            "starting another Pandoc export.",
        )
        return

    if state.path is not None and _same_document_path(out_path, state.path):
        show_message(
            "Unsafe export path",
            "The export destination is the Markdown file currently open in Carriage. "
            "Choose a different output filename so the source document cannot be replaced.",
        )
        return

    try:
        destination_snapshot = _disk_snapshot(out_path)
        if (
            destination_snapshot != _MISSING_DISK_SNAPSHOT
            and _path_is_read_only(out_path)
        ):
            show_message(
                "Read-only export destination",
                "That file is marked read-only, so Carriage will not replace it. "
                "Choose a different export filename.",
            )
            return
    except OSError as e:
        show_message("Error checking export destination", str(e))
        return

    new_file_mode = _new_file_mode_from_umask()

    def perform():
        _start_pandoc_export(
            out_path,
            source_text,
            extra_args or [],
            expected_snapshot=destination_snapshot,
            new_file_mode=new_file_mode,
        )

    if destination_snapshot != _MISSING_DISK_SNAPSHOT:
        _confirm_replace(
            "Replace existing export?",
            f"A file already exists at:\n{out_path}\n\nReplace it with this export?",
            perform,
        )
    else:
        perform()


def export_via_pandoc(fmt_label, ext, extra_args=None):
    if state.pandoc_export_running:
        show_message(
            "Export already running",
            "A Pandoc export is already in progress. Wait for it to finish before "
            "starting another Pandoc export.",
        )
        return
    if _configured_pandoc() is None:
        show_message(
            "Pandoc not found",
            f"Configured Pandoc executable not found: {PANDOC_EXECUTABLE}\n\n"
            f"Edit {_config_path()} to change the Pandoc executable.",
        )
        return

    def do_export(raw_path):
        out_path = os.path.expanduser(raw_path.strip())
        if not out_path:
            return
        try:
            source_text = _materialize_objects(text_area.text)
        except ValueError as e:
            show_message("Document object error", str(e))
            return
        _request_pandoc_export(out_path, source_text, extra_args or [])

    show_input_dialog(
        f"Export as {fmt_label}", "Output path:", _default_export_path(ext), do_export
    )


def do_custom_export():
    if state.pandoc_export_running:
        show_message(
            "Export already running",
            "A Pandoc export is already in progress. Wait for it to finish before "
            "starting another Pandoc export.",
        )
        return
    path_field = SingleLineInput(text=_default_export_path("out"))
    args_field = SingleLineInput(text="-t html --standalone")

    def ok_handler():
        out_path = os.path.expanduser(path_field.text.strip())
        try:
            extra = _split_custom_pandoc_arguments(args_field.text.strip())
        except ValueError as e:
            # Keep the export dialog underneath the error so the user can
            # dismiss the message and correct the malformed argument string.
            show_message("Invalid pandoc arguments", str(e))
            return

        if _pandoc_args_define_output(extra):
            show_message(
                "Invalid pandoc arguments",
                "Do not use -o or --output in Extra pandoc arguments. Use the "
                "Output path field above so Carriage can protect that destination.",
            )
            return

        close_dialog()
        if not out_path:
            return
        if _configured_pandoc() is None:
            show_message(
                "Pandoc not found",
                f"Configured Pandoc executable not found: {PANDOC_EXECUTABLE}\n\n"
                f"Edit {_config_path()} to change the Pandoc executable.",
            )
            return
        try:
            source_text = _materialize_objects(text_area.text)
        except ValueError as e:
            show_message("Document object error", str(e))
            return
        _request_pandoc_export(out_path, source_text, extra)

    dialog = Dialog(
        title="Custom pandoc export",
        body=HSplit(
            [
                Label(text="Output path:"),
                path_field,
                Label(text="Extra pandoc arguments:"),
                args_field,
            ]
        ),
        buttons=[
            Button(text="Export", handler=ok_handler),
            Button(text="Cancel", handler=close_dialog),
        ],
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=path_field)


# ---------------------------------------------------------------------------
# Spell check
# ---------------------------------------------------------------------------

def _spellcheck_argv(path):
    """Return the configured spell-check command with {file} substituted."""
    return [arg.replace("{file}", path) for arg in SPELLCHECK_COMMAND]


def do_run_spellcheck():
    if state.path is None:
        show_message(
            "Save first", "Save the file before running the spell checker."
        )
        return

    def proceed():
        do_save(on_saved=_launch_spellcheck)

    if state.is_modified(text_area.text):
        confirm(
            "Unsaved changes",
            "The spell checker works on the file on disk. Save your changes first?",
            proceed,
        )
    else:
        _launch_spellcheck()


async def _run_external_command_in_terminal(argv):
    """Run an argv command with terminal ownership and return its exit status."""
    async with in_terminal():
        process = await asyncio.create_subprocess_exec(*argv)
        try:
            return await process.wait()
        except asyncio.CancelledError:
            if process.returncode is None:
                try:
                    process.terminate()
                except ProcessLookupError:
                    pass
                try:
                    await process.wait()
                except Exception:
                    pass
            raise


def _spellcheck_failure_text(return_code):
    if return_code < 0:
        return f"The spell checker was terminated by signal {-return_code}."
    return f"The spell checker exited with status {return_code}."


def _reload_spellchecked_file(path, *, allow_large=False):
    """Reload a checker-edited file, confirming unexpected large growth."""
    try:
        content, disk_snapshot = _read_utf8_file_with_snapshot(
            path, allow_large=allow_large
        )
    except _LargeFileConfirmationRequired as e:
        confirm(
            "Large file",
            "The spell checker increased the file beyond Carriage's large-file "
            "warning threshold.\n\n" + _large_file_prompt_text(path, e.size_bytes),
            lambda: _reload_spellchecked_file(path, allow_large=True),
        )
        return False
    except (OSError, UnicodeError) as e:
        show_message("Error reloading file", str(e))
        return False

    if state.path is None or not _same_document_path(path, state.path):
        show_message(
            "Spell checker result not loaded",
            "The active document changed before the spell checker finished. "
            "The checked file was left on disk and the current editor document "
            "was not replaced.",
        )
        return False

    visible = _collapse_objects_from_source(content)
    text_area.buffer.reset(Document(text=visible))
    state.saved_text = content
    state.disk_snapshot = disk_snapshot
    cleanup_ok = _clear_recovery_file()
    _reset_working_state_tracking()
    if not cleanup_ok:
        show_message(
            "Recovery cleanup error",
            "The spell-checked file was reloaded successfully, but Carriage "
            "could not safely retire its obsolete recovery journal.\n\n"
            f"{state.recovery_error_message or 'Unknown recovery cleanup error.'}",
        )
    return True


def _launch_spellcheck():
    checked_path = state.path
    argv = _spellcheck_argv(checked_path)
    executable = _resolve_executable(argv[0])
    if executable is None:
        show_message(
            "Spell checker not found",
            f"Configured spell-check executable not found: {argv[0]}\n\n"
            f"Edit {_config_path()} to change spellcheck_command.",
        )
        return
    argv[0] = executable

    try:
        precheck_size = os.stat(checked_path).st_size
    except OSError as e:
        show_message("Spell checker error", str(e))
        return
    previously_large = precheck_size > LARGE_FILE_WARNING_BYTES

    async def run_and_reload():
        try:
            return_code = await _run_external_command_in_terminal(argv)
        except asyncio.CancelledError:
            raise
        except Exception as e:
            show_message("Spell checker error", str(e))
            return

        if return_code != 0:
            show_message("Spell checker error", _spellcheck_failure_text(return_code))
            return

        # A file that was already over the threshold has necessarily been
        # approved (or deliberately created/saved) in this editor session. A
        # checker that unexpectedly grows a formerly small file must ask again.
        _reload_spellchecked_file(
            checked_path, allow_large=previously_large
        )

    get_app().create_background_task(run_and_reload())


# ---------------------------------------------------------------------------
# Help
# ---------------------------------------------------------------------------


def _show_help_reference(title, text):
    """Show a word-wrapped, scrollable, read-only Help reference."""
    ok_button = Button(text="OK", handler=close_dialog)
    help_body = TextArea(
        text=text,
        read_only=True,
        wrap_lines=False,
        scrollbar=True,
        height=D(preferred=28),
        style="class:help-text",
        focus_on_click=True,
    )
    dialog = Dialog(
        title=title,
        body=help_body,
        buttons=[ok_button],
        width=D(preferred=76),
    )
    show_dialog(dialog, focus=help_body)

KEYBINDING_ROWS = [
    ("Ctrl+N", "New file"),
    ("Ctrl+O", "Open file"),
    ("Ctrl+S / F9", "Save"),
    ("Ctrl+Z", "Undo"),
    ("Ctrl+R", "Redo"),
    ("Ctrl+F", "Find / replace"),
    ("Ctrl+X", "Cut to clipboard"),
    ("Ctrl+C", "Copy to clipboard"),
    ("Ctrl+V", "Paste from clipboard"),
    ("Ctrl+Q", "Quit"),
    ("F1", "Carriage Help"),
    ("F2", "Toggle italic on selected text"),
    ("F3", "Toggle bold on selected text"),
    ("F4", "Insert table"),
    ("F5", "Insert footnote"),
    ("F6", "Toggle Extend Selection mode"),
    ("F7", "Spell check"),
    ("F8", "Renumber numbered list"),
    ("F10", "Open menu bar"),
    ("Ctrl+Space", "Open menu bar"),
    ("Home / End", "Start / end of displayed row"),
    ("Ctrl+Home", "Top of document"),
    ("Ctrl+End", "End of document"),
    ("Alt+G", "Go directly to a section"),
    ("Alt+Up", "Previous section; align heading at top"),
    ("Alt+Down", "Next section; align heading at top"),
    ("1-6", "Jump to File/Edit/Go/Export/Tools/Help"),
    ("Tab", "Indent; on a folded table or footnote, edit it"),
    ("Esc", "Close menu, dialog, or Find / Replace"),
]


def _format_keybinding_rows(rows, width=62, command_width=12):
    """Render a compact cheatsheet with one fixed description column."""
    rendered = []
    description_width = max(1, width - command_width - 2)
    for command, description in rows:
        chunks = textwrap.wrap(
            description,
            width=description_width,
            break_long_words=False,
            break_on_hyphens=False,
        ) or [""]
        rendered.append(f"{command:<{command_width}}  {chunks[0]}")
        continuation_prefix = " " * (command_width + 2)
        rendered.extend(continuation_prefix + chunk for chunk in chunks[1:])
    return "\n".join(rendered)


def _format_help_notes(width=62):
    """Build practical guidance that complements the shortcut list."""
    paragraphs = [
        (
            "Selection: F6 toggles Extend Selection mode. While active, Left/Right "
            "selects by character, Up/Down by displayed row, Ctrl+Left/Right by word, "
            "Home/End to the displayed-row boundary, and Ctrl+Home/End to the document "
            "boundary. Press F6 again to leave the mode while keeping the selection. "
            "The usual Shift combinations remain available when the terminal passes "
            "them through. Double-click selects a word and triple-click selects the "
            "current paragraph or list item. Structural Markdown shown in the hanging "
            "gutter is not a cursor destination."
        ),
        (
            "Navigation: Alt+G opens Go to Section with the current section selected. "
            "Headings are shown hierarchically by ATX level; type to filter the list, "
            "use Up/Down to choose a result, and press Enter to jump with that heading "
            "aligned at the top of the editor. Alt+Up and Alt+Down remain the faster "
            "commands for moving among nearby sections."
        ),
        (
            "Find / Replace: Ctrl+F opens the status-line search. Search is literal and "
            "begins at the cursor; a single-line selection pre-fills the query. Enter "
            "or Down moves to the next match, Up moves to the previous match, and Tab "
            "switches between Find and Replace. Alt+C toggles case sensitivity, Alt+W "
            "toggles whole-word matching, and Alt+A in Replace mode replaces all matches "
            "as one Undo step. Esc returns to the document. Search covers ordinary visible "
            "document text; folded table and footnote placeholder lines "
            "and their hidden contents are excluded from search. Structurally complex footnotes "
            "that remain ordinary Markdown are searched normally."
        ),
        (
            "Clipboard: Ctrl+X, Ctrl+C, and Ctrl+V use the desktop system clipboard "
            "for plain text when the platform provides an available backend. If the "
            "system clipboard is unavailable, Carriage automatically falls back to its "
            "internal clipboard and keeps Cut/Copy/Paste working within Carriage. Pasted "
            "CRLF or CR line endings are normalized to LF."
        ),
        (
            "Emphasis: Select text and press F2 for italic or F3 for bold. The attributes "
            "toggle independently, so both can produce bold italic. Carriage writes "
            "asterisks and leaves leading or trailing selection whitespace outside the "
            "markers. If a safe change cannot be identified, the source is left alone "
            "and the reason appears on the status line."
        ),
        (
            "Wrapping and conversion: Ordinary prose soft-wraps at the configured width "
            "without changing source line breaks. Edit > Convert for Carriage converts "
            "supported Setext headings to ATX, renumbers straightforward ordered lists, "
            "normalizes straightforward underscore emphasis to asterisks, joins "
            "supported hard-wrapped prose, and recognizes supported tables and footnotes. "
            "Ambiguous or line-sensitive Markdown is preserved. Export > Hard-Wrapped "
            "Markdown writes a separate wrapped copy."
        ),
        (
            "Hard breaks: Two trailing spaces create a Markdown hard line break. When "
            "enabled, Carriage displays that break as ↵. The marker is visual only."
        ),
        (
            "Renumber List: F8 or Edit > Renumber List changes only the supported numbered "
            "list containing the cursor. It preserves the first item's number and makes "
            "the following items consecutive."
        ),
        (
            "Saving and recovery: The Markdown file advances only through explicit Save "
            "or Save As. Carriage protects unsaved work separately in a private recovery "
            "journal, normally two seconds after editing becomes idle and at least every "
            "ten seconds during sustained editing. Saves use durable atomic replacement "
            "and detect external file changes. After an abnormal exit, Carriage offers "
            "to restore or discard recovered work. Recovery is not a substitute for "
            "backups or version control."
        ),
        (
            "Opening and naming: Carriage reads UTF-8 Markdown, normalizes line endings to "
            "LF, and asks before loading files larger than 8 MiB. Save As suggests a name "
            "from the first recognized ATX heading. It uses visible heading text, stops "
            "before a subtitle colon, removes Markdown formatting, and shortens a long "
            "title only at a useful word boundary."
        ),
        (
            "Tables: F4 or Tools > Insert Table creates a basic table with 2-6 columns and "
            f"1-{MAX_TABLE_INSERT_ROWS} data rows. Arrow keys navigate cells; Enter edits and commits a cell. "
            "Shift+Tab from the first cell focuses the optional title. R and C open row "
            "and column commands in navigation mode. Imported wider tables are preserved "
            "as Markdown but cannot be opened in the basic table editor."
        ),
        (
            "Footnotes: F5 or Tools > Insert Footnote creates a standard inline reference "
            "and folded prose definition. References display as [1], [2], and so on. Tab "
            "opens a multiline note editor; blank lines separate paragraphs. Adjacent "
            "references remain separate atomic objects. Footnotes containing structural "
            "blocks such as lists or code remain ordinary source."
        ),
        (
            "Spell check and export: Spell check works on a saved file and offers to save "
            "unsaved changes first. The file is reloaded only when the configured checker "
            "exits successfully. Pandoc exports run without blocking editing; only one can "
            "run at a time. Built-in targets are PDF, DOCX, ODT, and HTML, plus a custom "
            "Pandoc command. Hard-wrapped Markdown does not require Pandoc."
        ),
        (
            "Configuration: Settings are read at startup from "
            "$XDG_CONFIG_HOME/carriage/config.toml, or ~/.config/carriage/config.toml "
            "when XDG_CONFIG_HOME is unset. The file controls prose width, scrollbar, "
            "startup status bar, mouse support, hard-break marker, Pandoc executable, and "
            "spell-check command. Carriage has no Preferences dialog. Invalid entries are "
            "reported and ignored without discarding valid neighboring settings."
        ),
    ]
    return "\n\n".join(
        "\n".join(_wrap_dialog_paragraph(paragraph, width=width))
        for paragraph in paragraphs
    )


HELP_TEXT = (
    _format_keybinding_rows(KEYBINDING_ROWS)
    + "\n\n"
    + _format_help_notes()
)

ABOUT_PARAGRAPHS = [
    f"{APP_NAME} v{APP_VERSION}",
    (
        "Carriage is a prose-first Markdown editor for the terminal. It is "
        "designed to keep attention on sentences, paragraphs, and sections "
        "while leaving the document as ordinary, portable Markdown."
    ),
    (
        "Prose soft-wraps visually inside the configured writing width. "
        "Supported tables and prose footnotes become compact editing objects, "
        "while Save and export always materialize standard Markdown. Structural "
        "or ambiguous source is preserved rather than repaired speculatively."
    ),
    (
        "The Markdown file changes only through explicit Save or Save As. "
        "Unsaved work is protected separately by a private recovery journal, "
        "and saves use durable atomic replacement with external-change checks."
    ),
    (
        "The guiding principle is simple: help with writing where Carriage can "
        "do so confidently, and preserve the writer's text when it cannot."
    ),
]


def _wrap_about_text(width=62):
    """Word-wrap About prose explicitly; Label itself wraps by screen cell."""
    rendered = []
    for paragraph in ABOUT_PARAGRAPHS:
        rendered.append(
            textwrap.fill(
                paragraph,
                width=width,
                break_long_words=False,
                break_on_hyphens=False,
            )
        )
    return "\n\n".join(rendered)


ABOUT_TEXT = _wrap_about_text()


def _build_markdown_help(width=62):
    """Build Carriage's concise prose-oriented Markdown reference."""
    rule = "─" * width
    intro = (
        "This is a Markdown syntax reference, not a list of everything Carriage "
        "actively reformats. Carriage may normalize ordinary prose, simple flat "
        "lists, and simple single-level blockquotes. Code, YAML, raw HTML, complex "
        "containers, reference definitions, and ambiguous structures are preserved. "
        "Highlighting and folded-object labels are visual only."
    )
    sections = [
        (
            "Headings",
            [
                "    # H1    ## H2    ...    ###### H6",
                "ATX headings are Carriage's preferred form. Convert for Carriage can",
                "normalize supported Setext headings to ATX.",
            ],
        ),
        (
            "Emphasis",
            [
                "    *italic*",
                "    **bold**",
                "    ***bold italic***",
                "F2 toggles italic and F3 toggles bold on selected text.",
                "Carriage writes asterisks; conversion can normalize straightforward",
                "underscore emphasis.",
            ],
        ),
        (
            "Lists",
            [
                "    - unordered item",
                "    1. ordered item",
                "Carriage actively reformats only straightforward flat prose lists.",
            ],
        ),
        (
            "Blockquotes",
            [
                "    > quoted text",
                "Carriage actively reformats only simple single-level prose blockquotes.",
            ],
        ),
        (
            "Horizontal rules",
            [
                "    ---    ***    ___",
                "Use three or more matching -, *, or _ characters.",
            ],
        ),
        (
            "Links and images",
            [
                "    [link text](https://example.com)",
                "    ![alt text](image.png)",
            ],
        ),
        (
            "Code",
            [
                "    `inline code`",
                "Use matching triple backticks or tildes for a fenced code block.",
                "Carriage preserves code rather than reflowing it.",
            ],
        ),
        (
            "Hard line breaks",
            [
                "End a line with two spaces to force a Markdown line break.",
                "Carriage can display that break as ↵; the marker is visual only.",
            ],
        ),
        (
            "Footnotes",
            [
                "    Text with a note.[^id]",
                "    [^id]: Footnote text",
                "F5 or Tools > Insert Footnote creates a standard prose footnote.",
                "Single- and multi-paragraph prose definitions fold out of the prose view;",
                "references display sequentially as [1], [2], and so on. Blank lines in",
                "the note editor separate paragraphs. Structurally complex definitions",
                "remain ordinary source.",
            ],
        ),
        (
            "Tables",
            [
                "F4 or Tools > Insert Table creates a basic pipe table. Tab opens a",
                "folded table at the cursor. Optional titles use Pandoc captions and",
                "appear as [[Table N: Title]] in the prose view.",
                f"The basic editor creates 2-6 columns and 1-{MAX_TABLE_INSERT_ROWS} data rows.",
                "Existing and imported tables with up to six columns remain editable",
                "regardless of row count. Wider imported tables are preserved as Markdown",
                "but are not editable in that dialog.",
            ],
        ),
    ]

    rendered = ["Markdown syntax reference", rule]
    rendered.extend(_wrap_dialog_paragraph(intro, width=width))
    rendered.append(rule)
    for index, (heading, body_lines) in enumerate(sections):
        rendered.append(heading)
        prose_parts = []
        def flush_prose():
            nonlocal prose_parts
            if prose_parts:
                rendered.extend(_wrap_dialog_paragraph(" ".join(prose_parts), width=width))
                prose_parts = []
        for line in body_lines:
            if line.startswith("    "):
                flush_prose()
                rendered.append(line)
            else:
                prose_parts.append(line.strip())
        flush_prose()
        if index != len(sections) - 1:
            rendered.append(rule)
    return "\n".join(rendered)


MARKDOWN_HELP_TEXT = _build_markdown_help()

def do_show_help():
    _show_help_reference("Carriage Help", HELP_TEXT)


def do_show_markdown_help():
    _show_help_reference("Markdown Syntax Reference", MARKDOWN_HELP_TEXT)


def do_show_about():
    ok_button = Button(text="OK", handler=close_dialog)
    dialog = Dialog(
        title="About Carriage",
        body=_dialog_prose(ABOUT_TEXT, width=62),
        buttons=[ok_button],
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=ok_button)


# ---------------------------------------------------------------------------
# Status bar
# ---------------------------------------------------------------------------

def get_titlebar_text():
    fname = state.path or "[No Name]"
    if state.is_modified(text_area.text):
        return [
            ("class:title-bar", f" {fname} "),
            ("class:title-bar.modified", "\u25cf"),
        ]
    return [("class:title-bar", f" {fname}")]


def _heading_title(line):
    """Return the visible title for an ATX heading, or None."""
    parsed = _atx_heading_parts(line)
    return parsed[1] if parsed is not None else None


@dataclass(frozen=True)
class _DocumentMetadata:
    """Cached writer-facing metadata for one committed document generation.

    The visible text object and the copy-on-write object dictionaries are used
    as identity tokens. Cursor movement leaves all three identities unchanged,
    while prose edits and committed table/footnote changes replace at least one
    of them. This keeps repaint-only status work O(1) without tying display
    metadata to the recovery journal's broader revision counter.
    """

    visible_text: str
    tables: object
    footnotes: object
    word_count: int
    heading_rows: tuple[int, ...]
    heading_levels: tuple[int, ...]
    heading_titles: tuple[str | None, ...]
    heading_display_titles: tuple[str, ...]


_document_metadata_cache = None


def _document_metadata(visible_text=None):
    """Return cached word-count and heading metadata for the main document."""
    global _document_metadata_cache

    if visible_text is None:
        visible_text = text_area.text

    cache = _document_metadata_cache
    if (
        cache is not None
        and cache.visible_text is visible_text
        and cache.tables is state.tables
        and cache.footnotes is state.footnotes
    ):
        return cache

    blocks = _analyze_document_layout(visible_text, WRAP_COLUMN)
    heading_rows = []
    heading_levels = []
    heading_titles = []
    heading_display_titles = []
    for block in blocks:
        if block.kind == "heading" and block.source_lines:
            parts = _atx_heading_parts(block.source_lines[0])
            if parts is None:
                continue
            marker, title = parts
            heading_rows.append(block.start)
            heading_levels.append(len(marker))
            heading_titles.append(title)
            heading_display_titles.append(
                _plain_heading_text(title) or f"{marker} (untitled)"
            )

    cache = _DocumentMetadata(
        visible_text=visible_text,
        tables=state.tables,
        footnotes=state.footnotes,
        word_count=_prose_word_count(visible_text, blocks=blocks),
        heading_rows=tuple(heading_rows),
        heading_levels=tuple(heading_levels),
        heading_titles=tuple(heading_titles),
        heading_display_titles=tuple(heading_display_titles),
    )
    _document_metadata_cache = cache
    return cache


def _document_progress(doc):
    """Return cursor progress through the visible document as 0-100 percent."""
    if not doc.text:
        return 0
    return max(0, min(100, round(100 * doc.cursor_position / len(doc.text))))


def _document_heading_rows(doc):
    """Return recognized ATX heading rows in document order."""
    return _document_metadata(doc.text).heading_rows


def _move_editor_to_row(row, align_top=False):
    """Move the prose cursor to a logical row, optionally pinning it at top."""
    doc = text_area.buffer.document
    if not doc.lines:
        text_area.buffer.cursor_position = 0
        text_area.window._section_top_anchor_row = 0 if align_top else None
        return

    row = max(0, min(len(doc.lines) - 1, row))
    body_col = _hidden_structural_body_col(doc, row)
    text_area.buffer.cursor_position = doc.translate_row_col_to_index(row, body_col)
    # cursor_position_changed clears an existing anchor. Install the requested
    # one only after the move so it survives until the next ordinary action.
    text_area.window._section_top_anchor_row = row if align_top else None
    get_app().invalidate()


def do_go_top():
    _move_editor_to_row(0)


def do_go_end():
    text_area.buffer.cursor_position = len(text_area.text)
    get_app().invalidate()


def do_go_previous_section():
    """Jump to the nearest heading above the cursor, if any."""
    doc = text_area.buffer.document
    cursor_row = doc.cursor_position_row
    headings = _document_heading_rows(doc)

    # From within a section, the first jump returns to that section heading.
    # From a heading itself, jump to the previous heading instead.
    target = None
    current_title = _heading_title(doc.lines[cursor_row]) if doc.lines else None
    strict = current_title is not None

    for row in headings:
        if row < cursor_row or (row == cursor_row and not strict):
            target = row
        elif row >= cursor_row:
            break

    if target is not None:
        _move_editor_to_row(target, align_top=True)


def do_go_next_section():
    """Jump to the nearest heading below the cursor, if any."""
    doc = text_area.buffer.document
    cursor_row = doc.cursor_position_row
    for row in _document_heading_rows(doc):
        if row > cursor_row:
            _move_editor_to_row(row, align_top=True)
            return


def _section_filter_indices(metadata, query):
    """Return heading indexes whose visible titles contain query."""
    needle = str(query).strip().casefold()
    if not needle:
        return tuple(range(len(metadata.heading_rows)))
    return tuple(
        index
        for index, title in enumerate(metadata.heading_display_titles)
        if needle in title.casefold()
    )


def do_go_to_section():
    """Open the transient hierarchical ATX section navigator."""
    metadata = _document_metadata(text_area.text)
    if not metadata.heading_rows:
        show_transient_status("No sections in this document.")
        return

    cursor_row = text_area.buffer.document.cursor_position_row
    current_heading = bisect_right(metadata.heading_rows, cursor_row) - 1
    initial_heading = current_heading if current_heading >= 0 else 0

    filter_input = SingleLineInput(style="class:input-field")
    session = {
        "matches": tuple(range(len(metadata.heading_rows))),
        "selected": initial_heading,
    }

    def result_fragments():
        matches = session["matches"]
        selected = session["selected"]
        if not matches:
            return [("class:section-nav.empty", "  No matching sections.")]

        fragments = []
        for visible_index, heading_index in enumerate(matches):
            level = metadata.heading_levels[heading_index]
            title = metadata.heading_display_titles[heading_index]
            marker = "› " if visible_index == selected else "  "
            indent = "  " * max(0, level - 1)
            style_name = (
                "class:section-nav.selected"
                if visible_index == selected
                else "class:section-nav"
            )
            fragments.append((style_name, marker + indent + title))
            if visible_index < len(matches) - 1:
                fragments.append(("", "\n"))
        return fragments

    def result_cursor():
        if not session["matches"] or session["selected"] < 0:
            return Point(x=0, y=0)
        return Point(x=0, y=session["selected"])

    results_control = FormattedTextControl(
        text=result_fragments,
        focusable=False,
        show_cursor=False,
        get_cursor_position=result_cursor,
    )
    results_window = Window(
        content=results_control,
        height=D(min=5, preferred=16, max=20),
        wrap_lines=False,
        style="class:section-nav",
    )

    def hint_fragments():
        count = len(session["matches"])
        total = len(metadata.heading_rows)
        count_text = f"{count}/{total}" if filter_input.text.strip() else str(total)
        return [
            (
                "class:table.hint",
                f" {count_text} sections   type to filter   ↑/↓ choose   Enter go   Esc cancel ",
            )
        ]

    hint_window = Window(
        content=FormattedTextControl(hint_fragments),
        height=1,
        dont_extend_height=True,
    )

    def refresh_results(_buffer=None):
        old_matches = session["matches"]
        old_selected = session["selected"]
        old_heading = (
            old_matches[old_selected]
            if old_matches and 0 <= old_selected < len(old_matches)
            else None
        )
        matches = _section_filter_indices(metadata, filter_input.text)
        session["matches"] = matches
        if not matches:
            session["selected"] = -1
        elif old_heading in matches:
            session["selected"] = matches.index(old_heading)
        elif initial_heading in matches:
            session["selected"] = matches.index(initial_heading)
        else:
            session["selected"] = 0
        get_app().invalidate()

    def move_selection(delta):
        matches = session["matches"]
        if not matches:
            return
        selected = session["selected"]
        if selected < 0:
            selected = 0
        else:
            selected = max(0, min(len(matches) - 1, selected + delta))
        session["selected"] = selected
        get_app().invalidate()

    def jump_to_selection():
        matches = session["matches"]
        selected = session["selected"]
        if not matches or not (0 <= selected < len(matches)):
            return
        heading_index = matches[selected]
        target_row = metadata.heading_rows[heading_index]
        close_dialog()
        _move_editor_to_row(target_row, align_top=True)

    filter_input.buffer.on_text_changed += refresh_results
    navigator_kb = filter_input.control.key_bindings

    @navigator_kb.add("up")
    @navigator_kb.add("c-p")
    def _previous(event):
        move_selection(-1)

    @navigator_kb.add("down")
    @navigator_kb.add("c-n")
    def _next(event):
        move_selection(1)

    @navigator_kb.add("enter")
    def _jump(event):
        jump_to_selection()

    @navigator_kb.add("escape")
    def _cancel(event):
        close_dialog()

    body = HSplit(
        [
            Label(text="Filter:"),
            filter_input,
            Window(height=1),
            results_window,
            hint_window,
        ]
    )
    dialog = Dialog(
        title="Go to Section",
        body=body,
        buttons=None,
        width=D(preferred=72, max=88),
    )
    show_dialog(dialog, focus=filter_input)


def _fit_status_field(text, width):
    """Truncate/pad text to exactly `width` terminal columns."""
    width = max(0, width)
    if width == 0:
        return ""

    if get_cwidth(text) > width:
        ellipsis = "…"
        target = max(0, width - get_cwidth(ellipsis))
        chars = []
        used = 0
        for char in text:
            char_width = get_cwidth(char)
            if used + char_width > target:
                break
            chars.append(char)
            used += char_width
        text = "".join(chars).rstrip() + ellipsis

    padding = max(0, width - get_cwidth(text))
    return text + (" " * padding)


def _status_section_width(terminal_columns):
    """Choose a stable section slot from the current terminal width."""
    # Every field except the section uses a fixed-width presentation, so
    # changing section titles cannot shift the remaining status information.
    # At narrower terminal widths the section slot yields space first; on
    # wider screens it grows to roughly 38% of the window, capped to keep the
    # status bar visually balanced.
    fixed_other_width = (
        4  # progress field ("100%")
        + 15  # word-count field
        + 20  # command hint
        + (3 * 3)  # three ordinary " | " separators
        + 2  # outer padding
    )
    if state.recovery_error:
        fixed_other_width += 14 + 3  # "recovery:error" plus one separator
    available = max(1, terminal_columns - fixed_other_width)
    desired = max(16, round(terminal_columns * 0.38))
    return max(1, min(60, desired, available))


def _status_section_field(title, terminal_columns):
    width = _status_section_width(terminal_columns)
    label = f"§ {title}" if title else "§"
    return _fit_status_field(label, width)


def _blank_source_ranges(text, ranges):
    """Replace source-only inline ranges with spaces without joining words."""
    if not ranges:
        return text
    chars = list(text)
    for start, end in ranges:
        start = max(0, start)
        end = min(len(chars), end)
        for index in range(start, end):
            chars[index] = " "
    return "".join(chars)


def _prose_inline_text_for_count(text):
    """Return inline Markdown reduced to the prose that a writer actually wrote.

    Code spans, link destinations/reference labels, autolinks/raw inline HTML,
    and live footnote-reference markers are source mechanics rather than prose.
    Link labels and ordinary emphasized text remain, because they are visible
    document language. Bare URLs/e-mail addresses count as one token.
    """
    if not text:
        return ""

    # Original-Markdown autolinks render their address as visible document
    # text, so count each as one word. Raw inline HTML remains excluded below.
    text = _AUTOLINK_RE.sub(" proseurl ", text)
    protected = list(_inline_footnote_literal_ranges(text))
    reduced = _blank_source_ranges(text, protected)

    # Footnote references outside literal/protected ranges are annotations, not
    # prose words. Keep escaped ``\[^id]`` source literal.
    chars = list(reduced)
    for match in _FOOTNOTE_REFERENCE_RE.finditer(reduced):
        if _markdown_char_is_escaped(reduced, match.start()):
            continue
        for index in range(match.start(), match.end()):
            chars[index] = " "
    reduced = "".join(chars)

    # A bare URL or e-mail address behaves like one word in ordinary writing,
    # rather than contributing each domain/path component separately.
    reduced = _BARE_URL_OR_EMAIL_RE.sub(" proseurl ", reduced)
    return reduced


def _count_prose_fragment(text):
    return len(_PROSE_WORD_RE.findall(_prose_inline_text_for_count(str(text))))


def _count_table_prose(table):
    """Count table language without pipes, alignment syntax, or table numbers."""
    total = _count_prose_fragment(table.title)
    for cell in table.headers:
        total += _count_prose_fragment(cell)
    for row in table.rows:
        for cell in row:
            total += _count_prose_fragment(cell)
    return total


def _count_raw_pipe_table_prose(source_lines):
    """Count prose in a visible pipe table that has not been folded yet."""
    if len(source_lines) < 2 or not _is_pipe_table_separator(source_lines[1]):
        return sum(_count_prose_fragment(line) for line in source_lines)
    total = 0
    for row_index, line in enumerate(source_lines):
        if row_index == 1:
            continue
        for cell in _table_cells_from_line(line):
            total += _count_prose_fragment(cell)
    return total


def _prose_word_count(visible_text, blocks=None):
    """Return a writer-facing word count for the current Carriage document.

    Markdown block/inline syntax does not count as language. Folded object
    content is counted from its in-memory data, so the status bar reflects what
    will be saved without counting placeholder labels or table separators.
    ``blocks`` lets the metadata cache reuse the document analysis it already
    needed for the heading index.
    """
    total = 0

    if blocks is None:
        blocks = _analyze_document_layout(visible_text, WRAP_COLUMN)

    for block in blocks:
        if block.kind in {
            "blank",
            "front-matter",
            "code",
            "block-html",
            "thematic-break",
        }:
            continue

        if block.kind == "reference-definition":
            # Ordinary link reference definitions are source infrastructure. A
            # footnote definition, however, contains document prose. Foldable
            # prose notes are normally objects, but this keeps the live count sensible
            # while a writer is typing one directly into the buffer.
            first = _FOOTNOTE_DEFINITION_RE.match(block.source_lines[0])
            if first is not None:
                total += _count_prose_fragment(first.group(2))
                for continuation in block.source_lines[1:]:
                    body = _footnote_continuation_text(continuation)
                    if body is not None:
                        total += _count_prose_fragment(body)
            continue

        if block.kind == "table":
            # Folded tables are counted from the authoritative TableData object.
            if len(block.source_lines) == 1:
                match = TABLE_PLACEHOLDER_RE.match(block.source_lines[0])
                if match is not None:
                    table = state.tables.get(int(match.group(1)))
                    if table is not None:
                        total += _count_table_prose(table)
                    continue
            total += _count_raw_pipe_table_prose(block.source_lines)
            continue

        if block.kind == "footnote-placeholder":
            match = FOOTNOTE_PLACEHOLDER_RE.match(block.source_lines[0])
            if match is not None:
                note = state.footnotes.get(match.group(1))
                if note is not None:
                    total += _count_prose_fragment(note.text)
            continue

        source_lines = block.source_lines
        if block.kind == "setext-heading":
            source_lines = source_lines[:1]

        for source_line in source_lines:
            text = source_line

            # Ordered-list numbers are syntax. Unordered markers contain no
            # word characters, but stripping all markers keeps the rule clear.
            if block.kind in {"list", "list-run", "complex-list"}:
                list_match = _LIST_ITEM_RE.match(text)
                if list_match is not None:
                    text = text[list_match.end():]

            # A manually typed (not-yet-folded) prose footnote definition
            # counts its body but not the identifier. Continuation lines are
            # ordinary prose and fall through naturally.
            footnote_match = _FOOTNOTE_DEFINITION_RE.match(text)
            if footnote_match is not None:
                text = footnote_match.group(2)

            total += _count_prose_fragment(text)

    return total



def get_statusbar_text():
    transient = _current_transient_status_message()
    if transient is not None:
        return [("class:status", f" {transient} ")]

    doc = text_area.buffer.document
    metadata = _document_metadata(doc.text)
    words = metadata.word_count
    section_index = bisect_right(metadata.heading_rows, doc.cursor_position_row) - 1
    section = metadata.heading_titles[section_index] if section_index >= 0 else None
    progress = _document_progress(doc)

    try:
        terminal_columns = get_app().output.get_size().columns
    except Exception:
        terminal_columns = 80

    section_field = _status_section_field(section, terminal_columns)
    word_field = f"{words:,} words".ljust(15)
    progress_field = f"{progress:>3}%"
    command_field = (
        "EXTEND  F6 end" if state.extend_selection_mode else "^Space menu  ^Q quit"
    )

    # Working-state protection is normally silent. Surface only a failure.
    fields = [progress_field, section_field, word_field]
    if state.recovery_error:
        fields.append("recovery:error")
    if state.pandoc_export_running:
        fields.append("exporting")
    fields.append(command_field)

    # Keep navigation information together at the left, followed by
    # document/editor state and finally command hints.
    status = " | ".join(fields)
    return [("class:status", f" {status} ")]


# ---------------------------------------------------------------------------
# Layout / menus / key bindings
# ---------------------------------------------------------------------------

title_bar = Window(
    content=FormattedTextControl(get_titlebar_text),
    height=1,
    style="class:title-bar",
    align=WindowAlign.CENTER,
)
title_divider = Window(height=1, char="─", style="class:divider")

status_divider = ConditionalContainer(
    Window(height=1, char="─", style="class:divider"),
    filter=Condition(lambda: state.statusbar_visible),
)


# Find/Replace deliberately occupies the status-line row instead of opening a
# dialog. If the ordinary status bar is hidden, this one row is temporarily
# allocated while Find/Replace is active so the current match can never scroll
# underneath an overlay.
find_input = SingleLineInput(style="class:status")
replace_input = SingleLineInput(style="class:status")
find_input.window.width = D(min=12, preferred=30)
replace_input.window.width = D(min=12, preferred=30)
find_input.buffer.on_text_changed += _find_replace_query_changed
replace_input.buffer.on_text_changed += _find_replace_replacement_changed

normal_status_row = ConditionalContainer(
    Window(
        content=FormattedTextControl(get_statusbar_text),
        height=1,
        style="class:status",
    ),
    filter=Condition(lambda: not find_replace.active),
)
find_row = ConditionalContainer(
    VSplit(
        [
            Window(
                content=FormattedTextControl(lambda: [("class:status", " Find: ")]),
                height=1,
                width=D.exact(7),
                style="class:status",
            ),
            find_input,
            Window(
                content=FormattedTextControl(
                    lambda: [("class:status", _find_replace_hint_text())]
                ),
                height=1,
                width=D(min=20, preferred=52, max=68),
                dont_extend_width=True,
                style="class:status",
            ),
        ]
    ),
    filter=Condition(lambda: find_replace.active and find_replace.mode == "find"),
)
replace_row = ConditionalContainer(
    VSplit(
        [
            Window(
                content=FormattedTextControl(lambda: [("class:status", " Replace: ")]),
                height=1,
                width=D.exact(10),
                style="class:status",
            ),
            replace_input,
            Window(
                content=FormattedTextControl(
                    lambda: [("class:status", _find_replace_hint_text())]
                ),
                height=1,
                width=D(min=20, preferred=52, max=68),
                dont_extend_width=True,
                style="class:status",
            ),
        ]
    ),
    filter=Condition(lambda: find_replace.active and find_replace.mode == "replace"),
)
status_bar = ConditionalContainer(
    HSplit([normal_status_row, find_row, replace_row]),
    filter=Condition(lambda: state.statusbar_visible or find_replace.active),
)

# When the normal status bar is disabled, transient notices still occupy the
# same bottom screen row as an overlay. This keeps the notification location
# consistent without temporarily changing the editor's height.
transient_status_overlay = ConditionalContainer(
    Window(
        content=FormattedTextControl(get_statusbar_text),
        height=1,
        style="class:status",
    ),
    filter=Condition(
        lambda: (
            not state.statusbar_visible
            and not find_replace.active
            and _current_transient_status_message() is not None
        )
    ),
)
floats.append(
    Float(
        content=transient_status_overlay,
        left=0,
        right=0,
        bottom=0,
        height=1,
    )
)

body = HSplit(
    [
        text_area,
        status_divider,
        status_bar,
    ]
)

class EdgeAlignedMenuContainer(MenuContainer):
    """MenuContainer with symmetric top-level selection highlighting.

    prompt_toolkit inserts one separator cell before every top-level menu item.
    Keep that separator in the ordinary menu-bar style so the selected
    highlight covers only the menu label itself. Preserve Carriage's special
    first-menu anchoring by placing File's submenu marker before its separator;
    all later submenus anchor at the start of their visible label.
    """

    def _get_menu_fragments(self):
        focused = get_app().layout.has_focus(self.window)

        # Match MenuContainer's normal behavior: once focus leaves the menu
        # bar, reset the next opening to the first top-level item.
        if not focused:
            self.selected_menu = [0]

        def one_item(index, item):
            def mouse_handler(mouse_event):
                hover = mouse_event.event_type == MouseEventType.MOUSE_MOVE
                if (
                    mouse_event.event_type == MouseEventType.MOUSE_DOWN
                    or hover and focused
                ):
                    app = get_app()
                    if not hover:
                        if find_replace.active:
                            _close_find_replace()
                        if app.layout.has_focus(self.window):
                            if self.selected_menu == [index]:
                                app.layout.focus_last()
                        else:
                            app.layout.focus(self.window)
                    self.selected_menu = [index]

            selected = index == self.selected_menu[0] and focused

            # Keep File's pull-down flush with the menu bar's left edge, but
            # do not color its leading separator as part of the selection.
            if selected and index == 0:
                yield ("[SetMenuPosition]", "", mouse_handler)

            yield ("class:menu-bar", " ", mouse_handler)

            # Other pull-downs begin at the visible start of their labels,
            # matching prompt_toolkit's normal menu positioning.
            if selected and index != 0:
                yield ("[SetMenuPosition]", "", mouse_handler)

            style_name = (
                "class:menu-bar.selected-item"
                if selected
                else "class:menu-bar"
            )
            yield (style_name, item.text, mouse_handler)

        result = []
        for index, item in enumerate(self.menu_items):
            result.extend(one_item(index, item))
        return result


def _menu_label(label, shortcut=None, shortcut_col=None):
    """Return a menu caption with shortcuts aligned to one column.

    Each pull-down chooses a shortcut column appropriate to its own labels.
    Shortcutless commands remain unpadded, while every shortcut-bearing item
    in that menu begins at the same rendered cell.
    """
    if not shortcut:
        return label
    if shortcut_col is None:
        shortcut_col = get_cwidth(label) + 2
    padding = max(2, shortcut_col - get_cwidth(label))
    return f"{label}{' ' * padding}{shortcut}"


menu_container = EdgeAlignedMenuContainer(
    body=body,
    menu_items=[
        MenuItem(
            "  File  ",
            children=[
                MenuItem(_menu_label("New", "Ctrl+N", 13), handler=with_unsaved_changes_check(do_new)),
                MenuItem(_menu_label("Open...", "Ctrl+O", 13), handler=with_unsaved_changes_check(do_open)),
                MenuItem(_menu_label("Save", "Ctrl+S / F9", 13), handler=do_save),
                MenuItem("Save As...", handler=do_save_as),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Quit", "Ctrl+Q", 13), handler=with_unsaved_changes_check(do_quit)),
            ],
        ),
        MenuItem(
            "  Edit  ",
            children=[
                MenuItem(_menu_label("Undo", "Ctrl+Z", 18), handler=do_undo),
                MenuItem(_menu_label("Redo", "Ctrl+R", 18), handler=do_redo),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Cut", "Ctrl+X", 18), handler=do_cut),
                MenuItem(_menu_label("Copy", "Ctrl+C", 18), handler=do_copy),
                MenuItem(_menu_label("Paste", "Ctrl+V", 18), handler=do_paste),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Find / Replace...", "Ctrl+F", 18), handler=do_find_replace),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Italic", "F2", 18), handler=do_toggle_italic),
                MenuItem(_menu_label("Bold", "F3", 18), handler=do_toggle_bold),
                MenuItem(_menu_label("Extend Selection", "F6", 18), handler=lambda: _toggle_extend_selection_mode()),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Renumber List", "F8", 18), handler=do_renumber_list),
                MenuItem("Convert for Carriage", handler=do_convert_for_carriage),
                MenuItem("-", disabled=True),
                MenuItem("Toggle Status Bar", handler=do_toggle_statusbar),
            ],
        ),
        MenuItem(
            "  Go  ",
            children=[
                MenuItem(_menu_label("Top of Document", "Ctrl+Home", 20), handler=do_go_top),
                MenuItem(_menu_label("End of Document", "Ctrl+End", 20), handler=do_go_end),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Go to Section...", "Alt+G", 20), handler=do_go_to_section),
                MenuItem(_menu_label("Previous Section", "Alt+Up", 20), handler=do_go_previous_section),
                MenuItem(_menu_label("Next Section", "Alt+Down", 20), handler=do_go_next_section),
            ],
        ),
        MenuItem(
            "  Export  ",
            children=[
                MenuItem("Hard-Wrapped Markdown (.md)", handler=do_export_hard_wrapped_markdown),
                MenuItem("-", disabled=True),
                MenuItem("PDF (.pdf)", handler=lambda: export_via_pandoc("PDF", "pdf")),
                MenuItem("Word (.docx)", handler=lambda: export_via_pandoc("Word", "docx")),
                MenuItem(
                    "OpenDocument (.odt)",
                    handler=lambda: export_via_pandoc("OpenDocument Text", "odt"),
                ),
                MenuItem(
                    "HTML (.html)",
                    handler=lambda: export_via_pandoc(
                        "HTML", "html", ["--standalone"]
                    ),
                ),
                MenuItem("Custom pandoc command...", handler=do_custom_export),
            ],
        ),
        MenuItem(
            "  Tools  ",
            children=[
                MenuItem(_menu_label("Spell Check", "F7", 26), handler=do_run_spellcheck),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Insert Table...", "F4", 26), handler=do_insert_table),
                MenuItem(_menu_label("Edit Table at Cursor", "Tab", 26), handler=do_edit_table_at_cursor),
                MenuItem("Delete Table at Cursor...", handler=do_delete_table_at_cursor),
                MenuItem("-", disabled=True),
                MenuItem(_menu_label("Insert Footnote", "F5", 26), handler=do_insert_footnote),
                MenuItem(_menu_label("Edit Footnote at Cursor", "Tab", 26), handler=do_edit_footnote_at_cursor),
                MenuItem("Delete Footnote at Cursor...", handler=do_delete_footnote_at_cursor),
            ],
        ),
        MenuItem(
            "  Help  ",
            children=[
                MenuItem(_menu_label("Carriage Help", "F1", 16), handler=do_show_help),
                MenuItem("Markdown Syntax", handler=do_show_markdown_help),
                MenuItem("-", disabled=True),
                MenuItem("About Carriage", handler=do_show_about),
            ],
        ),
    ],
)

# MenuContainer concatenates whatever `floats` list you hand it into a *new*
# list at construction time (`... + (floats or [])`), so it never actually
# keeps a live reference to our `floats` list - appending to it later has no
# effect on what's rendered. We wrap it in our own FloatContainer instead,
# which stores the list by reference, so show_dialog()/close_dialog() can
# mutate `floats` and have it actually show up.
root_container = FloatContainer(
    content=HSplit([title_bar, title_divider, menu_container]), floats=floats
)

layout = Layout(root_container, focused_element=text_area)

editor_focused = Condition(
    lambda: get_app().layout.has_focus(text_area) and not find_replace.active
)
find_focused = Condition(lambda: get_app().layout.has_focus(find_input))
replace_focused = Condition(lambda: get_app().layout.has_focus(replace_input))
find_replace_focused = find_focused | replace_focused
find_replace_active = Condition(lambda: find_replace.active)

kb = KeyBindings()


@kb.add("c-n", filter=editor_focused)
def _(event):
    with_unsaved_changes_check(do_new)()


@kb.add("c-o", filter=editor_focused)
def _(event):
    with_unsaved_changes_check(do_open)()


@kb.add("c-f", filter=editor_focused)
def _(event):
    do_find_replace()


@kb.add("c-f", filter=find_replace_active)
def _(event):
    _find_replace_show_find()


@kb.add("f2", filter=editor_focused)
def _(event):
    # Selection-only italic toggle. Carriage intentionally does not provide a
    # persistent formatting mode or a Ctrl+I alias (Ctrl+I is Tab in terminals).
    do_toggle_italic()


@kb.add("f3", filter=editor_focused)
def _(event):
    # Selection-only bold toggle; F3 is the sole keyboard shortcut.
    do_toggle_bold()


@kb.add("f4", filter=editor_focused)
def _(event):
    # F4 is the single-keystroke alias for Tools > Insert Table.
    do_insert_table()


@kb.add("f5", filter=editor_focused)
def _(event):
    # F5 is the single-keystroke alias for Tools > Insert Footnote.
    do_insert_footnote()


@kb.add("c-s", filter=editor_focused)
@kb.add("f9", filter=editor_focused)
def _(event):
    # F9 is the single-keystroke function-key alias for the same explicit
    # manual Save operation as Ctrl+S. Keep one code path so both commands
    # share atomic replacement, conflict detection, and journal clearing.
    do_save()


@kb.add("c-q", filter=editor_focused)
def _(event):
    with_unsaved_changes_check(do_quit)()


@kb.add("c-x", filter=editor_focused, eager=True)
def _(event):
    # Ctrl+X is an Emacs prefix in prompt_toolkit's defaults. eager=True makes
    # the standard desktop Cut command immediate inside Carriage.
    do_cut()


@kb.add("c-c", filter=editor_focused)
def _(event):
    do_copy()


@kb.add("c-v", filter=editor_focused)
def _(event):
    do_paste()


# Carriage previously inherited prompt_toolkit's Emacs clipboard vocabulary.
# Consume those legacy chords so the documented Ctrl+X/C/V mapping is the one
# keyboard interface rather than an additional set of aliases.
@kb.add("c-w", filter=editor_focused)
@kb.add("escape", "w", filter=editor_focused)
@kb.add("c-y", filter=editor_focused)
def _(event):
    pass


@kb.add("c-home", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _extend_selection_to_position(0)
    else:
        event.current_buffer.exit_selection()
        do_go_top()


@kb.add("c-end", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _extend_selection_to_position(len(text_area.text))
    else:
        event.current_buffer.exit_selection()
        do_go_end()


# Most terminals encode Alt combinations as Escape followed by the key.
@kb.add("escape", "g", filter=editor_focused)
def _(event):
    do_go_to_section()


@kb.add("escape", "up", filter=editor_focused)
def _(event):
    do_go_previous_section()


@kb.add("escape", "down", filter=editor_focused)
def _(event):
    do_go_next_section()


@kb.add("c-z", filter=buffer_has_focus, save_before=lambda e: False)
def _(event):
    event.current_buffer.undo()


@kb.add("c-r", filter=buffer_has_focus, save_before=lambda e: False)
def _(event):
    event.current_buffer.redo()


@kb.add("f6", filter=editor_focused)
def _(event):
    _toggle_extend_selection_mode()


@kb.add("f7", filter=editor_focused)
def _(event):
    do_run_spellcheck()


@kb.add("f8", filter=editor_focused)
def _(event):
    do_renumber_list()


# Find/Replace key handling stays intentionally small and terminal-portable.
# prompt_toolkit 3.0.52/3.0.53 cannot represent Shift+Enter as a distinct key,
# and many terminals transmit it identically to Enter. Use Up for Previous and
# Enter/Down for Next instead of depending on an unportable escape sequence.
@kb.add("enter", filter=find_focused)
@kb.add("down", filter=find_focused)
@kb.add("c-n", filter=find_focused)
def _(event):
    _find_replace_step(1)


@kb.add("up", filter=find_focused)
@kb.add("c-p", filter=find_focused)
def _(event):
    _find_replace_step(-1)


@kb.add("tab", filter=find_focused)
def _(event):
    _find_replace_show_replace()


@kb.add("enter", filter=replace_focused)
def _(event):
    _find_replace_replace_current()


@kb.add("down", filter=replace_focused)
@kb.add("c-n", filter=replace_focused)
def _(event):
    _find_replace_step(1)


@kb.add("up", filter=replace_focused)
@kb.add("c-p", filter=replace_focused)
def _(event):
    _find_replace_step(-1)


@kb.add("tab", filter=replace_focused)
@kb.add("s-tab", filter=replace_focused)
def _(event):
    _find_replace_show_find()


@kb.add("escape", "c", filter=find_replace_focused)
def _(event):
    _find_replace_toggle_case()


@kb.add("escape", "w", filter=find_replace_focused)
def _(event):
    _find_replace_toggle_whole_word()


@kb.add("escape", "a", filter=replace_focused)
def _(event):
    _find_replace_replace_all()


@kb.add("escape", filter=find_replace_active)
def _(event):
    _close_find_replace()


no_dialog_open = Condition(
    lambda: current_float is None and not find_replace.active
)
menu_focused = Condition(lambda: get_app().layout.has_focus(menu_container.window))
dialog_open = Condition(lambda: current_float is not None)
table_editor_active = Condition(
    lambda: (
        current_table_editor is not None
        and current_float is current_table_editor.dialog_float
    )
)
cursor_on_table_reference = Condition(
    lambda: current_table_editor is None and _table_number_at_cursor() is not None
)
cursor_on_footnote_reference = Condition(
    lambda: current_footnote_editor is None and _footnote_identifier_at_cursor() is not None
)


@kb.add("tab", filter=editor_focused & cursor_on_table_reference)
def _(event):
    do_edit_table_at_cursor()


@kb.add("tab", filter=editor_focused & ~cursor_on_table_reference & cursor_on_footnote_reference)
def _(event):
    do_edit_footnote_at_cursor()


@kb.add("tab", filter=editor_focused & ~cursor_on_table_reference & ~cursor_on_footnote_reference)
def _(event):
    # prompt_toolkit displays literal tab characters as ^I. In the prose
    # editor, make Tab behave like a conventional indentation key instead:
    # insert spaces up to the next four-column tab stop. Folded tables and
    # footnote references keep their special Tab behavior above.
    col = event.current_buffer.document.cursor_position_col
    spaces = TAB_WIDTH - (col % TAB_WIDTH)
    event.current_buffer.insert_text(" " * spaces)


def _after_inline_footnote_reference():
    buf = text_area.buffer
    if buf.selection_state is not None:
        return False
    span = _footnote_source_span_at_cursor(buf.document, direction=-1)
    return span is not None and buf.document.cursor_position_col == span[1]


def _before_inline_footnote_reference():
    buf = text_area.buffer
    if buf.selection_state is not None:
        return False
    span = _footnote_source_span_at_cursor(buf.document, direction=1)
    return span is not None and buf.document.cursor_position_col == span[0]


def _delete_inline_footnote_reference(buf, direction):
    span = _footnote_source_span_at_cursor(buf.document, direction=direction)
    if span is None:
        return
    start_col, end_col, _identifier = span
    doc = buf.document
    row = doc.cursor_position_row
    start = doc.translate_row_col_to_index(row, start_col)
    end = doc.translate_row_col_to_index(row, end_col)
    buf.document = Document(
        text=buf.text[:start] + buf.text[end:],
        cursor_position=start,
    )


@kb.add("backspace", filter=editor_focused & Condition(_after_inline_footnote_reference))
def _(event):
    # Remove the compact [n] reference as one source object. The definition is
    # intentionally retained; orphaned note text is safer than silent data loss.
    _delete_inline_footnote_reference(event.current_buffer, direction=-1)


@kb.add("delete", filter=editor_focused & Condition(_before_inline_footnote_reference))
def _(event):
    _delete_inline_footnote_reference(event.current_buffer, direction=1)


def _at_list_item_body_start():
    """Return True at the visible start of a supported list item's prose.

    List markers live in the hanging gutter. From the writer's point of view,
    Backspace at the first prose character crosses that entire structural
    marker, not merely its final source-space character.
    """
    buf = text_area.buffer
    if buf.selection_state is not None:
        return False
    doc = buf.document
    row = doc.cursor_position_row
    prefix_width = _active_structural_prefix_width(
        doc, row, role="list-marker"
    )
    return prefix_width is not None and doc.cursor_position_col == prefix_width


def _at_list_continuation_start():
    buf = text_area.buffer
    if buf.selection_state is not None:
        return False
    doc = buf.document
    prefix_width = _list_continuation_prefix_width(doc, doc.cursor_position_row)
    return prefix_width is not None and doc.cursor_position_col == prefix_width


def _before_list_continuation():
    buf = text_area.buffer
    if buf.selection_state is not None:
        return False
    doc = buf.document
    row = doc.cursor_position_row
    if doc.cursor_position_col != len(doc.current_line) or row + 1 >= doc.line_count:
        return False
    return _list_continuation_prefix_width(doc, row + 1) is not None


@kb.add("backspace", filter=editor_focused & Condition(_at_list_item_body_start))
def _(event):
    # The marker is displayed in the hanging gutter, so Backspace from the
    # visible start of list prose removes the marker as one structural unit.
    # Canonical continuation indentation belongs to that same marker and is
    # removed at the same time, converting the item cleanly into ordinary
    # prose instead of leaving a half-broken marker plus hidden indentation.
    buf = event.current_buffer
    doc = buf.document
    row = doc.cursor_position_row
    lines = list(doc.lines)
    run_end = _nonblank_run_end(lines, row)
    block = _parse_simple_list_item(lines, row, limit=run_end)
    if block is None or block.marker is None:
        return

    converted = _unlist_simple_list_item(block)
    lines[block.start:block.end] = converted
    new_text = "\n".join(lines)
    tmp = Document(text=new_text)
    new_row = min(block.start, tmp.line_count - 1)
    new_cursor = tmp.translate_row_col_to_index(new_row, 0)
    buf.document = Document(text=new_text, cursor_position=new_cursor)


@kb.add("backspace", filter=editor_focused & Condition(_at_list_continuation_start))
def _(event):
    # Continuation indentation is structural Markdown presented in the hanging
    # gutter. At the visible start of continuation prose, Backspace therefore
    # crosses the whole hidden boundary in one step instead of deleting those
    # indentation spaces one by one.
    buf = event.current_buffer
    doc = buf.document
    prefix_width = _list_continuation_prefix_width(doc, doc.cursor_position_row)
    if prefix_width is None:
        return
    start = buf.cursor_position - prefix_width - 1  # newline + indentation
    if start < 0:
        return
    text = buf.text
    buf.document = Document(
        text=text[:start] + text[buf.cursor_position:],
        cursor_position=start,
    )


@kb.add("delete", filter=editor_focused & Condition(_before_list_continuation))
def _(event):
    # Symmetric with Backspace above: Delete at the end of a physical line
    # removes the following newline plus canonical continuation indentation as
    # one boundary.
    buf = event.current_buffer
    doc = buf.document
    prefix_width = _list_continuation_prefix_width(doc, doc.cursor_position_row + 1)
    if prefix_width is None:
        return
    pos = buf.cursor_position
    remove = 1 + prefix_width
    buf.document = Document(
        text=buf.text[:pos] + buf.text[pos + remove:],
        cursor_position=pos,
    )


@kb.add(
    "backspace",
    filter=(
        editor_focused
        & Condition(lambda: text_area.buffer.selection_state is not None)
        & ~cursor_on_table_reference
    ),
)
def _(event):
    # prompt_toolkit's default backward-delete behavior does not consistently
    # replace an active selection. In the prose editor, Backspace should match
    # Delete: when text is selected, remove the selection as one edit. Leave
    # ordinary Backspace behavior untouched when there is no selection.
    event.current_buffer.cut_selection()


@kb.add("enter", filter=editor_focused)
def _(event):
    folded = _folded_placeholder_at_cursor()
    if folded is not None:
        if folded[0] == "table":
            do_edit_table_at_cursor()
        else:
            open_footnote_editor(folded[1])
        return

    # Keep Return deliberately literal in the prose editor. prompt_toolkit's
    # default newline binding copies the current line's leading margin, which
    # makes list entry look as though Carriage is trying to continue the list.
    # Carriage does not auto-create list markers or indentation: Return starts
    # at column zero on the next physical line. If text is selected, replace
    # the selection with that newline, as a normal editor would.
    buf = event.current_buffer
    if buf.selection_state is not None:
        buf.cut_selection()
    buf.insert_text("\n")


def _line_prefix_cell_width(row, wrap_count):
    """Return the terminal-cell width of one display-only continuation prefix."""
    prefix = text_area.window.get_line_prefix
    if prefix is None:
        return 0
    try:
        fragments = prefix(row, wrap_count)
    except Exception:
        return 0
    width = 0
    for fragment in fragments or []:
        # Formatted-text fragments can carry mouse handlers/extra tuple fields;
        # style is item 0 and text is item 1.
        if len(fragment) >= 2:
            width += _display_text_width(fragment[1])
    return width


_VISUAL_NAVIGATION_CACHE_ROWS = 64


def _visual_navigation_cache_key(row, info):
    """Return the layout generation key for one navigated logical row."""
    if info is None or info.window_width <= 0:
        return None
    generation = getattr(text_area.window, "_height_cache_generation", 0)
    try:
        columns = get_app().output.get_size().columns
    except Exception:
        columns = None
    return (generation, int(row), int(info.window_width), columns)


def _store_bounded_visual_cache(cache, key, value):
    """Keep navigation caches useful without retaining an unbounded row set."""
    if key not in cache and len(cache) >= _VISUAL_NAVIGATION_CACHE_ROWS:
        cache.pop(next(iter(cache)))
    cache[key] = value
    return value


def _visual_display_positions(row, info):
    """Map processed display columns on one logical line to (wrap row, x).

    This mirrors prompt_toolkit Window._copy_body's line-wrapping rule, but it
    operates only on one logical line and creates no screen. ``x`` is measured
    in rendered terminal cells inside the editor Window, after Carriage's
    display processor and continuation prefix have been applied.

    Vertical navigation asks for this mapping repeatedly while moving through a
    long soft-wrapped paragraph.  Cache it for the current text/layout
    generation so the same transformed line is measured only once.
    """
    key = _visual_navigation_cache_key(row, info)
    if key is None:
        return None
    cache = text_area.window._visual_positions_cache
    cached = cache.get(key)
    if cached is not None:
        return cached

    try:
        get_processed = getattr(text_area.control, "_last_get_processed_line", None)
        if get_processed is None:
            return None
        # BufferControl's processed-line cache already contains Carriage's
        # transformed fragments. UIContent.get_line() wraps that same result
        # and appends one cursor cell; avoid asking it to process the line again.
        processed = get_processed(row)
        fragments = explode_text_fragments(processed.fragments)
        fragments.append(("", " "))
    except Exception:
        return None

    width = info.window_width
    wrap_row = 0
    x = _line_prefix_cell_width(row, 0)
    positions = []

    for fragment in fragments:
        char = fragment[1]
        char_width = _display_char_width(char)
        if x + char_width > width:
            wrap_row += 1
            x = _line_prefix_cell_width(row, wrap_row)
        positions.append((wrap_row, x))
        x += char_width

    # Cursor position after the final display character. In practice UIContent
    # appends one cursor cell to every line, so source EOL normally maps to the
    # position of that cell; keeping the terminal position here is useful for
    # defensive/fallback mappings as well.
    positions.append((wrap_row, x))
    return _store_bounded_visual_cache(cache, key, tuple(positions))


def _visual_source_candidates(row, info):
    """Return navigable source positions grouped by rendered wrap row.

    This is the single source/display resolver used by Up/Down and Home/End.
    Hidden structural prefixes, compact-footnote interiors, and positions after
    folded-object sentinels are excluded explicitly rather than relying on
    source-column tie breaking to make them unreachable by accident.
    """
    key = _visual_navigation_cache_key(row, info)
    if key is None:
        return None
    cache = text_area.window._visual_candidates_cache
    cached = cache.get(key)
    if cached is not None:
        return cached

    doc = text_area.buffer.document
    if not (0 <= row < doc.line_count):
        return None

    get_processed = getattr(text_area.control, "_last_get_processed_line", None)
    positions = _visual_display_positions(row, info)
    if get_processed is None or not positions:
        return None
    try:
        processed = get_processed(row)
    except Exception:
        return None

    source_line = doc.lines[row]
    body_col = _hidden_structural_body_col(doc, row)
    footnote_spans = tuple(_footnote_display_spans(doc.text, row))
    compact_ranges = tuple(
        (span[0], span[1])
        for span in footnote_spans
        if len(span) >= 5 and not span[4]
    )
    folded_footnote = any(len(span) >= 5 and span[4] for span in footnote_spans)
    folded_visible_end = (
        max(0, len(source_line) - 1)
        if folded_footnote and source_line.endswith(FOOTNOTE_SENTINEL)
        else None
    )

    by_wrap = {}
    for source_col in range(len(source_line) + 1):
        # Structural Markdown rendered in the hanging gutter is presentation,
        # not ordinary caret space.
        if source_col < body_col:
            continue
        # The source position after a folded-object sentinel is invisible. The
        # canonical visible line end is immediately before the sentinel.
        if (
            source_col > 0
            and source_line[source_col - 1:source_col]
            in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}
        ):
            continue
        # Compact footnote source such as ``[^smith]`` is displayed as ``[1]``.
        # Only the two visible object boundaries are legal cursor stops.
        if any(start_col < source_col < end_col for start_col, end_col in compact_ranges):
            continue
        # A folded footnote definition is also one atomic visible object. Its
        # source identifier is hidden behind ``[[Footnote N]]`` and must never
        # become an intermediate cursor stop.
        if (
            folded_visible_end is not None
            and source_col not in {0, folded_visible_end}
        ):
            continue

        try:
            display_col = processed.source_to_display(source_col)
        except Exception:
            continue
        display_col = max(0, min(display_col, len(positions) - 1))
        wrap_row, x = positions[display_col]
        candidate = (x, source_col)
        by_wrap.setdefault(wrap_row, []).append(candidate)

    # Source order is normally already visual order, but sorting makes the
    # boundary and nearest-x policies explicit even around transformed spans.
    frozen_by_wrap = {
        wrap_row: tuple(sorted(candidates, key=lambda item: (item[0], item[1])))
        for wrap_row, candidates in by_wrap.items()
    }
    return _store_bounded_visual_cache(cache, key, frozen_by_wrap)


def _normalize_visual_source_col(
    document, row, source_col, *, structural_body_col=None
):
    """Snap a source column to an explicit visible cursor boundary.

    ``structural_body_col`` lets startup/recovery normalization use the stable
    document layout before a real terminal width exists.  Interactive callers
    keep the ordinary width-aware gutter behavior by leaving it unset.
    """
    if not (0 <= row < document.line_count):
        return source_col
    source_line = document.lines[row]
    source_col = max(0, min(len(source_line), int(source_col)))
    if structural_body_col is None:
        structural_body_col = _hidden_structural_body_col(document, row)
    structural_body_col = max(0, min(len(source_line), int(structural_body_col)))
    source_col = max(source_col, structural_body_col)

    if (
        source_col > 0
        and source_line[source_col - 1:source_col]
        in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}
    ):
        source_col -= 1

    spans = tuple(_footnote_display_spans(document.text, row))
    for start_col, end_col, _label, _identifier, placeholder in spans:
        if placeholder:
            visible_end = (
                max(0, len(source_line) - 1)
                if source_line.endswith(FOOTNOTE_SENTINEL)
                else len(source_line)
            )
            if 0 < source_col < visible_end:
                return min(
                    (0, visible_end),
                    key=lambda boundary: (abs(boundary - source_col), boundary),
                )
        elif start_col < source_col < end_col:
            return min(
                (start_col, end_col),
                key=lambda boundary: (abs(boundary - source_col), boundary),
            )
    return source_col


def _source_visual_position(row, source_col, info):
    """Return (wrap row, x) for one explicit visible source position."""
    doc = text_area.buffer.document
    if not (0 <= row < doc.line_count):
        return None
    source_col = _normalize_visual_source_col(doc, row, source_col)

    get_processed = getattr(text_area.control, "_last_get_processed_line", None)
    if get_processed is None:
        return None
    try:
        processed = get_processed(row)
        display_col = processed.source_to_display(source_col)
        positions = _visual_display_positions(row, info)
    except Exception:
        return None
    if not positions:
        return None
    display_col = max(0, min(display_col, len(positions) - 1))
    return positions[display_col]


def _source_col_for_visual_position(row, wrap_row, preferred_x, info):
    """Return the navigable source column nearest ``preferred_x``."""
    by_wrap = _visual_source_candidates(row, info)
    if by_wrap is None:
        return None
    row_candidates = by_wrap.get(wrap_row, ())
    if not row_candidates:
        return None

    _x, source_col = min(
        row_candidates,
        key=lambda item: (abs(item[0] - preferred_x), item[1]),
    )
    return source_col

def _move_editor_cursor_visual_rows(delta):
    """Move the prose caret by one rendered screen row.

    Up/Down navigation is based on the visual soft-wrapped document, not the
    underlying logical source lines. The preferred x position is retained over
    repeated vertical moves so crossing a short rendered row and then a longer
    one returns to the writer's original visual column.
    """
    if delta == 0:
        return False

    buf = text_area.buffer
    doc = buf.document
    info = text_area.window.render_info
    if info is None or info.window_width <= 0 or doc.line_count <= 0:
        # Safe fallback before the first render.
        old = buf.cursor_position
        if delta < 0:
            buf.cursor_up(count=abs(delta))
        else:
            buf.cursor_down(count=abs(delta))
        return buf.cursor_position != old

    row = doc.cursor_position_row
    source_col = doc.cursor_position_col
    current_visual = _source_visual_position(row, source_col, info)
    heights, prefix = text_area.window._rendered_height_geometry(
        ui_content=info.ui_content, width=info.window_width
    )
    if current_visual is None or not heights or prefix is None:
        old = buf.cursor_position
        if delta < 0:
            buf.cursor_up(count=abs(delta))
        else:
            buf.cursor_down(count=abs(delta))
        return buf.cursor_position != old

    current_wrap, current_x = current_visual
    preferred_x = text_area.window._vertical_preferred_x
    if preferred_x is None:
        preferred_x = current_x
        text_area.window._vertical_preferred_x = preferred_x

    absolute_row = prefix[row] + current_wrap
    target_absolute = absolute_row + delta
    if target_absolute < 0 or target_absolute >= prefix[-1]:
        return False

    target_row = max(
        0,
        min(len(heights) - 1, bisect_right(prefix, target_absolute) - 1),
    )
    target_wrap = target_absolute - prefix[target_row]
    target_col = _source_col_for_visual_position(
        target_row, target_wrap, preferred_x, info
    )
    if target_col is None:
        return False

    target = doc.translate_row_col_to_index(target_row, target_col)
    if target == buf.cursor_position:
        return False

    # Keep the caret at its current screen row until it reaches a viewport edge;
    # after that, move the viewport by exactly the rendered rows necessary to
    # reveal the next visual cursor row. This avoids prompt_toolkit's wrapped
    # logical-line scroller pulling an entire paragraph into view at once.
    viewport_height = max(1, info.window_height)
    current_top = text_area.window._absolute_rendered_scroll(heights, prefix)
    desired_top = current_top
    if target_absolute < current_top:
        desired_top = target_absolute
    elif target_absolute >= current_top + viewport_height:
        desired_top = target_absolute - viewport_height + 1

    text_area.window.end_manual_scroll()
    text_area.window._set_keyboard_rendered_scroll(
        desired_top, heights, prefix, viewport_height
    )
    text_area.window._visual_vertical_move_in_progress = True
    try:
        buf.cursor_position = target
        # prompt_toolkit's logical preferred column must not leak into visual
        # movement if some other binding used cursor_up/cursor_down previously.
        buf.preferred_column = None
    finally:
        text_area.window._visual_vertical_move_in_progress = False
    get_app().invalidate()
    return True


def _toggle_extend_selection_mode():
    """Toggle Word-style keyboard selection while preserving any selection."""
    buf = text_area.buffer
    if state.extend_selection_mode:
        state.extend_selection_mode = False
        get_app().invalidate()
        return

    state.extend_selection_mode = True
    if buf.selection_state is None and buf.text:
        buf.start_selection(selection_type=SelectionType.CHARACTERS)
    if buf.selection_state is not None:
        # Keep prompt_toolkit's normal replace-selection behavior for typing,
        # while Carriage's F6-specific movement bindings prevent unmodified
        # navigation keys from cancelling the selection until F6 is pressed again.
        buf.selection_state.enter_shift_mode()
    get_app().invalidate()


def _extend_selection_to_position(target):
    """Move the active end of the F6 selection to an absolute source index."""
    buf = text_area.buffer
    target = max(0, min(len(buf.text), int(target)))
    target = _clamp_source_position_out_of_gutter(buf.text, target)
    original_position = buf.cursor_position

    if buf.selection_state is None:
        if not buf.text:
            return False
        buf.start_selection(selection_type=SelectionType.CHARACTERS)

    buf.cursor_position = target
    if buf.selection_state is not None:
        anchor = buf.selection_state.original_cursor_position
        if buf.cursor_position == anchor:
            buf.exit_selection()
    get_app().invalidate()
    return buf.cursor_position != original_position


def _move_editor_cursor_by_word(direction):
    """Move by a visible word boundary without entering hidden footnote source."""
    buf = text_area.buffer
    target = _word_navigation_target(buf.document, direction)
    if target is None or target == buf.cursor_position:
        return False
    text_area.window.end_manual_scroll()
    buf.cursor_position = target
    buf.preferred_column = None
    get_app().invalidate()
    return True


def _move_editor_selection_by_word(direction):
    """Extend an ordinary Shift/F6 selection by one visible word boundary."""
    buf = text_area.buffer
    target = _word_navigation_target(buf.document, direction)
    if target is None:
        return False

    if buf.selection_state is None:
        if not buf.text:
            return False
        buf.start_selection(selection_type=SelectionType.CHARACTERS)
    if buf.selection_state is not None:
        buf.selection_state.enter_shift_mode()

    original = buf.cursor_position
    buf.cursor_position = target
    if buf.selection_state is not None:
        anchor = buf.selection_state.original_cursor_position
        if buf.cursor_position == anchor:
            buf.exit_selection()
    get_app().invalidate()
    return buf.cursor_position != original


def _extend_selection_by_word(delta):
    """Extend the F6 selection one visible word boundary left or right."""
    return _move_editor_selection_by_word(delta)


def _visual_row_boundary_source_index(row, wrap_row, end=False, info=None):
    """Return one displayed-row boundary as an absolute source index.

    This is the shared boundary resolver for Home/End and prose-gutter clicks.
    ``row`` is a logical source row and ``wrap_row`` is the zero-based visual
    row within it. Hidden compact-footnote source and folded-object sentinels
    are excluded by the same candidate resolver used by Up/Down.
    """
    doc = text_area.buffer.document
    if not (0 <= row < doc.line_count):
        return None

    source_line = doc.lines[row]
    if info is None:
        info = text_area.window.render_info

    def physical_boundary():
        if end:
            source_col = len(source_line)
            if source_line.endswith((TABLE_SENTINEL, FOOTNOTE_SENTINEL)):
                source_col = max(0, source_col - 1)
        else:
            source_col = _hidden_structural_body_col(doc, row)
        return doc.translate_row_col_to_index(row, source_col)

    if info is None or info.window_width <= 0:
        return physical_boundary()

    by_wrap = _visual_source_candidates(row, info)
    if by_wrap is None:
        return physical_boundary()
    row_candidates = by_wrap.get(wrap_row, ())
    if not row_candidates:
        return physical_boundary()

    _x, source_col = row_candidates[-1] if end else row_candidates[0]
    return doc.translate_row_col_to_index(row, source_col)

def _visual_row_boundary_target(end=False):
    """Return the source index at the start/end of the current rendered row."""
    buf = text_area.buffer
    doc = buf.document
    row = doc.cursor_position_row
    info = text_area.window.render_info

    if info is None or info.window_width <= 0:
        amount = doc.get_end_of_line_position() if end else doc.get_start_of_line_position()
        target = doc.cursor_position + amount
        if end and doc.current_line.endswith((TABLE_SENTINEL, FOOTNOTE_SENTINEL)):
            target = max(doc.translate_row_col_to_index(row, 0), target - 1)
        return target

    current_visual = _source_visual_position(row, doc.cursor_position_col, info)
    if current_visual is None:
        amount = doc.get_end_of_line_position() if end else doc.get_start_of_line_position()
        return doc.cursor_position + amount

    return _visual_row_boundary_source_index(
        row, current_visual[0], end=end, info=info
    )


def _move_editor_cursor_to_visual_row_boundary(end=False):
    buf = text_area.buffer
    target = _visual_row_boundary_target(end=end)
    if target == buf.cursor_position:
        return False
    text_area.window.end_manual_scroll()
    buf.cursor_position = target
    buf.preferred_column = None
    get_app().invalidate()
    return True


def _move_editor_selection_to_visual_row_boundary(end=False):
    buf = text_area.buffer
    target = _visual_row_boundary_target(end=end)
    if buf.selection_state is None:
        if not buf.text:
            return False
        buf.start_selection(selection_type=SelectionType.CHARACTERS)
    if buf.selection_state is not None:
        buf.selection_state.enter_shift_mode()
    original = buf.cursor_position
    buf.cursor_position = target
    if buf.selection_state is not None:
        anchor = buf.selection_state.original_cursor_position
        if buf.cursor_position == anchor:
            buf.exit_selection()
    get_app().invalidate()
    return buf.cursor_position != original


def _extend_selection_to_line_boundary(end=False):
    """Compatibility name: F6 Home/End now use the rendered-row boundary."""
    return _move_editor_selection_to_visual_row_boundary(end=end)


def _move_editor_selection_visual_rows(delta):
    """Extend a Shift selection by one rendered row."""
    buf = text_area.buffer
    original_position = buf.cursor_position

    if buf.selection_state is None:
        if not buf.text:
            return
        buf.start_selection()
    if buf.selection_state is not None:
        buf.selection_state.enter_shift_mode()

    moved = _move_editor_cursor_visual_rows(delta)

    if buf.selection_state is not None:
        anchor = buf.selection_state.original_cursor_position
        if buf.cursor_position == anchor:
            buf.exit_selection()
        elif not moved and original_position == anchor:
            buf.exit_selection()


def _move_editor_selection_across_lines(delta):
    """Extend a Shift selection by one visible character left or right.

    prompt_toolkit's stock Shift+Left/Right bindings use raw source-character
    movement. Carriage has a slightly different visible-character model around
    folded-object sentinels and hidden list-continuation indentation, so selection
    movement must use the same cross-line path as ordinary Left/Right. This also
    makes Shift+Left at the start of a physical line select the newline and land
    at the end of the previous line, as users expect.
    """
    buf = text_area.buffer
    original_position = buf.cursor_position

    if buf.selection_state is None:
        if not buf.text:
            return
        buf.start_selection()

    # Mark the selection as Shift-driven so prompt_toolkit keeps its normal
    # replace-selection behavior for subsequent typing. Mouse-created
    # selections can safely enter the same mode when Shift+Arrow extends them.
    if buf.selection_state is not None:
        buf.selection_state.enter_shift_mode()

    _move_editor_cursor_across_lines(delta)

    if buf.selection_state is not None:
        anchor = buf.selection_state.original_cursor_position
        if buf.cursor_position == anchor:
            # Match prompt_toolkit's normal Shift-selection behavior: once the
            # moving end returns to the anchor, the selection is empty.
            buf.exit_selection()
        elif buf.cursor_position == original_position and original_position == anchor:
            # No movement was possible at the beginning/end of the document.
            buf.exit_selection()


def _move_editor_cursor_across_lines(delta):
    """Move one visible character left/right, crossing newline boundaries."""
    buf = text_area.buffer
    text = buf.text
    pos = buf.cursor_position
    doc = buf.document
    row = doc.cursor_position_row
    col = doc.cursor_position_col
    body_col = _hidden_structural_body_col(doc, row)

    # Hidden structural source is never ordinary cursor space. If an old
    # recovery/undo position or an indirect operation somehow lands there,
    # normalize it before interpreting the requested movement. At the visible
    # left edge of a guttered line, Left must still cross the newline normally:
    # skip the hidden prefix as a unit and land at the previous line's visible
    # end rather than stopping or exposing the structural Markdown.
    if col < body_col:
        buf.cursor_position = doc.translate_row_col_to_index(row, body_col)
        return
    if delta < 0 and body_col > 0 and col == body_col:
        if row <= 0:
            return
        line_start = doc.translate_row_col_to_index(row, 0)
        target = max(0, line_start - 1)
        # Folded-object sentinels are source-only; if the previous line ends in
        # one, land at its visible end rather than on the invisible marker.
        while target > 0 and text[target - 1] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
            target -= 1
        buf.cursor_position = _clamp_source_position_out_of_gutter(text, target)
        return

    folded_placeholder = _folded_placeholder_at_cursor(doc)
    if folded_placeholder is not None:
        # A folded object is one visible navigation unit. Its trailing sentinel
        # is a source-only implementation marker and must never consume a key.
        # The canonical visible end is immediately *before* that sentinel.
        line = doc.current_line
        visible_end = len(line)
        if line.endswith((TABLE_SENTINEL, FOOTNOTE_SENTINEL)):
            visible_end -= 1

        if delta > 0 and col < visible_end:
            buf.cursor_position = doc.translate_row_col_to_index(row, visible_end)
            return
        if delta < 0 and col > 0:
            buf.cursor_position = doc.translate_row_col_to_index(row, 0)
            return
        # At the visible right edge, fall through to the generic path below. It
        # skips the sentinel first and then crosses the newline in this same
        # keypress, taking the caret directly to the next visible line.

    footnote_span = _footnote_source_span_at_cursor(doc, direction=delta)
    if footnote_span is not None:
        start_col, end_col, _identifier = footnote_span
        if delta > 0 and col < end_col:
            buf.cursor_position = doc.translate_row_col_to_index(row, end_col)
            return
        if delta < 0 and col > start_col:
            buf.cursor_position = doc.translate_row_col_to_index(row, start_col)
            return

    if delta > 0:
        # Folded-object sentinels are internal zero-width markers. Treat the
        # position immediately before one as the visible line end, then skip the
        # marker without consuming a cursor step.
        current_line = doc.current_line
        visible_line_end = len(current_line)
        if current_line.endswith((TABLE_SENTINEL, FOOTNOTE_SENTINEL)):
            visible_line_end -= 1
        at_line_end = doc.cursor_position_col >= visible_line_end
        next_body_col = (
            _hidden_structural_body_col(doc, row + 1)
            if at_line_end and row + 1 < doc.line_count
            else 0
        )
        while pos < len(text) and text[pos] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
            pos += 1
        if pos < len(text):
            pos += 1
        if next_body_col:
            pos = min(len(text), pos + next_body_col)
        while pos < len(text) and text[pos] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
            pos += 1
    elif delta < 0:
        while pos > 0 and text[pos - 1] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
            pos -= 1
        if pos > 0:
            pos -= 1
        while pos > 0 and text[pos - 1] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
            pos -= 1

    buf.cursor_position = _clamp_source_position_out_of_gutter(text, pos)


@kb.add("s-up", filter=editor_focused)
def _(event):
    _move_editor_selection_visual_rows(-1)


@kb.add("s-down", filter=editor_focused)
def _(event):
    _move_editor_selection_visual_rows(1)


@kb.add("up", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _move_editor_selection_visual_rows(-1)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_visual_rows(-1)


@kb.add("down", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _move_editor_selection_visual_rows(1)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_visual_rows(1)


@kb.add("s-right", filter=editor_focused)
def _(event):
    _move_editor_selection_across_lines(1)


@kb.add("s-left", filter=editor_focused)
def _(event):
    _move_editor_selection_across_lines(-1)


@kb.add("right", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _move_editor_selection_across_lines(1)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_across_lines(1)


@kb.add("left", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _move_editor_selection_across_lines(-1)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_across_lines(-1)



@kb.add("c-left", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _extend_selection_by_word(-1)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_by_word(-1)


@kb.add("c-right", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _extend_selection_by_word(1)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_by_word(1)


@kb.add("c-s-left", filter=editor_focused)
def _(event):
    _move_editor_selection_by_word(-1)


@kb.add("c-s-right", filter=editor_focused)
def _(event):
    _move_editor_selection_by_word(1)


@kb.add("home", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _extend_selection_to_line_boundary(end=False)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_to_visual_row_boundary(end=False)


@kb.add("end", filter=editor_focused)
def _(event):
    if state.extend_selection_mode:
        _extend_selection_to_line_boundary(end=True)
    else:
        event.current_buffer.exit_selection()
        _move_editor_cursor_to_visual_row_boundary(end=True)


@kb.add("s-home", filter=editor_focused)
def _(event):
    _move_editor_selection_to_visual_row_boundary(end=False)


@kb.add("s-end", filter=editor_focused)
def _(event):
    _move_editor_selection_to_visual_row_boundary(end=True)


@kb.add("c-s", filter=table_editor_active)
def _(event):
    _save_table_editor()


@kb.add("f1", filter=no_dialog_open)
def _(event):
    do_show_help()


@kb.add("f10", filter=no_dialog_open)
@kb.add("c-space", filter=no_dialog_open)
def _(event):
    event.app.layout.focus(menu_container.window)


def _select_top_level_menu(index):
    """Select one top-level menu and reset any open submenu selection."""
    if 0 <= index < len(menu_container.menu_items):
        menu_container.selected_menu = [index]
        get_app().invalidate()


for _key, _index in (
    ("1", 0),
    ("2", 1),
    ("3", 2),
    ("4", 3),
    ("5", 4),
    ("6", 5),
):
    kb.add(_key, filter=menu_focused)(
        lambda event, index=_index: _select_top_level_menu(index)
    )


@kb.add("escape", filter=menu_focused)
def _(event):
    event.app.layout.focus(text_area)


@kb.add("escape", filter=dialog_open)
def _(event):
    close_dialog()


# Everforest (hard contrast, dark) palette - see
# https://github.com/sainnhe/everforest/blob/master/palette.md
EF_BG_DIM = "#1E2326"
EF_BG0 = "#272E33"  # dark text on green highlights (menu selection, focused button)
EF_BG2 = "#374145"  # popup menu / floating window background
EF_BG3 = "#414B50"  # borders, special keys
EF_BG4 = "#495156"  # window split separators
EF_FG = "#D3C6AA"  # default foreground
EF_GREEN = "#A7C080"  # statusline1 - menu selection background
EF_YELLOW = "#DBBC7F"  # unsaved-changes indicator / bold emphasis
EF_AQUA = "#83C092"  # italic emphasis
EF_GREY1 = "#859289"  # comments, UI borders, status line text

style = Style.from_dict(
    {
        # Leave the editor canvas transparent so the terminal's own background
        # remains visible. The menu and status bars use opaque UI chrome to
        # separate navigation/status information from the prose area.
        "": EF_FG,
        "editor": EF_FG,
        "markdown.heading": f"{EF_GREEN} bold",
        "markdown.bold": f"{EF_YELLOW} bold",
        "markdown.italic": f"{EF_AQUA} italic",
        "markdown.bold-italic": f"{EF_YELLOW} bold italic",
        "markdown.table-ref": f"{EF_AQUA} bold",
        "markdown.footnote-ref": f"{EF_AQUA} bold",
        "markdown.hard-break": f"{EF_GREY1} bold",
        "markdown.blockquote-gutter": EF_GREY1,
        # Rendered scrollbar: subdued Everforest chrome. Keep the track close
        # to the surrounding UI and let the thumb/arrows remain legible without
        # competing with the prose area.
        "scrollbar": f"bg:{EF_BG3}",
        "scrollbar.background": f"bg:{EF_BG3}",
        "scrollbar.button": f"bg:{EF_GREY1}",
        "scrollbar.arrow": f"bg:{EF_BG3} {EF_GREY1}",
        "footnote.editor": f"bg:{EF_BG3} {EF_FG}",
        "table.border": EF_GREY1,
        "table.header": f"{EF_GREEN} bold",
        "table.cell": EF_FG,
        "table.cell.selected": f"bg:{EF_GREEN} {EF_BG0} bold",
        "table.cell-editor": f"bg:{EF_BG3} {EF_FG}",
        "table.hint": EF_GREY1,
        "divider": EF_BG4,
        "status": f"bg:{EF_BG3} {EF_FG}",
        # The title bar remains on the transparent canvas; the menu and status
        # bars form matching opaque strips around the editing area.
        "title-bar": EF_FG,
        "title-bar.modified": f"{EF_YELLOW} bold",
        "menu-bar": f"bg:{EF_BG3} {EF_FG} bold",
        "menu-bar.selected-item": f"bg:{EF_GREEN} {EF_BG0} bold",
        "menu": f"bg:{EF_BG2} {EF_FG}",
        "menu-border": f"bg:{EF_BG2} {EF_GREY1}",
        "shadow": f"bg:{EF_BG_DIM}",
        # Dialogs (Open/Save/messages/confirmations).
        "dialog": f"bg:{EF_BG2} {EF_FG}",
        "dialog.body": f"bg:{EF_BG2} {EF_FG}",
        "frame.border": f"bg:{EF_BG2} {EF_GREY1}",
        "frame.label": f"bg:{EF_BG2} {EF_GREEN} bold",
        "button": f"bg:{EF_BG3} {EF_FG}",
        "button.focused": f"bg:{EF_GREEN} {EF_BG0} bold",
        # Dedicated class for dialog input fields (Open/Save/export paths),
        # rather than styling the built-in "text-area" class directly -
        # every TextArea (including the main editor) carries that tag
        # automatically, so styling it there would paint an opaque
        # background behind the editor too and undo the transparency above.
        # This also sidesteps prompt_toolkit's own built-in
        # "dialog.body text-area" rule, which defaults to a low-contrast
        # light grey background there.
        "input-field": f"bg:{EF_BG3} {EF_FG}",
        "section-nav": f"bg:{EF_BG2} {EF_FG}",
        "section-nav.selected": f"bg:{EF_GREEN} {EF_BG0} bold",
        "section-nav.empty": f"bg:{EF_BG2} {EF_GREY1}",
        "help-text": f"bg:{EF_BG2} {EF_FG}",
    }
)

application = None


def _create_application():
    """Construct the interactive prompt_toolkit application after CLI parsing."""
    app = Application(
        layout=layout,
        key_bindings=kb,
        style=style,
        clipboard=CarriageClipboard(),
        mouse_support=MOUSE_ENABLED,
        full_screen=True,
        # Without this, prompt_toolkit's default color depth is 256-color, not
        # true 24-bit - our exact hex values would get approximated to the
        # nearest of 256 colors, which can quietly collapse contrast between
        # similar tones. Kitty (and virtually every modern terminal) supports
        # real 24-bit color, so ask for it explicitly.
        color_depth=ColorDepth.DEPTH_24_BIT,
        cursor=SimpleCursorShapeConfig(cursor_shape=CursorShape.BEAM),
    )
    # VT100 terminals encode Alt/meta keys and special-key sequences with an
    # initial Escape byte. prompt_toolkit therefore has two relevant waits: the
    # VT100 input flush (ttimeoutlen) and the ambiguous key-binding prefix wait
    # (timeoutlen). The defaults make a lone Esc noticeably sluggish, especially
    # in Find/Replace where Esc is also the prefix for Alt+C/W/A. Keep both waits
    # short so Esc closes modes promptly while complete escape-prefixed sequences
    # still resolve normally.
    app.ttimeoutlen = 0.1
    app.timeoutlen = 0.1
    return app


def _format_config_startup_warning(diagnostics):
    path = _config_path()
    details = "\n".join(f"- {message}" for message in diagnostics)
    return (
        f"Carriage found configuration problems in:\n{path}\n\n"
        f"{details}\n\nValid settings were kept where possible. "
        "Ignored or unreadable settings use Carriage defaults."
    )


def _start_background_tasks(
    startup_error=None,
    startup_large_file=None,
    recovery_source_path=None,
    offer_any_recovery=False,
    config_diagnostics=None,
):
    application.create_background_task(_working_state_loop())

    def offer_recovery_after_startup(path=None):
        if path is not None:
            _offer_stale_recovery(path)
        elif offer_any_recovery:
            _offer_stale_recovery()

    def load_large_startup_file(path):
        try:
            content, disk_snapshot = _read_utf8_file_with_snapshot(
                path, allow_large=True
            )
        except (OSError, UnicodeError) as e:
            show_message("Error opening file", f"{path}\n\n{e}")
            return
        _install_open_document(path, content, disk_snapshot)
        offer_recovery_after_startup(path)

    def continue_startup():
        # Preserve the pre-v1.139 startup precedence: a requested file-open
        # error is shown instead of offering recovery for that launch. A large
        # command-line file is the one exception: defer its allocation until
        # the TUI exists so the user can explicitly approve the load.
        if startup_error is not None:
            title, message = startup_error
            show_message(title, message)
        elif startup_large_file is not None:
            path, size_bytes = startup_large_file
            confirm(
                "Large file",
                _large_file_prompt_text(path, size_bytes),
                lambda: load_large_startup_file(path),
            )
        elif recovery_source_path is not None:
            offer_recovery_after_startup(recovery_source_path)
        else:
            offer_recovery_after_startup()

    diagnostics = list(config_diagnostics or ())
    if diagnostics:
        show_message(
            "Configuration warning",
            _format_config_startup_warning(diagnostics),
            on_close=continue_startup,
        )
    else:
        continue_startup()



def main(argv=None):
    global application

    # argparse handles --help/--version by exiting here, before Carriage
    # constructs an Application or touches the terminal. This keeps CLI
    # metadata commands clean in pipes, package managers, and non-TTY shells.
    args = _parse_command_line(argv)

    try:
        _check_prompt_toolkit_private_contract()
    except RuntimeError as e:
        print(f"carriage: {e}", file=sys.stderr)
        return 2

    startup_error = None
    startup_large_file = None
    config_diagnostics = list(_CONFIG_DIAGNOSTICS)
    config_creation_warning = _ensure_config_file()
    if config_creation_warning is not None:
        config_diagnostics.append(config_creation_warning)

    if args.file is not None:
        path = os.path.expanduser(args.file)
        if os.path.exists(path):
            try:
                content, disk_snapshot = _read_utf8_file_with_snapshot(path)
            except _LargeFileConfirmationRequired as e:
                # Defer unusually large command-line files until the TUI exists
                # so Carriage can ask before allocating the full document.
                startup_large_file = (path, e.size_bytes)
            except (OSError, UnicodeError) as e:
                # Start the editor rather than crashing before the UI exists;
                # display the error as soon as the application is running.
                startup_error = ("Error opening file", f"{path}\n\n{e}")
            else:
                _install_open_document(path, content, disk_snapshot)
        else:
            state.path = path  # new file at this path on first save
            state.disk_snapshot = _MISSING_DISK_SNAPSHOT

    _reset_working_state_tracking()
    application = _create_application()
    application.run(
        pre_run=lambda: _start_background_tasks(
            startup_error,
            startup_large_file=startup_large_file,
            recovery_source_path=(
                state.path
                if args.file is not None and startup_large_file is None
                else None
            ),
            offer_any_recovery=(args.file is None),
            config_diagnostics=config_diagnostics,
        )
    )


if __name__ == "__main__":
    raise SystemExit(main())
