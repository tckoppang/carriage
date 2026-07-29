#!/usr/bin/env python3
"""
Carriage - A prose-first Markdown editor for the terminal.

Carriage is designed primarily for writing and revising prose in Markdown files.
It provides a full-screen prompt_toolkit interface with mouse support, menus,
keyboard shortcuts, autosave, spell checking, and Pandoc export. F10 or
Ctrl+Space activates the menu bar; while it is active, number keys 1 through 7
jump directly among the top-level menus.
A dedicated Go menu provides document and section navigation without changing
the text.

While typing, ordinary paragraph prose wraps automatically at 80 columns.
Explicit Markdown hard breaks are preserved, and long tokens such as URLs are
left intact rather than split. Text that looks structural or ambiguous is left
alone instead of being reformatted speculatively.

Format > Reflow Document (Ctrl+J) cleans up prose across the document. It
rewraps ordinary paragraphs, preserves explicit hard breaks, and handles only
simple flat lists and simple single-level blockquotes. Code, tables, YAML,
raw block HTML, complex containers, delimiter-style blocks, and other
structural-looking regions are treated as opaque and copied unchanged.

File operations include New, Open, Save, and Save As. Saves and autosaves use
a temporary file followed by atomic replacement so a failed write does not
truncate the existing file. Autosave runs every 30 seconds for named files;
modified untitled documents receive a private crash-recovery snapshot on the
same interval. Background writes pause while aspell or a modal dialog is active.

The Tools menu can hand a saved document to aspell in Markdown mode and reload
the edited file afterward. The Export menu sends the current buffer to Pandoc
for PDF, DOCX, ODT, HTML, plain-text, or custom-command output.

The interface uses an Everforest dark palette, a transparent editor canvas,
mouse-enabled scrolling, and modal dialogs with safe nested error handling. On
wide terminals, the 80-column prose area is centered while the scrollbar stays
flush against the far-right edge; narrow terminals use the available width.
Headings, bold emphasis, and italic emphasis receive lightweight syntax
highlighting; highlighting is visual only and never changes document text.

Ordinary Markdown pipe tables are folded in the prose view to compact
references such as [[Table 1]]. The Markdown file itself still contains a
plain-text pipe table. Tools > Insert Table creates a supported table, and
pressing Tab while the cursor is on a folded reference opens a dedicated table
editor whose cells wrap visually without inserting line breaks into the file.
The table editor can insert or delete data rows and columns while preserving a
rectangular table and a dedicated header row. It opens in navigation mode, where
the arrow keys move among cells. Enter switches the selected cell into edit
mode; Enter again commits that cell and returns to navigation mode.

Requires:
  pip install prompt_toolkit --break-system-packages

Optional:
  pandoc, for document export.
  aspell and an appropriate dictionary package, for spell checking.

Usage:
  ./carriage_v1.06.py [file.md]
"""

import asyncio
import copy
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import textwrap
import stat
from dataclasses import dataclass, field

from prompt_toolkit.application import Application
from prompt_toolkit.cursor_shapes import CursorShape, SimpleCursorShapeConfig
from prompt_toolkit.output.color_depth import ColorDepth
from prompt_toolkit.application.current import get_app
from prompt_toolkit.document import Document
from prompt_toolkit.filters import Condition
from prompt_toolkit.filters.app import buffer_has_focus
from prompt_toolkit.key_binding import KeyBindings
from prompt_toolkit.lexers import Lexer
from prompt_toolkit.layout.containers import (
    Float,
    FloatContainer,
    HSplit,
    ConditionalContainer,
    Window,
    WindowAlign,
)
from prompt_toolkit.layout.controls import BufferControl, FormattedTextControl
from prompt_toolkit.layout.dimension import D
from prompt_toolkit.layout.layout import Layout
from prompt_toolkit.layout.margins import Margin
from prompt_toolkit.mouse_events import MouseButton, MouseEventType
from prompt_toolkit.styles import Style
from prompt_toolkit.utils import get_cwidth
from prompt_toolkit.widgets import (
    Button,
    Dialog,
    Label,
    MenuContainer,
    MenuItem,
    TextArea,
)

APP_NAME = "Carriage"
APP_VERSION = "1.06"

WRAP_COLUMN = 80
TAB_WIDTH = 4
AUTOSAVE_INTERVAL_SECONDS = 30
RECOVERY_FORMAT_VERSION = 1
TABLE_SENTINEL = "\u2063"  # zero-width INVISIBLE SEPARATOR; never written to disk
TABLE_PLACEHOLDER_RE = re.compile(rf"^\[\[Table (\d+)\]\]{TABLE_SENTINEL}$")
MAX_TABLE_EDITOR_COLUMNS = 6


@dataclass
class TableData:
    """In-memory representation of one folded pipe table."""

    headers: list[str]
    rows: list[list[str]]
    alignments: list[str] = field(default_factory=list)
    original_lines: list[str] | None = None
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
    grid_control: object | None = None
    cell_label: object | None = None
    mode_label: object | None = None
    grid_window: object | None = None
    dialog_float: object | None = None
    editing: bool = False
    # Which edge of the selected row should be kept visible in the table
    # viewport. Moving downward anchors the row's bottom; moving upward anchors
    # its top. This matters for prose-heavy rows that span several screen lines.
    scroll_anchor: str = "top"


# ---------------------------------------------------------------------------
# Editor state
# ---------------------------------------------------------------------------

class EditorState:
    def __init__(self):
        self.path = None
        self.auto_wrap = True
        self.auto_save = True
        self.saved_text = ""
        # Fingerprint of the exact on-disk bytes last opened or successfully
        # written by Carriage. A save must still see this same version before
        # it is allowed to replace the file.
        self.disk_snapshot = None
        # Avoid repeatedly opening the same autosave-conflict warning every
        # 30 seconds while an externally changed file remains unresolved.
        self.autosave_conflict = False
        # True while an external interactive process (aspell) has the file
        # open on disk - autosave pauses during this window to avoid racing
        # with whatever that process writes back.
        self.external_process_running = False
        # Hidden crash-recovery state for an untitled document. Recovery is
        # deliberately separate from the user's document pathname and is
        # removed after a successful Save, New, Open, or clean discard/quit.
        self.recovery_path = None
        self.recovery_error = False
        self.tables = {}

    def is_modified(self, current_text):
        try:
            source_text = _materialize_tables(current_text)
        except ValueError:
            return True
        return source_text != self.saved_text


state = EditorState()


def _center_padding_widths(columns):
    """Return padding that centers an honest 80-column prose viewport.

    The scrollbar owns the far-right terminal column and is excluded from the
    centering calculation. On wide terminals, the prose area is exactly
    WRAP_COLUMN cells wide. Narrow terminals use all available space to the
    left of the scrollbar.
    """
    scrollbar_width = 1
    available = max(1, columns - scrollbar_width)
    prose_width = min(WRAP_COLUMN, available)
    spare = max(0, available - prose_width)
    left = spare // 2
    right = spare - left
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


class ScrollableWindow(Window):
    """
    Window subclass that makes TextArea's right-margin scrollbar clickable
    and draggable, and keeps mouse-wheel scrolling usable around very tall
    soft-wrapped logical lines.

    prompt_toolkit reports content_height in logical input lines, not rendered
    screen rows. Its stock wheel logic can therefore decide that a document
    cannot scroll even when one logical line (for example, a wide Markdown
    table row) wraps across more rows than the viewport. For lines taller than
    the viewport, this class advances vertical_scroll_2 through the wrapped
    portions and moves the cursor far enough into the line that the normal
    "keep cursor visible" pass does not immediately clamp that scroll away.

    The scrollbar track also weights logical lines by their rendered height,
    so clicking or dragging near a very tall wrapped line lands proportionally
    within that line instead of treating it as a single row.
    """

    on_scrollbar_interact = None

    def _line_height(self, row):
        info = self.render_info
        if info is None or info.window_width <= 0:
            return 1
        return max(1, info.get_height_for_line(row))

    def _cursor_col_for_wrapped_row(self, row, wrapped_row):
        """Return a buffer column that renders on or after wrapped_row."""
        info = self.render_info
        buffer = getattr(self.content, "buffer", None)
        if info is None or buffer is None or info.window_width <= 0:
            return 0

        line = buffer.document.lines[row]
        if wrapped_row <= 0 or not line:
            return 0

        target_height = wrapped_row + 1
        lo, hi = 0, len(line)
        while lo < hi:
            mid = (lo + hi) // 2
            height = info.ui_content.get_height_for_line(
                row,
                info.window_width,
                self.get_line_prefix,
                slice_stop=mid,
            )
            if height >= target_height:
                hi = mid
            else:
                lo = mid + 1
        return lo

    def _place_cursor_for_scroll(self, row, wrapped_row=0):
        buffer = getattr(self.content, "buffer", None)
        if buffer is None:
            return
        doc = buffer.document
        row = max(0, min(doc.line_count - 1, row))
        col = self._cursor_col_for_wrapped_row(row, wrapped_row)
        buffer.cursor_position = doc.translate_row_col_to_index(row, col)

    def _scroll_up(self):
        info = self.render_info
        buffer = getattr(self.content, "buffer", None)
        if info is None or buffer is None:
            return

        # If we're already partway through a single line taller than the
        # viewport, reveal one earlier rendered row inside that line.
        if self.vertical_scroll_2 > 0:
            self.vertical_scroll_2 -= 1
            self._place_cursor_for_scroll(
                self.vertical_scroll, self.vertical_scroll_2
            )
            return

        if self.vertical_scroll <= 0:
            return

        # Decrement from vertical_scroll's OWN current value, not from the
        # cursor's row: the cursor is not required to sit at the viewport's
        # top edge (there can be a large, perfectly normal gap between them),
        # and jumping vertical_scroll to match the cursor conflicts with
        # prompt_toolkit's own scroll-past-the-end clamp whenever that gap
        # exists, silently rejecting the jump - which is what reintroduced
        # stuck scrolling here. A plain decrement never overshoots.
        previous_row = self.vertical_scroll - 1
        previous_height = self._line_height(previous_row)
        self.vertical_scroll = previous_row
        if previous_height > info.window_height:
            # Enter a tall preceding line at its last valid viewport offset.
            self.vertical_scroll_2 = max(0, previous_height - info.window_height)
        else:
            self.vertical_scroll_2 = 0
        self._place_cursor_for_scroll(previous_row, self.vertical_scroll_2)

    def _scroll_down(self):
        info = self.render_info
        buffer = getattr(self.content, "buffer", None)
        if info is None or buffer is None:
            return

        # Operate on vertical_scroll's own current value, not the cursor's
        # row, for the same reason as _scroll_up: the cursor can sit well
        # within the viewport without being at its bottom edge, and until it
        # reaches that edge, moving only the cursor produces zero visible
        # change - the first several wheel ticks from a freshly opened file
        # would silently do nothing.
        current_height = self._line_height(self.vertical_scroll)

        if current_height > info.window_height:
            max_inside_offset = max(0, current_height - info.window_height)
            if self.vertical_scroll_2 < max_inside_offset:
                self.vertical_scroll_2 += 1
                self._place_cursor_for_scroll(self.vertical_scroll, self.vertical_scroll_2)
                return

        if self.vertical_scroll >= buffer.document.line_count - 1:
            return

        next_row = self.vertical_scroll + 1
        self.vertical_scroll = next_row
        self.vertical_scroll_2 = 0
        self._place_cursor_for_scroll(next_row)

    def _write_to_screen_at_index(
        self, screen, mouse_handlers, write_position, parent_style, erase_bg
    ):
        super()._write_to_screen_at_index(
            screen, mouse_handlers, write_position, parent_style, erase_bg
        )

        if self.on_scrollbar_interact is None or not self.right_margins:
            return

        # The prose-centering spacer is also a right margin, but only the
        # final margin is the actual scrollbar. Keep mouse handling pinned to
        # that far-right column instead of making the empty spacer clickable.
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


def _scrollbar_rendered_heights():
    """Return rendered heights for each logical line from the last render."""
    info = text_area.window.render_info
    if info is None:
        return None
    return [max(1, info.get_height_for_line(i)) for i in range(info.ui_content.line_count)]


def _move_to_rendered_position(rendered_row):
    """Move to the logical/wrapped position nearest an absolute rendered row."""
    info = text_area.window.render_info
    heights = _scrollbar_rendered_heights()
    if info is None or not heights:
        return

    total_height = sum(heights)
    rendered_row = max(0, min(total_height - 1, int(rendered_row)))

    accumulated = 0
    target_row = len(heights) - 1
    wrapped_offset = 0
    for row, height in enumerate(heights):
        if rendered_row < accumulated + height:
            target_row = row
            wrapped_offset = rendered_row - accumulated
            break
        accumulated += height

    # prompt_toolkit only supports vertical_scroll_2 while the cursor line is
    # taller than the viewport. Clamp track clicks inside shorter wrapped lines
    # to the start of the logical line; tall lines can be entered proportionally.
    if heights[target_row] <= info.window_height:
        wrapped_offset = 0
    else:
        wrapped_offset = min(
            wrapped_offset, max(0, heights[target_row] - info.window_height)
        )

    text_area.window.vertical_scroll = target_row
    text_area.window.vertical_scroll_2 = wrapped_offset
    text_area.window._place_cursor_for_scroll(target_row, wrapped_offset)


def _on_scrollbar_interact(row_in_window, window_height):
    # TextArea's scrollbar has arrow rows at the top and bottom; clicks there
    # move by a few rendered rows. The track maps proportionally across the
    # document's rendered height, so tall soft-wrapped lines get proper weight.
    heights = _scrollbar_rendered_heights()
    if not heights:
        return

    info = text_area.window.render_info
    total_height = sum(heights)
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
# visual only: ATX/Setext headings and inline bold/italic emphasis get styled,
# while the underlying buffer remains untouched. Fenced code blocks are left
# unhighlighted so prose markers inside code do not masquerade as Markdown.
_HIGHLIGHT_ATX_RE = re.compile(r"^\s{0,3}#{1,6}(?:\s|$)")
_HIGHLIGHT_SETEXT_RE = re.compile(r"^\s{0,3}(?:=+|-+)\s*$")
_HIGHLIGHT_FENCE_RE = re.compile(r"^\s{0,3}(`{3,}|~{3,})")

# Order matters: triple emphasis before bold, then italic. The patterns are
# intentionally conservative and line-local; Carriage is not trying to be a
# complete Markdown parser merely to color prose.
_HIGHLIGHT_INLINE_RE = re.compile(
    r"(?P<strong_em>"
    r"(?<!\\)\*\*\*(?=\S).+?(?<=\S)(?<!\\)\*\*\*"
    r"|(?<!\w)___(?=\S).+?(?<=\S)___(?!\w)"
    r")"
    r"|(?P<strong>"
    r"(?<!\\)\*\*(?=\S).+?(?<=\S)(?<!\\)\*\*"
    r"|(?<!\w)__(?=\S).+?(?<=\S)__(?!\w)"
    r")"
    r"|(?P<em>"
    r"(?<![\\*])\*(?!\*)(?=\S).+?(?<=\S)(?<!\\)\*(?!\*)"
    r"|(?<![\w\\])_(?!_)(?=\S).+?(?<=\S)_(?![\w_])"
    r")"
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


def _highlight_inline_markdown(line):
    """Return prompt_toolkit fragments for bold/italic spans in one line."""
    fragments = []
    pos = 0

    for match in _HIGHLIGHT_INLINE_RE.finditer(line):
        if match.start() > pos:
            fragments.append(("", line[pos:match.start()]))

        if match.lastgroup == "strong_em":
            style_name = "class:markdown.bold-italic"
        elif match.lastgroup == "strong":
            style_name = "class:markdown.bold"
        else:
            style_name = "class:markdown.italic"

        fragments.append((style_name, match.group(0)))
        pos = match.end()

    if pos < len(line):
        fragments.append(("", line[pos:]))

    return fragments or [("", line)]


class ProseMarkdownLexer(Lexer):
    """Minimal, non-destructive highlighting for prose-oriented Markdown."""

    def lex_document(self, document):
        lines = document.lines
        fenced_lines = _highlight_fenced_lines(lines)
        setext_text_lines = {
            row - 1
            for row, line in enumerate(lines)
            if row > 0
            and row not in fenced_lines
            and _HIGHLIGHT_SETEXT_RE.match(line)
            and lines[row - 1].strip()
        }
        setext_underline_lines = {
            row
            for row, line in enumerate(lines)
            if row > 0
            and row not in fenced_lines
            and _HIGHLIGHT_SETEXT_RE.match(line)
            and lines[row - 1].strip()
        }

        def get_line(lineno):
            if lineno < 0 or lineno >= len(lines):
                return []

            line = lines[lineno]
            if lineno in fenced_lines:
                return [("", line)]

            if TABLE_PLACEHOLDER_RE.match(line):
                return [("class:markdown.table-ref", line)]

            if (
                _HIGHLIGHT_ATX_RE.match(line)
                or lineno in setext_text_lines
                or lineno in setext_underline_lines
            ):
                return [("class:markdown.heading", line)]

            return _highlight_inline_markdown(line)

        return get_line


class FullWidthSafeBufferControl(BufferControl):
    """Avoid phantom blank rows after exactly full-width logical lines.

    prompt_toolkit appends one synthetic space to every BufferControl line so
    the terminal cursor can occupy the position just after the final character.
    With soft wrapping enabled, an 80-character line in an 80-column window
    therefore becomes 81 display cells and the synthetic cell wraps onto an
    otherwise blank screen row.

    Keep prompt_toolkit's normal behavior except when that synthetic cell is
    the *only* thing that would create another wrapped row. In that case, omit
    the cell for rendering. If the editing cursor is at the end of that line,
    display it on the final real character instead. Buffer positions and file
    contents are unchanged.
    """

    def create_content(self, width, height, preview_search=False):
        content = super().create_content(width, height, preview_search)
        if width <= 0:
            return content

        original_get_line = content.get_line
        cache = {}

        def adjusted_line(row):
            if row in cache:
                return cache[row]

            fragments = original_get_line(row)
            if not fragments or fragments[-1][:2] != ("", " "):
                cache[row] = fragments
                return fragments

            real_fragments = fragments[:-1]
            real_width = sum(get_cwidth(fragment[1]) for fragment in real_fragments)

            # Only suppress the synthetic cursor cell when it alone would
            # create a new wrapped row. Empty lines keep the normal cursor cell.
            if real_width > 0 and real_width % width == 0:
                fragments = real_fragments

            cache[row] = fragments
            return fragments

        content.get_line = adjusted_line

        cursor = content.cursor_position
        cursor_line = original_get_line(cursor.y)
        if cursor_line and cursor_line[-1][:2] == ("", " "):
            real_fragments = cursor_line[:-1]
            real_width = sum(get_cwidth(fragment[1]) for fragment in real_fragments)
            real_char_count = sum(len(fragment[1]) for fragment in real_fragments)
            if (
                real_width > 0
                and real_width % width == 0
                and cursor.x == real_char_count
            ):
                content.cursor_position = cursor._replace(x=max(0, cursor.x - 1))

        return content


text_area = TextArea(
    text="",
    lexer=ProseMarkdownLexer(),
    wrap_lines=True,
    scrollbar=True,
    style="class:editor",
)
text_area.control.__class__ = FullWidthSafeBufferControl
text_area.window.__class__ = ScrollableWindow
text_area.window.on_scrollbar_interact = _on_scrollbar_interact

# Keep the visible prose area exactly 80 columns on wide terminals. The custom
# BufferControl above prevents prompt_toolkit's synthetic end-of-line cursor
# cell from manufacturing a blank wrapped row when a physical line fills all
# 80 columns. The TextArea window remains full-width so the scrollbar stays
# flush against the terminal's far-right edge.
_scrollbar_margin = text_area.window.right_margins[-1]
text_area.window.left_margins = [CenterPaddingMargin("left")]
text_area.window.right_margins = [
    CenterPaddingMargin("right"),
    _scrollbar_margin,
]

floats = []
dialog_stack = []
current_float = None
current_table_editor = None


# ---------------------------------------------------------------------------
# Dialog helpers
# ---------------------------------------------------------------------------

def show_dialog(dialog, focus=None):
    """Show a modal dialog, preserving any dialog already underneath it."""
    global current_float
    dialog_float = Float(content=dialog)
    focus_target = focus if focus is not None else dialog
    floats.append(dialog_float)
    dialog_stack.append((dialog_float, focus_target))
    current_float = dialog_float

    app = get_app()
    app.layout.focus(focus_target)
    app.invalidate()
    return dialog_float


def close_dialog():
    """Close the top dialog and restore focus to the dialog beneath it."""
    global current_float, current_table_editor

    closed_float = None
    if dialog_stack:
        dialog_float, _ = dialog_stack.pop()
        closed_float = dialog_float
        if dialog_float in floats:
            floats.remove(dialog_float)

    if (
        current_table_editor is not None
        and closed_float is current_table_editor.dialog_float
    ):
        current_table_editor = None

    app = get_app()
    if dialog_stack:
        current_float, focus_target = dialog_stack[-1]
        app.layout.focus(focus_target)
    else:
        current_float = None
        app.layout.focus(text_area)
    app.invalidate()


def show_message(title, text):
    ok_button = Button(text="OK", handler=close_dialog)
    dialog = Dialog(
        title=title,
        body=Label(text=text),
        buttons=[ok_button],
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=ok_button)


def show_input_dialog(title, label_text, default, callback):
    input_field = TextArea(text=default, multiline=False, style="class:input-field")

    def ok_handler():
        value = input_field.text
        close_dialog()
        callback(value)

    dialog = Dialog(
        title=title,
        body=HSplit([Label(text=label_text), input_field]),
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
        body=Label(text=text),
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
            body=Label(text="Save changes before continuing?"),
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


def _canonical_path(path):
    """Return the concrete path Carriage will read from or replace."""
    return os.path.realpath(os.path.abspath(path))


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


def _read_utf8_file_with_snapshot(path):
    """Read one UTF-8 file and fingerprint exactly the bytes that were read."""
    target_path = _canonical_path(path)
    with open(target_path, "rb") as f:
        raw = f.read()
    content = raw.decode("utf-8")
    # Match the universal-newline behavior Carriage used before v1.03 while
    # keeping the fingerprint tied to the exact source bytes.
    content = content.replace("\r\n", "\n").replace("\r", "\n")
    return content, _snapshot_bytes(raw)


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


def _recovery_directory():
    """Return the per-user directory used for hidden crash-recovery state."""
    base = os.environ.get("XDG_STATE_HOME")
    if not base:
        base = os.path.join(os.path.expanduser("~"), ".local", "state")
    return os.path.join(base, "carriage", "recovery")


def _table_recovery_record(table):
    return {
        "headers": list(table.headers),
        "rows": [list(row) for row in table.rows],
        "alignments": list(table.alignments),
        "original_lines": None if table.original_lines is None else list(table.original_lines),
        "dirty": bool(table.dirty),
    }


def _recovery_payload():
    """Capture editor state without requiring the document to materialize.

    Recovery deliberately stores the visible buffer and table objects
    separately. That means it can preserve work even if an interrupted table
    operation has temporarily made normal Markdown materialization impossible.
    """
    return {
        "format": RECOVERY_FORMAT_VERSION,
        "pid": os.getpid(),
        "visible_text": text_area.text,
        "tables": {
            str(number): _table_recovery_record(table)
            for number, table in state.tables.items()
        },
    }


def _ensure_recovery_path():
    directory = _recovery_directory()
    os.makedirs(directory, mode=0o700, exist_ok=True)
    try:
        os.chmod(directory, 0o700)
    except OSError:
        # A pre-existing XDG state directory may live on a filesystem where
        # chmod is unsupported. The recovery file itself is still forced 0600.
        pass

    if state.recovery_path is None:
        token = os.urandom(6).hex()
        state.recovery_path = os.path.join(
            directory, f"untitled-{os.getpid()}-{token}.json"
        )
    return state.recovery_path


def _write_recovery_snapshot():
    """Atomically persist the current untitled document for crash recovery."""
    if state.path is not None or not state.is_modified(text_area.text):
        _clear_recovery_file()
        return

    recovery_path = _ensure_recovery_path()
    directory = os.path.dirname(recovery_path)
    temp_path = None
    fd = None
    payload = json.dumps(
        _recovery_payload(),
        ensure_ascii=False,
        separators=(",", ":"),
    )

    try:
        fd, temp_path = tempfile.mkstemp(
            prefix=".recovery-",
            suffix=".tmp",
            dir=directory,
            text=True,
        )
        os.fchmod(fd, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
            fd = None
            f.write(payload)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_path, recovery_path)
        temp_path = None
        try:
            dir_fd = os.open(directory, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
        except OSError:
            dir_fd = None
        if dir_fd is not None:
            try:
                os.fsync(dir_fd)
            finally:
                os.close(dir_fd)
    finally:
        if fd is not None:
            os.close(fd)
        if temp_path is not None:
            try:
                os.unlink(temp_path)
            except OSError:
                pass


def _clear_recovery_file():
    recovery_path = state.recovery_path
    state.recovery_path = None
    state.recovery_error = False
    if recovery_path is None:
        return
    try:
        os.unlink(recovery_path)
    except FileNotFoundError:
        pass
    except OSError:
        # A failed cleanup is safer than deleting anything else. A stale file
        # can simply be offered again on a future launch.
        pass


def _read_recovery_payload(path):
    with open(path, "r", encoding="utf-8") as f:
        payload = json.load(f)
    if payload.get("format") != RECOVERY_FORMAT_VERSION:
        raise ValueError("Unsupported Carriage recovery format.")
    if not isinstance(payload.get("visible_text"), str):
        raise ValueError("Recovery file does not contain document text.")
    if not isinstance(payload.get("tables"), dict):
        raise ValueError("Recovery file contains invalid table data.")
    return payload


def _process_is_running(pid):
    if not isinstance(pid, int) or pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    except OSError:
        return False
    return True


def _stale_recovery_files():
    """Return newest-first recovery files whose creating process is gone."""
    directory = _recovery_directory()
    try:
        names = os.listdir(directory)
    except FileNotFoundError:
        return []
    except OSError:
        return []

    stale = []
    for name in names:
        if not (name.startswith("untitled-") and name.endswith(".json")):
            continue
        path = os.path.join(directory, name)
        try:
            payload = _read_recovery_payload(path)
            pid = payload.get("pid")
            if _process_is_running(pid):
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
    payload = _read_recovery_payload(path)
    restored_tables = {}
    for raw_number, raw_table in payload["tables"].items():
        number = int(raw_number)
        if not isinstance(raw_table, dict):
            raise ValueError("Recovery file contains invalid table data.")
        restored_tables[number] = TableData(
            headers=list(raw_table.get("headers", [])),
            rows=[list(row) for row in raw_table.get("rows", [])],
            alignments=list(raw_table.get("alignments", [])),
            original_lines=(
                None
                if raw_table.get("original_lines") is None
                else list(raw_table.get("original_lines"))
            ),
            dirty=bool(raw_table.get("dirty", False)),
        )

    state.tables = restored_tables
    text_area.buffer.reset(Document(text=payload["visible_text"]))
    state.path = None
    state.saved_text = ""
    state.disk_snapshot = None
    state.autosave_conflict = False
    state.recovery_path = path
    state.recovery_error = False

    # Claim the restored journal for this process immediately so a second
    # concurrently running Carriage instance will not offer it as stale.
    _write_recovery_snapshot()


def _offer_stale_recovery():
    recoveries = _stale_recovery_files()
    if not recoveries:
        return

    recovery_path = recoveries[0]
    extra = len(recoveries) - 1
    suffix = (
        ""
        if extra == 0
        else f"\n\n{extra} older recovery file{'s' if extra != 1 else ''} will remain available."
    )

    def restore_handler():
        close_dialog()
        try:
            _restore_recovery_file(recovery_path)
        except (OSError, ValueError, json.JSONDecodeError) as e:
            show_message("Recovery error", str(e))

    def discard_handler():
        close_dialog()
        try:
            os.unlink(recovery_path)
        except FileNotFoundError:
            pass
        except OSError as e:
            show_message("Recovery error", str(e))
            return
        _offer_stale_recovery()

    restore_button = Button(text="Restore", handler=restore_handler)
    discard_button = Button(text="Discard", handler=discard_handler)
    later_button = Button(text="Later", handler=close_dialog)
    dialog = Dialog(
        title="Recover untitled document?",
        body=Label(
            text=(
                "Carriage found an untitled document recovery from an earlier "
                "session that did not close normally. Restore it?" + suffix
            )
        ),
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
        body=Label(
            text=(
                "The current file is marked read-only. Carriage will not replace it.\n\n"
                "Use Save As to write your changes to a different file."
            )
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
        body=Label(
            text=(
                "This file has been changed, replaced, or deleted outside Carriage "
                "since it was opened or last saved.\n\n"
                "Save As keeps both versions. Overwrite replaces the current disk "
                "version with the text in Carriage."
            )
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
        body=Label(text=text),
        buttons=[replace_button, cancel_button],
        width=D(preferred=74),
    )
    show_dialog(dialog, focus=cancel_button)


def do_new():
    _clear_recovery_file()
    text_area.buffer.reset(Document(text=""))
    state.path = None
    state.saved_text = ""
    state.disk_snapshot = None
    state.autosave_conflict = False
    state.tables = {}


def do_open():
    def cb(raw_path):
        path = os.path.expanduser(raw_path.strip())
        if not path:
            return
        if not os.path.exists(path):
            show_message("Not found", f"No such file:\n{path}")
            return
        try:
            content, disk_snapshot = _read_utf8_file_with_snapshot(path)
        except (OSError, UnicodeError) as e:
            show_message("Error opening file", str(e))
            return
        _clear_recovery_file()
        visible = _collapse_tables_from_source(content)
        text_area.buffer.reset(Document(text=visible))
        state.path = path
        state.saved_text = content
        state.disk_snapshot = disk_snapshot
        state.autosave_conflict = False

    show_input_dialog("Open File", "Path:", state.path or "", cb)


def _write_file(path, expected_snapshot, report_conflict=True, report_read_only=True):
    """Atomically save only if the destination is still the expected version."""
    try:
        content = _materialize_tables(text_area.text)
    except ValueError as e:
        show_message("Table error", str(e))
        return _SAVE_ERROR

    target_path = _canonical_path(path)
    directory = os.path.dirname(target_path) or "."
    temp_path = None

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

        try:
            existing_mode = stat.S_IMODE(os.stat(target_path).st_mode)
        except FileNotFoundError:
            existing_mode = None

        fd, temp_path = tempfile.mkstemp(
            prefix=f".{os.path.basename(target_path)}.",
            suffix=".tmp",
            dir=directory,
            text=True,
        )

        try:
            if existing_mode is not None:
                os.fchmod(fd, existing_mode)
            else:
                # Match the permissions a normal open(..., "w") would use
                # for a newly created file, including the process umask.
                current_umask = os.umask(0)
                os.umask(current_umask)
                os.fchmod(fd, 0o666 & ~current_umask)

            with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
                fd = None  # fdopen owns and closes the descriptor now.
                f.write(content)
                f.flush()
                os.fsync(f.fileno())

            # Recheck after the complete temporary file has been written. If
            # another program changed the destination while this save was in
            # progress, leave that version untouched.
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

            # The temporary file is in the destination directory, so this
            # replacement is atomic on the same filesystem. The existing file
            # stays untouched unless the complete new contents were written.
            os.replace(temp_path, target_path)
            temp_path = None
        finally:
            if fd is not None:
                os.close(fd)
            if temp_path is not None:
                try:
                    os.unlink(temp_path)
                except OSError:
                    pass

        state.saved_text = content
        state.path = path
        state.disk_snapshot = _snapshot_bytes(content.encode("utf-8"))
        state.autosave_conflict = False
        _clear_recovery_file()
        return _SAVE_OK
    except (OSError, UnicodeError) as e:
        show_message("Error saving file", str(e))
        return _SAVE_ERROR


def do_save(on_saved=None):
    if state.path is None:
        do_save_as(on_saved)
        return

    try:
        if _path_is_read_only(state.path):
            _show_read_only_save(on_saved)
            return
        disk_snapshot = _disk_snapshot(state.path)
    except OSError as e:
        show_message("Error checking file", str(e))
        return

    if state.disk_snapshot is None:
        # This can only occur for an unusual state created by older code or a
        # future caller. Fail safe by treating the version visible right now
        # as the one that must remain unchanged during this save.
        state.disk_snapshot = disk_snapshot

    if disk_snapshot != state.disk_snapshot:
        _show_save_conflict(disk_snapshot, on_saved)
        return

    result = _write_file(state.path, expected_snapshot=state.disk_snapshot)
    if result == _SAVE_OK and on_saved:
        on_saved()


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

    show_input_dialog("Save As", "Path:", state.path or "", cb)


def do_quit():
    _clear_recovery_file()
    get_app().exit()


# ---------------------------------------------------------------------------
# Prose-first wrapping and reflow
# ---------------------------------------------------------------------------

# The formatter intentionally understands only the Markdown structures that
# matter to ordinary prose editing. Everything else is treated conservatively:
# if a nonblank region looks structural or ambiguous, reflow leaves it alone.
# This keeps Ctrl+J useful for prose without turning the editor into a Markdown
# parser.

_ATX_HEADING_RE = re.compile(r"^\s{0,3}#{1,6}(?:\s|$)")
_LIST_ITEM_RE = re.compile(r"^(\s{0,3}(?:[-*+]|\d+[.)])\s+)")
_REFERENCE_DEF_RE = re.compile(r"^\s{0,3}\[[^\]]+\]:\s*\S")
_DEFINITION_MARKER_RE = re.compile(r"^\s{0,3}[:~]\s+\S")
_SETEXT_UNDERLINE_RE = re.compile(r"^\s{0,3}(?:=+|-+)\s*$")
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
_OTHER_LIST_RE = re.compile(
    r"^\s{0,3}(?:(?:[A-Za-z]|[ivxlcdmIVXLCDM]+|#)[.)]|\(@[^)]+\))\s+"
)
_GRID_BORDER_RE = re.compile(r"^\s*\+[+=:-]{2,}(?:\+[+=:-]{2,})+\+?\s*$")
_SIMPLE_TABLE_SEPARATOR_RE = re.compile(
    r"^\s*:?-{3,}:?(?:[ \t]+:?-{3,}:?)+\s*$"
)
# Generic fence-like delimiters used by non-prose formats (for example $$ or
# ::: note). We do not interpret their contents; a matching closing delimiter
# simply makes the whole region opaque to auto-wrap and reflow. Delimiters
# already meaningful to ordinary Markdown prose (#, -, *, _, `, ~) are handled
# by the dedicated rules above instead.
_GENERIC_FENCE_RE = re.compile(
    r"^\s{0,3}(?P<marker>[$:;%!?^&]{2,})(?:[ \t]+.*)?$"
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


def _hard_break_marker(line):
    """Return the Markdown hard-break marker at line end, if present."""
    trailing_spaces = len(line) - len(line.rstrip(" "))
    if trailing_spaces >= 2:
        return "  "

    stripped = line.rstrip(" ")
    backslashes = 0
    for char in reversed(stripped):
        if char != "\\":
            break
        backslashes += 1
    if backslashes % 2 == 1:
        return "\\"
    return None


def _strip_hard_break_marker(line, marker):
    if marker == "  ":
        return line.rstrip(" ")
    if marker == "\\":
        stripped = line.rstrip(" ")
        return stripped[:-1]
    return line


def _wrap_markdown_prose(source_lines, width, initial_indent="", subsequent_indent=""):
    """Wrap prose while preserving explicit Markdown hard line breaks."""
    segments = []
    current = []

    for raw_line in source_lines:
        marker = _hard_break_marker(raw_line)
        text = _strip_hard_break_marker(raw_line, marker)
        current.append(text.strip())
        if marker is not None:
            segments.append((" ".join(part for part in current if part), marker))
            current = []

    if current or not segments:
        segments.append((" ".join(part for part in current if part), None))

    rendered = []
    for segment_text, marker in segments:
        first_indent = initial_indent if not rendered else subsequent_indent
        wrapped = textwrap.wrap(
            segment_text,
            width=width,
            initial_indent=first_indent,
            subsequent_indent=subsequent_indent,
            # Prose wrapping must never manufacture whitespace inside a token.
            # A long URL, autolink, path, or hyphenated word may exceed the
            # target width rather than being split and changing Markdown text.
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
        and compact[0] in "-* _".replace(" ", "")
    )


def _is_indented_code(line):
    return line.startswith("    ") or line.startswith("\t")


def _generic_fence_marker(line):
    """Return an opaque delimiter marker for unfamiliar fence-like syntax."""
    match = _GENERIC_FENCE_RE.match(line)
    if not match:
        return None
    return match.group("marker")


def _is_generic_fence_close(line, marker):
    return line.strip() == marker


def _looks_structural_or_ambiguous(line):
    """Conservative signal that a line is not confidently ordinary prose."""
    if not line.strip():
        return False

    # One to three leading spaces are meaningful in several Markdown/Pandoc
    # constructs. Ordinary prose does not need us to normalize that ambiguity.
    leading_spaces = len(line) - len(line.lstrip(" "))
    if 1 <= leading_spaces <= 3:
        return True

    if _generic_fence_marker(line):
        return True

    stripped = line.strip()
    # Standalone punctuation-heavy delimiter/control lines are safer opaque.
    # This intentionally errs toward preservation instead of learning every
    # extension that Pandoc or another Markdown flavor may support.
    alnum = sum(char.isalnum() for char in stripped)
    punctuation = sum(not char.isalnum() and not char.isspace() for char in stripped)
    if len(stripped) >= 2 and alnum == 0 and punctuation >= 2:
        return True

    return False


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


def _definition_list_start(lines, index):
    return (
        index + 1 < len(lines)
        and bool(lines[index].strip())
        and bool(_DEFINITION_MARKER_RE.match(lines[index + 1]))
    )


def _setext_heading_start(lines, index):
    return (
        index + 1 < len(lines)
        and bool(lines[index].strip())
        and not _is_thematic_break(lines[index])
        and bool(_SETEXT_UNDERLINE_RE.match(lines[index + 1]))
    )


def _nonblank_run_end(lines, index):
    i = index
    while i < len(lines) and lines[i].strip():
        i += 1
    return i


def _nonblank_run_bounds(lines, row):
    start = row
    while start > 0 and lines[start - 1].strip():
        start -= 1
    end = row + 1
    while end < len(lines) and lines[end].strip():
        end += 1
    return start, end


def _run_has_opaque_signal(lines, start, end):
    """
    Return True when a nonblank run is safer to preserve than to interpret.

    This catches structures that are not core prose-editing targets. The
    formatter does not need to identify their exact Markdown dialect.
    """
    for i in range(start, end):
        line = lines[i]
        stripped = line.lstrip()
        if (
            TABLE_PLACEHOLDER_RE.match(line)
            or
            _fence_marker(line)
            or _REFERENCE_DEF_RE.match(line)
            or _DEFINITION_MARKER_RE.match(line)
            or _is_indented_code(line)
            or _is_strong_html_start(line)
            or _OTHER_LIST_RE.match(line)
            or stripped.startswith("|")
            or _GRID_BORDER_RE.match(line)
            or _SIMPLE_TABLE_SEPARATOR_RE.match(line)
            or _is_pipe_table_separator(line)
            or _looks_structural_or_ambiguous(line)
        ):
            return True
        if _is_pipe_table_start(lines, i) or _definition_list_start(lines, i):
            return True
    return False


def _collect_generic_opaque_block(lines, index):
    """Collect an unfamiliar fence-like block without interpreting its body."""
    marker = _generic_fence_marker(lines[index])
    block = [lines[index]]
    index += 1
    if marker is None:
        return block, index

    while index < len(lines):
        block.append(lines[index])
        if _is_generic_fence_close(lines[index], marker):
            index += 1
            break
        index += 1
    return block, index


def _row_in_multiline_opaque_block(lines, row):
    """Return True when row lies inside any known opaque multiline region."""
    i = 0
    while i < len(lines):
        if _fence_marker(lines[i]):
            _, end = _collect_fenced_block(lines, i)
            if i <= row < end:
                return True
            i = max(end, i + 1)
            continue
        if _is_strong_html_start(lines[i]):
            _, end = _collect_html_block(lines, i)
            if i <= row < end:
                return True
            i = max(end, i + 1)
            continue
        if _generic_fence_marker(lines[i]):
            _, end = _collect_generic_opaque_block(lines, i)
            if i <= row < end:
                return True
            i = max(end, i + 1)
            continue
        i += 1
    return False


def _run_is_plain_prose(lines, row):
    """Return True only when the cursor's whole nonblank run is plain prose."""
    start, end = _nonblank_run_bounds(lines, row)
    if _run_has_opaque_signal(lines, start, end):
        return False
    for i in range(start, end):
        line = lines[i]
        if (
            TABLE_PLACEHOLDER_RE.match(line)
            or
            _ATX_HEADING_RE.match(line)
            or _LIST_ITEM_RE.match(line)
            or line.lstrip().startswith(">")
            or _is_thematic_break(line)
            or _SETEXT_UNDERLINE_RE.match(line)
            or _setext_heading_start(lines, i)
        ):
            return False
    return True


def _collect_fenced_block(lines, index):
    marker = _fence_marker(lines[index])
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
    """Collect unmistakable raw HTML verbatim; do not parse HTML content."""
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

    # For an unmistakable block-level opening tag, preserve through its first
    # matching close even across blank lines. This is boundary detection only;
    # the editor does not inspect or format the HTML body. Void/self-closing
    # tags are single-line opaque blocks.
    block_match = _BLOCK_HTML_TAG_RE.match(first)
    if block_match:
        stripped_first = first.lstrip()
        tag = block_match.group("tag")
        void_tags = {"base", "basefont", "col", "frame", "hr", "link", "param", "track"}
        if stripped_first.startswith("</") or tag.lower() in void_tags or re.search(r"/\s*>\s*$", first):
            return [first], index + 1

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


# ---------------------------------------------------------------------------
# Folded table objects
# ---------------------------------------------------------------------------

def _table_placeholder(table_number):
    """Return the editor-buffer representation of a folded table."""
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
    return "\n".join(lines)


def _collapse_tables_from_source(source_text):
    """Replace supported source tables with folded references in the editor."""
    state.tables = {}
    lines = source_text.split("\n")
    visible = []
    i = 0
    table_number = 1

    yaml_end = _yaml_front_matter_end(lines)
    if yaml_end is not None:
        visible.extend(lines[:yaml_end])
        i = yaml_end

    while i < len(lines):
        # Table-looking text inside opaque regions is not a document table.
        if _fence_marker(lines[i]):
            block, end = _collect_fenced_block(lines, i)
            visible.extend(block)
            i = end
            continue
        if _generic_fence_marker(lines[i]):
            block, end = _collect_generic_opaque_block(lines, i)
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

        if _is_pipe_table_start(lines, i):
            block, end = _collect_pipe_table(lines, i)
            parsed = _parse_pipe_table(block)
            if parsed is not None:
                state.tables[table_number] = parsed
                visible.append(_table_placeholder(table_number))
                table_number += 1
                i = end
                continue
        visible.append(lines[i])
        i += 1

    return "\n".join(visible)


def _materialize_tables(visible_text):
    """Expand folded references back to Markdown for saving/exporting."""
    rendered = []
    seen = set()

    for line in visible_text.split("\n"):
        match = TABLE_PLACEHOLDER_RE.match(line)
        if not match:
            rendered.append(line)
            continue

        table_number = int(match.group(1))
        if table_number in seen:
            raise ValueError(
                f"Table {table_number} appears more than once in the document. "
                "Use one folded reference per table."
            )
        table = state.tables.get(table_number)
        if table is None:
            raise ValueError(
                f"Table {table_number} no longer has table data attached to it."
            )
        rendered.extend(_serialize_table(table).split("\n"))
        seen.add(table_number)

    missing = sorted(set(state.tables) - seen)
    if missing:
        label = ", ".join(f"Table {number}" for number in missing)
        raise ValueError(
            f"{label} no longer has a folded reference in the document. "
            "Undo the deletion before saving."
        )

    return "\n".join(rendered)


def _table_number_at_cursor():
    line = text_area.buffer.document.current_line
    match = TABLE_PLACEHOLDER_RE.match(line)
    return int(match.group(1)) if match else None


def _shift_table_numbers_for_insert(insert_number):
    """Make room for a new document-relative table number."""
    if not state.tables:
        return

    new_tables = {}
    for number in sorted(state.tables, reverse=True):
        target = number + 1 if number >= insert_number else number
        new_tables[target] = state.tables[number]
    state.tables = new_tables

    doc = text_area.buffer.document
    row = doc.cursor_position_row
    col = doc.cursor_position_col
    changed = False
    new_lines = []
    for line in doc.lines:
        match = TABLE_PLACEHOLDER_RE.match(line)
        if match and int(match.group(1)) >= insert_number:
            line = _table_placeholder(int(match.group(1)) + 1)
            changed = True
        new_lines.append(line)

    if changed:
        new_text = "\n".join(new_lines)
        tmp = Document(text=new_text)
        new_cursor = tmp.translate_row_col_to_index(
            min(row, tmp.line_count - 1),
            min(col, len(tmp.lines[min(row, tmp.line_count - 1)])),
        )
        text_area.buffer.document = Document(new_text, cursor_position=new_cursor)


def _insert_table_placeholder(table_number):
    """Insert a folded table as its own prose block at the cursor."""
    buf = text_area.buffer
    doc = buf.document
    before = doc.current_line_before_cursor
    after = doc.current_line_after_cursor

    prefix = ""
    suffix = ""
    if before.strip():
        prefix = "\n\n"
    elif doc.cursor_position_row > 0 and doc.lines[doc.cursor_position_row - 1].strip():
        prefix = "\n"

    if after.strip():
        suffix = "\n\n"
    elif doc.cursor_position_row + 1 < doc.line_count and doc.lines[doc.cursor_position_row + 1].strip():
        suffix = "\n"

    buf.insert_text(prefix + _table_placeholder(table_number) + suffix)


def _new_table_data(columns, rows):
    return TableData(
        headers=[""] * columns,
        rows=[[""] * columns for _ in range(rows)],
        alignments=["default"] * columns,
        original_lines=None,
        dirty=True,
    )


def _collect_definition_list(lines, index):
    """Preserve a definition-list run verbatim rather than formatting it."""
    end = _nonblank_run_end(lines, index)
    return lines[index:end], end


def _list_block_extent(lines, index):
    """Return (end, complex) for the list block beginning at index.

    A simple list is a contiguous run with no blank lines and with every item
    marker at the same indentation. Blank-separated items/paragraphs, nested
    markers, or indented continuation blocks make the list complex and opaque.
    """
    first = _LIST_ITEM_RE.match(lines[index])
    if not first:
        return index + 1, True

    base_indent = len(lines[index]) - len(lines[index].lstrip(" "))
    i = index
    complex_list = False

    while i < len(lines):
        line = lines[i]
        if not line.strip():
            # A blank line belongs to this list only when what follows still
            # looks list-owned: another item or an indented continuation.
            j = i
            while j < len(lines) and not lines[j].strip():
                j += 1
            if j >= len(lines):
                return i, complex_list

            next_line = lines[j]
            next_match = _LIST_ITEM_RE.match(next_line)
            next_indent = len(next_line) - len(next_line.lstrip(" "))
            if next_match or next_indent > base_indent:
                complex_list = True
                i = j
                continue
            return i, complex_list

        match = _LIST_ITEM_RE.match(line)
        if match:
            indent = len(line) - len(line.lstrip(" "))
            if indent != base_indent:
                complex_list = True
        elif i > index:
            indent = len(line) - len(line.lstrip(" "))
            if indent > base_indent:
                # Any explicitly indented continuation is structurally
                # ambiguous enough that preserving the whole list is safer.
                complex_list = True

        i += 1

    return i, complex_list


def _collect_simple_list(lines, index, width):
    """
    Reflow a flat prose list. Return None when the list looks complex.

    Complex, nested, or otherwise structural lists are deliberately left to
    the caller's opaque fallback.
    """
    end = _nonblank_run_end(lines, index)
    i = index
    items = []
    base_indent = len(lines[index]) - len(lines[index].lstrip(" "))

    while i < end:
        match = _LIST_ITEM_RE.match(lines[i])
        if not match:
            return None, end
        if len(lines[i]) - len(lines[i].lstrip(" ")) != base_indent:
            return None, end
        marker = match.group(1)
        body = [lines[i][len(marker):]]
        i += 1

        while i < end and not _LIST_ITEM_RE.match(lines[i]):
            candidate = lines[i]
            if (
                _ATX_HEADING_RE.match(candidate)
                or candidate.lstrip().startswith(">")
                or _fence_marker(candidate)
                or _is_indented_code(candidate)
                or _is_strong_html_start(candidate)
                or _REFERENCE_DEF_RE.match(candidate)
                or _DEFINITION_MARKER_RE.match(candidate)
                or _OTHER_LIST_RE.match(candidate)
                or _is_thematic_break(candidate)
                or _SETEXT_UNDERLINE_RE.match(candidate)
            ):
                return None, end
            # Keep the raw line so two-space/backslash hard breaks survive.
            body.append(candidate)
            i += 1

        items.append((marker, body))

    rendered = []
    for marker, body in items:
        rendered.extend(
            _wrap_markdown_prose(
                body,
                width=width,
                initial_indent=marker,
                subsequent_indent=" " * len(marker),
            )
        )
    return rendered, end


def _collect_simple_blockquote(lines, index, width):
    """
    Reflow only explicit, single-level prose blockquotes.

    Lazy continuations, nested quotes, or structural content make the whole
    nonblank run opaque. This is intentionally less clever than a Markdown
    parser and therefore safer for a prose editor.
    """
    end = _nonblank_run_end(lines, index)
    inner = []
    for i in range(index, end):
        match = re.match(r"^\s{0,3}>[ \t]?(.*)$", lines[i])
        if not match:
            return None, end
        content = match.group(1)
        if re.match(r"^\s{0,3}>", content):
            return None, end
        if content and (
            _fence_marker(content)
            or _ATX_HEADING_RE.match(content)
            or _LIST_ITEM_RE.match(content)
            or _is_indented_code(content)
            or _is_strong_html_start(content)
        ):
            return None, end
        inner.append(content)

    rendered = []
    paragraph = []
    for content in inner + [""]:
        if content.strip():
            paragraph.append(content)
            continue
        if paragraph:
            wrapped = _wrap_markdown_prose(
                paragraph,
                width=max(10, width - 2),
            )
            rendered.extend(f"> {line}" if line else ">" for line in wrapped)
            paragraph = []
        if content == "" and rendered and rendered[-1] != ">":
            rendered.append(">")

    if rendered and rendered[-1] == ">" and inner and inner[-1].strip():
        rendered.pop()
    return rendered, end


def _clear_supported_start(lines, index):
    line = lines[index]
    return bool(
        _ATX_HEADING_RE.match(line)
        or _LIST_ITEM_RE.match(line)
        or line.lstrip().startswith(">")
        or _fence_marker(line)
        or _is_thematic_break(line)
        or _setext_heading_start(lines, index)
    )


def _append_reflow_block(blocks, gap_before, kind, block_lines):
    if block_lines:
        blocks.append((gap_before, kind, block_lines))


def _should_insert_missing_blank(previous_kind, current_kind):
    """Normalize spacing only between structures we intentionally understand."""
    if previous_kind in {"opaque", "yaml"} or current_kind in {"opaque", "yaml"}:
        return False
    return previous_kind != current_kind or current_kind != "prose"


def _on_text_insert(buf):
    """Hard-wrap ordinary paragraph prose only."""
    if not state.auto_wrap:
        return

    for _ in range(20):
        doc = buf.document
        row = doc.cursor_position_row
        col = doc.cursor_position_col
        lines = doc.lines
        line = lines[row]

        hard_break_marker = _hard_break_marker(line)
        searchable_line = _strip_hard_break_marker(line, hard_break_marker)

        # Markdown hard-break markers are syntax, not prose content. In
        # particular, the two trailing spaces must never be considered word
        # boundaries: doing so can create an empty overflow line exactly when
        # the physical line first crosses WRAP_COLUMN. A line whose prose is
        # still within the target width is left alone even if its hard-break
        # marker makes the physical line one or two characters longer.
        if len(searchable_line) <= WRAP_COLUMN:
            return

        yaml_end = _yaml_front_matter_end(lines)
        if yaml_end is not None and row < yaml_end:
            return

        # A whole nonblank run must be plain prose before auto-wrap touches it.
        # Multiline opaque regions are checked separately so blank lines inside
        # fenced code or raw block HTML do not accidentally re-enable wrapping.
        if _row_in_multiline_opaque_block(lines, row):
            return
        if not _run_is_plain_prose(lines, row):
            return

        # Search only the prose portion of the line. The original line is
        # still sliced below so any hard-break marker remains attached to the
        # final overflow segment where it belongs.
        break_at = searchable_line.rfind(" ", 0, WRAP_COLUMN + 1)
        if break_at <= 0:
            return

        head = line[:break_at]
        tail = line[break_at + 1:]
        next_exists = row + 1 < len(lines)
        next_line = lines[row + 1] if next_exists else ""
        has_hard_break = hard_break_marker is not None

        new_lines = list(lines)
        new_lines[row] = head
        if next_exists and next_line.strip() and not has_hard_break:
            new_lines[row + 1] = tail + " " + next_line
        else:
            # When the original line ends in an explicit Markdown hard break,
            # its overflow must stay on a line of its own so the two spaces or
            # trailing backslash remain at the physical line boundary.
            new_lines.insert(row + 1, tail)

        new_text = "\n".join(new_lines)
        if col <= break_at:
            new_row, new_col = row, col
        else:
            new_row, new_col = row + 1, col - break_at - 1

        tmp = Document(text=new_text)
        new_cursor = tmp.translate_row_col_to_index(new_row, new_col)
        buf.document = Document(text=new_text, cursor_position=new_cursor)


text_area.buffer.on_text_insert += _on_text_insert


def reflow_text(full_text, width=WRAP_COLUMN):
    """
    Reflow prose, not Markdown syntax.

    Actively formatted:
      * ordinary prose paragraphs;
      * simple flat bullet/decimal lists;
      * explicit single-level prose blockquotes.

    Preserved verbatim:
      * YAML front matter, fenced/indented code, tables, definition/reference
        blocks, raw block HTML, complex lists/quotes, and unfamiliar or
        ambiguous non-prose structures.

    Clear prose structures such as headings may receive a missing blank line.
    Opaque material never receives invented spacing because doing so could
    change its meaning.
    """
    lines = full_text.split("\n")
    blocks = []
    i = 0
    pending_gap = 0

    yaml_end = _yaml_front_matter_end(lines)
    if yaml_end is not None:
        _append_reflow_block(blocks, 0, "yaml", lines[:yaml_end])
        i = yaml_end

    while i < len(lines):
        if not lines[i].strip():
            pending_gap += 1
            i += 1
            continue

        gap = pending_gap
        pending_gap = 0
        line = lines[i]

        if _fence_marker(line):
            block, i = _collect_fenced_block(lines, i)
            _append_reflow_block(blocks, gap, "opaque", block)
            continue

        if _generic_fence_marker(line):
            block, i = _collect_generic_opaque_block(lines, i)
            _append_reflow_block(blocks, gap, "opaque", block)
            continue

        if _is_strong_html_start(line):
            block, i = _collect_html_block(lines, i)
            _append_reflow_block(blocks, gap, "opaque", block)
            continue

        if _is_pipe_table_start(lines, i):
            block, i = _collect_pipe_table(lines, i)
            _append_reflow_block(blocks, gap, "opaque", block)
            continue

        if _definition_list_start(lines, i):
            block, i = _collect_definition_list(lines, i)
            _append_reflow_block(blocks, gap, "opaque", block)
            continue

        run_end = _nonblank_run_end(lines, i)
        if _run_has_opaque_signal(lines, i, run_end):
            _append_reflow_block(blocks, gap, "opaque", lines[i:run_end])
            i = run_end
            continue

        if _setext_heading_start(lines, i):
            _append_reflow_block(blocks, gap, "heading", [line, lines[i + 1]])
            i += 2
            continue

        if _ATX_HEADING_RE.match(line):
            _append_reflow_block(blocks, gap, "heading", [line])
            i += 1
            continue

        if _is_thematic_break(line) or _SETEXT_UNDERLINE_RE.match(line):
            _append_reflow_block(blocks, gap, "structure", [line])
            i += 1
            continue

        if _LIST_ITEM_RE.match(line):
            block_end, complex_list = _list_block_extent(lines, i)
            if complex_list:
                _append_reflow_block(blocks, gap, "opaque", lines[i:block_end])
                i = block_end
                continue

            wrapped, end = _collect_simple_list(lines, i, width)
            if wrapped is None:
                _append_reflow_block(blocks, gap, "opaque", lines[i:end])
            else:
                _append_reflow_block(blocks, gap, "list", wrapped)
            i = end
            continue

        if line.lstrip().startswith(">"):
            wrapped, end = _collect_simple_blockquote(lines, i, width)
            if wrapped is None:
                _append_reflow_block(blocks, gap, "opaque", lines[i:end])
            else:
                _append_reflow_block(blocks, gap, "quote", wrapped)
            i = end
            continue

        # Ordinary prose. Stop only at block forms we intentionally support;
        # anything suspicious would already have made the run opaque above.
        paragraph = [line]
        i += 1
        while i < len(lines) and lines[i].strip() and not _clear_supported_start(lines, i):
            paragraph.append(lines[i])
            i += 1
        wrapped = _wrap_markdown_prose(paragraph, width=width)
        _append_reflow_block(blocks, gap, "prose", wrapped)

    if not blocks:
        return "\n" * max(0, pending_gap - 1)

    rendered = []
    previous_kind = None
    for block_index, (gap_before, kind, block_lines) in enumerate(blocks):
        if block_index == 0:
            rendered.extend([""] * gap_before)
        elif gap_before > 0:
            rendered.extend([""] * gap_before)
        elif _should_insert_missing_blank(previous_kind, kind):
            rendered.append("")
        rendered.extend(block_lines)
        previous_kind = kind

    rendered.extend([""] * pending_gap)
    return "\n".join(rendered)


def do_reflow_document():
    # Keyboard-triggered actions get an undo snapshot automatically before
    # the handler runs; a menu click does not, so save one explicitly here.
    text_area.buffer.save_to_undo_stack()
    text_area.text = reflow_text(text_area.text)

def do_undo():
    text_area.buffer.undo()


def do_redo():
    text_area.buffer.redo()


def do_cut():
    data = text_area.buffer.cut_selection()
    get_app().clipboard.set_data(data)


def do_copy():
    data = text_area.buffer.copy_selection()
    get_app().clipboard.set_data(data)


def do_paste():
    text_area.buffer.paste_clipboard_data(get_app().clipboard.get_data())


def do_toggle_autowrap():
    state.auto_wrap = not state.auto_wrap


def do_toggle_autosave():
    state.auto_save = not state.auto_save


# ---------------------------------------------------------------------------
# Dedicated table editor
# ---------------------------------------------------------------------------

def _table_rows(session):
    return [session.working.headers] + session.working.rows


def _table_cell_label(session):
    location = (
        f"Header · column {session.selected_col + 1}"
        if session.selected_row == 0
        else f"Row {session.selected_row} · column {session.selected_col + 1}"
    )
    mode = "Editing" if session.editing else "Nav"
    return f"{mode} · {location}"


def _table_mode_hint(session):
    if session.editing:
        return "Editing: Enter saves cell · Esc discards cell edit · Ctrl+S saves table"
    return "Nav: ←↑↓→ move · Enter edit · ^R row · ^C col · ^S save · Esc cancel"


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
    _load_table_editor_cell(session)


def _delete_table_editor_column():
    """Delete the selected column, while keeping at least one column."""
    session = current_table_editor
    if session is None:
        return

    _commit_table_editor_cell(session)
    if session.working.column_count <= 1:
        show_message("Last column", "A table must contain at least one column.")
        return

    delete_at = session.selected_col
    del session.working.headers[delete_at]
    for row in session.working.rows:
        del row[delete_at]
    if delete_at < len(session.working.alignments):
        del session.working.alignments[delete_at]
    session.selected_col = min(delete_at, session.working.column_count - 1)
    session.working.dirty = True
    _load_table_editor_cell(session)


def _run_table_editor_command(action):
    """Close a row/column command popup, then apply its table operation."""
    close_dialog()
    action()


def _show_table_row_menu():
    session = current_table_editor
    if session is None:
        return
    if session.editing:
        _commit_table_editor_cell(session)
        session.editing = False
        _update_table_editor_ui(session)

    above = Button(
        text="Insert Above",
        handler=lambda: _run_table_editor_command(lambda: _insert_table_editor_row("above")),
    )
    below = Button(
        text="Insert Below",
        handler=lambda: _run_table_editor_command(lambda: _insert_table_editor_row("below")),
    )
    delete = Button(
        text="Delete Row",
        handler=lambda: _run_table_editor_command(_delete_table_editor_row),
    )
    cancel = Button(text="Cancel", handler=close_dialog)
    dialog = Dialog(
        title="Row",
        body=Label(text="Change the selected table row."),
        buttons=[above, below, delete, cancel],
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=below if session.selected_row == 0 else above)


def _show_table_column_menu():
    session = current_table_editor
    if session is None:
        return
    if session.editing:
        _commit_table_editor_cell(session)
        session.editing = False
        _update_table_editor_ui(session)

    left = Button(
        text="Insert Left",
        handler=lambda: _run_table_editor_command(lambda: _insert_table_editor_column("left")),
    )
    right = Button(
        text="Insert Right",
        handler=lambda: _run_table_editor_command(lambda: _insert_table_editor_column("right")),
    )
    delete = Button(
        text="Delete Column",
        handler=lambda: _run_table_editor_command(_delete_table_editor_column),
    )
    cancel = Button(text="Cancel", handler=close_dialog)
    dialog = Dialog(
        title="Column",
        body=Label(text="Change the selected table column."),
        buttons=[left, right, delete, cancel],
        width=D(preferred=76),
    )
    show_dialog(dialog, focus=right)


def _table_grid_fragments(session):
    """Render the complete table and anchor scrolling to the selected cell.

    The grid Window is deliberately a bounded viewport.  Every table row is
    rendered into its UIContent, including rows whose wrapped cell text makes
    them several screen lines tall.  A zero-width [SetCursorPosition] marker
    is placed at the selected cell; prompt_toolkit uses that logical cursor to
    keep the selection inside the viewport as arrow-key navigation moves
    through a tall table.  The cursor itself remains hidden.
    """
    rows = _table_rows(session)
    columns = session.working.column_count
    try:
        terminal_width = get_app().output.get_size().columns
    except Exception:
        terminal_width = 100
    available = max(50, min(120, terminal_width - 12))
    cell_width = max(8, (available - columns - 1) // columns - 2)

    fragments = []
    # Middle separators must terminate at the table edges. Using ┼ at the
    # ends draws a horizontal stroke beyond each outside vertical border;
    # ├/┤ join into those borders without overshooting them.
    border = "├" + "┼".join("─" * (cell_width + 2) for _ in range(columns)) + "┤"

    def add_border(first=False, last=False):
        if first:
            text = "┌" + "┬".join("─" * (cell_width + 2) for _ in range(columns)) + "┐"
        elif last:
            text = "└" + "┴".join("─" * (cell_width + 2) for _ in range(columns)) + "┘"
        else:
            text = border
        fragments.append(("class:table.border", text + "\n"))

    add_border(first=True)
    for row_number, row in enumerate(rows):
        wrapped_cells = []
        for cell in row:
            wrapped = textwrap.wrap(
                cell,
                width=cell_width,
                break_long_words=False,
                break_on_hyphens=False,
                replace_whitespace=False,
            ) or [""]
            wrapped_cells.append(wrapped)

        row_height = max(len(parts) for parts in wrapped_cells)
        selected_row = row_number == session.selected_row
        # prompt_toolkit scrolls this Window to keep its logical cursor visible.
        # Anchor downward navigation (and always the final row) at the row's
        # last rendered line so the bottom of a tall row can actually enter the
        # viewport. Upward navigation anchors at the first rendered line.
        cursor_visual_line = 0
        if selected_row and (session.scroll_anchor == "bottom" or row_number == len(rows) - 1):
            cursor_visual_line = row_height - 1

        for visual_line in range(row_height):
            fragments.append(("class:table.border", "│"))
            for col in range(columns):
                text = wrapped_cells[col][visual_line] if visual_line < len(wrapped_cells[col]) else ""
                text = text.ljust(cell_width)
                selected = selected_row and col == session.selected_col
                if selected and visual_line == cursor_visual_line:
                    # FormattedTextControl exposes this marker as its logical
                    # cursor position.  Window scrolling follows it even
                    # though show_cursor=False, giving the grid a real
                    # vertically scrolling viewport without altering data.
                    fragments.append(("[SetCursorPosition]", ""))
                if selected:
                    style_name = "class:table.cell.selected"
                elif row_number == 0:
                    style_name = "class:table.header"
                else:
                    style_name = "class:table.cell"
                fragments.append((style_name, f" {text} "))
                fragments.append(("class:table.border", "│"))
            fragments.append(("", "\n"))

        if row_number != len(rows) - 1:
            add_border()
    add_border(last=True)

    if len(rows) > 1:
        fragments.append(
            (
                "class:table.hint",
                "Arrow navigation scrolls the table automatically when the selected cell moves beyond the viewport.",
            )
        )
    return fragments


def _save_table_editor():
    session = current_table_editor
    if session is None:
        return
    _commit_table_editor_cell(session)
    session.working.dirty = True
    state.tables[session.table_number] = session.working
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
        _move_table_editor_cell(-1)

    @table_nav_kb.add("c-r")
    def _nav_row_commands(event):
        _show_table_row_menu()

    @table_nav_kb.add("c-c")
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
        height=D(preferred=16, max=20),
        dont_extend_height=True,
    )
    cell_label = Label(text=_table_cell_label(session))
    mode_label = Label(text=_table_mode_hint(session))
    cell_editor = TextArea(
        text=session.working.headers[0],
        multiline=False,
        wrap_lines=True,
        height=D(preferred=3),
        style="class:table.cell-editor",
    )

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

    cell_editor.control.key_bindings = table_cell_kb

    session.grid_control = grid_control
    session.grid_window = grid_window
    session.cell_label = cell_label
    session.mode_label = mode_label
    session.cell_editor = cell_editor

    dialog = Dialog(
        title=f"Table {table_number}",
        body=HSplit(
            [
                grid_window,
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
        show_message("No table", "Place the cursor on a [[Table N]] reference first.")
        return
    open_table_editor(table_number)


def do_insert_table():
    columns_field = TextArea(text="3", multiline=False, style="class:input-field")
    rows_field = TextArea(text="2", multiline=False, style="class:input-field")

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
        if not 1 <= rows <= 20:
            show_message("Invalid table size", "Choose between 1 and 20 data rows.")
            return

        # Number tables by document order. Existing tables at or after the
        # insertion point shift upward by one.
        current_row = text_area.buffer.document.cursor_position_row
        insert_number = 1
        for line in text_area.buffer.document.lines[:current_row + 1]:
            if TABLE_PLACEHOLDER_RE.match(line):
                insert_number += 1

        close_dialog()
        _shift_table_numbers_for_insert(insert_number)
        state.tables[insert_number] = _new_table_data(columns, rows)
        _insert_table_placeholder(insert_number)
        open_table_editor(insert_number)

    dialog = Dialog(
        title="Insert Table",
        body=HSplit(
            [
                Label(text="Columns (2–6):"),
                columns_field,
                Label(text="Data rows (1–20):"),
                rows_field,
            ]
        ),
        buttons=[
            Button(text="Insert", handler=insert_handler),
            Button(text="Cancel", handler=close_dialog),
        ],
        width=D(preferred=50),
    )
    show_dialog(dialog, focus=columns_field)


async def _autosave_loop():
    while True:
        await asyncio.sleep(AUTOSAVE_INTERVAL_SECONDS)
        if not state.auto_save:
            continue
        if state.external_process_running:
            continue
        if current_float is not None:
            # Do not write behind Open/Save/Export dialogs, and prevent a
            # persistent background-write failure from stacking error modals.
            continue

        if state.path is None:
            if not state.is_modified(text_area.text):
                _clear_recovery_file()
                continue
            try:
                _write_recovery_snapshot()
            except (OSError, UnicodeError, TypeError, ValueError) as e:
                if not state.recovery_error:
                    state.recovery_error = True
                    show_message(
                        "Recovery unavailable",
                        "Carriage could not update the crash-recovery copy for this "
                        f"untitled document.\n\n{e}",
                    )
            else:
                state.recovery_error = False
            get_app().invalidate()
            continue

        if not state.is_modified(text_area.text):
            continue

        try:
            if _path_is_read_only(state.path):
                if not state.autosave_conflict:
                    state.autosave_conflict = True
                    show_message(
                        "Autosave paused",
                        "The current file is marked read-only. Autosave will not "
                        "replace it. Use Save As to write your changes elsewhere.",
                    )
                continue
            disk_snapshot = _disk_snapshot(state.path)
        except OSError as e:
            if not state.autosave_conflict:
                state.autosave_conflict = True
                show_message(
                    "Autosave paused",
                    f"Carriage could not verify the file on disk, so it did not save.\n\n{e}",
                )
            continue

        if state.disk_snapshot is None or disk_snapshot != state.disk_snapshot:
            if not state.autosave_conflict:
                state.autosave_conflict = True
                show_message(
                    "Autosave paused",
                    "The file changed, was replaced, or was deleted outside Carriage. "
                    "Autosave will not overwrite that version. Use Save to choose "
                    "Save As, Overwrite, or Cancel.",
                )
            continue

        state.autosave_conflict = False
        result = _write_file(
            state.path,
            expected_snapshot=state.disk_snapshot,
            report_conflict=False,
            report_read_only=False,
        )
        if result == _SAVE_CONFLICT and not state.autosave_conflict:
            state.autosave_conflict = True
            show_message(
                "Autosave paused",
                "The file changed while autosave was running. Nothing was overwritten. "
                "Use Save to choose how to resolve the conflict.",
            )
        elif result == _SAVE_READ_ONLY and not state.autosave_conflict:
            state.autosave_conflict = True
            show_message(
                "Autosave paused",
                "The file became read-only while autosave was running. Nothing was "
                "overwritten. Use Save As to write your changes elsewhere.",
            )
        get_app().invalidate()


# ---------------------------------------------------------------------------
# Pandoc export
# ---------------------------------------------------------------------------

def _default_export_path(ext):
    base = os.path.splitext(state.path)[0] if state.path else "untitled"
    return base + "." + ext


def _pandoc_args_define_output(args):
    """Return True if custom arguments try to choose their own output path."""
    for arg in args:
        if arg == "--output" or arg.startswith("--output="):
            return True
        if arg == "-o" or (arg.startswith("-o") and len(arg) > 2):
            return True
    return False


def _perform_pandoc_export(out_path, source_text, extra_args, expected_snapshot):
    """Run Pandoc into a staging file, then safely replace the destination."""
    target_path = _canonical_path(out_path)
    directory = os.path.dirname(target_path) or "."
    basename = os.path.basename(target_path)
    stem, extension = os.path.splitext(basename)
    temp_path = None
    fd = None

    try:
        # Confirmation is tied to a specific destination version. If it
        # changed while the user was deciding, do not overwrite the new one.
        if _disk_snapshot(target_path) != expected_snapshot:
            show_message(
                "Export destination changed",
                "The output file changed before export began. Nothing was overwritten. "
                "Choose the export path again to review the current destination.",
            )
            return False

        try:
            existing_mode = stat.S_IMODE(os.stat(target_path).st_mode)
        except FileNotFoundError:
            existing_mode = None

        fd, temp_path = tempfile.mkstemp(
            prefix=f".{stem or basename}.",
            suffix=extension or ".tmp",
            dir=directory,
        )
        if existing_mode is not None:
            os.fchmod(fd, existing_mode)
        else:
            current_umask = os.umask(0)
            os.umask(current_umask)
            os.fchmod(fd, 0o666 & ~current_umask)
        os.close(fd)
        fd = None

        # Keep the real destination out of Pandoc's hands entirely. The
        # staging filename retains the requested extension so Pandoc can infer
        # PDF/DOCX/ODT/HTML/plain output exactly as before.
        cmd = ["pandoc", "-f", "markdown"] + list(extra_args or []) + ["-o", temp_path]
        subprocess.run(
            cmd,
            input=source_text,
            check=True,
            capture_output=True,
            text=True,
        )

        # Flush Pandoc's completed output before making it visible at the
        # destination pathname.
        with open(temp_path, "rb") as f:
            os.fsync(f.fileno())

        # Recheck immediately before replacement. This cannot eliminate the
        # tiny OS-level interval between check and rename, but it prevents the
        # practical race where a destination changes during a long export.
        if _disk_snapshot(target_path) != expected_snapshot:
            show_message(
                "Export destination changed",
                "The output file changed while Pandoc was running. The newer file was "
                "left untouched; the staged export was discarded.",
            )
            return False

        os.replace(temp_path, target_path)
        temp_path = None
        show_message("Export complete", f"Wrote {out_path}")
        return True
    except subprocess.CalledProcessError as e:
        show_message("Pandoc error", (e.stderr or str(e)).strip())
        return False
    except (OSError, UnicodeError) as e:
        show_message("Pandoc error", str(e))
        return False
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


def _request_pandoc_export(out_path, source_text, extra_args=None):
    """Validate/confirm an export destination before Pandoc is run."""
    if state.path is not None and _same_document_path(out_path, state.path):
        show_message(
            "Unsafe export path",
            "The export destination is the Markdown file currently open in Carriage. "
            "Choose a different output filename so the source document cannot be replaced.",
        )
        return

    try:
        destination_snapshot = _disk_snapshot(out_path)
    except OSError as e:
        show_message("Error checking export destination", str(e))
        return

    def perform():
        _perform_pandoc_export(
            out_path,
            source_text,
            extra_args or [],
            expected_snapshot=destination_snapshot,
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
    if shutil.which("pandoc") is None:
        show_message(
            "Pandoc not found",
            "pandoc isn't on PATH. Install it (e.g. `sudo dnf install pandoc`)"
            " and try again.",
        )
        return

    def do_export(raw_path):
        out_path = os.path.expanduser(raw_path.strip())
        if not out_path:
            return
        try:
            source_text = _materialize_tables(text_area.text)
        except ValueError as e:
            show_message("Table error", str(e))
            return
        _request_pandoc_export(out_path, source_text, extra_args or [])

    show_input_dialog(
        f"Export as {fmt_label}", "Output path:", _default_export_path(ext), do_export
    )


def do_custom_export():
    path_field = TextArea(
        text=_default_export_path("out"), multiline=False, style="class:input-field"
    )
    args_field = TextArea(
        text="-t html --standalone", multiline=False, style="class:input-field"
    )

    def ok_handler():
        out_path = os.path.expanduser(path_field.text.strip())
        try:
            extra = shlex.split(args_field.text.strip())
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
        if shutil.which("pandoc") is None:
            show_message("Pandoc not found", "pandoc isn't on PATH.")
            return
        try:
            source_text = _materialize_tables(text_area.text)
        except ValueError as e:
            show_message("Table error", str(e))
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
# Spell check (aspell)
# ---------------------------------------------------------------------------

def do_run_aspell():
    if state.path is None:
        show_message(
            "Save first", "Save the file before running the spell checker."
        )
        return

    def proceed():
        do_save(on_saved=_launch_aspell)

    if state.is_modified(text_area.text):
        confirm(
            "Unsaved changes",
            "aspell checks the file on disk. Save your changes first?",
            proceed,
        )
    else:
        _launch_aspell()


def _launch_aspell():
    if shutil.which("aspell") is None:
        show_message(
            "aspell not found",
            "aspell isn't on PATH. Install it (e.g. `sudo dnf install aspell"
            " aspell-en`) and try again.",
        )
        return

    async def run_and_reload():
        cmd = f"aspell --mode=markdown check {shlex.quote(state.path)}"
        state.external_process_running = True
        try:
            await application.run_system_command(cmd, wait_for_enter=False)
        except Exception as e:
            show_message("aspell error", str(e))
            return
        finally:
            state.external_process_running = False

        # aspell edits the file on disk directly - reload it into the buffer
        # and make that exact edited version the new conflict-detection baseline.
        try:
            content, disk_snapshot = _read_utf8_file_with_snapshot(state.path)
        except (OSError, UnicodeError) as e:
            show_message("Error reloading file", str(e))
            return
        visible = _collapse_tables_from_source(content)
        text_area.buffer.reset(Document(text=visible))
        state.saved_text = content
        state.disk_snapshot = disk_snapshot
        state.autosave_conflict = False

    get_app().create_background_task(run_and_reload())


# ---------------------------------------------------------------------------
# Help
# ---------------------------------------------------------------------------

HELP_DIALOG_TEXT_WIDTH = 62


def _wrap_help_text(text, width=HELP_DIALOG_TEXT_WIDTH):
    """Word-wrap Help prose while preserving shortcut/example layout.

    Source line breaks inside ordinary prose are treated as authoring layout,
    not as required display breaks. Consecutive prose lines are joined into a
    paragraph before wrapping, while shortcut rows and indented examples keep
    their intentional structure.
    """
    rendered = []
    paragraph = []

    def flush_paragraph():
        if not paragraph:
            return
        joined = " ".join(part.strip() for part in paragraph)
        rendered.extend(
            textwrap.wrap(
                joined,
                width=width,
                break_long_words=False,
                break_on_hyphens=False,
            ) or [""]
        )
        paragraph.clear()

    for raw_line in text.splitlines():
        if not raw_line.strip():
            flush_paragraph()
            if rendered and rendered[-1] != "":
                rendered.append("")
            continue

        # Shortcut/reference lines use a hanging indent for wrapped descriptions.
        shortcut = re.match(r"^(\S+)(\s{2,})(\S.*)$", raw_line)
        if shortcut:
            flush_paragraph()
            prefix = shortcut.group(1) + shortcut.group(2)
            description = shortcut.group(3)
            chunks = textwrap.wrap(
                description,
                width=max(1, width - len(prefix)),
                break_long_words=False,
                break_on_hyphens=False,
            ) or [""]
            rendered.append(prefix + chunks[0])
            rendered.extend(" " * len(prefix) + chunk for chunk in chunks[1:])
            continue

        # Indented syntax/examples retain their indentation and line identity.
        if raw_line.startswith(" "):
            flush_paragraph()
            indent = raw_line[: len(raw_line) - len(raw_line.lstrip(" "))]
            content = raw_line[len(indent):]
            chunks = textwrap.wrap(
                content,
                width=max(1, width - len(indent)),
                break_long_words=False,
                break_on_hyphens=False,
            ) or [""]
            rendered.extend(indent + chunk for chunk in chunks)
            continue

        paragraph.append(raw_line)

    flush_paragraph()
    while rendered and rendered[-1] == "":
        rendered.pop()
    return "\n".join(rendered)


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
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=help_body)

KEYBINDING_ROWS = [
    ("Ctrl+N", "New file"),
    ("Ctrl+O", "Open file"),
    ("Ctrl+S", "Save"),
    ("Ctrl+Z", "Undo"),
    ("Ctrl+R", "Redo"),
    ("Ctrl+J", "Reflow document to 80 columns"),
    ("Ctrl+Q", "Quit"),
    ("F7", "Spell check with aspell"),
    ("F10", "Open menu bar"),
    ("Ctrl+Space", "Open menu bar"),
    ("Ctrl+Home", "Go to top of document"),
    ("Ctrl+End", "Go to end of document"),
    ("Alt+Up", "Go to previous section"),
    ("Alt+Down", "Go to next section"),
    ("1-7", "Jump to File/Edit/Go/Format/Export/Tools/Help"),
    ("Tab", "Indent to next tab stop; on [[Table N]], open table"),
    ("Esc", "Close menu or dialog"),
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
    """Keep only the practical reminders that do not fit in the cheatsheet."""
    paragraphs = [
        (
            "Selection: Shift+Arrow or Shift+Home/End selects text. "
            "Ctrl+W cuts, Alt+W copies, and Ctrl+Y pastes. "
            "Cut/copy use Carriage's internal clipboard."
        ),
        (
            "Wrapping: Auto-wrap affects ordinary prose at 80 columns. "
            "Ctrl+J reflows prose; structural or ambiguous Markdown is "
            "left unchanged."
        ),
        (
            "Tables: Arrow keys navigate table cells. Enter edits the "
            "selected cell; Enter again commits it. Ctrl+R and Ctrl+C "
            "open row and column commands."
        ),
    ]
    return "\n\n".join(
        textwrap.fill(
            paragraph,
            width=width,
            break_long_words=False,
            break_on_hyphens=False,
        )
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
        "Carriage is a prose-first Markdown editor inspired by the focused "
        "writing experience of a typewriter. It is designed to keep attention "
        "on sentences, paragraphs, and sections rather than on Markdown syntax "
        "or source-code mechanics."
    ),
    (
        "Ordinary prose wraps to an 80-column writing area, while structural "
        "or ambiguous Markdown is left alone rather than interpreted "
        "aggressively. Supported tables are folded into compact references in "
        "the prose view and edited separately, while the file on disk remains "
        "ordinary, portable Markdown."
    ),
    (
        "The guiding principle is simple: help with writing where Carriage can "
        "do so confidently, and preserve the author's text when it cannot."
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
    sections = [
        (
            "Headings",
            [
                "    # H1    ## H2    ...    ###### H6",
            ],
        ),
        (
            "Emphasis",
            [
                "    *italic*  or  _italic_",
                "    **bold**  or  __bold__",
            ],
        ),
        (
            "Lists",
            [
                "    - unordered item",
                "    1. ordered item",
            ],
        ),
        (
            "Blockquotes",
            [
                "    > quoted text",
            ],
        ),
        (
            "Links",
            [
                "    [link text](https://example.com)",
            ],
        ),
        (
            "Hard line breaks",
            [
                "End a line with two spaces or a backslash to force a line break.",
            ],
        ),
        (
            "Tables",
            [
                "Use Tools > Insert Table to create a table, or edit a folded",
                "[[Table N]] reference with Tab or Tools > Edit Table at Cursor.",
            ],
        ),
    ]

    rendered = ["Markdown syntax reference", rule]
    for index, (heading, body_lines) in enumerate(sections):
        rendered.append(heading)
        for line in body_lines:
            if line.startswith("    "):
                rendered.append(line)
            else:
                rendered.extend(
                    textwrap.wrap(
                        line,
                        width=width,
                        break_long_words=False,
                        break_on_hyphens=False,
                    ) or [""]
                )
        if index != len(sections) - 1:
            rendered.append(rule)
    return "\n".join(rendered)


MARKDOWN_HELP_TEXT = _build_markdown_help()

def do_show_help():
    _show_help_reference("Keybindings", HELP_TEXT)


def do_show_markdown_help():
    _show_help_reference("Markdown Syntax Reference", MARKDOWN_HELP_TEXT)


def do_show_about():
    ok_button = Button(text="OK", handler=close_dialog)
    dialog = Dialog(
        title="About Carriage",
        body=Label(text=ABOUT_TEXT, wrap_lines=False),
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
    match = re.match(r"^\s{0,3}#{1,6}(?:[ \t]+|$)(.*)$", line)
    if not match:
        return None
    title = match.group(1).strip()
    # Markdown permits an optional closing run of # characters when it is
    # separated from the title by whitespace. Do not expose those source
    # markers in the prose-oriented status bar.
    title = re.sub(r"[ \t]+#+[ \t]*$", "", title).strip()
    return title


def _current_section_title(doc):
    """Return the nearest Markdown heading at or before the cursor."""
    lines = doc.lines
    if not lines:
        return None

    cursor_row = doc.cursor_position_row
    fenced_lines = _highlight_fenced_lines(lines)
    current = None

    for row in range(0, min(cursor_row, len(lines) - 1) + 1):
        if row in fenced_lines:
            continue

        title = _heading_title(lines[row])
        if title is not None:
            current = title
            continue

        if (
            row + 1 < len(lines)
            and row + 1 not in fenced_lines
            and _HIGHLIGHT_SETEXT_RE.match(lines[row + 1])
            and lines[row].strip()
        ):
            current = lines[row].strip()

    return current


def _document_progress(doc):
    """Return cursor progress through the visible document as 0-100 percent."""
    if not doc.text:
        return 0
    return max(0, min(100, round(100 * doc.cursor_position / len(doc.text))))


def _document_heading_rows(doc):
    """Return visible Markdown heading rows in document order."""
    lines = doc.lines
    if not lines:
        return []

    fenced_lines = _highlight_fenced_lines(lines)
    rows = []

    for row, line in enumerate(lines):
        if row in fenced_lines:
            continue

        if _heading_title(line) is not None:
            rows.append(row)
            continue

        if (
            row + 1 < len(lines)
            and row + 1 not in fenced_lines
            and _HIGHLIGHT_SETEXT_RE.match(lines[row + 1])
            and line.strip()
        ):
            rows.append(row)

    return rows


def _move_editor_to_row(row):
    """Move the prose-editor cursor to column zero of a logical row."""
    doc = text_area.buffer.document
    if not doc.lines:
        text_area.buffer.cursor_position = 0
        return

    row = max(0, min(len(doc.lines) - 1, row))
    text_area.buffer.cursor_position = doc.translate_row_col_to_index(row, 0)
    get_app().invalidate()


def do_go_top():
    text_area.buffer.cursor_position = 0
    get_app().invalidate()


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
    on_setext_title = (
        cursor_row + 1 < len(doc.lines)
        and _HIGHLIGHT_SETEXT_RE.match(doc.lines[cursor_row + 1])
        and doc.lines[cursor_row].strip()
    )
    strict = current_title is not None or on_setext_title

    for row in headings:
        if row < cursor_row or (row == cursor_row and not strict):
            target = row
        elif row >= cursor_row:
            break

    if target is not None:
        _move_editor_to_row(target)


def do_go_next_section():
    """Jump to the nearest heading below the cursor, if any."""
    doc = text_area.buffer.document
    cursor_row = doc.cursor_position_row
    for row in _document_heading_rows(doc):
        if row > cursor_row:
            _move_editor_to_row(row)
            return


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
        + 15  # wrap/save field
        + 20  # command hint
        + (3 * 4)  # four " | " separators
        + 2  # outer padding
    )
    available = max(1, terminal_columns - fixed_other_width)
    desired = max(16, round(terminal_columns * 0.38))
    return max(1, min(60, desired, available))


def _status_section_field(title, terminal_columns):
    width = _status_section_width(terminal_columns)
    label = f"§ {title}" if title else "§"
    return _fit_status_field(label, width)


def get_statusbar_text():
    doc = text_area.buffer.document
    try:
        count_text = _materialize_tables(text_area.text)
    except ValueError:
        count_text = text_area.text

    words = len(re.findall(r"\S+", count_text))
    section = _current_section_title(doc)
    progress = _document_progress(doc)
    wrap_status = "on" if state.auto_wrap else "off"
    save_status = "on" if state.auto_save else "off"

    try:
        terminal_columns = get_app().output.get_size().columns
    except Exception:
        terminal_columns = 80

    section_field = _status_section_field(section, terminal_columns)
    word_field = f"{words:,} words".ljust(15)
    progress_field = f"{progress:>3}%"
    state_field = f"wrap:{wrap_status} save:{save_status}"
    command_field = "^Space menu  ^Q quit"

    # Keep navigation information together at the left, followed by
    # document/editor state and finally command hints.
    status = " | ".join(
        [progress_field, section_field, word_field, state_field, command_field]
    )
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

body = HSplit(
    [
        Window(height=1, style="class:editor"),
        text_area,
        Window(height=1, char="─", style="class:divider"),
        Window(content=FormattedTextControl(get_statusbar_text), height=1, style="class:status"),
    ]
)

menu_container = MenuContainer(
    body=body,
    menu_items=[
        MenuItem(
            "  File  ",
            children=[
                MenuItem("New          Ctrl+N", handler=with_unsaved_changes_check(do_new)),
                MenuItem("Open...      Ctrl+O", handler=with_unsaved_changes_check(do_open)),
                MenuItem("Save         Ctrl+S", handler=do_save),
                MenuItem("Save As...", handler=do_save_as),
                MenuItem("-", disabled=True),
                MenuItem("Quit         Ctrl+Q", handler=with_unsaved_changes_check(do_quit)),
            ],
        ),
        MenuItem(
            "  Edit  ",
            children=[
                MenuItem("Undo         Ctrl+Z", handler=do_undo),
                MenuItem("Redo         Ctrl+R", handler=do_redo),
                MenuItem("-", disabled=True),
                MenuItem("Cut          Ctrl+W", handler=do_cut),
                MenuItem("Copy         Alt+W", handler=do_copy),
                MenuItem("Paste        Ctrl+Y", handler=do_paste),
            ],
        ),
        MenuItem(
            "  Go  ",
            children=[
                MenuItem("Top of Document      Ctrl+Home", handler=do_go_top),
                MenuItem("End of Document      Ctrl+End", handler=do_go_end),
                MenuItem("-", disabled=True),
                MenuItem("Previous Section     Alt+Up", handler=do_go_previous_section),
                MenuItem("Next Section         Alt+Down", handler=do_go_next_section),
            ],
        ),
        MenuItem(
            "  Format  ",
            children=[
                MenuItem("Reflow Document   Ctrl+J", handler=do_reflow_document),
                MenuItem("Toggle Auto-Wrap", handler=do_toggle_autowrap),
                MenuItem("Toggle Auto-Save", handler=do_toggle_autosave),
            ],
        ),
        MenuItem(
            "  Export  ",
            children=[
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
                MenuItem(
                    "Plain text (.txt)",
                    handler=lambda: export_via_pandoc("plain text", "txt", ["-t", "plain"]),
                ),
                MenuItem("Custom pandoc command...", handler=do_custom_export),
            ],
        ),
        MenuItem(
            "  Tools  ",
            children=[
                MenuItem("Spell Check (aspell)   F7", handler=do_run_aspell),
                MenuItem("-", disabled=True),
                MenuItem("Insert Table...", handler=do_insert_table),
                MenuItem("Edit Table at Cursor   Tab", handler=do_edit_table_at_cursor),
            ],
        ),
        MenuItem(
            "  Help  ",
            children=[
                MenuItem("Keybindings", handler=do_show_help),
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

editor_focused = Condition(lambda: get_app().layout.has_focus(text_area))

kb = KeyBindings()


@kb.add("c-n", filter=editor_focused)
def _(event):
    with_unsaved_changes_check(do_new)()


@kb.add("c-o", filter=editor_focused)
def _(event):
    with_unsaved_changes_check(do_open)()


@kb.add("c-s", filter=editor_focused)
def _(event):
    do_save()


@kb.add("c-q", filter=editor_focused)
def _(event):
    with_unsaved_changes_check(do_quit)()


@kb.add("c-j", filter=editor_focused)
def _(event):
    do_reflow_document()


@kb.add("c-home", filter=editor_focused)
def _(event):
    do_go_top()


@kb.add("c-end", filter=editor_focused)
def _(event):
    do_go_end()


# Most terminals encode Alt+Arrow as Escape followed by the arrow key.
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


@kb.add("f7", filter=editor_focused)
def _(event):
    do_run_aspell()


no_dialog_open = Condition(lambda: current_float is None)
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


@kb.add("tab", filter=editor_focused & cursor_on_table_reference)
def _(event):
    do_edit_table_at_cursor()


@kb.add("tab", filter=editor_focused & ~cursor_on_table_reference)
def _(event):
    # prompt_toolkit displays literal tab characters as ^I. In the prose
    # editor, make Tab behave like a conventional indentation key instead:
    # insert spaces up to the next four-column tab stop. Folded table
    # references keep their special Tab behavior above.
    col = event.current_buffer.document.cursor_position_col
    spaces = TAB_WIDTH - (col % TAB_WIDTH)
    event.current_buffer.insert_text(" " * spaces)


def _move_editor_cursor_across_lines(delta):
    """Move one visible character left/right, crossing newline boundaries."""
    buf = text_area.buffer
    text = buf.text
    pos = buf.cursor_position

    if delta > 0:
        # TABLE_SENTINEL is an internal zero-width marker attached to folded
        # table references. Skip it without consuming a visible cursor step.
        while pos < len(text) and text[pos] == TABLE_SENTINEL:
            pos += 1
        if pos < len(text):
            pos += 1
        while pos < len(text) and text[pos] == TABLE_SENTINEL:
            pos += 1
    elif delta < 0:
        while pos > 0 and text[pos - 1] == TABLE_SENTINEL:
            pos -= 1
        if pos > 0:
            pos -= 1
        while pos > 0 and text[pos - 1] == TABLE_SENTINEL:
            pos -= 1

    buf.cursor_position = pos


@kb.add("right", filter=editor_focused)
def _(event):
    _move_editor_cursor_across_lines(1)


@kb.add("left", filter=editor_focused)
def _(event):
    _move_editor_cursor_across_lines(-1)


@kb.add("c-s", filter=table_editor_active)
def _(event):
    _save_table_editor()


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
    ("7", 6),
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
        "help-text": f"bg:{EF_BG2} {EF_FG}",
    }
)

application = Application(
    layout=layout,
    key_bindings=kb,
    style=style,
    mouse_support=True,
    full_screen=True,
    # Without this, prompt_toolkit's default color depth is 256-color, not
    # true 24-bit - our exact hex values would get approximated to the
    # nearest of 256 colors, which can quietly collapse contrast between
    # similar tones. Kitty (and virtually every modern terminal) supports
    # real 24-bit color, so ask for it explicitly.
    color_depth=ColorDepth.DEPTH_24_BIT,
    cursor=SimpleCursorShapeConfig(cursor_shape=CursorShape.BEAM),
)


def _start_background_tasks(startup_error=None, offer_recovery=False):
    application.create_background_task(_autosave_loop())
    if startup_error is not None:
        title, message = startup_error
        show_message(title, message)
    elif offer_recovery:
        _offer_stale_recovery()


def main():
    startup_error = None

    if len(sys.argv) > 1:
        path = os.path.expanduser(sys.argv[1])
        if os.path.exists(path):
            try:
                content, disk_snapshot = _read_utf8_file_with_snapshot(path)
            except (OSError, UnicodeError) as e:
                # Start the editor rather than crashing before the UI exists;
                # display the error as soon as the application is running.
                startup_error = ("Error opening file", f"{path}\n\n{e}")
            else:
                text_area.text = _collapse_tables_from_source(content)
                state.path = path
                state.saved_text = content
                state.disk_snapshot = disk_snapshot
        else:
            state.path = path  # new file at this path on first save
            state.disk_snapshot = _MISSING_DISK_SNAPSHOT

    application.run(
        pre_run=lambda: _start_background_tasks(
            startup_error, offer_recovery=(len(sys.argv) == 1)
        )
    )


if __name__ == "__main__":
    main()
