#!/usr/bin/env python3
"""
Carriage - A prose-first Markdown editor for the terminal.

Carriage is designed primarily for writing and revising prose in Markdown files.
It provides a full-screen prompt_toolkit interface with mouse support, menus,
keyboard shortcuts, autosave, spell checking, and Pandoc export. F10 or
Ctrl+Space activates the menu bar; while it is active, number keys 1 through 6
jump directly among the top-level menus.
A dedicated Go menu provides document and section navigation without changing
the text.

While typing, ordinary paragraph prose wraps automatically at 80 columns.
Explicit Markdown hard breaks are preserved, and long tokens such as URLs are
left intact rather than split. Text that looks structural or ambiguous is left
alone instead of being reformatted speculatively.

Edit > Reflow Document (Ctrl+J) cleans up prose across the document. It
rewraps ordinary paragraphs, preserves explicit hard breaks, and handles only
simple flat lists and simple single-level blockquotes. Code, tables, YAML,
raw block HTML, complex containers, delimiter-style blocks, and other
structural-looking regions are treated as opaque and copied unchanged.

File operations include New, Open, Save, and Save As. Saves and autosaves use
a temporary file followed by atomic replacement so a failed write does not
truncate the existing file. Autosave runs every 30 seconds for named files.
Independently, every modified document receives a private crash-recovery
snapshot on the same interval, including in-progress table-editor work. Source
autosaves pause while aspell or a modal dialog is active; recovery does not.

The Tools menu can hand a saved document to aspell in Markdown mode and reload
the edited file afterward. The Export menu sends the current buffer to Pandoc
for PDF, DOCX, ODT, HTML, plain-text, or custom-command output.

The interface uses an Everforest dark palette, a transparent editor canvas,
mouse-enabled scrolling, and modal dialogs with safe nested error handling. On
wide terminals, the 80-column prose area is centered while list markers and ATX
heading markers hang into the existing left margin; the scrollbar stays flush
against the far-right edge. Narrow terminals use the available width.
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
  ./carriage_v1.33.py [file.md]
"""

import asyncio
import copy
from functools import lru_cache
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
from html.parser import HTMLParser
from dataclasses import dataclass, field

from prompt_toolkit.application import Application
from prompt_toolkit.cursor_shapes import CursorShape, SimpleCursorShapeConfig
from prompt_toolkit.output.color_depth import ColorDepth
from prompt_toolkit.application.current import get_app
from prompt_toolkit.document import Document
from prompt_toolkit.data_structures import Point
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
from prompt_toolkit.layout.processors import Processor, Transformation
from prompt_toolkit.layout.utils import explode_text_fragments
from prompt_toolkit.layout.dimension import D
from prompt_toolkit.layout.layout import Layout
from prompt_toolkit.layout.margins import Margin
from prompt_toolkit.mouse_events import MouseButton, MouseEvent, MouseEventType
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
APP_VERSION = "1.33"

WRAP_COLUMN = 80
STRUCTURE_GUTTER_WIDTH = 8
TAB_WIDTH = 4
AUTOSAVE_INTERVAL_SECONDS = 30
RECOVERY_FORMAT_VERSION = 2
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
        # Hidden crash-recovery state for the current working document.
        # Recovery is deliberately independent of ordinary autosave: it protects
        # named and untitled documents, including an in-progress table-editor
        # draft, and is removed after a successful Save, New, Open, or clean
        # discard/quit.
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


def _prose_layout_widths(columns):
    """Return left padding, structural gutter, and right padding.

    The 80-column prose body stays centered exactly where it did before the
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
    scrollbar_width = 1
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

            def content_handler(mouse_event):
                y = min(content_y_max - 1, mouse_event.position.y)
                x = mouse_event.position.x

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
                            return self._mouse_handler(mouse_event)
                        return result
                    x -= 1

                return self._mouse_handler(mouse_event)

            mouse_handlers.set_mouse_handler_for_range(
                x_min=content_x_min,
                x_max=content_x_max,
                y_min=content_y_min,
                y_max=content_y_max,
                handler=content_handler,
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
# visual only: ATX headings and inline bold/italic emphasis get styled, while
# the underlying buffer remains untouched. Fenced code blocks are left
# unhighlighted so prose markers inside code do not masquerade as Markdown.
_HIGHLIGHT_ATX_RE = re.compile(r"^\s{0,3}#{1,6}(?:\s|$)")
_HIGHLIGHT_FENCE_RE = re.compile(r"^\s{0,3}(`{3,}|~{3,})")

# Order matters: triple emphasis before bold, then italic. The patterns are
# intentionally conservative; Carriage is not trying to be a complete Markdown
# parser merely to color prose. DOTALL is deliberate: hard-wrapped prose can
# place the opening emphasis delimiter on one physical line and the closing
# delimiter on a later physical line within the same paragraph/list item.
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
    r")",
    re.DOTALL,
)

_HIGHLIGHT_LIST_ITEM_RE = re.compile(r"^\s{0,3}(?:[-*+]|\d+[.)])\s+")
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


def _highlight_style_for_match(match):
    if match.lastgroup == "strong_em":
        return "class:markdown.bold-italic"
    if match.lastgroup == "strong":
        return "class:markdown.bold"
    return "class:markdown.italic"


def _highlight_inline_markdown(line):
    """Return prompt_toolkit fragments for bold/italic spans in one line."""
    fragments = []
    pos = 0

    for match in _HIGHLIGHT_INLINE_RE.finditer(line):
        if match.start() > pos:
            fragments.append(("", line[pos:match.start()]))
        fragments.append((_highlight_style_for_match(match), match.group(0)))
        pos = match.end()

    if pos < len(line):
        fragments.append(("", line[pos:]))

    return fragments or [("", line)]


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
    styles = [""] * len(combined)

    for match in _HIGHLIGHT_INLINE_RE.finditer(combined):
        style_name = _highlight_style_for_match(match)
        for index in range(match.start(), match.end()):
            if combined[index] != "\n":
                styles[index] = style_name

    rendered = []
    offset = 0
    for line in block_lines:
        fragments = []
        if not line:
            rendered.append([("", "")])
            offset += 1
            continue

        line_styles = styles[offset:offset + len(line)]
        run_start = 0
        current_style = line_styles[0] if line_styles else ""
        for index in range(1, len(line)):
            if line_styles[index] != current_style:
                fragments.append((current_style, line[run_start:index]))
                run_start = index
                current_style = line_styles[index]
        fragments.append((current_style, line[run_start:]))
        rendered.append(fragments)
        offset += len(line) + 1

    return rendered


def _highlight_special_line(line, row, fenced_lines):
    """Return fixed fragments for structural lines, or None for prose."""
    if row in fenced_lines:
        return [("", line)]
    if TABLE_PLACEHOLDER_RE.match(line):
        return [("class:markdown.table-ref", line)]
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
            starts_list_item = bool(_HIGHLIGHT_LIST_ITEM_RE.match(lines[row]))
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
                if not starts_list_item and _HIGHLIGHT_LIST_ITEM_RE.match(lines[row]):
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


class ProseLayoutProcessor(Processor):
    """Render structural Markdown in a hanging gutter beside 80-column prose.

    The source buffer remains ordinary Markdown. This processor adds only
    display-space: supported list/ATX prefixes hang into the left gutter, and
    temporarily overlong physical source lines receive invisible right-edge
    padding at word boundaries so prompt_toolkit soft-wraps before the next
    word instead of cutting that word in half.

    The display-only padding never changes the Markdown buffer. Hard-wrapped
    source remains authoritative, and source/display mappings stay explicit so
    mouse placement and cursor movement continue to address real buffer
    positions.
    """

    def apply_transformation(self, ti):
        # The Window width is the hanging gutter + 80 prose cells + one spare
        # cursor cell on wide terminals. The spare cell gives the insertion
        # point after an exactly 80-column line a real screen position.
        gutter = max(0, min(STRUCTURE_GUTTER_WIDTH, ti.width - (WRAP_COLUMN + 1)))
        prefix_width = _display_structural_prefix_width(ti.document.text, ti.lineno)
        if prefix_width > gutter:
            # There is not enough left-side room to hang this marker without
            # stealing prose width. Fall back to ordinary source display.
            prefix_width = 0

        padding = max(0, gutter - prefix_width)
        fragments = explode_text_fragments(ti.fragments)
        source_length = len(fragments)

        result = []
        source_to_display_map = {}
        display_to_source_map = {}
        display_pos = 0

        # Display-only left padding. Clicking in it maps to source column zero.
        for _ in range(padding):
            result.append(("", " "))
            display_to_source_map[display_pos] = 0
            display_pos += 1

        def append_display_padding(count, source_pos):
            nonlocal display_pos
            for _ in range(max(0, count)):
                result.append(("", " "))
                display_to_source_map[display_pos] = source_pos
                display_pos += 1

        def next_word_width(start):
            """Display width of the next ordinary word after `start`."""
            width = 0
            found = False
            for index in range(start, source_length):
                char = fragments[index][1]
                if char.isspace():
                    if found:
                        break
                    continue
                found = True
                width += max(0, get_cwidth(char))
            return width

        # Number of display cells occupied by prose on the current visual row.
        # Structural source characters are rendered in the hanging gutter and
        # therefore do not consume this 80-column prose budget.
        body_col = 0

        for source_pos, fragment in enumerate(fragments):
            char = fragment[1]
            in_body = source_pos >= prefix_width

            if in_body and char != " " and body_col >= WRAP_COLUMN:
                # A token with no usable preceding separator has reached the
                # edge. Reserve the private cursor cell so prompt_toolkit wraps
                # the next source character onto the following visual row.
                fill = max(0, (WRAP_COLUMN + 1) - body_col)
                append_display_padding(fill, source_pos)
                body_col = 0

            source_to_display_map[source_pos] = display_pos
            display_to_source_map[display_pos] = source_pos
            result.append(fragment)
            display_pos += 1

            if not in_body:
                continue

            char_width = max(0, get_cwidth(char))
            body_col += char_width

            if char == " ":
                word_width = next_word_width(source_pos + 1)
                if (
                    0 < word_width <= WRAP_COLUMN
                    and body_col + word_width > WRAP_COLUMN
                ):
                    # Fill the remainder of this visual row, including the
                    # private cursor cell. The next source character then wraps
                    # naturally before the word. This is display-only: the one
                    # real Markdown separator remains the only source space.
                    fill = max(0, (WRAP_COLUMN + 1) - body_col)
                    append_display_padding(fill, source_pos)
                    body_col = 0

        source_to_display_map[source_length] = display_pos
        display_to_source_map[display_pos] = source_length

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
    """Align display-only soft-wrap continuations with the prose column."""
    if wrap_count <= 0:
        return []
    try:
        columns = get_app().output.get_size().columns
    except Exception:
        columns = WRAP_COLUMN + 1
    _left, gutter, _right = _prose_layout_widths(columns)
    if gutter <= 0:
        return []
    return [("class:editor", " " * gutter)]


class FullWidthSafeBufferControl(BufferControl):
    """Focus and position the prose editor on the same mouse click."""

    def mouse_handler(self, mouse_event):
        if mouse_event.event_type == MouseEventType.MOUSE_DOWN:
            app = get_app()
            if app.layout.current_control is not self:
                app.layout.current_control = self
        return super().mouse_handler(mouse_event)


text_area = TextArea(
    text="",
    lexer=ProseMarkdownLexer(),
    wrap_lines=True,
    scrollbar=True,
    focus_on_click=True,
    input_processors=[ProseLayoutProcessor()],
    style="class:editor",
)
text_area.control.__class__ = FullWidthSafeBufferControl
text_area.window.__class__ = ScrollableWindow
text_area.window.on_scrollbar_interact = _on_scrollbar_interact
# Keep display-only continuations aligned with the prose column. The layout
# processor pads only at word boundaries, so overlong/unreflowed source remains
# visible without horizontal scrolling or mid-word visual splits.
text_area.window.get_line_prefix = _soft_wrap_line_prefix
# Keep the prose body at exactly 80 display columns on wide terminals. The
# ProseLayoutProcessor borrows part of the existing left-side breathing room as
# a hanging structural gutter, with one spare cursor cell after the prose body.
# The Window remains full-width so the scrollbar stays flush right.
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
    """Read one regular UTF-8 file and fingerprint exactly the bytes read.

    Open the path nonblocking where the platform supports it, then validate
    the opened descriptor with fstat() before reading. This closes the unsafe
    gap where a FIFO, device, directory, or a path swapped to one of those
    could otherwise block or stream unbounded data during File > Open.
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

        with os.fdopen(fd, "rb") as f:
            fd = None  # fdopen owns and closes the descriptor now.
            raw = f.read()
    finally:
        if fd is not None:
            os.close(fd)

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


def _table_from_recovery_record(raw_table):
    if not isinstance(raw_table, dict):
        raise ValueError("Recovery file contains invalid table data.")
    return TableData(
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


def _table_content_key(table):
    """Return the editable table content, excluding bookkeeping metadata."""
    return (
        tuple(table.headers),
        tuple(tuple(row) for row in table.rows),
        tuple(table.alignments),
    )


def _active_table_draft():
    """Return a snapshot of the active table editor without committing it.

    The text currently present in an actively edited cell is folded into the
    snapshot using the same newline normalization as a real cell commit. The
    live table-editor session is never mutated by crash recovery.
    """
    session = current_table_editor
    if session is None:
        return None

    working = copy.deepcopy(session.working)
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
    if draft is None:
        return False
    table_number, working = draft
    committed = state.tables.get(table_number)
    return committed is None or _table_content_key(working) != _table_content_key(committed)


def _recovery_payload():
    """Capture all recoverable editor state, including an active table draft."""
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

    source_path = _canonical_path(state.path) if state.path is not None else None
    disk_snapshot = None if state.disk_snapshot is None else list(state.disk_snapshot)

    return {
        "format": RECOVERY_FORMAT_VERSION,
        "pid": os.getpid(),
        "source_path": source_path,
        "saved_text": state.saved_text,
        "disk_snapshot": disk_snapshot,
        "cursor_position": text_area.buffer.cursor_position,
        "visible_text": text_area.text,
        "tables": tables,
        "had_table_draft": had_table_draft,
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
            directory, f"recovery-{os.getpid()}-{token}.json"
        )
    return state.recovery_path


def _write_recovery_snapshot():
    """Atomically persist the current working document for crash recovery."""
    if not _has_recoverable_changes():
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

    # v1 is the untitled-only format written by Carriage 1.06. Keep accepting
    # it so upgrading Carriage cannot strand an existing recovery file.
    version = payload.get("format")
    if version not in (1, RECOVERY_FORMAT_VERSION):
        raise ValueError("Unsupported Carriage recovery format.")
    if not isinstance(payload.get("visible_text"), str):
        raise ValueError("Recovery file does not contain document text.")
    if not isinstance(payload.get("tables"), dict):
        raise ValueError("Recovery file contains invalid table data.")

    if version == 1:
        payload.setdefault("source_path", None)
        payload.setdefault("saved_text", "")
        payload.setdefault("disk_snapshot", None)
        payload.setdefault("cursor_position", len(payload["visible_text"]))
        payload.setdefault("had_table_draft", False)
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
        if not (
            name.endswith(".json")
            and (name.startswith("recovery-") or name.startswith("untitled-"))
        ):
            continue
        path = os.path.join(directory, name)
        try:
            payload = _read_recovery_payload(path)
            pid = payload.get("pid")
            if _process_is_running(pid):
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
    payload = _read_recovery_payload(path)
    restored_tables = {}
    for raw_number, raw_table in payload["tables"].items():
        number = int(raw_number)
        restored_tables[number] = _table_from_recovery_record(raw_table)

    state.tables = restored_tables
    visible_text = payload["visible_text"]
    cursor_position = payload.get("cursor_position", len(visible_text))
    if not isinstance(cursor_position, int):
        cursor_position = len(visible_text)
    cursor_position = max(0, min(len(visible_text), cursor_position))
    text_area.buffer.reset(
        Document(text=visible_text, cursor_position=cursor_position)
    )

    source_path = payload.get("source_path")
    state.path = source_path if isinstance(source_path, str) and source_path else None
    saved_text = payload.get("saved_text", "")
    state.saved_text = saved_text if isinstance(saved_text, str) else ""

    raw_snapshot = payload.get("disk_snapshot")
    if (
        isinstance(raw_snapshot, list)
        and len(raw_snapshot) == 2
        and isinstance(raw_snapshot[0], str)
    ):
        state.disk_snapshot = tuple(raw_snapshot)
    else:
        state.disk_snapshot = None

    state.autosave_conflict = False
    state.recovery_path = path
    state.recovery_error = False

    # Claim the restored journal for this process immediately so a second
    # concurrently running Carriage instance will not offer it as stale.
    _write_recovery_snapshot()


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
            f'Carriage found unsaved work for "{document_label}" from an earlier '
            "session that did not close normally. Restore it?"
        )
    else:
        description = (
            "Carriage found an untitled document recovery from an earlier "
            "session that did not close normally. Restore it?"
        )

    if payload.get("had_table_draft"):
        description += "\n\nThe recovery includes an in-progress table edit."

    extra = len(recoveries) - 1
    if extra:
        description += (
            f"\n\n{extra} older recovery file{'s' if extra != 1 else ''} "
            "will remain available."
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
        _offer_stale_recovery(source_path)

    restore_button = Button(text="Restore", handler=restore_handler)
    discard_button = Button(text="Discard", handler=discard_handler)
    later_button = Button(text="Later", handler=close_dialog)
    dialog = Dialog(
        title="Recover document?",
        body=Label(text=description),
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


@dataclass
class _WrapBlock:
    """A logical prose/list block that both wrapping paths can render."""

    kind: str
    start: int
    end: int
    source_lines: list[str]
    marker: str | None = None
    body_lines: list[str] | None = None
    # For a contiguous simple list, every item shares one prose width based
    # on the widest marker in that list. This keeps source lines at or below
    # WRAP_COLUMN without adding fake padding after shorter markers.
    wrap_width: int | None = None
    list_items: list["_WrapBlock"] | None = None


def _simple_list_fragment_is_safe(text):
    """Return True only for prose Carriage can safely treat as list content.

    This check is applied to both the first line (after its list marker) and
    every continuation line (after only a recognized continuation indent has
    been removed). Keeping this structural test in one place prevents live
    wrapping and Ctrl+J from disagreeing about what a "simple list" means.
    """
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
        or _DEFINITION_MARKER_RE.match(text)
        or _OTHER_LIST_RE.match(text)
        or _is_thematic_break(text)
        or _generic_fence_marker(text)
        or stripped.startswith("|")
        or _GRID_BORDER_RE.match(text)
        or _SIMPLE_TABLE_SEPARATOR_RE.match(text)
        or _is_pipe_table_separator(text)
        or _looks_structural_or_ambiguous(text)
    )


def _simple_list_continuation(line, marker_prefix, allow_lazy=False):
    """Return prose content for one supported simple-list continuation.

    Canonical continuation lines use the hanging indent implied by the full
    marker prefix. Markdown also permits a paragraph inside a list item to use
    a *lazy continuation* with no indentation. Ctrl+J/live wrapping may accept
    that valid form and normalize it when reflowing. Display-only gutter logic
    keeps ``allow_lazy`` false so it never hides source characters that are not
    actually indentation.
    """
    hanging_indent = len(marker_prefix)
    leading_spaces = len(line) - len(line.lstrip(" "))
    if leading_spaces == hanging_indent:
        return line[hanging_indent:]
    if allow_lazy and leading_spaces == 0:
        return line
    return None


def _parse_simple_list_item(lines, index, limit=None):
    """Parse one flat prose list item into the shared wrapping model.

    Return None when the item contains nested lists, headings, blockquotes,
    code-like indentation, raw HTML, noncanonical continuation indentation, or
    other structure that should remain opaque. Carriage does not repair list
    syntax: wrapping is allowed only when every physical line is confidently
    valid simple prose belonging to this one item.
    """
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
            # A differently indented marker is a nested/complex list.
            return None

        continuation = _simple_list_continuation(
            lines[i], marker, allow_lazy=True
        )
        if continuation is None:
            return None
        candidate = continuation

        # This catches nested markers that only become visible after removing
        # a four-character hanging indent, e.g. "10. parent" followed by
        # "    - nested child".
        if not _simple_list_fragment_is_safe(candidate):
            return None

        body.append(candidate)
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
    """Return a conservative family key for one simple Markdown list marker."""
    marker_text = marker_prefix.strip()
    if marker_text and marker_text[0].isdigit():
        return ("ordered", marker_text[-1])
    return ("unordered", marker_text[:1])


def _list_run_marker_budget(lines, index, limit, base_indent, family):
    """Return the widest top-level marker in the surrounding flat list run.

    This scan is intentionally shallower than the simple-item parser.  A
    complex item may remain verbatim, but its top-level marker still counts
    toward the source-width budget used by neighboring simple items.  That
    keeps Option 2 stable across the whole contiguous list without requiring
    every item to be simple enough for Carriage to reflow.
    """
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


def _parse_simple_list_run(lines, index, limit=None, width=WRAP_COLUMN):
    """Parse the longest simple prefix of one contiguous flat list.

    Ctrl+J must keep walking the document even when one list item contains
    unsupported structure.  Therefore a complex item ends the current simple
    prefix instead of invalidating every preceding item in the same nonblank
    run.  The surrounding list's widest top-level marker still determines the
    shared prose budget for the simple items that Carriage can safely wrap.
    """
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


def _complex_list_item_end(lines, index, limit=None):
    """Return the end of one unsupported top-level list item.

    Preserve only the item Carriage cannot safely understand, not the entire
    surrounding nonblank run.  This lets Ctrl+J resume at the next top-level
    item and continue hard-wrapping the rest of the document.
    """
    if not (0 <= index < len(lines)):
        return index + 1

    first = _LIST_ITEM_RE.match(lines[index])
    if first is None:
        return index + 1

    end_limit = len(lines) if limit is None else min(limit, len(lines))
    base_indent = len(lines[index]) - len(lines[index].lstrip(" "))
    i = index + 1
    while i < end_limit and lines[i].strip():
        match = _LIST_ITEM_RE.match(lines[i])
        if match is not None:
            indent = len(lines[i]) - len(lines[i].lstrip(" "))
            if indent == base_indent:
                break
        i += 1
    return i


def _make_plain_prose_block(lines, start, end):
    """Return a shared prose block when the requested range is plain prose."""
    if not (0 <= start < end <= len(lines)):
        return None
    for line in lines[start:end]:
        if not line.strip():
            return None
    return _WrapBlock(
        kind="prose",
        start=start,
        end=end,
        source_lines=list(lines[start:end]),
    )


def _render_wrap_block(block, width=WRAP_COLUMN):
    """Render a shared prose/list block to the requested physical width."""
    if block.kind == "prose":
        return _wrap_markdown_prose(block.source_lines, width=width)

    if block.kind == "list" and block.marker is not None:
        # List prose uses the shared budget of its containing list when one is
        # available. Otherwise a standalone item subtracts its own complete
        # marker prefix. Structural markers can still hang in the display
        # gutter, but they count toward the 80-character Markdown source line.
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

    return list(block.source_lines)


def _collect_simple_list(lines, index, width):
    """Reflow a contiguous flat list through the shared wrap engine."""
    end = _nonblank_run_end(lines, index)
    run = _parse_simple_list_run(lines, index, limit=end, width=width)
    if run is None or run.end != end:
        return None, end
    return _render_wrap_block(run, width=width), end


_ATX_DISPLAY_PREFIX_RE = re.compile(r"^\s{0,3}#{1,6}(?:[ \t]+|$)")


@lru_cache(maxsize=8)
def _structural_display_map(full_text):
    """Return display metadata for safely supported hanging structures.

    The map is presentation-only. It does not repair or reinterpret malformed
    Markdown. Only ATX headings and simple flat list items accepted by the
    shared wrapping parser participate; everything else displays verbatim.
    """
    lines = full_text.split("\n")
    result = {}
    fenced_lines = _highlight_fenced_lines(lines)
    yaml_end = _yaml_front_matter_end(lines)
    i = 0

    while i < len(lines):
        if (yaml_end is not None and i < yaml_end) or i in fenced_lines:
            i += 1
            continue

        heading = _ATX_DISPLAY_PREFIX_RE.match(lines[i])
        if heading is not None:
            result[i] = (len(heading.group(0)), "heading")
            i += 1
            continue

        list_match = _LIST_ITEM_RE.match(lines[i])
        if list_match is not None:
            if _row_in_multiline_opaque_block(lines, i) or _is_indented_code(lines[i]):
                i += 1
                continue

            # Display mapping is intentionally more local than the strict
            # wrapping parser. A temporarily malformed following line must not
            # invalidate the marker/gutter mapping for a valid item above it.
            # Hang this valid marker, then consume only canonical continuation
            # lines that are independently safe. Stop at the first line that
            # does not belong to this simple display item and let the outer
            # scan interpret that line on its own.
            marker = list_match.group(1)
            prefix_width = len(marker)
            result[i] = (prefix_width, "list-marker")

            run_end = _nonblank_run_end(lines, i)
            row = i + 1
            while row < run_end:
                if _LIST_ITEM_RE.match(lines[row]) is not None:
                    break
                continuation = _simple_list_continuation(lines[row], marker)
                if continuation is None or not _simple_list_fragment_is_safe(continuation):
                    break
                result[row] = (prefix_width, "list-continuation")
                row += 1

            i = max(i + 1, row)
            continue

        i += 1

    return result


def _display_structural_prefix_width(full_text, row):
    """Return source columns that visually occupy the hanging gutter."""
    info = _structural_display_map(full_text).get(row)
    return info[0] if info is not None else 0


def _list_continuation_prefix_width(document, row):
    """Return canonical continuation indentation for this row, if any."""
    info = _structural_display_map(document.text).get(row)
    if info is None or info[1] != "list-continuation":
        return None
    return info[0]


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
    )


def _append_reflow_block(blocks, gap_before, kind, block_lines):
    if block_lines:
        blocks.append((gap_before, kind, block_lines))


def _should_insert_missing_blank(previous_kind, current_kind):
    """Normalize spacing only between structures we intentionally understand."""
    if previous_kind in {"opaque", "yaml"} or current_kind in {"opaque", "yaml"}:
        return False
    return previous_kind != current_kind or current_kind != "prose"


def _find_live_wrap_block(lines, row):
    """Return the same logical wrap block Ctrl+J would use around `row`."""
    if not (0 <= row < len(lines)) or not lines[row].strip():
        return None

    yaml_end = _yaml_front_matter_end(lines)
    if yaml_end is not None and row < yaml_end:
        return None
    if _row_in_multiline_opaque_block(lines, row):
        return None

    run_start, run_end = _nonblank_run_bounds(lines, row)

    # A cursor may be on either a marker line or one of its physical
    # continuations. Parse the whole contiguous list so live wrapping uses the
    # same widest-marker width budget as Ctrl+J.
    for i in range(run_start, row + 1):
        if _LIST_ITEM_RE.match(lines[i]) is None:
            continue
        block = _parse_simple_list_run(lines, i, limit=run_end, width=WRAP_COLUMN)
        if block is not None and block.start <= row < block.end:
            return block

    # Ordinary prose retains the conservative run-level validation used by
    # Carriage historically. The rendering itself is now shared with Ctrl+J.
    if _run_is_plain_prose(lines, row):
        return _make_plain_prose_block(lines, run_start, run_end)
    return None


def _live_wrap_measure_text(line):
    """Return the text that should count toward a live-wrap decision.

    A single trailing space is an in-progress word separator while the user is
    typing. If that space is the character that first crosses WRAP_COLUMN, do
    not invoke the wrapper yet: `_wrap_markdown_prose()` intentionally trims
    layout whitespace, and doing so at this moment would consume the separator
    before the next word exists. Once a non-space character follows it, the
    space is internal prose and the shared wrapper can move the word safely.

    Explicit Markdown hard-break markers keep their existing treatment.
    """
    marker = _hard_break_marker(line)
    text = _strip_hard_break_marker(line, marker)
    if marker is None and text.endswith(" "):
        text = text.rstrip(" ")
    return text


def _wrap_block_needs_reflow(block, width=WRAP_COLUMN):
    """Return True when a supported block exceeds its active prose budget."""
    if block.kind == "list-run" and block.list_items is not None:
        body_width = block.wrap_width if block.wrap_width is not None else width
        for item in block.list_items:
            prefix_width = len(item.marker or "")
            for line in item.source_lines:
                body = line[prefix_width:] if len(line) >= prefix_width else ""
                if len(_live_wrap_measure_text(body)) > body_width:
                    return True
        return False

    if block.kind == "list" and block.marker is not None:
        body_width = block.wrap_width
        if body_width is None:
            body_width = max(10, width - len(block.marker))
        prefix_width = len(block.marker)
        for line in block.source_lines:
            body = line[prefix_width:] if len(line) >= prefix_width else ""
            if len(_live_wrap_measure_text(body)) > body_width:
                return True
        return False

    for line in block.source_lines:
        if len(_live_wrap_measure_text(line)) > width:
            return True
    return False


def _cursor_nonspace_units(lines, block, row, col):
    """Count stable non-whitespace characters before the live cursor.

    Wrapping changes only whitespace/layout for supported blocks, so this gives
    us a robust cursor anchor without maintaining a second wrapping algorithm.
    """
    units = 0
    for absolute_row in range(block.start, min(row, block.end - 1) + 1):
        line = lines[absolute_row]
        stop = col if absolute_row == row else len(line)
        stop = max(0, min(stop, len(line)))
        units += sum(not ch.isspace() for ch in line[:stop])
    return units


def _cursor_from_nonspace_units(rendered, units, prefer_end=False):
    """Map a non-whitespace cursor anchor back into rendered block lines."""
    if not rendered:
        return 0, 0
    if prefer_end:
        return len(rendered) - 1, len(rendered[-1])
    if units <= 0:
        return 0, 0

    seen = 0
    for row, line in enumerate(rendered):
        for col, char in enumerate(line):
            if not char.isspace():
                seen += 1
                if seen >= units:
                    return row, col + 1
    return len(rendered) - 1, len(rendered[-1])


def _on_text_insert(buf):
    """Live-wrap the affected logical prose/list block through one engine.

    Ctrl+J and live wrapping share the same list parser, safety checks,
    Markdown hard-break handling, width calculation, and renderer. The live
    path differs only in scope: it rewrites the logical block containing the
    insertion point rather than walking the whole document. Unsupported or
    malformed Markdown is preserved rather than repaired.
    """
    if not state.auto_wrap:
        return

    doc = buf.document
    row = doc.cursor_position_row
    col = doc.cursor_position_col
    lines = list(doc.lines)

    block = _find_live_wrap_block(lines, row)
    if block is None or not _wrap_block_needs_reflow(block):
        return

    rendered = _render_wrap_block(block, width=WRAP_COLUMN)
    if rendered == block.source_lines:
        return

    prefer_end = row == block.end - 1 and col == len(lines[row])
    units = _cursor_nonspace_units(lines, block, row, col)
    relative_row, new_col = _cursor_from_nonspace_units(
        rendered, units, prefer_end=prefer_end
    )

    lines[block.start:block.end] = rendered
    new_row = block.start + relative_row
    new_text = "\n".join(lines)
    tmp = Document(text=new_text)
    new_row = max(0, min(new_row, tmp.line_count - 1))
    new_col = max(0, min(new_col, len(tmp.lines[new_row])))
    new_cursor = tmp.translate_row_col_to_index(new_row, new_col)
    buf.document = Document(text=new_text, cursor_position=new_cursor)


text_area.buffer.on_text_insert += _on_text_insert


def _reflow_boundary_start(lines, index):
    """Return True when `index` starts something that is not plain prose.

    Ctrl+J scans the whole file block by block.  This predicate is deliberately
    local: one structural line ends the current prose paragraph, but it does not
    make the rest of the surrounding nonblank run opaque.  That keeps an
    unsupported construct from preventing later ordinary prose from being
    reflowed.
    """
    if not (0 <= index < len(lines)):
        return True

    line = lines[index]
    stripped = line.lstrip()
    return bool(
        TABLE_PLACEHOLDER_RE.match(line)
        or _fence_marker(line)
        or _generic_fence_marker(line)
        or _is_strong_html_start(line)
        or _is_pipe_table_start(lines, index)
        or _definition_list_start(lines, index)
        or _LIST_ITEM_RE.match(line)
        or _ATX_HEADING_RE.match(line)
        or stripped.startswith(">")
        or _is_thematic_break(line)
        or _REFERENCE_DEF_RE.match(line)
        or _DEFINITION_MARKER_RE.match(line)
        or _is_indented_code(line)
        or _OTHER_LIST_RE.match(line)
        or stripped.startswith("|")
        or _GRID_BORDER_RE.match(line)
        or _SIMPLE_TABLE_SEPARATOR_RE.match(line)
        or _is_pipe_table_separator(line)
        or _looks_structural_or_ambiguous(line)
    )


def _collect_simple_blockquote_run(lines, index, width):
    """Reflow one explicit single-level blockquote run.

    Only consecutive physical lines beginning with ``>`` belong to this
    supported block.  Lazy continuations and more complex quote structures are
    left unchanged rather than making neighboring prose opaque.
    """
    end = index
    while end < len(lines) and lines[end].strip() and lines[end].lstrip().startswith(">"):
        end += 1

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
            wrapped = _wrap_markdown_prose(paragraph, width=max(10, width - 2))
            rendered.extend(f"> {line}" if line else ">" for line in wrapped)
            paragraph = []
        if content == "" and rendered and rendered[-1] != ">":
            rendered.append(">")

    if rendered and rendered[-1] == ">" and inner and inner[-1].strip():
        rendered.pop()
    return rendered, end


def reflow_text(full_text, width=WRAP_COLUMN):
    """Hard-wrap every supported prose block in the document.

    Ctrl+J is document-wide.  It walks from the first physical line to the
    last, reflowing every ordinary prose paragraph, simple flat list, and
    explicit single-level blockquote it encounters.  Structural or unsupported
    Markdown is copied verbatim, but it never causes later supported prose to
    be skipped.

    Blank lines are preserved exactly; reflow does not add or remove document
    structure merely to normalize Markdown style.
    """
    lines = full_text.split("\n")
    rendered = []
    i = 0

    yaml_end = _yaml_front_matter_end(lines)
    if yaml_end is not None:
        rendered.extend(lines[:yaml_end])
        i = yaml_end

    while i < len(lines):
        line = lines[i]

        # Preserve blank-line boundaries exactly as authored.
        if not line.strip():
            rendered.append(line)
            i += 1
            continue

        # Multiline opaque structures are copied as units so text inside them
        # is never mistaken for prose on a later iteration.
        if _fence_marker(line):
            block, i = _collect_fenced_block(lines, i)
            rendered.extend(block)
            continue

        if _generic_fence_marker(line):
            block, i = _collect_generic_opaque_block(lines, i)
            rendered.extend(block)
            continue

        if _is_strong_html_start(line):
            block, i = _collect_html_block(lines, i)
            rendered.extend(block)
            continue

        if _is_pipe_table_start(lines, i):
            block, i = _collect_pipe_table(lines, i)
            rendered.extend(block)
            continue

        if _definition_list_start(lines, i):
            block, i = _collect_definition_list(lines, i)
            rendered.extend(block)
            continue

        # A valid simple list is reflowed as a complete contiguous list so the
        # widest ordered marker can determine one shared source-width budget.
        if _LIST_ITEM_RE.match(line):
            run_end = _nonblank_run_end(lines, i)
            run = _parse_simple_list_run(lines, i, limit=run_end, width=width)
            if run is not None:
                rendered.extend(_render_wrap_block(run, width=width))
                i = run.end
            else:
                # Preserve only the unsupported item, then resume scanning at
                # the next top-level item. One complex list entry must not
                # prevent Ctrl+J from hard-wrapping simple entries elsewhere
                # in the same list or later prose in the file.
                item_end = _complex_list_item_end(lines, i, limit=run_end)
                rendered.extend(lines[i:item_end])
                i = item_end
            continue

        if _ATX_HEADING_RE.match(line) or _is_thematic_break(line):
            rendered.append(line)
            i += 1
            continue

        if line.lstrip().startswith(">"):
            wrapped, end = _collect_simple_blockquote_run(lines, i, width)
            if wrapped is None:
                rendered.extend(lines[i:end])
            else:
                rendered.extend(wrapped)
            i = end
            continue

        # Unsupported single-line structures are preserved locally.  The next
        # iteration can still reflow ordinary prose that follows them.
        if _reflow_boundary_start(lines, i):
            rendered.append(line)
            i += 1
            continue

        # Ordinary prose continues until a blank line or the next local
        # structural boundary.  This is the key document-wide behavior: every
        # prose block gets its own chance to reflow regardless of what appeared
        # earlier in the same nonblank region.
        start = i
        i += 1
        while (
            i < len(lines)
            and lines[i].strip()
            and not _reflow_boundary_start(lines, i)
        ):
            i += 1

        prose_block = _make_plain_prose_block(lines, start, i)
        if prose_block is None:
            rendered.extend(lines[start:i])
        else:
            rendered.extend(_render_wrap_block(prose_block, width=width))

    return "\n".join(rendered)

def _document_cursor_nonspace_units(text, cursor_position):
    """Return a wrapping-stable logical cursor offset for the document.

    Reflow changes whitespace and physical line boundaries in supported prose,
    but it preserves the sequence of non-whitespace characters. Counting those
    characters before the insertion point gives Ctrl+J a stable anchor that
    follows the author's words instead of a raw byte/character offset whose
    meaning changes as line breaks move.
    """
    cursor_position = max(0, min(len(text), cursor_position))
    return sum(not char.isspace() for char in text[:cursor_position])


def _cursor_position_from_document_units(text, units, prefer_end=False):
    """Map a logical non-whitespace offset back into reflowed document text."""
    if prefer_end:
        return len(text)
    if units <= 0:
        return 0

    seen = 0
    for position, char in enumerate(text):
        if not char.isspace():
            seen += 1
            if seen >= units:
                return position + 1
    return len(text)


def do_reflow_document():
    """Reflow the document while keeping the insertion point near its text."""
    buf = text_area.buffer
    old_text = buf.text
    old_cursor = buf.cursor_position
    new_text = reflow_text(old_text)

    if new_text == old_text:
        return

    # Keyboard-triggered Ctrl+J explicitly disables prompt_toolkit's automatic
    # save_before snapshot so menu and keyboard invocation share one undo step.
    buf.save_to_undo_stack()

    logical_units = _document_cursor_nonspace_units(old_text, old_cursor)
    new_cursor = _cursor_position_from_document_units(
        new_text,
        logical_units,
        prefer_end=(old_cursor == len(old_text)),
    )
    buf.document = Document(text=new_text, cursor_position=new_cursor)

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

        # Crash recovery is independent of normal autosave. It runs for every
        # modified document, even when autosave is disabled, the source file is
        # conflicted/read-only, or a modal (including the table editor) is open.
        if _has_recoverable_changes():
            try:
                _write_recovery_snapshot()
            except (OSError, UnicodeError, TypeError, ValueError) as e:
                # Do not stack a warning over another modal. Leave the flag
                # clear in that case so the warning can be shown on a later
                # pass after the modal closes.
                if current_float is None and not state.recovery_error:
                    state.recovery_error = True
                    show_message(
                        "Recovery unavailable",
                        "Carriage could not update the crash-recovery copy for "
                        f"this document.\n\n{e}",
                    )
            else:
                state.recovery_error = False
        else:
            _clear_recovery_file()

        # Everything below this point concerns the user's actual source file.
        if not state.auto_save:
            get_app().invalidate()
            continue
        if state.path is None:
            get_app().invalidate()
            continue
        if state.external_process_running:
            get_app().invalidate()
            continue
        if current_float is not None:
            # Source autosave must not write behind Open/Save/Export dialogs or
            # commit a table-editor draft that the user has not saved yet.
            get_app().invalidate()
            continue
        if not state.is_modified(text_area.text):
            get_app().invalidate()
            continue

        try:
            if _path_is_read_only(state.path):
                if not state.autosave_conflict:
                    state.autosave_conflict = True
                    show_message(
                        "Autosave paused",
                        "The current file is marked read-only. Autosave will not "
                        "replace it. Your working copy is still protected by crash "
                        "recovery. Use Save As to write your changes elsewhere.",
                    )
                get_app().invalidate()
                continue
            disk_snapshot = _disk_snapshot(state.path)
        except OSError as e:
            if not state.autosave_conflict:
                state.autosave_conflict = True
                show_message(
                    "Autosave paused",
                    "Carriage could not verify the file on disk, so it did not "
                    f"save. Your working copy is still protected by crash recovery.\n\n{e}",
                )
            get_app().invalidate()
            continue

        if state.disk_snapshot is None or disk_snapshot != state.disk_snapshot:
            if not state.autosave_conflict:
                state.autosave_conflict = True
                show_message(
                    "Autosave paused",
                    "The file changed, was replaced, or was deleted outside Carriage. "
                    "Autosave will not overwrite that version. Your working copy is "
                    "still protected by crash recovery. Use Save to choose Save As, "
                    "Overwrite, or Cancel.",
                )
            get_app().invalidate()
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
                "Your working copy is still protected by crash recovery. Use Save to "
                "choose how to resolve the conflict.",
            )
        elif result == _SAVE_READ_ONLY and not state.autosave_conflict:
            state.autosave_conflict = True
            show_message(
                "Autosave paused",
                "The file became read-only while autosave was running. Nothing was "
                "overwritten. Your working copy is still protected by crash recovery. "
                "Use Save As to write your changes elsewhere.",
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
    ("1-6", "Jump to File/Edit/Go/Export/Tools/Help"),
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
    strict = current_title is not None

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
        + 20  # wrap/save field ("wrap:off save:paused")
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
    if not state.auto_save:
        save_status = "off"
    elif state.autosave_conflict or state.recovery_error:
        save_status = "paused"
    else:
        save_status = "on"

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

class EdgeAlignedMenuContainer(MenuContainer):
    """MenuContainer whose selection includes its leading separator cell.

    prompt_toolkit inserts one unselected space before every top-level menu
    item. For the first item, that leaves a one-cell strip of menu-bar
    background between the bar's left edge and the selected highlight. Keep
    the inter-item spacing, but treat that separator as part of the selected
    item and anchor its submenu at the same left edge.
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
                        if app.layout.has_focus(self.window):
                            if self.selected_menu == [index]:
                                app.layout.focus_last()
                        else:
                            app.layout.focus(self.window)
                    self.selected_menu = [index]

            selected = index == self.selected_menu[0] and focused
            style_name = (
                "class:menu-bar.selected-item"
                if selected
                else "class:menu-bar"
            )

            # Anchor the submenu at the left edge of the complete selected
            # block, including the separator cell. This makes File line up
            # exactly with the left edge of the menu bar.
            if selected:
                yield ("[SetMenuPosition]", "", mouse_handler)

            yield (style_name, " ", mouse_handler)
            yield (style_name, item.text, mouse_handler)

        result = []
        for index, item in enumerate(self.menu_items):
            result.extend(one_item(index, item))
        return result


menu_container = EdgeAlignedMenuContainer(
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
                MenuItem("-", disabled=True),
                MenuItem("Reflow Document   Ctrl+J", handler=do_reflow_document),
                MenuItem("Toggle Auto-Wrap", handler=do_toggle_autowrap),
                MenuItem("Toggle Auto-Save", handler=do_toggle_autosave),
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


@kb.add("c-j", filter=editor_focused, save_before=lambda e: False)
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
    info = _structural_display_map(doc.text).get(row)
    if info is None or info[1] != "list-marker":
        return False
    return doc.cursor_position_col == info[0]


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

    # Use the parser's logical body rather than slicing every physical source
    # line by the marker width. A valid lazy continuation has no indentation to
    # remove, while a canonical continuation does; body_lines already handles
    # both correctly.
    converted = list(block.body_lines or [])

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


@kb.add("backspace", filter=editor_focused & Condition(lambda: text_area.buffer.selection_state is not None))
def _(event):
    # prompt_toolkit's default backward-delete behavior does not consistently
    # replace an active selection. In the prose editor, Backspace should match
    # Delete: when text is selected, remove the selection as one edit. Leave
    # ordinary Backspace behavior untouched when there is no selection.
    event.current_buffer.cut_selection()


@kb.add("enter", filter=editor_focused)
def _(event):
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


def _move_editor_cursor_across_lines(delta):
    """Move one visible character left/right, crossing newline boundaries."""
    buf = text_area.buffer
    text = buf.text
    pos = buf.cursor_position

    if delta > 0:
        # TABLE_SENTINEL is an internal zero-width marker attached to folded
        # table references. Skip it without consuming a visible cursor step.
        doc = buf.document
        row = doc.cursor_position_row
        at_line_end = doc.cursor_position_col == len(doc.current_line)
        continuation_width = (
            _list_continuation_prefix_width(doc, row + 1)
            if at_line_end and row + 1 < doc.line_count
            else None
        )
        while pos < len(text) and text[pos] == TABLE_SENTINEL:
            pos += 1
        if pos < len(text):
            pos += 1
        if continuation_width is not None:
            pos = min(len(text), pos + continuation_width)
        while pos < len(text) and text[pos] == TABLE_SENTINEL:
            pos += 1
    elif delta < 0:
        doc = buf.document
        continuation_width = _list_continuation_prefix_width(
            doc, doc.cursor_position_row
        )
        if (
            continuation_width is not None
            and doc.cursor_position_col == continuation_width
        ):
            # Treat canonical continuation indentation as display structure:
            # one Left from visible column zero reaches the previous line end.
            pos = max(0, pos - continuation_width - 1)
        else:
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


def _start_background_tasks(startup_error=None, recovery_source_path=None, offer_any_recovery=False):
    application.create_background_task(_autosave_loop())
    if startup_error is not None:
        title, message = startup_error
        show_message(title, message)
    elif recovery_source_path is not None:
        _offer_stale_recovery(recovery_source_path)
    elif offer_any_recovery:
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
            startup_error,
            recovery_source_path=(state.path if len(sys.argv) > 1 else None),
            offer_any_recovery=(len(sys.argv) == 1),
        )
    )


if __name__ == "__main__":
    main()
