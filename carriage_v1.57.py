#!/usr/bin/env python3
"""
Carriage - A prose-first Markdown editor for the terminal.

Carriage provides a focused full-screen writing environment built with
prompt_toolkit. It is designed for writing and revising ordinary Markdown while
keeping the underlying file portable and readable outside Carriage.

Text soft-wraps visually inside an 80-column prose area without inserting source
line breaks. Lists and ATX heading markers can hang into the left margin so the
prose itself remains aligned. Edit > Convert for Carriage converts valid
original Markdown, plus supported pipe tables and footnotes, into Carriage's preferred
source form. It converts Setext headings to ATX headings, corrects simple ordered-list numbering, and normalizes hard-wrapped prose back to
logical source lines. Original-Markdown hard breaks made with two trailing
spaces render as a visible ↵ marker in the editor; the marker is display-only
and is never written to disk. Export > Hard-Wrapped Markdown creates a separate
80-column Markdown copy without modifying the working document.

Convert for Carriage preserves line-sensitive structures in its supported
Markdown scope, including code blocks, pipe tables, raw block HTML, headings,
thematic breaks, reference definitions, and footnotes.

Supported pipe tables are folded to compact references such as
[[Table 1: Movement Rates]] and edited through a dedicated table editor. Simple
Pandoc-style footnotes are also first-class objects: references display as
sequential numbers, simple definitions fold out of the prose view, and Tab opens
the associated footnote editor. More complex footnotes remain ordinary Markdown
source.

File operations include New, Open, Save, and Save As. Untitled documents use
the first recognized ATX heading as the suggested .md filename when available.
Named files can autosave every 30 seconds, while modified documents also receive
independent crash-recovery snapshots. Saves use durable atomic replacement and protect
against external file changes.

Carriage includes lightweight Markdown highlighting, mouse support, document
and section navigation, aspell integration, and Pandoc export to PDF, DOCX, ODT,
HTML, plain text, and custom formats.

Requires:
  pip install prompt_toolkit --break-system-packages

Optional:
  pandoc, for document export.
  aspell and an appropriate dictionary package, for spell checking.

Usage:
  ./carriage.py [file.md]
"""

import asyncio
import copy
from functools import lru_cache
from bisect import bisect_right
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
from prompt_toolkit.buffer import Buffer
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
APP_VERSION = "1.57"

WRAP_COLUMN = 80
STRUCTURE_GUTTER_WIDTH = 8
TAB_WIDTH = 4
HARD_BREAK_DISPLAY_CHAR = "↵"
AUTOSAVE_INTERVAL_SECONDS = 30
RECOVERY_FORMAT_VERSION = 3
TABLE_SENTINEL = "\u2063"  # zero-width INVISIBLE SEPARATOR; never written to disk
FOOTNOTE_SENTINEL = "\u2064"  # zero-width INVISIBLE PLUS; never written to disk
TABLE_PLACEHOLDER_RE = re.compile(
    rf"^\[\[Table (\d+)(?:: (.*?))?\]\]{TABLE_SENTINEL}$"
)
FOOTNOTE_PLACEHOLDER_RE = re.compile(
    rf"^\[\[Footnote: ([^\]]+)\]\]{FOOTNOTE_SENTINEL}$"
)
_FOOTNOTE_REFERENCE_RE = re.compile(r"\[\^([^\]\n]+)\](?!:)")


def _markdown_char_is_escaped(text, index):
    """Return True when the character at index is escaped by an odd \\ run."""
    backslashes = 0
    index -= 1
    while index >= 0 and text[index] == "\\":
        backslashes += 1
        index -= 1
    return bool(backslashes % 2)


def _range_contains(ranges, position):
    """Return True when position lies inside one of the sorted ranges."""
    for start, end in ranges:
        if position < start:
            return False
        if start <= position < end:
            return True
    return False


def _matching_link_label_start(text, close_index, protected):
    """Find the opening [ for a valid-looking Markdown link/image label."""
    depth = 1
    i = close_index - 1
    while i >= 0:
        if _range_contains(protected, i):
            i -= 1
            continue
        char = text[i]
        if char == "]" and not _markdown_char_is_escaped(text, i):
            depth += 1
        elif char == "[" and not _markdown_char_is_escaped(text, i):
            depth -= 1
            if depth == 0:
                return i
        elif char == "\n" and depth == 1:
            # Original Markdown permits inline content in labels, but treating
            # a prior physical line as the start of a link here would create
            # surprising footnote exclusions. Reference/inline link syntax
            # itself remains untouched; this helper only protects destinations.
            return None
        i -= 1
    return None


def _inline_footnote_literal_ranges(full_text):
    """Return inline source ranges where ``[^id]`` must remain literal.

    Footnotes are an extension layered on original Markdown. Their reference
    syntax must therefore lose special meaning inside original-Markdown code
    spans, autolinks/inline HTML, inline link/image destinations, and the
    second label of reference-style links/images.
    """
    ranges = []
    n = len(full_text)

    # Code spans. Markdown.pl 1.0.1 permits arbitrary-length backtick runs and
    # allows the span content to cross physical newlines.
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

    ranges.sort()

    # Angle-bracket inline constructs: autolinks and raw inline HTML. Under the
    # valid-Markdown input contract, a complete <...> pair is source whose
    # contents should not be reinterpreted as a footnote reference.
    i = 0
    while i < n:
        if full_text[i] == "<" and not _markdown_char_is_escaped(full_text, i) and not _range_contains(ranges, i):
            quote = None
            end = None
            j = i + 1
            while j < n and full_text[j] != "\n":
                char = full_text[j]
                if quote is not None:
                    if char == quote:
                        quote = None
                elif char in {'"', "'"}:
                    quote = char
                elif char == ">":
                    end = j
                    break
                j += 1
            if end is not None:
                ranges.append((i, end + 1))
                i = end + 1
                continue
        i += 1
    ranges.sort()

    # Inline destinations and reference-style second labels. Original
    # Markdown permits an optional space between the two bracket sets of a
    # reference link; inline links require the opening '(' immediately after
    # the closing ']'.
    i = 0
    while i < n:
        if full_text[i] != "]" or _markdown_char_is_escaped(full_text, i) or _range_contains(ranges, i):
            i += 1
            continue
        if _matching_link_label_start(full_text, i, ranges) is None:
            i += 1
            continue

        next_index = i + 1
        if next_index < n and full_text[next_index] == "(":
            depth = 1
            quote = None
            j = next_index + 1
            while j < n:
                char = full_text[j]
                if _markdown_char_is_escaped(full_text, j):
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
                        ranges.append((next_index, j + 1))
                        break
                j += 1
            i = max(i + 1, j + 1 if j < n else i + 1)
            ranges.sort()
            continue

        j = next_index
        while j < n and full_text[j] in " \t":
            j += 1
        if j < n and full_text[j] == "[" and not _markdown_char_is_escaped(full_text, j):
            close = j + 1
            while close < n:
                if full_text[close] == "]" and not _markdown_char_is_escaped(full_text, close):
                    ranges.append((j, close + 1))
                    ranges.sort()
                    i = close + 1
                    break
                if full_text[close] == "\n":
                    break
                close += 1
            else:
                i += 1
            if i == close + 1:
                continue
        i += 1

    # Merge overlaps so candidate tests are cheap and deterministic.
    merged = []
    for start, end in sorted(ranges):
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))
    return tuple(merged)


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
    # Which edge of the selected row should be kept visible in the table
    # viewport. Moving downward anchors the row's bottom; moving upward anchors
    # its top. This matters for prose-heavy rows that span several screen lines.
    scroll_anchor: str = "top"


@dataclass
class FootnoteData:
    """One simple folded footnote definition."""

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


# ---------------------------------------------------------------------------
# Editor state
# ---------------------------------------------------------------------------

class EditorState:
    def __init__(self):
        self.path = None
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
        # named and untitled documents, including in-progress table/footnote
        # drafts, and is removed after a successful Save, New, Open, or clean
        # discard/quit.
        self.recovery_path = None
        self.recovery_error = False
        self.tables = {}
        self.footnotes = {}

    def is_modified(self, current_text):
        try:
            source_text = _materialize_objects(current_text)
        except ValueError:
            return True
        return source_text != self.saved_text


state = EditorState()


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


def _set_committed_table(table_number, table):
    """Replace one committed table using copy-on-write for undo snapshots."""
    updated = dict(state.tables)
    updated[table_number] = table
    state.tables = updated


def _set_committed_footnote(identifier, note):
    """Replace one committed footnote using copy-on-write for undo snapshots."""
    updated = dict(state.footnotes)
    updated[identifier] = note
    state.footnotes = updated


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

    def invalidate_rendered_height_cache(self):
        """Discard cached soft-wrap geometry after source/layout changes."""
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

    def _rendered_height_geometry(self, ui_content=None, width=None):
        """Return cached (heights, prefix sums) for the current soft layout.

        A wheel tick must not ask prompt_toolkit to measure every logical line.
        Heights are therefore computed once per text/layout generation and then
        reused until document text or terminal geometry changes. ``prefix[n]``
        is the rendered-row offset at the start of logical line ``n``.
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
        key = (generation, width, self._height_cache_columns(), ui_content.line_count)
        if (
            getattr(self, "_height_cache_key", None) == key
            and getattr(self, "_height_cache_heights", None) is not None
            and getattr(self, "_height_cache_prefix", None) is not None
        ):
            return self._height_cache_heights, self._height_cache_prefix

        heights = [
            max(1, ui_content.get_height_for_line(i, width, self.get_line_prefix))
            for i in range(ui_content.line_count)
        ]
        prefix = [0]
        total = 0
        for line_height in heights:
            total += line_height
            prefix.append(total)

        self._height_cache_key = key
        self._height_cache_heights = heights
        self._height_cache_prefix = prefix
        return heights, prefix

    def _rendered_heights(self, ui_content=None, width=None):
        """Return cached rendered-screen heights for all logical lines."""
        heights, _prefix = self._rendered_height_geometry(ui_content, width)
        return heights

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

    def _scroll(self, ui_content, width, height):
        """Honor manual viewport scrolling without forcing the cursor into view."""
        if not self.manual_scroll_active:
            return super()._scroll(ui_content, width, height)

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

            def content_handler(mouse_event):
                y = min(content_y_max - 1, mouse_event.position.y)
                x = mouse_event.position.x

                # A real click resumes editing at the clicked location. End
                # manual scrolling before forwarding it to BufferControl; the
                # current render map still describes exactly what was clicked.
                if mouse_event.event_type == MouseEventType.MOUSE_DOWN:
                    self.end_manual_scroll()

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


def _scrollbar_rendered_geometry():
    """Return cached rendered heights/prefix sums from the last layout."""
    info = text_area.window.render_info
    if info is None:
        return None, None
    return text_area.window._rendered_height_geometry(
        ui_content=info.ui_content, width=info.window_width
    )


def _scrollbar_rendered_heights():
    """Compatibility helper returning cached rendered logical-line heights."""
    heights, _prefix = _scrollbar_rendered_geometry()
    return heights


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
_HIGHLIGHT_ATX_RE = re.compile(r"^\s{0,3}#{1,6}(?!#)")
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


def _highlight_style_for_match(match):
    if match.lastgroup == "strong_em":
        return "class:markdown.bold-italic"
    if match.lastgroup == "strong":
        return "class:markdown.bold"
    return "class:markdown.italic"



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
    lines = full_text.split("\n")
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

    # Do not reinterpret literal source inside block-level carve-outs.
    block_kind = None
    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        if block.start <= row < block.end:
            block_kind = block.kind
            break
    if block_kind in {
        "front-matter",
        "code",
        "block-html",
        "table",
        "reference-definition",
        "footnote-placeholder",
    }:
        return []

    spans = []
    for start, end, identifier in _footnote_references_on_row(full_text, row):
        number = numbers.get(identifier)
        if identifier and number is not None:
            spans.append((start, end, f"[{number}]", identifier, False))
    return spans


def _hard_break_display_span(full_text, row):
    """Return a display-only span for an original-Markdown hard line break.

    A valid hard break is two or more trailing spaces on a prose-bearing line.
    The source spaces remain authoritative; only the final trailing space is
    replaced visually by the marker, so display width and cursor positions stay
    aligned with the source. Structural blocks where trailing spaces are literal
    source (for example code, raw HTML, tables, and reference definitions) are
    deliberately excluded.
    """
    lines = full_text.split("\n")
    if not (0 <= row < len(lines)):
        return None

    line = lines[row]
    if not line.strip() or _hard_break_marker(line) is None:
        return None

    block_kind = None
    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        if block.start <= row < block.end:
            block_kind = block.kind
            break

    if block_kind not in {"prose", "list", "list-run", "blockquote"}:
        return None

    # Replace only the final trailing space. Keeping the other source spaces
    # visible-as-spaces preserves the line's display width and gives every
    # source cursor position a natural display position.
    start = len(line) - 1
    return start, len(line), HARD_BREAK_DISPLAY_CHAR


class ProseLayoutProcessor(Processor):
    """Render Carriage's hanging gutter and 80-column soft wrapping.

    Source lines remain authoritative and are never changed by this processor.
    For a physical line wider than its prose budget, display-only padding is
    inserted at word boundaries so prompt_toolkit wraps it cleanly inside the
    80-column writing area. Structural Markdown prefixes use metadata from the
    shared block analysis and hang into the left gutter.
    """

    def apply_transformation(self, ti):
        gutter = max(0, min(STRUCTURE_GUTTER_WIDTH, ti.width - (WRAP_COLUMN + 1)))
        row_layout = _display_row_layout(ti.document.text, ti.lineno)
        prefix_width = row_layout.structural_prefix_width
        if prefix_width > gutter:
            prefix_width = 0

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
            units.append((style, char, source_pos, source_pos + 1))
            source_pos += 1

        result = []
        source_to_display_map = {}
        display_to_source_map = {}
        display_pos = 0

        for _ in range(padding):
            result.append(("", " "))
            display_to_source_map[display_pos] = 0
            display_pos += 1

        body_width = max(1, min(WRAP_COLUMN, ti.width - gutter - 1))
        measured_parts = []
        for unit_style, text, src_start, _src_end in units:
            if src_start >= prefix_width:
                measured_parts.append(
                    "" if unit_style == "class:markdown.hard-break" else text
                )
        measured_body = _wrap_measure_text("".join(measured_parts))
        fallback_wrap = sum(max(0, get_cwidth(ch)) for ch in measured_body) > body_width

        def append_display_padding(count, src_anchor):
            nonlocal display_pos
            for _ in range(max(0, count)):
                result.append(("", " "))
                display_to_source_map[display_pos] = src_anchor
                display_pos += 1

        def next_word_width(unit_index):
            width = 0
            found = False
            for _style, text, _src_start, _src_end in units[unit_index:]:
                for char in text:
                    if char.isspace():
                        if found:
                            return width
                        continue
                    found = True
                    width += max(0, get_cwidth(char))
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
                body_col += sum(max(0, get_cwidth(ch)) for ch in text)

            if fallback_wrap and text.isspace():
                word_width = next_word_width(unit_index + 1)
                if 0 < word_width <= body_width and body_col + word_width > body_width:
                    fill = max(0, (body_width + 1) - body_col)
                    append_display_padding(fill, src_end - 1 if src_end > src_start else src_start)
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
# Preferred rendered-screen column for repeated Up/Down navigation. Unlike
# Buffer.preferred_column, this is measured in visual cells after Carriage's
# display transformations and soft wrapping.
text_area.window._vertical_preferred_x = None
text_area.window._visual_vertical_move_in_progress = False
text_area.window.on_scrollbar_interact = _on_scrollbar_interact
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


def _resume_editor_view(_buffer=None):
    """Exit viewport-only scrolling as soon as the cursor moves."""
    text_area.window.end_manual_scroll()
    # Repeated Up/Down presses preserve a rendered-screen column, just like a
    # conventional editor preserves a preferred column across short lines. Any
    # other cursor movement (Left/Right, mouse click, Home/End, etc.) starts a
    # new vertical-navigation column on the next Up/Down press.
    if not text_area.window._visual_vertical_move_in_progress:
        text_area.window._vertical_preferred_x = None


def _editor_text_changed(_buffer=None):
    """Reset viewport ownership and invalidate cached soft-wrap geometry."""
    text_area.window.end_manual_scroll()
    text_area.window._vertical_preferred_x = None
    text_area.window.invalidate_rendered_height_cache()


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
    global current_float, current_table_editor, current_footnote_editor

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
    if (
        current_footnote_editor is not None
        and closed_float is current_footnote_editor.dialog_float
    ):
        current_footnote_editor = None

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
_SAVE_DURABILITY_ERROR = "durability_error"


def _canonical_path(path):
    """Return the concrete path Carriage will read from or replace."""
    return os.path.realpath(os.path.abspath(path))


def _fsync_directory(directory):
    """Flush directory metadata so a completed rename survives a crash.

    Atomic replacement protects against partial writes, but the rename itself
    is not durably committed until the containing directory has been synced.
    Carriage uses this after replacing the source file and recovery journal.
    """
    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    dir_fd = os.open(directory, flags)
    try:
        os.fsync(dir_fd)
    finally:
        os.close(dir_fd)


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
        "title": table.title,
        "alignments": list(table.alignments),
        "original_lines": None if table.original_lines is None else list(table.original_lines),
        "caption_position": table.caption_position,
        "dirty": bool(table.dirty),
    }


def _table_from_recovery_record(raw_table):
    if not isinstance(raw_table, dict):
        raise ValueError("Recovery file contains invalid table data.")
    return TableData(
        headers=list(raw_table.get("headers", [])),
        rows=[list(row) for row in raw_table.get("rows", [])],
        title=str(raw_table.get("title", "")),
        alignments=list(raw_table.get("alignments", [])),
        original_lines=(
            None
            if raw_table.get("original_lines") is None
            else list(raw_table.get("original_lines"))
        ),
        caption_position=raw_table.get("caption_position"),
        dirty=bool(raw_table.get("dirty", False)),
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
    identifier = str(raw_note.get("identifier", "")).strip()
    if not identifier:
        raise ValueError("Recovery file contains a footnote without an identifier.")
    return FootnoteData(
        identifier=identifier,
        text=str(raw_note.get("text", "")),
        original_lines=(
            None
            if raw_note.get("original_lines") is None
            else list(raw_note.get("original_lines"))
        ),
        dirty=bool(raw_note.get("dirty", False)),
    )


def _footnote_content_key(note):
    return note.text


def _active_footnote_draft():
    session = current_footnote_editor
    if session is None:
        return None
    working = copy.deepcopy(session.working)
    if session.editor is not None:
        working.text = " ".join(session.editor.text.splitlines()).strip()
    return session.identifier, working


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
        "pid": os.getpid(),
        "source_path": source_path,
        "saved_text": state.saved_text,
        "disk_snapshot": disk_snapshot,
        "cursor_position": text_area.buffer.cursor_position,
        "visible_text": text_area.text,
        "tables": tables,
        "footnotes": footnotes,
        "had_table_draft": had_table_draft,
        "had_footnote_draft": had_footnote_draft,
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
        _fsync_directory(directory)
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
    if version not in (1, 2, RECOVERY_FORMAT_VERSION):
        raise ValueError("Unsupported Carriage recovery format.")
    if not isinstance(payload.get("visible_text"), str):
        raise ValueError("Recovery file does not contain document text.")
    if not isinstance(payload.get("tables"), dict):
        raise ValueError("Recovery file contains invalid table data.")
    if version >= 3 and not isinstance(payload.get("footnotes"), dict):
        raise ValueError("Recovery file contains invalid footnote data.")
    payload.setdefault("footnotes", {})
    payload.setdefault("had_footnote_draft", False)

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

    restored_footnotes = {}
    for raw_identifier, raw_note in payload.get("footnotes", {}).items():
        note = _footnote_from_recovery_record(raw_note)
        restored_footnotes[str(raw_identifier)] = note

    state.tables = restored_tables
    state.footnotes = restored_footnotes
    recovered_visible_text = payload["visible_text"]
    cursor_position = payload.get("cursor_position", len(recovered_visible_text))
    if not isinstance(cursor_position, int):
        cursor_position = len(recovered_visible_text)
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
    state.footnotes = {}


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
        visible = _collapse_objects_from_source(content)
        text_area.buffer.reset(Document(text=visible))
        state.path = path
        state.saved_text = content
        state.disk_snapshot = disk_snapshot
        state.autosave_conflict = False

    show_input_dialog("Open File", "Path:", state.path or "", cb)


def _write_file(path, expected_snapshot, report_conflict=True, report_read_only=True):
    """Atomically save only if the destination is still the expected version."""
    try:
        content = _materialize_objects(text_area.text)
    except ValueError as e:
        show_message("Document object error", str(e))
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

            # fsync() above made the new file contents durable. Now make the
            # rename itself durable before Carriage reports a successful save
            # or removes crash recovery. If this fails, the new bytes are
            # already visible at the destination, but a sudden crash could
            # still lose the directory update. Keep the document modified and
            # preserve a recovery copy so a later Save can retry safely.
            try:
                _fsync_directory(directory)
            except OSError as durability_error:
                state.path = path
                state.disk_snapshot = _snapshot_bytes(content.encode("utf-8"))
                state.autosave_conflict = False

                recovery_detail = (
                    "The new file is visible on disk, but Carriage could not "
                    "confirm that the directory update is durable. The document "
                    "will remain marked modified and Save can be tried again."
                )
                try:
                    _write_recovery_snapshot()
                except (OSError, UnicodeError, TypeError, ValueError) as recovery_error:
                    state.recovery_error = True
                    recovery_detail += (
                        "\n\nCarriage also could not update crash recovery: "
                        f"{recovery_error}"
                    )
                else:
                    state.recovery_error = False
                    recovery_detail += "\n\nCrash recovery has been retained."

                show_message(
                    "Save durability warning",
                    f"{recovery_detail}\n\nDirectory flush error: {durability_error}",
                )
                return _SAVE_DURABILITY_ERROR
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


def _suggested_new_document_filename():
    """Return a filename suggestion from the first ATX heading in an untitled document.

    Use the shared Markdown block classifier so apparent headings inside YAML,
    code, raw HTML, blockquotes, and other non-heading blocks are ignored. The
    first recognized ATX heading qualifies regardless of level, and its visible
    heading text is preserved as written rather than slugified.
    """
    if state.path is not None:
        return state.path

    for block in _analyze_document_layout(text_area.text, WRAP_COLUMN):
        if block.kind != "heading" or not block.source_lines:
            continue
        title = _heading_title(block.source_lines[0])
        if not title:
            continue

        # Keep the title human-readable. Only neutralize characters that can
        # turn the suggestion into a path (or cannot occur in a pathname).
        filename = title.replace("/", "-").replace("\\", "-").replace("\x00", "")
        filename = filename.strip()
        if not filename or filename in {".", ".."}:
            return ""
        if not filename.lower().endswith(".md"):
            filename += ".md"
        return filename

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
    _clear_recovery_file()
    get_app().exit()


# ---------------------------------------------------------------------------
# Prose layout, conversion, and hard-wrap export
# ---------------------------------------------------------------------------

# Normal editing is soft-wrapped and never reformats source automatically.
# This section implements the hard-wrapped Markdown export formatter and the
# shared Markdown structure metadata used by the display layer. Hard-wrap export
# preserves only the short set of line-sensitive constructs defined below.

_ATX_HEADING_RE = re.compile(r"^\s{0,3}#{1,6}(?!#)")
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
# Folded simple footnotes
# ---------------------------------------------------------------------------

def _footnote_placeholder(identifier):
    """Return the editor-buffer representation of a folded footnote."""
    return f"[[Footnote: {identifier}]]{FOOTNOTE_SENTINEL}"


def _footnote_fragment_is_simple(text):
    """Return True for prose-only content suitable for the v1 note editor."""
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


def _simple_footnote_definition_at(lines, index):
    """Return one foldable single-paragraph footnote definition, if present.

    Multi-paragraph notes and notes containing block structure are deliberately
    left in ordinary source for the first footnote implementation.
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
    body_parts = [first_body.strip()] if first_body.strip() else []
    i = index + 1
    while i < len(lines) and lines[i].strip():
        continuation = _footnote_continuation_text(lines[i])
        if continuation is None:
            break
        if (
            not _footnote_fragment_is_simple(continuation)
            or _hard_break_marker(lines[i]) is not None
        ):
            return None
        original.append(lines[i])
        if continuation.strip():
            body_parts.append(continuation.strip())
        i += 1

    # A blank line followed by indented content belongs to a multi-block note.
    # Leave the entire construct visible rather than folding only its first
    # paragraph and misrepresenting what the note contains.
    if i < len(lines) and not lines[i].strip():
        j = i
        while j < len(lines) and not lines[j].strip():
            j += 1
        if j < len(lines) and _footnote_continuation_text(lines[j]) is not None:
            return None

    return {
        "identifier": identifier,
        "text": " ".join(body_parts),
        "original_lines": original,
        "end": i,
    }


def _serialize_footnote(note):
    """Serialize a simple FootnoteData object to standard Markdown."""
    if not note.dirty and note.original_lines is not None:
        return "\n".join(note.original_lines)
    text = " ".join(str(note.text).splitlines()).strip()
    if text:
        return f"[^{note.identifier}]: {text}"
    return f"[^{note.identifier}]:"


def _collapse_objects_from_source(source_text):
    """Fold supported tables and simple footnote definitions in the editor."""
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
    This is used when restoring crash recovery so an in-progress title draft
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
    """Expand folded tables and simple footnotes for saving/exporting."""
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

def _table_number_at_cursor():
    line = text_area.buffer.document.current_line
    match = TABLE_PLACEHOLDER_RE.match(line)
    return int(match.group(1)) if match else None


def _table_placeholder_locked():
    """Return True while the main caret is on a folded table reference.

    Folded references are object labels, not editable Markdown source. The
    table editor owns the title and content; keeping the label read-only avoids
    a second, conflicting source of truth.
    """
    return _table_number_at_cursor() is not None


# prompt_toolkit's standard insertion/deletion bindings honor Buffer.read_only.
# Keep navigation and Tab-to-open behavior available while suppressing direct
# edits to a folded table label in the prose buffer.
text_area.buffer.read_only = Condition(_table_placeholder_locked)


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
            new_number = int(match.group(1)) + 1
            line = _table_placeholder(new_number, state.tables[new_number].title)
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

    table = state.tables.get(table_number)
    title = table.title if table is not None else ""
    buf.insert_text(prefix + _table_placeholder(table_number, title) + suffix)


def _refresh_table_placeholder(table_number):
    """Refresh one folded reference after its title changes."""
    table = state.tables.get(table_number)
    if table is None:
        return

    doc = text_area.buffer.document
    row = doc.cursor_position_row
    col = doc.cursor_position_col
    lines = list(doc.lines)
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
        return

    new_text = "\n".join(lines)
    tmp = Document(text=new_text)
    new_row = min(row, tmp.line_count - 1)
    new_col = min(col, len(tmp.lines[new_row]))
    text_area.buffer.set_document(
        Document(
            text=new_text,
            cursor_position=tmp.translate_row_col_to_index(new_row, new_col),
        ),
        bypass_readonly=True,
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
    """Display metadata for one existing physical source row."""

    role: str = "text"
    structural_prefix_width: int = 0


_ATX_DISPLAY_PREFIX_RE = re.compile(r"^\s{0,3}#{1,6}(?!#)[ \t]*")
_BLOCKQUOTE_LINE_RE = re.compile(r"^\s{0,3}>[ \t]?(.*)$")


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


def _parse_simple_list_run(lines, index, limit=None, width=WRAP_COLUMN):
    """Parse the longest supported flat-list prefix beginning at ``index``."""
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
    """Parse one supported explicit, single-level prose blockquote run."""
    if not (0 <= index < len(lines)) or not lines[index].lstrip().startswith(">"):
        return None

    end = index
    inner = []
    while end < len(lines) and lines[end].strip() and lines[end].lstrip().startswith(">"):
        match = _BLOCKQUOTE_LINE_RE.match(lines[end])
        if match is None:
            return None
        content = match.group(1)
        if re.match(r"^\s{0,3}>", content):
            return None
        if content and not _simple_list_fragment_is_safe(content):
            return None
        inner.append(content)
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


def _render_wrap_block(block, width=WRAP_COLUMN):
    """Render one logical block according to Carriage's source policy."""
    if not block.wrappable:
        return list(block.source_lines)

    if block.kind == "prose":
        return _wrap_markdown_prose(block.source_lines, width=width)

    if block.kind == "list" and block.marker is not None:
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
    """Return text that counts toward an 80-column wrap decision."""
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

    Setext headings are part of original Markdown. Convert for Carriage turns
    them into ATX headings, which are Carriage's canonical heading syntax.
    Recognition is intentionally contextual: the underline only counts when it
    immediately follows an ordinary heading-text line.
    """
    if not (0 <= index + 1 < len(lines)):
        return None

    title_line = lines[index]
    if not title_line.strip():
        return None

    # A Setext title is ordinary paragraph text, not another block construct.
    # Exclude structures that have their own original-Markdown meaning.
    if (
        _is_indented_code(title_line)
        or _ATX_HEADING_RE.match(title_line)
        or _LIST_ITEM_RE.match(title_line)
        or title_line.lstrip().startswith(">")
        or _REFERENCE_DEF_RE.match(title_line)
        or _is_strong_html_start(title_line)
        or _fence_marker(title_line)
        or _is_pipe_table_start(lines, index)
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

def _block_starts_at(lines, index, yaml_end=None, width=WRAP_COLUMN, allow_indented_code=True):
    """Return a recognized non-prose block beginning at ``index``, if any."""
    preserved = _preserved_block_at(
        lines, index, yaml_end=yaml_end, allow_indented_code=allow_indented_code
    )
    if preserved is not None:
        return preserved

    setext = _setext_heading_at(lines, index)
    if setext is not None:
        return setext

    stripped = lines[index].lstrip()
    if stripped[:1] in "-*+0123456789" and _LIST_ITEM_RE.match(lines[index]):
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
    the 80-column visual prose area merely because they count toward exported
    source width.
    """
    rows = [_LayoutRow() for _ in block.source_lines]

    if block.kind == "heading" and block.source_lines:
        match = _ATX_DISPLAY_PREFIX_RE.match(block.source_lines[0])
        if match is not None:
            rows[0] = _LayoutRow("heading", len(match.group(0)))
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
def _analyze_document_layout(full_text, width=WRAP_COLUMN):
    """Return the shared logical block layout for the current source text.

    Classification is intentionally cheap: it establishes block boundaries,
    wrap budgets, and structural roles without re-rendering every prose block.
    Hard-wrapped Markdown export feeds these blocks into ``_render_wrap_block()`` when it needs
    physical output lines. The display layer consumes the same classification
    and row metadata without changing the source.
    """
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
        # recognized in-scope block begins. Syntax outside Carriage's conversion
        # contract receives no special protection. Indentation cannot interrupt
        # an existing paragraph merely by looking like indented code.
        start = i
        i += 1
        while i < len(lines) and lines[i].strip():
            if _block_starts_at(
                lines, i, yaml_end=None, width=width, allow_indented_code=False
            ) is not None:
                break
            i += 1
        blocks.append(_make_plain_prose_block(lines, start, i))

    return tuple(blocks)




@lru_cache(maxsize=8)
def _structural_display_map(full_text):
    """Return gutter metadata projected from the shared block layout."""
    result = {}
    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        for offset, row_info in enumerate(_layout_rows_for_block(block)):
            if row_info.structural_prefix_width:
                result[block.start + offset] = (
                    row_info.structural_prefix_width,
                    row_info.role,
                )
    return result


@lru_cache(maxsize=8)
def _layout_row_map(full_text):
    """Return per-source-row metadata from the shared block layout."""
    lines = full_text.split("\n")
    result = [_LayoutRow() for _ in lines]
    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        for offset, row_info in enumerate(_layout_rows_for_block(block)):
            row = block.start + offset
            if 0 <= row < len(result):
                result[row] = row_info
    return tuple(result)


def _display_row_layout(full_text, row):
    rows = _layout_row_map(full_text)
    if 0 <= row < len(rows):
        return rows[row]
    return _LayoutRow()


def _active_structural_prefix_width(document, row, role=None, columns=None):
    """Return a prefix width only when it is actually hidden in the gutter."""
    info = _structural_display_map(document.text).get(row)
    if info is None or (role is not None and info[1] != role):
        return None
    if columns is None:
        try:
            columns = get_app().output.get_size().columns
        except Exception:
            columns = WRAP_COLUMN + STRUCTURE_GUTTER_WIDTH + 2
    _left, gutter, _right = _prose_layout_widths(columns)
    return info[0] if 0 < info[0] <= gutter else None


def _list_continuation_prefix_width(document, row):
    return _active_structural_prefix_width(
        document, row, role="list-continuation"
    )


def _hard_wrap_export_text(full_text, width=WRAP_COLUMN):
    """Hard-wrap a derived Markdown export using the explicit carve-outs."""
    rendered = []
    for block in _analyze_document_layout(full_text, width):
        rendered.extend(_render_wrap_block(block, width=width))
    return "\n".join(rendered)


def _convert_markdown_prose(source_lines):
    """Collapse wrapping whitespace while preserving explicit hard breaks.

    Each returned line is one logical prose segment. A Markdown hard-break
    marker ends the current segment and is retained at the end of that line.
    """
    rendered = []
    current = []

    for raw_line in source_lines:
        marker = _hard_break_marker(raw_line)
        text = _strip_hard_break_marker(raw_line, marker)
        stripped = text.strip()
        if stripped:
            current.append(stripped)

        if marker is not None:
            joined = " ".join(current)
            rendered.append(joined + marker)
            current = []

    if current or not rendered:
        rendered.append(" ".join(current))

    return rendered


def _atx_heading_parts(line):
    """Return ``(marker, title)`` for an original-Markdown ATX heading.

    Original Markdown accepts ATX headings with or without whitespace after the
    opening marker. Convert for Carriage emits one canonical form: the marker,
    exactly one space, and the title. A trailing run of ``#`` characters is
    closing syntax only when whitespace separates it from preceding title text;
    hashes attached directly to the title remain literal text.
    """
    match = re.match(r"^\s{0,3}(#{1,6})(?!#)(.*)$", line)
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
    """Render one heading in Carriage's canonical ATX source form."""
    title = _canonical_heading_title(title)
    return f"{marker} {title}" if title else marker


_ORDERED_LIST_MARKER_PARTS_RE = re.compile(
    r"^(?P<indent>[ \t]{0,3})(?P<number>\d+)\.(?P<spacing>[ \t]+)$"
)


def _convert_list_item(block, marker=None):
    """Convert one simple list item, optionally replacing its source marker."""
    marker = block.marker if marker is None else marker
    if marker is None:
        return list(block.source_lines)
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


def _convert_wrap_block(block):
    """Convert one block into Carriage's preferred Markdown representation."""
    if block.kind == "setext-heading" and block.source_lines:
        level = block.marker or "#"
        title = block.source_lines[0].strip()
        return [_canonical_atx_heading(level, title)]

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
        ordered_markers = _renumbered_ordered_list_markers(block.list_items)
        if ordered_markers is not None:
            for item, marker in zip(block.list_items, ordered_markers):
                rendered.extend(_convert_list_item(item, marker=marker))
        else:
            for item in block.list_items:
                rendered.extend(_convert_list_item(item))
        return rendered

    if block.kind == "blockquote":
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


def convert_for_carriage_text(full_text):
    """Convert valid Markdown into Carriage's preferred source representation.

    The conversion targets original Markdown plus Carriage's pipe-table and
    footnote extensions. Setext H1/H2 headings become ATX headings; simple
    ordered-list runs are renumbered consecutively from their first item; ordinary
    hard-wrapped prose becomes one physical line per logical segment; original
    Markdown hard breaks made with two trailing spaces remain physical line
    boundaries. Line-sensitive structural blocks are preserved when Carriage
    does not have a safe compatibility transformation for them.
    """
    rendered = []
    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        rendered.extend(_convert_wrap_block(block))
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
    match = re.match(r"^\s{0,3}(#{1,6})(?!#)(.*)$", line)
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
        title = _canonical_heading_title(stripped)
        title_start = leading
        # Setext titles have no ATX closing syntax, but Convert applies the
        # canonical trailing-hash rule to the emitted ATX title.
        semantic_end = title_start + len(title)
        target_prefix = len(block.marker or "#") + 1
        if source_col <= title_start:
            return target_prefix
        if source_col >= semantic_end:
            return len(target)
        return min(len(target), target_prefix + (source_col - title_start))

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


def _map_cursor_in_converted_block(block, target_lines, source_row, source_col):
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
        ordered_markers = _renumbered_ordered_list_markers(block.list_items)
        converted_prefix = 0
        for index, item in enumerate(block.list_items):
            marker = (
                ordered_markers[index]
                if ordered_markers is not None
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

    rendered = []
    rendered_length = 0
    mapped_cursor = None

    for block in _analyze_document_layout(full_text, WRAP_COLUMN):
        target_lines = _convert_wrap_block(block)
        block_start = rendered_length + (1 if rendered else 0)

        if block.start <= source_row < block.end:
            mapped_cursor = block_start + _map_cursor_in_converted_block(
                block, target_lines, source_row, source_col
            )

        if rendered:
            rendered_length += 1
        rendered.extend(target_lines)
        rendered_length += sum(len(line) for line in target_lines)
        rendered_length += max(0, len(target_lines) - 1)

    new_text = "\n".join(rendered)
    if mapped_cursor is None:
        mapped_cursor = len(new_text)
    return new_text, max(0, min(len(new_text), mapped_cursor))


def do_convert_for_carriage():
    """Convert the working document to Carriage's preferred Markdown form."""
    buf = text_area.buffer
    old_text = buf.text
    old_cursor = buf.cursor_position
    new_text, new_cursor = convert_for_carriage_with_cursor(old_text, old_cursor)
    if new_text == old_text:
        return

    if new_cursor is None:
        new_cursor = len(new_text)
    buf.save_to_undo_stack()
    buf.set_document(
        Document(text=new_text, cursor_position=new_cursor),
        bypass_readonly=True,
    )


def do_undo():
    text_area.buffer.undo()


def do_redo():
    text_area.buffer.redo()


def do_cut():
    if _table_placeholder_locked():
        show_message(
            "Folded table",
            "The folded table reference is read-only. Press Tab to edit the table.",
        )
        return
    data = text_area.buffer.cut_selection()
    get_app().clipboard.set_data(data)


def do_copy():
    data = text_area.buffer.copy_selection()
    get_app().clipboard.set_data(data)


def do_paste():
    if _table_placeholder_locked():
        show_message(
            "Folded table",
            "The folded table reference is read-only. Press Tab to edit the table.",
        )
        return
    text_area.buffer.paste_clipboard_data(get_app().clipboard.get_data())



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
    return (
        "Nav: ←↑↓→ move · Enter edit · Shift+Tab at first cell title · "
        "^R row · ^C col · ^S save · Esc cancel"
    )


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
        # One table save is one logical document edit. Capture the complete
        # pre-edit state before changing either the object or its placeholder.
        text_area.buffer.save_to_undo_stack()
        session.working.dirty = True
        _set_committed_table(session.table_number, session.working)
        _refresh_table_placeholder(session.table_number)

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
        if session.selected_row == 0 and session.selected_col == 0:
            _focus_table_title(session)
        else:
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
    title_editor = TextArea(
        text=session.working.title,
        multiline=False,
        focus_on_click=True,
        style="class:input-field",
    )
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
        show_message("No table", "Place the cursor on a [[Table N]] or [[Table N: Title]] reference first.")
        return
    open_table_editor(table_number)


def do_insert_table():
    if _table_placeholder_locked():
        show_message(
            "Folded table",
            "Move the cursor off the folded table reference before inserting another table.",
        )
        return
    title_field = TextArea(text="", multiline=False, style="class:input-field")
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

        title = " ".join(title_field.text.splitlines()).strip()
        close_dialog()

        # Insertion can renumber existing tables and rewrite several folded
        # placeholders. Treat that whole transformation as one undoable edit.
        text_area.buffer.save_to_undo_stack()
        _shift_table_numbers_for_insert(insert_number)
        _set_committed_table(
            insert_number, _new_table_data(columns, rows, title=title)
        )
        _insert_table_placeholder(insert_number)
        open_table_editor(insert_number)

    dialog = Dialog(
        title="Insert Table",
        body=HSplit(
            [
                Label(text="Title (optional):"),
                title_field,
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
    show_dialog(dialog, focus=title_field)


# ---------------------------------------------------------------------------
# Simple footnote editor
# ---------------------------------------------------------------------------

def _footnote_identifier_at_cursor():
    """Return the folded/simple footnote under the cursor, if any."""
    doc = text_area.buffer.document
    line = doc.current_line
    col = doc.cursor_position_col

    placeholder = FOOTNOTE_PLACEHOLDER_RE.match(line)
    if placeholder:
        return placeholder.group(1)

    for start, end, identifier in _footnote_references_on_row(doc.text, doc.cursor_position_row):
        if start <= col <= end:
            return identifier
    return None


def _footnote_source_span_at_cursor(document=None):
    """Return the source span of an inline footnote reference at the cursor."""
    doc = document or text_area.buffer.document
    line = doc.current_line
    col = doc.cursor_position_col
    for start, end, identifier in _footnote_references_on_row(doc.text, doc.cursor_position_row):
        if start <= col <= end:
            return start, end, identifier
    return None


def _next_footnote_identifier():
    """Return a stable generated identifier that does not renumber older notes."""
    highest = 0
    pattern = re.compile(r"^fn-(\d+)$")
    identifiers = set(state.footnotes)
    for _start, _end, identifier, _row, _start_col, _end_col in _footnote_reference_spans(text_area.text):
        identifiers.add(identifier)
    for identifier in identifiers:
        match = pattern.match(identifier)
        if match:
            highest = max(highest, int(match.group(1)))
    candidate = highest + 1
    while f"fn-{candidate}" in identifiers:
        candidate += 1
    return f"fn-{candidate}"


def _append_footnote_placeholder(identifier, cursor_position):
    """Append a folded definition while preserving the prose cursor."""
    buf = text_area.buffer
    text = buf.text
    placeholder = _footnote_placeholder(identifier)
    if not text:
        new_text = placeholder
    elif text.endswith("\n\n"):
        new_text = text + placeholder
    elif text.endswith("\n"):
        new_text = text + "\n" + placeholder
    else:
        new_text = text + "\n\n" + placeholder
    buf.document = Document(text=new_text, cursor_position=cursor_position)


def _save_footnote_editor():
    session = current_footnote_editor
    if session is None or session.editor is None:
        return
    session.working.text = " ".join(session.editor.text.splitlines()).strip()

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
        # does not change. Capture the old object state so Ctrl+Z can undo an
        # object-only edit in the correct chronological position.
        text_area.buffer.save_to_undo_stack()
        session.working.dirty = True
        _set_committed_footnote(session.identifier, session.working)

    close_dialog()
    get_app().invalidate()


def open_footnote_editor(identifier):
    """Open the dedicated editor for one simple folded footnote."""
    global current_footnote_editor

    note = state.footnotes.get(identifier)
    if note is None:
        show_message(
            "Footnote source",
            "This reference does not point to a simple folded footnote. "
            "Complex or unresolved footnotes remain ordinary Markdown source.",
        )
        return

    session = FootnoteEditorSession(identifier=identifier, working=copy.deepcopy(note))
    current_footnote_editor = session
    editor = TextArea(
        text=session.working.text,
        multiline=False,
        wrap_lines=True,
        height=D(preferred=8, max=14),
        style="class:footnote.editor",
    )
    session.editor = editor

    note_kb = KeyBindings()

    @note_kb.add("enter")
    @note_kb.add("c-s")
    def _save_note(event):
        _save_footnote_editor()

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
                Label(text="Enter/Ctrl+S saves · Esc cancels"),
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


def do_insert_footnote():
    """Insert a stable reference and append its simple definition object."""
    if _table_placeholder_locked():
        show_message(
            "Folded table",
            "Move the cursor off the folded table reference before inserting a footnote.",
        )
        return
    buf = text_area.buffer

    # The complete insertion, including replacement of any selected prose, is
    # one logical edit. Save before touching either text or object state.
    buf.save_to_undo_stack()
    if buf.selection_state is not None:
        buf.cut_selection()

    identifier = _next_footnote_identifier()
    reference = f"[^{identifier}]"
    pos = buf.cursor_position
    text = buf.text
    new_text = text[:pos] + reference + text[pos:]
    new_cursor = pos + len(reference)
    buf.document = Document(text=new_text, cursor_position=new_cursor)

    _set_committed_footnote(
        identifier,
        FootnoteData(
            identifier=identifier,
            text="",
            original_lines=None,
            dirty=True,
        ),
    )
    _append_footnote_placeholder(identifier, new_cursor)
    open_footnote_editor(identifier)


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
            # commit a table/footnote editor draft that the user has not saved yet.
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


def _default_wrapped_markdown_path():
    base = os.path.splitext(state.path)[0] if state.path else "untitled"
    return base + "-wrapped.md"


def _perform_text_export(out_path, content, expected_snapshot):
    """Atomically write a text export without touching the working document."""
    target_path = _canonical_path(out_path)
    directory = os.path.dirname(target_path) or "."
    basename = os.path.basename(target_path)
    temp_path = None
    fd = None

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

        try:
            existing_mode = stat.S_IMODE(os.stat(target_path).st_mode)
        except FileNotFoundError:
            existing_mode = None

        fd, temp_path = tempfile.mkstemp(
            prefix=f".{basename}.",
            suffix=".tmp",
            dir=directory,
            text=True,
        )
        if existing_mode is not None:
            os.fchmod(fd, existing_mode)
        else:
            current_umask = os.umask(0)
            os.umask(current_umask)
            os.fchmod(fd, 0o666 & ~current_umask)

        with os.fdopen(fd, "w", encoding="utf-8", newline="") as f:
            fd = None
            f.write(content)
            f.flush()
            os.fsync(f.fileno())

        if _disk_snapshot(target_path) != expected_snapshot:
            show_message(
                "Export destination changed",
                "The output file changed while Carriage was exporting. The newer file "
                "was left untouched; the staged export was discarded.",
            )
            return False

        if (
            expected_snapshot != _MISSING_DISK_SNAPSHOT
            and _path_is_read_only(target_path)
        ):
            show_message(
                "Read-only export destination",
                "The export destination became read-only while Carriage was exporting. "
                "Nothing was overwritten.",
            )
            return False

        os.replace(temp_path, target_path)
        temp_path = None
        show_message("Export complete", f"Wrote {out_path}")
        return True
    except (OSError, UnicodeError) as e:
        show_message("Export error", str(e))
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
    """Write a separate 80-column Markdown copy of the current document."""
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

        if (
            expected_snapshot != _MISSING_DISK_SNAPSHOT
            and _path_is_read_only(target_path)
        ):
            show_message(
                "Read-only export destination",
                "The export destination became read-only while Pandoc was running. "
                "Nothing was overwritten.",
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
            source_text = _materialize_objects(text_area.text)
        except ValueError as e:
            show_message("Document object error", str(e))
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
        visible = _collapse_objects_from_source(content)
        text_area.buffer.reset(Document(text=visible))
        state.saved_text = content
        state.disk_snapshot = disk_snapshot
        state.autosave_conflict = False

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
        width=D(preferred=70),
    )
    show_dialog(dialog, focus=help_body)

KEYBINDING_ROWS = [
    ("Ctrl+N", "New file"),
    ("Ctrl+O", "Open file"),
    ("Ctrl+S", "Save"),
    ("Ctrl+Z", "Undo"),
    ("Ctrl+R", "Redo"),
    ("Ctrl+Q", "Quit"),
    ("F7", "Spell check with aspell"),
    ("F10", "Open menu bar"),
    ("Ctrl+Space", "Open menu bar"),
    ("Ctrl+Home", "Go to top of document"),
    ("Ctrl+End", "Go to end of document"),
    ("Alt+Up", "Go to previous section"),
    ("Alt+Down", "Go to next section"),
    ("1-6", "Jump to File/Edit/Go/Export/Tools/Help"),
    ("Tab", "Indent normally; on a table or footnote, open its editor"),
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
            "Wrapping: Carriage soft-wraps visually at 80 columns without "
            "changing source line breaks. Edit > Convert for Carriage rewrites "
            "original Markdown plus pipe tables and footnotes into Carriage's "
            "preferred source form: Setext "
            "headings become ATX headings, simple ordered lists are renumbered "
            "consecutively from their first item, and hard-wrapped prose becomes logical "
            "source lines. Original Markdown hard breaks use two trailing spaces and "
            "display as ↵ in the editor; that marker is never written to the file. "
            "Export > Hard-Wrapped Markdown writes a separate 80-column Markdown copy."
        ),
        (
            "Tables: Arrow keys navigate table cells. Enter edits the "
            "selected cell; Enter again commits it. Shift+Tab from the first "
            "cell focuses the title field; Tab or Enter returns to the grid. "
            "Ctrl+R and Ctrl+C open row and column commands."
        ),
        (
            "Footnotes: Tools > Insert Footnote creates a standard Markdown "
            "reference and a folded single-paragraph definition. References "
            "display as [1], [2], and so on; Tab opens a simple note editor. "
            "Complex footnotes remain ordinary source."
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
        "Markdown soft-wraps visually inside an 80-column writing area without "
        "changing ordinary source line breaks. Hard wrapping is available only as "
        "a separate Markdown export. Supported tables and simple footnotes are "
        "folded into compact editing objects in the prose view, while the file "
        "on disk remains ordinary, portable Markdown."
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
                "End a line with two spaces to force a line break. Carriage displays",
                "that break as ↵; the marker is visual only.",
            ],
        ),
        (
            "Footnotes",
            [
                "    Text with a note.[^id]",
                "    [^id]: Footnote text",
                "Tools > Insert Footnote creates a simple standard footnote.",
                "Carriage folds single-paragraph definitions and displays",
                "references sequentially as [1], [2], and so on.",
            ],
        ),
        (
            "Tables",
            [
                "Use Tools > Insert Table to create a table, or edit a folded",
                "table placeholder with Tab or Tools > Edit Table at Cursor.",
                "Optional titles use Pandoc table captions and appear in the",
                "placeholder as [[Table N: Title]].",
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
    parsed = _atx_heading_parts(line)
    return parsed[1] if parsed is not None else None


def _current_section_title(doc):
    """Return the nearest recognized ATX heading at or before the cursor."""
    cursor_row = doc.cursor_position_row
    current = None
    for block in _analyze_document_layout(doc.text, WRAP_COLUMN):
        if block.start > cursor_row:
            break
        if block.kind == "heading" and block.source_lines:
            current = _heading_title(block.source_lines[0])
    return current


def _document_progress(doc):
    """Return cursor progress through the visible document as 0-100 percent."""
    if not doc.text:
        return 0
    return max(0, min(100, round(100 * doc.cursor_position / len(doc.text))))


def _document_heading_rows(doc):
    """Return recognized ATX heading rows in document order."""
    return [
        block.start
        for block in _analyze_document_layout(doc.text, WRAP_COLUMN)
        if block.kind == "heading"
    ]


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
        + 12  # save field ("save:paused")
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
        count_text = _materialize_objects(text_area.text)
    except ValueError:
        count_text = text_area.text

    words = len(re.findall(r"\S+", count_text))
    section = _current_section_title(doc)
    progress = _document_progress(doc)
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
    state_field = f"save:{save_status}"
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
                MenuItem("Convert for Carriage", handler=do_convert_for_carriage),
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
                MenuItem("-", disabled=True),
                MenuItem("Insert Footnote", handler=do_insert_footnote),
                MenuItem("Edit Footnote at Cursor   Tab", handler=do_edit_footnote_at_cursor),
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
    span = _footnote_source_span_at_cursor(buf.document)
    return span is not None and buf.document.cursor_position_col == span[1]


def _before_inline_footnote_reference():
    buf = text_area.buffer
    if buf.selection_state is not None:
        return False
    span = _footnote_source_span_at_cursor(buf.document)
    return span is not None and buf.document.cursor_position_col == span[0]


def _delete_inline_footnote_reference(buf):
    span = _footnote_source_span_at_cursor(buf.document)
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
    _delete_inline_footnote_reference(event.current_buffer)


@kb.add("delete", filter=editor_focused & Condition(_before_inline_footnote_reference))
def _(event):
    _delete_inline_footnote_reference(event.current_buffer)


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

    prefix_width = len(block.marker)
    converted = []
    for offset, line in enumerate(block.source_lines):
        if offset == 0:
            converted.append(line[prefix_width:])
        else:
            converted.append(line[prefix_width:])

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
    if _table_placeholder_locked():
        do_edit_table_at_cursor()
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
            width += get_cwidth(fragment[1])
    return width


def _visual_display_positions(row, info):
    """Map processed display columns on one logical line to (wrap row, x).

    This mirrors prompt_toolkit Window._copy_body's line-wrapping rule, but it
    operates only on one logical line and creates no screen. ``x`` is measured
    in rendered terminal cells inside the editor Window, after Carriage's
    display processor and continuation prefix have been applied.
    """
    if info is None or info.window_width <= 0:
        return None
    try:
        fragments = explode_text_fragments(info.ui_content.get_line(row))
    except Exception:
        return None

    width = info.window_width
    wrap_row = 0
    x = _line_prefix_cell_width(row, 0)
    positions = []

    for fragment in fragments:
        char = fragment[1]
        char_width = max(0, get_cwidth(char))
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
    return positions


def _source_visual_position(row, source_col, info):
    """Return (wrap row, x) for one source cursor position."""
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
    """Return the source column nearest ``preferred_x`` on a rendered row."""
    doc = text_area.buffer.document
    if not (0 <= row < doc.line_count):
        return None

    get_processed = getattr(text_area.control, "_last_get_processed_line", None)
    if get_processed is None:
        return None
    positions = _visual_display_positions(row, info)
    if not positions:
        return None

    try:
        processed = get_processed(row)
    except Exception:
        return None

    source_line = doc.lines[row]
    best = None
    for source_col in range(len(source_line) + 1):
        try:
            display_col = processed.source_to_display(source_col)
        except Exception:
            continue
        display_col = max(0, min(display_col, len(positions) - 1))
        candidate_wrap, candidate_x = positions[display_col]
        if candidate_wrap != wrap_row:
            continue

        distance = abs(candidate_x - preferred_x)
        # When two source positions map to the same visual place (for example,
        # inside a compact footnote display span), prefer a boundary closest to
        # the requested x, then the earlier source position. Left/Right retain
        # their existing atomic-object behavior once the cursor lands there.
        score = (distance, source_col)
        if best is None or score < best[0]:
            best = (score, source_col)

    return None if best is None else best[1]


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

    text_area.window.end_manual_scroll()
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
    folded table sentinels and hidden list-continuation indentation, so selection
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

    placeholder = FOOTNOTE_PLACEHOLDER_RE.match(doc.current_line)
    if placeholder:
        if delta > 0 and col < len(doc.current_line):
            buf.cursor_position = doc.translate_row_col_to_index(row, len(doc.current_line))
            return
        if delta < 0 and col > 0:
            buf.cursor_position = doc.translate_row_col_to_index(row, 0)
            return

    footnote_span = _footnote_source_span_at_cursor(doc)
    if footnote_span is not None:
        start_col, end_col, _identifier = footnote_span
        if delta > 0 and col < end_col:
            buf.cursor_position = doc.translate_row_col_to_index(row, end_col)
            return
        if delta < 0 and col > start_col:
            buf.cursor_position = doc.translate_row_col_to_index(row, start_col)
            return

    if delta > 0:
        # TABLE_SENTINEL is an internal zero-width marker attached to folded
        # table references. Skip it without consuming a visible cursor step.
        at_line_end = doc.cursor_position_col == len(doc.current_line)
        continuation_width = (
            _list_continuation_prefix_width(doc, row + 1)
            if at_line_end and row + 1 < doc.line_count
            else None
        )
        while pos < len(text) and text[pos] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
            pos += 1
        if pos < len(text):
            pos += 1
        if continuation_width is not None:
            pos = min(len(text), pos + continuation_width)
        while pos < len(text) and text[pos] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
            pos += 1
    elif delta < 0:
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
            while pos > 0 and text[pos - 1] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
                pos -= 1
            if pos > 0:
                pos -= 1
            while pos > 0 and text[pos - 1] in {TABLE_SENTINEL, FOOTNOTE_SENTINEL}:
                pos -= 1

    buf.cursor_position = pos


@kb.add("s-up", filter=editor_focused)
def _(event):
    _move_editor_selection_visual_rows(-1)


@kb.add("s-down", filter=editor_focused)
def _(event):
    _move_editor_selection_visual_rows(1)


@kb.add("up", filter=editor_focused)
def _(event):
    _move_editor_cursor_visual_rows(-1)


@kb.add("down", filter=editor_focused)
def _(event):
    _move_editor_cursor_visual_rows(1)


@kb.add("s-right", filter=editor_focused)
def _(event):
    _move_editor_selection_across_lines(1)


@kb.add("s-left", filter=editor_focused)
def _(event):
    _move_editor_selection_across_lines(-1)


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
        "markdown.footnote-ref": f"{EF_AQUA} bold",
        "markdown.hard-break": f"{EF_GREY1} bold",
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
                text_area.text = _collapse_objects_from_source(content)
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
