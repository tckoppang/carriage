# Carriage Features To-Do List

## Current priority

1. Add support for **switching files** within the same working directory as the current file, with a natural path toward project-folder navigation.

## Table editor

1. **Dynamic column widths.** Size columns according to their contents instead of dividing the grid evenly. Short-content columns should remain narrow while text-heavy columns receive more of the available width, subject to sensible minimum and maximum widths. Recalculate the layout when table contents or terminal size changes.

2. **Better handling of oversized cells.** Prevent a single text-heavy cell from making an entire table row awkwardly tall. Keep the grid compact with bounded display height and a clear overflow indication, while preserving the complete cell contents for editing. Improve the editing experience for long cell contents.

3. **Row and column reordering.** Provide a straightforward way to move an existing row or column without manually cutting and rebuilding the table.

4. **Column alignment editing.** Allow the table editor to set the Markdown alignment for a column: default, left, center, or right.

5. **Table-grid mouse support.** Add mouse-wheel scrolling, click-to-select cells, and double-click-to-edit. This is lower priority than the layout, large-cell, reordering, and alignment work above.

## Status bar

- **Viewport-aware progress percentage.** During normal editing, continue to calculate document progress from the insertion point. While manual mouse-wheel or scrollbar scrolling owns the viewport, show progress based on the visible viewport instead. Return to insertion-point progress when normal editing resumes.

## Possible later improvements

- Add targeted mouse support to other custom secondary views where normal mouse interaction is still absent.
- Allow optional saved Pandoc/export presets.
- Allow selective shortcut remapping for terminal or desktop key conflicts.

## Low-priority possibilities

- Show richer information in the recovery dialog, such as recovery age or timestamp and a useful indication of the amount of unsaved work.
- Add a lightweight document-statistics dialog for structural information beyond the existing word count and progress display.

## Completed from the original list

- **Find and replace:** `Ctrl+F` opens literal Find / Replace with match counts, wrap feedback, case-sensitive and whole-word options, and a single-step Replace All undo.
- **System clipboard:** Carriage uses the desktop clipboard when a supported platform backend is available, with an internal fallback.
- **Direct section selection:** `Alt+G` / **Go > Go to Section** provides a searchable hierarchical heading navigator in addition to previous/next section commands.
- **Multi-paragraph footnotes:** supported prose footnotes can contain multiple paragraphs and are edited in the folded footnote editor.
