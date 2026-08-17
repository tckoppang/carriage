# Carriage Help

## Keyboard reference

- `Ctrl+N` - New file.
- `Ctrl+O` - Open file.
- `Ctrl+S` or `F9` - Save.
- `Ctrl+Z` - Undo.
- `Ctrl+R` - Redo.
- `Ctrl+F` - Find / replace.
- `Ctrl+X` - Cut to the clipboard.
- `Ctrl+C` - Copy to the clipboard.
- `Ctrl+V` - Paste from the clipboard.
- `Ctrl+Q` - Quit.
- `F1` - Carriage Help.
- `F2` - Toggle italic on selected text.
- `F3` - Toggle bold on selected text.
- `F4` - Insert table.
- `F5` - Insert footnote.
- `F6` - Toggle Extend Selection mode.
- `F7` - Spell check.
- `F8` - Renumber the numbered list at the cursor.
- `F10` or `Ctrl+Space` - Open the menu bar.
- `Home` / `End` - Start / end of the displayed row.
- `Ctrl+Home` / `Ctrl+End` - Top / end of the document.
- `Alt+G` - Go directly to an ATX section.
- `Alt+Up` / `Alt+Down` - Previous / next ATX section.
- `1` through `6` - Jump among File, Edit, Go, Export, Tools, and Help while the menu bar is active.
- `Tab` - Indent normally; edit a folded table or footnote at the cursor.
- `Esc` - Close a menu, dialog, or Find / Replace.

## Selection

`F6` toggles Extend Selection mode. While it is active:

- Left and Right select by character.
- Up and Down select by displayed row.
- Ctrl+Left and Ctrl+Right select by word.
- Home and End extend to the displayed-row boundary.
- Ctrl+Home and Ctrl+End extend to the document boundary.

Press `F6` again to leave the mode while preserving the selection. Shift-based selection shortcuts remain available when the terminal passes them through.

Double-click selects a word. Triple-click selects the current paragraph or list item. Structural Markdown shown in the hanging gutter is not a cursor destination.

## Navigation

`Alt+G` opens **Go to Section**, a temporary hierarchical list of the document's recognized ATX headings. The current section is selected when the dialog opens. Type to filter by visible heading text, use Up and Down to choose a result, and press Enter to jump with that heading aligned at the top of the editor. Esc cancels without moving the document cursor.

`Alt+Up` and `Alt+Down` remain the faster commands for moving directly to the previous or next section.

## Find and replace

`Ctrl+F` opens Find / Replace on the status-line row. Search is literal, begins at the current cursor position, and wraps around the document. If a single-line selection is active, it becomes the initial search term.

While the Find field is active:

- Enter or Down moves to the next match.
- Up moves to the previous match.
- Tab switches to Replace.
- `Alt+C` toggles case-sensitive matching.
- `Alt+W` toggles whole-word matching.
- Esc closes Find / Replace and returns to the document.

While the Replace field is active, Enter replaces the current match and advances, Down skips to the next match, Up moves to the previous match, and `Alt+A` replaces all matches. Replace All is recorded as one undoable document change. Tab or Shift+Tab returns to Find.

Carriage does not use regular expressions for Find / Replace. Find / Replace searches ordinary visible document text. Folded table and footnote placeholder lines and their hidden contents are excluded from search. Structurally complex footnotes that remain ordinary Markdown are searched normally.

## Clipboard

`Ctrl+X`, `Ctrl+C`, and `Ctrl+V` exchange plain text with the desktop system clipboard when an available platform backend is present. Windows uses native clipboard support; macOS uses `pbcopy`/`pbpaste`; Linux uses `wl-copy`/`wl-paste` from **wl-clipboard** under Wayland, or `xclip`/`xsel` under X11. Linux clipboard helpers are optional. If no system clipboard backend is available, Carriage automatically falls back to its internal clipboard, so Cut/Copy/Paste continue to work within Carriage. Pasted CRLF or CR line endings are normalized to LF.

## Emphasis

Select text and press `F2` for italic or `F3` for bold. The attributes toggle independently, so applying both produces bold italic.

Carriage-generated emphasis uses asterisks. Leading and trailing selection whitespace remains outside the markers. If Carriage cannot identify a safe transformation, the source and selection are left unchanged and a short explanation appears on the status line.

## Wrapping and conversion

Ordinary prose soft-wraps visually at the configured prose width without changing source line breaks.

**Edit > Convert for Carriage** can:

- convert supported Setext headings to ATX
- renumber straightforward ordered lists
- normalize straightforward underscore emphasis to asterisks
- join supported hard-wrapped prose into logical source lines
- recognize supported tables and footnotes

Ambiguous or line-sensitive Markdown is preserved. This includes unsupported table forms such as headerless or malformed pipe-table runs and Pandoc grid/simple tables, as well as fenced containers and definition lists. **Export > Hard-Wrapped Markdown** uses the same conservative block classification and writes a separate wrapped copy without modifying the working file.

Two trailing spaces create a Markdown hard line break. When enabled, Carriage displays the break as `↵`. The marker is visual only.

## Renumber List

`F8` or **Edit > Renumber List** changes only the supported numbered list containing the cursor. The first item's number is preserved and the following items are made consecutive.

## Saving and recovery

The Markdown file advances only through explicit Save or Save As. Unsaved work is protected separately in a private recovery journal.

The journal is normally updated two seconds after editing becomes idle and at least every ten seconds during sustained editing. Saves use durable atomic replacement and detect external file changes. After an abnormal exit, Carriage offers to restore or discard recovered work.

Recovery is not a substitute for backups or version control.

## Opening and naming

Carriage reads UTF-8 Markdown, normalizes line endings to LF, and asks before loading files larger than 8 MiB.

Save As suggests a filename from the first recognized ATX heading. It uses visible heading text, stops before a subtitle colon, removes Markdown formatting, neutralizes unsafe filename characters, and shortens a long title only at a useful word boundary.

## Tables

`F4` or **Tools > Insert Table** creates a basic table with 2 to 6 columns and 1 to 60 data rows. Existing and imported tables with up to six columns can be edited regardless of row count.

In the table editor:

- Arrow keys navigate cells.
- Enter edits the selected cell and Enter again commits it.
- Shift+Tab from the first cell focuses the optional title.
- Tab or Enter returns from the title to the grid.
- `R` opens row commands in navigation mode.
- `C` opens column commands in navigation mode.
- Save commits the table; Cancel discards the table-editor session.

Imported tables wider than six columns are preserved as Markdown but cannot be opened in the basic editor. Headerless-looking pipe tables can use a blank header row and remain editable.

## Footnotes

`F5` or **Tools > Insert Footnote** creates a standard inline reference and a folded prose definition. References display sequentially as `[1]`, `[2]`, and so on. `Tab` opens the associated multiline editor. Enter inserts a line break; a blank line starts a new paragraph; `Ctrl+S` saves.

Adjacent references remain separate atomic objects. Footnotes containing structural blocks such as lists, blockquotes, code, raw HTML, reference definitions, thematic breaks, or tables remain ordinary Markdown source. The editor refuses to save structural Markdown into a folded prose footnote.

## Spell check and export

Spell check works on a saved file. Carriage offers to save unsaved changes before starting the configured terminal checker. The file is reloaded only when the checker exits successfully.

Pandoc exports run without blocking normal editing, and only one Pandoc export can run at a time. Built-in targets are PDF, DOCX, ODT, and standalone HTML, plus a custom Pandoc command. Hard-wrapped Markdown does not require Pandoc.

## Configuration

Settings are read at startup from `$XDG_CONFIG_HOME/carriage/config.toml`, or `~/.config/carriage/config.toml` when `XDG_CONFIG_HOME` is unset.

The file controls prose width, scrollbar visibility, startup status-bar visibility, mouse support, the hard-break marker, the Pandoc executable, and the spell-check command. Carriage has no Preferences dialog. Invalid entries are reported and ignored without discarding valid neighboring settings.
