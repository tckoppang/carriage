# Carriage Help

## Keyboard reference

| Command | Action |
|---|---|
| `Ctrl+N` | New file |
| `Ctrl+O` | Open file |
| `Ctrl+S` or `F9` | Save |
| `Ctrl+Z` | Undo |
| `Ctrl+R` | Redo |
| `Ctrl+X` | Cut to the Carriage clipboard |
| `Ctrl+C` | Copy to the Carriage clipboard |
| `Ctrl+V` | Paste from the Carriage clipboard |
| `Ctrl+Q` | Quit |
| `F1` | Carriage Help |
| `F2` | Toggle italic on selected text |
| `F3` | Toggle bold on selected text |
| `F4` | Insert table |
| `F5` | Insert footnote |
| `F6` | Toggle Extend Selection mode |
| `F7` | Spell check |
| `F8` | Renumber the numbered list at the cursor |
| `F10` or `Ctrl+Space` | Open the menu bar |
| `Home` / `End` | Start / end of the displayed row |
| `Ctrl+Home` / `Ctrl+End` | Top / end of the document |
| `Alt+Up` / `Alt+Down` | Previous / next ATX section |
| `1` through `6` | Jump among File, Edit, Go, Export, Tools, and Help while the menu bar is active |
| `Tab` | Indent normally; edit a folded table or footnote at the cursor |
| `Esc` | Close a menu or dialog |

## Selection

`F6` toggles Extend Selection mode. While it is active:

- Left and Right select by character.
- Up and Down select by displayed row.
- Ctrl+Left and Ctrl+Right select by word.
- Home and End extend to the displayed-row boundary.
- Ctrl+Home and Ctrl+End extend to the document boundary.

Press `F6` again to leave the mode while preserving the selection. Shift-based selection shortcuts remain available when the terminal passes them through.

Double-click selects a word. Triple-click selects the current paragraph or list item. Structural Markdown shown in the hanging gutter is not a cursor destination.

## Clipboard

`Ctrl+X`, `Ctrl+C`, and `Ctrl+V` use Carriage's internal clipboard. They do not automatically exchange text with the desktop clipboard.

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

Ambiguous or line-sensitive Markdown is preserved. **Export > Hard-Wrapped Markdown** writes a separate wrapped copy without modifying the working file.

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

`F4` or **Tools > Insert Table** creates a basic table with 2 to 6 columns and 1 to 20 data rows.

In the table editor:

- Arrow keys navigate cells.
- Enter edits the selected cell and Enter again commits it.
- Shift+Tab from the first cell focuses the optional title.
- Tab or Enter returns from the title to the grid.
- `R` opens row commands in navigation mode.
- `C` opens column commands in navigation mode.
- Save commits the table; Cancel discards the table-editor session.

Imported tables wider than six columns are preserved as Markdown but cannot be opened in the basic editor.

## Footnotes

`F5` or **Tools > Insert Footnote** creates a standard inline reference and a folded single-paragraph definition. References display sequentially as `[1]`, `[2]`, and so on. `Tab` opens the associated editor.

Adjacent references remain separate atomic objects. Complex footnotes remain ordinary Markdown source.

## Spell check and export

Spell check works on a saved file. Carriage offers to save unsaved changes before starting the configured terminal checker. The file is reloaded only when the checker exits successfully.

Pandoc exports run without blocking normal editing, and only one Pandoc export can run at a time. Built-in targets are PDF, DOCX, ODT, and standalone HTML, plus a custom Pandoc command. Hard-wrapped Markdown does not require Pandoc.

## Configuration

Settings are read at startup from `$XDG_CONFIG_HOME/carriage/config.toml`, or `~/.config/carriage/config.toml` when `XDG_CONFIG_HOME` is unset.

The file controls prose width, scrollbar visibility, startup status-bar visibility, mouse support, the hard-break marker, the Pandoc executable, and the spell-check command. Carriage has no Preferences dialog. Invalid entries are reported and ignored without discarding valid neighboring settings.
