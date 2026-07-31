<p align="center">
  <img src="assets/carriage-logo.svg" width="350" alt="Carriage Logo">
</p>

<p>
  <h1 align="center">Carriage</h1>
</p>

<p align="center">
  <strong>A prose-first Markdown editor for the terminal.</strong>
</p>

Carriage is built around writing documents rather than editing source code. It gives ordinary prose a focused writing area that is 80 columns wide by default, keeps Markdown structure out of the way where practical, and leaves the document on disk as ordinary, portable Markdown.

The goal is not to hide Markdown or replace it with a proprietary document format. Carriage is intended to make Markdown feel more like a writing environment while preserving the advantages of plain text.

## Writing first

Carriage treats prose as the primary unit of work.

Ordinary paragraphs soft-wrap visually within a configurable prose width, 80 columns by default, without inserting line breaks into the Markdown source. On wide terminals, the prose area is centered, while list markers and ATX heading markers can hang into the left margin and blockquotes use a display-only gutter so the prose itself remains aligned.

The result is a document that reads naturally in Carriage without filling the underlying Markdown file with editor-specific formatting.

Carriage takes a deliberately conservative approach to Markdown. It handles the straightforward structures it intentionally supports, does not try to repair malformed Markdown, and leaves line-sensitive structures outside its conversion model unchanged rather than guessing at their meaning.

## Markdown stays Markdown

Carriage works directly with ordinary Markdown files.

There is no Carriage document format. A file written in Carriage can still be opened in another text editor, tracked in Git, processed with Pandoc, or moved to another Markdown workflow.

### Convert for Carriage

Existing Markdown can be normalized with **Edit > Convert for Carriage**.

Conversion brings supported, valid Markdown into Carriage's preferred source form while preserving line-sensitive structures that Carriage does not safely reflow. Among other things, it:

- converts Setext headings to ATX headings
- normalizes supported ATX heading form
- renumbers simple ordered lists consecutively from the first item's existing number
- joins supported hard-wrapped prose into logical source lines
- preserves original Markdown hard breaks and structural blocks whose physical layout is significant

Conversion is intentionally conservative. It is a normalization command, not a Markdown repair tool; complex structures outside Carriage's supported conversion model are left unchanged.

### Hard line breaks

Markdown hard line breaks made with two trailing spaces are preserved.

Because trailing spaces are otherwise invisible, Carriage displays a `↵` marker at a valid hard break by default. The marker exists only in the editor and is never written to the Markdown file; its display can be disabled through the advanced configuration file.

## Tables

Supported Markdown pipe tables become first-class objects in Carriage.

In the prose view, a table is folded into a compact reference such as:

```text
[[Table 1: Movement Rates]]
```

Pressing `Tab` on the reference opens the table editor for supported tables of two through six columns. Tables can have titles, and rows, columns, headers, and cell contents can be edited without turning the main writing view into a grid of Markdown syntax. Existing Markdown column alignment is preserved when tables are edited.

The table editor has a navigation mode and a cell-editing mode. Arrow keys move among cells, `Enter` edits the selected cell, `R` opens row commands, and `C` opens column commands. In editable table text, the normal `Ctrl+X`, `Ctrl+C`, and `Ctrl+V` cut, copy, and paste shortcuts remain available.

On disk, the table remains a Markdown pipe table; optional titles use Pandoc-style table captions. Recognized tables wider than six columns can remain folded in the prose view but are not editable in the basic table editor. Table-like structures Carriage does not recognize remain ordinary Markdown source.

## Footnotes

Carriage also provides first-class support for simple Pandoc-style Markdown footnotes.

References are displayed as sequential footnote numbers in the prose view, while their definitions are folded out of the main text. Pressing `Tab` at a footnote opens its dedicated editor. The footnote editor uses the same `Ctrl+X`, `Ctrl+C`, and `Ctrl+V` cut, copy, and paste shortcuts as the main editor. `Enter` or `Ctrl+S` saves the footnote, and `Esc` cancels.

The saved document uses Pandoc-style Markdown footnote syntax. More complex footnotes that Carriage does not support as objects remain ordinary source.

## Undo and redo

Undo and redo operate across the document rather than only on visible prose.

Changes to prose, tables, footnotes, and their associated document state participate in the same chronological undo history. Editing a table or footnote therefore behaves as part of editing the document, rather than as a separate operation outside normal undo and redo.

## Saving and recovery

Carriage separates **protecting unsaved work** from **saving the Markdown file**.

While you edit, Carriage continuously protects the current working state in a private recovery journal without changing the document during ordinary editing. After editing has been idle for about two seconds, Carriage schedules a checkpoint. During sustained editing, it schedules one after about ten seconds even without an idle pause, so continuous typing cannot postpone protection indefinitely. The journal includes prose, tables, footnotes, the cursor position, and in-progress table or footnote drafts. Untitled documents are protected too.

During ordinary editing, Carriage writes changes to the Markdown file only when you explicitly use **Save**, **Save As**, `Ctrl+S`, or `F9`. A successful save uses durable atomic replacement, makes the current working state the new saved baseline, and removes the now-unneeded recovery journal. Choosing **Don't Save** when leaving a modified document deliberately discards the protected changes and leaves the last manually saved Markdown file intact. Spell checking is a separate user-invoked operation: the configured external spell checker may edit the source file in place, after which Carriage reloads it.

After an abnormal exit, Carriage detects an abandoned recovery journal and offers to restore the protected work, discard it, or leave it for later. Recovery is a safety mechanism, not version history or a substitute for backups.

Carriage also tracks the exact version of the source file that was opened or last successfully saved. If another program changes, replaces, or deletes that file before the next manual save, Carriage detects the conflict rather than silently overwriting the external changes.

## Preferences

**Edit > Preferences** exposes the small set of settings intended for routine adjustment:

- prose width, from 40 to 160 columns
- scrollbar on or off

Working-state protection is automatic and is not a preference. Carriage stores settings in `$XDG_CONFIG_HOME/carriage/config.toml`, or `~/.config/carriage/config.toml` when `XDG_CONFIG_HOME` is not set. A few advanced settings can be edited there manually, including startup status-bar visibility, mouse support, the hard-break marker, the Pandoc executable, and the external spell-check command.

The **Edit > Toggle Status Bar** command changes status-bar visibility for the current session only.

## Export

Carriage can create a separate hard-wrapped Markdown copy of a document without changing the working file.

**Export > Hard-Wrapped Markdown** produces Markdown wrapped to the configured prose width while preserving structures that should not be reflowed.

With Pandoc installed, Carriage has built-in export commands for:

- PDF
- DOCX
- ODT
- HTML

**Export > Custom pandoc command** also allows other Pandoc conversions by supplying an output path and additional Pandoc arguments. Plain-text export is not a built-in Carriage export option.

Pandoc is optional and is not required for normal editing.

## Other features

Carriage also includes:

- lightweight Markdown highlighting
- prose-aware word counting
- mouse support and scrolling
- menus and keyboard shortcuts
- document and section navigation
- configurable external terminal spell checking, with Aspell as the default
- built-in keybinding reference
- built-in Markdown syntax reference
- New, Open, Save, and Save As
- automatic filename suggestions for untitled documents based on the first ATX heading

Highlighting and other display features are visual only. They do not add Carriage-specific markup to the saved file.

## Beta status

> **Carriage is beta software.**
>
> It is under active development and has not yet received the breadth of real-world testing expected of a mature text editor. Although Carriage includes atomic saving, external-change detection, and continuous working-state recovery, important writing should still be backed up or kept under version control.

## Requirements

Carriage requires:

- Python 3.10 or newer
- `prompt_toolkit`

Optional external tools provide additional features:

- **Aspell plus an appropriate dictionary**: the default spell-check setup; another interactive terminal spell checker that accepts the supplied document path, edits that file in place, and returns when finished can be configured manually
- **Pandoc**: PDF, DOCX, ODT, HTML, and custom document export
- a PDF engine supported by Pandoc: PDF export only

## Installation

### Recommended: Python virtual environment

Clone or download Carriage and open a terminal in its directory.

Release files use the `carriage_vY.XX.py` naming scheme. Create a stable `carriage.py` symlink pointing to the version you installed:

```bash
ln -s carriage_vY.XX.py carriage.py
```

Create a virtual environment:

```bash
python3 -m venv .venv
```

Activate it:

```bash
source .venv/bin/activate
```

Install the required dependency:

```bash
python -m pip install prompt_toolkit
```

Run Carriage:

```bash
python carriage.py
```

Or open a Markdown file directly:

```bash
python carriage.py document.md
```

### Fedora

Fedora users can install `prompt_toolkit` from the system repositories instead:

```bash
sudo dnf install python3-prompt-toolkit
```

Optional default spell-checking and export tools can also be installed through DNF:

```bash
sudo dnf install aspell aspell-en pandoc-cli pandoc-pdf
```

`aspell-en` supplies the English dictionary for Aspell. `pandoc-pdf` installs Fedora's Pandoc PDF-support metapackage; it is not needed for DOCX, ODT, or HTML export.

Then run:

```bash
python3 carriage.py
```

You can also make the script executable:

```bash
chmod +x carriage.py
./carriage.py
```

## Create a `carriage` command

Using the stable `carriage.py` symlink means your shell configuration does not need to change when Carriage is updated.

If Carriage uses its own virtual environment, add the following to `~/.zshrc` or `~/.bashrc`, replacing `/path/to/carriage` with the actual directory:

```bash
alias carriage='/path/to/carriage/.venv/bin/python /path/to/carriage/carriage.py'
```

If `prompt_toolkit` is installed system-wide:

```bash
alias carriage='python3 /path/to/carriage/carriage.py'
```

You can then open Carriage from anywhere:

```bash
carriage
```

Or open a document:

```bash
carriage document.md
```

When installing a new release, update the stable symlink:

```bash
ln -sf carriage_vY.XX.py carriage.py
```

## Using Carriage

Press `F10` or `Ctrl+Space` to activate the menu bar. The **Help** menu contains the current Carriage keybinding reference and a concise Markdown syntax reference.

Carriage uses familiar editing shortcuts where the terminal permits them:

| Shortcut | Action |
| --- | --- |
| `Ctrl+N` | New file |
| `Ctrl+O` | Open file |
| `Ctrl+S` | Save |
| `F9` | Save |
| `Ctrl+Z` | Undo |
| `Ctrl+R` | Redo |
| `Ctrl+X` | Cut |
| `Ctrl+C` | Copy |
| `Ctrl+V` | Paste |
| `Ctrl+Q` | Quit |
| `F1` | Carriage Help |
| `F6` | Toggle Extend Selection mode |
| `F7` | Spell check |
| `F8` | Renumber the numbered list at the cursor |
| `F10` / `Ctrl+Space` | Open the menu bar |
| `Ctrl+Home` / `Ctrl+End` | Go to top / end of document |
| `Alt+Up` / `Alt+Down` | Previous / next section |
| `Tab` | Indent, or open a folded table or footnote |

### Selection

The usual Shift-based selection shortcuts remain available when the terminal emulator passes them through. Because some terminal emulators reserve combinations such as `Ctrl+Shift+Left` and `Ctrl+Shift+Right`, Carriage also provides a portable Extend Selection mode.

Press `F6` to enter Extend Selection mode. While it is active:

- `Left` / `Right` extends by character
- `Up` / `Down` extends by displayed row
- `Ctrl+Left` / `Ctrl+Right` extends by word
- `Home` / `End` extends to the current line boundary
- `Ctrl+Home` / `Ctrl+End` extends to the document boundary

Press `F6` again to leave Extend Selection mode while keeping the selection. With mouse support enabled, double-click selects a word and triple-click selects the current paragraph or list item.

Status-bar visibility is controlled from **Edit > Toggle Status Bar** rather than by a dedicated keyboard shortcut. The interface is intended to expose document operations through menus without requiring users to memorize a large command set.

## Design philosophy

Carriage is deliberately not a full Markdown IDE.

It is a writing tool built around a narrower idea: make ordinary Markdown prose comfortable to write in a terminal while keeping the document portable, predictable, and understandable outside the application.

Where Carriage understands the structure, it can provide a better writing interface for it. Where structure falls outside its supported editing and conversion model, Carriage avoids trying to repair it or turn it into something else.

The file belongs to the writer, not the editor.

## License

Carriage is licensed under the MIT License. See `LICENSE` for details.
