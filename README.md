<p align="center">
  <img src="assets/carriage-logo.svg" width="500" alt="Carriage">
</p>

<p align="center">
  <h2>Carriage</h2>
  <strong>A prose-first Markdown editor for the terminal.</strong>
</p>

Carriage is built around writing documents rather than editing source code. It gives ordinary prose a focused 80-column writing area, keeps Markdown structure out of the way where practical, and leaves the document on disk as ordinary, portable Markdown.

The goal is not to hide Markdown or replace it with a proprietary document format. Carriage is intended to make Markdown feel more like a writing environment while preserving the advantages of plain text.

## Writing first

Carriage treats prose as the primary unit of work.

Ordinary paragraphs soft-wrap visually within an 80-column writing area without inserting line breaks into the Markdown source. On wide terminals, the prose area is centered, while list markers and ATX heading markers can hang into the left margin so the text itself remains aligned.

The result is a document that reads naturally in Carriage without filling the underlying Markdown file with editor-specific formatting.

Carriage takes a deliberately conservative approach to Markdown. It handles straightforward structures it understands and preserves structural, complex, or ambiguous Markdown rather than attempting to repair or reinterpret it.

## Markdown stays Markdown

Carriage works directly with ordinary Markdown files.

There is no Carriage document format. A file written in Carriage can still be opened in another text editor, tracked in Git, processed with Pandoc, or moved to another Markdown workflow.

### Convert for Carriage

Existing Markdown can be normalized with **Edit > Convert for Carriage**.

Conversion brings valid Markdown into Carriage's preferred source form while preserving structures that cannot be safely converted. Among other things, it:

- converts Setext headings to ATX headings
- converts supported hard-wrapped prose to logical source lines
- recognizes supported pipe tables and footnotes as Carriage objects
- preserves Markdown structures whose physical line layout is significant

Conversion is intentionally conservative. Unsupported, complex, or ambiguous structures are preserved rather than repaired.

### Hard line breaks

Markdown hard line breaks made with two trailing spaces are preserved.

Because trailing spaces are otherwise invisible, Carriage displays a `↵` marker at a valid hard break. The marker exists only in the editor and is never written to the Markdown file.

## Tables

Supported Markdown pipe tables become first-class objects in Carriage.

In the prose view, a table is folded into a compact reference such as:

```text
[[Table 1: Movement Rates]]
```

Pressing `Tab` on the reference opens the table editor. Tables can have titles, and rows, columns, headers, alignment, and cell contents can be edited without turning the main writing view into a grid of Markdown syntax.

On disk, the table remains an ordinary Markdown pipe table.

Complex or unsupported tables remain ordinary Markdown source.

## Footnotes

Carriage also provides first-class support for simple Markdown footnotes.

References are displayed as sequential footnote numbers in the prose view, while their definitions are folded out of the main text. Pressing `Tab` at a footnote opens its dedicated editor.

The saved document uses ordinary Markdown footnote syntax. More complex footnotes that Carriage does not support as objects remain ordinary source.

## Undo and redo

Undo and redo operate across the document rather than only on visible prose.

Changes to prose, tables, footnotes, and their associated document state participate in the same chronological undo history. Editing a table or footnote therefore behaves as part of editing the document, rather than as a separate operation outside normal undo and redo.

## Saving and recovery

Carriage is designed to protect the Markdown file it is editing.

Named documents can autosave every 30 seconds. Saves use durable atomic replacement so the existing file is not truncated by a failed write.

Carriage also tracks the version of the file that was originally opened or last successfully saved. If another program changes the file on disk, Carriage detects the conflict rather than silently overwriting the external changes.

Modified documents receive separate crash-recovery snapshots so unsaved work can be recovered independently of the normal saved file.

## Export

Carriage can create a separate hard-wrapped Markdown copy of a document without changing the working file.

**Export > Hard-Wrapped Markdown** produces Markdown wrapped for an 80-column source file while preserving structures that should not be reflowed.

With Pandoc installed, Carriage can also export to:

- PDF
- DOCX
- ODT
- HTML
- plain text
- custom Pandoc formats

Pandoc is optional and is not required for normal editing.

## Other features

Carriage also includes:

- lightweight Markdown highlighting
- mouse support and scrolling
- menus and keyboard shortcuts
- document and section navigation
- Aspell spell checking
- built-in keybinding reference
- built-in Markdown syntax reference
- New, Open, Save, and Save As
- automatic filename suggestions for untitled documents based on the first ATX heading

Highlighting and other display features are visual only. They do not add Carriage-specific markup to the saved file.

## Beta status

> **Carriage is beta software.**
>
> It is under active development and has not yet received the breadth of real-world testing expected of a mature text editor. Although Carriage includes atomic saving, external-change detection, autosave, and crash recovery, important writing should still be backed up or kept under version control.

## Requirements

Carriage requires:

- Python 3.10 or newer
- `prompt_toolkit`

Optional external tools provide additional features:

- **Aspell**: spell checking
- **Pandoc**: document export
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

Optional spell-checking and export tools can also be installed through DNF:

```bash
sudo dnf install aspell aspell-en pandoc-cli pandoc-pdf
```

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

Press `F10` or `Ctrl+Space` to activate the menu bar.

The **Help** menu contains the current keybinding reference and a concise Markdown syntax reference. The interface itself is intended to expose most document operations through menus rather than requiring users to memorize a large command set.

## Design philosophy

Carriage is deliberately not a full Markdown IDE.

It is a writing tool built around a narrower idea: make ordinary Markdown prose comfortable to write in a terminal while keeping the document portable, predictable, and understandable outside the application.

Where Carriage understands the structure, it can provide a better writing interface for it. Where it does not, it preserves the Markdown rather than guessing.

The file belongs to the writer, not the editor.

## License

Carriage is licensed under the MIT License. See `LICENSE` for details.
