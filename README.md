# Carriage

Carriage is a prose-first Markdown editor for the terminal. It is built around
the needs of people who are writing documents rather than writing code.

Most terminal editors treat prose as just another kind of source text. Carriage
takes the opposite approach. Paragraphs are the primary unit of work, line
wrapping and reflow are Markdown-aware, and the interface is deliberately
structured around drafting, revising, navigating, and formatting written
documents. Markdown remains the underlying file format, but the editor tries to
keep the mechanics of Markdown from becoming the center of the writing
experience.

The goal is not to hide Markdown or replace it with a proprietary document
format. Carriage keeps your work as ordinary, portable Markdown that can be
opened in any text editor, tracked in Git, converted with Pandoc, or moved to
another tool at any time. Its job is to make that Markdown feel more like a
writing environment and less like a programming workspace.

Carriage provides an 80-column writing area, Markdown-aware wrapping and
reflow, mouse support, menus, autosave, lightweight syntax highlighting,
document navigation, table editing, spell checking through Aspell, and document
export through Pandoc. Features are chosen for their usefulness to prose work,
with an emphasis on readability, predictable editing behavior, and preserving
the document's underlying Markdown.

## Beta status and data-loss warning

> **Carriage should currently be considered beta-quality software.**
>
> It is under active development and has not yet had the breadth of testing
> expected of a mature text editor. Bugs may still exist, including bugs that
> could cause unsaved changes to be lost or, in the worst case, damage or
> overwrite a document.
>
> **Do not use Carriage as the only repository for important writing.** Keep
> regular backups or use version control, cloud file history, snapshots, or
> another recovery mechanism appropriate to your workflow. Autosave is a
> convenience feature, not a substitute for backups.
>
> Until Carriage has seen wider real-world testing, treat it as a beta release
> and use it with appropriate caution on irreplaceable files.

## Requirements

Carriage requires:

- Python 3.10 or newer
- `prompt_toolkit`

Optional external tools enable additional features:

- **Aspell**: spell checking
- **Pandoc**: PDF, DOCX, ODT, HTML, and plain-text export
- A PDF engine supported by Pandoc: required only for PDF export

Carriage itself does not require GTK, Qt, or another graphical toolkit.

## Installation

### Recommended: Python virtual environment

Download or clone Carriage, then open a terminal in the Carriage directory.

Release files are named using the `carriage_vY.XX.py` pattern. In the commands
below, replace `Y.XX` with the version you downloaded. First, create a stable
symlink named `carriage.py`:

```bash
ln -s carriage_vY.XX.py carriage.py
```

The rest of the setup can use `carriage.py`, so these instructions do not need
to change for each point release.

Create a virtual environment:

```bash
python3 -m venv .venv
```

Activate it on Linux or macOS:

```bash
source .venv/bin/activate
```

Install the required Python dependency:

```bash
python -m pip install prompt_toolkit
```

Run Carriage:

```bash
python carriage.py
```

To open a Markdown file directly:

```bash
python carriage.py document.md
```

When returning to Carriage later, activate the virtual environment again before
running it:

```bash
source .venv/bin/activate
python carriage.py
```

### Fedora

Fedora users can install the required Python dependency from the system
repositories instead of creating a virtual environment:

```bash
sudo dnf install python3-prompt-toolkit
```

The optional spell-checking and export tools can also be installed through DNF:

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

For regular use, it is cleaner to create a stable `carriage.py` symlink that
points to the current versioned release file. Your shell alias can then remain
unchanged when you upgrade Carriage.

Replace `/path/to/carriage` below with the directory where you keep Carriage.

### If you installed Carriage in a virtual environment

For Zsh, add this line to `~/.zshrc`:

```bash
alias carriage='/path/to/carriage/.venv/bin/python /path/to/carriage/carriage.py'
```

For Bash, add the same line to `~/.bashrc`:

```bash
alias carriage='/path/to/carriage/.venv/bin/python /path/to/carriage/carriage.py'
```

This uses the Python interpreter inside Carriage's virtual environment, so you
do not need to activate the environment before launching the editor.

Reload your shell configuration after saving it:

```bash
source ~/.zshrc
```

or, for Bash:

```bash
source ~/.bashrc
```

You can then launch Carriage from anywhere:

```bash
carriage
```

Or open a Markdown file:

```bash
carriage document.md
```

### If `prompt_toolkit` is installed system-wide

If you installed `python3-prompt-toolkit` through your Linux distribution, the
alias can use the system Python instead:

```bash
alias carriage='python3 /path/to/carriage/carriage.py'
```

Add that line to `~/.zshrc` for Zsh or `~/.bashrc` for Bash, then reload the
appropriate configuration file.

### Updating Carriage

Release files use the `carriage_vY.XX.py` naming scheme. When installing a new
version, update the symlink instead of editing your shell configuration:

```bash
ln -sf carriage_vY.XX.py carriage.py
```

Replace `Y.XX` with the version you installed. The `carriage` command will then
launch that version automatically.

## Optional features

### Spell checking

Carriage uses the external `aspell` command for spell checking. An appropriate
Aspell dictionary must also be installed for the language you use.

Spell checking operates on a saved Markdown file. Carriage temporarily hands
the terminal to Aspell and reloads the document after Aspell exits.

### Document export

Carriage uses Pandoc for document export. Pandoc is not required for normal
editing.

Supported export targets include:

- PDF
- DOCX
- ODT
- HTML
- Plain text
- Custom Pandoc commands

PDF export also requires a PDF-generation engine available to Pandoc.

## Usage

Start with an empty document:

```bash
python3 carriage.py
```

Open an existing Markdown file:

```bash
python3 carriage.py path/to/document.md
```

Press `F10` or `Ctrl+Space` to activate the menu bar. Carriage also includes
built-in keybinding and Markdown reference screens under the Help menu.

## Design

Carriage takes a conservative approach to Markdown. Ordinary prose is formatted
for writing, while structural or ambiguous Markdown is preserved rather than
aggressively rewritten.

Supported pipe tables are shown as compact references in the prose view and can
be edited through Carriage's table editor. The saved file remains ordinary,
portable Markdown.

## License

Carriage is licensed under the MIT License. See `LICENSE` for details.

