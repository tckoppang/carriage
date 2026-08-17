# Carriage Configuration

Carriage reads persistent settings at startup from:

```text
$XDG_CONFIG_HOME/carriage/config.toml
```

When `XDG_CONFIG_HOME` is unset, it uses:

```text
~/.config/carriage/config.toml
```

Carriage creates the file on first launch. There is no Preferences dialog; edit `config.toml` manually and restart Carriage to apply changes.

## Complete generated configuration

```toml
# Carriage configuration
# Persistent settings are read at startup.
# Edit this file manually; Carriage has no Preferences dialog.
# Unsaved working state is protected automatically and is not configurable.

[editor]
prose_width = 80

[interface]
scrollbar = true

# Advanced: startup/default interface behavior. The status bar can be
# toggled for the current session from the Edit menu.
statusbar = true
mouse = true
hard_break_marker = true

[tools]
# Advanced: executable used for all Pandoc exports.
pandoc = "pandoc"

# Advanced: interactive terminal spell checker. The command must edit the
# open file in place and exit when finished. {file} is replaced by the path.
spellcheck_command = ["aspell", "--mode=markdown", "check", "{file}"]
```

## Settings

### `editor.prose_width`

Integer from 40 through 160. Default: `80`.

This controls the visual prose width and the width used by **Export > Hard-Wrapped Markdown**. It does not insert source line breaks while editing. This setting is not a terminal-size limit: supported modal dialogs require an 80×24 or larger terminal, while terminal width and height otherwise have no configured maximum.

### `interface.scrollbar`

Boolean. Default: `true`.

Shows or hides the document scrollbar. When hidden, Carriage reclaims the scrollbar column for layout.

### `interface.statusbar`

Boolean. Default: `true`.

Sets status-bar visibility at startup. The status bar can be toggled for the current session through **Edit > Toggle Status Bar**.

Temporary messages still occupy the status-bar line when the normal status bar is hidden.

### `interface.mouse`

Boolean. Default: `true`.

Enables prompt_toolkit mouse handling, including clicking, scrolling, double-click word selection, and triple-click paragraph or list-item selection.

### `interface.hard_break_marker`

Boolean. Default: `true`.

Displays `↵` at Markdown hard line breaks made with two trailing spaces. The marker is visual only and is never saved.

### `tools.pandoc`

Nonempty string. Default: `"pandoc"`.

Specifies the executable used for PDF, DOCX, ODT, HTML, and custom Pandoc exports. It can be an executable name found on `PATH` or a path to an executable.

### `tools.spellcheck_command`

Nonempty array of nonempty strings. Default:

```toml
spellcheck_command = ["aspell", "--mode=markdown", "check", "{file}"]
```

The first item is the executable. At least one later argument must contain `{file}`, which Carriage replaces with the current document path.

The command must edit the file in place, retain control of the terminal until complete, and return exit status zero on success. Carriage reloads the file only after successful completion.

## Validation and warnings

Missing settings use their defaults without a warning.

A syntactically valid file can contain one invalid value without losing valid neighboring values. Carriage reports the ignored setting and uses the default for that setting.

Malformed TOML, unreadable files, and non-UTF-8 configuration files produce a startup warning and cause all settings to use defaults for that launch.

Unrecognized tables and setting names are reported and ignored.

## Python 3.10

Python 3.11 and newer include `tomllib` in the standard library. On Python 3.10, Carriage first looks for the optional `tomli` package. Without `tomli`, Carriage can still read the limited TOML subset used by its own generated configuration.

Install full TOML support on Python 3.10 with:

```bash
python -m pip install tomli
```

## Recovery is not configurable

Carriage's private recovery journal is independent of `config.toml`. Unsaved working state is protected automatically; the Markdown file itself changes only through explicit Save or Save As.
