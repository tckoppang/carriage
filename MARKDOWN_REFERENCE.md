# Markdown Syntax Reference

This is a Markdown syntax reference, not a list of everything Carriage actively reformats. Carriage may normalize ordinary prose, simple flat lists, and simple single-level blockquotes. Code, YAML front matter, raw HTML, reference definitions, complex containers, and ambiguous structures are preserved rather than repaired.

Highlighting, hanging structural markers, hard-break markers, and folded-object labels are visual only.

## Headings

```markdown
# H1
## H2
### H3
#### H4
##### H5
###### H6
```

ATX headings are Carriage's preferred form. Convert for Carriage can normalize supported Setext headings to ATX.

## Emphasis

```markdown
*italic*
**bold**
***bold italic***
```

`F2` toggles italic and `F3` toggles bold on selected text. Carriage writes asterisks; Convert for Carriage can normalize straightforward underscore emphasis.

## Lists

```markdown
- unordered item
1. ordered item
```

Carriage actively reformats only straightforward flat prose lists. Nested, malformed, or ambiguous list structures are preserved.

## Blockquotes

```markdown
> quoted text
```

Carriage actively reformats only simple single-level prose blockquotes.

## Horizontal rules

```markdown
---
***
___
```

Use three or more matching hyphens, asterisks, or underscores.

## Links and images

```markdown
[link text](https://example.com)
![alt text](image.png)
```

## Code

Inline code:

```markdown
`inline code`
```

Use matching triple backticks or tildes for a fenced code block. Carriage preserves code rather than reflowing it.

## Hard line breaks

End a line with two spaces to force a Markdown line break. Carriage can display that break as `↵`; the marker is visual only.

## Footnotes

```markdown
Text with a note.[^id]

[^id]: Footnote text
```

`F5` or **Tools > Insert Footnote** creates a simple standard footnote. Supported single-paragraph definitions fold out of the prose view, and references display sequentially as `[1]`, `[2]`, and so on. Complex definitions remain ordinary source.

## Tables

Use `F4` or **Tools > Insert Table** to create a basic pipe table. Press `Tab` on a folded table reference to edit it.

Optional titles use Pandoc table captions and appear in the prose view as:

```text
[[Table N: Title]]
```

The basic editor supports 2 to 6 columns. Wider imported tables are preserved as Markdown but cannot be opened in that dialog.
