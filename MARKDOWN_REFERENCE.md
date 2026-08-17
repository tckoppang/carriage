# Markdown Syntax Reference

This is a Markdown syntax reference, not a list of everything Carriage actively reformats. Carriage may normalize ordinary prose, simple flat lists, and simple single-level blockquotes. Reflow is opt-in by recognition: if Carriage cannot positively identify a block as supported structure or safe plain prose, it preserves that block as opaque source rather than guessing. Code, YAML front matter, raw HTML, reference definitions, display math, line blocks, directive or container syntax, alerts, task lists, unsupported table forms, and other unfamiliar or ambiguous structures are therefore preserved rather than repaired.

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

`F5` or **Tools > Insert Footnote** creates a standard prose footnote. Supported single- and multi-paragraph prose definitions fold out of the prose view, and references display sequentially as `[1]`, `[2]`, and so on. Blank lines in the footnote editor separate paragraphs. Definitions containing structural blocks such as lists, blockquotes, code, raw HTML, reference definitions, thematic breaks, or tables remain ordinary source.

## Tables

Use `F4` or **Tools > Insert Table** to create a basic pipe table. Press `Tab` on a folded table reference to edit it.

Optional titles use Pandoc table captions and appear in the prose view as:

```text
[[Table N: Title]]
```

The basic editor creates tables with 2 to 6 columns and 1 to 60 data rows. Existing and imported tables with up to six columns can be edited regardless of row count. Wider imported tables are preserved as Markdown but cannot be opened in that dialog. A table that conceptually has no header can use a blank header row.
