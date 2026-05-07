---
name: markdown-style
description: Markdown formatting + prose register for Claude-generated text in this repository — chat replies, design docs, READMEs, PR bodies, commit messages. Two load-bearing rules. (1) Links must be unambiguously clickable — bold/italic emphasis around URLs and link syntax frequently breaks the click target. (2) No sycophantic adjectives — drop "honest", "genuine", "important", "critical", "big picture", "key insight", "headline", and similar candor-performance words. Use whenever generating user-facing markdown that may be rendered in different clients (CLI, web, mobile chat, GitHub).
---

# Markdown style for Factoidal

Different markdown renderers handle edge cases differently. Some
interpret `**[link](url)**` cleanly; others fold the trailing `**`
into the link text or URL and break the click target. This skill
documents the patterns that work everywhere and the patterns that
silently break in at least one renderer in regular use.

The single load-bearing rule:

> **Links must be unambiguously clickable. Never put emphasis
> markers (`**`, `*`, `_`, `__`) immediately adjacent to the
> closing `)` of a markdown link, or at the end of a bare URL.**

If a link target needs visual emphasis, put the emphasis **inside**
the link text, not around the link.

## The bad patterns

### Wrapping a link in bold

❌ Bad:
```
**[Authorize here](https://github.com/login/device)**
```
**Why it breaks**: in some renderers (mobile chat, minimal CLI
renderers, plain-text fall-throughs) the trailing `**` is
ambiguous — is it bold-close, or part of the URL, or part of the
link text? Click target may include or exclude the `**`, and the
URL itself may show `https://...device**` to the user.

✅ Good — put the bold inside the link text:
```
[**Authorize here**](https://github.com/login/device)
```

✅ Also good — drop the bold entirely, since a link is already
visually distinguished:
```
[Authorize here](https://github.com/login/device)
```

### Bare URL followed by a bold close

❌ Bad:
```
Open **https://github.com/login/device**
```
**Why it breaks**: most renderers treat bare URLs as autolinks,
so they detect the URL and stop at the first character that
can't be in a URL. Whether `*` counts varies by renderer. Some
include `https://...device**` in the link target; the link
404s.

✅ Good — wrap in markdown link syntax + put any bold inside
the text:
```
Open [**https://github.com/login/device**](https://github.com/login/device)
```

✅ Better — drop the bold; the URL is already visually distinct:
```
Open https://github.com/login/device
```

### Any emphasis adjacent to URL boundary characters

❌ Bad:
```
Visit **https://example.com**.
Visit *https://example.com*, then click.
URL: __https://example.com__
```

The autolinker in most renderers treats `*` and `_` as continuation
characters in some positions. You get either a broken link or the
wrong characters in the link text.

✅ Good — separate emphasis from URL:
```
Visit https://example.com.
Visit https://example.com, then click.
URL: https://example.com
```

### Heading-like bold lines that contain URLs

❌ Bad — using `**Label: url**` as a pseudo-heading:
```
**URL: https://github.com/login/device**
**Code: `AFCF-7227`**
```
The first line breaks the URL link; the second is fine but
inconsistent with the first.

✅ Good — promote to a real heading or use a label without bold:
```
URL: https://github.com/login/device
Code: `AFCF-7227`
```

Or:
```
### Authorize

URL: https://github.com/login/device
Code: `AFCF-7227`
```

## Other patterns worth caring about

### Code spans that contain backticks

For inline code containing a literal backtick, use a longer fence
on the outside:

✅ ``Use `` `--z3version 4.13.3` `` to override the default.``

### Tables

Plain GFM tables only. No HTML inside cells. Right-align
numeric columns. Each cell on one line; for multi-line content
use a list outside the table.

### Lists

- `-` for unordered (consistency).
- Numbered lists start at `1.`; let the renderer renumber.
- One blank line between adjacent lists of different types,
  otherwise some renderers merge them.

### Links to local files

Always relative paths from the repo root, in markdown link
syntax:

```
See [recovery plan](docs/designissues/2026-05-07-query-planning-fstar-recovery.md).
```

Don't use `file://` URLs — they're machine-specific.

### Line wrapping

Wrap prose at 80 columns where practical. Don't wrap inside link
syntax — keep `[text](url)` on one line so the link doesn't
visibly split when soft-wrapping is off.

## Prose register — no sycophantic adjectives

User-facing prose (chat replies, PR bodies, commit messages, design
docs) must not perform candor through word choice. Drop the following
filler:

- `honest update`, `honest assessment`, `honestly`, `to be candid`
- `genuine`, `genuinely`
- `important`, `critical`, `big-picture`, `headline`, `key insight`,
  `key finding`, `key headline`, `headline finding`
- `notable`, `notably`
- `surprising-but-good`, `striking`, `sharp finding`
- Setup phrases like "Two headlines:", "Three things landed:",
  "**Critical headline:**" — when the next sentence already
  contains the substance, the setup is filler.

Why these are bad: they signal "trust me this is real" instead of
just being real. The sentence either carries weight or it doesn't.
A genuine update is genuine in the absence of the word "genuine";
adding the word performs the property rather than displays it.

### Bad → Good rewrites

❌ "Honest update on the migration: we retired Tav5 and Heth3."
✅ "We retired Tav5 and Heth3."

❌ "Important finding: the agent picked RL not DL."
✅ "The agent picked RL not DL."

❌ "**Big-picture honest update on the migration epic #200:**"
✅ "Migration epic #200 status:"

❌ "**Critical headline: the 1 non-RIF SPARQL fail is reachable
   inside OWL 2 RL.**"
✅ "The 1 non-RIF SPARQL fail is reachable inside OWL 2 RL."

❌ "Genuinely good finding: the patches were already retired earlier."
✅ "The patches were already retired earlier."

### Heading rule

When section content is already substantive, don't add a header
that performs significance. `## Status` beats `## The current
honest state`. `## Why this matters` is sometimes load-bearing;
`## Key why-this-matters` is not.

### One-word adjectives are fine when load-bearing

`fast`, `slow`, `correct`, `verified`, `failing`, `merged`,
`pending`, `blocked`, `pre-existing`, `out of scope`, `deferred`
all carry information. Drop only the words that perform candor or
significance without carrying it.

### Why this rule exists

User feedback (2026-05-07): "Spraying those adjectives around like
cheap deodorant is a miserable, distracting and depressing pattern
you are falling in to in your current Opus 4.x incarnation. Stop
doing it." This skill is the durable form of that feedback so the
correction survives session boundaries.

## Quick checklist before sending a reply or committing a doc

1. Every URL is either bare on its own (no surrounding emphasis)
   or wrapped as `[text](url)` with any emphasis **inside** the
   link text.
2. No `**` or `*` directly before `[` or after `)`.
3. No `**` immediately after a bare URL's final character.
4. Code spans use the right number of backticks for their content.
5. Tables are valid GFM; cells are single-line.
6. No sycophantic adjectives (`honest`, `genuine`, `important`,
   `critical`, `big-picture`, `headline`, `key insight`, …). When
   you catch yourself typing one, delete it and re-read — the
   sentence is almost always better without.

## Why this matters in this project

Factoidal docs render in many places: GitHub web UI, GitHub
mobile, terminal `gh pr view`, the `claude.ai` chat surface, the
Claude Code TUI, README mirrors on `npm`, and the deployed
gh-pages dashboard. The intersection of "patterns that render
cleanly everywhere" is smaller than the intersection of "patterns
GitHub web accepts". Stick to the unambiguous patterns and the
docs work everywhere.

## What this skill does NOT cover

- Code formatting style (covered by language-specific tooling).
- Headings hierarchy (use what fits the doc).
- Doc-of-truth selection (CLAUDE.md vs design docs vs skills) —
  see CLAUDE.md.
