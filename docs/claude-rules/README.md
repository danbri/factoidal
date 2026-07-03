# Claude Rules — Expanded Reference

`CLAUDE.md` at the repo root is the **short-form** file loaded into every
Claude session's context. It's kept trim so the file fits in context.
The full rationale, war-stories, and living-snapshot material lives here
and is read on demand. Operational how-to lives one level up in
`skills/<name>/SKILL.md` (agentskills.io format, indexed from
`CLAUDE.md` § Skills); these files are the rationale and the record.

## Index

- [`anti-patterns.md`](./anti-patterns.md) — the 25 numbered
  "Do NOT Repeat These Mistakes" rules, with full context + war-story
  justifications. Read when writing subagent prompts or diagnosing a
  new failure mode. Cross-references like "rule #17" in commit messages
  point here.
- [`performance.md`](./performance.md) — performance status +
  history: current measured Turtle throughput, the 2026-04 slow-era
  root causes, and the standing measurement rules.
- [`scope.md`](./scope.md) — what is permanently in/out of scope
  (RIF Core skips, tableau limits). Update **in the same commit** as
  any scope-changing code.
- [`current-state.md`](./current-state.md) — Current State (Honest
  Assessment): F\* module inventory, `assume val` table, verification
  gaps, W3C suite scores. Goes stale within a week — refresh after
  material progress.

## Relationship to `CLAUDE.md`

`CLAUDE.md` contains the 10 **Iron Rules** in full (they're short and
load-bearing every session). The 25 numbered **anti-pattern** rules
are summarised in `CLAUDE.md` by number with a one-line title and a
pointer back to `anti-patterns.md` for the full text.

Numbering is stable. Never renumber. Commit messages and internal
cross-references ("per rule #17", "anti-pattern #15") are expected to
resolve forever.
