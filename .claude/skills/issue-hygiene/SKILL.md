---
name: issue-hygiene
description: Sweep open GitHub issues against recent merged PRs + active design docs; close-with-link, update, or leave alone. Use on Fridays, after a merge cluster, when an issue is referenced in a PR body, or whenever the user types /issue-hygiene. Tracker is danbri/factoidal#198. Pairs with the github-and-prs skill for the gh CLI mechanics.
---

# Issue tracker hygiene

The repo's issue tracker drifts: PRs merge that resolve open issues but
forget to link back; assumptions in older issues become invalid silently;
codename-violator items continue to track work that's now blocked-on-or-
covered-by the recovery plan. This skill keeps the tracker honest.

The standing home for findings + tech-debt items is **#198 (Issue
tracker hygiene)**. The migration tracker is **#200**.

## When to invoke

- **Friday** afternoon — full-sweep hygiene pass.
- **After a merge cluster** (≥3 PRs merged in <1 hour) — quick pass to
  link any newly-resolved issues.
- **When opening a PR** that references an issue — cross-link in both
  directions; don't auto-close.
- **When merging a PR** that closes an issue via "Closes #X" — verify
  the linkage rendered correctly + the auto-closure happened.
- **User invokes** `/issue-hygiene` or asks to "review issues".

## Auth + repo

- `gh` is authenticated as the user; ensure with `gh auth status`.
- Always pass `--repo danbri/factoidal` (local-proxy git remote).

## Sweep flow

### 1. Pull the inputs

```bash
gh issue list --repo danbri/factoidal --state open --limit 200 \
  --json number,title,body,labels,createdAt,updatedAt \
  > /tmp/issues-open.json

gh pr list --repo danbri/factoidal --state merged --limit 100 \
  --json number,title,body,mergedAt,headRefName \
  > /tmp/prs-merged-recent.json
```

### 2. For each open issue, decide

| Outcome | Action |
|---|---|
| **Close + link** | A merged PR / current `claude/main` state resolves the issue. Post one-sentence comment naming the PR; `gh issue close <n>`. |
| **Comment + leave open** | Partial progress; or the issue's broader framing isn't fully resolved. Post a status comment cross-linking the relevant PRs / design docs. |
| **Leave alone** | Issue is current and accurate. Move on. |
| **Mark duplicate** | Another open issue covers the same ground. Comment, close as duplicate, link to the survivor. |
| **Mark stale** (rare) | Pure exploration that's been answered elsewhere or is no longer relevant. Comment + close with `not-planned` or `wontfix`. |

### 3. Cross-reference for the codename-violator cluster

Issues #106 + #107–#116 (and any with `Yod6` / `Tet3` / `Lamed3` / `Mem5`
/ `Pe5` / `Bet7` / `Tav5` / `Heth3` in title or body) are part of the
recovery plan. **Don't close them based on PRs alone** — they close when
the relevant codename is retired in `claude/main` AND the boundary audit
shows the corresponding `VIOLATION-SEM` row gone.

The migration epic (#200) has a checkbox per codename. Tick the
checkbox first; close the issue only when the box is ticked AND the
PR that retired the violator is merged.

### 4. Standing tech-debt sweeps

The hygiene tracker (#198) carries a checklist of small tech-debt items
that don't warrant their own issue. Run through them on each Friday
sweep:

- `failwith "Not yet implemented"` straggler scan in extracted `.ml`.
- Orphan `experimental_ocaml_glue/*.sh` patches with no matching
  `assume val`.
- Stale `docs/designissues/` plan docs (>90 days, status pending).
- Retired-codename entries in `docs/code-name-glossary.md` that should
  be marked historical.
- `bin/<platform>/` binary staleness vs `ocaml-output/*.ml` mtimes.

If any sweep produces a real chunk of work, file a dedicated issue and
link from #198.

## Reporting template

End every sweep with a comment on #198 in this shape:

```markdown
## Hygiene sweep <YYYY-MM-DD HH:MM UTC>

- Open at start: N
- Closed: K — list of #N → resolving PR
- Updated: M — short description of each
- Left alone: P
- New issues filed from sweep: Q (link each)
- Tech-debt checklist progress: ticked X of Y
```

Use the `markdown-style` skill for the comment body — no `**` adjacent
to issue link `]` chars.

## Cautions

- **Never bulk-close based on age**. Old isn't dead.
- **Never close codename-violator issues** without the migration-epic
  box ticked AND a PR link AND the audit confirming retirement.
- **Never reorder priority labels** — that's the user's call.
- **Don't post wall-of-text comments**. One sentence + the resolving PR
  is enough. Multi-paragraph belongs in a design doc, not an issue.
- **Don't open new issues during a sweep** unless the finding is real
  and stand-alone work; otherwise note it on #198.

## What this skill does NOT do

- Doesn't decide priority; doesn't reorder a backlog.
- Doesn't merge PRs.
- Doesn't close issues marked with the user's hold labels (e.g.
  `discussion`, `decision-pending`).
- Doesn't create labels — those are the user's curation.

## Cross-references

- `github-and-prs` skill — gh CLI mechanics, branch/PR conventions.
- `markdown-style` skill — for hygiene-comment formatting.
- Issue **#198** — the hygiene tracker (this skill's home).
- Issue **#200** — F\* migration epic; cross-tick from here.
- `docs/designissues/2026-05-07-query-planning-fstar-recovery.md` —
  recovery plan; inputs to violator-issue decisions.
- `docs/designissues/fstar-ocaml-boundary-audit.md` — current
  classification; the source of truth for "is the violator retired".
