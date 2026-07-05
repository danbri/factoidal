---
name: session-cost-accounting
description: Calculate the token cost of an agent session INCLUDING all its subagent children, using agentsview (uvx agentsview). Use when the owner asks "what has this session cost", "how much did last night cost", when planning subagent fan-outs against a budget, or when writing a retrospective that should carry real spend numbers. The one-liner is tools/session-cost.sh; this doc records the working recipe and the traps (main-only usage under-counts by ~40%, sync first, JSON key names).
---

# Session cost accounting with agentsview

`agentsview` (PyPI, run via `uvx agentsview`) parses the local
`~/.claude/projects/*/**.jsonl` transcripts into SQLite and estimates
per-session cost from token usage and model pricing.

## The one-liner

```bash
tools/session-cost.sh            # this project (factoidal)
tools/session-cost.sh myproject  # any agentsview project name
```

Prints total estimated cost split main-vs-subagents, total output
tokens, and the top-10 sessions by cost.

## The recipe it wraps (verified 2026-07-05, agentsview v0.36.1)

1. **Sync first** — the DB lags the live transcripts:
   `uvx agentsview sync`
2. **List with children** — subagent transcripts are separate
   sessions with `agent-<id>` ids, EXCLUDED by default:
   `uvx agentsview session list --project factoidal --include-children --json`
3. **Per-session cost** — for each id from step 2:
   `uvx agentsview session usage <id> --json`
   JSON keys: `cost_usd` (float), `total_output_tokens`,
   `peak_context_tokens`, `models` (list).
4. Sum `cost_usd` across all ids.

## Traps

- **Main-session usage alone under-counts badly.** On 2026-07-05 the
  main session read ~$1,044 while the 103 subagent children carried
  another ~$617 — 37% of real spend invisible without
  `--include-children`.
- `session list` without `--project` returns every project on the
  machine; filter or you will sum unrelated work.
- `session usage` takes ONE id; there is no bulk usage endpoint as of
  v0.36.1, hence the per-id loop (104 ids ≈ a minute; fine).
- The cost is an ESTIMATE from public pricing for the models seen in
  the transcript (`models` field) — treat as directional, label it
  "estimated" when reporting to the owner (rule #25 discipline:
  labelled numbers).
- First `uvx agentsview` call downloads ~32 MB; needs the proxy to
  allow PyPI. Cache-friendly afterwards.

## Reporting form

Per the score-reporting discipline: report as
"estimated $X total ($Y main + $Z across N subagents), M output
tokens" — never a bare number without the split, since the split is
what informs subagent-economy decisions (see `choosing-models` +
`session-economy`).
