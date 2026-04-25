# P4 Sentinel — Tail-Recursion Audit Verification

**Agent:** Ayin (P4 background sentinel)
**Started:** 2026-04-25 09:38 UTC
**HEAD:** db3bfd0 (rdfc10: HNDQ Phase 3 — 3-level neighbour hash + RDF set-semantics dedup)
**Target:** [`docs/designissues/2026-04-23-tail-recursion-audit.md`](2026-04-23-tail-recursion-audit.md)

## Why this target

Random selection (50/50 docs vs issue → docs; uniform among
3 fixed pages + 5 random designissues) drew this 2-day-old audit doc.
Two days is just long enough that some of the listed line numbers
or function bodies could have drifted — for instance, commit `8a3155e`
("stack-safe GROUP BY / DISTINCT / op_At — fixes browser demo")
in the recent history may have already addressed some hazards.

## Verification plan

1. For each entry in the Hazard Table (rows ~16–30), confirm:
   - The cited file + line range still contains that function.
   - The cited pattern (`x :: f xs`, `@ f xs`, `fold_left + rev`) is still the
     pattern in HEAD.
   - For any line that has shifted, note current line range.
2. Pay extra attention to the "Top 5 Fix-This-First" entries.
3. Check `8a3155e` (stack-safe GROUP BY / DISTINCT / op_At) — likely already
   touches some of these; if so, note in audit doc as "addressed in 8a3155e".

Read-only on `.fst`. Will commit doc-only fixes.

## First findings

(See report.)
