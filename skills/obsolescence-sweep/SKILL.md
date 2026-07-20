---
name: obsolescence-sweep
description: Post-feature-landing sweep for statements the landing just made false — stale "not yet / out of scope / parked / later stage" claims in docs, hub notebooks, skills, .fst header comments, test-suite yamls, the ledger, and dashboard prose. Use IMMEDIATELY AFTER landing any feature, capability, or score change; when writing any "we don't have X / can't do X" sentence (verify against the tree first — negative claims rot fastest); or when a reader reports prose contradicting behavior. Ships tools/obsolescence-sweep.sh, the stale-claim lexicon, the target-surface list, and the 2026-07-10 war stories (VC "crypto is a later stage", "Protocol/GSP parked", ShExC "out of scope indefinitely" — all asserted from stale text while the features sat in the tree).
---

# Obsolescence sweep: landing a feature obsoletes sentences, not just code

Every feature landing silently falsifies prose somewhere else in the
repo. Code gets rebuilt; sentences do not. In a repo that moves this
fast, stale documentation skews **pessimistic** — it undershoots
reality — and the failure mode is always the same: someone (human,
agent, or the public dashboard) answers a question from a stale claim
instead of from the tree.

**The rule (owner directive 2026-07-10): a feature landing is not
complete until the statements it obsoletes are corrected — in the same
commit or an immediate follow-up. And any NEGATIVE capability claim
("we don't have X", "X is not implemented", "X is a later stage")
must be verified against code or a measurement before it is written
or repeated.**

## War stories (all from one day, 2026-07-10)

1. **"Verifying holder binding requires crypto — a later stage of this
   work."** Public dashboard prose. The eddsa-rdfc-2022 stack (HACL\*,
   native + Node + browser) had landed days earlier and was linked
   into the very binary printing that sentence.
2. **"SPARQL Protocol / Graph Store parked — not implemented against
   the W3C test suite yet."** Gap list on the public page. Protocol
   34/0 and GSP 19/0 had been passing for weeks; a live server binary
   shipped in `bin/`.
3. **"ShExC is out of scope indefinitely (Stage 9)."**
   `ShEx.Schema.fst` header. `Parser.ShExC.fst` sat in the same
   directory, with a 433/433 differential against the ShExJ twins.
   The stale header was quoted to the owner as fact.
4. **Lenient-comparison caveats** ("ASK never compared, any bnode
   matches any") still disclosed in `skills/test-suites` months…
   days after the strict runner retired them.

5. **"RDFC-1.0 … all remaining out of scope; within scope DONE."**
   `current-state.md`, dated 2026-07-04. The 3 poison "evil" fails + 1
   poison-clique NegEval stub it wrote off were SOLVED the very next day
   (2026-07-05 HNDQ work-budget). The "out of scope" line was never
   retracted, so a 2026-07-19 audit — and the owner — read a **86/86
   complete** capability as partial-and-excluded. "Out of scope" written
   as a *disposition of hard residual work* is the most dangerous label
   in the repo: it looks like a decision, but it is often just "we
   haven't done this yet" — and when the work then lands, nobody unlabels
   it. Never write "out of scope" for something merely hard; write
   "not done yet (hard because …)" so the next landing knows to retract
   it.

Every one was corrected only after an external reader challenged it.
This skill exists so the correction happens at landing time instead.

## Rot cuts BOTH ways — and scores rot silently

Two failure modes, one root cause (docs don't auto-refresh from code):

- **Optimistic overclaim** — "X is done / works" when it isn't (war
  stories 1-3, 5). Erodes trust when caught.
- **Pessimistic undersell** — "X is a gap / lenient / out of scope" when
  it's actually FIXED and stricter than claimed (war story 4; and the
  2026-07-19 ASK-boolean + bnode-isomorphism caveats that described
  already-retired runner leniency). Hides real strength; makes you
  distrust *correct* numbers. **When writing ANY negative claim ("we
  don't / can't / lenient / out of scope"), grep the code FIRST — negative
  claims rot fastest.**

**The score-staleness trap (the structural one).** A committed
`*_results.log` or dashboard number is only as fresh as the last time a
human re-ran the suite. If no workflow re-runs a suite, its number can
drift for days with zero signal — proven 2026-07-19: committed
`owl_type_inconsistency` + `csvw` logs predated their own source files by
a day. Consequences for this skill's discipline:

- A score you are about to quote as current is NOT trustworthy because it
  is committed — it is trustworthy only if a run produced it recently.
  When it matters, **re-run the suite (committed binaries, no toolchain
  needed) and read the LIVE number**, don't trust the committed log.
- The durable fix is a scheduled re-run that commits refreshed logs, so
  drift becomes a visible diff (`.github/workflows/conformance-rerun.yml`,
  epic #235). A suite with no scheduled/triggered re-run path is a silent
  gap regardless of how green its committed number looks.
- Cross-ref `test-suites` (§ Drift signal) and the boundary-audit method:
  when auditing "what's silently missing," the dangerous pattern is NOT
  big labeled skip pools (those are honest) — it's clean-looking fully-
  dispositioned scores that nobody re-verifies.

## The sweep

After landing feature X, run the advisory scanner with 2-4 keywords
that name the capability:

```bash
tools/obsolescence-sweep.sh shexc "compact syntax"
tools/obsolescence-sweep.sh crypto sign verify ed25519
```

It greps the **stale-claim lexicon** near your keywords across the
**target surfaces** and prints `file:line` hits for human judgement.
It is advisory (exit 0 unless `--ci`); most hits need a brain — some
"not yet" sentences are still true.

### Stale-claim lexicon (grep patterns the script uses)

`not yet`, `not implemented`, `no runner`, `unscored`, `out of
scope`, `parked`, `deferred`, `later stage`, `future work`, `in
flight`, `planned`, `TODO`, `does not (yet )?(run|support|exist)`,
`cannot`, `stage [0-9]`, `pending`, `unsupported`, `stub`,
`placeholder`, `known gap`, `we don't`, `no .* exists`.

### Target surfaces (in priority order — public first)

1. `formal/fstar/generate-report.sh` — dashboard prose/heredoc (PUBLIC).
2. `.github/test-suites/*.yaml` — `remaining:` gap lists + comments (PUBLIC via dashboard).
3. `docs/web/hub/*.md` — hub notebook prose + live-cell captions (PUBLIC).
4. `README*`, `docs/index.md`, `npm/factoidal/README.md` (PUBLIC).
5. `docs/claude-rules/w3c-completeness-ledger.md`, `current-state.md` — drive future work selection.
6. `skills/*/SKILL.md` — drive future agent behavior.
7. `formal/fstar/*.fst` header comments — quoted as architecture fact (war story 3). Comment-only .fst edits are extraction-inert but still note them in the commit message.
8. `CLAUDE.md`, `docs/designissues/*.md` status lines, `bin/*/`
   runner comments, `tests/` fixture READMEs.

### Fix discipline

- Correct at the SOURCE, in the same commit as the landing (or the
  cherry-picked landing commit on main). Never only in chat.
- When a claim is half-stale, rewrite it to the measured truth with a
  date, not to a new prediction.
- Score lines follow anti-pattern #25 (labelled, with denominators).
- If the sweep finds a stale claim about someone ELSE's feature,
  fix it anyway or file it — do not re-bury it.

## Wiring

- **Subagent briefs**: `skills/subagent-prompting` requires
  feature-landing briefs to include the sweep before the single
  commit (see its MANDATORY sections).
- **Coordinator landings**: run the script after each cherry-pick
  lands on main, before the dashboard regeneration — the regen
  publishes whatever prose is in the tree.
- **CI (advisory)**: `tools/obsolescence-sweep.sh --ci <keywords>` exits
  non-zero on hits, for use in PR checks when a workflow wants to
  force the author to look. Not wired as a blocking hook by default:
  the lexicon has false positives by design.
