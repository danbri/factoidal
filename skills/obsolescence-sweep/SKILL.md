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

Every one was corrected only after an external reader challenged it.
This skill exists so the correction happens at landing time instead.

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
