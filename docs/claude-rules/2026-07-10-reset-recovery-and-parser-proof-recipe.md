# 2026-07-10 container resets: what landed, what was lost, the retained recipe

Two container resets hit the overnight session of 2026-07-09/10. This doc
preserves (a) the landed-work inventory with commits, (b) the full
solution recipe for the one piece of work that was lost before commit —
the SPARQL11.Parser admit-shrink — so any session can redo it without
the original agent's context, and (c) the environment-restore traps hit
on the way back up.

## a. Landed and pushed BEFORE the resets (safe; do not redo)

All on `claude/main`. Verify presence with `git log --oneline`.

| Work | Commits | Score after |
|---|---|---|
| Strict-runner integrity (RDFC canon + byte-compare graph equality) | (earlier, pre-`ccb603e`) | exposed 8 real SPARQL fails |
| SPARQL evaluator: 7 of 8 strict fails (BNODE/UUID per-binding freshness, NOW(), OWL-rewrite var scoping, rdf01 rdfD2) | `ccb603e`, `1ed5450` | SPARQL 630 pass, 1 fail |
| RIF import-profile materialisation (rif04, the 8th fail) | `4e57b9b`, `d5e08cd` | **SPARQL 631 pass, 0 fail (of 631)**; regimes 70/70 |
| JSON-LD toRdf + fromRdf closed out | `e7f28da`, `eda1427`, `9e4580d` | toRdf 461/0/6, fromRdf 53/0/1 |
| JSON-LD expand suite (never-run → measured + 5 spec-step clusters implemented) | `5790df6`, `d2af395` | expand 379 pass, 0 fail, 6 skip (of 385) |
| CSVW UAX-35 format engines (`CSVW.Formats.fst`) | `93eb649`, `48f8698` | csv2rdf 218 pass, 52 fail (of 270) |
| HDT js-bundle query perf (O(1) decoded-byte representation) | `71b5053` | 5,838 ms → 349 ms/call; hub 30/30, post 24 un-allowlisted |
| XML namespace-aware XPath name tests; GRDDL Stage 1; XSLT 69/88 | `e92ae0b`, `7784d9a`, `5ae76ce` | GRDDL 9/8/51 |
| Headless-Chromium hub harness (30 posts) | `2b8fff8` | 30 pass, 0 fail |
| QUDT + OpenPGP-subset scoping docs | `3b95106`, `ab78acc` | — |

## b. LOST work + retained recipe: SPARQL11.Parser admit-shrink

The agent had **finished the proof work** — both
`#push-options "--admit_smt_queries true"` regions deleted from
`formal/fstar/SPARQL11.Parser.fst` (119 admitted definitions → 0), full
file verified clean — but the container died between its final relink
and its commit. The worktree did not survive. Re-dispatched 2026-07-10
with this recipe (task #88); if that run is also lost, redo from here.

**The 20 obligations that appear when the pragmas are removed, and the
fixes that are KNOWN TO WORK (verified clean in the lost run):**

1. **14 termination obligations.** The offending definitions use inner
   (nested `let rec`) recursive helpers whose decreases metric F\*
   cannot infer at the nesting site. Fix: hoist each inner recursive
   helper to a top-level private function with an explicit
   `(decreases ...)` clause on the tokens/remaining-input list. Pure
   relocation plus explicit metric; no logic change.
2. **6 subtyping obligations.** Three patterns:
   - Strengthen the prefix-map entry type to carry the `wf_iri`
     (well-formed IRI) refinement — prefix-map values flow into
     wf_iri positions and the unrefined type was the mismatch.
   - `assert_norm` for the constant vocabulary IRIs the parser embeds
     (well-formedness is decidable by computation).
   - Ascribe LIMIT/OFFSET numeric parse results to `nat` explicitly
     (parser produced `int` where the algebra type wants `nat`).

**Verification cost:** full-file batch verify of the final text runs
~62–78 s under z3 4.13.3, "All verification conditions discharged".

**Extraction expectations:** the diff vs the committed
`ocaml-output/SPARQL11_Parser.ml` is semantically inert — function
relocations (from the hoists), a type alias, and two dead guard
branches. Anything beyond that class means a mistake; stop and
re-examine.

**Gates measured in the lost run (must reproduce):** SPARQL 631 pass,
0 fail; RDF 1031 pass, 0 fail; post16 hub tests 5 pass, 0 fail. Run the
w3c_runner from the repo root (its RIF fixture resolver is
cwd-relative).

**Disclosure sites to update on landing:** grep `admit_smt_queries`
across `README*`, `docs/claude-rules/current-state.md`, the SPARQL row
of `docs/claude-rules/w3c-completeness-ledger.md` (mentions "#91"),
and `skills/*/SKILL.md`.

## c. Environment-restore traps (2026-07-10 edition)

1. **The restored container may be a STALE SNAPSHOT.** Check
   `git log origin/claude/main` freshness FIRST; a fetch that times
   out once is not "offline forever" — the network came back within
   the hour. Everything pushed survives; only uncommitted worktrees
   die. Push after every landing.
2. **z3 version drift:** the fresh container had z3 4.16.0 first on
   PATH (both `/usr/local/bin/z3` and the opam switch's `z3`), while
   4.13.3 lives at `/usr/local/bin/z3-4.13.3`. Fix:
   `ln -sf /usr/local/bin/z3-4.13.3 /root/.opam/fstar/bin/z3` and the
   same for `/usr/local/bin/z3`. Always `z3 --version` before proof
   work — wrong z3 is a top-three time sink.
3. **The task list / harness state also reverts** with the snapshot —
   re-sync it from this doc and the ledger, not from memory.
4. `tools/install-toolchain-cache.sh` + `tools/ensure-test-env.sh`
   restore F\* and all suite submodules in ~2 min total.

## d. Queue at time of writing (2026-07-10, after re-dispatch)

- In flight: admit-shrink re-run (task #88, recipe above); test-page
  tree rework + ShEx dashboard row (task #90; page generator is the
  heredoc in `formal/fstar/generate-report.sh`, ShEx submodule is
  present, suite was green at last full run but has no public row).
- Next: reconciliation rebuild on quiet main (task #89) to unify
  mixed-epoch binaries and all three bundle copies (rdfDirection,
  CSVW.Formats, HDT byte-array fix, JSONLD.Expand, strict runner in
  every artifact simultaneously), then full battery + dashboard regen.
- Burndown after that (per the ledger): OWL 2 catalogs, JSON-LD
  compact/flatten/frame/html suites, CSVW's enumerated 52, RIF 4
  fails + 12 skips, SHACL denominator audit.
