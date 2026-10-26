# Lean standards status and Codex skill discovery

Date: 2026-09-08. Reviewed checkout:
`0c331255b3a0fec0306b5459a944749364db891f`.
Toolchain: `leanprover/lean4:v4.33.1`.

The owner requested a review of Lean RDF 1.1/1.2, SPARQL 1.x, and OWL
RL/QL/DL/tableau, a summary of CLAUDE.md in AGENTS.md, and skill symlinks
for Codex. The result is in [AGENTS.md](../AGENTS.md). This note records
the method and the limits of the evidence.

## Source and test review

Read CLAUDE.md, the skill catalog, and the applicable Lean, coverage,
test-suite, repository-tour, issue-management, and Markdown instructions.
Compared the current RDF, SPARQL, and OWL sources with these records:

- [RDF/SPARQL 1.2 semantics](designissues/2026-09-07-rdf12-sparql12-semantics.md).
- [OWL corpus and proof analysis](designissues/2026-09-07-lean-owl-corpus-gap.md),
  especially the final results in section 13.
- [Shared function library](designissues/2026-09-07-function-library.md),
  which also records the earlier SPARQL 1.0 evaluation-only run.
- [Lean README](../formal/lean4/README.md),
  [port notes](../formal/lean4/PORT_NOTES.md), and
  [theorem registry](theorem-registry.md).

Built `l4w3c`, `l4rdf-semantics`, and `l4owl-probe` from current sources:
228 jobs, successful. The explicit working directory for the Lake command
was `formal/lean4/`. This was a targeted executable build, not a full
`lake build`; theorem-only modules outside these dependencies were not
rechecked. No semantic source was edited.

Ran the rebuilt binaries from the repository root, with absolute manifest
paths for `l4w3c` and explicit `--dir third_party/testing/owl` for OWL.
The initial OWL invocation omitted `--dir`; its default is relative to the
Lake project, so it read no catalogs. That run was discarded and replaced
with the explicit-directory run. Never count a missing catalog as a test.

RDF and SPARQL fixtures belong to the same vendored `w3c` checkout, at
`35c503a6323db83c2e54ff404387210c20d57c18`. OWL fixtures are stored in the
main repository. The review did not update fixture pins.

[Machine-readable evidence](20260908-lean-standards-status-evidence.json)
contains the fresh suite lines, diagnostics, commands, and failure messages.
Exit status 1 on failing suites is retained. No local override was added.

| Fresh native run | Pass | Fail | Skip | Unsupported | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| RDF 1.1, six manifests | 1031 | 0 | 0 | 0 | 1031 |
| RDF 1.2 syntax/evaluation/canonical forms, nine manifests | 324 | 0 | 0 | 0 | 324 |
| RDF 1.2 semantics | 40 | 7 | 0 | 0 | 47 |
| SPARQL 1.0, umbrella manifest | 397 | 84 | 0 | 0 | 481 |
| SPARQL 1.1, manifest-all | 631 | 0 | 0 | 0 | 631 |
| SPARQL 1.2, ten leaf manifests | 254 | 0 | 0 | 0 | 254 |
| OWL profile-RL, default RL mode | 126 | 0 | 0 | 0 | 126 |
| OWL profile-QL, default RL mode | 87 | 0 | 0 | 0 | 87 |
| OWL profile-EL, default RL mode | 118 | 2 | 1 | 0 | 121 |
| OWL all six catalogs, default RL mode | 1229 | 218 | 2 | 8 | 1457 |
| OWL type-inconsistency, --dl | 116 | 11 | 1 | 0 | 128 |

All RDF/SPARQL runs reported `no_manifest=0`, `zero_tests=0`, and
`budget_exceeded=0`. The RDF 1.2 semantics runner printed its existing
`MANIFEST-RECOVERY` warning for the undeclared `test:` prefix. All 47 tests
ran. The six-catalog OWL run reported zero cap hits and one parser failure,
`FS2RDF-literals-ar`. Its 1,457 units come from 931 catalog cases, since
one case may carry more than one test type and occur in multiple catalogs.

The RDF 1.1 figure excludes the separate RDFC-1.0 and JSON-LD suites.
Passing syntax tests and passing semantic entailment tests are reported
separately. These are tests of native harness paths; browser, wasm,
network-service, and persisted-store behavior was not re-tested.

## SPARQL 1.0 needs a separate status line

The 481-entry umbrella combines 282 evaluation entries and 199 syntax
entries. The [7 September function-library record](designissues/2026-09-07-function-library.md)
reported 208 pass and 74 fail for evaluation alone. This review adds the
syntax portion: 189 pass and 10 fail. The differing denominator is suite
selection, not a newly established regression.

The 84 fresh failures divide by the runner's reported failure stage:

- 30 expected files are not decoded as Boolean ASK results.
- 10 `.rdf` expected-result files report `unknown result format`.
- 10 query-parser verdicts disagree with their syntax fixtures.
- 34 result comparisons disagree, including open-world equality,
  OPTIONAL, graph/dataset cases, numeric datatype preservation,
  dateTime comparison, and normalization.

These are observed runner failures, not 84 established evaluator defects.
The complete failure messages are in the evidence JSON. A correction
requires per-case analysis of the legacy expectation and the current
parser, evaluator, or result reader. No failing test was waived, and this
review did not assign new expected-failure classifications without that
analysis. The existing [Lean workstream](https://github.com/danbri/factoidal/issues/466)
provides the scope reference; SPARQL 1.1 remains the main project gate.

## Semantic and proof boundaries

### RDF 1.1 and 1.2

`RDF/Core.lean`, `Graph.lean`, `Semantics.lean`, `Entailment*.lean`,
`RDFS/Closure*.lean`, `FullClosure.lean`, and the syntax modules carry
both executable functionality and specification/proof layers. The
rdfs-core completeness theorem requires saturation; model-theoretic
claims must retain the interpretation conditions of the relevant theorem.

The seven RDF 1.2 semantic failures reproduce the final 7 September
record: `literal-type`, `malformed-literal-no-spurious`,
`malformed-literal-bnode-neg`, `annotation`, `annotation-unfolded`,
`triple-terms-propositions`, and `reifies-range`. Their analysis separates
literal-denotation typing, malformed-literal entailment, reifier identity,
subject representation, and the `.rdfs`/`.rdfsPlus` distinction. See
[RDF semantics issue](https://github.com/danbri/factoidal/issues/605).
The fresh failures remain visible; the review did not decide disputed
semantic readings or change the formal model to improve the score.

### SPARQL 1.1 and 1.2

Parser/tokenizer, query algebra, expression evaluation, paths, aggregates,
updates, protocol, Graph Store, SERVICE parameters, results, and OWL query
rewriting exist. `Fn` provides shared function semantics. SPARQL 1.2 tests
exercise triple terms and their accessors, directional language functions,
version directives, and codepoint escapes.

`SPARQL/AlgebraRefinement.lean` proves selected operators with explicit
compatibility and expression hypotheses. Indexed-evaluator equivalence
does not by itself prove the full language against W3C semantics. See
[unified SPARQL adequacy](https://github.com/danbri/factoidal/issues/614)
and [OWL query-rewrite proof work](https://github.com/danbri/factoidal/issues/568).

### OWL RL, QL, and the comprehension layer

`RLRules`, `RLClosure`, `RLClosureIndexed`, `RLTheorems`, and
`RLSemantics` provide a derivation relation, executable closure, indexed
refinement, rule licensing, and conditional semantic preservation.
`indexedClosure_eq` is list equality for every fuel. Completeness is
relative to the represented derivation relation at saturation.

`tools/lean-registry-audit.py` freshly found 52 registry rule identifiers,
50 named by Lean theorems, and two recorded as unproved in both trees:
`cls-maxqc3` and `cls-maxqc4`. This is theorem-name discovery against the
repository registry, not a census of all OWL 2 RL requirements or a review
of theorem strength.

The probe's positive-entailment pipeline also calls `Comprehension`.
`ComprehensionTheorems.comprehensionLayer_sound` proves membership in
`CompStar`; its general model-theoretic soundness remains a separate
obligation in [OWL corpus/proof work](https://github.com/danbri/factoidal/issues/672).

The QL catalog runs through the same RL judges. No profile-identification
checker is run, and source inspection found no dedicated QL/DL-Lite
rewriting implementation. The existing `QueryRewrite*` files implement
OWL class-expression query rewriting, which does not establish a complete
QL algorithm. Read 87 passing units as a catalog result only.

The two profile-EL failures are `New-Feature-Keys-002` and
`WebOnt-someValuesFrom-003`; `WebOnt-Thing-005` is skipped for
`semantics-rdf-based-only`. These cases are listed in the same
[OWL corpus issue](https://github.com/danbri/factoidal/issues/672).

### OWL DL and tableau

`Tableau.lean` defines a declarative Direct Semantics fragment, including
Boolean concepts, existential/universal restrictions, cardinalities,
role inclusions/transitivity, witness introduction, and merging.
`TableauTheorems.refuted_sound` proves the calculus sound. Its canonical
model construction covers the clash-free literal leaf, not full SROIQ(D).

`Refute.lean` implements the graph-based search with `partial def search`,
witness depth 3, batches of at most 6 generated witnesses, and fuel/time budgets. It has no
blocking-based completeness argument. `some false` has a refutation
contract; `some true` does not prove satisfiability; `none` is unknown.
The general executable-to-calculus certificate connection is still
tracked in [tableau completion](https://github.com/danbri/factoidal/issues/586).
Named-individual merging is present in `isMergeableTerm`; the older
module-header statement that only blank nodes merge is stale.

`CountingOracle.farkasSound` and `classSizeUnsat_sound` prove arithmetic
unsatisfiability of constructed constraints. The model-theoretic validity
of extracting those constraints from an OWL graph is a separate proof
obligation. `Refute` does not import or call `CountingOracle`.

The fresh DL inconsistency run used default `--cap-ms 30000`,
`--refute-budget 64`, and `--refute-ms 20000`: 116 pass, 11 fail, one skip,
out of 128, with zero closure cap hits or refuter flips to failure.
The remaining eleven IDs are retained in the evidence JSON.

The other two DL catalogs were not re-run. The latest
[recorded full DL run](designissues/2026-09-07-lean-owl-corpus-gap.md#final-scores---dl-default-budgets)
is 1,032 pass, 82 fail, one skip, eight unsupported, out of 1,123 units
on 2026-09-07, at the same default budgets. It took 19 minutes 56 seconds
on that recorded run. Do not compare its denominator or regime directly
with the six-catalog default RL total. Completion remains tracked in
[the OWL goal](https://github.com/danbri/factoidal/issues/651).

## Instructions and skill discovery

Expanded AGENTS.md while preserving its Lake-working-directory and
worktree rules. Added the dated capability table and the proof boundaries
above. CLAUDE.md remains required reading. Its later full-scope Lean
direction is retained alongside its existing F*-first parser rule.

Reviewed all 43 local skill names/descriptions. The existing
`.claude/skills` catalog already contained a working relative link for
every local skill, plus `lean-proof`, `lean-mwe`, and `lean-review` from
the vendored directories. Added one link:

```
.agents/skills -> ../.claude/skills
```

That shares the complete existing catalog without copying instructions or
changing the user's global skill installation. The `.agents` path is
sandbox-protected; creation used the approved sandbox escalation for the
owner's requested link.

[Official Codex documentation](https://learn.chatgpt.com/docs/build-skills#where-codex-loads-local-skills)
specifies repository `.agents/skills` discovery and symlink support.
Verification used the installed Codex app-server schema and local
`skills/list` API with `forceReload: true`. Both the repository root and
`formal/lean4/` returned the same 46 repository skills, all enabled, with
no errors. No model turn was started. The app server required its normal
local SQLite access, supplied through approved sandbox escalation.

The available-skills prompt in an already running session may retain its
earlier list. Restart the session if the new skills do not appear. The
links and local loader were verified independently of that prompt.

## Validation and status-record limits

Fresh `tools/lean-hygiene-audit.py`: 669 files scanned after stripping
comments and strings; zero `sorry`, user `axiom`, `native_decide`, `unsafe`,
and `@[implemented_by]`; 172 `partial def`, equal to the baseline. No
`--build-log` dependency audit was supplied. This source scan cannot
establish all imported theorem dependencies.

The README, skill score tables, and several issue titles still contain
older states. For example, the README reports the first RDF 1.2 semantic
run, while the current runner reports 40 pass and seven fail. The OWL
issue body stops before the final section-13 scores. Open issue links were
checked read-only on 2026-09-08; their open state does not make every old
description a current defect. This review does not edit issue state.

No complete standards-conformance, full proof-build, or cross-runtime
claim follows from this review. The dated table and saved diagnostics
state exactly which paths and suites were checked.
