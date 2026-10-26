# Factoidal agent instructions

Read [`CLAUDE.md`](CLAUDE.md) and the relevant `skills/<topic>/SKILL.md` before
working in that area. These instructions apply to every coding agent, not only
Claude.

## Project rules from CLAUDE.md

- Use short, technical Simplified English and established W3C terminology.
  Report results directly. Keep issue references clickable with full URLs.
- Lean 4 is the intended full-scope target, per the owner's 2026-08-29
  direction. Keep F* executable as lineage and a differential reference.
  Port functionality, not files; a module-name match is not coverage.
- Specifications and implementations are distinct artifacts. Put semantic
  logic in the formal sources and prove or test the relation between them.
  Compile/extract executable code; do not reproduce it in handwritten
  JS, Rust, or OCaml. Performance work in the formal trees is in scope.
- Follow CLAUDE.md's F*-first rule for new parsers. Activate the `fstar`
  opam switch before F* commands. No `--lax` or admission flags. Keep
  `assume val` gaps and permitted host realisations explicit.
- Full SPARQL 1.1 includes query, update, protocol, SERVICE, and results.
  RDF/S and RDF 1.2 semantics are required. A priority changes ordering;
  it does not exclude functionality from the product.
- Lean policy: no `sorry`, user `axiom`, `native_decide`, or new partial
  semantic definitions. Check theorem dependencies with `#print axioms`;
  the accepted foundations are `propext`, `Classical.choice`, `Quot.sound`.
  Existing partial functions and host externs remain explicit trust limits.
- Run real manifests and fixtures. Label passes, failures, skips,
  unsupported cases, expected failures, backend, regime, and caps. Measure
  performance separately. A suite tests its invoked path only.
- A stated implementation shortfall needs an open issue and an expected
  failure test that fails on unexpected success. Preserve raw failure
  evidence during reviews; do not turn untriaged mismatches into passes.
- Record methodology repairs in the relevant instructions in the same
  change. Attribute decisions to their source; Git authorship alone does
  not distinguish owner instructions from agent-written text. Commit
  attribution belongs to the responsible human.

## Lean 4 working directory

`formal/lean4/` is a self-contained Lake project. Every `lake build`, `lake
exe`, or `lake env` command **must** use `formal/lean4/` as its explicit
working directory. Never run a `lake` command from the repository root,
including after a separate earlier command which happened to `cd` there. Run
repository Git commands from the repository root.

Do not write a combined command that assumes a prior `cd` remains active. Use
separate commands (or set the tool's working directory explicitly) for Lean
and Git work. Before each Lean command, check the tool call's `workdir`, not
the previous transcript. This repeated failure caused root-level Lake errors
and misleading test results on 2026-08-31.

## Worktree discipline

Preserve unrelated working-tree changes. Stage only the files needed for the
current coherent change. Record substantive design and implementation progress
in dated `docs/YYYYMMDD-*.md` worknotes.

## Lean status reviewed 2026-09-08

Current owner priority: complete DL/tableau and measure performance on
useful dataset sizes. SPARQL 1.0 conformance is a parallel subagent task;
keep SPARQL 1.1/1.2 green. The [completion worknote](docs/20260908-lean-dl-completion-and-scale.md)
records subsequent work against the baseline below.

Locally integrated follow-up: total tableau search, qualified-merge
correction, proved public indexed closure, complete RDF-list reading,
definite-filler comparisons, and datatype value exclusions. Native DL
inconsistency is now 118 pass / 9 fail / 1 skip of 128. Three old failures
close; one malformed RDF-list fixture now withholds the old false
refutation. Resource nominal branching and indexed initialization are also integrated;
the inconsistency run now takes 80.813 seconds, so branching cost remains
active work. Shared result decoding and numeric changes bring legacy
SPARQL to 445/36; subsequent dataset-scoping root runs reach 456/25 of 481. The parser
delta reaches 466/15, with SPARQL 1.1/1.2 still 631/0 and 254/0.
Exact IEEE result comparison repairs the two aggregate
comparison regressions; root reruns restore SPARQL 1.1 to 631/0 and
SPARQL 1.2 to 254/0.
The [soundness review](docs/designissues/2026-09-08-qualified-tableau-merges-and-public-closure.md)
records the reproduced counterexamples and their repairs. Do not treat the baseline refutation
contract as an established executable soundness result.
Negation-goal name collisions are repaired by scoping both input graphs;
public entailment now returns unknown for uncertified open branches and
unsupported conclusion forms. Root focused builds and all 128 native ABI
smoke checks pass. Unresolved witness obligations now return unknown;
the depth-four/five contradictions no longer return false consistency.
The untyped functional-property counterexample is repaired and its public
controls pass. The zero-cardinality/superproperty repair and its public controls also pass. Indexed initial nodes equal the explicit subject-seeding and type-label
specification through a proved compiler substitution. The latest full build passes all 1198 jobs, including subject seeding,
zero-bound repair, parser proof repairs and proved named TBox dispatch. Its hygiene audit scans
671 Lean files, retains 171 partial definitions, and reads 962 axiom
reports with no prohibited trust mechanisms. The native OWL probe now terminates
and reaps a separate refuter process at the deadline; a one-second test
exits in 1.30 seconds. Parent serialization precedes this deadline. The
latest full DL catalog rerun is 1050 pass / 64 fail / 1 skip / 8 unsupported
out of the same 1123 judgments (482 distinct IDs), in 452.2 seconds with
ten refuter timeouts. The completion worknote records exact changed cases.
All 128 native API checks pass. Further catalog and scale measurements are
recorded in the [9 September continuation](docs/20260909-lean-dl-completion-continuation.md).

This is a dated snapshot, not a standing conformance claim. The
[review worknote](docs/20260908-lean-standards-status-and-codex-skills.md)
records source boundaries, manifests, commands, and evidence. The table
below records the baseline at `0c331255b3a0fec0306b5459a944749364db891f`,
before the locally integrated follow-up. All rows were measured on
2026-09-08, including a fresh three-catalog DL rerun. These scores do not certify browser, wasm, or persisted-store paths. The
three DL catalogs overlap: 1123 catalog/type judgments cover 482 distinct
test identifiers. See the completion worknote before aggregating counts. The native refuter
timeout wrapper was found to run pure work before task creation; baseline
cap settings are configured values, not verified wall-clock bounds.

| Area / suite | Pass | Fail | Skip | Unsupported | Total | Evidence date |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| RDF 1.1: six syntax/semantics manifests, including rdf-mt | 1031 | 0 | 0 | 0 | 1031 | 2026-09-08 |
| RDF 1.2: nine syntax/evaluation/canonical-form manifests | 324 | 0 | 0 | 0 | 324 | 2026-09-08 |
| RDF 1.2 semantics | 40 | 7 | 0 | 0 | 47 | 2026-09-08 |
| SPARQL 1.0: legacy umbrella manifest | 397 | 84 | 0 | 0 | 481 | 2026-09-08 |
| SPARQL 1.1: manifest-all | 631 | 0 | 0 | 0 | 631 | 2026-09-08 |
| SPARQL 1.2: ten leaf manifests | 254 | 0 | 0 | 0 | 254 | 2026-09-08 |
| OWL profile-RL catalog, default RL mode | 126 | 0 | 0 | 0 | 126 | 2026-09-08 |
| OWL profile-QL catalog, default RL mode | 87 | 0 | 0 | 0 | 87 | 2026-09-08 |
| OWL profile-EL catalog, default RL mode | 118 | 2 | 1 | 0 | 121 | 2026-09-08 |
| OWL: all six catalogs, default RL mode | 1229 | 218 | 2 | 8 | 1457 | 2026-09-08 |
| OWL DL: type-inconsistency, --dl | 116 | 11 | 1 | 0 | 128 | 2026-09-08 |
| OWL DL: three type-* catalogs, --dl, default budgets | 1032 | 82 | 1 | 8 | 1123 | 2026-09-08 |

- **RDF 1.1/1.2:** term, graph, dataset, datatype, syntax, and
  interpretation layers exist under `L4Factoidal/{RDF,RDFS,Syntax}`.
  RDF 1.2 triple terms, reifiers, annotation syntax, base direction, and
  version directives are exercised. The seven semantics failures are
  `literal-type`, `malformed-literal-no-spurious`,
  `malformed-literal-bnode-neg`, `annotation`, `annotation-unfolded`,
  `triple-terms-propositions`, and `reifies-range`. See
  [RDF semantics tracking](https://github.com/danbri/factoidal/issues/605)
  and the [1.2 analysis](docs/designissues/2026-09-07-rdf12-sparql12-semantics.md).
- **SPARQL:** parser, algebra, expressions, query forms, aggregates,
  property paths, updates, protocol/Graph Store, results, and OWL query
  rewriting exist. The legacy 1.0 result includes 40 runner result-format
  failures, 10 query-parser verdict failures, and 34 result mismatches;
  it is not 84 established evaluator defects. Algebra refinement and
  unified adequacy have explicit fragment/hypothesis limits. See
  [Lean workstream](https://github.com/danbri/factoidal/issues/466),
  [algebra adequacy](https://github.com/danbri/factoidal/issues/614), and
  [OWL rewrite proofs](https://github.com/danbri/factoidal/issues/568).
- **OWL RL and QL:** `RLRules`, `RLClosure`, `RLTheorems`, and
  `RLSemantics` separate rules, execution, and semantics;
  `RLClosureIndexed.indexedClosure_eq` proves equality to the list engine
  for every fuel. Completeness is relative to the represented rules at
  saturation. The probe also uses a separate comprehension layer whose
  `CompStar` model-theoretic soundness remains tracked in
  [OWL corpus/proof work](https://github.com/danbri/factoidal/issues/672).
  The QL catalog runs through the same RL judges: it does not establish a
  QL profile checker, DL-Lite rewriting algorithm, or QL completeness.
- **OWL DL/tableau:** `Tableau` and `TableauTheorems` prove soundness of
  the declarative fragment; `Refute` is a separate executable search.
  Its general certificate/refinement connection remains tracked in
  [tableau completion](https://github.com/danbri/factoidal/issues/586).
  Search is now total with an explicit work stack and proved remaining-
  budget bounds. Witness depth 3, batches of at most 6 generated witnesses,
  and search/time
  budgets remain, without a blocking-based completeness result.
  `some true` is not a proved satisfiability result; `none` is unknown.
  `CountingOracle` proves its arithmetic certificate check, not the
  graph-to-constraint model theory, and the refuter does not call it.
  See the [DL corpus/proof analysis](docs/designissues/2026-09-07-lean-owl-corpus-gap.md)
  and [OWL completion goal](https://github.com/danbri/factoidal/issues/651).

Baseline source audit: 669 Lean files; zero `sorry`, user `axiom`,
`native_decide`, `unsafe`, and `@[implemented_by]`; 172 `partial def`
declarations, equal to the committed baseline. This scan did not audit
imported theorem dependencies. The 228-job targeted runner build passed;
it is not a full `lake build` or full proof audit. The later integrated
total-search/result-decoder tree passed all 1196 Lake jobs and the axiom
audit; its partial-definition count is 171. Further integration checks
are recorded in the completion worknote.

## Codex skill discovery

`.agents/skills` is a relative symlink to `../.claude/skills`. That existing
catalog links to the canonical `skills/*` directories and to three vendored
Lean skills under `third_party/skills/`. Keep one copy of each skill's
instructions. When adding a skill, add its `.claude/skills/<name>` link;
Codex sees the same catalog through `.agents/skills`.

On 2026-09-08, Codex's local `skills/list` with `forceReload: true` found
all 43 repository skills plus `lean-proof`, `lean-mwe`, and `lean-review`,
with no errors, from both the repository root and `formal/lean4/`.
[Official discovery documentation](https://learn.chatgpt.com/docs/build-skills#where-codex-loads-local-skills)
describes `.agents/skills` and symlink support. If the current session's
skill list does not refresh, start a new Codex session.

Read the relevant skill before work; use the complete catalog in
[CLAUDE.md](CLAUDE.md#skills-operational-details-on-demand). Common entry points:

- [Lean basics](skills/factoidal-lean-basics/SKILL.md),
  [proof patterns](skills/lean4-proof-patterns/SKILL.md), and
  [vendored proof review](third_party/skills/lean-agent-skills/lean-review/SKILL.md).
- [Coverage counting](skills/counting-coverage/SKILL.md),
  [test suites](skills/test-suites/SKILL.md), and
  [inference measurement](skills/measuring-inference/SKILL.md).
- [Lean performance](skills/lean4-performance/SKILL.md),
  [resource-scaling checks](skills/danbri-function-precrime-checkers/SKILL.md),
  and [wasm export](skills/lean4-wasm-export/SKILL.md).
- [Block engine](skills/blockengine/SKILL.md) and
  [Shardborough storage](skills/shardborough-storage/SKILL.md).
- [Issue management](skills/issue-management/SKILL.md),
  [Markdown style](skills/markdown-style/SKILL.md), and
  [repository tour](skills/repo-tour/SKILL.md).
