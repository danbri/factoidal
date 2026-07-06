# ShEx program plan

Scoping doc for a ShEx (Shape Expressions) validator, modeled on the
scope cuts in
[`2026-07-04-jsonld-program-lessons.md`](2026-07-04-jsonld-program-lessons.md).
ShEx is a second shapes language alongside SHACL — same problem shape
(validate an RDF node against a schema, produce pass/fail), different
schema language and a genuinely harder semantics for recursive shapes.
`SHACL.Validation.fst` (98/98) is the closest precedent and is used
throughout as the reuse baseline.

## Vendored suite: verdict

`third_party/testing/shex` is **already declared as a git submodule**
in `.gitmodules` (`url = https://github.com/shexSpec/shexTest.git`),
pinned at commit `7d0cd92b` (2023-09-09, "fix typo in
validation/#extends-closed-diamond_pass-bottom"). The working
directory is empty — the submodule was never initialized, not never
vendored. `git ls-files -s third_party/testing/shex` shows the
`160000` gitlink; there is simply no checkout.

Checked via `git ls-remote` + a scratch clone (no fetch beyond that
was needed):

- The pin **is** an ancestor of `shexSpec/shexTest`'s current `main`
  (last touched 2026-05-02), only 2 commits behind, and both of those
  commits are a `package-lock.json` dependency bump (`@xmldom/xmldom`)
  — zero test-content drift. The pin is effectively current.
- The `2.2.0-alpha.1` tag is *older* than the pin (2022-08-19, a
  pre-merge snapshot of the `extends` feature branch), not a newer
  draft — ignore it.
- **Verdict: no re-vendor needed.** Run
  `git submodule update --init --depth 1 third_party/testing/shex`
  (or a full clone if depth-1 causes checkout issues) to populate the
  already-pinned, already-current submodule. This is the only network
  operation the plan requires; everything else below was inventoried
  from a disposable scratch clone, not committed anywhere.

### Suite inventory (shexSpec/shexTest, pinned commit)

| Directory | Manifest entries | Format |
|---|---|---|
| `validation/` | 1190 (620 `sht:ValidationTest` pass + 570 `sht:ValidationFailure` fail) | `manifest.ttl` (+ `manifest.jsonld` sibling, unneeded) |
| `schemas/` | 441 `sht:RepresentationTest` (ShExC↔ShExJ↔ShExC round trip) | `manifest.ttl`, ~466 `.shex` + ~437 `.json` + ~453 `.ttl` files |
| `negativeStructure/` | 14 `sht:NegativeStructure` (schema-level errors, incl. negation cycles) | ShExC only (`sx:shex`, no `sx:json`) |
| `negativeSyntax/` | 100 `sht:NegativeSyntax` (ShExC grammar violations) | ShExC only |

Manifests are **plain Turtle** — `SPARQL11.Parser`/RDF store already
read these natively. Unlike the JSON-LD program (which needed a
Python manifest flattener because JSON-LD manifests need JSON-LD
processing to read), ingesting shexTest manifests costs nothing new.

### ShExC vs ShExJ: the scope-cut that makes ShExJ-first cheap

`validation/manifest.ttl`'s `sht:schema` predicate points at `.shex`
(ShExC) in 1188 of 1190 entries — the suite's *canonical* test format
is ShExC, not JSON. But cross-checking the 346 unique schema
basenames actually referenced from `validation/` against the `.json`
files present in `schemas/`: **342/346 (98.8%) have a ready-made ShExJ
twin** (same basename, `.json` instead of `.shex`). Only 4 do not
(`1literalTotaldigitsxsd-integer`, `extends-abstract-multi-empty`,
`extends-closed-3diamond-split`, `extends-closed-diamond`).

So: consuming `../schemas/<name>.json` in place of the manifest's
`.shex` reference is nearly free for validation testing, at the cost
of 4 known-missing fixtures. `negativeStructure/` and
`negativeSyntax/` ship **ShExC only** by construction — they test the
ShExC grammar and structural parse failures, so there is no ShExJ
substitute; they stayed out of reach until Stage 9 landed a ShExC
grammar (`Parser.ShExC.fst` — 433/433 `schemas/` pairs structurally
equal against the existing ShExJ decoder, `bin/shex-runner
--differential`). `schemas/`'s 441 `RepresentationTest` entries
explicitly require ShExC↔ShExJ conversion in both directions; the
differential run above covers the ShExC→AST direction (the direction
this project's validator actually needs — it consumes schema text, it
never re-serializes ShExJ back to ShExC), so `negativeSyntax`'s 100
grammar-rejection tests and `negativeStructure`'s 14 tests are the
remaining unexercised part of this stage's original scope (not run by
this landing; the differential oracle only walks `schemas/`, the
positive-parse corpus).

## Latest draft status

ShEx 2.1, **Final Community Group Report**, published 2019-10-08
([shex.io/shex-semantics](https://shex.io/shex-semantics/)), editors
Prud'hommeaux / Boneva / Labra Gayo / Kellogg. It is not a W3C
Recommendation-track document (ShEx has stayed a CG report, unlike
SHACL). There is no 2.2 or 3.0 successor draft; the `2.2.0-alpha.1`
tag in the test repo is an older pre-merge snapshot, not a newer
draft, per the ancestry check above. `shexSpec/shexTest` `main` is
actively maintained (dependabot bumps as recently as May 2026);
`shexSpec/spec` `main` likewise has recent activity. Test-suite
*content* has been stable since ~2023.

The shexTest README defines three conformance tiers: **Logic-conformant**
(pass/fail only), **Result-conformant** and **Error-conformant** (both
explicitly marked experimental — structured `ValidationResult`/error
shape matching). Same cut as JSON-LD's toRdf-only scope: target
Logic-conformant only.

## Reuse vs ShEx-specific, against `SHACL.Validation.fst`

**Reusable machinery (transliterate the computation, not the module —
ShExJ's AST shapes differ from SHACL's RDF-graph-encoded shapes):**

- Path evaluation. `SHACL.Validation.fst`'s `eval_path_fuel` /
  `eval_seq_fuel` / `eval_alt_fuel` / `eval_plus_fuel` (lines 744-804)
  already implement `sequence`/`alternative`/`oneOrMore` path
  evaluation with a fuel-bounded recursive-descent — ShEx paths
  (`predicate`, `inversePath`) are structurally the same problem.
- Leaf constraint checks. SHACL's `constraint_component` dispatch
  (`node_kind_ok`, datatype/pattern/facet comparisons,
  `numeric_cmp_le`/`numeric_cmp_lt`, `literal_to_scaled`) computes the
  same things ShEx's `NodeConstraint` needs (`nodeKind`, `datatype`,
  `values`, `stem`, length/pattern/numeric facets) — same arithmetic,
  new AST to pattern-match on.
- Fuel-bounded recursion idiom. `shacl_class_closure` (fixpoint over a
  graph, fuel-decreasing) and `collect_shape_violations`
  (mutually-recursive shape descent, fuel-decreasing) are the pattern
  Stage 5's fixpoint typing reuses directly.
- Manifest ingestion. Turtle parser reads `manifest.ttl` with zero new
  tooling (see above) — better than the JSON-LD precedent.

**Genuinely ShEx-specific (no SHACL analog):**

- ShExJ AST + JSON decoder. New module, `Parser.JSON`-based (same
  pattern as `JSONLD.Context.fst` consuming `Parser.JSON`).
- Triple-expression partition matching (`EachOf`/`OneOf` with
  cardinalities). SHACL's `sh:property` list is an implicit "each
  property shape validates independently against the full value set
  reachable via its own path" — there is no shared-predicate
  ambiguity to resolve, because SHACL property shapes each own their
  path. ShEx's `TripleConstraint`s **partition a single triple set**
  among siblings, which is a matching problem SHACL never had. This is
  the hard part — see the design sketch below.
- Shape maps (external focus/shape association syntax,
  `{focus}@<shape>`). No SHACL analog (SHACL uses in-graph
  `sh:targetNode`/`sh:targetClass`).
- Recursion + negation stratification. SHACL's fuel-recursion has no
  monotonicity guarantee — SHACL Core leaves recursive-shape behavior
  undefined, so `collect_shape_violations` just fuel-bounds and moves
  on. ShEx's spec **mandates** a stratified fixpoint semantics (see
  Stage 5) — this is new design work, not a port.
- `EXTENDS` (shape inheritance / triple-expression merge). Wholly new,
  a ShEx 2.1 addition with its own algorithm in the spec.

## Scope cuts

1. **ShExJ-first; ShExC deferred indefinitely.** Loses
   `negativeSyntax` (100 tests, by construction ShExC-grammar-only),
   `schemas/`'s `RepresentationTest` (441, requires round-trip
   conversion), and 4 of 346 validation schemas lacking a `.json`
   twin. Everything else — 1186/1190 validation entries, all 14
   `negativeStructure` entries — reachable via ShExJ alone. A ShExC
   grammar is a program of its own size (comparable to Turtle's, per
   iron rule #4: new parsers are F\*-first) and is not justified until
   the ShExJ-reachable 99.7% is done.
2. **Logic-conformant only.** Boolean pass/fail; no
   `ValidationResult`/error-report structure matching (the suite's own
   README calls those tiers experimental).
3. **Shape maps: manifest-only, no query syntax.** `validation/`
   entries carry `sht:focus`/`sht:shape` as a single pair per test —
   that is all a validator needs. The full external ShapeMap query
   syntax (`{focus}@<shape>,{...}` with wildcards, `sht:map`/
   `sht:ShapeMap`-tagged, 3 tests) is a query-tool feature, same tier
   as SPARQL query-planning follow-ups — out of scope until something
   needs to *query* rather than *validate*.
4. **SemActs + EXTERNAL declared out of scope.** Semantic actions
   (`sht:SemanticAction` 22 + `sht:ExternalSemanticAction` 4) and
   `EXTERNAL` node kind (`sht:ExternalShape` 4) are host-language
   extension points, orthogonal to core validation semantics. ~2% of
   `validation/`, no suite pressure to implement.
5. **Imports deferred.** `sht:Import` (33) + `sht:circularImports` (1)
   — cross-file schema composition. Small, mechanically a schema-merge
   pass once `ShEx.Schema.fst` exists; no new validation semantics.
6. **EXTENDS staged separately from recursion.** `sht:Extends` (77) +
   `sht:MultiExtends` (7) + `sht:Abstract` (7) is shape-inheritance
   triple-expression merging — a distinct spec algorithm from
   `shapeExprRef` recursion, not a subcase of it. Do not conflate the
   two designs.

## Staged plan

| Stage | Deliverable | Predicted coverage | Gate |
|---|---|---|---|
| 1 | Vendor + `ShEx.Schema.fst` (ShExJ AST + `Parser.JSON` decoder) | Structural parse of ~437 ShExJ fixtures; no pass/fail signal yet | none |
| 2 | `ShEx.Validation.fst` NodeConstraint dispatch (nodeKind, datatype, values, stem, facets, equivalence) | Validation tests whose shape is a bare `NodeConstraint` — a few hundred of 1190 | Stage 1 |
| 3 | Triple-expression matching, **disjoint-predicate fast path only** (`TripleConstraint` + `EachOf`, no ambiguity) | `TriplePattern` (45) + most `EachOf` (73) + `DotCardinality` (28) + `FocusConstraint` (47) + non-ambiguous `Extra` (24) — likely the single largest jump, probably a majority of `validation/` | Stage 2 |
| 4 | Backtracking slow path + `Extra`/`Closed` | `OneOf` (15) + `RepeatedOneOf` (17) + `Greedy` (3) + `RepeatedGroup` (3) + `VapidExtra` (8) + `Wildcard` (1) + `Closed` (12) | Stage 3 |
| 5 | Recursion + stratification (the hard design problem, see below) | `ShapeReference` (24) + `RecursiveData` (2) + correctly **rejecting** the `negativeStructure` cycle-negation tests (`Cycle1Negation1/2/3`, `Cycle2Negation`, `TwoNegation`/`TwoNegation2`) | Stage 4 |
| 6 | `ShEx.Extends.fst` (shape inheritance merge) | `Extends` (77) + `MultiExtends` (7) + `Abstract` (7) + `ExtendsDiamond` (14) | Stage 4 (reuses the partition engine, not Stage 5) |
| 7 | Imports (34) + manifest-driven ShapeMap pair (already free from Stage 2 onward) | remaining small trait tags | Stage 2 |
| 8 | `bin/shex-runner/` wiring | Score `validation/` at Logic-conformant level, labelled by stage reached | Stage 3 (first stage with a nontrivial signal) |
| 9 (**landed**) | ShExC grammar in F\* (`formal/fstar/Parser.ShExC.fst`) | 433 of 433 `schemas/` ShExC↔ShExJ pairs structurally equal (`bin/shex-runner --differential`; the 1 known upstream-defect fixture, `start2RefS2`, counted as a correct disagreement, not a failure) | own program, iron rule #4 |

**Recommended commit-sized Stage 1, today:**
`git submodule update --init --depth 1 third_party/testing/shex`
(populate the already-pinned, already-current submodule — zero design
risk) + a `ShEx.Schema.fst` skeleton: the ShExJ `Schema`/`shapeExpr`/
`tripleExpr` sum types and a `Parser.JSON`-based decoder for the
top-level `{"type":"Schema","shapes":[...]}` structure, verified but
inert (no `validate` function yet). Predicted result: parses all
~437 ShExJ fixtures — a "does it parse" smoke check, not a suite
score, exactly like the JSON-LD program's Stage 1 (expanded-form →
dataset before context processing existed).

## Partition-semantics design sketch (Stage 4's hard part)

The spec's `matches(T, expr, m)` (shex.io/shex-semantics) requires,
for `EachOf(e1..en)` applied to triple set `T`: **some partition** of
`T` into `T1..Tn` such that `matches(Ti, ei, m)` for each `i`. For a
`TripleConstraint(p, se, min, max)`: a sub-multiset of `T`'s
`p`-predicate triples whose size is in `[min, max]` and whose values
all satisfy `se`. For cardinality-wrapped groups (`RepeatedOneOf`,
`RepeatedGroup`, "Greedy" in the trait vocabulary): `T` splits into
`k` repetitions, each repetition itself fully matching **one**
alternative — this is where naive per-branch evaluation breaks,
because which alternative a given repetition belongs to is not known
in advance when alternatives share a predicate.

**Two-tier design, mirroring the reference JS implementation's
observed behavior:**

1. **Fast path — static predicate-signature disjointness.** For each
   shape, statically compute each triple-expression subtree's "arc
   signature" (the set of predicates it can consume, direction-aware
   for `inversePath`): `TripleConstraint` → `{p}`; `EachOf`/`OneOf` →
   union of children. If every sibling group at every node has
   pairwise-disjoint signatures — true for the overwhelming majority
   of the corpus (`TriplePattern`, most `EachOf`, `DotCardinality`) —
   assignment is fully determined: group `T` by predicate, hand each
   bucket to the unique claimant, check `[min,max]` and value
   satisfaction. No search. This check runs once per shape (schema
   load time), not per instance.
2. **Slow path — fuel-bounded backtracking.** When signatures overlap
   (shared predicate across `OneOf` alternatives or across `EachOf`
   siblings — the `RepeatedOneOf`/`Greedy`/`RepeatedGroup` tests, ~23
   of 1190), fall back to a recursive search: pick a triple from `T`,
   try it against each candidate leaf whose signature contains its
   predicate and whose count is still under `max`, recurse on the
   reduced multiset and reduced counters, backtrack on dead ends.
   Bound with a `fuel : nat` decreasing on triples-remaining (same
   idiom as `eval_plus_fuel`/`shacl_class_closure`) to keep the
   function `Tot`. Test-suite data graphs are small (a handful of
   triples per focus node), so worst-case exponential blowup is
   acceptable for a correctness-first cut — this is a place perf work
   is explicitly deferred (perf-benchmarking rule: never bundle a perf
   claim into a correctness change). A memoized DP refinement
   (bucket-then-permute-within-bucket, avoiding re-exploring identical
   sub-multisets) is the natural follow-up once the slow path is
   measured to matter.

`Extends` (Stage 6) reuses this same engine — an inherited shape's
triple expression is merged into the derived shape's `EachOf` before
partition matching runs, so sequencing Stage 6 after Stage 4 means the
partition engine already exists to be fed into, not redesigned.

## Recursion/negation strategy (Stage 5)

The spec's approach (confirmed against shex.io/shex-semantics):

1. **Dependency graph.** One node per shape label; an edge `s1 -> s2`
   (positive) if `s1`'s expression references `s2` (via a shape
   reference inside a `ShapeAnd`/`ShapeOr`/`Shape`'s triple
   expressions); the edge is *negated* if it passes through an odd
   number of enclosing `ShapeNot`s (double negation cancels back to
   positive — the spec explicitly permits this).
2. **Validity check.** Compute strongly connected components (a small
   Tarjan/Kosaraju routine — check first whether an SCC helper already
   exists anywhere in the codebase for OWL closure work before writing
   a new one). Reject the schema (this is exactly what
   `negativeStructure`'s `Cycle1Negation1/2/3`, `Cycle2Negation`,
   `TwoNegation`/`TwoNegation2` test) if any negated edge's two
   endpoints land in the same SCC — "the dependency graph MUST NOT
   have a cycle that traverses a negated reference," per spec.
3. **Stratification.** Condense SCCs into a DAG (mutually-recursive,
   non-negated-internally shapes share a stratum); topologically sort
   the condensation; assign strata in increasing order along that
   sort so that `stratum(callee) < stratum(caller)` for positive
   references.
4. **Fixpoint typing per stratum.** Within one stratum, compute the
   typing relation via monotone fixpoint iteration (start empty,
   repeatedly extend until stable or fuel exhausted) — the same
   fuel-bounded-fixpoint idiom `shacl_class_closure` already uses for
   `rdfs:subClassOf` closure. Cross-stratum references read the
   already-finalized typing from lower strata as fixed input.

**Scope-narrowing observation:** recursion-tagged tests
(`ShapeReference` 24, `RecursiveData` 2) plus the 6 negation-cycle
`negativeStructure` tests are a small minority of the 1190+14 corpus.
Schemas with **no** recursion at all — the majority — need none of
this machinery; a plain top-down recursive-descent evaluator (no
fixpoint, no SCC) suffices and should be what Stages 2-4 actually
build. Stage 5 is additive: build the SCC/stratification/fixpoint
layer only once Stage 4's runner shows which failures are actually
attributable to shape-reference cycles, rather than building it
speculatively. This is the one place where copying
`SHACL.Validation.fst`'s fuel-recursion wholesale would be wrong: it
silently *accepts* inputs ShEx's spec requires *rejecting*
(unstratifiable negation) — SHACL Core leaves recursive-shape
semantics undefined and never had to make this call.

## Module layout

- `formal/fstar/ShEx.Schema.fst` — ShExJ AST (`Schema`, `shapeExpr`,
  `tripleExpr` sum types) + `Parser.JSON`-based decoder. Same
  precedent as `JSONLD.Context.fst` consuming `Parser.JSON`.
- `formal/fstar/ShEx.Validation.fst` — NodeConstraint dispatch +
  `matches()` partition engine (fast + slow path). If this grows past
  the semantic-core-vs-pragmatics comfort zone (see
  `fstar-module-style`), split the SCC/stratification/fixpoint layer
  into `ShEx.Recursion.fst` to keep `.checked` cascades cheap.
- `formal/fstar/ShEx.Extends.fst` — Stage 6, kept as its own module
  (own algorithm, own spec section) rather than folded into
  `ShEx.Validation.fst`.
- `bin/shex-runner/shex_runner.ml` — consumer wiring only (rule #11):
  reads `manifest.ttl` via the existing extracted Turtle parser and
  generic RDF term accessors (no Python converter needed, unlike the
  JSON-LD runner), loads the `.json` schema fixture through extracted
  `ShEx.Schema`, loads `.ttl` data through the existing Turtle parser,
  calls extracted `ShEx.Validation.validate`, compares against the
  manifest's `sht:ValidationTest`/`sht:ValidationFailure` expectation.
  No new `assume val`s expected — same I/O shape as the SHACL and
  JSON-LD runners already realise.

## Open questions / risks

- Backtracking worst-case complexity in the Stage 4 slow path is
  exponential; acceptable now because suite fixtures are small, but
  flag it for `perf-benchmarking` once Stage 4 lands rather than
  asserting it is fine forever.
- Whether an SCC/Tarjan helper already exists in the OWL modules
  (closure/consistency checking sometimes needs one) — check before
  writing a new one for Stage 5; if one exists it may not be reusable
  as-is (label domain, fuel style) but the algorithm shape transfers.
- `negativeStructure`'s 14 tests are ShExC-only fixtures (`sx:shex`,
  no `sx:json`) even though the errors they test (cycle-negation) are
  schema-structural, not grammar-level — Stage 5 will need either a
  minimal hand run of the reference `bin/genJSON.js` converter (not
  something we write ourselves; it is the suite's own tooling) or to
  accept these 14 tests stay unreachable until Stage 9's ShExC parser
  exists. Note this rather than silently skip it.
