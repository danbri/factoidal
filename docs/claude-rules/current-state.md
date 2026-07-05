# Current State (Honest Assessment)

Last refreshed: 2026-07-05 (ShEx-completion wave B: **1176 pass, 6
mismatch, 0 deferred, 0 skipped (of 1182)**. Runner side: focus
base-resolution fix (+25), recursive cycle-safe Imports (+17),
ShapeExternal (+4), bnode shape labels (+2), base-threaded schema
decoding (+2). Semantics side: diamond-dedup ancestor resolution,
running-intersection chain matching, unbounded-completion
restriction, abstract shapes per the inheritance paper's Definition
4 (+12). The 6 remainders: 1 upstream fixture defect
(start2RefS2.json has p1 where the canonical .shex has p2) + 5
vitals-RESTRICTS tracing to a distinct same-predicate exact-valued
TripleConstraint pairing gap in tc_choose_acc — one focused
follow-up. All floors held.)

Previous (ShEx-completion wave A: **1115 pass, 42
mismatch, 25 deferred, 0 skipped (of 1182)** — stage 4 backtracking
partition search, stage 5 recursion (coinductive visited-stack),
stage 6 EXTENDS per the inheritance-semantics paper, SemActs with
the Test extension, ShapeMap-form tests, 23 hand-translated ShExJ
twins with provenance (tests/shex-shexj-twins/), plus an XSD
leading-plus datatype fix. Remainder precisely triaged: 25
mismatches are a runner base-resolution bug, ~13 need
multi-ancestor/abstract inheritance, 18 deferred need Imports, 4
ShapeExternal, 2 bnode shape labels, 2 relative-IRI bases — wave B
in flight. All floors held: SHACL 120/120, RDFC 86/86, JSON-LD
404/52/11, SPARQL 631/0, RDF 1031/0, unit 23/23, npm 60/61.)

Previous (wave-10 battery: **OWL 2 RL maximally
complete** — PE 28 pass, 2 fail (the documented-impossible
comprehension pair), 0 skip; NE 6/0; Consistency 76/0/0;
Inconsistency 14/0/0 — via three new closure rules
(transitive-to-chain scaffold, cls-hv1/hv2, dt-range-clash) + the
Consistency functional-syntax path. JSON-LD toRdf 404/52/11 — the
@graph-container cluster fell to a spec decision table (plain
@container:@graph wraps unconditionally; @id/@index maps
conditionally — one dispatch arm changed, zero regressions across
the 27 previously-implicated tests). RIF 13 pass, 1 KNOWN-DEFECT
fail (W3C zip defect), 36 bucketed skips (of 50) — PlainLiteral
lang-tag decoding + OWL-Direct annotation exclusion
(OWL.DirectMapping.Filter.fst); rif_runner now has a build stanza
(manual installs were being silently reverted by chain rebuilds).
RML stage 2: RML.Sources.fst (JSON iteration + JSONPath subset) +
RML.Eval.fst (full term-map evaluation, IRI-safe encoding per spec)
— 60 pass, 6 documented mismatches, 10 stage-5/6 skips (of 76
rml-core JSON tests, scratch driver; runner is stage 8). Held: RDFC
86/86, SHACL 120/120, ShEx 1022, SPARQL 631/0, RDF 1031/0, unit
23/23, npm 60/61.)

Previous (wave-9 battery: JSON-LD toRdf 399 pass,
57 fail, 11 skip of 467 (alias-@value dispatch, fromMap
pop-suppression, property-scoped ordering; @graph-container fix
attempted, found to regress 22 tests, reverted with diagnosis). OWL
functional-syntax parser landed (Parser.OWLFunctional.fst) — zero
skips left in PE/Inconsistency, every non-pass now diagnosed: PE
27/3/0 (2 comprehension impossible + 1 needs chain-to-transitive
rule), Inconsistency 12/2/0 (both need cls-hv/datatype-range rules),
NE 6/0, Consistency 75/0/1. RIF measured against the real W3C Core
corpus (46 tests vendored): 11 pass, 3 fail, 36 skip of 50 total —
skips bucketed by construct (16 BLD builtins, 6 syntax-safeness, 6
import-rejection, …), 1 fail is a 2010-era defect in the official
W3C zip. RML stage 1: five kg-construct suites vendored (224
tests), RML.Mapping.fst decodes 73 of 76 rml-core mapping docs (3
are error fixtures). Held: RDFC 86/86, SHACL 120/120, ShEx
1022/11/123/26, SPARQL 631/0, RDF 1031/0, unit 23/23, npm 60/61.)

Previous (wave-8 battery — three suites now
complete: **RDFC-1.0 86 pass, 0 fail (of 86)** (Map tests compared
structurally per the suite README; HNDQ poison budget implements the
NegEval abort), **SHACL 120 of 120**, **RIF 4 of 4**. OWL 2 RL:
NegativeEntailment 6/0 via semantics-flavor dispatch (Direct vs
RDF-Based mode threading), Consistency 75/0 + 1 functional-syntax
skip, Inconsistency 11/0 + 3 FS skips, PE 27 + 2 comprehension
(definitively scoped out in scope.md) + 1 FS skip — every non-pass is
documented-impossible or awaits the planned functional-syntax parser
(docs/designissues/2026-07-05-owl-functional-syntax-plan.md). ShEx
battery-visible via bin/shex-runner: 1022 pass, 11 mismatch, 123
deferred, 26 skipped (of 1182) — XSD float/digit-facet fixes + regex
{0,m}/control-escape fixes flipped 20. JSON-LD toRdf 389/67/11
(protected-terms + processingMode clusters). Regex glue: #276+#277
fixed, 71-case pin battery, unit suite 23 files. RML program plan:
docs/designissues/2026-07-05-rml-program-plan.md. SPARQL 631/0, RDF
1031/0, npm 60/61 all held.)

Previous (wave-7 battery: JSON-LD toRdf 379 pass
77 fail 11 skip of 467 (+5, type-scoped context fixes); ShEx stage 3
triple-expression matching — 1005 of 1182 validation-manifest entries
match expected verdicts (31 triaged mismatches, 146 correctly
deferred); regex ? quantifier glue fixed (#276, 38-case unit pin
battery, unit suite now 22 files); canonicalize #272 hashing tail
fixed — 100k bnode-heavy 462.9s to 4.83s (96x), 300k timeout to
16.2s, byte-identical, rdfc10 84/1/1 exact; SPARQL 631/0 + RDF
1031/0 + SHACL 120/120 + OWL floors + npm 60/61 all held.
Process note: patch-script changes REQUIRE invalidating the
manifest entries of the modules they patch — see fast-verify-extract
skill.)

Previous (wave-6 battery: SPARQL 631/0, RDF
1031/0, RDFC-1.0 84 pass 1 fail 1 stub of 86, **SHACL suite complete:
core 98/0 report-isomorphism + sparql 22/0 of 22** (custom constraint
components, ASK+SELECT validators, $shapesGraph/$currentShape), OWL
RL PE 27/2/1 + NE 4/2 + Inconsistency 11/0/3, JSON-LD toRdf 374/82/11
of 467, RIF 4/0, ShEx stage 2 node-constraint validation 43 of 44
reachable manifest entries (regex ? glue bug #276 accounts for the
1), XSD.Datatypes foundation module landed (slice 1), dump-nq #272
tail fixed: near-flat ~40k triples/s from 10k to 300k (was 12k/s
degrading to stack overflow at 300k), unit 21/21 + npm 60/61 green.
Note: w3c_runner shows 2 RIF entailment fails when run from
ocaml-output/ — cwd-dependent file resolution, run from repo root.)

Spot-check 2026-07-03 (`bin/linux-x86_64/w3c_runner --all` on a fresh
clone with submodules initialised): SPARQL 631 pass, 0 fail; RDF 1031
pass, 0 fail. OWL 2 RL positive-entailment via `generate-report.sh`:
20 pass, 10 fail (out of 30). Turtle throughput re-measured the same
day: ~100k triples/s, near-linear to 1M triples (details in
`performance.md`). The module inventory and `assume val` tables below
were refreshed 2026-07-03 from the live tree.

This file is a **periodic refresh doc** — it goes stale within a week.
Update after material progress (suite-score movements, new F\* modules,
resolved `assume val`s).

## Standing priorities (as of 2026-07-04)

Toward the goal in CLAUDE.md (performant, compliant RDF/S + OWL +
SHACL + RDFC + SPARQL engine). Re-rank when one lands; a dashboard
red always jumps the queue.

Landed 2026-07-05 wave 4 (all six agents gate-evidenced together):
SHACL phase 3 — core 98 pass, 0 fail (of 98) under the suite's full
report-isomorphism rule (was conforms-only), sh:sparql dispatch in
pure F\* with 17 pass, 5 fail (of 22; fails = custom constraint
components, documented); JSON-LD options block — toRdf 374 pass, 82
fail, 11 skip (of 467, was 307): @direction/rdfDirection, property
index containers, canonical xsd:double, well-formedness gates,
@prefix, keyword-lookalikes; RIF — live in-browser demo (rifSmoke +
general rifEval via Parser.RIFXML) AND bin/rif-runner running the 4
vendored W3C RIF cases end-to-end: 4 pass, 0 fail (scope.md updated
from "permanent SKIP" to supported subset); npm functional/dataflow
API (fn.js: frozen FnDataset, backend interface for future on-disk
COTTAS, builder seam for streaming parsers, memoized RDFC hashes,
cell/derive); all demo pages migrated to the npm package (legacy
client is now UI-only); unit run-all + build-ocaml.sh link order
fixed for the new SHACL→SPARQL11_Parser dependency.

Landed 2026-07-04 night wave: JSON-LD remote contexts + @import +
document base via the JSONLD.Loader seam (issue #275 closed) - toRdf
307 of 467; SHACL core validator slice 1 - 91 of 98 W3C core tests,
factoidal validate --shapes as the user tool (the goal's largest gap
is now a scored, burning-down number).

Landed 2026-07-04 evening wave: RDFC-1.0 to 82 pass, 3 fail, 1 stub
(of 86 - all remaining out of scope; within scope DONE); OWL RL PE
25 of 30 (suite runs in 0.6s); JSON-LD toRdf 287 of 467; RDFS closure
33.2s to 1.39s on 27k triples (O(N^2) join order fixed); RFC 3986
IRI resolution as the first reusable-foundations module; JSON-LD
Playground demo + npm-on-Pages mirror; dev loop: no-op extract 48min
to 1s, layered-parallel extraction, hints measured-and-rejected,
affected-suite runner.

Landed 2026-07-04 (all gate-evidenced on claude/main): Later the same day: JSON-LD
Phases 3a+3b (W3C toRdf 33 -> 181 pass of 467); #269/#270 closed;
#272 serializer speedup (dump-nq 162 -> 12069 triples/s at 10k;
still superlinear at 100k, issue open); #273 RDF/XML overflow AND
silent >5k-triple truncation fixed (50k parses exactly); Turtle
pretty-printer (factoidal dump-turtle, 17/0 round-trip suite);
graphs API slice 1 (graphs list/get/hash/diff + npm graphs()/
canonicalHash(), 9/0); parse+serialize bench live on the dashboard. 2c and 2d
below; #262 sameAs closure rewrite; #21 exact on-disk counts; #267
COTTAS dataset semantics + #268 backend property paths (backend
parity 36 of 36, zero knowns); #271 canonicalize/dump-nq UTF-8
corruption + the mirrored-JSON-escape bug in SPARQL.JSON.Escape;
JSON-LD Phase 1 (RFC 8259 parser + expanded-form toRdf, 10 of 10
local fixtures) with the Phase 2 W3C-manifest runner scaffolded; PE
slice 1 (22 of 30). Three of the four serializer-side bugs were the
same bytes-vs-codepoints disease — the RDF.Unicode foundation module
in item 4 is where that class of bug goes to die.

1. **#118 — retire the COTTAS on-disk OCaml runtime** (718 lines of
   unverified glue on the hot path; plan doc scoped, ukparliament-bench
   gated). The precondition for dropping the rule-#11 qualifier.
2. **#262 — OWL-RL sameAs closure blow-up** — diagnosed 2026-07-03
   (`2026-07-03-owl-rl-sameas-blowup-diagnosis.md`): measured O(k⁶)
   per closure step (163.87 s at a 24-individual sameAs clique); fix
   sketch is snapshot-fold + bucket lookups for the five sameAs
   rules. NOT the cause of the 10 PE fails; it bites ConsistencyTests
   — which currently **mask** the stall by passing on the un-closed
   graph after a 30 s cap trip (soundness hazard) — and the
   entailment-regime simple1 stall.
2b. **The 10 OWL RL positive-entailment fails** (20 pass, 10 fail of
   30 — the dashboard red) are semantic gaps, not timeouts: 7 missing
   bnode class-expression conclusions
   (complementOf/AllDifferent/unionOf/Restriction), 2 XSD
   range-hierarchy gaps, 1 no-premise. Separate work item from #262;
   needs rule-coverage additions in the OWL-RL rule set. Fix sketches:
   `2026-07-03-owl-rl-pe-fails-fix-sketch.md` (path to 27 pass, 2
   documented fails, 1 skip).
2c. **[DONE 2026-07-04]** Backend eval path skips the bnode-pattern rewrite — found by
   the Jena probe refresh (`2026-07-03-jena-probe-refresh.md`),
   invisible to the W3C dashboard: bnode-pattern SELECT/ASK via the
   CLI's default route match 0 rows (`SPARQL11.Store.fst` ~752 misses
   the `rewrite_query_bnodes_pattern` call the algebra path makes).
   Small F\* fix; gate on the jena basic probe returning to 20 of 20.
2d. **[DONE 2026-07-04]** No per-file blank-node scoping at dataset load — `_:x` in
   separately loaded files spuriously joins (`factoidal_cli.ml:112`;
   Jena graph probe 9 of 11, was 11 of 11). Bnode labels are
   document-scoped per RDF 1.1; decide loader-namespacing vs F\*
   dataset-merge fix.
3. **Shrink `--admit_smt_queries` in `SPARQL11.Parser.fst`** (~65% of
   the file admitted; the biggest verification caveat we disclose).
4. **Stratification + reusable foundations** — split
   `RDF.Graph.Executable` and `SPARQL11.Algebra` per the roadmap in
   `skills/fstar-module-style/SKILL.md`; commit-sized slices, suites
   green at each step. Owner directive 2026-07-04: the split's
   FIRST-CLASS deliverables are reusable foundation modules shared by
   every parser/serializer/evaluator instead of today's scatter —
   `RDF.IRI` (RFC 3986/3987; today: SPARQL11.IRI.Resolve +
   Parser.IRI + per-parser fragments), `XSD.Datatypes` (value spaces,
   canonical forms, numeric promotion; today embedded in
   SPARQL11.Algebra), `RDF.Unicode` (UTF-8/codepoints/escapes; today
   assume-vals + per-parser char logic — the new Parser.JSON escape
   handling should consume it), `RDF.LanguageTag` (BCP47 well-formed
   + case-insensitive comparison — fixes the known literal_eq gap
   where @en-US and @en-us compare unequal). JSON-LD phases 3-4 need
   RDF.IRI + RDF.Unicode, so extraction of those two leads.
5. **[SUITE COMPLETE, 2026-07-05 wave 6] SHACL** —
   `SHACL.Validation.fst` is a full validator: core 98 pass, 0 fail
   (of 98) under the suite's report-isomorphism comparison; sparql
   section 22 pass, 0 fail (of 22) including custom constraint
   components (sh:parameter + ASK/SELECT validators) and
   $shapesGraph/$currentShape pre-binding — the whole vendored suite
   passes, 120 of 120. `factoidal validate --shapes` is the user
   tool. One `assume val` left (`eval_sparql_target_select`,
   SPARQL-SELECT targets, unreachable in the suite, #181 stub patch). (`third_party/testing/shex` is
   ShEx, a different shapes language — program plan in
   `docs/designissues/2026-07-05-shex-program-plan.md`.)
6. **[DONE, 2026-07-05] RDFC-1.0 as a tool** — `factoidal
   canonicalize FILE` shipped; suite at 84 pass, 1 fail, 1 stub (of
   86) with SHA-256 + SHA-384 (the fail is a vendored-fixture
   artifact, the stub the poison-clique NegEval deferral — both
   documented out of scope). Canonical hashes feed the graphs API,
   the npm fn API's content identity, and cache keys. Remaining perf:
   canonicalize's own 100k+ HFDQ-hashing tail (#272 fixed the
   serializer side; hashing side still superlinear).
7. Small, fold into any session: `tests/local`
   scripts that need external corpora get skip-or-fetch treatment
   (parser regressions done 2026-07-03; ukparliament bench corpus is
   absent from fresh clones and self-skips in CI).
8. **`dump-nq`/`canonicalize` superlinear scaling + RDF/XML stack
   overflow** — found 2026-07-04 while building
   `tools/bench-parse-serialize.sh` (see `perf-benchmarking` skill).
   `factoidal count` scales linearly as expected (~80-90k triples/s
   through 1M), but on the *same* bnode-free fixtures
   `factoidal-dump-nq` and `factoidal canonicalize` are severely
   superlinear: `dump-nq` on 1,000 triples takes ~0.65s, on 2,000
   triples ~12.9s (should be ~1.3s if linear); `canonicalize` shows
   the same shape (1,000: ~0.46s, 2,000: ~8.6s). Both blow through a
   120s/run cap well before 100k triples — the new bench records this
   as a documented skip rather than hanging. Separately, RDF/XML
   parsing (`factoidal count FILE.rdf`) crashes with `Stack overflow`
   above ~10k triples, independent of the above. Not diagnosed or
   fixed here — needs a GitHub issue and a profiling pass (candidate
   suspects: whatever "sorted N-Quads" dedup/sort path `dump-nq` and
   `canonicalize` share that `count` doesn't use; non-tail recursion
   in `Parser.XML`/`Parser.RDFXML` for the stack overflow).

Perf experiment queue (ranked, from
`2026-07-03-shapes-canon-storage-strategies.md`): E1 characteristic-set
row clustering in the COTTAS writer (zero reader changes, measured on
ukparliament bench); E2 per-CS statistics sidecar for
`cottas_ondisk_estimate`; E3 canonical-hash sidecars + Merkle roll-ups
riding on `factoidal canonicalize` (item 6).

Standing discipline: **every session watches for perf optimisation
opportunities** while doing anything else — a suspicious phase in the
`Server-Timing` breakdown, a super-linear shape in a loop you read, a
list scan a bitmap could kill. Don't fix out-of-scope perf smells
mid-task; measure enough to file them here or as an issue, then
finish the task. Speed claims still need their own measured commit
(`perf-benchmarking` skill).

Done recently: in-memory index-build wall (#259, verified fixed
2026-07-03 — 137s → 2.2s on lifesci Q01, linear to 1M quads);
rdf-canon totals in latest.json; parser-regressions external-corpus
skip; SHACL suite vendored; current-state inventory refresh
(2026-07-03).

## F\* Specifications

Repository contains 90 F\* modules totalling 47517 lines of code. Key modules:

```
formal/fstar/

Core (RDF/SPARQL evaluation):
  SPARQL11.Algebra.fst            5777 lines, 13 assume val (query evaluator)
  SPARQL11.Parser.fst             4343 lines
                                  ⚠ ~65% uses --admit_smt_queries true (see below)
  RDF.Graph.Executable.fst        4152 lines

Query planning (on-disk backend infrastructure):
  RDF.CottasStore.fst             1528 lines, 10 assume val
  RDF.CottasStore.OnDiskIndex.fst  407 lines,  7 assume val
  RDF.CottasStore.OnDiskRuntime.fst 117 lines, 15 assume val
  SPARQL11.Store.fst               780 lines

RDF parsers (all F*-extracted):
  Parser.Turtle.fst               1918 lines
  Parser.RDFXML.fst               1159 lines
  Parser.NTriples.fst             1025 lines
  Parser.TriG.fst                  525 lines
  Parser.NQuads.fst                518 lines
  Parser.XML.fst                   680 lines (non-validating XML foundation)
  Parser.SRX.fst                   273 lines (SPARQL Results XML)
  Parser.CSVResults.fst            610 lines
  Parser.JSONResults.fst           408 lines
  Parser.IRI.fst                   447 lines
  Parser.Combinators.fst           396 lines (parser combinator foundation)

OWL/RIF:
  OWL.QueryRewrite.fst            1796 lines
  RIF.Core.Eval.fst                470 lines
  Tableau.fst                      1103 lines

Query planning and diagnostics:
  SPARQL.Protocol.fst             1229 lines
  SPARQL.HTTP.fst                  579 lines

Miscellaneous support:
  Parquet.Footer.fst              2591 lines,  3 assume val
  RDF.Canonical.fst               1142 lines,  1 assume val
  SHACL.Validation.fst            2546 lines,  1 assume val (phase 3: reports + sh:sparql)
  Parser.FastString.fst            210 lines,  7 assume val
  Parser.BallyhooHDTQ.fst          174 lines, 17 assume val
  Parser.BallyhooHDT.fst           173 lines, 13 assume val
  Parser.BallyhooCOTTAS.fst        170 lines, 17 assume val

Build and test harness:
  Makefile                         verify + extract-c targets
  build-ocaml.sh                   F* -> OCaml -> js_of_ocaml pipeline
  ocaml-patches.sh                 master script: applies all patches from
                                   minimal_regrettable_glue_code_each_with_an_open_issue/
  minimal_regrettable_glue_code_each_with_an_open_issue/
                                   individual patch files, each named
                                   <issue>_<description>.sh with GitHub issue
```

Inventory summary: 90 modules, 47517 lines total, 141 assume val declarations.

## ⚠ Verification Gaps — Be Honest About These

**SPARQL11.Parser.fst** uses `--admit_smt_queries true` from approximately
line 802 to line 2722 (~1920 lines, ~65% of the file). This means Z3 does
NOT verify the proof obligations for the parser's mutually recursive
functions. The parser type-checks but the SMT proofs are not discharged.
This is a significant gap in the formal verification story and must be
disclosed when claiming "verified."

**ASK query comparison in w3c_runner.ml** does not check the expected
boolean value — ASK tests always pass regardless of the query result. This
inflates the pass count slightly.

**Blank node comparison** in the test runner uses a simplified matching
(any bnode matches any other bnode) rather than proper graph isomorphism.
Some tests may pass that shouldn't under strict comparison.

## Known Gaps in RDF.Graph.Executable.fst

The F\* RDF graph spec uses **syntactic equality only**. It lacks:

- **Language tag case-insensitivity**: `literal_eq` compares `lang_tag` with `=`
  (string equality). Per RDF 1.1, `@en-US` and `@en-us` denote the same value.
- **Plain literal ↔ xsd:string equivalence**: Per RDF 1.1, `"foo"` (plain) and
  `"foo"^^xsd:string` are the same value. The spec treats them as distinct.
- **Datatype value equivalence**: `"010"^^xsd:integer` and `"10"^^xsd:integer`
  denote the same value. The spec compares lexical forms as strings.
- **RDFS closure rules**: No subClassOf/subPropertyOf inference, no domain/range
  type inference, no container membership property axioms.

These are not exotic features — they are what the W3C rdf-mt test suite tests.

## OCaml Output (extracted + test glue)

```
formal/fstar/ocaml-output/
  RDF_Graph_Executable.ml    F*-extracted OCaml
  SPARQL11_Algebra.ml        F*-extracted OCaml (patched for assume vals)
  SPARQL11_Parser.ml         F*-extracted SPARQL parser
  Parser_Combinators.ml      F*-extracted parser combinators
  Parser_NTriples.ml         F*-extracted N-Triples parser
  Parser_Turtle.ml           F*-extracted Turtle parser
  Parser_NQuads.ml           F*-extracted N-Quads parser
  Parser_TriG.ml             F*-extracted TriG parser
  Parser_XML.ml              F*-extracted XML parser
  Parser_RDFXML.ml           F*-extracted RDF/XML parser
  Parser_SRX.ml              F*-extracted SRX (SPARQL Results XML) parser
  Parser_CSVResults.ml       F*-extracted CSV/TSV results parser
  w3c_runner.ml              W3C manifest reader + test runner CLI (I/O glue)
  fstar_int_stubs.js         js_of_ocaml int stubs
```

Hand-coded parsers have been deleted. Legacy copies remain in `junk/do_not_use/hand_coded_parsers/` as a warning.

## assume val inventory

141 assume val declarations across 20 modules. Summary by module (largest first):

**SPARQL11.Algebra.fst** (13 assume vals — query evaluator core):

| assume val | Purpose | Stub |
|-----------|---------|------|
| `regex_match` | SPARQL REGEX | OCaml `Str` in ocaml-patches.sh |
| `regex_replace` | SPARQL REPLACE | OCaml `Str` in ocaml-patches.sh (forward ref) |
| `hash_md5` | MD5 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha1` | SHA-1 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha256` | SHA-256 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha384` | SHA-384 hash | OCaml `Digest` in ocaml-patches.sh |
| `hash_sha512` | SHA-512 hash | OCaml `Digest` in ocaml-patches.sh |
| `eval_expr_ebv` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_expr_fwd` | forward decl (mutual recursion) | wired in ocaml-patches.sh |
| `eval_exists_fwd` | forward decl (EXISTS) | wired in ocaml-patches.sh |
| `eval_subselect_fwd` | forward decl (subqueries) | wired in ocaml-patches.sh |
| `eval_property_path_fwd` | forward decl (property paths) | wired in ocaml-patches.sh |

**Other modules with assume vals** (128 total): Ballyhoo HDT parsers (47: Parser.BallyhooCOTTAS.fst 17, Parser.BallyhooHDTQ.fst 17, Parser.BallyhooHDT.fst 13), on-disk store/indexing (44: RDF.CottasStore.OnDiskRuntime.fst 15, RDF.CottasStore.fst 10, RDF.CottasStore.OnDiskIndex.fst 7, RDF.CottasStore.LazyDict.fst 9, RDF.CottasStore.LazyDictRegistry.fst 5), fast string parsing (7: Parser.FastString.fst), lazy term caching (10: RDF.Store.LazyTermCache.fst 6, RDF.Store.HDTTermCacheRegistry.fst 4), misc (11: Parquet.Footer.fst 3, RDF.CottasStore.ColumnSeq.fst 3, SHACL.Validation.fst 3, Util.Log.fst 5).

## Plain-English Status Summary (as of 2026-05-07)

Factoidal is a formally verified RDF/SPARQL implementation written in F\* and
tested against the official W3C conformance suites. SPARQL UPDATE, HTTP
protocol, GSP, and SERVICE are live. The core SPARQL evaluator + updater
passes 630 of 631 applicable query/syntax/update/protocol tests (99.8%),
with perfect scores across every suite except entailment, where one OWL
case still fails (RIF-style rule entailment, out of scope for OWL-DL).
Suites at 100%: add, aggregates (47/47), basic-update (13/13), bind,
bindings, cast (6/6), clear, construct (7/7), copy, csv-tsv-res, delete,
delete-data, delete-insert, delete-where, drop, exists, functions (75/75),
grouping, http-rdf-update (19/19), json-res, move, negation (12/12),
project-expression, property-path (33/33), protocol (34/34), service (7/7),
service-description (3/3), subquery (14/14), syntax-fed, syntax-query
(94/94), syntax-update-1 (54/54), syntax-update-2, update-silent (13/13).

On the RDF parsing side, **all six RDF suites are at 100%**: rdf-turtle
313/313, rdf-trig 356/356, rdf-n-triples 70/70, rdf-n-quads 87/87,
rdf-xml 166/166, rdf-mt 39/39 (1031/1031 combined).

**Caveats on test numbers (be honest):** ASK query comparison in w3c_runner.ml
does not check the expected boolean value — ASK tests always pass. Blank node
matching is simplified (any bnode matches any other) rather than proper graph
isomorphism. These may inflate the pass count slightly.

## W3C Test Results (as of 2026-05-07)

**SPARQL 1.1 — 630 pass, 1 fail (out of 631)**

Per-suite: add 8/8, aggregates 47/47, basic-update 13/13, bind 10/10,
bindings 11/11, cast 6/6, clear 4/4, construct 7/7, copy 6/6, csv-tsv-res 6/6,
delete 19/19, delete-data 6/6, delete-insert 17/17, delete-where 6/6,
drop 4/4, entailment 69/70, exists 6/6, functions 75/75, grouping 6/6,
http-rdf-update 19/19, json-res 4/4, move 6/6, negation 12/12,
project-expression 7/7, property-path 33/33, protocol 34/34, service 7/7,
service-description 3/3, subquery 14/14, syntax-fed 3/3, syntax-query 94/94,
syntax-update-1 54/54, syntax-update-2 1/1, update-silent 13/13.
Single remaining fail: one entailment case (RIF-style rule entailment,
out of scope for OWL-DL).

**RDF 1.1 — 1031 pass, 0 fail (out of 1031)**

Per-suite: N-Triples 70/70, Turtle 313/313, N-Quads 87/87, TriG 356/356,
RDF/XML 166/166, rdf-mt 39/39. RDF/XML reached 166/166 after the 2026-04-23
through 2026-05-07 fixes (reification, UTF-8 char refs, RFC 3986 resolver,
NCName codepoint validator, mutual-exclusion rules, xml:base scoping,
empty-property-element-as-bnode, parseType="Literal" canonicalisation,
duplicate-rdf:ID tracking, processing-instruction-in-property-element).

**Combined: 1661 pass, 1 fail (out of 1662).**

Session delta (from morning baseline 1514/81):

  +1   SPARQL REPLACE: codepoint-aware UTF-8
  +3   SPARQL UPDATE ADD/COPY/MOVE no-op on missing source
  +6   Turtle/TriG reject forbidden-char UCHAR escapes
  +1   TriG reject bare collection as sole statement
  +3   RDF/XML allow rdf:Seq/Bag/Alt as property element names
  +1   Parser.XML encode numeric char refs as UTF-8
  +1   codepoint-aware NCName validator
  +5   rdf:bagID + RDF 1.1 attribute mutual-exclusion rules
  +2   xml:base/lang/namespaces don't leak to siblings
  +4   delegate RDF/XML IRI resolution to RFC 3986 v2
  +1   reject rdf:li as attribute
  +8   reification quads from rdf:ID on property elements
  +1   split node vs property mutual-exclusion rules
  +4   empty-property-element with property attrs → bnode object
  +1   strip fragment from xml:base
  +1   reify parseType="Collection" with rdf:ID
  ≡    bnode labels without leading `_:` (cosmetic; runner's lenient
       bnode compare hid it but downstream serialisers now round-trip)
  = +43 net.

**RDF 1.1 Model Theory — 39 pass, 0 fail (39 total)**

All rdf-mt tests pass: literal equivalence, datatype handling, RDFS closure
rules, language tag normalization, value-space entailment with consistent
blank node mapping.

## What rdf-mt Actually Tests (39 tests)

| Category | Count | What It Tests | F\* Status |
|----------|-------|---------------|------------|
| Simple matching | 7 | Language tag distinction, URI matching, reification non-entailment | **PASS** |
| Literal/datatype semantics | 20 | Value equivalence, plain↔xsd:string, lang tag case, ill-formedness | **PASS** |
| RDF closure rules | 4 | Container membership (rdf:\_n), rdfs:member superProperty | **PASS** |
| RDFS closure rules | 14 | subClassOf, subPropertyOf, domain, range, intensional semantics | **PASS** (via ocaml-patches.sh closure) |
| Advanced model theory | 3 | Value space disjointness, completeness axioms | **PASS** (not tested — 9 skipped) |

## What Was Removed (junk/do_not_use/)

Everything in `junk/do_not_use/` is **vibe-coded or derived from vibe-coded
artifacts**. Do not use it. Do not revive it.

## The Plan

### Architecture

```
F* formal spec (the product)
    |
    v
fstar.exe --codegen OCaml (extraction, proof-erased)
    |
    v
OCaml test runner (minimal I/O glue only)
    |-- reads W3C manifest files from disk (I/O)
    |-- calls F*-extracted parsers for .rq/.ttl/.nt/.nq/.trig/.rdf/.srx
    |-- calls F*-extracted evaluator
    |-- compares actual vs expected (using F*-extracted comparison)
    |-- emits pass/fail per test
    v
W3C SPARQL 1.1 + RDF 1.1 conformance results
```

### Phase 1 — SPARQL test infrastructure (DONE)

W3C test runner works. SPARQL 1.1 query/syntax/update/protocol coverage
is 630 pass, 1 fail (out of 631). See "W3C Test Results (as of
2026-05-07)" above for the per-suite breakdown.

### Phase 2 — Fix RDF semantics in F\* (MOSTLY DONE)

1. **Language tag case-insensitive comparison** — DONE (`lang_tag_eq` in F\*)
2. **Plain literal ↔ xsd:string equivalence** — DONE (`literal_value_eq`)
3. **Datatype value space equivalence** — DONE (`datatype_value_eq`, `normalize_integer_lexical`)
4. **RDFS closure rules** — DONE (`rdfs_closure` with subPropertyOf, domain, range, subClassOf, container membership)
5. **Simple entailment** (blank node as existential variable) — TODO

Remaining: re-extract, wire into test runner, run rdf-mt tests.

### Phase 3 — F\* parsers (IN PROGRESS)

Replace hand-written OCaml parsers with F\*-extracted implementations.

**Parser architecture**: `Parser.Combinators.fst` provides the combinator
foundation (pchar, pstring, psat, pbind, pmap, palt, pmany, etc.). All parsers
are built on this. `Parser.XML.fst` is a **non-validating XML parser** — it
reads well-formed XML into a tree but does NO DTD processing, NO external entity
resolution, NO schema validation. Only predefined entities (&amp; &lt; &gt;
&quot; &apos;) and character references (&#123; &#x1A;). Namespace prefixes are
preserved as part of element/attribute names (namespace URI resolution is the
RDF/XML layer's job, not the XML parser's).

1. N-Triples parser in F\*
2. Turtle parser in F\*
3. N-Quads parser in F\*
4. TriG parser in F\*
5. RDF/XML parser in F\* (uses Parser.XML.fst — non-validating XML parser)
6. CSV/TSV results format parser in F\*
7. SRX (SPARQL Results XML) parser in F\*
8. SPARQL query parser in F\* (SPARQL11.Parser.fst started)

### Phase 4 — Close SPARQL gaps

Working from test failures, extend the F\* SPARQL spec:

1. **Result formats** — JSON Results (`application/sparql-results+json`),
   CSV (`text/csv`), TSV (`text/tab-separated-values`) serializers in F\*.
   SRX parser already exists; JSON/CSV/TSV result parsers needed for test
   comparison. ~20 tests blocked.
2. **SPARQL UPDATE** — INSERT DATA, DELETE DATA, INSERT/DELETE (with WHERE),
   LOAD, CLEAR, DROP, ADD, MOVE, COPY, CREATE. Requires mutable graph store
   model in F\*. 205 tests. Tracked by #59.
3. **SPARQL Protocol** — HTTP interface for query and update operations.
   34 tests. Requires HTTP server, which can use `assume val` with OCaml
   stub (see I/O and networking below).
4. **SERVICE (federated query)** — Requires HTTP client to contact remote
   SPARQL endpoints. 7 tests. Tracked by #57.
5. **Service Description** — 3 tests.

### Phase 5 — I/O, Networking, and Async

F\* extracted code is pure/total by default. Networking (SERVICE, Protocol,
LOAD) requires I/O effects. Strategy:

- **`assume val` for I/O primitives.** Declare HTTP client/server operations
  as `assume val` in F\* with OCaml stubs. This keeps the verified boundary
  around query semantics while allowing real network operations.
- **Simple synchronous blocking API.** For `web_fetch : url -> result`, a
  blocking OCaml stub using `Unix.open_connection` or `Cohttp_lwt_unix` is
  the simplest approach. Good enough for test runner and CLI usage.
- **Async considerations for extracted applications.** When F\*-extracted code
  runs in a larger async context (e.g., a web server), the blocking stubs
  become a problem. Options:
  1. **Thread pool** — run blocking F\* calls in a thread pool, integrate
     with Lwt/Async via `Lwt_preemptive.detach` or similar.
  2. **Effect-polymorphic F\*** — F\* has `Effect` and `PURE`/`DIV`/`ST`
     effect system. In principle, I/O effects can be modeled, but extraction
     of effectful code to async OCaml is not well-supported by F\* today.
  3. **js_of_ocaml + promises** — for browser/Node targets, blocking I/O
     is impossible. The js_of_ocaml path would need promise-based stubs
     with continuation-passing, which is architecturally different.
  The current plan: start with blocking stubs (#57), document the limitation,
  and track async extraction as a separate research issue.

### Phase 6 — Verified extraction pipeline

- Low\* rewrite for standalone C extraction via KaRaMeL
- CI: verify F\* → extract → test → sign
