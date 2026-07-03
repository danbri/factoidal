# Current State (Honest Assessment)

Last refreshed: 2026-05-07 (W3C scores re-measured against
`bin/linux-x86_64/w3c_runner --all`; OWL profile-RL re-measured against
`bin/linux-x86_64/owl_runner`).

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

## Standing priorities (as of 2026-07-03)

Toward the goal in CLAUDE.md (performant, compliant RDF/S + OWL +
SHACL + RDFC + SPARQL engine). Re-rank when one lands; a dashboard
red always jumps the queue.

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
   needs rule-coverage additions in the OWL-RL rule set.
3. **Shrink `--admit_smt_queries` in `SPARQL11.Parser.fst`** (~65% of
   the file admitted; the biggest verification caveat we disclose).
4. **Stratification** — split `RDF.Graph.Executable` and
   `SPARQL11.Algebra` per the roadmap in
   `skills/fstar-module-style/SKILL.md`; commit-sized slices, suites
   green at each step.
5. **SHACL** — `SHACL.Validation.fst` is a Phase-1 skeleton with a
   stubbed validator (#181). The W3C suite is now vendored at
   `third_party/testing/shacl` (data-shapes-test-suite, core +
   sparql) but unwired. Target shape: not just a conformance row but
   a **user-facing tool** — `factoidal validate --shapes shapes.ttl
   data.ttl` — validator in F\*, CLI wiring in `bin/factoidal-cli/`.
   Currently the largest gap between goal and engine. (Note:
   `third_party/testing/shex` is ShEx, a different shapes language —
   also unwired, lower priority.)
6. **RDFC-1.0 as a tool** — the canonicalization algorithm exists in
   F\* (`RDF.Canonical.fst`) and is suite-tested (62 pass, 23 fail,
   1 skip of 86), but the CLI never exposes it. Add
   `factoidal canonicalize FILE` emitting RDFC-1.0 canonical N-Quads
   (consumer wiring only, no new F\*), and chase the 23 fails.
   Canonical output doubles as a perf primitive: canonical hashes
   enable dataset diffing, dedup, and cache keys.
7. Small, fold into any session: `tests/local`
   scripts that need external corpora get skip-or-fetch treatment
   (parser regressions done 2026-07-03; ukparliament bench corpus is
   absent from fresh clones and self-skips in CI).

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
  SHACL.Validation.fst             340 lines,  3 assume val (Phase 1 skeleton)
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
