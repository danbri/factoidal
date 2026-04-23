# Near-perfect W3C fails — root-cause survey (2026-04-23)

Background: 8 suites sit at 1–3 fails out of otherwise 100%. The 15
failing tests across those suites are in effect the "short leg" of
our conformance story. This survey asks: do they share root causes?
Can we clear multiple tests with one principled fix?

Subagent pass, read-only. Ordered roughly top-to-bottom from safest
and highest-value to highest-risk. User instruction: "fix them all
but do not do it for the PASSes, do it for the underlying health of
our codebase."

## Bucket 1 — CONSTRUCT template duplication (3 tests, 1 commit)

`SPARQL11.Parser.fst : collect_template_triples (~line 2615)` flattens
a BGP-shaped pattern tree for CONSTRUCT templates. When the parser
represents comma-separated templates as `GP_Join (GP_BGP [a], GP_BGP
[b])` vs a single `GP_BGP [a; b]`, the collection logic can produce
duplicate template patterns, causing too many triples at eval time.

Tests: `constructwhere02` (expected 2 got 4), `constructwhere03`
(expected 2 got 8), `constructwhere04` (expected 4 got 0 — converse
case where the collection returns too few or empty).

Risk: Medium. Touches every CONSTRUCT query. Need regression
testing against constructwhere05/06 + `CONSTRUCT list` + sq12
(all currently passing).

## Bucket 2 — XSD numeric lexical canonicalisation (2 tests, 1-2 commits)

`SPARQL11.Algebra.fst : xsd_cast (~line 3693–3802)` preserves input
lexical forms verbatim. `"0E1"^^xsd:float` stays as `"0E1"`; test
expects canonical `"0.0"`. Same applies to xsd:decimal lexical forms
("33.3300" should canonicalise to "33.33").

Cross-cutting smell: `ER_Dbl` / `ER_Dec` / `ER_Num` treat literals as
opaque strings. Every cast, compare, or serialise site risks a
non-canonical form. A single `canonicalize_numeric_literal` applied
at parse time (when a literal is first minted) would prevent
cascading bugs.

Tests: `xsd:float cast`, `xsd:decimal cast`.

Risk: Low-Medium. Local to numeric casts + output serialisation.

## Bucket 3 — GRAPH + aggregate / VALUES cross-context (3 tests, 2-3 commits, **highest risk**)

Three tests fail when a sub-query with GROUP BY, a VALUES clause, or
an INSERT DATA crosses the GRAPH { … } boundary:

- aggregates: "COUNT: no GROUP BY inside of GRAPH"
- bindings: "VALUES inside GRAPH binding the same variable as the graph name"
- basic-update: "INSERT same bnode twice" + "INSERTing the same bnode with INSERT DATA into two different Graphs is the same bnode"

Diagnosis: `SPARQL11.Algebra.fst : eval_pattern_store (~line 1945–1975)`
threads graph context through nested evaluation but doesn't cleanly
separate graph bindings from outer solution variable bindings.
Subqueries inside `GP_Graph` lose variable mappings on their way
back to the outer scope.

Cross-cutting smell flagged as "graph store context threading is
fragile". Any sub-query / aggregate / VALUES / INSERT-DATA site
inside GRAPH is at risk.

Risk: **High** — graph algebra is load-bearing. This is the bucket
most likely to cause regressions if fixed carelessly.
Recommended: save for last.

## Bucket 4 — Duplicate rdf:ID validation (1 test, 1 commit, add-only)

`Parser.RDFXML.fst : ~line 419–430` resolves `rdf:ID="foo"` against
the base IRI without checking whether that ID has already been used
in this document. Per RDF/XML §7.2.10 this is a syntax error.

Fix: thread `seen_ids : list string` through `rdfxml_state`; in
`determine_subject`, reject if the resolved ID matches a prior one.
`rdfms-difference-between-ID-and-about-error1` exercises exactly
this.

Risk: Low. Add-only validation; no existing passes flip.

## Bucket 5 — parseType="Literal" XML canonicalisation (2 tests, 1 commit)

`Parser.XML.fst : serialize_xml_node (~line 358–400)` reproduces XML
content byte-for-byte but doesn't canonicalise per XML-C14N:
namespace declarations, attribute ordering, whitespace all may
differ. `xml-canon-test001/002` compare against the C14N form.

Risk: Low-Medium. XML serialisation is localised; not used for RDF
semantics beyond `parseType="Literal"` bodies.

## Bucket 6 — rdf:li / container bnode identity (2 tests, 1 commit)

`Parser.RDFXML.fst : process_collection (~line 655–664)` emits the
right *number* of triples for `rdf:Bag/Seq/Alt` but bnode identity
or `rdf:_N` numbering diverges from expected on
`rdf-containers-syntax-vs-schema-test004/007`.

Risk: Low. Container path only.

## Bucket 7 — MINUS / NOT-EXISTS semantics (1 test, 1 commit)

`SPARQL11.Algebra.fst : minus (~line 1925–1926)` + `sm_compatible
(~lines 99–107)`: the MINUS operator is under-filtering solutions.
`subset-02.rq` expects 11, we produce 30 — almost 3× — suggesting
the compatibility check is too loose or variable-domain awareness
is missing.

Negation-subsets test is the only MINUS failure. Fix is self-contained.

Risk: Medium. Logic error in set operation.

## Bucket 8 — CONSTRUCT + sub-SELECT + LIMIT (1 test, 1 commit)

`eval_construct_query (~line 3331-3346)` applies LIMIT at the outer
level. `sq14` uses a sub-SELECT with its own LIMIT that should
restrict template solutions; we're producing 14 triples instead
of 11.

Risk: Low. CONSTRUCT-local.

## Cross-cutting code smells

These recur across multiple buckets:

1. **Graph-context threading is fragile** (Bucket 3). Every
   sub-pattern evaluation inside GRAPH risks dropping or aliasing
   variable bindings. Worth a refactor of `eval_pattern_store` to
   explicitly pass a separated graph-context parameter.

2. **Template collection flattens pattern structure** (Bucket 1).
   Parser/algebra mismatch per anti-pattern #7: the collection
   doesn't round-trip the tree shape the parser produced.

3. **Numeric lexical forms never normalised** (Bucket 2).
   `canonicalize_numeric_literal` applied at literal-creation time
   (both parser and cast output) would close a whole class of bugs
   preemptively.

4. **Blank node identity relies on string names** (Buckets 3 & 6).
   Pattern bnode `b1` becomes `tpl_0_b1` at instantiation, but
   `sm_bind_if_compatible` uses `rdf_term_eq` (syntactic equality).
   Any scheme that renames bnodes risks silent breakage.

5. **Solution-mapping compatibility doesn't check bnode
   identity** (Bucket 3). `sm_compatible` agrees on overlapping
   variables but doesn't verify that shared bnodes across solutions
   remain the same bnode.

## Recommended attack order

1. Bucket 1 (CONSTRUCT template dup) — 3 tests, safest, highest ROI
2. Bucket 4 (duplicate rdf:ID) — 1 test, add-only
3. Bucket 2 (numeric canonicalisation) — 2 tests, contained
4. Bucket 7 (MINUS semantics) — 1 test, contained
5. Bucket 8 (CONSTRUCT sub-SELECT LIMIT) — 1 test, contained
6. Bucket 5 (parseType=Literal C14N) — 2 tests, contained
7. Bucket 6 (container bnode identity) — 2 tests, contained
8. Bucket 3 (GRAPH context refactor) — 3 tests, **save for last**

Total projected: ~13 tests, 10–12 commits, 3–4 days with heavy
regression checking between buckets.

One-offs: none — every failure fits into a bucket.

## Source

Subagent report 2026-04-23 late session.
