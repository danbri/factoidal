# Lean 4 vs F\*: feature parity, measured

Owner question, 2026-08-22: "How close is our L4 version to working
feature parity with the F\* codebase?"

Everything below is MEASURED in this session unless the row says
otherwise. F\* numbers come from `docs/test-results/latest.json`; Lean
numbers come from building `l4w3c` and the probes and running them
against the same W3C manifests on disk.

## Headline

**The Lean tree is at or near parity on the RDF + SPARQL + JSON-LD
core, and absent on the periphery and the storage/serving layers.**
The single most useful number: on the full SPARQL 1.1 manifest the
Lean engine scores **601 pass, 0 fail, 30 unsupported (out of 631)**
against F\*'s 631 pass, 0 fail — and **all 30 unsupported are
entailment-regime tests** (OWL-Direct, OWL-RDF-Based, RIF), not core
SPARQL. Zero failures on either side.

## At parity (measured this session)

| Suite | F\* | Lean 4 |
|---|---|---|
| SPARQL 1.1, non-entailment-regime | 631 pass, 0 fail (of 631) | 601 pass, 0 fail (of 601 attempted) |
| rdf-turtle | in rdf 1030 of 1031 | 313 pass, 0 fail (of 313) |
| rdf-trig | in rdf | 356 pass, 0 fail (of 356) |
| rdf-n-triples | in rdf | 70 pass, 0 fail (of 70) |
| rdf-n-quads | in rdf | 87 pass, 0 fail (of 87) |
| rdf-mt (RDF semantics) | in rdf | 39 pass, 0 fail (of 39) |
| JSON-LD toRdf | 467 pass, 0 fail (of 467) | 467 pass, 0 fail (of 467) |
| SHACL core / SPARQL | 98 / 22 | 98 / 22 (from PORT_NOTES, not re-run here) |

## Close, with known gaps (measured)

| Area | F\* | Lean 4 | Gap |
|---|---|---|---|
| RDF/XML | in rdf suite | 130 pass, 2 fail (of 132, eval-isomorphic) | 2 tests |
| SPARQL entailment regimes | supported | 30 unsupported | see below |

Re-measured 2026-08-23: `owl2_profile_ql` is 87 pass, 0 fail (of 87),
and the whole rdf manifest is 1031 pass, 0 fail (of 1031). The two
RDF/XML failures are `rdfms-xml-literal-namespaces` XMLLiteral
canonicalisation differences, reported as `notEqual` rather than as a
comparison that gave up.

## Suites the Lean tree now runs END TO END (measured 2026-08-23)

Each of these has a real conformance runner, not a reader-level probe:
the whole pipeline runs and the result is compared against the suite's
own expected output.

| Suite | Runner | Result |
|---|---|---|
| csv2rdf | `l4csvw-rdf` | **252 pass, 10 fail, 6 skip (of 270)** |
| csv2json | `l4csvw-json` | **253 pass, 9 fail, 6 skip (of 270)** |
| JSON Schema draft-07 | `l4jsonschema` | **726 pass, 0 fail (of 726 decided), 44 undetermined (of 770)** |
| Content MathML | `l4mathml` | **56 pass, 0 fail (of 56)** |

Both CSVW numbers include the 58 NEGATIVE tests, scored by the
validator: 58 pass, 0 fail on each. Each CSVW runner also cross-checks
the validator against every POSITIVE test's metadata and reports the
documents it wrongly rejects — currently 0. That number exists because
a negative score can otherwise be bought with rules that reject
everything, and nothing in the negative column would disagree.

The JSON Schema residue is NAMED rather than counted: every draft-07
assertion keyword is implemented, so the 44 undetermined are `$id`
base-URI resolution, not a missing keyword.

**Opened 2026-08-22, same day** (module set ported, W3C suites not yet
run against the Lean side — that needs harness wiring):

| Family | Lean modules |
|---|---|
| ShEx | `ShEx/Schema`, `Validation` (node constraints), `Shapes` (satisfaction with EXTRA/CLOSED) |
| RML | `RML/Mapping` (term maps, templates, IRI-vs-URI encoding) |
| RIF Core | `RIF/Core` (AST + bounded forward chaining) |
| JSON Schema | `JSONSchema/Validate` (three-valued, exact rationals) |
| Schematron | `Schematron/Validate` (assert/report inversion) |
| XPath | `XPath/Number` (IEEE specials + exact decimals) |
| HTTP serving | `HTTP/Server` (routing, negotiation, responses) |
| Storage | `Storage/Bytes` (VByte, CRCs, checksummed sections) |

The HTTP one closes the gap this ledger flagged against the project's
framing: the Lean tree HAD the protocol SEMANTICS (`SPARQL/Protocol`,
`GraphStore`, `ServiceDescription`) but not the server that speaks
them. It now has both.

## Absent from the Lean tree

Present in F\*, no Lean counterpart: XSLT, MathML, the XML conformance
corpus (1,447 of 2,585), the VC/DID stack beyond the Lean `VC/`
modules, and the COTTAS columnar store above the byte layer. Several
ported families are SLICES rather than complete — ShEx has no
reference recursion, RIF no builtins, XPath only the number type,
storage only the byte primitives, CSVW no date formats. Each states
its own scope in its module header.

## The 30 unsupported, characterised

All are SPARQL queries under an entailment regime the Lean engine does
not yet answer: OWL-Direct (about 20, including the `paper-sparqldl-*`
and `simple 1..8` families and the qualified-cardinality parent/child
queries), OWL-RDF-Based (about 6), and RIF (4). None is a core SPARQL
feature.

This is the same target the Lean OWL tableau ladder is walking toward
(https://github.com/danbri/factoidal/issues/466): three rungs landed —
base clash calculus, ∃-witness, role box — with the ≤-rule witness
merge and qualified cardinality still to come. When the tableau can
decide these concept forms, the regime tests become answerable rather
than unsupported. **That is the shortest path from 601 to 631**, and
it is already in progress.

## Honest reading

- Parity on the CORE is real, not aspirational: identical pass counts,
  zero failures, on the same manifest files.
- Parity on BREADTH is not close. F\* carries roughly 9 spec families
  the Lean tree has never touched.
- The Lean tree is not a serving system: no storage backend, no HTTP
  server. It computes; it does not yet host.
- Performance is a separate axis and is measured separately: the Lean
  evaluator is quadratic on joins
  (`docs/designissues/2026-08-22-indexing-and-join-processing.md`).

---

# Addendum, 2026-08-23 — six suites measured end to end

Six conformance suites that this ledger listed as absent or as slices
now have runners and measured scores. Every number below is one
command, and the command is named.

| Suite | Score | Runner |
| --- | --- | --- |
| csv2rdf | 270 pass, 0 fail, 0 skip (out of 270) | `lake exe l4csvw-rdf` |
| csv2json | 270 pass, 0 fail, 0 skip (out of 270) | `lake exe l4csvw-json` |
| JSON Schema draft-07 | 770 pass, 0 fail, 0 undetermined (out of 770) | `lake exe l4jsonschema` |
| RML-Core | 60 pass, 0 fail (out of 60 compared) | `lake exe l4rml` |
| Schematron | 8 pass, 0 fail (out of 8) | `lake exe l4schematron` |
| MathML content | 56 pass, 0 fail (out of 56) | `lake exe l4mathml` |
| ShEx validation | 1075 pass, 104 fail (out of 1179 decided) | `lake exe l4shex` |
| XML conformance | 1840 pass, 22 fail (out of 1862 in profile) | `lake exe l4xmlconf` |
| RIF Core | 24 pass, 2 fail (out of 26 decided) | `lake exe l4rif` |

## What changed in the tree, not just in the scores

- **Schematron** had a validator with two open parameters and nothing
  to supply them. `XPath/Mini.lean` is the XPath 1.0 subset a `@test`
  and a `@context` need, and `Schematron/FromXml.lean` reads a `.sch`.
- **RML** had term generation and templates and nothing else. It now
  has a JSONPath subset, a typed source value, a mapping model, a
  graph reader, an evaluator, and dataset-isomorphism comparison.
- **RIF** had an RDF-triple-shaped model that could not state
  membership, subclass, positional atoms or built-ins. It is replaced
  by a presentation-syntax parser, a three-valued built-in library, a
  forward-chaining engine with Core safeness, and a runner.
- **XML** read no external resource at all. `parseXMLWith` takes a
  resolver, the external DTD subset and conditional sections are
  parsed, parameter entities are expanded, and an entity's
  replacement text is reparsed as content.

## Still absent, and named

XSLT (88 vendored cases, no engine), GRDDL, the COTTAS columnar store
above the byte layer, `Math.*` (a computer-algebra slice: Diff,
Matrix, Series, Simplify, Subst), `Parser.OWLFunctional`,
`Parser.ShExC`, `XForms.Bind`, and `SPARQL.HTTP.*` beyond
`HTTP/Server.lean`. The RIF built-in library is a named subset of
RIF-DTB's 197, and the 13 UNDECIDED RIF cases are exactly the ones
that need the rest.

---

# Addendum 2, 2026-08-23 — XSLT and GRDDL

The two suites the first addendum listed first under "still absent"
now have engines and measured scores. XSLT came first because GRDDL
depends on it: a GRDDL transformation IS an XSLT stylesheet.

| Suite | Lean score | F\* score | Runner |
| --- | --- | --- | --- |
| XSLT 1.0 | 84 pass, 3 fail (out of 87 decided), 1 refused (of 88) | 87 pass, 0 fail, 1 skip (of 88) | `lake exe l4xslt` |
| GRDDL | 19 pass, 22 fail (out of 41 decided) (of 68) | 18 pass, 50 fail (of 68) | `lake exe l4grddl` |

## What landed in the tree

- **A real XPath 1.0 engine.** `XPath/{Data,Expr,Eval}.lean`: the
  data model with node IDENTITY as an address, the whole grammar
  (thirteen axes, predicates on every step, unions, arithmetic,
  filter expressions), and an evaluator with the §4 function library.
  It is a SECOND model beside `XPath/Mini.lean`, in namespace
  `L4Factoidal.XPath.Full`, because `Mini` addresses nodes by an
  element-only path string that cannot name a text, comment or PI
  node — and changing `Mini` would change the node identity
  Schematron depends on.
- **An XSLT 1.0 engine.** `XSLT/Transform.lean`: stylesheet reading,
  template instantiation, attribute value templates, variables and
  parameters, modes, sorting, `xsl:import`/`xsl:include` with import
  precedence, result-tree serialisation with namespace fixup.
  `XSLT/Templates.lean`'s §5.5 conflict resolution, which was already
  ported, is what it feeds.
- **GRDDL discovery.** `GRDDL/Discovery.lean`: the four ways a
  document names a transformation (§2 attribute, §4 profile-gated
  links, §5 profile documents, §3 namespace documents), and the §7
  merge.

## Three features that are NOT in the 1.0 specifications

`eq ne lt le gt ge` (XPath 2.0 value comparisons), the `1e3` double
literal (XPath 2.0), and `xsl:copy-of copy-namespaces="no"` (XSLT
2.0). Each is implemented because the F\* engine implements it and
because ignoring it is certainly wrong; each is marked as an
out-of-version extension where it appears.

## I/O is a parameter, everywhere

Neither engine opens a file. `document(uri)` reads a map the caller
supplies; `XSLT.importHrefs` says which `xsl:import` targets a
stylesheet wants and the caller fetches them; the GRDDL runner
fetches namespace and profile documents from the vendored docroot.
A URI nobody supplied is a REFUSAL, never an empty tree the
stylesheet would quietly transform into nothing.

## The residue, named

- XSLT: namespace declaration ORDER on one case (the suite's own
  expected files are not self-consistent about it), the
  implementation-defined `namespace::` axis order on one, `xsl:copy`
  of a node from a second document on one, and one case whose
  `document()` target the vendoring did not capture.
- GRDDL: 17 cases need a document the vendored docroot does not
  carry; 10 name no transformation this stage can follow; 7 of the 22
  failures differ ONLY by the http/https scheme, which is vendoring
  drift rather than a transform defect. The 15 real failures are
  multi-transformation merges that come up short — the
  one-level-not-a-fixpoint limit `Discovery.lean` states.

## Still absent after this

The COTTAS columnar store above the byte layer, `Math.*` (Diff,
Matrix, Series, Simplify, Subst), `Parser.OWLFunctional`,
`Parser.ShExC`, `XForms.Bind`, and `SPARQL.HTTP.*` beyond
`HTTP/Server.lean`.

# Addendum 3, 2026-08-23 — ShExC, and what the "still absent" list now says

## ShExC

`L4Factoidal/ShEx/Compact.lean` reads the ShEx compact syntax into
the same `Schema` AST that `ShEx/FromJson.lean` builds from ShExJ.
`ShEx/SchemaEq.lean` compares two schemas. `Harness/ShExCRun.lean`
runs both front doors over every fixture in
`third_party/testing/shex/schemas/` — each ships a `.shex` and a
`.json` twin of the SAME schema — and reports the two trees' verdict.

| Suite | Score | Runner |
| --- | --- | --- |
| ShExC compact syntax | 442 match, 0 mismatch, 0 declined (out of 442) | `lake exe l4shexc` |
| ShEx validation | 1075 pass, 104 fail (out of 1179 decided) | `lake exe l4shex` |

The validation score is unchanged by this landing: the two readers
now agree without either moving.

A DECLINED schema is counted apart from a mismatch. A construct
outside the implemented grammar is visibly unparsed, never a schema
that validates the wrong graphs — and keeping the buckets apart is
what made the work tractable. The first run read 365 match, 53
mismatch, 24 declined: the refusals named exactly two grammar holes
and the mismatches four content defects. One number would have
covered six unrelated causes.

⚠️ The differential's limit is worth stating: it certifies that the
two readers build the SAME tree, not that either tree is right. What
protects against a shared error is that the two were written from
different specifications — the compact grammar and the ShExJ schema —
and that the validation suite exercises the result against real
graphs.

Eight defects and the fixtures that paid for them are in
`formal/lean4/PORT_NOTES.md` § "ShExC"; each is pinned in
`L4Factoidal/ShEx/CompactTests.lean`. The one worth repeating here:
numeric facets were compared as SPELLINGS, so `MININCLUSIVE 05`,
`5.0` and `05.00E0` each differed from `5`. That single defect
accounted for 48 of the 53 mismatches — a disagreement about
spelling, reported as a disagreement about the schema.

## Correction to the earlier "still absent" list

Addendum 2 ended with a list that later landings have overtaken.
What it named, and where each now is:

| Named absent in Addendum 2 | Now |
| --- | --- |
| `Math.*` (Diff, Matrix, Series, Simplify, Subst) | landed, `L4Factoidal/Math/` |
| `Parser.OWLFunctional` | landed, `L4Factoidal/OWL/FunctionalSyntax.lean` |
| `Parser.ShExC` | landed, `L4Factoidal/ShEx/Compact.lean` (this addendum) |
| `XForms.Bind` | landed, `L4Factoidal/XForms/Bind.lean` |
| `SPARQL.HTTP.*` beyond `HTTP/Server.lean` | landed, `L4Factoidal/HTTP/{Client,RunQuery,Ops}.lean` |
| The COTTAS columnar store above the byte layer | 🔴 still absent |

Standing rule this correction earns: a "still absent" list is a
measurement with a date on it, and it decays. Re-derive it from the
tree rather than copying it forward.

## Next

The executable OWL DL tableau refuter,
https://github.com/danbri/factoidal/issues/548 — the F* modules total
7,867 lines (`Tableau.fst` 1,522, `Tableau.Refute.fst` 4,682,
`Tableau.CountingOracle.fst` 1,663). Step 1, the class-expression AST
and graph reader (`L4Factoidal/OWL/ClassExpr.lean`), is done.

# Addendum 4, 2026-08-23 — the OWL DL reasoner, steps 2 and 3

Tracked at https://github.com/danbri/factoidal/issues/548 . Step 1
(the class-expression AST and graph reader) landed earlier; steps 2
and 3 wave 1 land here, with step 4's wiring.

## 📊 Measured

`lake exe l4owl-probe --dir third_party/testing/owl [--dl]`

| Regime | Score |
| --- | --- |
| RL closure only | 1131 pass, 316 fail, 2 skip, 8 unsupported (out of 1457) |
| RL + materialisation + refuter (`--dl`) | 1177 pass, 270 fail, 2 skip, 8 unsupported (out of 1457) |

Most of it is one catalog: `type-inconsistency.rdf` goes from 30
pass, 97 fail to 67 pass, 60 fail (out of 127 decided). The F\* line
for that catalog is 126 pass, 1 fail, so wave 1 closes about half the
distance.

⚠️ `type-consistency.rdf` reads 485 pass, 94 fail in BOTH columns,
and that is a net figure hiding a trade: `--dl` gains three
positive-entailment cases there and loses three consistency cases
(`WebOnt-description-logic-018`, `-020`, `-021`) where the RL clash
detector fires on the materialised graph. Named residue, not a
wash.

## The design decision worth carrying forward

`Refute.refute` answers `some false` or `none`. It has **no
`some true`**.

The F\* module returns `Some true` for a saturated clash-free branch
and its own header then instructs callers to treat it exactly like
`None`, because the calculus is incomplete. A value that no caller
may act on is a trap — sooner or later something scores "consistent"
on it. Wave 1 does not have the value to misuse.

The same discipline shows up twice more in this landing:

* `cePositiveSound` gates what a `some true` may WRITE into a graph,
  and the gate is structural — a refused shape anywhere inside a
  Boolean combination closes it;
* `materialiseWithBudget` caps the membership pass and REPORTS the
  cap, and the probe scores a budget hit as a cap hit, so an absence
  verdict on a capped premise is a failure rather than a pass.

## Three defects, and what each says about refuters

Full war stories in `formal/lean4/PORT_NOTES.md` § "OWL DL". The
short forms:

1. **A spelling difference is not a value difference.** Two literals
   sharing a datatype and differing in lexical form are not
   necessarily different values — `"1"` and `"01"` are one
   `xsd:integer`. `WebOnt-miscellaneous-202` asserts the
   `rdf:XMLLiteral` whitespace case as CONSISTENT, and the rule
   refuted it. A refuter that reads formatting as meaning invents
   contradictions out of whitespace, CONFIDENTLY, on premises a human
   would call obviously satisfiable.
2. **A witness must not be counted, including by consumers.** The
   tableau states that rule for itself, but the materialisation pass
   writes its witness into the graph and the RL clash detector counts
   blank nodes like any other name. The rule has to hold downstream
   too. The first fix — strip every witness edge — was the more
   obviously "correct" one and measured WORSE by twelve cases; the
   measurement settled it.
3. **A vacuous truth is not an entailment.** `∀p.C` holds vacuously
   of an individual with no known successor, and that membership is
   not entailed under the open world assumption.

## Correction to Addendum 3's "still absent" list

The COTTAS columnar store above the byte layer remains the only
named absence. This addendum adds no new one.
