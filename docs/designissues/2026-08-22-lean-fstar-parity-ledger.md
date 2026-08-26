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
The single most useful number, **re-measured 2026-08-26**: on the full
SPARQL 1.1 manifest BOTH engines score **631 pass, 0 fail, 0 skip, 0
unsupported (out of 631)**. The Lean side is level with F\*.

⚠️ SUPERSEDED, kept as the record of the drift: this paragraph read
**601 pass, 0 fail, 30 unsupported (out of 631)** for Lean, measured
2026-08-22, with the 30 unsupported characterised below as
entailment-regime tests (OWL-Direct, OWL-RDF-Based, RIF). Those 30 were
closed at some point in the following four days and this file was not
re-run, so the stale figure was quoted into a GitHub issue on
2026-08-26 as a live Lean-versus-F\* gap. Verified by running
`.lake/build/bin/l4w3c --quiet third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`
FROM THE REPOSITORY ROOT — the runners resolve manifest paths relative
to the root and print `manifest not found` while still exiting 0 when
run from `formal/lean4`, so a wrong working directory yields no score
rather than a wrong one. Re-run before quoting any row here.

## At parity (measured this session)

| Suite | F\* | Lean 4 |
|---|---|---|
| SPARQL 1.1, whole manifest (re-measured 2026-08-26) | 631 pass, 0 fail (of 631) | 631 pass, 0 fail (of 631) |
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
| SPARQL entailment regimes | supported | supported (re-measured 2026-08-26: 0 unsupported; the "30 unsupported" section below is SUPERSEDED) | none |

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

## The 30 unsupported, characterised — SUPERSEDED 2026-08-26

⚠️ This section describes a gap that no longer exists: the whole
SPARQL 1.1 manifest reads 631 pass, 0 fail, 0 unsupported on the Lean
side as of 2026-08-26. Retained as the record of what the gap was and
of how long a stale row survived unnoticed.

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

# Addendum 5, 2026-08-23 — OWL DL wave 2, and the XSD value spaces

## 📊 Measured

`lake exe l4owl-probe --dir third_party/testing/owl [--dl]`

| Regime | Score |
| --- | --- |
| RL closure only | 1131 pass, 316 fail, 2 skip, 8 unsupported (out of 1457) |
| Wave 1 | 1177 pass, 270 fail |
| Wave 2 | 1192 pass, 255 fail, 2 skip, 8 unsupported (out of 1457) |

`type-inconsistency.rdf` carries it: 30 pass, 97 fail with the RL
closure alone becomes 80 pass, 47 fail (out of 127 decided). The F\*
line for that catalog is 126 pass, 1 fail.

`type-consistency.rdf` is unchanged and carries the SAME three
regressions Addendum 4 named. The datatype rules added no new
fabricated contradiction.

## A new module, not only new rules

`formal/lean4/L4Factoidal/XSD/Facets.lean` ports
`formal/fstar/XSD.Facets.fst`: the OWL 2 datatype map as a decidable
value space. It is the concrete-domain half of the DL reasoner and it
was absent from the Lean tree entirely.

Four value spaces, not one. OWL 2 Syntax §4.1 makes `owl:real`
disjoint from `xsd:double` and `xsd:float`; §4.2 keeps those two
apart; `xsd:dateTime` is a fourth dimension. Modelling them as one
number line would let `"1.0"^^xsd:float` be proved equal to
`"1.0"^^xsd:decimal`, which OWL 2 denies.

Every operation in it is ONE-SIDED, and that is the whole design: an
empty value space is a clash, which refutes an ontology, so a value
is dropped only on a proof that it is outside. "Not proved equal" is
not "proved distinct" — `"3.0"^^xsd:decimal` and `"3"^^xsd:integer`
are one value, so the pair answers `false` to both predicates and
withholds the clash.

## 🔴 The cost, filed

The `--dl` run takes 26 minutes 34 seconds against well under one for
the RL closure alone. Tracked at
https://github.com/danbri/factoidal/issues/549 , with the attribution
measured rather than guessed: on `type-consistency.rdf` the closure
alone is 17 s, `--dl` with the refuter off is 5 m 10 s, and `--dl` at
the default budget is over 10 m.

`--dl` is a flag, so no routine gate is affected.

## The methodology note this landing earns

Four performance defects were found and fixed. THREE of them —
a per-branch search depth, list-scanning successor lookups, and
recomputed role closures — each looked like the answer and each moved
the number by nothing measurable. What explained
`type-inconsistency.rdf`'s 76 seconds was a BUDGET SWEEP showing one
case (`WebOnt-description-logic-504`) accounting for 71 of them.

`skills/measuring-inference` already says to find which phase the
time is in before optimising anything. This is the fourth time that
rule has been paid for. The specific shape here: a plausible
mechanism plus a code reading produced three work orders, and the
measurement that would have ruled all three out took two minutes.

# Addendum 6, 2026-08-23 — wave 3, and a CORRECTION to Addendum 5

## 🔴 Correction first

Addendum 5 ends with a methodology note headed "The methodology note
this landing earns", which says three of four performance fixes
"each looked like the answer and each moved the number by nothing
measurable", and draws the lesson that a plausible mechanism plus a
code reading produced three work orders that a two-minute
measurement would have ruled out.

**That note is wrong.** Three of those edits were never applied to
the file at all. The scripts that made them wrote the file only at
the end, so an assertion failure on a later replacement discarded
every earlier one — after the script had printed its progress. The
build that followed compiled the unchanged file and passed. The
measurement that followed measured the unchanged file.

Verified by grepping the file for each change: the indexed successor
lookups and the memoised role closures were present; the threaded
search budget, the `labelsOf` lookup and the hoisted per-axiom label
reads were not. A sixth item was defined and never called.

📊 With all of them ACTUALLY applied, the `--dl` run goes from
**26 minutes 34 seconds to 4 minutes 30 seconds** — 5.9× — and the
score goes UP by one case. So the fixes did not "buy nothing"; they
were absent.

The real lesson is a different one, and it is now
`skills/workflow-gotchas-debugging` hazard #26: a green build is not
evidence that an edit landed, and one `grep -c` per claim before
writing a commit message would have caught all three in under a
minute.

## 📊 Wave 3 measured

| Regime | Score | Wall |
| --- | --- | --- |
| RL closure only | 1131 pass, 316 fail, 2 skip, 8 unsupported (out of 1457) | under 1 m |
| Wave 1 | 1177 pass, 270 fail | — |
| Wave 2 as committed | 1192 pass, 255 fail | 26 m 34 s |
| Wave 3 | 1193 pass, 254 fail, 2 skip, 8 unsupported (out of 1457) | 4 m 30 s |

`type-inconsistency.rdf` reaches 81 pass, 46 fail (out of 127
decided); the F\* line for that catalog is 126 pass, 1 fail.
`type-consistency.rdf` is unchanged with the same three regressions
Addendum 4 named.

## The ≤-rule, and the second thing it taught

The SHIQ ≤-rule identifies two successors of a node that is over its
cardinality bound and whose successors are not forced apart. Seventeen
`WebOnt-description-logic` inconsistency fixtures need it.

The first implementation REWROTE EDGES and passed a hand-built guard
reproducing one of those fixtures. On the corpus it fired ZERO times:
the `--dl` regime runs the materialisation pass first, and that pass
writes its own existential witnesses INTO the graph, where an edge
cannot be rewritten. Identification is now done at READ TIME —
`RState.ident` records pairs, `labelsOf` pools the group and
`successorsOf` maps through the representative.

That is `skills/workflow-gotchas-debugging` hazard #27: a synthetic
input built from a rule's own preconditions tests the rule's LOGIC
and cannot test whether the real pipeline ever presents those
preconditions. The upstream stage had changed the shape of the input
the rule was written against.

## Also in wave 3

Closure scaffolding (`__rl_`-prefixed blank nodes, materialised by
`RLRules.lean` as support triples with a deliberately loose encoding)
now parses to `unknown`. The F\* module guards against this and says
reading it literally MANUFACTURES refutations of consistent premises.
It moved no score, which is what a soundness guard that is not yet
being violated looks like.
