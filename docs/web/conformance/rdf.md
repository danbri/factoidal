---
title: RDF conformance
layout: base.njk
---

# RDF conformance — measured scores and every named residual

Factoidal runs the W3C RDF test suites from disk, through the
F\*-extracted parsers, canonicaliser and entailment engines, and reports
the result per suite. This page states the scores as measured, defines
the entailment regimes they are measured under, names **every** test
that still fails or is skipped with the reason and its disposition, and
separates what is **proved** from what is only **measured**.

Every number below comes from one re-run of every RDF suite against the
committed `bin/linux-x86_64/w3c_runner` and
`bin/linux-x86_64/rdfc10_runner` binaries on 2026-07-30, from the repo
root, at tree `873aed4`. Nothing here is copied from a document. The
machine-readable copy is the
[test-results dashboard]({{ '/test-results/' | url }}) and its
`latest.json`; a number here that disagrees with that file is a bug in
one of them, not a judgement call.

Parser and algebra spec are verified in F\*; the on-disk backend has
unverified OCaml-side optimization layers being migrated back to F\*.

Sibling pages: [OWL 2 conformance]({{ '/web/conformance/owl2/' | url }})
&middot; [SPARQL conformance]({{ '/web/conformance/sparql/' | url }})
&middot; [per-module assurance inventory]({{ '/web/conformance/assurance-inventory/' | url }}).

## What each entailment regime means

The RDF suites are not all syntax. Three of them (`rdf-mt`,
`rdf12entail`, and the entailment part of the OWL/SPARQL work) score an
**entailment** question: does graph A entail graph B? The answer depends
entirely on which regime you ask under, so the regimes are stated first
and the dispatch is stated with them.

**Simple entailment.** No vocabulary has any special meaning. A entails
B exactly when there is a mapping of B's blank nodes to terms of A that
turns every triple of B into a triple of A — a graph homomorphism. IRIs
and literals are compared as syntax; nothing is derived. This is the
weakest regime and the only one for which this project has a
machine-checked soundness *and* completeness proof (see
[what is proved](#what-is-proved-versus-what-is-measured) below).

**RDF entailment.** Simple entailment plus the RDF axiomatic triples and
the rule that every predicate is an `rdf:Property` (rdfD2), plus
recognised-datatype value equality — so `"1"^^xsd:integer` and
`"1.0"^^xsd:decimal` denote the same thing, and an ill-typed literal in
a recognised datatype makes the graph inconsistent.

**RDFS entailment.** RDF entailment plus the RDFS rules: `rdfs:domain`
and `rdfs:range` type their subjects and objects, `rdfs:subClassOf` and
`rdfs:subPropertyOf` propagate and are transitive, container membership
properties are sub-properties of `rdfs:member`.

**D entailment (datatype entailment).** Parameterised by a set of
recognised datatypes: literals are compared by *value* in those
datatypes rather than by lexical form, and a literal whose lexical form
is not in its datatype's lexical space makes the graph inconsistent. RDF
and RDFS entailment are both defined on top of a D-entailment step.

### Which regime each runner actually dispatches

| Suite | Regimes in the manifests | What the runner does |
|---|---|---|
| `rdf-mt` (RDF 1.1 Semantics, 39 tests) | RDFS 24, RDF 10, simple 5 | Closes the premise with the F\*-extracted `rdfs_closure` (`RDFS.Closure.fst`, reached through `RDF.Graph.Executable`'s `include`), then runs a homomorphism search **written in OCaml inside `bin/w3c-runner/w3c_runner.ml`** (`simple_entails_regime` / `literal_match`), not the F\*-extracted entailment engine. The "simple" regime there is strict syntactic literal equality; RDF and RDFS use a value-equality comparison that delegates to the F\*-extracted `datatype_value_eq` and the normalisers but whose cross-datatype cases are hand-written OCaml. |
| `rdf12entail` (RDF 1.2 Semantics, 47 tests) | simple, RDF, RDFS, RDFS-Plus, and regimes the engine does not model | Dispatches into the **F\*-extracted** `RDF.Entailment.Regime.entails_rdf` / `entails_rdfs` / `entails_rdfs_plus`, each of which is `RDF.Entailment.Simple.entails_with` under a datatype `leq` and a blank-node-ranging predicate. Any regime outside that set is an honest `Skip`, never a guessed verdict. |
| the syntax suites (`rdf-n-triples`, `rdf-turtle`, `rdf-n-quads`, `rdf-trig`, `rdf-xml`, and their RDF 1.2 counterparts) | none — accept/reject and parse-and-compare | No entailment at all. Negative-syntax tests go through `parse_turtle_strict` (a genuine reject path); eval tests parse and compare graphs after RDFC-1.0 canonicalisation. |
| `rdfc10` | none | Canonicalisation, not entailment: `RDF.Canonical.fst` (Hash First Degree Quads plus full Hash N-Degree Quads permutation enumeration), compared bytewise on Eval tests, structurally on Map tests, and against an HNDQ work budget on NegEval tests. |

So the two entailment suites are checked by **two different engines**,
and only one of them is the F\*-extracted one. That is stated here
because it changes what a green `rdf-mt` row means; see
[what is proved](#what-is-proved-versus-what-is-measured).

## Scores

| Suite | Runner invocation | Score |
|---|---|---|
| RDF 1.1 N-Triples | `w3c_runner --rdf rdf-n-triples` | 70 pass, 0 fail, 0 skip (out of 70) |
| RDF 1.1 Turtle | `w3c_runner --rdf rdf-turtle` | 313 pass, 0 fail, 0 skip (out of 313) |
| RDF 1.1 N-Quads | `w3c_runner --rdf rdf-n-quads` | 87 pass, 0 fail, 0 skip (out of 87) |
| RDF 1.1 TriG | `w3c_runner --rdf rdf-trig` | 356 pass, 0 fail, 0 skip (out of 356) |
| RDF 1.1 RDF/XML | `w3c_runner --rdf rdf-xml` | 166 pass, 0 fail, 0 skip (out of 166) |
| RDF 1.1 Semantics (`rdf-mt`) | `w3c_runner --rdf rdf-mt` | 39 pass, 0 fail, 0 skip (out of 39) |
| **RDF 1.1, all six** | `w3c_runner --rdf` | **1031 pass, 0 fail, 0 skip (out of 1031)** |
| RDF 1.2 syntax + eval (`rdf12`) | `w3c_runner --rdf12` | 242 pass, 0 fail, 0 skip (out of 242) |
| RDF 1.2 canonicalization (`rdf12c14n`) | `w3c_runner --rdf12c14n` | 82 pass, 0 fail, 0 skip (out of 82) |
| RDF 1.2 Semantics (`rdf12entail`) | `w3c_runner --rdf12entail` | 41 pass, 3 fail, 3 skip (out of 47) |
| RDFC-1.0 (`rdfc10`) | `rdfc10_runner third_party/testing/rdf-canon/tests/manifest.ttl` | 86 pass, 0 fail, 0 stub (out of 86) |

The RDF 1.2 rows break down per leaf manifest as: N-Triples syntax 29,
N-Quads syntax 27, Turtle syntax 67, Turtle eval 29, TriG syntax 35,
TriG eval 25, RDF/XML eval 30 — each 0 fail, 0 skip; and c14n
N-Triples 41, c14n N-Quads 41, each 0 fail, 0 skip.

RDF 1.2 and its suites are **W3C Working Drafts**, not Recommendations.
A green row there is progress against a moving target.

### The denominators, checked independently

Every denominator above was re-derived from the `mf:entries` list of
each manifest, not taken from the runner. They agree exactly: 70, 313,
87, 356, 166, 39 (sum 1031) for RDF 1.1; 242 and 82 and 47 for the RDF
1.2 suites; 86 `mf:action` entries for `rdfc10`.

Twelve further test descriptions exist in those manifests but are
**commented out of the `mf:entries` list upstream**, so they are outside
every denominator on this page. They are not skips — a skip is work we
intend to do; these are tests the W3C suite itself withdrew:

| Suite | Withdrawn entry | Upstream note |
|---|---|---|
| `rdf-mt` | `datatypes-intensional-xsd-integer-string-incompatible` | "recinded 2013-12-18" |
| `rdf-mt` | `pfps-10-non-well-formed-literal-1` | "duplicate" |
| `rdf-mt` | `xmlsch-02-whitespace-facet-3` | "recinded 2013-12-17" |
| `rdf-xml` | `rdfms-empty-property-elements-error003`, `-test003`, `-test009` | commented out, no inline reason |
| `rdf-xml` | `rdfms-xml-literal-namespaces-test001`, `-test002` | commented out, no inline reason |
| `rdf-xml` | `rdfms-xmllang-test001`, `-test002` | commented out, no inline reason |
| `rdf12c14n` | `lantag_with_subtag` (N-Triples and N-Quads copies) | commented out, no inline reason |

### A manifest defect in this repo's own suite wiring

Six `.github/test-suites/*.yaml` manifests — `rdf-turtle`, `rdf-xml`,
`rdf-trig`, `rdf-n-triples`, `rdf-n-quads` and `rdf-mt` — declare
`log_path: formal/fstar/ocaml-output/sparql_results.log`. That file
carries the **SPARQL** score lines. The RDF suites' scores are in
`rdf_results.log`. Anything that resolves an RDF suite's score by
reading its declared `log_path` and taking the file total will read
`631` (the SPARQL 1.1 total) where the correct answer is the per-suite
label, e.g. `313` for `rdf-turtle`. That mis-resolution has already
happened once in draft prose for this page. Resolve by exact suite
label, never by file total, until the manifests are corrected.

## Disposition vocabulary

Each residual carries one of five labels, from the completeness ledger's
fixed vocabulary (issue
[#308](https://github.com/danbri/factoidal/issues/308)):

- **by-design** — the test asks for something outside what this engine
  claims, citing the suite's own metadata or a written scope decision.
- **planned-family** — a real gap in a named family of missing
  behaviour, tracked and intended.
- **dependency-blocked** — waiting on a capability elsewhere in the
  engine.
- **disputed-fixture** — the fixture itself is defective or its expected
  verdict does not follow; documented per test.
- **environment** — toolchain or harness, not semantics.

## Residual failures — RDF 1.2 Semantics (3 of 47)

These are the only failing tests in any RDF suite measured on this page.
All three are `mf:PositiveEntailmentTest`s reported as "Should entail but
doesn't" — under-derivation, never a wrong entailment. Every fixture
below was read, not inferred from the test name. All three carry
`rdft:approval rdft:NotClassified`: the RDF 1.2 Working Group has not
approved them.

| Test | Disposition | Reason |
|---|---|---|
| `annotation` | disputed-fixture | Premise `test007a.ttl` is `:a :b :c {| :p1 :o1 |}.`, which expands to three triples over `:a :b :c :p1 :o1 rdf:reifies` and a fresh blank node. The expected graph `test007r2.ttl` is `:a1 :p1 <<( :a :b :c )>>.` — it names the ground IRI `:a1`, which occurs nowhere in the premise. No monotone entailment relation over RDF can introduce a ground IRI absent from the premise and from the axiomatic triples, so the assertion does not follow under any regime. `test007r2.ttl` is byte-identical to the second line of `test007a2.ttl`, so it reads as the result file belonging to a different action. |
| `annotation-unfolded` | disputed-fixture | The mirror-image defect. Premise `test007a2.ttl` is `:a :b :c.` plus `:a1 :p1 <<( :a :b :c )>>.`; the expected graph is `test007a.ttl`, whose annotation shorthand expands to include `_:r :p1 :o1`. The ground IRI `:o1` occurs nowhere in the premise, so again nothing can derive it. The manifest's own comment concedes the test "is not really a semantics test". |
| `triple-terms-propositions` | dependency-blocked | Premise `:a1 :p1 <<( :a :b :c )>> .`; expected `:a1 :p1 _:pp . _:pp rdf:type rdfs:Proposition .` under the RDFS regime. This needs the RDF 1.2 Semantics axiom that a **triple term** denotes an instance of `rdfs:Proposition`. The engine has the reifier form of that rule — `X rdf:reifies Y` adds `Y rdf:type rdfs:Proposition` when `Y` is an IRI or blank node (`RDF.Entailment.Regime.reifies_prop_triples`) — but not the triple-term form, because `RDF.Term.subject = S_IRI \| S_BNode` cannot hold a triple term in subject position. `RDF.Entailment.Regime.fst` names this test in its own header as blocked on a generalized-RDF term model. Tracked under the RDF 1.2 epic [#305](https://github.com/danbri/factoidal/issues/305), phase P9. |

## Skipped tests — RDF 1.2 Semantics (3 of 47)

Skips are reported by the runner, counted in the denominator, and named
here rather than dropped.

| Test | Disposition | Reason |
|---|---|---|
| `malformed-literal-control` | planned-family | `mf:result false` — an **inconsistency** test: the premise is meant to be inconsistent under D entailment because it carries a malformed `xsd:integer` literal. The engine has no inconsistency detection at the RDF/D level, so the runner reports `Skip "No result file (mf:result false — inconsistency test)"` instead of scoring an absence it never checked. Tracked under [#305](https://github.com/danbri/factoidal/issues/305) P9. |
| `malformed-literal` | planned-family | Same mechanism: "Malformed literals are allowed in triple terms, but cause inconsistency." |
| `literal-type` | disputed-fixture | The manifest entry `trs:literal-type` uses the prefixed names `test:approval test:NotClassified`, and **no `test:` prefix is declared anywhere in that manifest** — it is the only entry in the file that does. Verified: `grep` finds exactly one `test:` occurrence, upstream commit `2b35822` ("Add test for entailment of literal type", 2025-06-28) added it, and parsing the manifest yields exactly one triple mentioning `literal-type` (its membership in `mf:entries`) rather than the seven the block declares. The whole description block is therefore dropped, the entry has no `mf:name` / `mf:action` / `mf:result`, and the runner prints it by raw IRI and skips it. Underneath the fixture defect there is also a real gap: `RDF.Entailment.Regime.fst` names `literal-type` as blocked on the same generalized-RDF term model as `triple-terms-propositions` (its conclusion `"42" rdf:type xsd:integer` puts a **literal** in subject position). |

### Harness note the `literal-type` skip exposes

The Turtle parser used to load manifests (`parse_turtle_fstar`) drops a
statement that uses an undeclared prefix and carries on, instead of
rejecting the document. Measured directly: a three-statement file whose
middle statement uses an undeclared prefix parses to the other two
statements and exits 0. The document-level guard only fires when the
result is empty ("parsed to zero triples but is not an empty document",
issue [#325](https://github.com/danbri/factoidal/issues/325)), which is
why the five `turtle-syntax-bad-prefix-*` negative tests still pass —
they are single-statement files, and they are additionally scored
through the separate strict path `parse_turtle_strict`, which does
reject. The W3C Turtle suite contains no multi-statement
undeclared-prefix fixture, so this leniency is invisible to the score
and visible only here.

## Passes that are decided without running an entailment check

`rdf-mt` reads 39 pass, 0 fail (out of 39). Ten of those 39 are decided
by the harness before any entailment or consistency question is asked.
This is measured, not inferred: replacing a fixture with non-RDF text
and re-running the suite shows which verdicts change.

- **Seven `mf:PositiveEntailmentTest`s carry `mf:result false`** — they
  assert the premise is *inconsistent*. The runner has no inconsistency
  check, and its positive-entailment arm returns `Pass` as soon as it
  sees "action file present, no result file". Verified by replacing
  `rdf-mt/datatypes/test006.nt` with the line `this is not RDF at all
  @@@ <<< >>>`: `datatypes-range-clash` still reports PASS. Deleting the
  file instead turns it into `Skip "Action file missing"`, so the pass
  is conditioned on file existence and nothing else. The seven are
  `datatypes-non-well-formed-literal-2`, `datatypes-range-clash`,
  `datatypes-test010`, `rdfs-entailment-test001`,
  `rdfs-entailment-test002`, `xmlsch-02-whitespace-facet-2`,
  `xmlsch-02-whitespace-facet-4`.
- **Three `mf:NegativeEntailmentTest`s carry `mf:result false`** — they
  assert the premise is *not* inconsistent. The runner's arm for these
  loads the premise and passes if loading raised nothing; the runner's
  own comment says "For now, just check action parses." Verified by
  replacing `rdf-mt/rdfs-subClassOf-a-Property/test001.nt` with non-RDF
  text: `rdfs-subClassOf-a-Property-test001` still reports PASS. The
  three are `datatypes-intensional-xsd-integer-decimal-compatible`,
  `datatypes-non-well-formed-literal-1`,
  `rdfs-subClassOf-a-Property-test001`.
- **The other 29 do bite.** Verified by replacing the expected graph of
  `datatypes-semantic-equivalence-within-type-1` with an unrelated
  triple: the test flips to `FAIL: Entailment failed: action has 11
  triples (after closure), expected 1`.

So the defensible reading of the row is: **39 pass, 0 fail (out of 39),
of which 29 are decided by an entailment check and 10 by the presence or
loadability of a file.** The ten are the RDF 1.1 Semantics
*inconsistency* tests, and inconsistency detection is the same
planned-family gap that skips `malformed-literal` in RDF 1.2. Both are
tracked under [#305](https://github.com/danbri/factoidal/issues/305) P9;
the RDF 1.1 side additionally deserves the honest-verdict treatment OWL
got in [#326](https://github.com/danbri/factoidal/issues/326), where an
answer the engine did not compute scores `unsupported` rather than
`pass`.

## Disposition counts

Across the 6 distinct tests that fail or are skipped in any RDF suite —
all six in `rdf12entail`; every other RDF suite is at 0 fail, 0 skip:

| Disposition | Count |
|---|---|
| by-design | 0 |
| planned-family | 2 |
| dependency-blocked | 1 |
| disputed-fixture | 3 |
| environment | 0 |

The ten `rdf-mt` file-existence passes are counted separately and carry
no disposition label from this vocabulary, for the same reason OWL's
`unsupported` verdicts do: they are not answers the engine got wrong,
they are questions it did not ask.

## What is proved versus what is measured

The rest of this page is measurement. This section is the part that is
not.

Three claims are easy to blur together, and the project keeps them apart
deliberately (issue
[#313](https://github.com/danbri/factoidal/issues/313)): a module can be
**implemented in F\***, **accepted by the F\* verifier**, or **proved
correct against a formalisation of the spec stated independently of the
code**. The third is rare. The machine-derived, hand-edit-free record of
which module is which is the
[per-module assurance inventory]({{ '/web/conformance/assurance-inventory/' | url }})
— its oracle is extraction, and it fails downward, so a module is
under-credited there rather than over-credited.

⚠️ One caveat on the inventory's numbers, from
[#328](https://github.com/danbri/factoidal/issues/328): its
**theorem-class** counts depend on build state, because the oracle asks
whether a module's extracted `.ml` exists on disk and 12 of those files
are gitignored. In fresh-clone / CI state the tool reports 30
W3C-refinement theorems; after a local `./build-ocaml.sh extract` it
reports 0. Every figure quoted below was re-derived on 2026-07-30 in a
**fresh worktree with no local extract** — the same regime that produced
the committed artifacts — and matched them exactly. The `assume val`,
admission and `--lax` counts are pure source scans and never flip; the
shipping-function counts quoted here are stable too, because every
module named on this page has its extracted `.ml` tracked in git.

**Proved: simple entailment, soundness and completeness.**
`RDF.Entailment.Simple.simple_entails` — the shipping blank-node
homomorphism search — carries 17 refinement theorems against declarative
relations defined in separate, fully-erased specification modules
(`RDF.Entailment.Simple.Spec`, `.Refinement`, `.ModelTheory`,
`.Boundary`). They include `simple_entails_complete`,
`simple_entails_sound`, `simple_entails_iff_spec`, the model-theoretic
`simple_entails_iff_model_theory`, blank-node-label independence
(`simple_entails_rename_invariant`), the same refinement at the
parameterised engine `entails_with` that the RDF 1.2 regimes call, and a
parser-boundary theorem `entails_ntriples_boundary` on
`Parser.NTriples.parse_ntriples_strict`. No admits, no `--lax`, z3
4.13.3. Design note:
[`docs/designissues/2026-07-29-simple-entailment-refinement.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-29-simple-entailment-refinement.md).

The soundness theorem is **conditional**, and the condition is stated as
a theorem too. `simple_entails_sound` requires `graph_exact` on both
graphs; `simple_entails_not_sound_unconditionally` is a machine-checked
*counter*-example showing that without it the shipping function accepts
an entailment the specification denies — two literals whose language
tags differ only in case. That is tracked as
[#324](https://github.com/danbri/factoidal/issues/324). A conditional
soundness proof plus a machine-checked witness for the missing case is a
stronger honesty position than an unconditional claim, and it is the
reason this vertical is worth pointing at.

### Landed 2026-07-30 — the RDF and RDFS rungs

The two refinement agents that were in flight when the table below was
measured have both landed. The table describes the shipping modules,
and **it is still accurate**: no shipping module changed. The
declarative relations live in separate, fully-erased companion modules.

| Module | Role | Lines |
|---|---|---|
| `RDF.Entailment.RDF.Spec` | RDF rung: rdfD1 / rdfD2, the recognized-datatype set, the axiomatic triples, `rdf_closed` | 209 |
| `RDF.Entailment.RDFS.Spec` | RDFS rung: the complete rdfs1–rdfs13 table quoted row by row, the axiomatic triples, `rdfs_closed`, the rho-df fragment | 380 |
| `RDF.Entailment.RDFS.Refinement` | The shipping rules against those tables | 788 |
| `RDF.Entailment.RDFS.ModelTheory` | Interpretation conditions, rule-table soundness, closure soundness | 724 |

Neither Spec module opens `RDFS.Closure`, `OWL.Closure`,
`RDF.Graph.Executable` or `RDF.Entailment.Regime`, so each can be
diffed against the W3C text on its own. All four verify with no
`admit` and no `--lax`, under z3 4.13.3.

Seven of the shipping rules now carry a transcription-fidelity theorem
(rdfD2, rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11, plus container
membership): every triple the rule emits is in the seed graph or is
derived from the source graph by one application of the rule row it
claims to implement. The model-theory module then proves every row of
the rule tables truth-preserving, and lifts that through one closure
step to the fixed-point driver.

⚠️ **The fixed-point theorem has no machine-checked instance**
([#338](https://github.com/danbri/factoidal/issues/338)). Its
hypothesis `closure_chain_wf` cannot be discharged for a single graph,
including the empty one, because `sp_key` is not proved injective —
and it is not injective on IRI subjects alone, since `is_iri` admits a
control character. The hypothesis is true of any graph avoiding
U+001F, so the theorem is **not vacuous**; what is missing is anyone
able to instantiate it. The per-rule truth-preservation theorems above
are unaffected. A theorem nobody can instantiate carries no assurance
until someone can, so this row should be read as pending, not as
closure soundness established.

The condition bundle those theorems quantify over **is** now proved
consistent, and proved to admit a model that falsifies a graph — so
`rdfs_entails` is a proper relation and the soundness theorems are not
vacuous for that reason either. Both were unproved before 2026-07-30;
see [`docs/designissues/2026-07-30-hypothesis-satisfiability.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-30-hypothesis-satisfiability.md).

🔴 **The attempt found four gaps**, tracked as
[#335](https://github.com/danbri/factoidal/issues/335). RS-1 is an
unsoundness in shipping code: `rdfs_reflexivity_axioms` harvests
reflexive `rdfs:subClassOf` / `rdfs:subPropertyOf` triples more widely
than any RDFS rule licenses, and the witness
`reflexivity_axioms_not_rdfs_sound` is hypothesis-free. RS-2 is six
rule rows with no implementation — rdfs1, rdfs4a, rdfs4b, rdfs8,
rdfs13 and rdfD1 — plus unseeded axiomatic triples. RS-3 is
`rdfs_rule_range` dropping literal objects, which the specification
forces: the rule's conclusion moves the object into subject position,
and `RDF.Term.subject` is IRI-or-bnode only. RS-4 is the rdf12
manifests' "RDFS" regime
running none of rdfs1–rdfs13, because two functions share the name
`rdfs_closure`.

Design note:
[`docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/designissues/2026-07-30-rdf-rdfs-entailment-refinement.md).

The SPARQL vertical landed the same day; see
[the SPARQL conformance page](sparql.md).

**Measured, not proved: everything else on this page.**

| Component | Assurance today (inventory, tree `fcb83d8`, re-derived 2026-07-30 with identical totals) |
|---|---|
| `RDFS.Closure` (7 rules: rdfs2, rdfs3, rdfs5, rdfs7, rdfs9, rdfs11, container membership) | 44 shipping functions, **0 declarative relations in the module**. Exactly **one** of the seven rules, `rdfs_rule_domain` (rdfs2), has refinement theorems — `rdfs_rule_domain_sound` and `rdfs_rule_domain_entailed`, proved in `OWL.Semantics.Soundness` against the RDF-Based-Semantics pilot's `cond_domain` / `pilot_entails`. The other six rules are merely total. |
| `RDF.Entailment.Regime` (the RDF 1.2 regimes) | 24 shipping functions, 0 declarative relations, **no theorem of its own**. Its strength is inherited: `entails_rdf` / `entails_rdfs` / `entails_rdfs_plus` are all `RDF.Entailment.Simple.entails_with` applied to a closed premise, and `entails_with` *is* proved sound and complete. The closure step it applies first is not. |
| `RDF.Graph.Executable` | 26 shipping functions, 0 declarative relations, 3 local refinement lemmas, no correctness theorem. |
| `Parser.Turtle` (116 shipping functions), `Parser.TurtleScanner`, `Parser.RDFXML`, `Parser.NQuads` | **merely `Tot`** — total, terminating, and measured by 1031 RDF 1.1 tests plus 242 RDF 1.2 tests, with no theorem relating them to the grammar. `Parser.NTriples` is the exception: it carries the simple-entailment boundary theorem. |
| `RDF.Canonical` (RDFC-1.0) | 152 shipping functions, **merely `Tot`**, 2 active `assume val`s (`hash_sha256`, `hash_sha384`). 86 pass, 0 fail (out of 86) is the whole of the evidence. There is no theorem that two datasets have equal canonical forms exactly when they are isomorphic — the external review named this specifically, and it is still open. |
| `rdf-mt`'s entailment check | Not F\*-extracted at all. `simple_entails_regime` and `literal_match` are hand-written OCaml in `bin/w3c-runner/w3c_runner.ml`, so 39 pass, 0 fail (out of 39) measures the runner as much as the engine. Iron rule #15 forbids semantic logic in the runner; this is the largest surviving instance in the RDF path. |

Across the whole tree the inventory reports 6 modules with a
W3C-refinement theorem, 7 with an internal-refinement theorem, 19 with
an algorithm-correctness theorem, and **139 modules that are merely
`Tot`** — out of 194 analysed. Zero active admissions, zero
`--lax`/`--admit_smt_queries` regions, 143 active `assume val`
declarations (iron rule #3 classifies each as an acknowledged gap with
an issue or an allowed realisation).

The short version, in the review's own framing: RDF simple entailment is
proved. The syntax parsers, the canonicaliser, the RDFS closure beyond
rdfs2, and the `rdf-mt` harness are implemented in F\* (except the last)
and measured against the official suites. Those are different claims and
this page will not merge them.

## Where the numbers live

- Live scores and history: [test-results dashboard]({{ '/test-results/' | url }}).
- Per-module assurance: [assurance inventory]({{ '/web/conformance/assurance-inventory/' | url }}).
- Per-suite disposition ledger:
  [`docs/claude-rules/w3c-completeness-ledger.md`](https://github.com/danbri/factoidal/blob/claude/main/docs/claude-rules/w3c-completeness-ledger.md).
- Tracking issues: [#305](https://github.com/danbri/factoidal/issues/305)
  (RDF 1.2 / SPARQL 1.2 epic, phase P9 is RDF 1.2 semantics),
  [#313](https://github.com/danbri/factoidal/issues/313) (claim
  discipline), [#324](https://github.com/danbri/factoidal/issues/324)
  (the conditional-soundness witness),
  [#325](https://github.com/danbri/factoidal/issues/325) (parser
  soundness on non-ASCII input and the empty-parse guard).
- How the pieces work, with runnable cells:
  [triples and Turtle from first principles]({{ '/web/hub/01-triples-rdf-from-first-principles/' | url }}),
  [canonical graphs (RDFC-1.0)]({{ '/web/hub/08-canonical-graphs-rdfc10/' | url }}),
  [RDF 1.2 triple terms]({{ '/web/hub/31-rdf-1-2-triple-terms/' | url }}).
