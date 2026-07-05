# OWL 2 Functional-Syntax parser — scope + plan (not built yet)

Companion to `docs/designissues/2026-07-03-owl-rl-pe-fails-fix-sketch.md`
§2.7 (option 1). Written per the 2026-07-05 OWL catalog audit; this
doc is the "what it would take" answer — no parser code lands here.

## Tests unlocked

4 catalog entries in `profile-RL.rdf` carry only
`test:fsPremiseOntology` / `test:fsConclusionOntology` (OWL 2
Functional Syntax) with `test:normativeSyntax FUNCTIONAL` and no
`test:rdfXmlPremiseOntology` — `owl_runner.ml` reads only `rdfXml*`
literals (rule #4: parsers belong in F\*) and honestly reports
`SKIP/functional-syntax-only` for each:

- 1 PositiveEntailmentTest: `New-Feature-ObjectPropertyChain-BJP-002`.
- 3 InconsistencyTest: `Plus and Minus Zero are Distinct`,
  `functionality-clash`, `string-integer-clash`.

## Grammar subset actually needed

Inspecting all 4 documents (they are short, hand-written W3C fixtures,
not general OWL 2 FS): `Prefix( pfx = <IRI> )` directives, one
`Ontology( ... )` wrapper, `Declaration(ObjectProperty(:p))` /
`Declaration(DataProperty(:p))` / `Declaration(NamedIndividual(:x))`,
and exactly 5 axiom forms: `TransitiveObjectProperty(:p)`,
`FunctionalDataProperty(:p)`, `DataPropertyRange(:p xsd:T)`,
`DataPropertyAssertion(:p :ind "lit"^^xsd:T)`, and
`ClassAssertion(DataHasValue(:p "lit"^^xsd:T) :ind)`. No class
expressions, no object property expressions, no annotations, no
`SubObjectPropertyOf`/chain axioms beyond the transitive declaration.
This is a small, closed grammar — not general OWL 2 Functional Syntax
(which also has `SubClassOf`, `EquivalentClasses`, restrictions,
punning, etc.) — sized to these 4 fixtures plus reasonable adjacent
forms (declarations for the other 2 entity kinds, a few more axiom
heads) so the module isn't a one-shot hack.

## Module shape

New module `Parser.OWLFunctional.fst`, following the existing
`Parser.<Format>.fst` naming (`Parser.Turtle.fst`, `Parser.RDFXML.fst`)
and the semantic-core/pragmatics split in `skills/fstar-module-style/
SKILL.md`: a tokenizer + recursive-descent parser over the
S-expression-like FS grammar, translating directly to `RDF.Graph.
Executable`'s `rdf_graph`/`triple` type (mirroring how
`Parser.RDFXML.fst` produces triples, not an intermediate OWL AST —
no `OWL.Syntax.fst` needed at this scope). Axiom-to-triple mapping
follows the OWL 2 Mapping to RDF Graphs spec's per-axiom tables (e.g.
`TransitiveObjectProperty(:p)` -> `:p rdf:type owl:TransitiveProperty`).
`.fsti` per project policy once the module stabilizes.

## Wiring

`bin/owl-runner/owl_runner.ml`'s `run_positive_entailment` /
`run_inconsistency_test`: when `info.premise = None` and
`test_syntax_functional` is set, try the new
`Parser_OWLFunctional.parse_functional_syntax` extracted entrypoint on
the raw `test:fsPremiseOntology` literal instead of emitting
`Skip_functional_syntax_only`; same for conclusion literals. Plumbing
only, mirrors the existing rdfXml path.

## Size estimate

Tokenizer + parser + axiom-to-triple emission for the grammar above:
150-250 lines of F\* (comparable to `Parser.NTriples.fst`, the
smallest existing format parser), plus the runner wiring (~20 lines,
`owl_runner.ml` only). One sitting for a subagent; not a multi-day
effort. The `owl_rule_chain_to_transitive` converse rule
`docs/designissues/2026-07-03-owl-rl-pe-fails-fix-sketch.md` §2.7
flags (needed to actually PASS BJP-002, not just parse it) is a
separate ~10-line closure rule in `RDF.Graph.Executable.fst`, filed
as its own follow-up once parsing lands.
