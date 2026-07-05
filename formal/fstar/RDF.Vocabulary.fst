module RDF.Vocabulary

// Every definition lives in RDF.Vocabulary.fsti (transparent `let`s —
// see that file's banner for why). Nothing further belongs here: this
// module has no pragmatics, no algorithm, nothing beyond the constant
// table itself. Per docs/designissues/2026-07-05-foundational-core-
// refactor.md §2.6/§3.3 step 2.
//
// Full exclusion-list history (moved here 2026-07-05 when the .fsti
// banner was trimmed per the owner's reading-order critique — see
// skills/fstar-module-style/SKILL.md's ".fsti reading-order
// convention"):
//
// Deliberately excluded from this module (still assigned to other
// designs' modules, so a reader doesn't wonder where they went):
//   - `xsd:string`/`xsd:integer`/`xsd:decimal`/`xsd:double`/`xsd:boolean`
//     — these are part of the term algebra (`literal`/`wf_literal`
//     construction), not "vocabulary" in the RDFS/OWL sense; they now
//     live in `RDF.Term.fsti` (design doc §2.1, step 5, landed
//     2026-07-05 — previously inline in RDF.Graph.Executable.fst
//     lines 36-50, then a "future module" note here before step 5
//     shipped), not here.
//   - The XSD datatype-hierarchy constants (`xsd_long`,
//     `xsd_nonNegativeInteger`, `xsd_hierarchy_edges`, RDF.Graph.
//     Executable.fst lines ~4007-4098) and the `_iri`-suffixed OWL
//     restriction-vocabulary duplicate block (lines 2216-2283) — both
//     are interleaved with OWL-RL closure code that hasn't moved out
//     of RDF.Graph.Executable.fst yet (design doc step 6). Moving
//     their vocabulary constants here now would require either
//     duplicating the closure code's own copies or creating a
//     dependency cycle (RDF.Vocabulary would need `wf_iri`/`is_iri`
//     from RDF.Graph.Executable, whose closure code would then need to
//     `open RDF.Vocabulary` back). Deferred to when step 6 relocates
//     the closure code that consumes them.
//   - `rdf:first`/`rdf:rest`/`rdf:nil_iri` as separately named at
//     RDF.Graph.Executable.fst lines 3340-3350 (property-chain/list
//     decoding inside the OWL-RL closure section) — same reason.
//   - OWL.QueryRewrite.fst's own `_iri`-suffixed forwarders — out of
//     this slice's territory (a different agent's migration step).
//
// What DID move here (slice 1 of the RDF.Vocabulary consolidation):
//   - RDF.Graph.Executable.fst's section 16 "RDF/RDFS Vocabulary
//     Constants" block (lines 806-876).
//   - OWL.Vocabulary.fst's entire content (class-expression/
//     restriction/cardinality constants + its own rdf:first/rdf:rest/
//     rdf:nil copy).
//   - New: the additional RDF/RDFS terms needed by the
//     `RDF.Vocabulary.Axioms` companion (rdf:subject/predicate/object/
//     value/Statement/Alt/Bag/Seq/List, rdfs:seeAlso/isDefinedBy/
//     comment/label/Container) that previously had no named constant
//     anywhere in the tree (only inline string literals, e.g.
//     RDF.Graph.Executable.fst lines 2708-2710).
