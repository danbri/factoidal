module RDF.Term

// Every definition lives in RDF.Term.fsti (transparent `let`s/`type`s —
// see that file's banner for the human-first skim contract). Nothing
// further belongs here. Per docs/designissues/2026-07-05-foundational-
// core-refactor.md §2.1/§3.3 step 5.
//
// Full history (moved here 2026-07-05 when the .fsti banner was
// trimmed to <=10 lines per the owner's reading-order critique —
// skills/fstar-module-style/SKILL.md's ".fsti reading-order
// convention"):
//
// This is the tree's THIRD `.fsti` (after RDF.Vocabulary and
// RDF.Indexed) and the first written for a human reader before a
// compiler: one RDF concept per block, a one-line prose definition
// citing RDF 1.1 Concepts (https://www.w3.org/TR/rdf11-concepts/) §3,
// then the F* type or function that realizes it.
//
// Every declaration in the .fsti is a *transparent* `let`/`type` (not
// an abstract `val`), same discipline as RDF.Vocabulary.fsti and
// RDF.Indexed.fsti: 53+ modules pattern-match directly on `T_IRI`/
// `S_IRI`/etc., and plain transparent variants are also what extracts
// cleanest to C via KaRaMeL. Hiding these behind a signature would
// force every call site through accessor functions for no correctness
// gain (design doc §2.9, Open decision 3) — revisit only if a genuine
// abstraction need appears.
//
// This is a copy-move from RDF.Graph.Executable.fst lines 1-159 (plus
// the xsd:*/rdf:langString term-algebra constants at lines 36-50,
// which RDF.Vocabulary.fsti's own banner already earmarks for "the
// future RDF.Term module" rather than the RDFS/OWL vocabulary table)
// — no new proof obligations, no behavior change.
//
// Deliberately NOT here (still assigned elsewhere, so a reader isn't
// left wondering where they went):
//   - `datatype_value_eq` (XSD value-space equality) and the two
//     lexical-normalization helpers it depends on — `XSD.Datatypes.fst`'s
//     job per docs/designissues/2026-07-05-xsd-datatypes-module.md
//     §Migration order item 1.
//   - `add_triple_if_new`/`add_triple_unchecked` and every other graph
//     operation (`graph_add`, `graph_remove`, `find_by_subject`, the
//     `rename_*_bnodes` family, `graph_bnodes`) — those stay in
//     `RDF.Graph.Executable.fst` for now. This slice moves only the
//     type tier + its decidable-equality/reflexivity lemmas (design
//     doc §2.1's literal scope); the remaining accessor/algorithm
//     functions are a candidate for a later, separately-gated slice,
//     same "narrower-than-planned, ship what's achievable" call step 3
//     made for `RDF.Indexed`.
//   - The `indexed_graph`/bucket-map acceleration structure
//     (`RDF.Indexed.fst`) and the RDFS/OWL-RL closure rules
//     (`RDFS.Closure`/`OWL.Closure`, design doc step 6) — both still
//     consume these types via `RDF.Graph.Executable.fst`'s shim.
//
// Reading-order restructure (2026-07-05, owner critique): the .fsti
// used to open the IRI concept with `string_has_colon_from`'s
// multi-line fuel recursion three lines in. That machinery now sits
// in a labelled "Preamble" block ahead of the Concepts section (F*
// transparent `let`s can't forward-reference `is_iri`, so it can't
// move to the bottom Appendix); the xsd:* constants, equality
// functions, and reflexivity lemmas — none of them a new RDF concept —
// moved to a labelled "Appendix: mechanical definitions" block at the
// bottom. No semantic change; reordering + comment moves only.
