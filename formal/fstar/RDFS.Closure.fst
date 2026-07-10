module RDFS.Closure

// Every definition lives in RDFS.Closure.fsti (transparent `let`s —
// see that file's banner for the rule-table cross-reference and the
// cyclic-dependency reasoning that shaped this module's scope). Nothing
// further belongs here. Per docs/designissues/2026-07-05-foundational-
// core-refactor.md §2.4/§3.3 step 6.
// (2026-07-10) rdf_property_axiom_closure added to the .fsti (#236/#287
// strict-runner work, rdfD2 for the ent:RDF regime) — this comment
// bumps the .fst content hash so the extractor re-emits RDFS_Closure.ml
// with the new transparent let (the extractor keys skip decisions on the
// .fst source, not the .fsti).
