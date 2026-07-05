module RDF.Indexed

// Every definition lives in RDF.Indexed.fsti (transparent `let`s —
// see that file's banner for why, and for the cyclic-dependency
// finding that shaped this module's scope). Nothing further belongs
// here. Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.3/§3.3 step 3.
//
// Full history (moved here 2026-07-05 when the .fsti banner was
// trimmed per the owner's reading-order critique — see
// skills/fstar-module-style/SKILL.md's ".fsti reading-order
// convention"):
//
// Step 3 landed only the generic association-list "bucket map"
// plumbing (`bucket_map`, `bucket_lookup`, `bucket_replace`,
// `bucket_push`, `build_bucket`), because the RDF-specific glue that
// instantiates it at `triple` (`indexed_graph` itself, `subject_to_key`,
// `term_to_key_opt`, `find_objects_indexed`/`find_subjects_indexed`,
// `add_triple_to_indexes`, `build_indexed`) pattern-matches on
// `triple`/`subject`/`rdf_term`, which at that point still lived in
// RDF.Graph.Executable.fst alongside the RDFS/OWL-RL closure rules
// that also consume `indexed_graph` — opening RDF.Graph.Executable
// from here for the types, while it opened this module back for the
// closure rules' `indexed_graph` parameter, would have been a cyclic
// module dependency.
//
// Step 5 (RDF.Term/RDF.Triple/RDF.Graph split) dissolved that cycle:
// `triple`/`subject`/`rdf_term` now live in their own modules, so step
// 6 (RDFS.Closure/OWL.Closure extraction) folded the RDF-specific glue
// in here as planned. `build_indexed` takes a plain `list triple` (not
// `RDF.Graph.rdf_graph`, a transparent alias for the same type)
// specifically so this module still does NOT need to open RDF.Graph —
// its only dependencies are RDF.Term (`subject`, `rdf_term`, `wf_iri`)
// and RDF.Triple (`triple`), keeping the dependency direction one-way
// (RDF.Graph / RDFS.Closure / OWL.Closure all depend on RDF.Indexed,
// never the reverse).
