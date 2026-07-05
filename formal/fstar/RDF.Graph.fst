module RDF.Graph

// Every definition lives in RDF.Graph.fsti (transparent `let`s/
// `type`s — see that file's banner). Nothing further belongs here.
// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.2/§3.3 step 5.
//
// Full history (moved here 2026-07-05 when the .fsti banner was
// trimmed per the owner's reading-order critique — see
// skills/fstar-module-style/SKILL.md's ".fsti reading-order
// convention"): a copy-move from RDF.Graph.Executable.fst (the
// `rdf_graph`/`named_graph`/`rdf_dataset` types + `empty_graph`/
// `empty_dataset`/`lookup_named_graph`), no behavior change.
//
// Step 5's original banner predicted `graph_add`/`find_objects`/
// `find_subjects`/`graph_dedup_sort`/etc. moving here as a later,
// separately-gated slice with "touches nothing step 6 needs." That
// prediction did not hold: step 6 (RDFS.Closure/OWL.Closure
// extraction) needs a handful of these to stay reachable WITHOUT
// creating a cycle back through RDF.Graph.Executable.fst
// (RDFS.Closure/OWL.Closure cannot `open RDF.Graph.Executable` — that
// file will `include` them back). The minimal subset the closure code
// actually calls moved into the .fsti's Appendix: `mem_triple`,
// `graph_add`, `graph_len`, `subject_to_term`, `term_to_subject`,
// `add_triple_if_new`, `add_triple_unchecked`, `add_triples_if_new`,
// and the dedup path (`term_to_key_total`/`triple_to_key`/
// `triple_cmp`/`dedup_sorted_aux`/`graph_dedup_sort`).
//
// Deliberately still NOT here (not needed by step 6, no external
// `.fst` caller found via grep beyond RDF.Graph.Executable.fst's own
// remaining code, which still reaches them unqualified via `include
// RDF.Graph`): `graph_add_unchecked`/`graph_remove`/`graph_union`/
// `graph_finalise`/`dataset_finalise`, `find_by_subject`/
// `find_by_predicate`, `find_objects`/`find_subjects` (naive,
// non-indexed — used by ShEx.Validation/Tableau/SHACL.Validation/etc.
// but not by the closure rules, which use the indexed variants),
// `graph_bnodes`, the `rename_*_bnodes` family, `lemma_mem_triple_append`/
// `lemma_remove_absent`. They stay in RDF.Graph.Executable.fst for now.
