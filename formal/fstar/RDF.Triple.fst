module RDF.Triple

// Every definition lives in RDF.Triple.fsti (transparent `let`s/
// `type`s — see that file's banner). Nothing further belongs here.
// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.2/§3.3 step 5.
//
// Full history (moved here 2026-07-05 when the .fsti banner was
// trimmed per the owner's reading-order critique — see
// skills/fstar-module-style/SKILL.md's ".fsti reading-order
// convention"): a copy-move from RDF.Graph.Executable.fst (the
// `triple` record + `triple_eq` + their reflexivity lemma), no
// behavior change. Same transparent-`let` discipline as
// RDF.Term.fsti/RDF.Vocabulary.fsti/RDF.Indexed.fsti — see
// RDF.Term.fsti's banner for why.
//
// Deliberately NOT here: `add_triple_if_new`/`add_triple_unchecked`
// and the rest of the graph-operation surface (`graph_add`,
// `mem_triple`, `rename_triple_bnodes`, …) — those stay in
// RDF.Graph.Executable.fst this slice, same narrower-than-original-
// plan scoping RDF.Term.fsti's banner explains.
