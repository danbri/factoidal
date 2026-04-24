module OWL.QueryEval

// Thin F* wiring layer that composes OWL.QueryRewrite.rewrite_query
// (Phase 3: flat query-CE rewriter for owl:intersectionOf / owl:unionOf)
// with SPARQL11.Algebra's top-level query evaluators.
//
// WHY A SEPARATE MODULE:
//   OWL.QueryRewrite opens SPARQL11.Algebra (it needs the query AST
//   types). SPARQL11.Algebra therefore cannot `open OWL.QueryRewrite`
//   without creating a module cycle (F* reports "Recursive dependency
//   on module SPARQL11.Algebra.fst" and refuses to build). The natural
//   place for the composition is a downstream module that imports both;
//   that is this module.
//
// WHAT IT DOES:
//   For each top-level query form (SELECT, CONSTRUCT, ASK) we expose an
//   `_owl` variant that first applies `rewrite_query` and then hands
//   the rewritten AST to the existing evaluator. The rewriter is a
//   no-op for queries that contain no flat-CE shape (see Section 9 of
//   OWL.QueryRewrite — `rewrite_ggp` structurally preserves every
//   constructor; only `GP_BGP` nodes with a recognised CE marker
//   change), so it is safe to apply unconditionally.
//
// TARGET TESTS (SPARQL 1.1 entailment suite):
//   simple 1, simple 4, paper-sparqldl-Q2.
//
// This module contains NO RDF/SPARQL semantic logic of its own —
// it is pure forward-reference wiring (rule #10 compliant).

open RDF.Graph.Executable
open SPARQL11.Algebra
open OWL.QueryRewrite

// SELECT evaluator with OWL-DL flat-CE rewriting applied first.
let eval_select_query_owl (q : query) (g : rdf_graph) (ds : rdf_dataset)
  : solution_sequence =
  eval_select_query (rewrite_query q) g ds

// ASK evaluator with OWL-DL flat-CE rewriting applied first.
let eval_ask_query_owl (q : query) (g : rdf_graph) (ds : rdf_dataset) : bool =
  eval_ask_query (rewrite_query q) g ds

// CONSTRUCT evaluator with OWL-DL flat-CE rewriting applied first.
let eval_construct_query_owl (q : query) (g : rdf_graph) (ds : rdf_dataset)
  : list triple =
  eval_construct_query (rewrite_query q) g ds
