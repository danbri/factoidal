module SPARQL.QuerySpec

open RDF.CoreSpec

// SPARQL Query Language core concepts.
//
// Bucket: CORE SPEC.
//
// This module names the algebraic/query concepts laid out by SPARQL. The
// existing `SPARQL11.Algebra` file still contains the executable evaluator;
// this file is the readable target shape for the normative/query side.

type variable = string

type binding = variable * term
type solution_mapping = collection binding
type solution_set = collection solution_mapping

type pattern_term =
  | PatternVar  : variable -> pattern_term
  | PatternTerm : term -> pattern_term

type pattern_subject =
  | PatternSubjectVar : variable -> pattern_subject
  | PatternSubject    : subject -> pattern_subject

type pattern_predicate =
  | PatternPredicateVar : variable -> pattern_predicate
  | PatternPredicate    : predicate -> pattern_predicate

noeq type triple_pattern = {
  ps : pattern_subject;
  pp : pattern_predicate;
  po : pattern_term;
}

type bgp = collection triple_pattern

// A deliberately small algebra spine. It is enough to state the spec shape
// without mixing in parser state, storage search, or extraction shortcuts.
noeq type algebra =
  | BGP      : bgp -> algebra
  | Join     : algebra -> algebra -> algebra
  | Union    : algebra -> algebra -> algebra
  | LeftJoin : algebra -> algebra -> algebra
  | Filter   : string -> algebra -> algebra
  | Project  : collection variable -> algebra -> algebra
  | Distinct : algebra -> algebra
  | Slice    : offset:option nat -> limit:option nat -> algebra -> algebra

let algebra_eval_relation (_:dataset) (_:algebra) (_:solution_set) : proposition =
  True
