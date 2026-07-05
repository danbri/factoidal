module RDF.Canonical.Manifest

// Test-manifest helpers for the W3C RDF-canon (RDFC-1.0) suite.
// Migrated from rdfc10_runner.ml. Per CLAUDE.md rule #11 OCaml
// glue may not classify test kinds.

type test_kind =
  | TK_Eval
  | TK_NegEval
  | TK_Map
  | TK_Unknown

let rdfc_ns : string = "https://w3c.github.io/rdf-canon/tests/vocab#"

let rdfc_eval_test     : string = "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10EvalTest"
let rdfc_neg_eval_test : string = "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10NegativeEvalTest"
let rdfc_map_test      : string = "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10MapTest"

// 2026-07-05: some manifest entries (e.g. test075c/test075m) declare
// `rdfc:hashAlgorithm "SHA384"` to select a non-default hash primitive
// for RDFC-1.0 §4.4/§4.8. Runner reads this predicate the same way it
// already reads mf:action / mf:result / mf:name (plain literal-object
// lookup); the resulting string is mapped to RDF.Canonical's
// `hash_algorithm` type by `RDF_Canonical.hash_algorithm_of_string`.
let rdfc_hash_algorithm : string = "https://w3c.github.io/rdf-canon/tests/vocab#hashAlgorithm"

let kind_of_iri (iri : string) : Tot test_kind =
  if iri = rdfc_eval_test then TK_Eval
  else if iri = rdfc_neg_eval_test then TK_NegEval
  else if iri = rdfc_map_test then TK_Map
  else TK_Unknown

let kind_label (k : test_kind) : Tot string =
  match k with
  | TK_Eval    -> "Eval"
  | TK_NegEval -> "NegEval"
  | TK_Map     -> "Map"
  | TK_Unknown -> "Unknown"
