open Prims
type test_kind =
  | TK_Eval 
  | TK_NegEval 
  | TK_Map 
  | TK_Unknown 
let uu___is_TK_Eval (projectee : test_kind) : Prims.bool=
  match projectee with | TK_Eval -> true | uu___ -> false
let uu___is_TK_NegEval (projectee : test_kind) : Prims.bool=
  match projectee with | TK_NegEval -> true | uu___ -> false
let uu___is_TK_Map (projectee : test_kind) : Prims.bool=
  match projectee with | TK_Map -> true | uu___ -> false
let uu___is_TK_Unknown (projectee : test_kind) : Prims.bool=
  match projectee with | TK_Unknown -> true | uu___ -> false
let rdfc_ns : Prims.string= "https://w3c.github.io/rdf-canon/tests/vocab#"
let rdfc_eval_test : Prims.string=
  "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10EvalTest"
let rdfc_neg_eval_test : Prims.string=
  "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10NegativeEvalTest"
let rdfc_map_test : Prims.string=
  "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10MapTest"
let rdfc_hash_algorithm : Prims.string=
  "https://w3c.github.io/rdf-canon/tests/vocab#hashAlgorithm"
let kind_of_iri (iri : Prims.string) : test_kind=
  if iri = rdfc_eval_test
  then TK_Eval
  else
    if iri = rdfc_neg_eval_test
    then TK_NegEval
    else if iri = rdfc_map_test then TK_Map else TK_Unknown
let kind_label (k : test_kind) : Prims.string=
  match k with
  | TK_Eval -> "Eval"
  | TK_NegEval -> "NegEval"
  | TK_Map -> "Map"
  | TK_Unknown -> "Unknown"
