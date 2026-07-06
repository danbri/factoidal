module ShEx.SchemaEq

// ============================================================================
// Structural equality over ShEx.Schema.fst's `shex_schema` AST, used by the
// ShExC-vs-ShExJ differential oracle (bin/shex-runner --differential):
// parse a vendored .shex fixture with Parser.ShExC.parse_shexc_schema,
// decode its .json twin with ShEx.Schema.decode_shex_schema, and check the
// two trees are the same schema. Per iron rule #11 / anti-pattern #15 this
// comparison is semantic logic and belongs in F*, not in the OCaml runner
// glue -- the runner only calls `shex_schema_equal` and reports pass/fail.
//
// Normalization policy (explicit, since "modulo ordering" needs to say
// exactly which orderings are irrelevant):
//   - NodeConstraint "values" (nc_values): the ShExJ grammar defines this
//     as a set, not a sequence (shex.io/shex-semantics's own prose: "an
//     array of NodeConstraint values" with no ordering significance to
//     validation) -- compared as a MULTISET (permutation-tolerant).
//   - Shape "extra" (sh_extra): a set of predicates -- MULTISET.
//   - Shape "extends" (sh_extends): compared as a MULTISET (a shape's
//     EXTENDS clauses are logically a conjunction of independent parent
//     shapes; no vendored fixture's declaration order carries meaning
//     beyond "which parents", and a hand-authored ShExJ twin has no
//     obligation to preserve ShExC's left-to-right EXTENDS order).
//   - StemRange "exclusions": a set of excluded values/stems -- MULTISET.
//   - NodeConstraint numeric facets (mininclusive/maxinclusive/
//     minexclusive/maxexclusive): ShEx.Schema.fst's own header banner
//     documents these as kept VERBATIM lexeme strings (never numerically
//     parsed at decode time), but the vendored corpus's ShExC source and
//     its hand/tool-generated ShExJ twin frequently write the SAME value
//     with different lexical form (`5.5E0` in the .shex vs `5.5` in the
//     .json; `0E0` vs `0.0`) -- compared by DECIMAL VALUE equality via
//     SPARQL11.Algebra.parse_double_to_scaled, not string equality.
//   - Everything else (AND/OR branch order, EachOf/OneOf expression
//     order, annotations, semActs, tripleConstraint field order) is
//     compared POSITIONALLY (order-sensitive) -- these are grammar
//     productions where the corpus's own ShExC/.json twins are written
//     in matching textual order, and reordering AND/OR branches or
//     EachOf members is not a semantically-neutral operation in general
//     (side effects via semActs, or shapes with the same signature but
//     different validation outcomes under NOT/annotation-order-sensitive
//     tooling), so no normalization is applied there.
// ============================================================================

open FStar.String
open FStar.List.Tot
open ShEx.Schema
open SPARQL11.Algebra

// Cross-multiplied scaled-decimal comparison: `(m1, s1)` denotes
// `m1 / 10^s1`; two such pairs denote the same value iff
// `m1 * 10^s2 = m2 * 10^s1` (avoids floating point entirely, and doesn't
// care that the two scales differ -- e.g. (55,1) "5.5" vs (550,2) "5.50").
let scaled_eq (mant_a: int) (scale_a: nat) (mant_b: int) (scale_b: nat) : bool =
  if scale_a <= scale_b
  then (op_Multiply mant_a (pow10 (scale_b - scale_a))) = mant_b
  else (op_Multiply mant_b (pow10 (scale_a - scale_b))) = mant_a

// Two numeric-facet lexemes denote the same decimal value. Falls back to
// plain string equality when either side fails to parse as a (decimal or
// double/E-notation) number -- an honest "can't prove equal, don't crash"
// rather than silently treating unparseable lexemes as always-different
// OR always-equal.
let numeric_lexeme_eq (a b: string) : bool =
  match parse_double_to_scaled a, parse_double_to_scaled b with
  | Some (mant_a, scale_a), Some (mant_b, scale_b) -> scaled_eq mant_a scale_a mant_b scale_b
  | _ -> a = b

let opt_numeric_lexeme_eq (a b: option string) : bool =
  match a, b with
  | None, None -> true
  | Some x, Some y -> numeric_lexeme_eq x y
  | _ -> false

(* ---- small option/string equality lifts ---- *)

let opt_str_eq (a b: option string) : bool =
  match a, b with
  | None, None -> true
  | Some x, Some y -> x = y
  | _ -> false

let opt_int_eq (a b: option int) : bool =
  match a, b with
  | None, None -> true
  | Some x, Some y -> x = y
  | _ -> false

(* ---- multiset (permutation-tolerant) list equality ---- *)

// Removes the first element of `xs` equal to `x` (per `eq`), returning
// None if no such element exists.
let rec remove_one (#a: Type) (eq: a -> a -> bool) (x: a) (xs: list a)
  : Tot (option (list a)) (decreases xs) =
  match xs with
  | [] -> None
  | hd :: tl -> if eq x hd then Some tl else (match remove_one eq x tl with
                                                | Some tl' -> Some (hd :: tl')
                                                | None -> None)

let rec multiset_eq (#a: Type) (eq: a -> a -> bool) (xs ys: list a)
  : Tot bool (decreases xs) =
  match xs with
  | [] -> (match ys with [] -> true | _ -> false)
  | hd :: tl ->
    (match remove_one eq hd ys with
     | None -> false
     | Some ys' -> multiset_eq eq tl ys')

let string_multiset_eq (xs ys: list string) : bool = multiset_eq (fun a b -> a = b) xs ys

(* ---- leaf types ---- *)

let node_kind_eq (a b: shex_node_kind) : bool = (a = b)

let stem_eq (a b: shex_stem) : bool =
  match a, b with
  | ShexStemWildcard, ShexStemWildcard -> true
  | ShexStemPlain x, ShexStemPlain y -> x = y
  | _ -> false

let object_value_eq (a b: shex_object_value) : bool =
  match a, b with
  | ShexOV_Iri x, ShexOV_Iri y -> x = y
  | ShexOV_Literal v1 l1 d1, ShexOV_Literal v2 l2 d2 ->
    v1 = v2 && opt_str_eq l1 l2 && opt_str_eq d1 d2
  | _ -> false

let sem_act_eq (a b: shex_sem_act) : bool =
  a.sa_name = b.sa_name && opt_str_eq a.sa_code b.sa_code

let rec sem_act_list_eq (a b: list shex_sem_act) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> sem_act_eq x y && sem_act_list_eq xs ys
  | _ -> false

let annotation_eq (a b: shex_annotation) : bool =
  a.an_predicate = b.an_predicate && object_value_eq a.an_object b.an_object

let rec annotation_list_eq (a b: list shex_annotation) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> annotation_eq x y && annotation_list_eq xs ys
  | _ -> false

(* ---- value_set_value (self-recursive via exclusions) ----
   The AST type permits arbitrary StemRange-within-exclusions nesting
   (the real ShExJ grammar doesn't, but nothing here relies on that), so
   this mutual group is fuel-threaded rather than structurally recursive
   -- same fuel-parameter idiom ShEx.Schema.fst's own decode_* family and
   Parser.ShExC.fst's grammar functions use. *)

let rec value_set_value_eq (a b: shex_value_set_value) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match a, b with
    | VSV_Value x, VSV_Value y -> object_value_eq x y
    | VSV_IriStem x, VSV_IriStem y -> stem_eq x y
    | VSV_LiteralStem x, VSV_LiteralStem y -> stem_eq x y
    | VSV_LanguageStem x, VSV_LanguageStem y -> stem_eq x y
    | VSV_Language x, VSV_Language y -> x = y
    | VSV_IriStemRange sx ex, VSV_IriStemRange sy ey -> stem_eq sx sy && value_set_value_multiset_eq ex ey (fuel - 1)
    | VSV_LiteralStemRange sx ex, VSV_LiteralStemRange sy ey -> stem_eq sx sy && value_set_value_multiset_eq ex ey (fuel - 1)
    | VSV_LanguageStemRange sx ex, VSV_LanguageStemRange sy ey -> stem_eq sx sy && value_set_value_multiset_eq ex ey (fuel - 1)
    | _ -> false

and value_set_value_multiset_eq (xs ys: list shex_value_set_value) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match xs with
    | [] -> (match ys with [] -> true | _ -> false)
    | hd :: tl ->
      (match remove_one_vsv hd ys (fuel - 1) with
       | None -> false
       | Some ys' -> value_set_value_multiset_eq tl ys' (fuel - 1))

and remove_one_vsv (x: shex_value_set_value) (xs: list shex_value_set_value) (fuel: nat)
  : Tot (option (list shex_value_set_value)) (decreases fuel) =
  if fuel = 0 then None
  else
    match xs with
    | [] -> None
    | hd :: tl ->
      if value_set_value_eq x hd (fuel - 1) then Some tl
      else (match remove_one_vsv x tl (fuel - 1) with Some tl' -> Some (hd :: tl') | None -> None)

let node_constraint_eq (a b: shex_node_constraint) : bool =
  (match a.nc_node_kind, b.nc_node_kind with
   | None, None -> true
   | Some x, Some y -> node_kind_eq x y
   | _ -> false) &&
  opt_str_eq a.nc_datatype b.nc_datatype &&
  value_set_value_multiset_eq a.nc_values b.nc_values 10000 &&
  opt_int_eq a.nc_length b.nc_length &&
  opt_int_eq a.nc_minlength b.nc_minlength &&
  opt_int_eq a.nc_maxlength b.nc_maxlength &&
  opt_str_eq a.nc_pattern b.nc_pattern &&
  opt_str_eq a.nc_flags b.nc_flags &&
  opt_numeric_lexeme_eq a.nc_mininclusive b.nc_mininclusive &&
  opt_numeric_lexeme_eq a.nc_maxinclusive b.nc_maxinclusive &&
  opt_numeric_lexeme_eq a.nc_minexclusive b.nc_minexclusive &&
  opt_numeric_lexeme_eq a.nc_maxexclusive b.nc_maxexclusive &&
  opt_int_eq a.nc_totaldigits b.nc_totaldigits &&
  opt_int_eq a.nc_fractiondigits b.nc_fractiondigits

(* ---- shapeExpr / shape / tripleExpr mutual equality ---- *)

let rec shape_expr_eq (a b: shex_shape_expr) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match a, b with
    | SE_Ref x, SE_Ref y -> x = y
    | SE_ShapeAnd xs, SE_ShapeAnd ys -> shape_expr_list_eq xs ys (fuel - 1)
    | SE_ShapeOr xs, SE_ShapeOr ys -> shape_expr_list_eq xs ys (fuel - 1)
    | SE_ShapeNot x, SE_ShapeNot y -> shape_expr_eq x y (fuel - 1)
    | SE_NodeConstraint x, SE_NodeConstraint y -> node_constraint_eq x y
    | SE_Shape x, SE_Shape y -> shape_eq x y (fuel - 1)
    | SE_ShapeExternal, SE_ShapeExternal -> true
    | _ -> false

and shape_expr_list_eq (a b: list shex_shape_expr) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match a, b with
    | [], [] -> true
    | x :: xs, y :: ys -> shape_expr_eq x y (fuel - 1) && shape_expr_list_eq xs ys (fuel - 1)
    | _ -> false

and shape_eq (a b: shex_shape) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    a.sh_closed = b.sh_closed &&
    string_multiset_eq a.sh_extra b.sh_extra &&
    string_multiset_eq a.sh_extends b.sh_extends &&
    sem_act_list_eq a.sh_semacts b.sh_semacts &&
    annotation_list_eq a.sh_annotations b.sh_annotations &&
    (match a.sh_expression, b.sh_expression with
     | None, None -> true
     | Some x, Some y -> triple_expr_eq x y (fuel - 1)
     | _ -> false)

and triple_expr_eq (a b: shex_triple_expr) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match a, b with
    | TE_Ref x, TE_Ref y -> x = y
    | TE_TripleConstraint x, TE_TripleConstraint y -> triple_constraint_eq x y (fuel - 1)
    | TE_EachOf x, TE_EachOf y -> group_eq x y (fuel - 1)
    | TE_OneOf x, TE_OneOf y -> group_eq x y (fuel - 1)
    | _ -> false

and triple_expr_list_eq (a b: list shex_triple_expr) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    match a, b with
    | [], [] -> true
    | x :: xs, y :: ys -> triple_expr_eq x y (fuel - 1) && triple_expr_list_eq xs ys (fuel - 1)
    | _ -> false

and group_eq (a b: shex_group) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    // gr_id is a purely-internal tripleExprLabel used only for `&label`
    // includes elsewhere in the SAME schema; the differential test
    // compares two independently-authored trees (ShExC-parsed vs
    // ShExJ-decoded) where label spelling is not itself the thing under
    // test -- only the shape it stands for is. Not compared.
    opt_int_eq a.gr_min b.gr_min &&
    opt_int_eq a.gr_max b.gr_max &&
    sem_act_list_eq a.gr_semacts b.gr_semacts &&
    annotation_list_eq a.gr_annotations b.gr_annotations &&
    triple_expr_list_eq a.gr_expressions b.gr_expressions (fuel - 1)

and triple_constraint_eq (a b: shex_triple_constraint) (fuel: nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    a.tc_inverse = b.tc_inverse &&
    a.tc_predicate = b.tc_predicate &&
    a.tc_min = b.tc_min &&
    a.tc_max = b.tc_max &&
    sem_act_list_eq a.tc_semacts b.tc_semacts &&
    annotation_list_eq a.tc_annotations b.tc_annotations &&
    (match a.tc_value_expr, b.tc_value_expr with
     | None, None -> true
     | Some x, Some y -> shape_expr_eq x y (fuel - 1)
     | _ -> false)

let shape_decl_eq (a b: shex_shape_decl) (fuel: nat) : bool =
  a.sd_id = b.sd_id && a.sd_is_abstract = b.sd_is_abstract && shape_expr_eq a.sd_expr b.sd_expr fuel

let rec shape_decl_list_eq (a b: list shex_shape_decl) (fuel: nat) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> shape_decl_eq x y fuel && shape_decl_list_eq xs ys fuel
  | _ -> false

// Same top-level "big fuel" convention Parser.ShExC.fst documents: every
// mutual call decrements by >=1 and no vendored schema comes remotely
// close to exhausting a six-figure budget.
let schema_eq_fuel : nat = 200000

let shex_schema_equal (a b: shex_schema) : bool =
  (match a.sch_start, b.sch_start with
   | None, None -> true
   | Some x, Some y -> shape_expr_eq x y schema_eq_fuel
   | _ -> false) &&
  sem_act_list_eq a.sch_start_acts b.sch_start_acts &&
  string_multiset_eq a.sch_imports b.sch_imports &&
  shape_decl_list_eq a.sch_shapes b.sch_shapes schema_eq_fuel
