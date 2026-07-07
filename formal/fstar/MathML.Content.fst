module MathML.Content

// Content MathML front-end. THIN layer over Math.Expr: it maps a
// Content MathML xml_node tree (parsed by Parser.XML — iron rule #1/#4,
// this module never re-parses XML syntax) into a Math.Expr.expr, then
// reuses Math.Expr.eval to compute an exact result. All arithmetic, the
// exact value type, number-literal parsing, the function-name dispatch,
// and the evaluator live in Math.Expr (the CAS-agnostic core); the only
// MathML-specific knowledge here is:
//   * the Content MathML element vocabulary (<apply>/<cn>/<ci>/
//     <csymbol>/<sep/>/<degree>), and
//   * the MathML-operator-element -> Math.Expr-function-name table
//     (mathml_op_name / canonical_op).
//
// Presentation MathML is NOT rendered here — browsers render it
// natively. mathml_kind_of only classifies a tree as Content vs
// Presentation so a caller can dispatch.

open FStar.String
open FStar.List.Tot
open Parser.XML
open Math.Expr

(* ================================================================ *)
(* MathML / XML navigation helpers                                   *)
(* ================================================================ *)

// Strip an XML namespace prefix: keep the substring after the LAST ':'.
let local_name (tag:string) : string =
  let rec after_colon (l:list FStar.Char.char) (acc:list FStar.Char.char)
    : Tot (list FStar.Char.char) (decreases l) =
    match l with
    | [] -> List.Tot.rev acc
    | c :: rest -> if c = ':' then after_colon rest [] else after_colon rest (c :: acc)
  in
  String.string_of_list (after_colon (String.list_of_string tag) [])

let is_element (n:xml_node) : bool = XElement? n

let rec element_children_only (nodes:list xml_node) : Tot (list xml_node) (decreases nodes) =
  match nodes with
  | [] -> []
  | n :: rest -> if is_element n then n :: element_children_only rest
                 else element_children_only rest

let first_element (nodes:list xml_node) : option xml_node =
  match element_children_only nodes with
  | e :: _ -> Some e
  | [] -> None

// Qualifier elements are Content MathML schemata (degree, logbase,
// bound-variable, limits, conditions) that are NOT plain operands.
let is_qualifier (n:xml_node) : bool =
  match n with
  | XElement tag _ _ ->
    let ln = local_name tag in
    ln = "degree" || ln = "logbase" || ln = "bvar" ||
    ln = "lowlimit" || ln = "uplimit" || ln = "condition" ||
    ln = "domainofapplication" || ln = "interval" || ln = "momentabout"
  | _ -> false

let rec drop_qualifiers (nodes:list xml_node) : Tot (list xml_node) (decreases nodes) =
  match nodes with
  | [] -> []
  | n :: rest -> if is_qualifier n then drop_qualifiers rest
                 else n :: drop_qualifiers rest

let rec find_local (name:string) (nodes:list xml_node) : Tot (option xml_node) (decreases nodes) =
  match nodes with
  | [] -> None
  | n :: rest ->
    (match n with
     | XElement tag _ _ -> if local_name tag = name then Some n else find_local name rest
     | _ -> find_local name rest)

(* ================================================================ *)
(* cn literal parsing (integer / real / rational via <sep/>)         *)
(* ================================================================ *)

// Split a cn element's children at a <sep/> element into the text
// before and after (used for type="rational" a<sep/>b).
let rec split_at_sep (children:list xml_node)
                     (before:list FStar.Char.char)
  : Tot (list FStar.Char.char & option (list FStar.Char.char)) (decreases children) =
  match children with
  | [] -> (List.Tot.rev before, None)
  | n :: rest ->
    (match n with
     | XElement tag _ _ ->
       if local_name tag = "sep"
       then (List.Tot.rev before, Some (String.list_of_string (text_content (XElement "wrap" [] rest))))
       else split_at_sep rest before
     | XText t -> split_at_sep rest (List.Tot.rev (String.list_of_string t) @ before)
     | _ -> split_at_sep rest before)

// A <cn> element -> exact value (delegating all number parsing to
// Math.Expr.parse_decimal / m_div).
let eval_cn_value (attrs:list xml_attribute) (children:list xml_node) : mvalue =
  let ty = match find_attr "type" attrs with Some t -> t | None -> "real" in
  if ty = "rational" then
    let (num_cs, den_opt) = split_at_sep children [] in
    (match den_opt with
     | None -> parse_decimal (String.string_of_list num_cs)
     | Some den_cs ->
       let nv = parse_decimal (String.string_of_list num_cs) in
       let dv = parse_decimal (String.string_of_list den_cs) in
       m_div nv dv)
  else
    // integer / real / decimal / e-notation: the concatenated text
    parse_decimal (text_content (XElement "wrap" [] children))

(* ================================================================ *)
(* MathML-operator-element -> Math.Expr-function-name table          *)
(*                                                                   *)
(* Content MathML names its arithmetic/relational operators by empty  *)
(* elements (<plus/>, <times/>, ...) or <csymbol> text. The names     *)
(* below are the domain-neutral function names Math.Expr.apply_fn     *)
(* dispatches on. Most are identity; the mapping is made explicit so   *)
(* the vocabulary knowledge lives here, not in the core.              *)
(* ================================================================ *)

let canonical_op (ln:string) : string =
  match ln with
  | "plus" -> "plus"       | "times" -> "times"
  | "minus" -> "minus"     | "divide" -> "divide"
  | "power" -> "power"     | "root" -> "root"
  | "abs" -> "abs"         | "quotient" -> "quotient"
  | "rem" -> "rem"         | "factorial" -> "factorial"
  | "gcd" -> "gcd"         | "max" -> "max"           | "min" -> "min"
  | "eq" -> "eq"           | "neq" -> "neq"
  | "lt" -> "lt"           | "gt" -> "gt"
  | "leq" -> "leq"         | "geq" -> "geq"
  | other -> other

// The operator name of an <apply>: the first element child's local
// name (mapped through canonical_op), or, for <csymbol>...</csymbol>,
// its text content.
let mathml_op_name (opnode:xml_node) : string =
  match opnode with
  | XElement tag _ _ ->
    let ln = local_name tag in
    if ln = "csymbol" then canonical_op (trim_str (text_content opnode))
    else canonical_op ln
  | _ -> ""

(* ================================================================ *)
(* Content MathML tree -> Math.Expr.expr                             *)
(* ================================================================ *)

let rec mathml_to_expr (n:xml_node) (fuel:nat)
  : Tot (option expr) (decreases %[fuel; 0])
=
  if fuel = 0 then None
  else
    match n with
    | XElement tag attrs children ->
      let ln = local_name tag in
      if ln = "cn" then Some (value_to_lit (eval_cn_value attrs children))
      else if ln = "ci" then Some (E_Sym (trim_str (text_content n)))
      else if ln = "csymbol" then Some (E_Sym (trim_str (text_content n)))
      else if ln = "true" then Some (E_Bool true)
      else if ln = "false" then Some (E_Bool false)
      else if ln = "math" || ln = "cerror" then
        (match first_element children with
         | Some e -> mathml_to_expr e (fuel - 1)
         | None -> None)
      else if ln = "apply" then
        (match element_children_only children with
         | [] -> None
         | opnode :: rest ->
           let op = mathml_op_name opnode in
           let arg_nodes = drop_qualifiers rest in
           (match mathml_to_expr_list arg_nodes (fuel - 1) with
            | None -> None
            | Some arglist ->
              if op = "root" then
                (match find_local "degree" rest with
                 | Some d ->
                   (match first_element (element_children d) with
                    | Some de ->
                      (match mathml_to_expr de (fuel - 1) with
                       | Some dexpr -> Some (E_App "root" (dexpr :: arglist))
                       | None -> Some (E_App "root" arglist))
                    | None -> Some (E_App "root" arglist))
                 | None -> Some (E_App "root" arglist))
              else Some (E_App op arglist)))
      else
        // Unknown element: a nullary function node that Math.Expr.eval
        // reports as an unsupported function (undefined), not a guess.
        Some (E_App ln [])
    | _ -> None

and mathml_to_expr_list (ns:list xml_node) (fuel:nat)
  : Tot (option (list expr)) (decreases %[fuel; 1 + List.Tot.length ns])
=
  match ns with
  | [] -> Some []
  | hd :: tl ->
    (match mathml_to_expr hd fuel with
     | None -> None
     | Some e ->
       (match mathml_to_expr_list tl fuel with
        | None -> None
        | Some es -> Some (e :: es)))

(* ================================================================ *)
(* Entry points                                                      *)
(* ================================================================ *)

// Evaluate a document: unwrap an outer <math> to its first expression
// element, map to Math.Expr, then evaluate exactly.
let eval_doc (env:list (string & mvalue)) (root:xml_node) : mvalue =
  let start =
    match root with
    | XElement tag _ children ->
      if local_name tag = "math" then
        (match first_element children with Some e -> e | None -> root)
      else root
    | _ -> root
  in
  match mathml_to_expr start eval_fuel with
  | Some e -> eval env e eval_fuel
  | None -> MV_Undef "unmappable-mathml"

// Convenience: evaluate with a raw (name, numeric-string) environment.
let eval_doc_env (pairs:list (string & string)) (root:xml_node) : mvalue =
  eval_doc (mk_env pairs) root

// Re-exported for the runner's stable API (all logic is Math.Expr's).
let value_to_string (v:mvalue) : string = Math.Expr.value_to_string v
let value_reason (v:mvalue) : string = Math.Expr.value_reason v

(* ================================================================ *)
(* Presentation vs Content MathML detection                          *)
(* ================================================================ *)

type mathml_kind =
  | MK_Content
  | MK_Presentation
  | MK_Unknown

let content_vocab (ln:string) : bool =
  ln = "apply" || ln = "cn" || ln = "ci" || ln = "csymbol" ||
  ln = "bind" || ln = "bvar" || ln = "cbytes" || ln = "cs" ||
  ln = "cerror" || ln = "share"

let presentation_vocab (ln:string) : bool =
  ln = "mi" || ln = "mo" || ln = "mn" || ln = "mrow" || ln = "mfrac" ||
  ln = "msqrt" || ln = "mroot" || ln = "msup" || ln = "msub" ||
  ln = "msubsup" || ln = "mtable" || ln = "mtr" || ln = "mtd" ||
  ln = "mtext" || ln = "mspace" || ln = "mover" || ln = "munder" ||
  ln = "munderover" || ln = "mfenced" || ln = "mpadded" || ln = "mstyle"

// tree_has: does any element in the tree satisfy pred on its local name?
let rec tree_has (pred:(string -> bool)) (n:xml_node) (fuel:nat)
  : Tot bool (decreases %[fuel; 0])
=
  if fuel = 0 then false
  else
    match n with
    | XElement tag _ children ->
      if pred (local_name tag) then true
      else tree_has_list pred children (fuel - 1)
    | _ -> false

and tree_has_list (pred:(string -> bool)) (ns:list xml_node) (fuel:nat)
  : Tot bool (decreases %[fuel; 1 + List.Tot.length ns])
=
  match ns with
  | [] -> false
  | hd :: tl -> if tree_has pred hd fuel then true else tree_has_list pred tl fuel

let mathml_kind_of (root:xml_node) : mathml_kind =
  if tree_has content_vocab root eval_fuel then MK_Content
  else if tree_has presentation_vocab root eval_fuel then MK_Presentation
  else MK_Unknown
