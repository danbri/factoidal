module Parser.XPath

open FStar.String
open FStar.List.Tot
open FStar.Char
open Parser.FastString
open Parser.Combinators

// XPath 1.0 (https://www.w3.org/TR/1999/REC-xpath-19991116/) expression
// parser. Territory note: this module intentionally does NOT open
// Parser.XML — the expression grammar is pure text, the AST here is
// consumed by XPath.Eval.fst which pairs it with Parser.XML's xml_node.
//
// Scope (2026-07-05 xforms-model-program-plan, Stage 1): abbreviated +
// full axis syntax for child/descendant/descendant-or-self/parent/
// self/attribute/ancestor/ancestor-or-self (following/preceding/
// following-sibling/preceding-sibling deferred to Stage 1.5 — see the
// plan doc's Open decision #5); node tests (name, *, prefix:*, text(),
// comment(), node()); predicates; the six comparison operators with
// §3.4 type coercion; +,-,*,div,mod, unary minus; '|' union. Numeric
// literals follow the XPath 1.0 `Number` production exactly (Digits
// ('.' Digits?)? | '.' Digits) — no E-notation, no sign (a leading '-'
// on a literal is UnaryExpr wrapping a Number, per the grammar's own
// UnaryExpr/Number split).
//
// Termination: XPath's grammar is a ~10-level operator-precedence
// cascade (OrExpr..PrimaryExpr) with genuine recursion back to the top
// via parenthesized primaries, predicates, and function-call
// arguments. Every function in the mutually-recursive descent takes an
// explicit `fuel:nat` and every call (both "down a precedence level"
// and "genuinely recursive") passes `fuel - 1`, mirroring Parser.XML's
// fuel idiom (`decreases fuel`, no structural measure attempted across
// this many mutually-recursive levels). `fuel` is threaded from input
// length at the single entry point (`parse_xpath`), never a bare
// constant, per the "fixed fuel constants silently truncate" trap —
// see the module banner's fuel-sizing note below the AST.

(* ================================================================ *)
(* AST                                                               *)
(* ================================================================ *)

type xp_axis =
  | Ax_Child | Ax_Descendant | Ax_DescendantOrSelf
  | Ax_Parent | Ax_Self
  | Ax_Attribute
  | Ax_Ancestor | Ax_AncestorOrSelf

// NT_Name carries the full tag/attribute-name string as stored by
// Parser.XML's xml_node (which does not split QNames — "rdf:Description"
// is one opaque string), so a name test with a prefix ("rdf:Description")
// is just NT_Name "rdf:Description"; only the wildcard-with-prefix form
// ("rdf:*") needs its own constructor, since matching that requires
// prefix-splitting at eval time rather than plain string equality.
type xp_nodetest =
  | NT_Name    : string -> xp_nodetest
  | NT_Prefix  : string -> xp_nodetest   // "prefix:*"
  | NT_Any     : xp_nodetest             // "*"
  | NT_Text    : xp_nodetest             // text()
  | NT_Comment : xp_nodetest             // comment()
  | NT_Node    : xp_nodetest             // node()

type xp_comp_op = | Cmp_Eq | Cmp_Ne | Cmp_Lt | Cmp_Le | Cmp_Gt | Cmp_Ge
type xp_arith_op = | Ar_Add | Ar_Sub | Ar_Mul | Ar_Div | Ar_Mod

noeq type xp_step = {
  step_axis  : xp_axis;
  step_test  : xp_nodetest;
  step_preds : list xp_expr;
}

and xp_expr =
  // Location path. `absolute` = leading '/'. Steps already have any
  // '//' abbreviation desugared into an explicit
  // {Ax_DescendantOrSelf; NT_Node; []} step by the parser (XPath 1.0
  // §2.5: "// is short for /descendant-or-self::node()/").
  | XE_Path       : absolute:bool -> steps:list xp_step -> xp_expr
  // FilterExpr optionally continued by a relative location path
  // (PathExpr ::= FilterExpr | FilterExpr '/' RelativeLocationPath |
  // FilterExpr '//' RelativeLocationPath). Only built when there is at
  // least one predicate or at least one continuation step — a bare
  // PrimaryExpr with neither is returned unwrapped.
  | XE_FilterPath : primary:xp_expr -> preds:list xp_expr -> steps:list xp_step -> xp_expr
  | XE_Union   : xp_expr -> xp_expr -> xp_expr
  | XE_Or      : xp_expr -> xp_expr -> xp_expr
  | XE_And     : xp_expr -> xp_expr -> xp_expr
  | XE_Compare : xp_comp_op -> xp_expr -> xp_expr -> xp_expr
  | XE_Arith   : xp_arith_op -> xp_expr -> xp_expr -> xp_expr
  | XE_Neg     : xp_expr -> xp_expr
  // (mantissa, scale): value = mantissa / 10^scale. See XPath.Eval's
  // Number-semantics banner for why this mirrors, without importing,
  // SPARQL11.Algebra's scaled-decimal promoted-type representation.
  | XE_Number  : int -> nat -> xp_expr
  | XE_Literal : string -> xp_expr
  | XE_VarRef  : string -> xp_expr
  | XE_FunCall : string -> list xp_expr -> xp_expr


(* ================================================================ *)
(* Lexical helpers (ASCII fast path, mirrors Parser.XML's approach)  *)
(* ================================================================ *)

let is_ws (c:char) : bool =
  let code = Char.int_of_char c in
  code = 0x20 || code = 0x09 || code = 0x0A || code = 0x0D

let is_digit_char (c:char) : bool =
  let code = Char.int_of_char c in
  code >= 0x30 && code <= 0x39

let is_name_start_char (c:char) : bool =
  let code = Char.int_of_char c in
  if code < 0x80 then
    (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A) || code = 0x5F
  else code >= 0xC0

let is_name_char (c:char) : bool =
  let code = Char.int_of_char c in
  if code < 0x80 then
    (code >= 0x41 && code <= 0x5A) || (code >= 0x61 && code <= 0x7A) ||
    (code >= 0x30 && code <= 0x39) || code = 0x5F || code = 0x2D || code = 0x2E
  else code >= 0xC0

let skip_ws (input:string) (pos:nat) : nat =
  match ptake_while_pos is_ws input pos with
  | ParseOk _ pos' -> pos'
  | ParseFail _ fpos -> fpos

let peek_char (input:string) (pos:nat) : option char =
  if pos < fs_byte_length input then Some (fs_byte_index input pos) else None

// True iff `pos` is NOT immediately followed by a name character —
// the keyword/word-boundary check ("or" must not match inside
// "orange"). end-of-input counts as a boundary.
let word_boundary_after (input:string) (pos:nat) : bool =
  match peek_char input pos with
  | None -> true
  | Some c -> not (is_name_char c)

// Match a bare-word keyword (must not be followed by a name char).
let match_keyword (kw:string) (input:string) (pos:nat) : option nat =
  match pstring kw input pos with
  | ParseOk _ pos' -> if word_boundary_after input pos' then Some pos' else None
  | ParseFail _ _ -> None

// NCName token: name_start name_char*. None if no name-start char at pos.
let parse_ncname (input:string) (pos:nat) : option (string & nat) =
  match peek_char input pos with
  | Some c ->
    if is_name_start_char c then
      (match ptake_while_pos is_name_char input (pos + 1) with
       | ParseOk rest pos' -> Some (String.concat "" [String.string_of_char c; rest], pos')
       | ParseFail _ _ -> Some (String.string_of_char c, pos + 1))
    else None
  | None -> None

let rec pow10_nat (n:nat) : Tot int (decreases n) =
  if n = 0 then 1 else op_Multiply 10 (pow10_nat (n - 1))

// digits (all ASCII 0-9) -> nat, left to right (most-significant first)
let rec digits_to_nat (input:string) (pos:nat) (endpos:nat) (acc:nat)
  : Tot nat (decreases (if endpos > pos then endpos - pos else 0)) =
  if pos >= endpos then acc
  else
    let c = fs_byte_index input pos in
    let d = Char.int_of_char c - 0x30 in
    let d' = if d < 0 then 0 else d in
    digits_to_nat input (pos + 1) endpos (op_Multiply acc 10 + d')


(* ================================================================ *)
(* Fuel sizing                                                       *)
(* ================================================================ *)

// Grammar depth for this cascade is a small fixed constant (~11
// levels: Or/And/Equality/Relational/Additive/Multiplicative/Unary/
// Union/PathExpr/FilterExpr/PrimaryExpr); genuine nesting (parens,
// predicates, function args) consumes at least 2 input bytes per
// level. `4 * (len+1)` bounds "hops through the cascade" for a single
// top-to-bottom-and-back traversal at every nesting depth the input
// could possibly contain; the flat `+ 64` covers the fixed cascade
// depth for a trivial (near-empty) input. Threaded from input size,
// never a bare constant (extraction-semantics trap #3).
let initial_parse_fuel (input:string) : nat =
  op_Multiply 4 (fs_byte_length input + 1) + 64


(* ================================================================ *)
(* Number and Literal                                                *)
(* ================================================================ *)

// Number ::= Digits ('.' Digits?)? | '.' Digits   (no sign, no E-notation)
let parse_number_lit (input:string) (pos:nat) : option (int & nat & nat) =
  let len = fs_byte_length input in
  let has_int_digit = match peek_char input pos with Some c -> is_digit_char c | None -> false in
  let starts_dot = match peek_char input pos with Some c -> c = '.' | None -> false in
  if not has_int_digit && not starts_dot then None
  else
    let int_end = ptake_while_scan is_digit_char input pos (len - pos + 1) in
    let int_val = digits_to_nat input pos int_end 0 in
    if int_end < len && fs_byte_index input int_end = '.' then
      let frac_start = int_end + 1 in
      let frac_end = ptake_while_scan is_digit_char input frac_start (len - frac_start + 1) in
      let scale = frac_end - frac_start in
      if scale = 0 then
        // "42." — Digits '.' with no fraction digits is still valid
        // per the grammar (`'.' Digits?`).
        Some (int_val, 0, frac_end)
      else
        let frac_val = digits_to_nat input frac_start frac_end 0 in
        Some (op_Multiply int_val (pow10_nat scale) + frac_val, scale, frac_end)
    else if int_end = pos then None // ".": neither an int digit nor dot consumed a fraction digit
    else Some (int_val, 0, int_end)

// Literal ::= '"' [^"]* '"' | "'" [^']* "'"   -- NO escape mechanism.
let parse_string_lit (input:string) (pos:nat) : option (string & nat) =
  match peek_char input pos with
  | Some q ->
    if q = '"' || q = '\'' then
      let len = fs_byte_length input in
      let body_end = fs_find_byte input (Char.int_of_char q) (pos + 1) in
      if body_end < len && body_end >= pos + 1 then Some (fs_byte_sub input (pos + 1) (body_end - pos - 1), body_end + 1)
      else None
    else None
  | None -> None


(* ================================================================ *)
(* Axis / node-type keyword tables                                   *)
(* ================================================================ *)

let axis_of_name (name:string) : option xp_axis =
  if name = "child" then Some Ax_Child
  else if name = "descendant" then Some Ax_Descendant
  else if name = "descendant-or-self" then Some Ax_DescendantOrSelf
  else if name = "parent" then Some Ax_Parent
  else if name = "self" then Some Ax_Self
  else if name = "attribute" then Some Ax_Attribute
  else if name = "ancestor" then Some Ax_Ancestor
  else if name = "ancestor-or-self" then Some Ax_AncestorOrSelf
  else None // following/preceding/(-sibling)/namespace: Stage 1.5, not recognized

let is_nodetype_keyword (name:string) : bool =
  name = "text" || name = "comment" || name = "node" || name = "processing-instruction"

// NodeTest (shared by '@'-prefixed, axis::-prefixed, and default/child
// steps): '*' | NCName ':' '*' | NCName ':' NCName | NodeType '(' ')' |
// bare NCName. Not a recursive-descent function (no Expr involved), so
// no fuel needed — same footing as Parser.XML's non-parsing helpers.
let parse_node_test (input:string) (pos:nat) : option (xp_nodetest & nat) =
  let len = fs_byte_length input in
  match peek_char input pos with
  | Some '*' -> Some (NT_Any, pos + 1)
  | _ ->
    (match parse_ncname input pos with
     | None -> None
     | Some (nm, pos1) ->
       if pos1 < len && fs_byte_index input pos1 = ':' && pos1 + 1 < len && fs_byte_index input (pos1 + 1) = '*' then
         Some (NT_Prefix nm, pos1 + 2)
       else if pos1 < len && fs_byte_index input pos1 = ':' && pos1 + 1 < len && is_name_start_char (fs_byte_index input (pos1 + 1)) then
         (match parse_ncname input (pos1 + 1) with
          | Some (local, pos2) -> Some (NT_Name (String.concat "" [nm; ":"; local]), pos2)
          | None -> None)
       else
         let posws = skip_ws input pos1 in
         if posws < len && fs_byte_index input posws = '(' && is_nodetype_keyword nm then
           if nm = "processing-instruction" then None // unsupported: Stage 1.5
           else
             let posws2 = skip_ws input (posws + 1) in
             if posws2 < len && fs_byte_index input posws2 = ')' then
               let test = if nm = "text" then NT_Text
                          else if nm = "comment" then NT_Comment
                          else NT_Node in
               Some (test, posws2 + 1)
             else None
         else Some (NT_Name nm, pos1))


(* ================================================================ *)
(* Recursive-descent expression parser                               *)
(*                                                                   *)
(* One mutually recursive block covering the full precedence cascade *)
(* (looser to tighter): Or, And, Equality, Relational, Additive,     *)
(* Multiplicative, Unary, Union, PathExpr/FilterExpr/PrimaryExpr,    *)
(* plus LocationPath/Step/Predicate/FunctionArgs. Every function     *)
(* takes an explicit `fuel:nat` and every call — "down a precedence  *)
(* level" or genuinely recursive (parens, predicates, args) — passes *)
(* `fuel - 1`; see the fuel-sizing note above for why this is safe   *)
(* and non-truncating for realistic inputs.                         *)
(* ================================================================ *)

let rec parse_or_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_and_expr input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk lhs pos1 -> parse_or_rest input lhs pos1 (fuel - 1)

and parse_or_rest (input:string) (lhs:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk lhs pos
  else
    let pos1 = skip_ws input pos in
    match match_keyword "or" input pos1 with
    | Some pos2 ->
      (match parse_and_expr input (skip_ws input pos2) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos3 -> parse_or_rest input (XE_Or lhs rhs) pos3 (fuel - 1))
    | None -> ParseOk lhs pos1

and parse_and_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_equality_expr input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk lhs pos1 -> parse_and_rest input lhs pos1 (fuel - 1)

and parse_and_rest (input:string) (lhs:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk lhs pos
  else
    let pos1 = skip_ws input pos in
    match match_keyword "and" input pos1 with
    | Some pos2 ->
      (match parse_equality_expr input (skip_ws input pos2) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos3 -> parse_and_rest input (XE_And lhs rhs) pos3 (fuel - 1))
    | None -> ParseOk lhs pos1

and parse_equality_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_relational_expr input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk lhs pos1 -> parse_equality_rest input lhs pos1 (fuel - 1)

and parse_equality_rest (input:string) (lhs:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk lhs pos
  else
    let pos1 = skip_ws input pos in
    let len = fs_byte_length input in
    if pos1 + 1 < len && fs_byte_index input pos1 = '!' && fs_byte_index input (pos1 + 1) = '=' then
      (match parse_relational_expr input (skip_ws input (pos1 + 2)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_equality_rest input (XE_Compare Cmp_Ne lhs rhs) pos2 (fuel - 1))
    else if pos1 < len && fs_byte_index input pos1 = '=' then
      (match parse_relational_expr input (skip_ws input (pos1 + 1)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_equality_rest input (XE_Compare Cmp_Eq lhs rhs) pos2 (fuel - 1))
    else ParseOk lhs pos1

and parse_relational_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_additive_expr input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk lhs pos1 -> parse_relational_rest input lhs pos1 (fuel - 1)

and parse_relational_rest (input:string) (lhs:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk lhs pos
  else
    let pos1 = skip_ws input pos in
    let len = fs_byte_length input in
    if pos1 + 1 < len && fs_byte_index input pos1 = '<' && fs_byte_index input (pos1 + 1) = '=' then
      (match parse_additive_expr input (skip_ws input (pos1 + 2)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_relational_rest input (XE_Compare Cmp_Le lhs rhs) pos2 (fuel - 1))
    else if pos1 + 1 < len && fs_byte_index input pos1 = '>' && fs_byte_index input (pos1 + 1) = '=' then
      (match parse_additive_expr input (skip_ws input (pos1 + 2)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_relational_rest input (XE_Compare Cmp_Ge lhs rhs) pos2 (fuel - 1))
    else if pos1 < len && fs_byte_index input pos1 = '<' then
      (match parse_additive_expr input (skip_ws input (pos1 + 1)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_relational_rest input (XE_Compare Cmp_Lt lhs rhs) pos2 (fuel - 1))
    else if pos1 < len && fs_byte_index input pos1 = '>' then
      (match parse_additive_expr input (skip_ws input (pos1 + 1)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_relational_rest input (XE_Compare Cmp_Gt lhs rhs) pos2 (fuel - 1))
    else ParseOk lhs pos1

and parse_additive_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_multiplicative_expr input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk lhs pos1 -> parse_additive_rest input lhs pos1 (fuel - 1)

and parse_additive_rest (input:string) (lhs:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk lhs pos
  else
    let pos1 = skip_ws input pos in
    let len = fs_byte_length input in
    if pos1 < len && fs_byte_index input pos1 = '+' then
      (match parse_multiplicative_expr input (skip_ws input (pos1 + 1)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_additive_rest input (XE_Arith Ar_Add lhs rhs) pos2 (fuel - 1))
    else if pos1 < len && fs_byte_index input pos1 = '-' then
      (match parse_multiplicative_expr input (skip_ws input (pos1 + 1)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_additive_rest input (XE_Arith Ar_Sub lhs rhs) pos2 (fuel - 1))
    else ParseOk lhs pos1

and parse_multiplicative_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_unary_expr input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk lhs pos1 -> parse_multiplicative_rest input lhs pos1 (fuel - 1)

and parse_multiplicative_rest (input:string) (lhs:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk lhs pos
  else
    let pos1 = skip_ws input pos in
    let len = fs_byte_length input in
    if pos1 < len && fs_byte_index input pos1 = '*' then
      (match parse_unary_expr input (skip_ws input (pos1 + 1)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk rhs pos2 -> parse_multiplicative_rest input (XE_Arith Ar_Mul lhs rhs) pos2 (fuel - 1))
    else
      match match_keyword "div" input pos1 with
      | Some pos2 ->
        (match parse_unary_expr input (skip_ws input pos2) (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk rhs pos3 -> parse_multiplicative_rest input (XE_Arith Ar_Div lhs rhs) pos3 (fuel - 1))
      | None ->
        (match match_keyword "mod" input pos1 with
         | Some pos2 ->
           (match parse_unary_expr input (skip_ws input pos2) (fuel - 1) with
            | ParseFail msg fpos -> ParseFail msg fpos
            | ParseOk rhs pos3 -> parse_multiplicative_rest input (XE_Arith Ar_Mod lhs rhs) pos3 (fuel - 1))
         | None -> ParseOk lhs pos1)

and parse_unary_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    let pos1 = skip_ws input pos in
    if pos1 < fs_byte_length input && fs_byte_index input pos1 = '-' then
      match parse_unary_expr input (pos1 + 1) (fuel - 1) with
      | ParseFail msg fpos -> ParseFail msg fpos
      | ParseOk e pos2 -> ParseOk (XE_Neg e) pos2
    else parse_union_expr input pos1 (fuel - 1)

and parse_union_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_path_expr input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk lhs pos1 -> parse_union_rest input lhs pos1 (fuel - 1)

and parse_union_rest (input:string) (lhs:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk lhs pos
  else
    let pos1 = skip_ws input pos in
    if pos1 < fs_byte_length input && fs_byte_index input pos1 = '|' then
      match parse_path_expr input (pos1 + 1) (fuel - 1) with
      | ParseFail msg fpos -> ParseFail msg fpos
      | ParseOk rhs pos2 -> parse_union_rest input (XE_Union lhs rhs) pos2 (fuel - 1)
    else ParseOk lhs pos1

and parse_path_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    let pos1 = skip_ws input pos in
    let len = fs_byte_length input in
    match peek_char input pos1 with
    | None -> ParseFail "expected an expression" pos1
    | Some '/' -> parse_absolute_location_path input pos1 (fuel - 1)
    | Some '@' ->
      (match parse_node_test input (pos1 + 1) with
       | None -> ParseFail "expected node test after '@'" (pos1 + 1)
       | Some (test, pos2) ->
         (match parse_predicates input pos2 (fuel - 1) with
          | ParseFail msg fpos -> ParseFail msg fpos
          | ParseOk preds pos3 ->
            let first = { step_axis = Ax_Attribute; step_test = test; step_preds = preds } in
            (match parse_location_path_rest input [first] pos3 (fuel - 1) with
             | ParseFail msg fpos -> ParseFail msg fpos
             | ParseOk steps pos4 -> ParseOk (XE_Path false steps) pos4)))
    | Some '*' ->
      (match parse_predicates input (pos1 + 1) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk preds pos2 ->
         let first = { step_axis = Ax_Child; step_test = NT_Any; step_preds = preds } in
         (match parse_location_path_rest input [first] pos2 (fuel - 1) with
          | ParseFail msg fpos -> ParseFail msg fpos
          | ParseOk steps pos3 -> ParseOk (XE_Path false steps) pos3))
    | Some '.' ->
      if pos1 + 1 < len && fs_byte_index input (pos1 + 1) = '.' then
        (match parse_location_path_rest input [{ step_axis = Ax_Parent; step_test = NT_Node; step_preds = [] }] (pos1 + 2) (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk steps pos2 -> ParseOk (XE_Path false steps) pos2)
      else if pos1 + 1 < len && is_digit_char (fs_byte_index input (pos1 + 1)) then
        (match parse_primary_expr input pos1 (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk e pos2 -> parse_filter_suffix input e pos2 (fuel - 1))
      else
        (match parse_location_path_rest input [{ step_axis = Ax_Self; step_test = NT_Node; step_preds = [] }] (pos1 + 1) (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk steps pos2 -> ParseOk (XE_Path false steps) pos2)
    | Some c ->
      if is_name_start_char c then parse_name_lead input pos1 (fuel - 1)
      else
        (match parse_primary_expr input pos1 (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk e pos2 -> parse_filter_suffix input e pos2 (fuel - 1))

and parse_name_lead (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_ncname input pos with
    | None -> ParseFail "expected a name" pos
    | Some (nm, pos1) ->
      let len = fs_byte_length input in
      if pos1 + 1 < len && fs_byte_index input pos1 = ':' && fs_byte_index input (pos1 + 1) = ':' then
        (match axis_of_name nm with
         | None -> ParseFail (String.concat "" ["axis '"; nm; "' not supported (see Stage 1.5)"]) pos
         | Some ax ->
           (match parse_node_test input (pos1 + 2) with
            | None -> ParseFail "expected node test after axis '::'" (pos1 + 2)
            | Some (test, pos2) ->
              (match parse_predicates input pos2 (fuel - 1) with
               | ParseFail msg fpos -> ParseFail msg fpos
               | ParseOk preds pos3 ->
                 let first = { step_axis = ax; step_test = test; step_preds = preds } in
                 (match parse_location_path_rest input [first] pos3 (fuel - 1) with
                  | ParseFail msg fpos -> ParseFail msg fpos
                  | ParseOk steps pos4 -> ParseOk (XE_Path false steps) pos4))))
      else
        let has_qname_local =
          pos1 < len && fs_byte_index input pos1 = ':' &&
          pos1 + 1 < len && (fs_byte_index input (pos1 + 1) = '*' || is_name_start_char (fs_byte_index input (pos1 + 1)))
        in
        if has_qname_local then
          (match parse_node_test input pos with
           | None -> ParseFail "expected a node test" pos
           | Some (test, pos1') ->
             (match parse_predicates input pos1' (fuel - 1) with
              | ParseFail msg fpos -> ParseFail msg fpos
              | ParseOk preds pos2 ->
                let first = { step_axis = Ax_Child; step_test = test; step_preds = preds } in
                (match parse_location_path_rest input [first] pos2 (fuel - 1) with
                 | ParseFail msg fpos -> ParseFail msg fpos
                 | ParseOk steps pos3 -> ParseOk (XE_Path false steps) pos3)))
        else
          let posws = skip_ws input pos1 in
          if posws < len && fs_byte_index input posws = '(' then
            if is_nodetype_keyword nm then
              (match parse_node_test input pos with
               | None -> ParseFail "unsupported node type (processing-instruction — Stage 1.5)" pos
               | Some (test, pos1') ->
                 (match parse_predicates input pos1' (fuel - 1) with
                  | ParseFail msg fpos -> ParseFail msg fpos
                  | ParseOk preds pos2 ->
                    let first = { step_axis = Ax_Child; step_test = test; step_preds = preds } in
                    (match parse_location_path_rest input [first] pos2 (fuel - 1) with
                     | ParseFail msg fpos -> ParseFail msg fpos
                     | ParseOk steps pos3 -> ParseOk (XE_Path false steps) pos3)))
            else
              (match parse_function_args input (skip_ws input (posws + 1)) (fuel - 1) with
               | ParseFail msg fpos -> ParseFail msg fpos
               | ParseOk args pos2 -> parse_filter_suffix input (XE_FunCall nm args) pos2 (fuel - 1))
          else
            (match parse_predicates input pos1 (fuel - 1) with
             | ParseFail msg fpos -> ParseFail msg fpos
             | ParseOk preds pos2 ->
               let first = { step_axis = Ax_Child; step_test = NT_Name nm; step_preds = preds } in
               (match parse_location_path_rest input [first] pos2 (fuel - 1) with
                | ParseFail msg fpos -> ParseFail msg fpos
                | ParseOk steps pos3 -> ParseOk (XE_Path false steps) pos3))

and parse_primary_expr (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    let len = fs_byte_length input in
    match peek_char input pos with
    | Some '$' ->
      (match parse_ncname input (pos + 1) with
       | None -> ParseFail "expected variable name after '$'" (pos + 1)
       | Some (nm, pos1) ->
         if pos1 < len && fs_byte_index input pos1 = ':' && pos1 + 1 < len && is_name_start_char (fs_byte_index input (pos1 + 1)) then
           (match parse_ncname input (pos1 + 1) with
            | Some (local, pos2) -> ParseOk (XE_VarRef (String.concat "" [nm; ":"; local])) pos2
            | None -> ParseOk (XE_VarRef nm) pos1)
         else ParseOk (XE_VarRef nm) pos1)
    | Some '(' ->
      (match parse_or_expr input (skip_ws input (pos + 1)) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk e pos1 ->
         let pos2 = skip_ws input pos1 in
         if pos2 < len && fs_byte_index input pos2 = ')' then ParseOk e (pos2 + 1)
         else ParseFail "expected ')'" pos2)
    | Some c ->
      if c = '"' || c = '\'' then
        (match parse_string_lit input pos with
         | Some (s, pos1) -> ParseOk (XE_Literal s) pos1
         | None -> ParseFail "unterminated string literal" pos)
      else
        (match parse_number_lit input pos with
         | Some (v, scale, pos1) -> ParseOk (XE_Number v scale) pos1
         | None -> ParseFail "expected an expression" pos)
    | _ ->
      (match parse_number_lit input pos with
       | Some (v, scale, pos1) -> ParseOk (XE_Number v scale) pos1
       | None -> ParseFail "expected an expression" pos)

and parse_filter_suffix (input:string) (primary:xp_expr) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseOk primary pos
  else
    match parse_predicates input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk preds pos1 ->
      let len = fs_byte_length input in
      let pos2 = skip_ws input pos1 in
      if pos2 < len && fs_byte_index input pos2 = '/' then
        if pos2 + 1 < len && fs_byte_index input (pos2 + 1) = '/' then
          let dstep = { step_axis = Ax_DescendantOrSelf; step_test = NT_Node; step_preds = [] } in
          (match parse_relative_location_path input (pos2 + 2) (fuel - 1) with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk steps pos3 -> ParseOk (XE_FilterPath primary preds (dstep :: steps)) pos3)
        else
          (match parse_relative_location_path input (pos2 + 1) (fuel - 1) with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk steps pos3 -> ParseOk (XE_FilterPath primary preds steps) pos3)
      else if Nil? preds then ParseOk primary pos1
      else ParseOk (XE_FilterPath primary preds []) pos1

and parse_absolute_location_path (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_expr) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    let len = fs_byte_length input in
    if pos + 1 < len && fs_byte_index input (pos + 1) = '/' then
      let dstep = { step_axis = Ax_DescendantOrSelf; step_test = NT_Node; step_preds = [] } in
      (match parse_relative_location_path input (pos + 2) (fuel - 1) with
       | ParseFail msg fpos -> ParseFail msg fpos
       | ParseOk steps pos1 -> ParseOk (XE_Path true (dstep :: steps)) pos1)
    else
      let pos1 = pos + 1 in
      let looks_like_step =
        match peek_char input pos1 with
        | None -> false
        | Some c -> c = '@' || c = '.' || c = '*' || is_name_start_char c
      in
      if looks_like_step then
        (match parse_relative_location_path input pos1 (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk steps pos2 -> ParseOk (XE_Path true steps) pos2)
      else ParseOk (XE_Path true []) pos1

and parse_relative_location_path (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list xp_step)) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    match parse_step input pos (fuel - 1) with
    | ParseFail msg fpos -> ParseFail msg fpos
    | ParseOk s pos1 -> parse_location_path_rest input [s] pos1 (fuel - 1)

and parse_location_path_rest (input:string) (acc:list xp_step) (pos:nat) (fuel:nat)
  : Tot (parse_result (list xp_step)) (decreases fuel) =
  if fuel = 0 then ParseOk (List.Tot.rev acc) pos
  else
    let len = fs_byte_length input in
    let pos1 = skip_ws input pos in
    if pos1 < len && fs_byte_index input pos1 = '/' then
      if pos1 + 1 < len && fs_byte_index input (pos1 + 1) = '/' then
        let dstep = { step_axis = Ax_DescendantOrSelf; step_test = NT_Node; step_preds = [] } in
        (match parse_step input (pos1 + 2) (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk s pos2 -> parse_location_path_rest input (s :: dstep :: acc) pos2 (fuel - 1))
      else
        (match parse_step input (pos1 + 1) (fuel - 1) with
         | ParseFail msg fpos -> ParseFail msg fpos
         | ParseOk s pos2 -> parse_location_path_rest input (s :: acc) pos2 (fuel - 1))
    else ParseOk (List.Tot.rev acc) pos1

and parse_step (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result xp_step) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    let len = fs_byte_length input in
    match peek_char input pos with
    | Some '.' ->
      if pos + 1 < len && fs_byte_index input (pos + 1) = '.' then
        ParseOk ({ step_axis = Ax_Parent; step_test = NT_Node; step_preds = [] }) (pos + 2)
      else
        ParseOk ({ step_axis = Ax_Self; step_test = NT_Node; step_preds = [] }) (pos + 1)
    | Some '@' ->
      (match parse_node_test input (pos + 1) with
       | None -> ParseFail "expected node test after '@'" (pos + 1)
       | Some (test, pos1) ->
         (match parse_predicates input pos1 (fuel - 1) with
          | ParseFail msg fpos -> ParseFail msg fpos
          | ParseOk preds pos2 -> ParseOk ({ step_axis = Ax_Attribute; step_test = test; step_preds = preds }) pos2))
    | _ ->
      let is_axis_lead =
        match parse_ncname input pos with
        | Some (_, pos1) -> pos1 + 1 < len && fs_byte_index input pos1 = ':' && fs_byte_index input (pos1 + 1) = ':'
        | None -> false
      in
      if is_axis_lead then
        (match parse_ncname input pos with
         | None -> ParseFail "expected a step" pos
         | Some (nm, pos1) ->
           (match axis_of_name nm with
            | None -> ParseFail (String.concat "" ["axis '"; nm; "' not supported (see Stage 1.5)"]) pos
            | Some ax ->
              (match parse_node_test input (pos1 + 2) with
               | None -> ParseFail "expected node test after axis '::'" (pos1 + 2)
               | Some (test, pos2) ->
                 (match parse_predicates input pos2 (fuel - 1) with
                  | ParseFail msg fpos -> ParseFail msg fpos
                  | ParseOk preds pos3 -> ParseOk ({ step_axis = ax; step_test = test; step_preds = preds }) pos3))))
      else
        (match parse_node_test input pos with
         | None -> ParseFail "expected a step" pos
         | Some (test, pos1) ->
           (match parse_predicates input pos1 (fuel - 1) with
            | ParseFail msg fpos -> ParseFail msg fpos
            | ParseOk preds pos2 -> ParseOk ({ step_axis = Ax_Child; step_test = test; step_preds = preds }) pos2))

and parse_predicates (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list xp_expr)) (decreases fuel) =
  if fuel = 0 then ParseOk [] pos
  else
    let pos1 = skip_ws input pos in
    if pos1 < fs_byte_length input && fs_byte_index input pos1 = '[' then
      match parse_or_expr input (skip_ws input (pos1 + 1)) (fuel - 1) with
      | ParseFail msg fpos -> ParseFail msg fpos
      | ParseOk pred pos2 ->
        let pos3 = skip_ws input pos2 in
        if pos3 < fs_byte_length input && fs_byte_index input pos3 = ']' then
          (match parse_predicates input (pos3 + 1) (fuel - 1) with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk rest pos4 -> ParseOk (pred :: rest) pos4)
        else ParseFail "expected ']'" pos3
    else ParseOk [] pos1

and parse_function_args (input:string) (pos:nat) (fuel:nat)
  : Tot (parse_result (list xp_expr)) (decreases fuel) =
  if fuel = 0 then ParseFail "expression too complex (out of fuel)" pos
  else
    let pos1 = skip_ws input pos in
    if pos1 < fs_byte_length input && fs_byte_index input pos1 = ')' then ParseOk [] (pos1 + 1)
    else
      match parse_or_expr input pos1 (fuel - 1) with
      | ParseFail msg fpos -> ParseFail msg fpos
      | ParseOk a pos2 ->
        let pos3 = skip_ws input pos2 in
        if pos3 < fs_byte_length input && fs_byte_index input pos3 = ',' then
          (match parse_function_args input (skip_ws input (pos3 + 1)) (fuel - 1) with
           | ParseFail msg fpos -> ParseFail msg fpos
           | ParseOk rest pos4 -> ParseOk (a :: rest) pos4)
        else if pos3 < fs_byte_length input && fs_byte_index input pos3 = ')' then
          ParseOk [a] (pos3 + 1)
        else ParseFail "expected ',' or ')'" pos3


(* ================================================================ *)
(* Entry point                                                       *)
(* ================================================================ *)

// Parses a full XPath 1.0 expression, requiring the entire (trimmed)
// input to be consumed. Returns None on any parse failure or trailing
// garbage.
let parse_xpath (input:string) : option xp_expr =
  let fuel = initial_parse_fuel input in
  match parse_or_expr input 0 fuel with
  | ParseFail _ _ -> None
  | ParseOk e pos ->
    let pos' = skip_ws input pos in
    if pos' = fs_byte_length input then Some e else None
