module MathML.Present

// Expression -> MathML serializer (the reverse of MathML.Content, which
// PARSES Content MathML into Math.Expr.expr). Two outputs:
//
//   * to_presentation_mathml : produces Presentation MathML
//     (<math>..</math> with <mrow>/<mi>/<mn>/<mo>/<mfrac>/<msup>/<msqrt>
//     ..) so a browser typesets the expression natively. Operator
//     precedence drives MINIMAL parenthesization: a subexpression is
//     fenced only when its top operator binds looser than the position
//     it sits in (e.g. (x+y)*z fences the sum; x^2*y does not fence the
//     power). A fraction / power / function box is visually atomic, so
//     it is never fenced.
//
//   * to_content_mathml : produces semantic Content MathML
//     (<apply><plus/>..</apply>) that mirrors the AST one-to-one. It
//     round-trips with MathML.Content's parser: parsing it back and
//     simplifying recovers the original up to simplify.
//
// Pure F*, total, structural recursion on the expression (no fuel).
// XML special characters in symbol / function names are escaped.

open FStar.String
open FStar.List.Tot
open Math.Expr

(* ================================================================ *)
(* XML escaping                                                      *)
(* ================================================================ *)

let escape_char (c:FStar.Char.char) : string =
  if c = '&' then "&amp;"
  else if c = '<' then "&lt;"
  else if c = '>' then "&gt;"
  else if c = '"' then "&quot;"
  else if c = '\'' then "&apos;"
  else String.string_of_list [c]

let rec escape_chars (l:list FStar.Char.char) : Tot string (decreases l) =
  match l with
  | [] -> ""
  | c :: t -> String.concat "" [escape_char c; escape_chars t]

let escape_xml (s:string) : string = escape_chars (String.list_of_string s)

(* ================================================================ *)
(* Number rendering                                                 *)
(* ================================================================ *)

// An integer as <mn>; a negative sign is carried inside the token.
let render_int (n:int) : string =
  String.concat "" ["<mn>"; string_of_int n; "</mn>"]

// A rational as a fraction box; the sign lives in the numerator.
let render_rat (n:int) (d:int) : string =
  String.concat ""
    ["<mfrac><mn>"; string_of_int n; "</mn><mn>"; string_of_int d; "</mn></mfrac>"]

(* ================================================================ *)
(* Precedence (higher binds tighter). Drives minimal fencing.        *)
(*   1 : additive        (plus, binary minus)                        *)
(*   2 : multiplicative  (times, unary minus)                        *)
(*   3 : power                                                        *)
(*   4 : atomic          (symbol, non-negative number, fraction,     *)
(*                        divide-as-fraction, root, function apply)   *)
(* A negative number leaf is additive-ish (1) so it is fenced where  *)
(* a bare number would not need to be.                                *)
(* ================================================================ *)

let prec (e:expr) : int =
  match e with
  | E_Int n -> if n < 0 then 1 else 4
  | E_Rat n _ -> if n < 0 then 1 else 4
  | E_Bool _ -> 4
  | E_Sym _ -> 4
  | E_App fn args ->
    if fn = "plus" then 1
    else if fn = "minus" then (match args with [_] -> 2 | _ -> 1)
    else if fn = "times" then 2
    else if fn = "power" then 3
    else if fn = "divide" then 4
    else 4

let fence (s:string) : string =
  String.concat "" ["<mrow><mo>(</mo>"; s; "<mo>)</mo></mrow>"]

(* ================================================================ *)
(* Presentation MathML                                              *)
(*                                                                   *)
(* pres renders a node; the caller decides fencing from prec. The    *)
(* mutually-recursive pres_join renders each operand of an operator, *)
(* fencing it when its precedence is below the operator's minimum,   *)
(* and inserts the operator token between operands.                  *)
(* ================================================================ *)

// Structural size measures. A lexicographic %[size; tag] measure gives
// the mutually-recursive renderers a common well-founded order: the
// operand renderers (tag 1) and the function-application wrapper (tag 2)
// may call back into pres (tag 0) at an equal size, and the tag breaks
// the tie in the strictly-decreasing direction.
let rec expr_size (e:expr) : Tot nat (decreases e) =
  match e with
  | E_App _ args -> 1 + exprs_size args
  | _ -> 1
and exprs_size (es:list expr) : Tot nat (decreases es) =
  match es with
  | [] -> 0
  | h :: t -> expr_size h + exprs_size t

// Fence an already-rendered operand if its operator binds looser than
// the position it sits in (minp). Non-recursive.
let fenced (minp:int) (p:int) (s:string) : string =
  if p < minp then fence s else s

let rec pres (e:expr) : Tot string (decreases %[expr_size e; 0]) =
  match e with
  | E_Int n -> render_int n
  | E_Rat n d -> render_rat n d
  | E_Bool b -> String.concat "" ["<mi>"; (if b then "true" else "false"); "</mi>"]
  | E_Sym s -> String.concat "" ["<mi>"; escape_xml s; "</mi>"]
  | E_App fn args ->
    if fn = "plus" then
      (match args with
       | [] -> render_int 0
       | a :: rest -> String.concat "" [fenced 1 (prec a) (pres a); pres_plus_rest rest])
    else if fn = "minus" then
      (match args with
       | [a] -> String.concat "" ["<mo>-</mo>"; fenced 2 (prec a) (pres a)]
       | [a; b] ->
         String.concat "" [fenced 1 (prec a) (pres a); "<mo>-</mo>"; fenced 2 (prec b) (pres b)]
       | _ -> pres_apply fn args)
    else if fn = "times" then
      (match args with
       | [] -> render_int 1
       | a :: rest -> String.concat "" [fenced 2 (prec a) (pres a); pres_times_rest rest])
    else if fn = "divide" then
      (match args with
       | [a; b] ->
         String.concat "" ["<mfrac><mrow>"; pres a; "</mrow><mrow>"; pres b; "</mrow></mfrac>"]
       | _ -> pres_apply fn args)
    else if fn = "power" then
      (match args with
       | [a; b] ->
         String.concat ""
           ["<msup><mrow>"; fenced 4 (prec a) (pres a); "</mrow><mrow>"; pres b; "</mrow></msup>"]
       | _ -> pres_apply fn args)
    else if fn = "root" then
      (match args with
       | [a] -> String.concat "" ["<msqrt><mrow>"; pres a; "</mrow></msqrt>"]
       | [d; a] ->
         String.concat "" ["<mroot><mrow>"; pres a; "</mrow><mrow>"; pres d; "</mrow></mroot>"]
       | _ -> pres_apply fn args)
    else pres_apply fn args

// Remaining summands, each preceded by its own sign operator.
and pres_plus_rest (es:list expr) : Tot string (decreases %[exprs_size es; 1]) =
  match es with
  | [] -> ""
  | a :: rest ->
    String.concat "" ["<mo>+</mo>"; fenced 1 (prec a) (pres a); pres_plus_rest rest]

// Remaining factors, joined by an invisible-times operator.
and pres_times_rest (es:list expr) : Tot string (decreases %[exprs_size es; 1]) =
  match es with
  | [] -> ""
  | a :: rest ->
    String.concat "" ["<mo>&#x2062;</mo>"; fenced 2 (prec a) (pres a); pres_times_rest rest]

// Function application f(a, b, ..): atomic, args comma-separated.
and pres_apply (fn:string) (args:list expr) : Tot string (decreases %[exprs_size args; 2]) =
  String.concat ""
    ["<mrow><mi>"; escape_xml fn; "</mi><mo>&#x2061;</mo><mo>(</mo>";
     pres_apply_args args; "<mo>)</mo></mrow>"]

and pres_apply_args (es:list expr) : Tot string (decreases %[exprs_size es; 1]) =
  match es with
  | [] -> ""
  | [a] -> pres a
  | a :: rest -> String.concat "" [pres a; "<mo>,</mo>"; pres_apply_args rest]

let to_presentation_mathml (e:expr) : string =
  String.concat ""
    ["<math xmlns=\"http://www.w3.org/1998/Math/MathML\">"; pres e; "</math>"]

(* ================================================================ *)
(* Content MathML (mirrors the AST; round-trips with MathML.Content) *)
(* ================================================================ *)

// Operator elements Content MathML names with an empty element; other
// function names are carried as <csymbol> text (which MathML.Content
// reads back through canonical_op).
let known_content_op (fn:string) : bool =
  fn = "plus" || fn = "times" || fn = "minus" || fn = "divide" ||
  fn = "power" || fn = "root" || fn = "abs" || fn = "quotient" ||
  fn = "rem" || fn = "factorial" || fn = "gcd" || fn = "max" ||
  fn = "min" || fn = "eq" || fn = "neq" || fn = "lt" || fn = "gt" ||
  fn = "leq" || fn = "geq"

let content_op (fn:string) : string =
  if known_content_op fn then String.concat "" ["<"; fn; "/>"]
  else String.concat "" ["<csymbol>"; escape_xml fn; "</csymbol>"]

let rec content (e:expr) : Tot string (decreases e) =
  match e with
  | E_Int n -> String.concat "" ["<cn type=\"integer\">"; string_of_int n; "</cn>"]
  | E_Rat n d ->
    String.concat ""
      ["<cn type=\"rational\">"; string_of_int n; "<sep/>"; string_of_int d; "</cn>"]
  | E_Bool b -> if b then "<true/>" else "<false/>"
  | E_Sym s -> String.concat "" ["<ci>"; escape_xml s; "</ci>"]
  | E_App fn args ->
    String.concat "" ["<apply>"; content_op fn; content_args args; "</apply>"]

and content_args (es:list expr) : Tot string (decreases es) =
  match es with
  | [] -> ""
  | a :: rest -> String.concat "" [content a; content_args rest]

let to_content_mathml (e:expr) : string =
  String.concat ""
    ["<math xmlns=\"http://www.w3.org/1998/Math/MathML\">"; content e; "</math>"]
