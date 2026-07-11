(* toan_tests.ml — regression battery for the ThinkOfANumber (TOAN)
   extensions to the verified CAS layer:

     Math.Series.fst    (summation / finite_product over an integer range)
     Math.Simplify.fst  (coefficient-carrying like-term merge)
     MathML.Present.fst (expr -> Presentation / Content MathML)

   All CAS logic lives in F* (rule #7 / #1). This .ml is a CONSUMER: it
   builds Math.Expr.expr trees, calls the extracted F* functions, and
   compares — no algebra, no serialization, no parenthesization logic is
   implemented here. Structural comparison goes through the canonical key
   Math_Simplify.expr_key so operand ordering does not matter.

   Sections:
     1. The two motivating examples (exact expected expressions).
     2. Empty-range identities (summation -> 0, product -> 1).
     3. Coefficient-merge cases + unlike-term soundness.
     4. simplify idempotence still holds (incl. merged + series output).
     5. simplify value-preservation on the merge cases.
     6. Presentation-MathML shape + minimal-parenthesization checks, and
        the round-trip property key(simplify(parse(content e))) =
        key(simplify e) using MathML.Content's parser + Parser.XML. *)

module E = Math_Expr
module Sm = Math_Simplify
module Se = Math_Series
module Pr = MathML_Present
module Mc = MathML_Content
module Px = Parser_XML
module Md = Math_Diff

let passed = ref 0
let failed = ref 0
let fail_cats : (string, int) Hashtbl.t = Hashtbl.create 16

let note_fail cat =
  let n = try Hashtbl.find fail_cats cat with Not_found -> 0 in
  Hashtbl.replace fail_cats cat (n + 1)

let check ~cat ~name expected actual =
  if String.equal expected actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed; note_fail cat;
    Printf.printf "  FAIL  [%s] %s: expected %S got %S\n" cat name expected actual
  end

let check_true ~cat ~name b =
  check ~cat ~name "true" (if b then "true" else "false")

(* ------------------------------------------------------------------ *)
(* expr / value builders (Prims.int = Zarith Z.t)                     *)
(* ------------------------------------------------------------------ *)

let ei n : E.expr = E.E_Int (Z.of_int n)
let erat n d : E.expr = E.E_Rat (Z.of_int n, Z.of_int d)
let sym s : E.expr = E.E_Sym s
let app fn args : E.expr = E.E_App (fn, args)
let eadd a b = app "plus" [a; b]
let eaddn xs = app "plus" xs
let emul a b = app "times" [a; b]
let emuln xs = app "times" xs
let epow a b = app "power" [a; b]
let ediv a b = app "divide" [a; b]
let eminus a b = app "minus" [a; b]
let fapp1 fn a = app fn [a]
let erel fn a b = app fn [a; b]

let mv_rat n d : E.mvalue = E.MV_Rat (Z.of_int n, Z.of_int d)

let key e = Sm.expr_key e
let keq a b = String.equal (key a) (key b)

let x = sym "x"
let y = sym "y"
let z = sym "z"
let i = sym "i"

(* body of the two motivating examples: x + i*y *)
let body = eadd x (emul i y)

let zi n = Z.of_int n

(* Compare simplify(actual) to simplify(expected) via canonical key. *)
let check_simpl ~cat ~name actual expected =
  check_true ~cat ~name (keq (Sm.simplify actual) (Sm.simplify expected))

let eval_at env e = E.eval_expr env e

(* ------------------------------------------------------------------ *)
(* 1. The two motivating examples                                     *)
(* ------------------------------------------------------------------ *)

let () =
  (* summation(x + i*y, i, 1, 4)  ==>  4*x + 10*y *)
  let s = Se.summation body "i" (zi 1) (zi 4) in
  let s_expected = eadd (emul (ei 4) x) (emul (ei 10) y) in
  check_true ~cat:"motivating-summation"
    ~name:"summation(x + i*y, i, 1, 4) = 4*x + 10*y"
    (keq s (Sm.simplify s_expected));
  (* echo the actual serialized result for the report *)
  Printf.printf "  [info] summation(x + i*y, i, 1, 4) key = %s\n" (key s);

  (* product(x + i*y, i, 0, 5)
       ==>  x*(x+y)*(x+2*y)*(x+3*y)*(x+4*y)*(x+5*y)  (left factored) *)
  let p = Se.finite_product body "i" (zi 0) (zi 5) in
  let p_expected =
    emuln [ x;
            eadd x y;
            eadd x (emul (ei 2) y);
            eadd x (emul (ei 3) y);
            eadd x (emul (ei 4) y);
            eadd x (emul (ei 5) y) ] in
  check_true ~cat:"motivating-product"
    ~name:"product(x + i*y, i, 0, 5) = x*(x+y)*(x+2y)*(x+3y)*(x+4y)*(x+5y)"
    (keq p (Sm.simplify p_expected));
  Printf.printf "  [info] product(x + i*y, i, 0, 5) key = %s\n" (key p)

(* ------------------------------------------------------------------ *)
(* 2. Empty-range identities                                          *)
(* ------------------------------------------------------------------ *)

let () =
  (* hi < lo : empty range. summation -> 0 (additive identity). *)
  check_true ~cat:"empty-range"
    ~name:"summation over empty range (5..1) = 0"
    (keq (Se.summation body "i" (zi 5) (zi 1)) (ei 0));
  (* product -> 1 (multiplicative identity). *)
  check_true ~cat:"empty-range"
    ~name:"product over empty range (5..1) = 1"
    (keq (Se.finite_product body "i" (zi 5) (zi 1)) (ei 1));
  (* single-element range: summation(x + i*y, i, 2, 2) = x + 2*y. *)
  check_true ~cat:"empty-range"
    ~name:"summation over single point (2..2) = x + 2*y"
    (keq (Se.summation body "i" (zi 2) (zi 2))
         (Sm.simplify (eadd x (emul (ei 2) y))));
  (* single-element product(x + i*y, i, 3, 3) = x + 3*y. *)
  check_true ~cat:"empty-range"
    ~name:"product over single point (3..3) = x + 3*y"
    (keq (Se.finite_product body "i" (zi 3) (zi 3))
         (Sm.simplify (eadd x (emul (ei 3) y))))

(* ------------------------------------------------------------------ *)
(* 3. Coefficient-carrying like-term merge                            *)
(* ------------------------------------------------------------------ *)

let () =
  check_simpl ~cat:"coeff-merge" ~name:"simplify(2*y + 3*y) = 5*y"
    (eadd (emul (ei 2) y) (emul (ei 3) y)) (emul (ei 5) y);
  check_simpl ~cat:"coeff-merge" ~name:"simplify(y + 2*y + 3*y + 4*y) = 10*y"
    (eaddn [y; emul (ei 2) y; emul (ei 3) y; emul (ei 4) y]) (emul (ei 10) y);
  check_simpl ~cat:"coeff-merge" ~name:"simplify(3*x + x) = 4*x"
    (eadd (emul (ei 3) x) x) (emul (ei 4) x);
  check_simpl ~cat:"coeff-merge" ~name:"simplify(x + 2*y + 3*y) = x + 5*y"
    (eaddn [x; emul (ei 2) y; emul (ei 3) y]) (eadd x (emul (ei 5) y));
  check_simpl ~cat:"coeff-merge" ~name:"simplify(2*x + 3*x + 4) = 5*x + 4"
    (eaddn [emul (ei 2) x; emul (ei 3) x; ei 4]) (eadd (emul (ei 5) x) (ei 4));
  (* rational coefficients merge too: (1/2)*y + (1/2)*y = y *)
  check_simpl ~cat:"coeff-merge" ~name:"simplify((1/2)*y + (1/2)*y) = y"
    (eadd (emul (erat 1 2) y) (emul (erat 1 2) y)) y;
  (* coefficients that cancel: 2*y + (-2)*y = 0 *)
  check_simpl ~cat:"coeff-merge" ~name:"simplify(2*y + (-2)*y) = 0"
    (eadd (emul (ei 2) y) (emul (ei (-2)) y)) (ei 0);
  (* shared multi-factor core: 2*x*y + 3*x*y = 5*x*y *)
  check_simpl ~cat:"coeff-merge" ~name:"simplify(2*x*y + 3*x*y) = 5*x*y"
    (eadd (emuln [ei 2; x; y]) (emuln [ei 3; x; y])) (emuln [ei 5; x; y]);

  (* --- soundness: UNLIKE terms are NEVER merged --- *)
  check_true ~cat:"coeff-merge-soundness"
    ~name:"simplify(2*x + 3*y) keeps two distinct terms (no merge)"
    (match Sm.simplify (eadd (emul (ei 2) x) (emul (ei 3) y)) with
     | E.E_App ("plus", [_; _]) -> true
     | _ -> false);
  check_true ~cat:"coeff-merge-soundness"
    ~name:"simplify(2*x + 3*x^2) keeps distinct cores x vs x^2"
    (match Sm.simplify (eadd (emul (ei 2) x) (emul (ei 3) (epow x (ei 2)))) with
     | E.E_App ("plus", [_; _]) -> true
     | _ -> false);
  (* value oracle for the unlike case: eval preserved at a point *)
  let unlike = eadd (emul (ei 2) x) (emul (ei 3) y) in
  let env = [("x", mv_rat 5 1); ("y", mv_rat 7 1)] in
  check ~cat:"coeff-merge-soundness"
    ~name:"eval(simplify(2*x+3*y)) = eval(2*x+3*y) at x=5,y=7"
    (E.value_to_string (eval_at env unlike))
    (E.value_to_string (eval_at env (Sm.simplify unlike)))

(* ------------------------------------------------------------------ *)
(* 4. simplify idempotence still holds (the existing bar, extended)   *)
(* ------------------------------------------------------------------ *)

let idem_check ~name (e : E.expr) =
  let s1 = Sm.simplify e in
  let s2 = Sm.simplify s1 in
  check ~cat:"simplify-idempotence" ~name (key s1) (key s2)

let () =
  let es : (string * E.expr) list = [
    "2*y + 3*y",          eadd (emul (ei 2) y) (emul (ei 3) y);
    "y + 2y + 3y + 4y",   eaddn [y; emul (ei 2) y; emul (ei 3) y; emul (ei 4) y];
    "x + 2y + 3y",        eaddn [x; emul (ei 2) y; emul (ei 3) y];
    "2*x*y + 3*x*y",      eadd (emuln [ei 2; x; y]) (emuln [ei 3; x; y]);
    "2y + (-2)y",         eadd (emul (ei 2) y) (emul (ei (-2)) y);
    "summation(1..4)",    Se.summation body "i" (zi 1) (zi 4);
    "summation(0..6)",    Se.summation body "i" (zi 0) (zi 6);
    "product(0..5)",      Se.finite_product body "i" (zi 0) (zi 5);
    "product(1..4)",      Se.finite_product body "i" (zi 1) (zi 4);
  ] in
  List.iter (fun (nm, e) -> idem_check ~name:("idempotent: " ^ nm) e) es

(* ------------------------------------------------------------------ *)
(* 5. simplify value-preservation on the merge cases                  *)
(* ------------------------------------------------------------------ *)

let simpl_eval_check ~name (f : E.expr) env =
  let sv = eval_at env (Sm.simplify f) in
  let fv = eval_at env f in
  check ~cat:"simplify-soundness" ~name (E.value_to_string fv) (E.value_to_string sv)

let () =
  let env = [("x", mv_rat 3 1); ("y", mv_rat 5 2)] in
  let fs : (string * E.expr) list = [
    "2y + 3y",            eadd (emul (ei 2) y) (emul (ei 3) y);
    "y + 2y + 3y + 4y",   eaddn [y; emul (ei 2) y; emul (ei 3) y; emul (ei 4) y];
    "x + 2y + 3y",        eaddn [x; emul (ei 2) y; emul (ei 3) y];
    "2*x*y + 3*x*y",      eadd (emuln [ei 2; x; y]) (emuln [ei 3; x; y]);
    "summation(1..4)",    Se.summation body "i" (zi 1) (zi 4);
    "product(1..4)",      Se.finite_product body "i" (zi 1) (zi 4);
  ] in
  List.iter (fun (nm, f) ->
    simpl_eval_check ~name:(Printf.sprintf "eval(simplify %s) = eval(%s)" nm nm) f env
  ) fs

(* ------------------------------------------------------------------ *)
(* 6. MathML serialization: shape, parenthesization, round-trip       *)
(* ------------------------------------------------------------------ *)

let contains ~needle hay =
  let nl = String.length needle and hl = String.length hay in
  let rec go k = k + nl <= hl && (String.equal (String.sub hay k nl) needle || go (k + 1)) in
  nl = 0 || go 0

let xml_parses s =
  match Px.parse_xml_document s with
  | FStar_Pervasives_Native.Some _ -> true
  | FStar_Pervasives_Native.None -> false

let () =
  (* presentation is well-formed XML that our own Parser.XML accepts *)
  let shapes : (string * E.expr) list = [
    "x",              x;
    "4*x + 10*y",     eadd (emul (ei 4) x) (emul (ei 10) y);
    "(x+y)*z",        emul (eadd x y) z;
    "x^2 * y",        emul (epow x (ei 2)) y;
    "(x+y)^2",        epow (eadd x y) (ei 2);
    "1/2",            erat 1 2;
    "x/(x^2+1)",      ediv x (eadd (epow x (ei 2)) (ei 1));
    "sin(x^2)",       fapp1 "sin" (epow x (ei 2));
    "product(0..5)",  Se.finite_product body "i" (zi 0) (zi 5);
  ] in
  List.iter (fun (nm, e) ->
    let m = Pr.to_presentation_mathml e in
    check_true ~cat:"present-wellformed"
      ~name:(Printf.sprintf "to_presentation_mathml(%s) starts with <math" nm)
      (contains ~needle:"<math" m && contains ~needle:"</math>" m);
    check_true ~cat:"present-wellformed"
      ~name:(Printf.sprintf "Parser.XML accepts to_presentation_mathml(%s)" nm)
      (xml_parses m)
  ) shapes;

  (* minimal parenthesization: a sum under a product IS fenced ... *)
  check_true ~cat:"present-parens"
    ~name:"(x+y)*z fences the sum"
    (contains ~needle:"<mo>(</mo>" (Pr.to_presentation_mathml (emul (eadd x y) z)));
  (* ... but a power under a product is NOT (power binds tighter) *)
  check_true ~cat:"present-parens"
    ~name:"x^2 * y does NOT parenthesize the power"
    (not (contains ~needle:"<mo>(</mo>" (Pr.to_presentation_mathml (emul (epow x (ei 2)) y))));
  (* a sum as a power base IS fenced *)
  check_true ~cat:"present-parens"
    ~name:"(x+y)^2 fences the base"
    (contains ~needle:"<mo>(</mo>" (Pr.to_presentation_mathml (epow (eadd x y) (ei 2))));
  (* a plain sum is NOT fenced *)
  check_true ~cat:"present-parens"
    ~name:"x + y is not parenthesized"
    (not (contains ~needle:"<mo>(</mo>" (Pr.to_presentation_mathml (eadd x y))));
  (* a fraction (divide) is atomic: x/(y) as a factor needs no fence *)
  check_true ~cat:"present-parens"
    ~name:"(x/y)*z does not fence the fraction"
    (not (contains ~needle:"<mo>(</mo>" (Pr.to_presentation_mathml (emul (ediv x y) z))))

(* Content-MathML round-trip: key(simplify(parse(content e))) = key(simplify e) *)
let content_roundtrip ~name e =
  let s = Pr.to_content_mathml e in
  match Px.parse_xml_document s with
  | FStar_Pervasives_Native.None ->
    check_true ~cat:"content-roundtrip" ~name:(name ^ " [xml parses]") false
  | FStar_Pervasives_Native.Some node ->
    (match Mc.mathml_to_expr node E.eval_fuel with
     | FStar_Pervasives_Native.None ->
       check_true ~cat:"content-roundtrip" ~name:(name ^ " [maps back]") false
     | FStar_Pervasives_Native.Some e2 ->
       check ~cat:"content-roundtrip" ~name
         (key (Sm.simplify e)) (key (Sm.simplify e2)))

let () =
  let es : (string * E.expr) list = [
    "x^2 + 1",         eadd (epow x (ei 2)) (ei 1);
    "2*x + 3*y",       eadd (emul (ei 2) x) (emul (ei 3) y);
    "x*(x+y)",         emul x (eadd x y);
    "5/2",             erat 5 2;
    "x/(x^2+1)",       ediv x (eadd (epow x (ei 2)) (ei 1));
    "4*x + 10*y",      eadd (emul (ei 4) x) (emul (ei 10) y);
    "summation(1..4)", Se.summation body "i" (zi 1) (zi 4);
    "product(0..5)",   Se.finite_product body "i" (zi 0) (zi 5);
  ] in
  List.iter (fun (nm, e) -> content_roundtrip ~name:("content round-trip: " ^ nm) e) es

(* ------------------------------------------------------------------ *)
(* 7. Relations / abs / factorial / exp / diff_unsupported rendering  *)
(*                                                                     *)
(* MathML.Present.fst grew five new pres cases (relations, abs,       *)
(* factorial, exp, the Math.Diff "diff_unsupported" sentinel) plus an  *)
(* addition to known_content_op (exp is a genuine MathML3 content      *)
(* element, <exp/>). Every case below is an exact-expected-string      *)
(* assertion — no `contains` fuzzing — so a precedence/fencing         *)
(* regression trips immediately. *)
(* ------------------------------------------------------------------ *)

let mathml_doc s = "<math xmlns=\"http://www.w3.org/1998/Math/MathML\">" ^ s ^ "</math>"

let check_pres ~name e expected_inner =
  check ~cat:"present-new-ops" ~name (mathml_doc expected_inner) (Pr.to_presentation_mathml e)

let () =
  (* --- relations: each of the six heads, exact infix token --- *)
  check_pres ~name:"eq(x,y)"
    (erel "eq" x y) "<mi>x</mi><mo>=</mo><mi>y</mi>";
  check_pres ~name:"neq(x,y)"
    (erel "neq" x y) "<mi>x</mi><mo>&#x2260;</mo><mi>y</mi>";
  check_pres ~name:"lt(x,y)"
    (erel "lt" x y) "<mi>x</mi><mo>&lt;</mo><mi>y</mi>";
  check_pres ~name:"gt(x,y)"
    (erel "gt" x y) "<mi>x</mi><mo>&gt;</mo><mi>y</mi>";
  check_pres ~name:"leq(x,y)"
    (erel "leq" x y) "<mi>x</mi><mo>&#x2264;</mo><mi>y</mi>";
  check_pres ~name:"geq(x,y)"
    (erel "geq" x y) "<mi>x</mi><mo>&#x2265;</mo><mi>y</mi>";
  (* compound operand on the right, no fencing (plus binds tighter) *)
  check_pres ~name:"eq(x, plus(y,1))"
    (erel "eq" x (eadd y (ei 1))) "<mi>x</mi><mo>=</mo><mi>y</mi><mo>+</mo><mn>1</mn>";
  (* nested relation operand: precedence 0 < minp 1 -> fenced *)
  check_pres ~name:"geq(eq(x,y), z) fences the nested relation"
    (erel "geq" (erel "eq" x y) z)
    "<mrow><mo>(</mo><mi>x</mi><mo>=</mo><mi>y</mi><mo>)</mo></mrow><mo>&#x2265;</mo><mi>z</mi>";
  (* non-relation (plus, prec 1) operand under a relation: NOT fenced *)
  check_pres ~name:"lt(plus(x,y), z) does not fence the sum"
    (erel "lt" (eadd x y) z) "<mi>x</mi><mo>+</mo><mi>y</mi><mo>&lt;</mo><mi>z</mi>";

  (* --- abs: atomic box, no internal fencing --- *)
  check_pres ~name:"abs(x)"
    (fapp1 "abs" x) "<mrow><mo>|</mo><mi>x</mi><mo>|</mo></mrow>";
  check_pres ~name:"abs(plus(x,y)) does not fence the sum inside the bars"
    (fapp1 "abs" (eadd x y)) "<mrow><mo>|</mo><mi>x</mi><mo>+</mo><mi>y</mi><mo>|</mo></mrow>";
  check_pres ~name:"abs(-3) carries the sign inside the bars unfenced"
    (fapp1 "abs" (ei (-3))) "<mrow><mo>|</mo><mn>-3</mn><mo>|</mo></mrow>";

  (* --- factorial: atomic; operand fenced only if it binds looser --- *)
  check_pres ~name:"factorial(n)"
    (fapp1 "factorial" (sym "n")) "<mi>n</mi><mo>!</mo>";
  check_pres ~name:"factorial(plus(x,y)) fences the sum"
    (fapp1 "factorial" (eadd x y)) "<mrow><mo>(</mo><mi>x</mi><mo>+</mo><mi>y</mi><mo>)</mo></mrow><mo>!</mo>";
  check_pres ~name:"factorial(abs(x)) does not re-fence an already-atomic operand"
    (fapp1 "factorial" (fapp1 "abs" x)) "<mrow><mo>|</mo><mi>x</mi><mo>|</mo></mrow><mo>!</mo>";

  (* --- exp: e^x as a superscript, matching power's visual form --- *)
  check_pres ~name:"exp(x)"
    (fapp1 "exp" x) "<msup><mi>e</mi><mrow><mi>x</mi></mrow></msup>";
  check_pres ~name:"exp(plus(x,y)) puts the sum in the exponent unfenced"
    (fapp1 "exp" (eadd x y)) "<msup><mi>e</mi><mrow><mi>x</mi><mo>+</mo><mi>y</mi></mrow></msup>";

  (* --- diff_unsupported: Math.Diff's "no rule" sentinel renders as a  *)
  (* visible error box, ignoring the wrapped (unrenderable) argument.  *)
  check_pres ~name:"diff_unsupported(x) direct construction"
    (app "diff_unsupported" [x]) "<merror><mtext>unsupported derivative</mtext></merror>";
  check_pres ~name:"diff x (coth x) has no rule -> diff_unsupported -> merror"
    (Md.diff "x" (fapp1 "coth" x)) "<merror><mtext>unsupported derivative</mtext></merror>";
  check_pres ~name:"plus(x, diff_unsupported(y)) embeds the error box atomically"
    (eadd x (app "diff_unsupported" [y]))
    "<mi>x</mi><mo>+</mo><merror><mtext>unsupported derivative</mtext></merror>"

(* ------------------------------------------------------------------ *)
(* 7b. Well-formedness self-check for the new cases (same pattern as   *)
(* section 6's `shapes` loop): every serialized <math> parses via our  *)
(* own Parser.XML.                                                     *)
(* ------------------------------------------------------------------ *)

let () =
  let new_shapes : (string * E.expr) list = [
    "eq(x,y)",              erel "eq" x y;
    "geq(eq(x,y), z)",      erel "geq" (erel "eq" x y) z;
    "abs(minus(x,y))",      fapp1 "abs" (eminus x y);
    "factorial(plus(x,1))", fapp1 "factorial" (eadd x (ei 1));
    "exp(power(x,2))",      fapp1 "exp" (epow x (ei 2));
    "diff_unsupported(x)",  app "diff_unsupported" [x];
    "eq(x, abs(y))",        erel "eq" x (fapp1 "abs" y);
  ] in
  List.iter (fun (nm, e) ->
    let m = Pr.to_presentation_mathml e in
    check_true ~cat:"present-new-ops-wellformed"
      ~name:(Printf.sprintf "to_presentation_mathml(%s) starts with <math" nm)
      (contains ~needle:"<math" m && contains ~needle:"</math>" m);
    check_true ~cat:"present-new-ops-wellformed"
      ~name:(Printf.sprintf "Parser.XML accepts to_presentation_mathml(%s)" nm)
      (xml_parses m)
  ) new_shapes

(* ------------------------------------------------------------------ *)
(* 7c. Content-MathML round-trip for the new ops, including <exp/>     *)
(* (which known_content_op now names as a real element rather than a   *)
(* <csymbol> fallback).                                                *)
(* ------------------------------------------------------------------ *)

let () =
  let es : (string * E.expr) list = [
    "eq(x,y)",         erel "eq" x y;
    "neq(x,y)",        erel "neq" x y;
    "lt(x,y)",         erel "lt" x y;
    "gt(x,y)",         erel "gt" x y;
    "leq(x,y)",        erel "leq" x y;
    "geq(x,y)",        erel "geq" x y;
    "abs(x)",          fapp1 "abs" x;
    "factorial(n)",    fapp1 "factorial" (sym "n");
    "exp(x)",          fapp1 "exp" x;
  ] in
  List.iter (fun (nm, e) -> content_roundtrip ~name:("content round-trip: " ^ nm) e) es;

  (* exp is emitted as the genuine content element <exp/>, not a
     <csymbol>exp</csymbol> fallback. *)
  check_true ~cat:"content-new-ops"
    ~name:"to_content_mathml(exp(x)) uses <exp/> not <csymbol>"
    (contains ~needle:"<exp/>" (Pr.to_content_mathml (fapp1 "exp" x)));
  check_true ~cat:"content-new-ops"
    ~name:"to_content_mathml(abs(x)) uses <abs/>"
    (contains ~needle:"<abs/>" (Pr.to_content_mathml (fapp1 "abs" x)));
  check_true ~cat:"content-new-ops"
    ~name:"to_content_mathml(factorial(n)) uses <factorial/>"
    (contains ~needle:"<factorial/>" (Pr.to_content_mathml (fapp1 "factorial" (sym "n"))));
  check_true ~cat:"content-new-ops"
    ~name:"to_content_mathml(eq(x,y)) uses <eq/>"
    (contains ~needle:"<eq/>" (Pr.to_content_mathml (erel "eq" x y)))

(* ------------------------------------------------------------------ *)
(* Summary                                                            *)
(* ------------------------------------------------------------------ *)

let () =
  Printf.printf "\n";
  if Hashtbl.length fail_cats > 0 then begin
    Printf.printf "failing categories:\n";
    Hashtbl.iter (fun cat n -> Printf.printf "  %s: %d\n" cat n) fail_cats
  end;
  Printf.printf "TOAN: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
