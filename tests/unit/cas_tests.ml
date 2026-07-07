(* cas_tests.ml — spec-cited + property regression battery for the
   verified CAS layer built on Math.Expr:

     Math.Subst.fst     (subst)
     Math.Diff.fst      (diff)
     Math.Simplify.fst  (simplify)

   All CAS logic lives in F* (rule #7 / #1). This .ml is a CONSUMER:
   it only builds Math.Expr.expr trees, calls the extracted F*
   functions, evaluates via Math.Expr.eval_expr, and compares —
   no algebra is implemented here.

   Two kinds of checks (per CLAUDE.md rule #25 the summary is labelled):

   1. Worked cases cited to standard calculus/algebra identities
      (d/dx x^2 = 2x; d/dx sin x = cos x; product/chain instances;
      simplify(x+0)=x; simplify(2+3)=5; ...). Compared structurally
      through the canonical key Math_Simplify.expr_key, so operand
      ordering does not matter.

   2. Property checks — the part that catches wrong rules that
      hand-picked examples miss:
        * diff soundness oracle: eval(diff f) at a point vs the exact
          rational central finite difference (f(x0+h)-f(x0-h))/(2h),
          within tolerance, over algebraic (eval-defined) f. Math.Expr's
          evaluator is exact rational, so the only error is the O(h^2)
          truncation of the difference quotient — no float noise.
        * subst: eval(subst x v f) with empty env == eval(f) with x:=eval(v).
        * simplify idempotence: key(simplify(simplify e)) == key(simplify e).
        * simplify soundness: eval(simplify f) == eval(f) on closed
          instances (env binds every free symbol).

   Not yet wired into tests/unit/run-all.sh's COMMON_MODULES; built and
   run standalone by the CAS landing (see the implementation report for
   the exact invocation and pass/fail count). *)

module E = Math_Expr
module S = Math_Subst
module D = Math_Diff
module Sm = Math_Simplify

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
let esub a b = app "minus" [a; b]
let eneg a = app "minus" [a]
let epow a b = app "power" [a; b]
let ediv a b = app "divide" [a; b]
let fapp1 fn a = app fn [a]

let mv_rat n d : E.mvalue = E.MV_Rat (Z.of_int n, Z.of_int d)

let key e = Sm.expr_key e
let keq a b = String.equal (key a) (key b)

let is_undef (v : E.mvalue) = match v with E.MV_Undef _ -> true | _ -> false

(* env with a single symbol x bound to the rational xn/xd *)
let env_x xn xd : (string * E.mvalue) list = [("x", mv_rat xn xd)]

let eval_at env e = E.eval_expr env e

(* ------------------------------------------------------------------ *)
(* 1. Worked identity cases (compared via canonical key)              *)
(* ------------------------------------------------------------------ *)

(* Compare simplify(actual) to simplify(expected). *)
let check_simpl ~name actual expected =
  check_true ~cat:"worked-identity" ~name (keq (Sm.simplify actual) (Sm.simplify expected))

let x = sym "x"

let () =
  (* --- simplify: numeric folding + identities (algebra basics) --- *)
  check_simpl ~name:"simplify(2+3) = 5" (eadd (ei 2) (ei 3)) (ei 5);
  check_simpl ~name:"simplify(2*3) = 6" (emul (ei 2) (ei 3)) (ei 6);
  check_simpl ~name:"simplify(2^3) = 8" (epow (ei 2) (ei 3)) (ei 8);
  check_simpl ~name:"simplify(6/2) = 3" (ediv (ei 6) (ei 2)) (ei 3);
  check_simpl ~name:"simplify(x+0) = x  (additive identity)" (eadd x (ei 0)) x;
  check_simpl ~name:"simplify(0+x) = x" (eadd (ei 0) x) x;
  check_simpl ~name:"simplify(x*1) = x  (multiplicative identity)" (emul x (ei 1)) x;
  check_simpl ~name:"simplify(x*0) = 0  (annihilation)" (emul x (ei 0)) (ei 0);
  check_simpl ~name:"simplify(x-0) = x" (esub x (ei 0)) x;
  check_simpl ~name:"simplify(x^1) = x" (epow x (ei 1)) x;
  check_simpl ~name:"simplify(x/1) = x" (ediv x (ei 1)) x;
  (* like-term collection + power combination *)
  check_simpl ~name:"simplify(x+x) = 2*x  (coefficient collection)"
    (eadd x x) (emul (ei 2) x);
  check_simpl ~name:"simplify(x+x+x) = 3*x"
    (eaddn [x; x; x]) (emul (ei 3) x);
  check_simpl ~name:"simplify(x*x) = x^2  (exponent combination)"
    (emul x x) (epow x (ei 2));
  check_simpl ~name:"simplify(x^2 * x^3) = x^5"
    (emul (epow x (ei 2)) (epow x (ei 3))) (epow x (ei 5));
  check_simpl ~name:"simplify flattens nested plus  ((x+2)+3) = x+5"
    (eadd (eadd x (ei 2)) (ei 3)) (eadd x (ei 5));
  check_simpl ~name:"simplify constant-folds inside a symbolic sum  (2+x+3) = x+5"
    (eaddn [ei 2; x; ei 3]) (eadd x (ei 5));

  (* --- diff: derivative identities (result run through simplify) --- *)
  check_simpl ~name:"d/dx x^2 = 2x  (power rule)"
    (D.diff "x" (epow x (ei 2))) (emul (ei 2) x);
  check_simpl ~name:"d/dx x^3 = 3x^2"
    (D.diff "x" (epow x (ei 3))) (emul (ei 3) (epow x (ei 2)));
  check_simpl ~name:"d/dx (x^2 + 3x + 5) = 2x + 3"
    (D.diff "x" (eaddn [epow x (ei 2); emul (ei 3) x; ei 5]))
    (eadd (emul (ei 2) x) (ei 3));
  check_simpl ~name:"d/dx c = 0  (constant)"
    (D.diff "x" (ei 7)) (ei 0);
  check_simpl ~name:"d/dx y = 0  (independent symbol)"
    (D.diff "x" (sym "y")) (ei 0);
  check_simpl ~name:"d/dx x = 1"
    (D.diff "x" x) (ei 1);
  check_simpl ~name:"d/dx sin x = cos x"
    (D.diff "x" (fapp1 "sin" x)) (fapp1 "cos" x);
  check_simpl ~name:"d/dx cos x = -sin x"
    (D.diff "x" (fapp1 "cos" x)) (eneg (fapp1 "sin" x));
  check_simpl ~name:"d/dx exp x = exp x"
    (D.diff "x" (fapp1 "exp" x)) (fapp1 "exp" x);
  check_simpl ~name:"d/dx ln x = 1/x"
    (D.diff "x" (fapp1 "ln" x)) (ediv (ei 1) x);
  check_simpl ~name:"d/dx sin(x^2) = 2*x*cos(x^2)  (chain rule)"
    (D.diff "x" (fapp1 "sin" (epow x (ei 2))))
    (emuln [ei 2; x; fapp1 "cos" (epow x (ei 2))]);
  check_simpl ~name:"d/dx (x * sin x) = sin x + x*cos x  (product rule)"
    (D.diff "x" (emul x (fapp1 "sin" x)))
    (eadd (fapp1 "sin" x) (emul x (fapp1 "cos" x)));
  check_simpl ~name:"d/dx exp(sin x) = cos x * exp(sin x)  (chain rule)"
    (D.diff "x" (fapp1 "exp" (fapp1 "sin" x)))
    (emul (fapp1 "cos" x) (fapp1 "exp" (fapp1 "sin" x)));

  (* --- diff soundness marker: uncovered function is NOT guessed --- *)
  check_true ~cat:"diff-soundness-marker"
    ~name:"d/dx of an uncovered function (arcsin) yields an explicit marker, not a wrong value"
    (match Sm.simplify (D.diff "x" (fapp1 "arcsin" x)) with
     | E.E_App ("diff_unsupported", _) -> true
     | _ -> false)

(* ------------------------------------------------------------------ *)
(* 2a. diff soundness oracle: central finite difference               *)
(* ------------------------------------------------------------------ *)

(* h = 1/1000, tolerance = 1/100. Both exact rationals. *)
let fd_check ~name (f : E.expr) (xn, xd) =
  let d = D.diff "x" f in
  (* x0 +/- h as rationals with common denom xd*1000 *)
  let hplus_n = xn * 1000 + xd and hden = xd * 1000 in
  let hminus_n = xn * 1000 - xd in
  let fph = eval_at [("x", mv_rat hplus_n hden)] f in
  let fmh = eval_at [("x", mv_rat hminus_n hden)] f in
  let dv  = eval_at (env_x xn xd) d in
  if is_undef fph || is_undef fmh || is_undef dv then
    check_true ~cat:"diff-oracle-setup" ~name:(name ^ " [eval defined]") false
  else begin
    (* central = (fph - fmh) / (2h),  2h = 2/1000 = 1/500 *)
    let central = E.m_div (E.m_sub fph fmh) (mv_rat 2 1000) in
    let err = E.m_abs (E.m_sub dv central) in
    let tol = mv_rat 1 100 in
    let ok = match E.rat_cmp err tol with
      | FStar_Pervasives_Native.Some c -> Z.leq c Z.zero
      | FStar_Pervasives_Native.None -> false in
    check_true ~cat:"diff-oracle" ~name ok
  end

let () =
  (* Algebraic f only (eval is exact but undefined for trig/exp/ln). *)
  let cases : (string * E.expr) list = [
    "x^2",                 epow x (ei 2);
    "x^3",                 epow x (ei 3);
    "x^4",                 epow x (ei 4);
    "x^2+3x+5",            eaddn [epow x (ei 2); emul (ei 3) x; ei 5];
    "x*x (product rule)",  emul x x;
    "x^2 * x^3 (product)", emul (epow x (ei 2)) (epow x (ei 3));
    "(x+1)^2 (power/chain)", epow (eadd x (ei 1)) (ei 2);
    "1/x (quotient)",      ediv (ei 1) x;
    "x/(x^2+1) (quotient)", ediv x (eadd (epow x (ei 2)) (ei 1));
    "x^3 - 2x (minus)",    esub (epow x (ei 3)) (emul (ei 2) x);
    "(2x+1)*(x-3) (product)", emul (eadd (emul (ei 2) x) (ei 1)) (esub x (ei 3));
  ] in
  let points = [ (2,1); (3,1); (1,2); (5,2); (7,3) ] in
  List.iter (fun (nm, f) ->
    List.iter (fun (pn, pd) ->
      fd_check ~name:(Printf.sprintf "d/dx %s at x=%d/%d matches finite difference" nm pn pd)
        f (pn, pd)
    ) points
  ) cases

(* ------------------------------------------------------------------ *)
(* 2b. subst soundness: eval(subst x v f) == eval f [x := eval v]      *)
(* ------------------------------------------------------------------ *)

let subst_check ~name (f : E.expr) (v : E.expr) =
  let lhs = eval_at [] (S.subst "x" v f) in
  let vv = eval_at [] v in
  let rhs = eval_at [("x", vv)] f in
  check ~cat:"subst-soundness" ~name (E.value_to_string rhs) (E.value_to_string lhs)

let () =
  let fs : (string * E.expr) list = [
    "x^2+1",     eadd (epow x (ei 2)) (ei 1);
    "x^3 - 2x",  esub (epow x (ei 3)) (emul (ei 2) x);
    "(x+1)*(x-1)", emul (eadd x (ei 1)) (esub x (ei 1));
    "x/(x^2+1)", ediv x (eadd (epow x (ei 2)) (ei 1));
  ] in
  let vs : (string * E.expr) list = [
    "3",   ei 3;
    "-4",  ei (-4);
    "5/2", erat 5 2;
    "0",   ei 0;
  ] in
  List.iter (fun (fn, f) ->
    List.iter (fun (vn, v) ->
      subst_check ~name:(Printf.sprintf "subst x:=%s in %s" vn fn) f v
    ) vs
  ) fs

(* ------------------------------------------------------------------ *)
(* 2c. simplify idempotence: key(simplify(simplify e)) = key(simplify e)*)
(* ------------------------------------------------------------------ *)

let idem_check ~name (e : E.expr) =
  let s1 = Sm.simplify e in
  let s2 = Sm.simplify s1 in
  check ~cat:"simplify-idempotence" ~name (key s1) (key s2)

let () =
  let es : (string * E.expr) list = [
    "2+3",             eadd (ei 2) (ei 3);
    "x+0",             eadd x (ei 0);
    "x+x",             eadd x x;
    "x*x",             emul x x;
    "nested plus",     eadd (eadd (eadd x (ei 1)) x) (ei 2);
    "nested times",    emuln [emul (ei 2) x; x; ei 3];
    "x^2 * x^3",       emul (epow x (ei 2)) (epow x (ei 3));
    "x^2 * x^-2",      emul (epow x (ei 2)) (epow x (ei (-2)));
    "sin(x)+sin(x)",   eadd (fapp1 "sin" x) (fapp1 "sin" x);
    "diff of x^5",     D.diff "x" (epow x (ei 5));
    "diff of x*sin x", D.diff "x" (emul x (fapp1 "sin" x));
    "diff of sin(x^2)",D.diff "x" (fapp1 "sin" (epow x (ei 2)));
    "diff of x^x (general power rule)", D.diff "x" (epow x x);
    "diff of arcsin (unsupported marker)", D.diff "x" (fapp1 "arcsin" x);
    "big mixed", eaddn [emul (ei 2) x; emul (ei 3) x; ei 4; ei 5; epow x (ei 2); emul x x];
  ] in
  List.iter (fun (nm, e) -> idem_check ~name:("idempotent: " ^ nm) e) es

(* ------------------------------------------------------------------ *)
(* 2d. simplify soundness: eval(simplify f) == eval f  (closed inst.)  *)
(* ------------------------------------------------------------------ *)

let simpl_eval_check ~name (f : E.expr) (xn, xd) =
  let sv = eval_at (env_x xn xd) (Sm.simplify f) in
  let fv = eval_at (env_x xn xd) f in
  check ~cat:"simplify-soundness" ~name (E.value_to_string fv) (E.value_to_string sv)

let () =
  let fs : (string * E.expr) list = [
    "x+x",              eadd x x;
    "x*x",              emul x x;
    "2+x+3",            eaddn [ei 2; x; ei 3];
    "x^2 * x^3",        emul (epow x (ei 2)) (epow x (ei 3));
    "(x+1)+(x+2)",      eadd (eadd x (ei 1)) (eadd x (ei 2));
    "3*x + x",          eadd (emul (ei 3) x) x;
    "x*1 + 0",          eadd (emul x (ei 1)) (ei 0);
    "6/2 * x",          emul (ediv (ei 6) (ei 2)) x;
    "diff(x^3 - 2x)",   D.diff "x" (esub (epow x (ei 3)) (emul (ei 2) x));
  ] in
  let points = [ (2,1); (3,1); (5,2); (1,3) ] in
  List.iter (fun (nm, f) ->
    List.iter (fun (pn, pd) ->
      simpl_eval_check ~name:(Printf.sprintf "eval(simplify %s) = eval(%s) at x=%d/%d" nm nm pn pd)
        f (pn, pd)
    ) points
  ) fs

(* ------------------------------------------------------------------ *)
(* Summary                                                            *)
(* ------------------------------------------------------------------ *)

let () =
  Printf.printf "\n";
  if Hashtbl.length fail_cats > 0 then begin
    Printf.printf "failing categories:\n";
    Hashtbl.iter (fun cat n -> Printf.printf "  %s: %d\n" cat n) fail_cats
  end;
  Printf.printf "CAS: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
