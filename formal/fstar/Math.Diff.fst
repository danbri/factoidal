module Math.Diff

// Symbolic differentiation over Math.Expr.expr. Total and structural
// (recursion on the strict subterm ordering — no fuel). Soundness over
// coverage: any construct we do not have a rule for is returned wrapped
// in an explicit E_App "diff_unsupported" marker rather than guessing a
// derivative. eval never fabricates a value for such a marker (it is an
// unknown function name), so a missing rule can never masquerade as a
// wrong answer.
//
// Rules implemented (differentiation w.r.t. a symbol x):
//   * constants (E_Int / E_Rat / E_Bool)            -> 0
//   * the variable x                                -> 1
//   * any other symbol                              -> 0
//   * plus (n-ary)          : sum of derivatives
//   * minus (unary / binary): negation / difference of derivatives
//   * times (n-ary)         : full product rule
//   * divide (binary)       : quotient rule
//   * power  a^b            : power rule for a literal exponent,
//                             general f^g log-derivative otherwise
//   * root [a]  (sqrt)      : d/dx = a' / (2*sqrt a)
//   * root [k;a] (const k>0): d/dx = (1/k) a^((1-k)/k) a'
//   * sin, cos, exp, ln, tan: chain rule
// Everything else -> diff_unsupported marker.

open Math.Expr
open FStar.List.Tot

// Explicit "no rule" marker. A unique unsupported function name so eval
// reports it undefined rather than producing a bogus number.
let diff_unknown (e:expr) : expr = E_App "diff_unsupported" [e]

let rec diff (x:string) (e:expr) : Tot expr (decreases e) =
  match e with
  | E_Int _ -> E_Int 0
  | E_Rat _ _ -> E_Int 0
  | E_Bool _ -> E_Int 0
  | E_Sym name -> if name = x then E_Int 1 else E_Int 0

  | E_App "plus" args -> E_App "plus" (diff_list x args)

  | E_App "minus" args ->
    (match args with
     | [a] -> e_neg (diff x a)
     | [a; b] -> E_App "minus" [diff x a; diff x b]
     | _ -> diff_unknown e)

  | E_App "times" args -> E_App "plus" (diff_prod x [] args)

  | E_App "divide" args ->
    (match args with
     | [a; b] ->
       // (a'b - a b') / b^2
       E_App "divide"
         [ E_App "minus" [ e_mul (diff x a) b; e_mul a (diff x b) ];
           e_pow b (E_Int 2) ]
     | _ -> diff_unknown e)

  | E_App "power" args ->
    (match args with
     | [a; b] ->
       (match b with
        // power rule for a constant (x-independent) literal exponent:
        // d(a^n) = n * a^(n-1) * a'. Valid for every base a.
        | E_Int n -> e_mul (e_mul (E_Int n) (e_pow a (E_Int (n - 1)))) (diff x a)
        | E_Rat p q -> e_mul (e_mul (E_Rat p q) (e_pow a (E_Rat (p - q) q))) (diff x a)
        // general f^g = f^g * (g' ln f + g f'/f); sound where f > 0.
        | _ ->
          let fg = e_pow a b in
          e_mul fg
            (e_add (e_mul (diff x b) (E_App "ln" [a]))
                   (e_mul b (E_App "divide" [diff x a; a]))))
     | _ -> diff_unknown e)

  | E_App "root" args ->
    (match args with
     | [a] ->
       // sqrt a : d/dx = a' / (2 * sqrt a)
       E_App "divide" [diff x a; e_mul (E_Int 2) (E_App "root" [a])]
     | [E_Int k; a] ->
       if k > 0
       // k-th root = a^(1/k): d/dx = (1/k) a^((1-k)/k) a'
       then e_mul (e_mul (E_Rat 1 k) (e_pow a (E_Rat (1 - k) k))) (diff x a)
       else diff_unknown e
     | _ -> diff_unknown e)

  | E_App "sin" args ->
    (match args with [a] -> e_mul (E_App "cos" [a]) (diff x a) | _ -> diff_unknown e)
  | E_App "cos" args ->
    (match args with [a] -> e_mul (e_neg (E_App "sin" [a])) (diff x a) | _ -> diff_unknown e)
  | E_App "exp" args ->
    (match args with [a] -> e_mul (E_App "exp" [a]) (diff x a) | _ -> diff_unknown e)
  | E_App "ln" args ->
    (match args with [a] -> E_App "divide" [diff x a; a] | _ -> diff_unknown e)
  | E_App "tan" args ->
    (match args with
     | [a] -> E_App "divide" [diff x a; e_pow (E_App "cos" [a]) (E_Int 2)]
     | _ -> diff_unknown e)

  | E_App _ _ -> diff_unknown e

and diff_list (x:string) (es:list expr) : Tot (list expr) (decreases es) =
  match es with
  | [] -> []
  | h :: t -> diff x h :: diff_list x t

// Product rule for an n-ary product. For factors args = [f0; ...; fk],
// the derivative is the sum over i of (product with fi replaced by fi').
// pre accumulates the already-visited (undifferentiated) factors.
and diff_prod (x:string) (pre:list expr) (args:list expr)
  : Tot (list expr) (decreases args) =
  match args with
  | [] -> []
  | a :: rest ->
    let term = E_App "times" (append pre (diff x a :: rest)) in
    term :: diff_prod x (append pre [a]) rest
