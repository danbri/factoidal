module Math.Subst

// Symbolic substitution over Math.Expr.expr: replace every occurrence
// of a symbol by a replacement expression. Building block for the
// verified CAS layer (Math.Diff / Math.Simplify). Structural, total,
// no fuel needed — recursion is on the strict subterm ordering.

open Math.Expr

// subst x v e = e with every (E_Sym x) replaced by v.
let rec subst (x:string) (v:expr) (e:expr) : Tot expr (decreases e) =
  match e with
  | E_Int _ -> e
  | E_Rat _ _ -> e
  | E_Bool _ -> e
  | E_Sym name -> if name = x then v else e
  | E_App fn args -> E_App fn (subst_list x v args)

and subst_list (x:string) (v:expr) (es:list expr) : Tot (list expr) (decreases es) =
  match es with
  | [] -> []
  | h :: t -> subst x v h :: subst_list x v t
