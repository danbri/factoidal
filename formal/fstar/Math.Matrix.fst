module Math.Matrix

// Verified exact-rational linear algebra, built ON TOP of Math.Expr's
// exact value type (mvalue = MV_Rat num den | MV_Bool | MV_Undef). This
// module is domain-neutral (no MathML knowledge); the Content MathML
// front-end (MathML.Content.fst) maps <matrix>/<vector>/<apply> trees
// onto the operations here, exactly as it already maps scalar <apply>
// nodes onto Math.Expr.apply_fn.
//
// SHAPE DISCIPLINE (the interesting F-star part)
// ----------------------------------------------
// A matrix is a dimension-indexed refinement type
//     matrix r c = rows:(list (list mvalue)){length rows = r /\ rect c rows}
// so the row-count and every row-width are part of the TYPE. The core
// operations are STATICALLY-SHAPED: their signatures make an ill-shaped
// call a type error, and their result shape is PROVEN, never checked.
//   * mat_add / mat_sub : matrix r c -> matrix r c -> matrix r c
//   * scalar_mul_m      : mvalue -> matrix r c -> matrix r c
//   * transpose_m       : matrix r c -> matrix c r
//   * mat_mul           : matrix r1 c1 -> matrix r2 c2 -> matrix r1 c2
//                         with PRECONDITION (requires c1 == r2) --
//                         the inner dimensions must agree or the term
//                         does not type-check.
//   * identity_m n      : matrix n n
//   * trace_m / determinant : square by refinement (require length = n
//                         and rect n).
// Vector ops (dot, cross) carry the length in the type (vector n) with a
// requires-length precondition.
//
// The MathML front-end cannot know dimensions statically (they come from
// runtime XML), so a DYNAMICALLY-CHECKED adapter layer sits on top:
// amatrix packs (r, c, matrix r c) existentially, mk_amatrix validates
// rectangularity once, and the dyn_* operators check dimension agreement
// at RUNTIME, turning a mismatch into an explicit R_Undef -- never a
// bogus matrix (the project's soundness discipline). The dyn_* layer is
// a thin wrapper: all shape correctness of the RESULT still comes from
// the statically-shaped core.

open FStar.String
open FStar.List.Tot
open Math.Expr

(* ================================================================ *)
(* Rectangularity predicate and the dimension-indexed matrix type    *)
(* ================================================================ *)

// rect c rows: every row has exactly c entries.
let rec rect (c:nat) (rows:list (list mvalue)) : Tot bool (decreases rows) =
  match rows with
  | [] -> true
  | h :: t -> (length h = c) && rect c t

// A matrix carries its shape in the type: r rows, each of width c.
type matrix (r:nat) (c:nat) = rows:(list (list mvalue)){length rows = r /\ rect c rows}

// A vector of length n.
type mvec (n:nat) = v:(list mvalue){length v = n}

// rect implies each indexed row has width c.
let rec rect_index_lemma (c:nat) (rows:list (list mvalue)) (i:nat)
  : Lemma (requires rect c rows /\ i < length rows)
          (ensures length (index rows i) = c)
          (decreases rows)
=
  match rows with
  | h :: t -> if i = 0 then () else rect_index_lemma c t (i - 1)

(* ================================================================ *)
(* Row-level exact-rational helpers                                  *)
(* ================================================================ *)

// Elementwise binary op on two equal-length rows.
let rec row_binop (f:(mvalue -> mvalue -> mvalue)) (a:list mvalue) (b:list mvalue)
  : Pure (list mvalue)
    (requires length a = length b)
    (ensures fun res -> length res = length a)
    (decreases a)
=
  match a, b with
  | [], [] -> []
  | x :: xs, y :: ys -> f x y :: row_binop f xs ys

// Exact dot product of two equal-length rows (sum of products).
let rec row_dot (a:list mvalue) (b:list mvalue)
  : Pure mvalue
    (requires length a = length b)
    (ensures fun _ -> True)
    (decreases a)
=
  match a, b with
  | [], [] -> MV_Rat 0 1
  | x :: xs, y :: ys -> m_add (m_mul x y) (row_dot xs ys)

// Scale every entry of a row by a scalar.
let rec scale_row (s:mvalue) (v:list mvalue)
  : Pure (list mvalue)
    (requires True)
    (ensures fun res -> length res = length v)
    (decreases v)
=
  match v with
  | [] -> []
  | y :: ys -> m_mul s y :: scale_row s ys

(* ================================================================ *)
(* Statically-shaped core: add / sub / scalar-mul                    *)
(* ================================================================ *)

let rec addsub_rows (f:(mvalue -> mvalue -> mvalue)) (c:nat)
                    (a:list (list mvalue)) (b:list (list mvalue))
  : Pure (list (list mvalue))
    (requires rect c a /\ rect c b /\ length a = length b)
    (ensures fun res -> length res = length a /\ rect c res)
    (decreases a)
=
  match a, b with
  | [], [] -> []
  | ha :: ta, hb :: tb -> row_binop f ha hb :: addsub_rows f c ta tb
  | _, _ -> []

let mat_add (r:nat) (c:nat) (a:matrix r c) (b:matrix r c) : matrix r c =
  addsub_rows m_add c a b

let mat_sub (r:nat) (c:nat) (a:matrix r c) (b:matrix r c) : matrix r c =
  addsub_rows m_sub c a b

let rec smul_rows (s:mvalue) (c:nat) (rows:list (list mvalue))
  : Pure (list (list mvalue))
    (requires rect c rows)
    (ensures fun res -> length res = length rows /\ rect c res)
    (decreases rows)
=
  match rows with
  | [] -> []
  | h :: t -> scale_row s h :: smul_rows s c t

let scalar_mul_m (s:mvalue) (r:nat) (c:nat) (m:matrix r c) : matrix r c =
  smul_rows s c m

let mat_neg (r:nat) (c:nat) (m:matrix r c) : matrix r c =
  smul_rows (MV_Rat (-1) 1) c m

(* ================================================================ *)
(* Statically-shaped core: transpose                                 *)
(* ================================================================ *)

// First entry of each row (rows are width c >= 1, so each is non-empty).
let rec map_head (c:nat) (rows:list (list mvalue))
  : Pure (list mvalue)
    (requires c >= 1 /\ rect c rows)
    (ensures fun res -> length res = length rows)
    (decreases rows)
=
  match rows with
  | [] -> []
  | h :: t -> (match h with | x :: _ -> x | [] -> MV_Undef "unreachable") :: map_head c t

// Drop the first entry of each row (width c -> width c-1).
let rec map_tail (c:nat) (rows:list (list mvalue))
  : Pure (list (list mvalue))
    (requires c >= 1 /\ rect c rows)
    (ensures fun res -> length res = length rows /\ rect (c - 1) res)
    (decreases rows)
=
  match rows with
  | [] -> []
  | h :: t -> (match h with | _ :: xs -> xs | [] -> []) :: map_tail c t

let rec transpose_build (r:nat) (c:nat) (rows:list (list mvalue))
  : Pure (list (list mvalue))
    (requires length rows = r /\ rect c rows)
    (ensures fun res -> length res = c /\ rect r res)
    (decreases c)
=
  if c = 0 then []
  else map_head c rows :: transpose_build r (c - 1) (map_tail c rows)

let transpose_m (r:nat) (c:nat) (m:matrix r c) : matrix c r =
  transpose_build r c m

(* ================================================================ *)
(* Statically-shaped core: matrix multiply                           *)
(*                                                                   *)
(* mat_mul's precondition (requires c1 == r2) is where "inner         *)
(* dimensions must agree" lives: a caller cannot even form the term   *)
(* unless the shared dimension matches. The result shape matrix r1 c2 *)
(* is proven, not checked.                                            *)
(* ================================================================ *)

// One output row: dot the a-row against every row of b-transposed.
let rec mul_one_row (arow:list mvalue) (bt:list (list mvalue)) (k:nat)
  : Pure (list mvalue)
    (requires length arow = k /\ rect k bt)
    (ensures fun res -> length res = length bt)
    (decreases bt)
=
  match bt with
  | [] -> []
  | brow :: rest -> row_dot arow brow :: mul_one_row arow rest k

let rec mul_all_rows (a:list (list mvalue)) (bt:list (list mvalue)) (k:nat) (p:nat)
  : Pure (list (list mvalue))
    (requires rect k a /\ rect k bt /\ length bt = p)
    (ensures fun res -> length res = length a /\ rect p res)
    (decreases a)
=
  match a with
  | [] -> []
  | arow :: rest -> mul_one_row arow bt k :: mul_all_rows rest bt k p

let mat_mul (r1:nat) (c1:nat) (r2:nat) (c2:nat) (a:matrix r1 c1) (b:matrix r2 c2)
  : Pure (matrix r1 c2)
    (requires c1 == r2)
    (ensures fun _ -> True)
=
  let bt : matrix c2 r2 = transpose_m r2 c2 b in
  // bt has width r2 = c1, so it is rect c1; each a-row also has width c1.
  mul_all_rows a bt c1 c2

(* ================================================================ *)
(* Statically-shaped core: identity, trace, determinant (square)     *)
(* ================================================================ *)

// A length-n row that is 1 at position i and 0 elsewhere.
let rec unit_row (n:nat) (i:nat)
  : Pure (list mvalue)
    (requires True)
    (ensures fun res -> length res = n)
    (decreases n)
=
  if n = 0 then []
  else (if i = 0 then MV_Rat 1 1 else MV_Rat 0 1)
       :: unit_row (n - 1) (if i = 0 then n else i - 1)

let rec ident_build (n:nat) (k:nat)
  : Pure (list (list mvalue))
    (requires k <= n)
    (ensures fun res -> length res = n - k /\ rect n res)
    (decreases (n - k))
=
  if k = n then []
  else unit_row n k :: ident_build n (k + 1)

let identity_m (n:nat) : matrix n n = ident_build n 0

// Element (i,j) of a rect-c matrix (both indices in range).
let mat_elem (c:nat) (rows:list (list mvalue){rect c rows})
             (i:nat{i < length rows}) (j:nat{j < c}) : mvalue =
  rect_index_lemma c rows i;
  index (index rows i) j

let rec trace_acc (n:nat) (i:nat) (rows:list (list mvalue))
  : Pure mvalue
    (requires length rows = n /\ rect n rows /\ i <= n)
    (ensures fun _ -> True)
    (decreases (n - i))
=
  if i = n then MV_Rat 0 1
  else m_add (mat_elem n rows i i) (trace_acc n (i + 1) rows)

let trace_m (n:nat) (m:matrix n n) : mvalue = trace_acc n 0 m

// Delete entry j from a non-short row.
let rec del_at (j:nat) (xs:list mvalue)
  : Pure (list mvalue)
    (requires j < length xs)
    (ensures fun res -> length res = length xs - 1)
    (decreases xs)
=
  match xs with
  | h :: t -> if j = 0 then t else h :: del_at (j - 1) t

// Delete column j from every row (width n -> width n-1).
let rec del_col (n:nat) (j:nat) (rows:list (list mvalue))
  : Pure (list (list mvalue))
    (requires n >= 1 /\ j < n /\ rect n rows)
    (ensures fun res -> length res = length rows /\ rect (n - 1) res)
    (decreases rows)
=
  match rows with
  | [] -> []
  | h :: t -> del_at j h :: del_col n j t

// Laplace / cofactor expansion along the first row. det of the 0x0
// matrix is 1 by convention. Mutually recursive with cofactor_sum,
// ordered lexicographically by [n; tag; n-j].
let rec det_rows (n:nat) (rows:list (list mvalue){length rows = n /\ rect n rows})
  : Tot mvalue (decreases %[n; 1; 0])
=
  if n = 0 then MV_Rat 1 1
  else
    match rows with
    | head :: tail -> cofactor_sum n 0 head tail
    | [] -> MV_Rat 0 1

and cofactor_sum (n:nat) (j:nat)
                 (head:list mvalue{length head = n})
                 (tail:list (list mvalue){length tail = n - 1 /\ rect n tail})
  : Tot mvalue (decreases %[n; 0; n - j])
=
  if j >= n then MV_Rat 0 1
  else
    let a0j = index head j in
    let sign = if j % 2 = 0 then MV_Rat 1 1 else MV_Rat (-1) 1 in
    let minor = del_col n j tail in
    // minor is (n-1) x (n-1): length tail = n-1 rows, each width n-1.
    let sub = det_rows (n - 1) minor in
    let term = m_mul sign (m_mul a0j sub) in
    m_add term (cofactor_sum n (j + 1) head tail)

let determinant (n:nat) (rows:list (list mvalue){length rows = n /\ rect n rows}) : mvalue =
  det_rows n rows

(* ================================================================ *)
(* Vector operations                                                 *)
(* ================================================================ *)

let vec_dot (a:list mvalue) (b:list mvalue)
  : Pure mvalue (requires length a = length b) (ensures fun _ -> True) =
  row_dot a b

// Cross product of two 3-vectors -> a 3-vector.
let cross3 (a:list mvalue) (b:list mvalue)
  : Pure (list mvalue)
    (requires length a = 3 /\ length b = 3)
    (ensures fun res -> length res = 3)
=
  let a1 = index a 0 in let a2 = index a 1 in let a3 = index a 2 in
  let b1 = index b 0 in let b2 = index b 1 in let b3 = index b 2 in
  [ m_sub (m_mul a2 b3) (m_mul a3 b2);
    m_sub (m_mul a3 b1) (m_mul a1 b3);
    m_sub (m_mul a1 b2) (m_mul a2 b1) ]

// Outer product u (length nu) (x) v (length nv) -> nu x nv matrix.
let rec outer_build (u:list mvalue) (v:list mvalue) (nv:nat)
  : Pure (list (list mvalue))
    (requires length v = nv)
    (ensures fun res -> length res = length u /\ rect nv res)
    (decreases u)
=
  match u with
  | [] -> []
  | x :: xs -> scale_row x v :: outer_build xs v nv

(* ================================================================ *)
(* Dynamically-checked adapter layer (for the MathML front-end)      *)
(*                                                                   *)
(* amatrix packs (r, c, matrix r c). mk_amatrix validates             *)
(* rectangularity once; every dyn_* operator checks dimension         *)
(* agreement at runtime and yields R_Undef on mismatch. The RESULT    *)
(* shape is always produced by the statically-shaped core above, so a *)
(* bogus (non-rectangular) matrix can never be constructed here.      *)
(* ================================================================ *)

type amatrix =
  | AMat : r:nat -> c:nat -> rows:matrix r c -> amatrix

// Evaluation result: a scalar, a matrix, a vector, or an explicit
// undefined (dimension mismatch, non-square determinant, etc.).
type mres =
  | R_Scalar : v:mvalue -> mres
  | R_Matrix : m:amatrix -> mres
  | R_Vector : n:nat -> v:mvec n -> mres
  | R_Undef  : reason:string -> mres

// Validate a raw list-of-rows into a packed matrix, or None if ragged.
let mk_amatrix (rows:list (list mvalue)) : option amatrix =
  let nr = length rows in
  let nc = match rows with | [] -> 0 | h :: _ -> length h in
  if rect nc rows then Some (AMat nr nc rows) else None

let mk_matrix_res (rows:list (list mvalue)) : mres =
  match mk_amatrix rows with
  | Some am -> R_Matrix am
  | None -> R_Undef "non-rectangular-matrix"

let mk_vector_res (v:list mvalue) : mres = R_Vector (length v) v

let dyn_add (x:mres) (y:mres) : mres =
  match x, y with
  | R_Undef s, _ -> R_Undef s
  | _, R_Undef s -> R_Undef s
  | R_Scalar a, R_Scalar b -> R_Scalar (m_add a b)
  | R_Matrix (AMat r1 c1 a), R_Matrix (AMat r2 c2 b) ->
    if r1 = r2 && c1 = c2 then R_Matrix (AMat r1 c1 (mat_add r1 c1 a b))
    else R_Undef "matrix-add-shape-mismatch"
  | _, _ -> R_Undef "add-type-mismatch"

let dyn_sub (x:mres) (y:mres) : mres =
  match x, y with
  | R_Undef s, _ -> R_Undef s
  | _, R_Undef s -> R_Undef s
  | R_Scalar a, R_Scalar b -> R_Scalar (m_sub a b)
  | R_Matrix (AMat r1 c1 a), R_Matrix (AMat r2 c2 b) ->
    if r1 = r2 && c1 = c2 then R_Matrix (AMat r1 c1 (mat_sub r1 c1 a b))
    else R_Undef "matrix-sub-shape-mismatch"
  | _, _ -> R_Undef "sub-type-mismatch"

// times: scalar*scalar, scalar*matrix (either order), matrix*matrix.
let dyn_times (x:mres) (y:mres) : mres =
  match x, y with
  | R_Undef s, _ -> R_Undef s
  | _, R_Undef s -> R_Undef s
  | R_Scalar a, R_Scalar b -> R_Scalar (m_mul a b)
  | R_Scalar s, R_Matrix (AMat r c m) -> R_Matrix (AMat r c (scalar_mul_m s r c m))
  | R_Matrix (AMat r c m), R_Scalar s -> R_Matrix (AMat r c (scalar_mul_m s r c m))
  | R_Matrix (AMat r1 c1 a), R_Matrix (AMat r2 c2 b) ->
    if c1 = r2 then R_Matrix (AMat r1 c2 (mat_mul r1 c1 r2 c2 a b))
    else R_Undef "matrix-multiply-inner-dimension-mismatch"
  | _, _ -> R_Undef "times-type-mismatch"

let dyn_transpose (x:mres) : mres =
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat r c m) -> R_Matrix (AMat c r (transpose_m r c m))
  | _ -> R_Undef "transpose-requires-matrix"

let dyn_determinant (x:mres) : mres =
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat r c m) ->
    if r = c then R_Scalar (determinant r m)
    else R_Undef "determinant-requires-square-matrix"
  | _ -> R_Undef "determinant-requires-matrix"

let dyn_trace (x:mres) : mres =
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat r c m) ->
    if r = c then R_Scalar (trace_m r m)
    else R_Undef "trace-requires-square-matrix"
  | _ -> R_Undef "trace-requires-matrix"

let dyn_scalarproduct (x:mres) (y:mres) : mres =
  match x, y with
  | R_Undef s, _ -> R_Undef s
  | _, R_Undef s -> R_Undef s
  | R_Vector n1 u, R_Vector n2 v ->
    if n1 = n2 then R_Scalar (vec_dot u v)
    else R_Undef "scalarproduct-length-mismatch"
  | _, _ -> R_Undef "scalarproduct-requires-vectors"

let dyn_vectorproduct (x:mres) (y:mres) : mres =
  match x, y with
  | R_Undef s, _ -> R_Undef s
  | _, R_Undef s -> R_Undef s
  | R_Vector n1 u, R_Vector n2 v ->
    if n1 = 3 && n2 = 3 then R_Vector 3 (cross3 u v)
    else R_Undef "vectorproduct-requires-3-vectors"
  | _, _ -> R_Undef "vectorproduct-requires-vectors"

let dyn_outerproduct (x:mres) (y:mres) : mres =
  match x, y with
  | R_Undef s, _ -> R_Undef s
  | _, R_Undef s -> R_Undef s
  | R_Vector n1 u, R_Vector n2 v ->
    R_Matrix (AMat n1 n2 (outer_build u v n2))
  | _, _ -> R_Undef "outerproduct-requires-vectors"

// selector(A, i, j) on a matrix (1-based MathML indices) -> element.
let dyn_selector_matrix (x:mres) (i1:int) (j1:int) : mres =
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat r c m) ->
    if i1 >= 1 && j1 >= 1 && i1 <= r && j1 <= c then
      let i:nat = i1 - 1 in let j:nat = j1 - 1 in
      // i < r = length m, j < c
      R_Scalar (mat_elem c m i j)
    else R_Undef "selector-index-out-of-range"
  | R_Vector n v ->
    if i1 >= 1 && i1 <= n then
      let i:nat = i1 - 1 in
      R_Scalar (index v i)
    else R_Undef "selector-index-out-of-range"
  | _ -> R_Undef "selector-requires-matrix-or-vector"

(* ================================================================ *)
(* Canonical string form of a result (for exact test comparison)     *)
(* ================================================================ *)

// Scalars stringify exactly as Math.Expr does ("n", "num/den",
// "true"/"false", "undef"). A vector is "[a,b,c]"; a matrix is
// "[[a,b],[c,d]]" (rows comma-separated, each row bracketed) -- the
// nesting keeps the two unambiguous. Undefined collapses to "undef".
let row_to_string (v:list mvalue) : string =
  String.concat "" ["["; String.concat "," (List.Tot.map Math.Expr.value_to_string v); "]"]

let mres_to_string (x:mres) : string =
  match x with
  | R_Scalar v -> Math.Expr.value_to_string v
  | R_Vector _ v -> row_to_string v
  | R_Matrix (AMat _ _ rows) ->
    String.concat "" ["["; String.concat "," (List.Tot.map row_to_string rows); "]"]
  | R_Undef _ -> "undef"

let mres_reason (x:mres) : string =
  match x with
  | R_Undef r -> r
  | R_Scalar v -> Math.Expr.value_reason v
  | _ -> ""
