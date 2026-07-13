open Prims
let rec rect (c : Prims.nat) (rows : Math_Expr.mvalue Prims.list Prims.list)
  : Prims.bool=
  match rows with
  | [] -> true
  | h::t -> ((FStar_List_Tot_Base.length h) = c) && (rect c t)
type ('r, 'c) matrix = Math_Expr.mvalue Prims.list Prims.list
type 'n mvec = Math_Expr.mvalue Prims.list
let rec row_binop
  (f : Math_Expr.mvalue -> Math_Expr.mvalue -> Math_Expr.mvalue)
  (a : Math_Expr.mvalue Prims.list) (b : Math_Expr.mvalue Prims.list) :
  Math_Expr.mvalue Prims.list=
  match (a, b) with
  | ([], []) -> []
  | (x::xs, y::ys) -> (f x y) :: (row_binop f xs ys)
let rec row_dot (a : Math_Expr.mvalue Prims.list)
  (b : Math_Expr.mvalue Prims.list) : Math_Expr.mvalue=
  match (a, b) with
  | ([], []) -> Math_Expr.MV_Rat (Prims.int_zero, Prims.int_one)
  | (x::xs, y::ys) -> Math_Expr.m_add (Math_Expr.m_mul x y) (row_dot xs ys)
let rec scale_row (s : Math_Expr.mvalue) (v : Math_Expr.mvalue Prims.list) :
  Math_Expr.mvalue Prims.list=
  match v with
  | [] -> []
  | y::ys -> (Math_Expr.m_mul s y) :: (scale_row s ys)
let rec addsub_rows
  (f : Math_Expr.mvalue -> Math_Expr.mvalue -> Math_Expr.mvalue)
  (c : Prims.nat) (a : Math_Expr.mvalue Prims.list Prims.list)
  (b : Math_Expr.mvalue Prims.list Prims.list) :
  Math_Expr.mvalue Prims.list Prims.list=
  match (a, b) with
  | ([], []) -> []
  | (ha::ta, hb::tb) -> (row_binop f ha hb) :: (addsub_rows f c ta tb)
  | (uu___, uu___1) -> []
let mat_add (r : Prims.nat) (c : Prims.nat) (a : (Obj.t, Obj.t) matrix)
  (b : (Obj.t, Obj.t) matrix) : (Obj.t, Obj.t) matrix=
  addsub_rows Math_Expr.m_add c a b
let mat_sub (r : Prims.nat) (c : Prims.nat) (a : (Obj.t, Obj.t) matrix)
  (b : (Obj.t, Obj.t) matrix) : (Obj.t, Obj.t) matrix=
  addsub_rows Math_Expr.m_sub c a b
let rec smul_rows (s : Math_Expr.mvalue) (c : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) :
  Math_Expr.mvalue Prims.list Prims.list=
  match rows with | [] -> [] | h::t -> (scale_row s h) :: (smul_rows s c t)
let scalar_mul_m (s : Math_Expr.mvalue) (r : Prims.nat) (c : Prims.nat)
  (m : (Obj.t, Obj.t) matrix) : (Obj.t, Obj.t) matrix= smul_rows s c m
let mat_neg (r : Prims.nat) (c : Prims.nat) (m : (Obj.t, Obj.t) matrix) :
  (Obj.t, Obj.t) matrix=
  smul_rows (Math_Expr.MV_Rat ((Prims.of_int (-1)), Prims.int_one)) c m
let rec map_head (c : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) :
  Math_Expr.mvalue Prims.list=
  match rows with
  | [] -> []
  | h::t ->
      ((match h with | x::uu___ -> x | [] -> Math_Expr.MV_Undef "unreachable"))
      :: (map_head c t)
let rec map_tail (c : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) :
  Math_Expr.mvalue Prims.list Prims.list=
  match rows with
  | [] -> []
  | h::t -> ((match h with | uu___::xs -> xs | [] -> [])) :: (map_tail c t)
let rec transpose_build (r : Prims.nat) (c : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) :
  Math_Expr.mvalue Prims.list Prims.list=
  if c = Prims.int_zero
  then []
  else (map_head c rows) ::
    (transpose_build r (c - Prims.int_one) (map_tail c rows))
let transpose_m (r : Prims.nat) (c : Prims.nat) (m : (Obj.t, Obj.t) matrix) :
  (Obj.t, Obj.t) matrix= transpose_build r c m
let rec mul_one_row (arow : Math_Expr.mvalue Prims.list)
  (bt : Math_Expr.mvalue Prims.list Prims.list) (k : Prims.nat) :
  Math_Expr.mvalue Prims.list=
  match bt with
  | [] -> []
  | brow::rest -> (row_dot arow brow) :: (mul_one_row arow rest k)
let rec mul_all_rows (a : Math_Expr.mvalue Prims.list Prims.list)
  (bt : Math_Expr.mvalue Prims.list Prims.list) (k : Prims.nat)
  (p : Prims.nat) : Math_Expr.mvalue Prims.list Prims.list=
  match a with
  | [] -> []
  | arow::rest -> (mul_one_row arow bt k) :: (mul_all_rows rest bt k p)
let mat_mul (r1 : Prims.nat) (c1 : Prims.nat) (r2 : Prims.nat)
  (c2 : Prims.nat) (a : (Obj.t, Obj.t) matrix) (b : (Obj.t, Obj.t) matrix) :
  (Obj.t, Obj.t) matrix=
  let bt = transpose_m r2 c2 b in mul_all_rows a bt c1 c2
let rec unit_row (n : Prims.nat) (i : Prims.nat) :
  Math_Expr.mvalue Prims.list=
  if n = Prims.int_zero
  then []
  else
    (if i = Prims.int_zero
     then Math_Expr.MV_Rat (Prims.int_one, Prims.int_one)
     else Math_Expr.MV_Rat (Prims.int_zero, Prims.int_one))
    ::
    (unit_row (n - Prims.int_one)
       (if i = Prims.int_zero then n else i - Prims.int_one))
let rec ident_build (n : Prims.nat) (k : Prims.nat) :
  Math_Expr.mvalue Prims.list Prims.list=
  if k = n then [] else (unit_row n k) :: (ident_build n (k + Prims.int_one))
let identity_m (n : Prims.nat) : (Obj.t, Obj.t) matrix=
  ident_build n Prims.int_zero
let mat_elem (c : Prims.nat) (rows : Math_Expr.mvalue Prims.list Prims.list)
  (i : Prims.nat) (j : Prims.nat) : Math_Expr.mvalue=
  FStar_List_Tot_Base.index (FStar_List_Tot_Base.index rows i) j
let rec trace_acc (n : Prims.nat) (i : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) : Math_Expr.mvalue=
  if i = n
  then Math_Expr.MV_Rat (Prims.int_zero, Prims.int_one)
  else
    Math_Expr.m_add (mat_elem n rows i i)
      (trace_acc n (i + Prims.int_one) rows)
let trace_m (n : Prims.nat) (m : (Obj.t, Obj.t) matrix) : Math_Expr.mvalue=
  trace_acc n Prims.int_zero m
let rec del_at (j : Prims.nat) (xs : Math_Expr.mvalue Prims.list) :
  Math_Expr.mvalue Prims.list=
  match xs with
  | h::t ->
      if j = Prims.int_zero then t else h :: (del_at (j - Prims.int_one) t)
let rec del_col (n : Prims.nat) (j : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) :
  Math_Expr.mvalue Prims.list Prims.list=
  match rows with | [] -> [] | h::t -> (del_at j h) :: (del_col n j t)
let rec det_rows (n : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) : Math_Expr.mvalue=
  if n = Prims.int_zero
  then Math_Expr.MV_Rat (Prims.int_one, Prims.int_one)
  else
    (match rows with
     | head::tail -> cofactor_sum n Prims.int_zero head tail
     | [] -> Math_Expr.MV_Rat (Prims.int_zero, Prims.int_one))
and cofactor_sum (n : Prims.nat) (j : Prims.nat)
  (head : Math_Expr.mvalue Prims.list)
  (tail : Math_Expr.mvalue Prims.list Prims.list) : Math_Expr.mvalue=
  if j >= n
  then Math_Expr.MV_Rat (Prims.int_zero, Prims.int_one)
  else
    (let a0j = FStar_List_Tot_Base.index head j in
     let sign =
       if ((mod) j (Prims.of_int (2))) = Prims.int_zero
       then Math_Expr.MV_Rat (Prims.int_one, Prims.int_one)
       else Math_Expr.MV_Rat ((Prims.of_int (-1)), Prims.int_one) in
     let minor = del_col n j tail in
     let sub = det_rows (n - Prims.int_one) minor in
     let term = Math_Expr.m_mul sign (Math_Expr.m_mul a0j sub) in
     Math_Expr.m_add term (cofactor_sum n (j + Prims.int_one) head tail))
let determinant (n : Prims.nat)
  (rows : Math_Expr.mvalue Prims.list Prims.list) : Math_Expr.mvalue=
  det_rows n rows
let vec_dot (a : Math_Expr.mvalue Prims.list)
  (b : Math_Expr.mvalue Prims.list) : Math_Expr.mvalue= row_dot a b
let cross3 (a : Math_Expr.mvalue Prims.list)
  (b : Math_Expr.mvalue Prims.list) : Math_Expr.mvalue Prims.list=
  let a1 = FStar_List_Tot_Base.index a Prims.int_zero in
  let a2 = FStar_List_Tot_Base.index a Prims.int_one in
  let a3 = FStar_List_Tot_Base.index a (Prims.of_int (2)) in
  let b1 = FStar_List_Tot_Base.index b Prims.int_zero in
  let b2 = FStar_List_Tot_Base.index b Prims.int_one in
  let b3 = FStar_List_Tot_Base.index b (Prims.of_int (2)) in
  [Math_Expr.m_sub (Math_Expr.m_mul a2 b3) (Math_Expr.m_mul a3 b2);
  Math_Expr.m_sub (Math_Expr.m_mul a3 b1) (Math_Expr.m_mul a1 b3);
  Math_Expr.m_sub (Math_Expr.m_mul a1 b2) (Math_Expr.m_mul a2 b1)]
let rec outer_build (u : Math_Expr.mvalue Prims.list)
  (v : Math_Expr.mvalue Prims.list) (nv : Prims.nat) :
  Math_Expr.mvalue Prims.list Prims.list=
  match u with | [] -> [] | x::xs -> (scale_row x v) :: (outer_build xs v nv)
type amatrix =
  | AMat of Prims.nat * Prims.nat * (Obj.t, Obj.t) matrix 
let uu___is_AMat (projectee : amatrix) : Prims.bool= true
let __proj__AMat__item__r (projectee : amatrix) : Prims.nat=
  match projectee with | AMat (r, c, rows) -> r
let __proj__AMat__item__c (projectee : amatrix) : Prims.nat=
  match projectee with | AMat (r, c, rows) -> c
let __proj__AMat__item__rows (projectee : amatrix) : (Obj.t, Obj.t) matrix=
  match projectee with | AMat (r, c, rows) -> rows
type mres =
  | R_Scalar of Math_Expr.mvalue 
  | R_Matrix of amatrix 
  | R_Vector of Prims.nat * Obj.t mvec 
  | R_Undef of Prims.string 
let uu___is_R_Scalar (projectee : mres) : Prims.bool=
  match projectee with | R_Scalar v -> true | uu___ -> false
let __proj__R_Scalar__item__v (projectee : mres) : Math_Expr.mvalue=
  match projectee with | R_Scalar v -> v
let uu___is_R_Matrix (projectee : mres) : Prims.bool=
  match projectee with | R_Matrix m -> true | uu___ -> false
let __proj__R_Matrix__item__m (projectee : mres) : amatrix=
  match projectee with | R_Matrix m -> m
let uu___is_R_Vector (projectee : mres) : Prims.bool=
  match projectee with | R_Vector (n, v) -> true | uu___ -> false
let __proj__R_Vector__item__n (projectee : mres) : Prims.nat=
  match projectee with | R_Vector (n, v) -> n
let __proj__R_Vector__item__v (projectee : mres) : Obj.t mvec=
  match projectee with | R_Vector (n, v) -> v
let uu___is_R_Undef (projectee : mres) : Prims.bool=
  match projectee with | R_Undef reason -> true | uu___ -> false
let __proj__R_Undef__item__reason (projectee : mres) : Prims.string=
  match projectee with | R_Undef reason -> reason
let mk_amatrix (rows : Math_Expr.mvalue Prims.list Prims.list) :
  amatrix FStar_Pervasives_Native.option=
  let nr = FStar_List_Tot_Base.length rows in
  let nc =
    match rows with
    | [] -> Prims.int_zero
    | h::uu___ -> FStar_List_Tot_Base.length h in
  if rect nc rows
  then FStar_Pervasives_Native.Some (AMat (nr, nc, rows))
  else FStar_Pervasives_Native.None
let mk_matrix_res (rows : Math_Expr.mvalue Prims.list Prims.list) : mres=
  match mk_amatrix rows with
  | FStar_Pervasives_Native.Some am -> R_Matrix am
  | FStar_Pervasives_Native.None -> R_Undef "non-rectangular-matrix"
let mk_vector_res (v : Math_Expr.mvalue Prims.list) : mres=
  R_Vector ((FStar_List_Tot_Base.length v), v)
let dyn_add (x : mres) (y : mres) : mres=
  match (x, y) with
  | (R_Undef s, uu___) -> R_Undef s
  | (uu___, R_Undef s) -> R_Undef s
  | (R_Scalar a, R_Scalar b) -> R_Scalar (Math_Expr.m_add a b)
  | (R_Matrix (AMat (r1, c1, a)), R_Matrix (AMat (r2, c2, b))) ->
      if (r1 = r2) && (c1 = c2)
      then R_Matrix (AMat (r1, c1, (mat_add r1 c1 a b)))
      else R_Undef "matrix-add-shape-mismatch"
  | (uu___, uu___1) -> R_Undef "add-type-mismatch"
let dyn_sub (x : mres) (y : mres) : mres=
  match (x, y) with
  | (R_Undef s, uu___) -> R_Undef s
  | (uu___, R_Undef s) -> R_Undef s
  | (R_Scalar a, R_Scalar b) -> R_Scalar (Math_Expr.m_sub a b)
  | (R_Matrix (AMat (r1, c1, a)), R_Matrix (AMat (r2, c2, b))) ->
      if (r1 = r2) && (c1 = c2)
      then R_Matrix (AMat (r1, c1, (mat_sub r1 c1 a b)))
      else R_Undef "matrix-sub-shape-mismatch"
  | (uu___, uu___1) -> R_Undef "sub-type-mismatch"
let dyn_times (x : mres) (y : mres) : mres=
  match (x, y) with
  | (R_Undef s, uu___) -> R_Undef s
  | (uu___, R_Undef s) -> R_Undef s
  | (R_Scalar a, R_Scalar b) -> R_Scalar (Math_Expr.m_mul a b)
  | (R_Scalar s, R_Matrix (AMat (r, c, m))) ->
      R_Matrix (AMat (r, c, (scalar_mul_m s r c m)))
  | (R_Matrix (AMat (r, c, m)), R_Scalar s) ->
      R_Matrix (AMat (r, c, (scalar_mul_m s r c m)))
  | (R_Matrix (AMat (r1, c1, a)), R_Matrix (AMat (r2, c2, b))) ->
      if c1 = r2
      then R_Matrix (AMat (r1, c2, (mat_mul r1 c1 r2 c2 a b)))
      else R_Undef "matrix-multiply-inner-dimension-mismatch"
  | (uu___, uu___1) -> R_Undef "times-type-mismatch"
let dyn_transpose (x : mres) : mres=
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat (r, c, m)) -> R_Matrix (AMat (c, r, (transpose_m r c m)))
  | uu___ -> R_Undef "transpose-requires-matrix"
let dyn_determinant (x : mres) : mres=
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat (r, c, m)) ->
      if r = c
      then R_Scalar (determinant r m)
      else R_Undef "determinant-requires-square-matrix"
  | uu___ -> R_Undef "determinant-requires-matrix"
let dyn_trace (x : mres) : mres=
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat (r, c, m)) ->
      if r = c
      then R_Scalar (trace_m r m)
      else R_Undef "trace-requires-square-matrix"
  | uu___ -> R_Undef "trace-requires-matrix"
let dyn_scalarproduct (x : mres) (y : mres) : mres=
  match (x, y) with
  | (R_Undef s, uu___) -> R_Undef s
  | (uu___, R_Undef s) -> R_Undef s
  | (R_Vector (n1, u), R_Vector (n2, v)) ->
      if n1 = n2
      then R_Scalar (vec_dot u v)
      else R_Undef "scalarproduct-length-mismatch"
  | (uu___, uu___1) -> R_Undef "scalarproduct-requires-vectors"
let dyn_vectorproduct (x : mres) (y : mres) : mres=
  match (x, y) with
  | (R_Undef s, uu___) -> R_Undef s
  | (uu___, R_Undef s) -> R_Undef s
  | (R_Vector (n1, u), R_Vector (n2, v)) ->
      if (n1 = (Prims.of_int (3))) && (n2 = (Prims.of_int (3)))
      then R_Vector ((Prims.of_int (3)), (cross3 u v))
      else R_Undef "vectorproduct-requires-3-vectors"
  | (uu___, uu___1) -> R_Undef "vectorproduct-requires-vectors"
let dyn_outerproduct (x : mres) (y : mres) : mres=
  match (x, y) with
  | (R_Undef s, uu___) -> R_Undef s
  | (uu___, R_Undef s) -> R_Undef s
  | (R_Vector (n1, u), R_Vector (n2, v)) ->
      R_Matrix (AMat (n1, n2, (outer_build u v n2)))
  | (uu___, uu___1) -> R_Undef "outerproduct-requires-vectors"
let dyn_selector_matrix (x : mres) (i1 : Prims.int) (j1 : Prims.int) : 
  mres=
  match x with
  | R_Undef s -> R_Undef s
  | R_Matrix (AMat (r, c, m)) ->
      if
        (((i1 >= Prims.int_one) && (j1 >= Prims.int_one)) && (i1 <= r)) &&
          (j1 <= c)
      then
        let i = i1 - Prims.int_one in
        let j = j1 - Prims.int_one in R_Scalar (mat_elem c m i j)
      else R_Undef "selector-index-out-of-range"
  | R_Vector (n, v) ->
      if (i1 >= Prims.int_one) && (i1 <= n)
      then
        let i = i1 - Prims.int_one in
        R_Scalar (FStar_List_Tot_Base.index v i)
      else R_Undef "selector-index-out-of-range"
  | uu___ -> R_Undef "selector-requires-matrix-or-vector"
let row_to_string (v : Math_Expr.mvalue Prims.list) : Prims.string=
  FStar_String.concat ""
    ["[";
    FStar_String.concat ","
      (FStar_List_Tot_Base.map Math_Expr.value_to_string v);
    "]"]
let mres_to_string (x : mres) : Prims.string=
  match x with
  | R_Scalar v -> Math_Expr.value_to_string v
  | R_Vector (uu___, v) -> row_to_string v
  | R_Matrix (AMat (uu___, uu___1, rows)) ->
      FStar_String.concat ""
        ["[";
        FStar_String.concat "," (FStar_List_Tot_Base.map row_to_string rows);
        "]"]
  | R_Undef uu___ -> "undef"
let mres_reason (x : mres) : Prims.string=
  match x with
  | R_Undef r -> r
  | R_Scalar v -> Math_Expr.value_reason v
  | uu___ -> ""
