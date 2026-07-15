open Prims
type regex =
  | R_Empty 
  | R_Eps 
  | R_Ranges of (Prims.nat * Prims.nat) Prims.list 
  | R_Cat of regex * regex 
  | R_Alt of regex * regex 
  | R_Star of regex 
  | R_And of regex * regex 
  | R_Not of regex 
let uu___is_R_Empty (projectee : regex) : Prims.bool=
  match projectee with | R_Empty -> true | uu___ -> false
let uu___is_R_Eps (projectee : regex) : Prims.bool=
  match projectee with | R_Eps -> true | uu___ -> false
let uu___is_R_Ranges (projectee : regex) : Prims.bool=
  match projectee with | R_Ranges _0 -> true | uu___ -> false
let __proj__R_Ranges__item___0 (projectee : regex) :
  (Prims.nat * Prims.nat) Prims.list=
  match projectee with | R_Ranges _0 -> _0
let uu___is_R_Cat (projectee : regex) : Prims.bool=
  match projectee with | R_Cat (_0, _1) -> true | uu___ -> false
let __proj__R_Cat__item___0 (projectee : regex) : regex=
  match projectee with | R_Cat (_0, _1) -> _0
let __proj__R_Cat__item___1 (projectee : regex) : regex=
  match projectee with | R_Cat (_0, _1) -> _1
let uu___is_R_Alt (projectee : regex) : Prims.bool=
  match projectee with | R_Alt (_0, _1) -> true | uu___ -> false
let __proj__R_Alt__item___0 (projectee : regex) : regex=
  match projectee with | R_Alt (_0, _1) -> _0
let __proj__R_Alt__item___1 (projectee : regex) : regex=
  match projectee with | R_Alt (_0, _1) -> _1
let uu___is_R_Star (projectee : regex) : Prims.bool=
  match projectee with | R_Star _0 -> true | uu___ -> false
let __proj__R_Star__item___0 (projectee : regex) : regex=
  match projectee with | R_Star _0 -> _0
let uu___is_R_And (projectee : regex) : Prims.bool=
  match projectee with | R_And (_0, _1) -> true | uu___ -> false
let __proj__R_And__item___0 (projectee : regex) : regex=
  match projectee with | R_And (_0, _1) -> _0
let __proj__R_And__item___1 (projectee : regex) : regex=
  match projectee with | R_And (_0, _1) -> _1
let uu___is_R_Not (projectee : regex) : Prims.bool=
  match projectee with | R_Not _0 -> true | uu___ -> false
let __proj__R_Not__item___0 (projectee : regex) : regex=
  match projectee with | R_Not _0 -> _0
let max_codepoint : Prims.nat= (Prims.parse_int "0x10FFFF")
let rec size (r : regex) : Prims.nat=
  match r with
  | R_Empty -> Prims.int_one
  | R_Eps -> Prims.int_one
  | R_Ranges uu___ -> Prims.int_one
  | R_Cat (a, b) -> ((Prims.of_int (3)) + (size a)) + (size b)
  | R_Alt (a, b) -> (Prims.int_one + (size a)) + (size b)
  | R_And (a, b) -> (Prims.int_one + (size a)) + (size b)
  | R_Not a -> Prims.int_one + (size a)
  | R_Star a -> (Prims.of_int (3)) + (size a)
let rec in_ranges (c : Prims.nat) (rs : (Prims.nat * Prims.nat) Prims.list) :
  Prims.bool=
  match rs with
  | [] -> false
  | (lo, hi)::tl -> ((lo <= c) && (c <= hi)) || (in_ranges c tl)
let rec complement_from (lo : Prims.nat)
  (rs : (Prims.nat * Prims.nat) Prims.list) :
  (Prims.nat * Prims.nat) Prims.list=
  match rs with
  | [] -> if lo <= max_codepoint then [(lo, max_codepoint)] else []
  | (a, b)::tl ->
      let head =
        if (a >= Prims.int_one) && (lo <= (a - Prims.int_one))
        then [(lo, (a - Prims.int_one))]
        else [] in
      let next = if (b + Prims.int_one) > lo then b + Prims.int_one else lo in
      FStar_List_Tot_Base.append head (complement_from next tl)
let complement_ranges (rs : (Prims.nat * Prims.nat) Prims.list) :
  (Prims.nat * Prims.nat) Prims.list= complement_from Prims.int_zero rs
let rec take_n (k : Prims.nat) (w : Prims.nat Prims.list) :
  Prims.nat Prims.list=
  if k = Prims.int_zero
  then []
  else
    (match w with | [] -> [] | x::xs -> x :: (take_n (k - Prims.int_one) xs))
let rec drop_n (k : Prims.nat) (w : Prims.nat Prims.list) :
  Prims.nat Prims.list=
  if k = Prims.int_zero
  then w
  else
    (match w with | [] -> [] | uu___1::xs -> drop_n (k - Prims.int_one) xs)
let rec mem (r : regex) (w : Prims.nat Prims.list) : Prims.bool=
  match r with
  | R_Empty -> false
  | R_Eps -> Prims.uu___is_Nil w
  | R_Ranges rs -> (match w with | c::[] -> in_ranges c rs | uu___ -> false)
  | R_Alt (a, b) -> (mem a w) || (mem b w)
  | R_And (a, b) -> (mem a w) && (mem b w)
  | R_Not a -> Prims.op_Negation (mem a w)
  | R_Cat (a, b) -> cat_try a b w (FStar_List_Tot_Base.length w)
  | R_Star a ->
      (match w with
       | [] -> true
       | uu___::uu___1 -> star_try a w (FStar_List_Tot_Base.length w))
and cat_try (a : regex) (b : regex) (w : Prims.nat Prims.list)
  (k : Prims.nat) : Prims.bool=
  ((mem a (take_n k w)) && (mem b (drop_n k w))) ||
    (if k = Prims.int_zero then false else cat_try a b w (k - Prims.int_one))
and star_try (a : regex) (w : Prims.nat Prims.list) (k : Prims.nat) :
  Prims.bool=
  if k = Prims.int_zero
  then false
  else
    ((mem a (take_n k w)) && (mem (R_Star a) (drop_n k w))) ||
      (star_try a w (k - Prims.int_one))
let rec nullable (r : regex) : Prims.bool=
  match r with
  | R_Empty -> false
  | R_Eps -> true
  | R_Ranges uu___ -> false
  | R_Cat (a, b) -> (nullable a) && (nullable b)
  | R_Alt (a, b) -> (nullable a) || (nullable b)
  | R_And (a, b) -> (nullable a) && (nullable b)
  | R_Not a -> Prims.op_Negation (nullable a)
  | R_Star uu___ -> true
let r_universal : regex= R_Not R_Empty
let rec ranges_cmp (x : (Prims.nat * Prims.nat) Prims.list)
  (y : (Prims.nat * Prims.nat) Prims.list) : Prims.int=
  match (x, y) with
  | ([], []) -> Prims.int_zero
  | ([], uu___::uu___1) -> (Prims.of_int (-1))
  | (uu___::uu___1, []) -> Prims.int_one
  | ((a1, b1)::xs, (a2, b2)::ys) ->
      if a1 <> a2
      then (if a1 < a2 then (Prims.of_int (-1)) else Prims.int_one)
      else
        if b1 <> b2
        then (if b1 < b2 then (Prims.of_int (-1)) else Prims.int_one)
        else ranges_cmp xs ys
let rec regex_cmp (a : regex) (b : regex) : Prims.int=
  let tag r =
    match r with
    | R_Empty -> Prims.int_zero
    | R_Eps -> Prims.int_one
    | R_Ranges uu___ -> (Prims.of_int (2))
    | R_Cat (uu___, uu___1) -> (Prims.of_int (3))
    | R_Alt (uu___, uu___1) -> (Prims.of_int (4))
    | R_Star uu___ -> (Prims.of_int (5))
    | R_And (uu___, uu___1) -> (Prims.of_int (6))
    | R_Not uu___ -> (Prims.of_int (7)) in
  let ta = tag a in
  let tb = tag b in
  if ta <> tb
  then (if ta < tb then (Prims.of_int (-1)) else Prims.int_one)
  else
    (match (a, b) with
     | (R_Ranges x, R_Ranges y) -> ranges_cmp x y
     | (R_Cat (a1, a2), R_Cat (b1, b2)) ->
         let c = regex_cmp a1 b1 in
         if c <> Prims.int_zero then c else regex_cmp a2 b2
     | (R_Alt (a1, a2), R_Alt (b1, b2)) ->
         let c = regex_cmp a1 b1 in
         if c <> Prims.int_zero then c else regex_cmp a2 b2
     | (R_And (a1, a2), R_And (b1, b2)) ->
         let c = regex_cmp a1 b1 in
         if c <> Prims.int_zero then c else regex_cmp a2 b2
     | (R_Star a1, R_Star b1) -> regex_cmp a1 b1
     | (R_Not a1, R_Not b1) -> regex_cmp a1 b1
     | (uu___1, uu___2) -> Prims.int_zero)
let regex_le (a : regex) (b : regex) : Prims.bool=
  (regex_cmp a b) <= Prims.int_zero
let smart_alt (a : regex) (b : regex) : regex=
  if uu___is_R_Empty a
  then b
  else
    if uu___is_R_Empty b
    then a
    else
      if a = b
      then a
      else
        if (a = r_universal) || (b = r_universal)
        then r_universal
        else if regex_le a b then R_Alt (a, b) else R_Alt (b, a)
let smart_and (a : regex) (b : regex) : regex=
  if (uu___is_R_Empty a) || (uu___is_R_Empty b)
  then R_Empty
  else
    if a = r_universal
    then b
    else
      if b = r_universal
      then a
      else
        if a = b
        then a
        else if regex_le a b then R_And (a, b) else R_And (b, a)
let smart_not (a : regex) : regex=
  match a with | R_Not x -> x | uu___ -> R_Not a
let smart_cat (a : regex) (b : regex) : regex=
  if (uu___is_R_Empty a) || (uu___is_R_Empty b)
  then R_Empty
  else
    if uu___is_R_Eps a
    then b
    else if uu___is_R_Eps b then a else R_Cat (a, b)
let smart_star (a : regex) : regex=
  match a with
  | R_Empty -> R_Eps
  | R_Eps -> R_Eps
  | R_Star uu___ -> a
  | uu___ -> R_Star a
