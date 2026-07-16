open Prims
let rec insert_regex (x : Regex_Syntax.regex)
  (xs : Regex_Syntax.regex Prims.list) : Regex_Syntax.regex Prims.list=
  match xs with
  | [] -> [x]
  | y::ys ->
      let c = Regex_Syntax.regex_cmp x y in
      if c = Prims.int_zero
      then xs
      else if c < Prims.int_zero then x :: xs else y :: (insert_regex x ys)
let rec alt_flatten (r : Regex_Syntax.regex)
  (acc : Regex_Syntax.regex Prims.list) : Regex_Syntax.regex Prims.list=
  match r with
  | Regex_Syntax.R_Empty -> acc
  | Regex_Syntax.R_Alt (a, b) -> alt_flatten a (alt_flatten b acc)
  | uu___ -> insert_regex r acc
let rec and_flatten (r : Regex_Syntax.regex)
  (acc : Regex_Syntax.regex Prims.list) : Regex_Syntax.regex Prims.list=
  match r with
  | Regex_Syntax.R_And (a, b) -> and_flatten a (and_flatten b acc)
  | uu___ -> if r = Regex_Syntax.r_universal then acc else insert_regex r acc
let rec has_universal (xs : Regex_Syntax.regex Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | y::ys -> (y = Regex_Syntax.r_universal) || (has_universal ys)
let rec has_empty (xs : Regex_Syntax.regex Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | y::ys -> (Regex_Syntax.uu___is_R_Empty y) || (has_empty ys)
let rec rebuild_alt (xs : Regex_Syntax.regex Prims.list) :
  Regex_Syntax.regex=
  match xs with
  | [] -> Regex_Syntax.R_Empty
  | x::[] -> x
  | x::rest -> Regex_Syntax.R_Alt (x, (rebuild_alt rest))
let rec rebuild_and (xs : Regex_Syntax.regex Prims.list) :
  Regex_Syntax.regex=
  match xs with
  | [] -> Regex_Syntax.r_universal
  | x::[] -> x
  | x::rest -> Regex_Syntax.R_And (x, (rebuild_and rest))
let ealt (a : Regex_Syntax.regex) (b : Regex_Syntax.regex) :
  Regex_Syntax.regex=
  let leaves = alt_flatten a (alt_flatten b []) in
  if has_universal leaves
  then Regex_Syntax.r_universal
  else rebuild_alt leaves
let eand (a : Regex_Syntax.regex) (b : Regex_Syntax.regex) :
  Regex_Syntax.regex=
  let leaves = and_flatten a (and_flatten b []) in
  if has_empty leaves then Regex_Syntax.R_Empty else rebuild_and leaves
let rec nderiv (c : Prims.nat) (r : Regex_Syntax.regex) : Regex_Syntax.regex=
  match r with
  | Regex_Syntax.R_Empty -> Regex_Syntax.R_Empty
  | Regex_Syntax.R_Eps -> Regex_Syntax.R_Empty
  | Regex_Syntax.R_Ranges rs ->
      if Regex_Syntax.in_ranges c rs
      then Regex_Syntax.R_Eps
      else Regex_Syntax.R_Empty
  | Regex_Syntax.R_Alt (a, b) -> ealt (nderiv c a) (nderiv c b)
  | Regex_Syntax.R_And (a, b) -> eand (nderiv c a) (nderiv c b)
  | Regex_Syntax.R_Not a -> Regex_Syntax.smart_not (nderiv c a)
  | Regex_Syntax.R_Cat (a, b) ->
      let left = Regex_Syntax.smart_cat (nderiv c a) b in
      if Regex_Syntax.nullable a then ealt left (nderiv c b) else left
  | Regex_Syntax.R_Star a ->
      Regex_Syntax.smart_cat (nderiv c a) (Regex_Syntax.R_Star a)
let rec run_word (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) :
  Regex_Syntax.regex=
  match w with
  | [] -> r
  | c::rest -> run_word (Regex_Derivative.deriv c r) rest
let matches (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) : Prims.bool=
  Regex_Syntax.nullable (run_word r w)
let rec run_word_norm (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) :
  Regex_Syntax.regex=
  match w with | [] -> r | c::rest -> run_word_norm (nderiv c r) rest
let matches_norm (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) :
  Prims.bool= Regex_Syntax.nullable (run_word_norm r w)
let any_char : Regex_Syntax.regex=
  Regex_Syntax.R_Ranges [(Prims.int_zero, Regex_Syntax.max_codepoint)]
let dot_star : Regex_Syntax.regex= Regex_Syntax.R_Star any_char
let contains (r : Regex_Syntax.regex) : Regex_Syntax.regex=
  Regex_Syntax.R_Cat (dot_star, (Regex_Syntax.R_Cat (r, dot_star)))
let search (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) : Prims.bool=
  matches_norm (contains r) w
let anchored_prefix (r : Regex_Syntax.regex) : Regex_Syntax.regex=
  Regex_Syntax.R_Cat (r, dot_star)
let rec find_from (r : Regex_Syntax.regex) (w : Prims.nat Prims.list)
  (idx : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if matches_norm (anchored_prefix r) w
  then FStar_Pervasives_Native.Some idx
  else
    (match w with
     | [] -> FStar_Pervasives_Native.None
     | uu___1::rest -> find_from r rest (idx + Prims.int_one))
let find_match (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) :
  Prims.nat FStar_Pervasives_Native.option= find_from r w Prims.int_zero
let rec insert_sorted (x : Prims.nat) (xs : Prims.nat Prims.list) :
  Prims.nat Prims.list=
  match xs with
  | [] -> [x]
  | y::ys ->
      if x = y
      then xs
      else if x < y then x :: xs else y :: (insert_sorted x ys)
let rec collect_bounds (r : Regex_Syntax.regex) (acc : Prims.nat Prims.list)
  : Prims.nat Prims.list=
  match r with
  | Regex_Syntax.R_Empty -> acc
  | Regex_Syntax.R_Eps -> acc
  | Regex_Syntax.R_Ranges rs -> collect_range_bounds rs acc
  | Regex_Syntax.R_Cat (a, b) -> collect_bounds b (collect_bounds a acc)
  | Regex_Syntax.R_Alt (a, b) -> collect_bounds b (collect_bounds a acc)
  | Regex_Syntax.R_And (a, b) -> collect_bounds b (collect_bounds a acc)
  | Regex_Syntax.R_Not a -> collect_bounds a acc
  | Regex_Syntax.R_Star a -> collect_bounds a acc
and collect_range_bounds (rs : (Prims.nat * Prims.nat) Prims.list)
  (acc : Prims.nat Prims.list) : Prims.nat Prims.list=
  match rs with
  | [] -> acc
  | (lo, hi)::tl ->
      let acc1 = insert_sorted lo acc in
      let acc2 =
        if (hi + Prims.int_one) <= Regex_Syntax.max_codepoint
        then insert_sorted (hi + Prims.int_one) acc1
        else acc1 in
      collect_range_bounds tl acc2
let class_reps (r : Regex_Syntax.regex) : Prims.nat Prims.list=
  insert_sorted Prims.int_zero
    (insert_sorted Regex_Syntax.max_codepoint (collect_bounds r []))
let rec mem_state (r : Regex_Syntax.regex)
  (xs : Regex_Syntax.regex Prims.list) : Prims.bool=
  match xs with | [] -> false | y::ys -> (r = y) || (mem_state r ys)
let rec succ_states (r : Regex_Syntax.regex) (reps : Prims.nat Prims.list) :
  Regex_Syntax.regex Prims.list=
  match reps with | [] -> [] | c::cs -> (nderiv c r) :: (succ_states r cs)
let rec add_new (news : Regex_Syntax.regex Prims.list)
  (visited : Regex_Syntax.regex Prims.list)
  (worklist : Regex_Syntax.regex Prims.list) :
  (Regex_Syntax.regex Prims.list * Regex_Syntax.regex Prims.list)=
  match news with
  | [] -> (visited, worklist)
  | s::rest ->
      if mem_state s visited
      then add_new rest visited worklist
      else add_new rest (s :: visited) (s :: worklist)
let rec bfs_empty (worklist : Regex_Syntax.regex Prims.list)
  (visited : Regex_Syntax.regex Prims.list) (reps : Prims.nat Prims.list)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (match worklist with
     | [] -> true
     | s::rest ->
         if Regex_Syntax.nullable s
         then false
         else
           (let succs = succ_states s reps in
            let uu___2 = add_new succs visited rest in
            match uu___2 with
            | (visited', worklist') ->
                bfs_empty worklist' visited' reps (fuel - Prims.int_one)))
let is_empty (r : Regex_Syntax.regex) : Prims.bool=
  let reps = class_reps r in
  let fuel = (Prims.of_int (1000)) * ((Regex_Syntax.size r) + Prims.int_one) in
  bfs_empty [r] [r] reps fuel
let intersection_empty (p : Regex_Syntax.regex) (q : Regex_Syntax.regex) :
  Prims.bool= is_empty (Regex_Syntax.R_And (p, q))
let subsumes (p : Regex_Syntax.regex) (q : Regex_Syntax.regex) : Prims.bool=
  is_empty (Regex_Syntax.R_And (q, (Regex_Syntax.R_Not p)))
let rec mem_alt_list (xs : Regex_Syntax.regex Prims.list)
  (w : Prims.nat Prims.list) : Prims.bool=
  match xs with
  | [] -> false
  | x::rest -> (Regex_Syntax.mem x w) || (mem_alt_list rest w)
let rec mem_and_list (xs : Regex_Syntax.regex Prims.list)
  (w : Prims.nat Prims.list) : Prims.bool=
  match xs with
  | [] -> true
  | x::rest -> (Regex_Syntax.mem x w) && (mem_and_list rest w)
