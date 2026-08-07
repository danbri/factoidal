module TupRepro7

// Extra variant: tuple binder whose COMPONENTS are a multi-constructor
// sum type, matched with a PARTIAL/asymmetric pattern (one arm runs
// the inner fold, the other arm is a trivial `acc`-preserving wildcard)
// — closer to the real "match decl.s with | S_IRI p -> ..." shape but
// lifted to a pair of sum-typed scrutinees, `match a, b with | P1, P2 ->`.

open FStar.List.Tot

#push-options "--z3rlimit 1500 --fuel 4 --ifuel 4"

let inv (l : list int) : prop = forall (z:int). List.Tot.memP z l ==> z >= 0

let rec fold_left_inv (#a #b : Type) (inv : a -> prop) (f : a -> b -> a) (l : list b) (acc : a)
  : Lemma (requires inv acc /\ (forall (x : a) (y : b). (List.Tot.memP y l /\ inv x) ==> inv (f x y)))
    (ensures inv (List.Tot.fold_left f acc l)) (decreases l) =
  match l with [] -> () | hd :: tl -> fold_left_inv inv f tl (f acc hd)

type tag =
  | TA of nat
  | TB

let items : list (tag * tag) = [(TA 0, TB); (TA 1, TA 5); (TB, TB)]

val outer_sound (seed : list int) : Lemma
  (requires inv seed)
  (ensures inv (List.Tot.fold_left
                  (fun (acc : list int) (ab : tag * tag) ->
                     match ab with
                     | (TA n, _) -> List.Tot.fold_left (fun a z -> (n + z) :: a) acc [1; 2]
                     | _ -> acc)
                  seed items))

let outer_sound seed =
  let outer_step : list int -> (tag * tag) -> list int =
    fun (acc : list int) (ab : tag * tag) ->
      match ab with
      | (TA n, _) -> List.Tot.fold_left (fun a z -> (n + z) :: a) acc [1; 2]
      | _ -> acc in
  introduce forall (acc : list int) (ab : tag * tag).
      (List.Tot.memP ab items /\ inv acc) ==> inv (outer_step acc ab)
  with introduce (List.Tot.memP ab items /\ inv acc) ==> inv (outer_step acc ab)
  with _ . begin
    match ab with
    | (TA n, _) -> fold_left_inv inv (fun a z -> (n + z) :: a) [1; 2] acc
    | _ -> ()
  end;
  fold_left_inv inv outer_step items seed

#pop-options
