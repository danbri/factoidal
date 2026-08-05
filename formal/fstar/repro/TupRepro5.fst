module TupRepro5

// Tuple binder, inner captures x, but outer DELEGATES to a helper
// lambda over the two components (candidate FIX pattern).

open FStar.List.Tot

#push-options "--z3rlimit 1500 --fuel 4 --ifuel 4"

let inv (l : list int) : prop = forall (z:int). List.Tot.memP z l ==> z >= 0

let rec fold_left_inv (#a #b : Type) (inv : a -> prop) (f : a -> b -> a) (l : list b) (acc : a)
  : Lemma (requires inv acc /\ (forall (x : a) (y : b). (List.Tot.memP y l /\ inv x) ==> inv (f x y)))
    (ensures inv (List.Tot.fold_left f acc l)) (decreases l) =
  match l with [] -> () | hd :: tl -> fold_left_inv inv f tl (f acc hd)

let items : list (nat * nat) = [(0,0); (1,1); (2,2)]

let outer_helper : list int -> nat -> nat -> list int =
  fun (acc2 : list int) (x : nat) (y : nat) ->
    List.Tot.fold_left (fun a z -> (x + z) :: a) acc2 [1; 2]

val outer_sound (seed : list int) : Lemma
  (requires inv seed)
  (ensures inv (List.Tot.fold_left
                  (fun (acc : list int) (xy : nat * nat) ->
                     outer_helper acc (fst xy) (snd xy))
                  seed items))

let outer_sound seed =
  let outer_step : list int -> (nat * nat) -> list int =
    fun (acc : list int) (xy : nat * nat) ->
      outer_helper acc (fst xy) (snd xy) in
  introduce forall (acc : list int) (xy : nat * nat).
      (List.Tot.memP xy items /\ inv acc) ==> inv (outer_step acc xy)
  with introduce (List.Tot.memP xy items /\ inv acc) ==> inv (outer_step acc xy)
  with _ . begin
    fold_left_inv inv (fun a z -> (fst xy + z) :: a) [1; 2] acc
  end;
  fold_left_inv inv outer_step items seed

#pop-options
