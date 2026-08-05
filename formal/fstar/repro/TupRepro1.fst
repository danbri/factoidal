module TupRepro1

// Control: SINGLE-binder outer lambda, inner fold_left captures the
// single bound variable. Expected: PASS.

open FStar.List.Tot

#push-options "--z3rlimit 1500 --fuel 4 --ifuel 4"

let inv (l : list int) : prop = forall (z:int). List.Tot.memP z l ==> z >= 0

let rec fold_left_inv (#a #b : Type) (inv : a -> prop) (f : a -> b -> a) (l : list b) (acc : a)
  : Lemma (requires inv acc /\ (forall (x : a) (y : b). (List.Tot.memP y l /\ inv x) ==> inv (f x y)))
    (ensures inv (List.Tot.fold_left f acc l)) (decreases l) =
  match l with [] -> () | hd :: tl -> fold_left_inv inv f tl (f acc hd)

let items : list nat = [0; 1; 2]

val outer_sound (seed : list int) : Lemma
  (requires inv seed)
  (ensures inv (List.Tot.fold_left
                  (fun (acc : list int) (n : nat) ->
                     List.Tot.fold_left (fun a z -> (n + z) :: a) acc [1; 2])
                  seed items))

let outer_sound seed =
  let outer_step : list int -> nat -> list int =
    fun (acc : list int) (n : nat) ->
      List.Tot.fold_left (fun a z -> (n + z) :: a) acc [1; 2] in
  introduce forall (acc : list int) (n : nat).
      (List.Tot.memP n items /\ inv acc) ==> inv (outer_step acc n)
  with introduce (List.Tot.memP n items /\ inv acc) ==> inv (outer_step acc n)
  with _ . begin
    fold_left_inv inv (fun a z -> (n + z) :: a) [1; 2] acc
  end;
  fold_left_inv inv outer_step items seed

#pop-options
