module TupRepro8

// Extra variant: DEPENDENT pair (Sigma-type, `&`) instead of a plain
// non-dependent product (`*`). Tests whether dependent-pair projection
// (dfst/dsnd, `(| x, y |)` pattern) behaves differently from Mktuple2.

open FStar.List.Tot

#push-options "--z3rlimit 1500 --fuel 4 --ifuel 4"

let inv (l : list int) : prop = forall (z:int). List.Tot.memP z l ==> z >= 0

let rec fold_left_inv (#a #b : Type) (inv : a -> prop) (f : a -> b -> a) (l : list b) (acc : a)
  : Lemma (requires inv acc /\ (forall (x : a) (y : b). (List.Tot.memP y l /\ inv x) ==> inv (f x y)))
    (ensures inv (List.Tot.fold_left f acc l)) (decreases l) =
  match l with [] -> () | hd :: tl -> fold_left_inv inv f tl (f acc hd)

// dependent pair: second component's type mentions the first
let dpair = (x:nat & y:nat{y >= x})

let items : list dpair = [(| 0, 0 |); (| 1, 3 |); (| 2, 2 |)]

val outer_sound (seed : list int) : Lemma
  (requires inv seed)
  (ensures inv (List.Tot.fold_left
                  (fun (acc : list int) (xy : dpair) ->
                     let (| x, y |) = xy in
                     List.Tot.fold_left (fun a z -> (x + z) :: a) acc [1; 2])
                  seed items))

let outer_sound seed =
  let outer_step : list int -> dpair -> list int =
    fun (acc : list int) (xy : dpair) ->
      let (| x, y |) = xy in
      List.Tot.fold_left (fun a z -> (x + z) :: a) acc [1; 2] in
  introduce forall (acc : list int) (xy : dpair).
      (List.Tot.memP xy items /\ inv acc) ==> inv (outer_step acc xy)
  with introduce (List.Tot.memP xy items /\ inv acc) ==> inv (outer_step acc xy)
  with _ . begin
    let (| x, y |) = xy in
    fold_left_inv inv (fun a z -> (x + z) :: a) [1; 2] acc
  end;
  fold_left_inv inv outer_step items seed

#pop-options
