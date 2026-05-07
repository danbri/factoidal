module RDF.List.Helpers

// Tail-recursive replacements for the non-tail-recursive list ops in
// FStar.List.Tot.Base that appear in the SPARQL/RIF eval hot path.
//
// Why this module exists:
//   FStar.List.Tot.append, concatMap, and snoc-style usages are
//   straightforward structural recursions that overflow the OCaml
//   stack on long lists. Past stack-overflow incidents on the Turtle
//   parser path (issue #94) and the BGP filter_map path (sin7,
//   2026-04-26) used the same fix: a `*_acc` accumulator version that
//   compiles to a real tail call.
//
// What we provide:
//   - append_tr : tail-rec append, equal to List.Tot.append.
//   - concatMap_tr : tail-rec concatMap, equal to List.Tot.concatMap.
//   - assoc_tr : a re-statement of List.Tot.assoc kept here for
//                naming-symmetry with the other helpers; the stdlib
//                version is already tail-position recursive but
//                consumers grep-find it more readily under a project
//                module.
//
// Equivalence is proved against the stdlib functions so any caller
// can switch to the tr variant without changing the externally
// observable semantics. Verified under F* with no --lax,
// no --admit_smt_queries, no assume val (rules #10, #3).

open FStar.List.Tot

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"

// -------------------------------------------------------------------
// 1. append_tr
//
// Walk xs with an explicit reverse-accumulator, then splice ys at
// the end via rev_acc. The library rev_acc is itself tail-rec.
// -------------------------------------------------------------------

let rec append_aux (#a:Type) (acc:list a) (xs:list a) (ys:list a)
  : Tot (list a) (decreases xs) =
  match xs with
  | []        -> rev_acc acc ys
  | x :: rest -> append_aux (x :: acc) rest ys

let append_tr (#a:Type) (xs ys : list a) : Tot (list a) =
  append_aux [] xs ys

// Equivalence lemma: append_aux acc xs ys == rev acc @ xs @ ys.
//
// We prove a slightly stronger invariant on the accumulator so the
// induction step lines up with the recursive call. Once we have it,
// instantiating acc = [] gives the desired statement for append_tr.
let rec lemma_append_aux_eq (#a:Type) (acc xs ys : list a)
  : Lemma (ensures append_aux acc xs ys == append (rev acc) (append xs ys))
          (decreases xs)
  =
  match xs with
  | [] ->
    // Goal: rev_acc acc ys == rev acc @ ([] @ ys)
    //                     == rev acc @ ys
    rev_acc_rev' acc ys;
    // rev_acc acc ys == rev' acc @ ys
    rev_rev' acc
    // rev acc == rev' acc
  | x :: rest ->
    // LHS: append_aux (x :: acc) rest ys
    // IH:  append_aux (x :: acc) rest ys
    //      == rev (x :: acc) @ (rest @ ys)
    //      == (rev acc @ [x]) @ (rest @ ys)
    lemma_append_aux_eq (x :: acc) rest ys;
    // Goal: append_aux acc (x :: rest) ys == rev acc @ ((x :: rest) @ ys)
    //                                     == rev acc @ (x :: (rest @ ys))
    //                                     == (rev acc @ [x]) @ (rest @ ys)
    // — the last step is append_assoc.
    rev_rev' (x :: acc);
    rev_rev' acc;
    append_assoc (rev acc) [x] (append rest ys);
    append_l_cons x (append rest ys) (rev acc)

let lemma_append_tr_eq (#a:Type) (xs ys : list a)
  : Lemma (append_tr xs ys == append xs ys)
  =
  lemma_append_aux_eq [] xs ys
  // append_aux [] xs ys == rev [] @ (xs @ ys) == [] @ (xs @ ys) == xs @ ys

#pop-options

// -------------------------------------------------------------------
// 2. concatMap_tr
//
// Tail-rec concatMap. Walk the outer list xs with an accumulator
// holding the reversed concatenation so far. At each step we reverse
// (f x) onto the accumulator. At the end we reverse the accumulator.
//
// Invariant: concatMap_aux f xs acc
//              == rev acc @ concatMap f xs
//
// Using rev_acc and rev keeps the recursion tail-position.
// -------------------------------------------------------------------

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

let rec concatMap_aux
  (#a #b : Type) (f : a -> list b) (xs : list a) (acc : list b)
  : Tot (list b) (decreases xs)
  =
  match xs with
  | []        -> rev acc
  | x :: rest -> concatMap_aux f rest (rev_acc (f x) acc)

let concatMap_tr (#a #b : Type) (f : a -> list b) (xs : list a)
  : Tot (list b)
  = concatMap_aux f xs []

// Lemma: rev (rev (f x) @ acc) == rev acc @ f x.
// Used to discharge the inductive step on concatMap_aux below.
let lemma_rev_rev_app
  (#b : Type) (zs ws : list b)
  : Lemma (rev (append (rev zs) ws) == append (rev ws) zs)
  =
  rev_append (rev zs) ws;
  // rev ((rev zs) @ ws) == rev ws @ rev (rev zs)
  rev_involutive zs

// Inductive equivalence with the explicit accumulator carried.
let rec lemma_concatMap_aux_eq
  (#a #b : Type) (f : a -> list b) (xs : list a) (acc : list b)
  : Lemma (ensures concatMap_aux f xs acc
                   == append (rev acc) (concatMap f xs))
          (decreases xs)
  =
  match xs with
  | [] ->
    // concatMap_aux f [] acc == rev acc
    // concatMap f [] == [], so rev acc @ [] == rev acc
    append_l_nil (rev acc)
  | x :: rest ->
    // concatMap_aux f (x :: rest) acc
    //   == concatMap_aux f rest (rev_acc (f x) acc)         by definition
    //   == rev (rev_acc (f x) acc) @ concatMap f rest       by IH
    //   == rev (rev (f x) @ acc) @ concatMap f rest         by rev_acc_rev'
    //   == (rev acc @ f x) @ concatMap f rest               by lemma_rev_rev_app
    //   == rev acc @ (f x @ concatMap f rest)               by append_assoc
    //   == rev acc @ concatMap f (x :: rest)                by definition
    let acc' = rev_acc (f x) acc in
    lemma_concatMap_aux_eq f rest acc';
    rev_acc_rev' (f x) acc;
    // acc' == rev' (f x) @ acc
    rev_rev' (f x);
    // rev (f x) == rev' (f x), so acc' == rev (f x) @ acc
    lemma_rev_rev_app (f x) acc;
    // rev acc' == rev acc @ f x
    append_assoc (rev acc) (f x) (concatMap f rest)

let lemma_concatMap_tr_eq
  (#a #b : Type) (f : a -> list b) (xs : list a)
  : Lemma (concatMap_tr f xs == concatMap f xs)
  =
  lemma_concatMap_aux_eq f xs [];
  // concatMap_aux f xs [] == rev [] @ concatMap f xs == [] @ concatMap f xs
  append_l_nil (concatMap f xs)

#pop-options

// -------------------------------------------------------------------
// 3. assoc_tr
//
// FStar.List.Tot.assoc is already tail-position recursive — the
// last call in the else-branch is the recursive call, with no
// pending wrapper. We re-state it here so call-sites in the
// SPARQL/RIF path use a uniform `*_tr` naming and so future audits
// can grep one module for "is this the tail-rec form?".
// -------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 2 --ifuel 2"

let rec assoc_tr
  (#a:eqtype) (#b:Type) (x : a) (xs : list (a * b))
  : Tot (option b) (decreases xs)
  =
  match xs with
  | []            -> None
  | (k, v) :: rest -> if x = k then Some v else assoc_tr x rest

let rec lemma_assoc_tr_eq
  (#a:eqtype) (#b:Type) (x : a) (xs : list (a * b))
  : Lemma (ensures assoc_tr x xs == assoc x xs)
          (decreases xs)
  =
  match xs with
  | []            -> ()
  | (k, _) :: rest ->
    if x = k then () else lemma_assoc_tr_eq x rest

#pop-options
