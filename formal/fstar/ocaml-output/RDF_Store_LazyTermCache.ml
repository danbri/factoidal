open Prims
type 'a entries = (Prims.nat * 'a) Prims.list
type 'a lazy_term_cache = {
  mutable populated : bool;
  forward           : (Stdlib.Int.t, 'a) Stdlib.Hashtbl.t;
  reverse           : (string, Stdlib.Int.t) Stdlib.Hashtbl.t;
  populate          : unit -> (Z.t * 'a) Prims.list;
  key_of            : 'a -> Prims.string;
} (* __LAZY_TERM_CACHE_RUNTIME_APPLIED__ *)

(* Run c.populate once; fill both hashtables; mark c.populated.
   Idempotent. NOT mutex-protected — matches the pre-#253 baseline
   thread-safety (Mutex.t not available in this build's Stdlib).
   The reverse hashtable is keyed on the canonical-key string
   produced by c.key_of. *)
let _lazy_term_cache_ensure (c : 'a lazy_term_cache) : unit =
  if not c.populated then begin
    let entries = c.populate () in
    Stdlib.List.iter (fun (id_z, v) ->
      let id = Z.to_int id_z in
      Stdlib.Hashtbl.replace c.forward id v;
      Stdlib.Hashtbl.replace c.reverse (c.key_of v) id
    ) entries;
    c.populated <- true
  end
let mk_lazy_term_cache (populate : unit -> (Z.t * 'a) Prims.list) (key_of : 'a -> Prims.string) : 'a lazy_term_cache =
  { populated = false;
    forward   = Stdlib.Hashtbl.create 17;
    reverse   = Stdlib.Hashtbl.create 17;
    populate  = populate;
    key_of    = key_of }
let lookup_by_id (c : 'a lazy_term_cache) (i : Prims.nat) : 'a FStar_Pervasives_Native.option =
  _lazy_term_cache_ensure c;
  match Stdlib.Hashtbl.find_opt c.forward (Z.to_int i) with
  | Some v -> FStar_Pervasives_Native.Some v
  | None   -> FStar_Pervasives_Native.None
let lookup_by_key (c : 'a lazy_term_cache) (k : Prims.string) : Prims.nat FStar_Pervasives_Native.option =
  _lazy_term_cache_ensure c;
  match Stdlib.Hashtbl.find_opt c.reverse k with
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
  | None   -> FStar_Pervasives_Native.None
let is_populated (c : 'a lazy_term_cache) : Prims.bool =
  c.populated
let size (c : 'a lazy_term_cache) : Prims.nat =
  Z.of_int (Stdlib.Hashtbl.length c.forward)
let to_list (c : 'a lazy_term_cache) : 'a Prims.list =
  _lazy_term_cache_ensure c;
  let pairs = Stdlib.Hashtbl.fold (fun i v acc -> (i, v) :: acc) c.forward [] in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.map snd sorted
