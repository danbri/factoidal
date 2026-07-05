open Prims
type 'a populate_result = (Prims.nat * 'a * Prims.string) Prims.list
type 'a lazy_dict = {
  mutable populated  : bool;
  forward_typed      : (Stdlib.Int.t, 'a) Stdlib.Hashtbl.t;
  forward_raw        : (Stdlib.Int.t, string) Stdlib.Hashtbl.t;
  reverse_canonical  : (string, Stdlib.Int.t) Stdlib.Hashtbl.t;
  reverse_raw        : (string, Stdlib.Int.t) Stdlib.Hashtbl.t;
  populate           : unit -> (Z.t * 'a * Prims.string) Prims.list;
  key_of             : 'a -> Prims.string;
} (* __LAZY_DICT_RUNTIME_APPLIED__ *)

(* Run d.populate once; fill all four hashtables; mark d.populated.
   Idempotent. NOT mutex-protected — matches the pre-#254 baseline
   thread-safety (Mutex.t not available in the build's Stdlib for
   this OCaml toolchain). Cross-thread safety is provided by OCaml's
   GC-pause semantics that the original cottas_ondisk_z_lazy_open
   patch also relies on. *)
let _lazy_dict_ensure (d : 'a lazy_dict) : unit =
  if not d.populated then begin
    let entries = d.populate () in
    Stdlib.List.iter (fun (id_z, typed, raw) ->
      let id = Z.to_int id_z in
      Stdlib.Hashtbl.replace d.forward_typed     id typed;
      Stdlib.Hashtbl.replace d.forward_raw       id raw;
      Stdlib.Hashtbl.replace d.reverse_canonical (d.key_of typed) id;
      Stdlib.Hashtbl.replace d.reverse_raw       raw id
    ) entries;
    d.populated <- true
  end
let mk_lazy_dict (populate : unit -> (Z.t * 'a * Prims.string) Prims.list) (key_of : 'a -> Prims.string) : 'a lazy_dict =
  { populated = false;
    forward_typed     = Stdlib.Hashtbl.create 17;
    forward_raw       = Stdlib.Hashtbl.create 17;
    reverse_canonical = Stdlib.Hashtbl.create 17;
    reverse_raw       = Stdlib.Hashtbl.create 17;
    populate          = populate;
    key_of            = key_of }
let decode_by_id (d : 'a lazy_dict) (i : Prims.nat) : 'a FStar_Pervasives_Native.option =
  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.forward_typed (Z.to_int i) with
  | Some v -> FStar_Pervasives_Native.Some v
  | None   -> FStar_Pervasives_Native.None
let decode_raw_by_id (d : 'a lazy_dict) (i : Prims.nat) : Prims.string FStar_Pervasives_Native.option =
  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.forward_raw (Z.to_int i) with
  | Some s -> FStar_Pervasives_Native.Some s
  | None   -> FStar_Pervasives_Native.None
let encode_by_key (d : 'a lazy_dict) (k : Prims.string) : Prims.nat FStar_Pervasives_Native.option =
  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.reverse_canonical k with
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
  | None   -> FStar_Pervasives_Native.None
let encode_by_raw_token (d : 'a lazy_dict) (t : Prims.string) : Prims.nat FStar_Pervasives_Native.option =
  _lazy_dict_ensure d;
  match Stdlib.Hashtbl.find_opt d.reverse_raw t with
  | Some i -> FStar_Pervasives_Native.Some (Z.of_int i)
  | None   -> FStar_Pervasives_Native.None
let is_populated (d : 'a lazy_dict) : Prims.bool =
  d.populated
let size (d : 'a lazy_dict) : Prims.nat =
  Z.of_int (Stdlib.Hashtbl.length d.forward_typed)
let to_typed_list (d : 'a lazy_dict) : 'a Prims.list =
  _lazy_dict_ensure d;
  let pairs = Stdlib.Hashtbl.fold (fun i v acc -> (i, v) :: acc) d.forward_typed [] in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.map snd sorted
let to_raw_list (d : 'a lazy_dict) : Prims.string Prims.list =
  _lazy_dict_ensure d;
  let pairs = Stdlib.Hashtbl.fold (fun i v acc -> (i, v) :: acc) d.forward_raw [] in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.map snd sorted
let rec lookup_id_in_list :
  'a .
    (Prims.nat * 'a) Prims.list ->
      Prims.nat -> 'a FStar_Pervasives_Native.option
  =
  fun entries id ->
    match entries with
    | [] -> FStar_Pervasives_Native.None
    | (id', v)::rest ->
        if id = id'
        then FStar_Pervasives_Native.Some v
        else lookup_id_in_list rest id
let rec lookup_key_in_list :
  'a .
    (Prims.string * 'a) Prims.list ->
      Prims.string -> 'a FStar_Pervasives_Native.option
  =
  fun entries key ->
    match entries with
    | [] -> FStar_Pervasives_Native.None
    | (k, v)::rest ->
        if k = key
        then FStar_Pervasives_Native.Some v
        else lookup_key_in_list rest key
