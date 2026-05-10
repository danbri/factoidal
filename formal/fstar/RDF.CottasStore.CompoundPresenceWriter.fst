module RDF.CottasStore.CompoundPresenceWriter

(* Pure-F* serialiser for the COTTAS .po.presence companion file's
   header. Issue #104 / #200 PR2 part 3 (2026-05-09). Migrates the
   byte-layout half of `Cottas_compound_po_writer` from
   formal/fstar/experimental_ocaml_glue/
   cottas_ondisk_zzzzzzzzzzzzz_compound_po_writer.sh out of OCaml.

   Rule-#11 scope: as with PresenceWriter, the FILE FORMAT HEADER
   belongs in F*. The rg_offsets array (u64 * (num_rgs+1) bytes) and
   the pairs array (u64 * total_pairs bytes) stay in OCaml — these
   are large data buffers built from sorted-array merges, where F*'s
   list representation costs millions of cons cells per column.

   On-disk format (mirrors the OCaml writer comment):

     [ magic       : u32   'COPO' = 0x4f504f43 (LE) ]
     [ version     : u32   currently 1 ]
     [ num_rgs     : u32 ]
     [ pred_dict_size : u32 ]
     [ obj_dict_size  : u32 ]
                                                        (20 bytes header)
     [ rg_offsets : u64 * (num_rgs + 1) ]
     [ pairs      : u64 * total_pairs   ]

   Caller responsibility:
     1. Compute sorted (p_id, o_id) pairs per rg, build flat pair array.
     2. Compute rg_offsets prefix-sum array.
     3. Call serialize_header with num_rgs, pred_size, obj_size to get
        the 20-byte prefix.
     4. Write header + rg_offsets bytes + pairs bytes via atomic_write. *)

open FStar.List.Tot

module Lh = RDF.List.Helpers

(* --- Header constants ------------------------------------------------- *)

let copo_magic     : nat = 0x4f504f43      (* 'COPO' little-endian *)
let copo_version   : nat = 1
let header_size    : nat = 20

(* --- Header builder --------------------------------------------------- *)

let build_header
  (num_rgs        : nat{num_rgs        < 4294967296})
  (pred_dict_size : nat{pred_dict_size < 4294967296})
  (obj_dict_size  : nat{obj_dict_size  < 4294967296})
  : Tot RDF.Bytes.bytes
  =
  Lh.append_tr (RDF.Bytes.write_u32_le copo_magic)
    (Lh.append_tr (RDF.Bytes.write_u32_le copo_version)
      (Lh.append_tr (RDF.Bytes.write_u32_le num_rgs)
        (Lh.append_tr (RDF.Bytes.write_u32_le pred_dict_size)
          (RDF.Bytes.write_u32_le obj_dict_size))))

(* serialize_header num_rgs pred_dict_size obj_dict_size
     Produces the 20-byte .po.presence header.

     Returns [] if any size overflows u32. The on-disk reader checks
     the same bounds; out-of-range corpora can't be written
     correctly. *)
let serialize_compound_presence_header
  (num_rgs        : nat)
  (pred_dict_size : nat)
  (obj_dict_size  : nat)
  : Tot RDF.Bytes.bytes
  =
  if num_rgs        >= 4294967296 then []
  else if pred_dict_size >= 4294967296 then []
  else if obj_dict_size  >= 4294967296 then []
  else build_header num_rgs pred_dict_size obj_dict_size

(* --- u64-array (de)serialisation helpers ------------------------------ *)

(* Each u64_le entry is 8 bytes; bounded so the recursion terminates. *)
let rec serialize_u64_list (xs : list nat)
  : Tot RDF.Bytes.bytes (decreases xs)
  =
  match xs with
  | [] -> []
  | x :: rest ->
    if x >= 18446744073709551616 then []
    else Lh.append_tr (RDF.Bytes.write_u64_le x) (serialize_u64_list rest)

(* Read exactly k u64_le values from bs. Returns the list and the
   remaining tail. None on premature end. *)
let rec parse_n_u64s (k : nat) (bs : RDF.Bytes.bytes)
  : Tot (option (list nat & RDF.Bytes.bytes)) (decreases k)
  =
  if k = 0 then Some ([], bs)
  else
    match RDF.Bytes.parse_u64_le bs with
    | None -> None
    | Some (v, rest) ->
      match parse_n_u64s (k - 1) rest with
      | None -> None
      | Some (xs, after) -> Some (v :: xs, after)

(* last_of_or xs default
     Returns the last element of [xs], or [default] if [xs] is empty.
     Used to read the total_pairs sentinel from rg_offsets. *)
let rec last_of_or (xs : list nat) (default_ : nat)
  : Tot nat (decreases xs)
  =
  match xs with
  | [] -> default_
  | [x] -> x
  | _ :: t -> last_of_or t default_

(* --- Top-level serialiser -------------------------------------------- *)

(* serialize_compound_presence num_rgs pred_dict_size obj_dict_size rg_offsets pairs
     Produces the full .po.presence file byte sequence.

     Returns [] if any header field overflows u32. Caller-provided
     invariants (NOT enforced here, mirroring serialize_dict's contract):
       - length rg_offsets = num_rgs + 1
       - rg_offsets is monotonic non-decreasing
       - rg_offsets[num_rgs] = length pairs (= total_pairs)
       - every entry in rg_offsets and pairs fits in u64.

     The on-disk reader (CompoundPresenceBitmap.fst) interprets the
     same byte layout. *)
let serialize_compound_presence
  (num_rgs        : nat)
  (pred_dict_size : nat)
  (obj_dict_size  : nat)
  (rg_offsets     : list nat)
  (pairs          : list nat)
  : Tot RDF.Bytes.bytes
  =
  if num_rgs        >= 4294967296 then []
  else if pred_dict_size >= 4294967296 then []
  else if obj_dict_size  >= 4294967296 then []
  else
    let header  = build_header num_rgs pred_dict_size obj_dict_size in
    let off_b   = serialize_u64_list rg_offsets in
    let pair_b  = serialize_u64_list pairs in
    Lh.append_tr header (Lh.append_tr off_b pair_b)

(* --- Round-trip parser ------------------------------------------------ *)

(* parse_compound_presence bs
     Inverse of [serialize_compound_presence]. Reads the COPO header,
     validates magic + version, then peels rg_offsets (num_rgs + 1
     u64 entries) and pairs (rg_offsets[num_rgs] u64 entries — read
     from the trailing offset entry).

     Returns [None] if any of:
       - magic mismatch ('COPO' = 0x4f504f43)
       - version mismatch (currently 1)
       - input shorter than declared by header
       - rg_offsets is empty (num_rgs + 1 must be >= 1)

     Round-trip witness:
       parse_compound_presence
         (serialize_compound_presence n p o offs pairs)
         == Some (n, p, o, offs, pairs)
     for any (n, p, o) under 2^32 with [length offs = n+1],
     [last offs = length pairs], and every entry < 2^64. *)
let parse_compound_presence (bs : RDF.Bytes.bytes)
  : Tot (option (nat & nat & nat & list nat & list nat))
  =
  match RDF.Bytes.parse_u32_le bs with
  | None -> None
  | Some (m, after_magic) ->
    if not (m = copo_magic) then None
    else
      match RDF.Bytes.parse_u32_le after_magic with
      | None -> None
      | Some (v, after_version) ->
        if not (v = copo_version) then None
        else
          match RDF.Bytes.parse_u32_le after_version with
          | None -> None
          | Some (num_rgs, after_rgs) ->
            match RDF.Bytes.parse_u32_le after_rgs with
            | None -> None
            | Some (pred_size, after_pred) ->
              match RDF.Bytes.parse_u32_le after_pred with
              | None -> None
              | Some (obj_size, after_header) ->
                match parse_n_u64s (num_rgs + 1) after_header with
                | None -> None
                | Some (rg_offsets, after_offsets) ->
                  // Number of pairs = trailing offsets entry. The list
                  // has num_rgs+1 entries; the last is pairs_total.
                  let total_pairs : nat = last_of_or rg_offsets 0 in
                  match parse_n_u64s total_pairs after_offsets with
                  | None -> None
                  | Some (pairs, _trailing) ->
                    Some (num_rgs, pred_size, obj_size, rg_offsets, pairs)

(* --- Empty base case sublemmas --------------------------------------- *)

let lemma_parse_n_u64s_one (v : nat{v < 18446744073709551616}) (rest : RDF.Bytes.bytes)
  : Lemma (ensures parse_n_u64s 1
                     (FStar.List.Tot.append (RDF.Bytes.write_u64_le v) rest)
                   == Some ([v], rest))
  = RDF.Bytes.lemma_parse_write_u64_le_inverse v rest

let lemma_parse_n_u64s_zero (bs : RDF.Bytes.bytes)
  : Lemma (ensures parse_n_u64s 0 bs == Some ([], bs))
  = ()

let lemma_last_of_or_singleton_zero ()
  : Lemma (ensures last_of_or [0] 0 == 0)
  = ()

(* Bridge: serialize_compound_presence 0 0 0 [0] [] reduces to a
   right-associated FStar.List.Tot.append chain. Mirror of the
   OffsetsWriter shape lemma; one extra u32 in the header
   (5 u32s here vs. 4 in OffsetsWriter). *)
let lemma_serialize_compound_presence_empty_shape ()
  : Lemma (ensures (
      let m = RDF.Bytes.write_u32_le copo_magic in
      let v = RDF.Bytes.write_u32_le copo_version in
      let r = RDF.Bytes.write_u32_le 0 in
      let p = RDF.Bytes.write_u32_le 0 in
      let o = RDF.Bytes.write_u32_le 0 in
      let s = RDF.Bytes.write_u64_le 0 in
      serialize_compound_presence 0 0 0 [0] []
        == FStar.List.Tot.append m
            (FStar.List.Tot.append v
              (FStar.List.Tot.append r
                (FStar.List.Tot.append p
                  (FStar.List.Tot.append o s))))))
  = let m = RDF.Bytes.write_u32_le copo_magic in
    let v = RDF.Bytes.write_u32_le copo_version in
    let r = RDF.Bytes.write_u32_le 0 in
    let p = RDF.Bytes.write_u32_le 0 in
    let o = RDF.Bytes.write_u32_le 0 in
    let s = RDF.Bytes.write_u64_le 0 in
    (* build_header: append_tr m (append_tr v (append_tr r (append_tr p o))). *)
    Lh.lemma_append_tr_eq p o;
    Lh.lemma_append_tr_eq r (Lh.append_tr p o);
    Lh.lemma_append_tr_eq v (Lh.append_tr r (Lh.append_tr p o));
    Lh.lemma_append_tr_eq m (Lh.append_tr v (Lh.append_tr r (Lh.append_tr p o)));
    (* serialize_u64_list [0] = s; serialize_u64_list [] = []. *)
    Lh.lemma_append_tr_eq s [];
    FStar.List.Tot.Properties.append_l_nil s;
    let off_b = serialize_u64_list [0] in
    let pair_b = serialize_u64_list [] in
    Lh.lemma_append_tr_eq off_b pair_b;
    FStar.List.Tot.Properties.append_l_nil off_b;
    let header = build_header 0 0 0 in
    Lh.lemma_append_tr_eq header s;
    (* Right-associate via four append_assoc applications. *)
    FStar.List.Tot.Properties.append_assoc m
      (FStar.List.Tot.append v
        (FStar.List.Tot.append r
          (FStar.List.Tot.append p o))) s;
    FStar.List.Tot.Properties.append_assoc v
      (FStar.List.Tot.append r
        (FStar.List.Tot.append p o)) s;
    FStar.List.Tot.Properties.append_assoc r
      (FStar.List.Tot.append p o) s;
    FStar.List.Tot.Properties.append_assoc p o s

(* Empty base case: serialize_compound_presence 0 0 0 [0] [] then
   parse_compound_presence round-trips to Some(0, 0, 0, [0], []).
   28 bytes total (20-byte header + 8-byte sentinel u64). *)
let lemma_parse_serialize_compound_presence_empty_case ()
  : Lemma (ensures parse_compound_presence
                     (serialize_compound_presence 0 0 0 [0] [])
                   == Some (0, 0, 0, [0], []))
  = let m = RDF.Bytes.write_u32_le copo_magic in
    let v = RDF.Bytes.write_u32_le copo_version in
    let r = RDF.Bytes.write_u32_le 0 in
    let p = RDF.Bytes.write_u32_le 0 in
    let o = RDF.Bytes.write_u32_le 0 in
    let s = RDF.Bytes.write_u64_le 0 in
    lemma_serialize_compound_presence_empty_shape ();
    (* Peel five header u32s. *)
    RDF.Bytes.lemma_parse_write_u32_le_inverse copo_magic
      (FStar.List.Tot.append v
        (FStar.List.Tot.append r
          (FStar.List.Tot.append p
            (FStar.List.Tot.append o s))));
    RDF.Bytes.lemma_parse_write_u32_le_inverse copo_version
      (FStar.List.Tot.append r
        (FStar.List.Tot.append p
          (FStar.List.Tot.append o s)));
    RDF.Bytes.lemma_parse_write_u32_le_inverse 0
      (FStar.List.Tot.append p
        (FStar.List.Tot.append o s));
    RDF.Bytes.lemma_parse_write_u32_le_inverse 0
      (FStar.List.Tot.append o s);
    RDF.Bytes.lemma_parse_write_u32_le_inverse 0 s;
    (* Peel sentinel u64 + parse_n_u64s 0 (for pairs). *)
    FStar.List.Tot.Properties.append_l_nil s;
    lemma_parse_n_u64s_one 0 [];
    lemma_last_of_or_singleton_zero ();
    lemma_parse_n_u64s_zero []
