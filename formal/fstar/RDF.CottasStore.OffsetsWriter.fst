module RDF.CottasStore.OffsetsWriter

(* Pure-F* serialiser for the COTTAS .p.offsets companion file's
   header. Issue Lamed3 / #200 PR2 part 4 (2026-05-09). Migrates the
   byte-layout half of `build_offsets_file` from
   formal/fstar/experimental_ocaml_glue/
   cottas_ondisk_zzzzzz_lamed3_offset_idx.sh out of OCaml.

   Rule-#11 scope: same split as PresenceWriter and
   CompoundPresenceWriter. The 16-byte header (magic, version,
   num_rgs, num_preds) belongs in F*. The rg_offsets u64 array
   (length num_rgs * num_preds + 1) and the subject-id payload
   (parliament-scale: tens of millions of entries) stay in OCaml as
   imperative array fills.

   On-disk format:

     [ magic       : u32   'COTO' = 0x4f544f43 (LE) ]
     [ version     : u32   currently 1 ]
     [ num_rgs     : u32 ]
     [ num_preds   : u32 ]
                                                        (16 bytes header)
     [ rg_offsets  : u64 * (num_rgs * num_preds + 1) ]
     [ subject_ids : u32[] sorted per (rg, pred) bucket ]

   Caller responsibility:
     1. Walk parquet rows, bucket subject ids by (rg, pred).
     2. Compute prefix-sum rg_offsets array.
     3. Call serialize_offsets_header with num_rgs, num_preds.
     4. Write header + rg_offsets bytes + subject_ids bytes via
        atomic_write. *)

open FStar.List.Tot

module Lh = RDF.List.Helpers

(* --- Header constants ------------------------------------------------- *)

let coto_magic     : nat = 0x4f544f43      (* 'COTO' little-endian *)
let coto_version   : nat = 1
let header_size    : nat = 16

(* --- Header builder --------------------------------------------------- *)

let build_header
  (num_rgs   : nat{num_rgs   < 4294967296})
  (num_preds : nat{num_preds < 4294967296})
  : Tot RDF.Bytes.bytes
  =
  Lh.append_tr (RDF.Bytes.write_u32_le coto_magic)
    (Lh.append_tr (RDF.Bytes.write_u32_le coto_version)
      (Lh.append_tr (RDF.Bytes.write_u32_le num_rgs)
        (RDF.Bytes.write_u32_le num_preds)))

(* serialize_offsets_header num_rgs num_preds
     Produces the 16-byte .p.offsets header.

     Returns [] on u32 overflow; the on-disk reader checks the same
     bounds. *)
let serialize_offsets_header
  (num_rgs   : nat)
  (num_preds : nat)
  : Tot RDF.Bytes.bytes
  =
  if num_rgs   >= 4294967296 then []
  else if num_preds >= 4294967296 then []
  else build_header num_rgs num_preds

(* --- u32-array (de)serialisation helpers ------------------------------ *)

(* Each u32_le entry is 4 bytes. *)
let rec serialize_u32_list (xs : list nat)
  : Tot RDF.Bytes.bytes (decreases xs)
  =
  match xs with
  | [] -> []
  | x :: rest ->
    if x >= 4294967296 then []
    else Lh.append_tr (RDF.Bytes.write_u32_le x) (serialize_u32_list rest)

(* Read exactly k u32_le values from bs. *)
let rec parse_n_u32s (k : nat) (bs : RDF.Bytes.bytes)
  : Tot (option (list nat & RDF.Bytes.bytes)) (decreases k)
  =
  if k = 0 then Some ([], bs)
  else
    match RDF.Bytes.parse_u32_le bs with
    | None -> None
    | Some (v, rest) ->
      match parse_n_u32s (k - 1) rest with
      | None -> None
      | Some (xs, after) -> Some (v :: xs, after)

(* --- u64-array (de)serialisation helpers ------------------------------ *)

let rec serialize_u64_list (xs : list nat)
  : Tot RDF.Bytes.bytes (decreases xs)
  =
  match xs with
  | [] -> []
  | x :: rest ->
    if x >= 18446744073709551616 then []
    else Lh.append_tr (RDF.Bytes.write_u64_le x) (serialize_u64_list rest)

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

let rec last_of_or (xs : list nat) (default_ : nat)
  : Tot nat (decreases xs)
  =
  match xs with
  | [] -> default_
  | [x] -> x
  | _ :: t -> last_of_or t default_

(* --- Top-level serialiser -------------------------------------------- *)

(* serialize_offsets num_rgs num_preds rg_offsets subject_ids
     Produces the full .p.offsets file byte sequence.

     Returns [] on u32 overflow of num_rgs / num_preds. Caller-provided
     invariants:
       - length rg_offsets = num_rgs * num_preds + 1
       - rg_offsets is monotonic non-decreasing
       - rg_offsets[num_rgs * num_preds] = length subject_ids
       - every entry in rg_offsets fits in u64
       - every subject_id fits in u32. *)
let serialize_offsets
  (num_rgs     : nat)
  (num_preds   : nat)
  (rg_offsets  : list nat)
  (subject_ids : list nat)
  : Tot RDF.Bytes.bytes
  =
  if num_rgs   >= 4294967296 then []
  else if num_preds >= 4294967296 then []
  else
    let header   = build_header num_rgs num_preds in
    let off_b    = serialize_u64_list rg_offsets in
    let subj_b   = serialize_u32_list subject_ids in
    Lh.append_tr header (Lh.append_tr off_b subj_b)

(* --- Round-trip parser ------------------------------------------------ *)

(* parse_offsets bs
     Inverse of [serialize_offsets]. Reads the COTO header, validates
     magic + version, peels rg_offsets (num_rgs * num_preds + 1 u64s),
     then subject_ids (rg_offsets[last] u32s — read from the trailing
     offset entry).

     Returns [None] on:
       - magic mismatch ('COTO' = 0x4f544f43)
       - version mismatch (currently 1)
       - input shorter than declared

     Round-trip witness:
       parse_offsets (serialize_offsets r p offs subjs)
         == Some (r, p, offs, subjs)
     for any (r, p) under 2^32, [length offs = r*p + 1],
     [last offs = length subjs], every offset < 2^64, every subj < 2^32. *)
let parse_offsets (bs : RDF.Bytes.bytes)
  : Tot (option (nat & nat & list nat & list nat))
  =
  match RDF.Bytes.parse_u32_le bs with
  | None -> None
  | Some (m, after_magic) ->
    if not (m = coto_magic) then None
    else
      match RDF.Bytes.parse_u32_le after_magic with
      | None -> None
      | Some (v, after_version) ->
        if not (v = coto_version) then None
        else
          match RDF.Bytes.parse_u32_le after_version with
          | None -> None
          | Some (num_rgs, after_rgs) ->
            match RDF.Bytes.parse_u32_le after_rgs with
            | None -> None
            | Some (num_preds, after_header) ->
              let n_offsets : nat = num_rgs `op_Multiply` num_preds + 1 in
              match parse_n_u64s n_offsets after_header with
              | None -> None
              | Some (rg_offsets, after_offsets) ->
                let total_subjs : nat = last_of_or rg_offsets 0 in
                match parse_n_u32s total_subjs after_offsets with
                | None -> None
                | Some (subject_ids, _trailing) ->
                  Some (num_rgs, num_preds, rg_offsets, subject_ids)
