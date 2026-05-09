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
