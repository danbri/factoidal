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
