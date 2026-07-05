open Prims
(* ---- Phase A scaffold ----------------------------------------------
   The in-memory COTTAS encoder produces a cottas_ondisk_store backed
   by a Bytes.t buffer instead of an mmap'd file. Phase A wires the
   skeleton; the encoder body is intentionally NOT implemented here.
   Returning None signals "no in-mem store available" to callers, who
   fall back to the existing indexed_graph_backend path. This keeps
   W3C 1657/1658 stable while the design lands.

   Phase A.5 will add:
     - Cottas_inmem_encoder.encode_to_bytes : rdf_graph -> Bytes.t
       (footer + 4 string columns + row count; no presence bitmaps)
     - process-wide registry mapping graph_id -> Bytes.t ref
     - hookup into Mim2 byte cache so parquet_read_range / _tail
       resolve "inmem://..." paths against the registry.
   See docs/designissues/in-memory-cottas-encoder.md.

   Rule #11: this module is pure I/O glue. No semantic logic here —
   the bytes produced (in Phase A.5) are consumed by the existing
   F*-extracted reader in RDF.CottasStore unchanged. *)

module Cottas_inmem_encoder = struct
  (* Phase A.5 hook points: process-wide buffer registry. Keyed by
     graph_id (the same string carried as cods_artifact_path), maps
     to the encoded Bytes.t. Empty in Phase A. *)
  let buffers : (string, Bytes.t) Hashtbl.t = Hashtbl.create 7

  let inmem_path_prefix = "inmem://"
  let _ = inmem_path_prefix  (* Phase A.5 will use this *)

  (* Phase A.5 will fill in encode_to_bytes : rdf_graph -> Bytes.t.
     Layout sketch (per design note):
       - parquet footer (num_rows = List.length g, 1 row group)
       - 4 string columns: subject, predicate, object, graph
       - NO presence bitmaps (Phase B)
       - NO compound (p,o) bitmap (Phase C)
     The footer + column page format must match what
     Parquet.Footer.probe_parquet_* parses today. *)
  let _encode_to_bytes_todo (_g : 'a) : Bytes.t =
    failwith "Cottas_inmem_encoder.encode_to_bytes: Phase A.5 not yet wired"
end

let cottas_inmem_open (_graph_id : Prims.string) (_g : 'a) :
  RDF_CottasStore.cottas_ondisk_store FStar_Pervasives_Native.option =
  (* Phase A: stub returns None. Callers fall back to the
     indexed_graph_backend path. Phase A.5 will encode g to bytes,
     register them under graph_id, and construct a cottas_ondisk_store
     whose cods_artifact_path = "inmem://" ^ graph_id. *)
  FStar_Pervasives_Native.None
