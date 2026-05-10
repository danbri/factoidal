module RDF.CottasStore.PresenceWriter

(* Pure-F* serialiser for the COTTAS .presence companion file.

   #200 PR2 part 2 (2026-05-09). Migrates the byte-layout half of
   `write_presence_file` from formal/fstar/experimental_ocaml_glue/
   cottas_ondisk_zzzzz_ondisk_index.sh out of OCaml.

   Rule-#11 scope: the FILE FORMAT HEADER (magic, version, counts)
   belongs in F*. The bitmap CONTENTS are computed by the OCaml
   caller — that step is per-pair set-bit data processing whose
   perf cost matters for parliament-scale corpora (parliament-sized
   .presence is ~12.5MB; materializing as F*'s `list FStar.Char.char`
   would allocate millions of cons cells). The F* layer here enforces:
     - magic 'COTP' (0x50544f43 LE)
     - version 1
     - 16-byte header layout
     - rg_count, num_tokens fit in u32

   Two entry points:
     - `serialize_presence_header` — produces the 16-byte header, used
       by the OCaml caller as a `Bytes.t` prefix that it concatenates
       with its own non-F-star bitmap construction. Preferred for large
       corpora.
     - `serialize_presence` — produces the full file (header + bitmap)
       when the bitmap is small enough to fit in F-star's `bytes` list.
       Useful for tests and the round-trip lemma.

   On-disk format (mirrors RDF.CottasStore.PresenceBitmap.fst):

     [ magic       : u32   'COTP' = 0x50544f43 (LE) ]
     [ version     : u32   currently 1 ]
     [ num_rgs     : u32 ]
     [ num_tokens  : u32 ]
     [ bitmap      : ceil(num_rgs * num_tokens / 8) bytes,
                     row-major, bit (rg*num_tokens + tok) ]

   The OCaml caller's responsibility:
     1. Walk per-rg distinct-token sets, set bits in a Bytes.t.
     2. Convert Bytes.t to a `bytes` list and call `serialize_presence`.
     3. Atomic-write the result. *)

open FStar.List.Tot

module Lh = RDF.List.Helpers

(* --- Header constants ------------------------------------------------- *)

let presence_magic   : nat = 0x50544f43      (* 'COTP' little-endian *)
let presence_version : nat = 1
let header_size      : nat = 16

(* --- Header builder --------------------------------------------------- *)

let build_header
  (num_rgs : nat{num_rgs < 4294967296})
  (num_tokens : nat{num_tokens < 4294967296})
  : Tot RDF.Bytes.bytes
  =
  Lh.append_tr (RDF.Bytes.write_u32_le presence_magic)
    (Lh.append_tr (RDF.Bytes.write_u32_le presence_version)
      (Lh.append_tr (RDF.Bytes.write_u32_le num_rgs)
        (RDF.Bytes.write_u32_le num_tokens)))

(* Header-only entry point. Returns [] on overflow; otherwise a 16-byte
   sequence the OCaml caller writes to the start of the .presence file
   before its own bitmap bytes. *)
let serialize_presence_header
  (num_rgs : nat)
  (num_tokens : nat)
  : Tot RDF.Bytes.bytes
  =
  if num_rgs >= 4294967296 then []
  else if num_tokens >= 4294967296 then []
  else build_header num_rgs num_tokens

(* --- Top-level serialiser -------------------------------------------- *)

(* serialize_presence num_rgs num_tokens bitmap
     Produces the .presence file byte sequence.

     Returns [] if num_rgs or num_tokens overflows u32 — practical
     impossibilities for real corpora but the precondition keeps F*
     honest.

     Caller-provided invariant (NOT enforced here): bitmap length must
     equal ceil(num_rgs * num_tokens / 8). The on-disk reader
     (PresenceBitmap.fst) computes this same expression and indexes
     past the header by header_size bytes. *)
let serialize_presence
  (num_rgs : nat)
  (num_tokens : nat)
  (bitmap : RDF.Bytes.bytes)
  : Tot RDF.Bytes.bytes
  =
  if num_rgs >= 4294967296 then []
  else if num_tokens >= 4294967296 then []
  else
    let header = build_header num_rgs num_tokens in
    Lh.append_tr header bitmap

(* --- Round-trip parser ------------------------------------------------ *)

(* parse_presence bs
     Inverse of [serialize_presence]. Reads the COTP header, validates
     magic + version, then peels (num_rgs, num_tokens) and the trailing
     bitmap of length ceil(num_rgs * num_tokens / 8) bytes.

     Returns [None] if any of:
       - magic mismatch ('COTP' = 0x50544f43)
       - version mismatch (currently 1)
       - input shorter than declared by header
       - header counts overflow u32

     The caller's expectation (round-trip witness):
       parse_presence (serialize_presence num_rgs num_tokens bm)
         == Some (num_rgs, num_tokens, bm)
     for any (num_rgs, num_tokens) under 2^32 and any bitmap whose
     length matches ceil(num_rgs * num_tokens / 8). The CI hash test
     in tests/unit/presence_writer_roundtrip.ml gives empirical
     evidence; promotion to a formal F* lemma is deferred. *)
let parse_presence (bs : RDF.Bytes.bytes)
  : Tot (option (nat & nat & RDF.Bytes.bytes))
  =
  match RDF.Bytes.parse_u32_le bs with
  | None -> None
  | Some (m, after_magic) ->
    if not (m = presence_magic) then None
    else
      match RDF.Bytes.parse_u32_le after_magic with
      | None -> None
      | Some (v, after_version) ->
        if not (v = presence_version) then None
        else
          match RDF.Bytes.parse_u32_le after_version with
          | None -> None
          | Some (num_rgs, after_rgs) ->
            match RDF.Bytes.parse_u32_le after_rgs with
            | None -> None
            | Some (num_tokens, after_header) ->
              let bits : nat = num_rgs `op_Multiply` num_tokens in
              let needed : nat = (bits + 7) / 8 in
              match RDF.Bytes.parse_n_bytes needed after_header with
              | None -> None
              | Some (bitmap, _trailing) ->
                Some (num_rgs, num_tokens, bitmap)
