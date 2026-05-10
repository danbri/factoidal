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

(* Empty base case: serialize_presence 0 0 [] then parse_presence
   round-trips to Some (0, 0, []). 16-byte header only, no bitmap.
   Verifies via foundation lemmas in RDF.Bytes (post-#252).

   The proof composes:
     - Lh.lemma_append_tr_eq + FStar.List.Tot.Properties.append_l_nil
       to show serialize_presence 0 0 [] reduces to build_header 0 0.
     - Four applications of lemma_parse_write_u32_le_inverse to peel
       the four u32 fields off the header.
     - lemma_parse_n_bytes_inverse with bs = [] and rest = [] to
       discharge the trailing parse_n_bytes 0 [] = Some([], []).

   The CI hash-roundtrip test in tests/unit/presence_writer_roundtrip.ml
   provides 5-fixture empirical evidence for the general non-empty
   case meanwhile. Inductive case (general bitmap) is tracked as a
   follow-up; mirrors the DictWriter cons-case work needed under
   #200 Section B. *)
let lemma_parse_serialize_presence_empty_case ()
  : Lemma (ensures parse_presence (serialize_presence 0 0 []) == Some (0, 0, []))
  = let header = build_header 0 0 in
    Lh.lemma_append_tr_eq header [];
    FStar.List.Tot.Properties.append_l_nil header;
    assert (serialize_presence 0 0 [] == header);
    (* header structurally is:
         append_tr (write_u32_le magic) (
           append_tr (write_u32_le version) (
             append_tr (write_u32_le 0) (write_u32_le 0))) *)
    let b1 = RDF.Bytes.write_u32_le 0 in
    let b2 = RDF.Bytes.write_u32_le 0 in
    let b3 = Lh.append_tr b1 b2 in
    let b4 = RDF.Bytes.write_u32_le presence_version in
    let b5 = Lh.append_tr b4 b3 in
    let b6 = RDF.Bytes.write_u32_le presence_magic in
    Lh.lemma_append_tr_eq b1 b2;
    Lh.lemma_append_tr_eq b4 b3;
    Lh.lemma_append_tr_eq b6 b5;
    (* Now header == FStar.List.Tot.append b6 (append b4 (append b1 b2)). *)
    RDF.Bytes.lemma_parse_write_u32_le_inverse presence_magic
      (FStar.List.Tot.append b4 (FStar.List.Tot.append b1 b2));
    RDF.Bytes.lemma_parse_write_u32_le_inverse presence_version
      (FStar.List.Tot.append b1 b2);
    RDF.Bytes.lemma_parse_write_u32_le_inverse 0 b2;
    RDF.Bytes.lemma_parse_write_u32_le_inverse 0 [];
    RDF.Bytes.lemma_parse_n_bytes_inverse [] []

(* General-case round-trip: serialize_presence num_rgs num_tokens bitmap
   round-trips back to (num_rgs, num_tokens, bitmap), provided the
   header-field bounds hold and the bitmap length matches what the
   parser expects.

   Note: the parser computes `needed = ceil(num_rgs * num_tokens / 8)`
   and reads exactly that many bytes. The round-trip therefore only
   holds when the supplied bitmap has THAT exact length. The lemma
   states this as a precondition; the empty case is a special case
   where length bitmap == 0 == ceil(0/8). *)
let lemma_parse_serialize_presence
  (num_rgs : nat) (num_tokens : nat) (bitmap : RDF.Bytes.bytes)
  : Lemma
      (requires num_rgs < 4294967296
                /\ num_tokens < 4294967296
                /\ FStar.List.Tot.length bitmap
                   == (num_rgs `op_Multiply` num_tokens + 7) / 8)
      (ensures parse_presence (serialize_presence num_rgs num_tokens bitmap)
               == Some (num_rgs, num_tokens, bitmap))
  = let m = RDF.Bytes.write_u32_le presence_magic in
    let v = RDF.Bytes.write_u32_le presence_version in
    let r = RDF.Bytes.write_u32_le num_rgs in
    let nt = RDF.Bytes.write_u32_le num_tokens in
    (* Bridge build_header's append_tr chain to FStar.List.Tot.append. *)
    Lh.lemma_append_tr_eq r nt;
    Lh.lemma_append_tr_eq v (Lh.append_tr r nt);
    Lh.lemma_append_tr_eq m (Lh.append_tr v (Lh.append_tr r nt));
    let header = build_header num_rgs num_tokens in
    Lh.lemma_append_tr_eq header bitmap;
    (* Re-associate: header @ bitmap = m @ (v @ (r @ (nt @ bitmap))). *)
    FStar.List.Tot.Properties.append_assoc m
      (FStar.List.Tot.append v (FStar.List.Tot.append r nt)) bitmap;
    FStar.List.Tot.Properties.append_assoc v
      (FStar.List.Tot.append r nt) bitmap;
    FStar.List.Tot.Properties.append_assoc r nt bitmap;
    (* Peel the four u32s. *)
    RDF.Bytes.lemma_parse_write_u32_le_inverse presence_magic
      (FStar.List.Tot.append v
        (FStar.List.Tot.append r
          (FStar.List.Tot.append nt bitmap)));
    RDF.Bytes.lemma_parse_write_u32_le_inverse presence_version
      (FStar.List.Tot.append r
        (FStar.List.Tot.append nt bitmap));
    RDF.Bytes.lemma_parse_write_u32_le_inverse num_rgs
      (FStar.List.Tot.append nt bitmap);
    RDF.Bytes.lemma_parse_write_u32_le_inverse num_tokens bitmap;
    (* Peel the bitmap. parse_n_bytes (length bitmap) (bitmap @ []) =
       Some (bitmap, []). *)
    FStar.List.Tot.Properties.append_l_nil bitmap;
    RDF.Bytes.lemma_parse_n_bytes_inverse bitmap []
