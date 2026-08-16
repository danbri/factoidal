module RDF.Bytes

(* Little-endian byte-layout primitives for companion-file writers.
   Section B of #200's migration epic (writers: .dict, .presence,
   .compound-presence, .p.offsets, etc.).

   Per CLAUDE.md rule #11: byte assembly belongs in F\*. Each
   `serialize : data -> Tot (list u8)` lives here or in a sibling
   F\* module; the OCaml side reduces to `write_bytes` of the
   pre-assembled byte sequence.

   Representation: `list FStar.Char.char` where each `char` is
   constrained to the byte range [0, 255]. The tighter type
   `FStar.UInt8.t` is available but Char gives us cheaper string
   conversion via `String.string_of_list` for the final write step.

   Verification scope: total, pure, no `assume val`, no `--lax`.

   UTF-8 (issue #445, 2026-08-15): `bytes_of_string` / `bytes_to_string`
   are NOT a Latin-1/codepoint identity — a string's bytes are its UTF-8
   ENCODING, produced and consumed via `Parser.FastString.Spec`'s
   already-proved codec (`utf8_bytes` / `utf8_decode_all`), never a
   second hand-written encoder (that duplication is exactly what issue
   #443 cost a day over — see `skills/workflow-gotchas-debugging`
   hazard #25). See `lemma_bytes_to_string_of_bytes_of_string` below for
   the round-trip proof. *)

open FStar.List.Tot

module Spec = Parser.FastString.Spec

(* --------------------------------------------------------------------
   byte = char restricted to 0..255, NOW ENFORCED by refinement (issue
   #445). Before this fix `byte` was a bare `FStar.Char.char` alias with
   no upper bound, so `bytes_of_string = String.list_of_string` (raw
   CODEPOINTS, unbounded) typechecked silently — the type never caught
   the very defect its own comment claimed to rule out. With the
   refinement below, that definition no longer typechecks: THAT failure
   is the point, not a regression to work around.
   -------------------------------------------------------------------- *)

let byte = c:FStar.Char.char{FStar.Char.int_of_char c < 256}
let bytes = list byte

let byte_of_int (n : int{n >= 0 /\ n < 256}) : Tot byte =
  FStar.Char.char_of_int n

(* --------------------------------------------------------------------
   int_of_byte b
     Inverse of byte_of_int. Moved ahead of bytes_of_string/
     bytes_to_string (issue #445) because bytes_to_string now needs it
     to bridge into Parser.FastString.Spec's byte type — F* has no
     forward references within a module.
   -------------------------------------------------------------------- *)

let int_of_byte (b : byte) : Tot (n:int{n >= 0 /\ n < 256}) =
  let n = FStar.Char.int_of_char b in
  if n < 0 || n >= 256 then 0 else n

(* int_of_byte (byte_of_int n) == n for n in [0, 256).

   FStar.Char's `char_of_u32_of_char` / `u32_of_char_of_u32` SMTPats
   discharge the round-trip; the U32 round-trip on values < 2^32 is
   automatic. The conditional branch in [int_of_byte] is dead because
   we only call it on bytes produced by [byte_of_int]. *)
let lemma_int_of_byte_of_int (n : int{n >= 0 /\ n < 256})
  : Lemma (ensures int_of_byte (byte_of_int n) == n)
          [SMTPat (int_of_byte (byte_of_int n))]
  = ()

(* --------------------------------------------------------------------
   write_u32_le n
     Little-endian 4-byte encoding of a non-negative int < 2^32.
     Returns a list of 4 bytes in LE order: [n%256; (n/256)%256;
     (n/65536)%256; (n/16777216)%256].
   -------------------------------------------------------------------- *)

let write_u32_le (n : nat{n < 4294967296}) : Tot (b:bytes{length b == 4}) =
  let b0 = n % 256 in
  let b1 = (n / 256) % 256 in
  let b2 = (n / 65536) % 256 in
  let b3 = (n / 16777216) % 256 in
  [byte_of_int b0; byte_of_int b1; byte_of_int b2; byte_of_int b3]

(* --------------------------------------------------------------------
   write_u64_le n
     Little-endian 8-byte encoding of a non-negative int < 2^64.
     Same pattern as write_u32_le.
   -------------------------------------------------------------------- *)

let write_u64_le (n : nat{n < 18446744073709551616}) : Tot bytes =
  let b0 = n % 256 in
  let b1 = (n / 256) % 256 in
  let b2 = (n / 65536) % 256 in
  let b3 = (n / 16777216) % 256 in
  let b4 = (n / 4294967296) % 256 in
  let b5 = (n / 1099511627776) % 256 in
  let b6 = (n / 281474976710656) % 256 in
  let b7 = (n / 72057594037927936) % 256 in
  [byte_of_int b0; byte_of_int b1; byte_of_int b2; byte_of_int b3;
   byte_of_int b4; byte_of_int b5; byte_of_int b6; byte_of_int b7]

(* --------------------------------------------------------------------
   bytes_of_string s
     The UTF-8 ENCODING of s (issue #445): every codepoint becomes its
     1-4 byte UTF-8 form via `Parser.FastString.Spec.utf8_bytes`, the
     same proved encoder `Parser.FastString.fst`'s fast path is
     re-founded on. ASCII strings are unaffected (1 codepoint = 1 byte
     there, same as before); non-ASCII strings now produce their real
     multi-byte UTF-8 encoding instead of a truncated codepoint.

     Returns the byte list whose UTF-8 decoding reproduces s — see
     `lemma_bytes_to_string_of_bytes_of_string`.
   -------------------------------------------------------------------- *)

let bytes_of_string (s : string) : Tot bytes =
  List.Tot.map byte_of_int (Spec.utf8_bytes s)

(* --------------------------------------------------------------------
   byte_to_spec_byte
     Bridges RDF.Bytes.byte (a refined FStar.Char.char) to
     Parser.FastString.Spec.byte (a refined nat) so bytes can be handed
     to the Spec decoder. Both refinements assert the identical fact
     (0 <= n < 256) over the same underlying int, so this is a
     same-value re-typing, not a conversion.
   -------------------------------------------------------------------- *)

let byte_to_spec_byte (b : byte) : Spec.byte =
  int_of_byte b

(* --------------------------------------------------------------------
   bytes_to_string bs
     The UTF-8 DECODING of bs (issue #445): re-typed to Spec.byte via
     byte_to_spec_byte, decoded codepoint-by-codepoint with
     `Parser.FastString.Spec.utf8_decode_all`, then reassembled into a
     string. Malformed input (bytes that did not come from
     `bytes_of_string`) decodes permissively per Spec's own policy
     (invalid sequences become U+FFFD) rather than failing — this
     function has always been `Tot`, not `option`-returning, so it
     keeps that contract; the round-trip lemma below is what guarantees
     well-formed input never hits that branch.
   -------------------------------------------------------------------- *)

let bytes_to_string (bs : bytes) : Tot string =
  FStar.String.string_of_list (Spec.utf8_decode_all (List.Tot.map byte_to_spec_byte bs))

(* --------------------------------------------------------------------
   ROUND-TRIP PROOF (issue #445): bytes_to_string (bytes_of_string s)
   == s, for an ARBITRARY string s — no ASCII-only hypothesis. Built
   directly on Parser.FastString.Spec's own proved facts (per the task
   brief: reuse, do not re-derive):
     - lemma_int_of_byte_of_int (already above): int_of_byte re-inverts
       byte_of_int, so the RDF.Bytes <-> Spec.byte re-typing round-trips.
     - Spec.utf8_decode_all_utf8_bytes_identity: decoding a string's own
       UTF-8 encoding recovers exactly FStar.String.list_of_string s
       (proved UNCONDITIONALLY in Parser.FastString.Spec.fst, session
       2026-08-11 — the "SINGLE-DECODER ROUND TRIP" that module's own
       banner once listed as parked; it landed since).
     - FStar.String.string_of_list_of_string: the stdlib's own
       string<->codepoint-list inverse.
   -------------------------------------------------------------------- *)

(* map byte_to_spec_byte (map byte_of_int xs) == xs, for any xs already
   typed as Spec.byte. Structural induction; each cons step collapses
   via lemma_int_of_byte_of_int's SMTPat (byte_to_spec_byte (byte_of_int
   hd) unfolds to int_of_byte (byte_of_int hd), which the pattern fires
   on). *)
let rec lemma_map_byte_roundtrip (xs : list Spec.byte)
  : Lemma (ensures List.Tot.map byte_to_spec_byte (List.Tot.map byte_of_int xs) == xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> lemma_map_byte_roundtrip tl

let lemma_bytes_to_string_of_bytes_of_string (s : string)
  : Lemma (ensures bytes_to_string (bytes_of_string s) == s)
  = let spec_bytes = Spec.utf8_bytes s in
    lemma_map_byte_roundtrip spec_bytes;
    Spec.utf8_decode_all_utf8_bytes_identity s;
    FStar.String.string_of_list_of_string s

(* --------------------------------------------------------------------
   sum_lengths_acc / sum_lengths
     Total byte length of a list of strings. Used to size buffers.

     NOTE (issue #445 audit): this sums `String.length`, i.e.
     CODEPOINTS, not UTF-8 bytes — an under-count for any non-ASCII
     string. No live caller was found (grep across formal/fstar/*.fst
     at the time of the #445 fix); if a future caller sizes a byte
     buffer with this for non-ASCII data, use
     `sum_lengths_acc`-over-`bytes_of_string`'s lengths instead, or a
     dedicated UTF-8 byte-length summer. Left as-is rather than
     changed blind, since this function is out of the #445 task's
     scoped fix list and has no exercised call site to regression-test
     against.
   -------------------------------------------------------------------- *)

let rec sum_lengths_acc (acc : nat) (xs : list string)
  : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | x :: rest -> sum_lengths_acc (acc + String.length x) rest

let sum_lengths (xs : list string) : Tot nat =
  sum_lengths_acc 0 xs

(* --------------------------------------------------------------------
   Read primitives — inverse of the write_u32_le / write_u64_le /
   bytes_of_string helpers above. Used by parsers (parse_dict,
   parse_presence, parse_offsets, parse_compound_presence) for the
   round-trip witness pattern: parse (serialize x) == Some x.

   All read primitives are total and pure. Each peels its consumed
   bytes off the FRONT of the input and returns the unread suffix
   alongside the parsed value. Returning [None] means the input was
   shorter than the requested field.
   -------------------------------------------------------------------- *)

let parse_u32_le (bs : bytes) : Tot (option (nat & bytes)) =
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest ->
    let v0 : nat = int_of_byte b0 in
    let v1 : nat = (int_of_byte b1) `op_Multiply` 256 in
    let v2 : nat = (int_of_byte b2) `op_Multiply` 65536 in
    let v3 : nat = (int_of_byte b3) `op_Multiply` 16777216 in
    let n : nat = v0 + v1 + v2 + v3 in
    Some (n, rest)
  | _ -> None

let parse_u64_le (bs : bytes) : Tot (option (nat & bytes)) =
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest ->
    let v0 : nat = int_of_byte b0 in
    let v1 : nat = (int_of_byte b1) `op_Multiply` 256 in
    let v2 : nat = (int_of_byte b2) `op_Multiply` 65536 in
    let v3 : nat = (int_of_byte b3) `op_Multiply` 16777216 in
    let v4 : nat = (int_of_byte b4) `op_Multiply` 4294967296 in
    let v5 : nat = (int_of_byte b5) `op_Multiply` 1099511627776 in
    let v6 : nat = (int_of_byte b6) `op_Multiply` 281474976710656 in
    let v7 : nat = (int_of_byte b7) `op_Multiply` 72057594037927936 in
    let n : nat = v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 in
    Some (n, rest)
  | _ -> None

let rec parse_n_bytes (n : nat) (bs : bytes)
  : Tot (option (bytes & bytes)) (decreases n) =
  if n = 0 then Some ([], bs)
  else
    match bs with
    | [] -> None
    | b :: rest ->
      match parse_n_bytes (n - 1) rest with
      | None -> None
      | Some (taken, remainder) -> Some (b :: taken, remainder)

let parse_string_of_length (n : nat) (bs : bytes)
  : Tot (option (string & bytes)) =
  match parse_n_bytes n bs with
  | None -> None
  | Some (taken, remainder) -> Some (bytes_to_string taken, remainder)

(* --- Foundation lemmas for round-trip witnesses (#252) ---------------
   Each (write, parse) pair is a left-inverse on its own preconditions.
   These are the building blocks for the higher-level
   `lemma_parse_serialize_*` round-trip lemmas in DictWriter /
   PresenceWriter / CompoundPresenceWriter / OffsetsWriter.
   -------------------------------------------------------------------- *)

(* parse_u32_le ((write_u32_le n) @ rest) == Some (n, rest)
   for n < 2^32 and any [rest].

   Proof composition:
     - List.append unfolds: write_u32_le n is exactly
       [b0; b1; b2; b3], so [b0;b1;b2;b3] @ rest = b0::b1::b2::b3::rest.
     - parse_u32_le matches that pattern and returns
       int_of_byte b0 + (int_of_byte b1)*256 + (int_of_byte b2)*65536
       + (int_of_byte b3)*16777216.
     - The SMTPat lemma_int_of_byte_of_int collapses each
       int_of_byte (byte_of_int x) back to x.
     - The arithmetic identity
         n = n%256 + (n/256 % 256)*256 + (n/65536 % 256)*65536
             + (n/16777216 % 256)*16777216
       for n < 2^32 is a standard SMT/Z3 fact under the
       `op_Multiply` interpretation. *)
let lemma_parse_write_u32_le_inverse
  (n : nat{n < 4294967296}) (rest : bytes)
  : Lemma (ensures parse_u32_le (FStar.List.Tot.append (write_u32_le n) rest)
                   == Some (n, rest))
  = ()

(* --- u64_le inverse: decomposition proof (#252 closed) -------------

   The straight-line analogue to lemma_parse_write_u32_le_inverse stalls
   in z3 4.13.3 (a quantifier-matching loop on the 8-term polynomial
   identity n == sum_i b_i * 256^i). The decomposition strategy below
   sidesteps that pathology: we show
       write_u64_le n == write_u32_le (n%2^32) @ write_u32_le (n/2^32)
   via byte-by-byte equality, then compose two applications of the u32
   inverse lemma. SMT only ever sees 4-byte arithmetic.

   Foundation lemmas from FStar.Math.Lemmas:
     - modulo_modulo_lemma         : (a % (b*c)) % b = a % b
     - modulo_division_lemma       : (a % (b*c)) / b = (a/b) % c
     - division_multiplication_lemma : a / (b*c) = (a/b)/c
     - lemma_div_mod               : n = (n/b)*b + (n%b)

   The 8 per-byte equalities chain these into the decomposition. Full
   proof outline + war stories in
   docs/designissues/2026-05-10-issue-252-u64-lemma-proof-sketch.md. *)

(* LO half: bytes 0..3 of write_u64_le n equal bytes 0..3 of
   write_u32_le (n%2^32). *)

let lemma_lo_byte0 (n : nat{n < 18446744073709551616})
  : Lemma (ensures (n % 4294967296) % 256 == n % 256)
  = FStar.Math.Lemmas.modulo_modulo_lemma n 256 16777216

let lemma_lo_byte1 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n % 4294967296) / 256) % 256 == (n / 256) % 256)
  = FStar.Math.Lemmas.modulo_division_lemma n 256 16777216;
    FStar.Math.Lemmas.modulo_modulo_lemma (n / 256) 256 65536

let lemma_lo_byte2 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n % 4294967296) / 65536) % 256 == (n / 65536) % 256)
  = FStar.Math.Lemmas.modulo_division_lemma n 65536 65536;
    FStar.Math.Lemmas.modulo_modulo_lemma (n / 65536) 256 256

let lemma_lo_byte3 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n % 4294967296) / 16777216) % 256 == (n / 16777216) % 256)
  = FStar.Math.Lemmas.modulo_division_lemma n 16777216 256

(* HI half: bytes 4..7 of write_u64_le n equal bytes 0..3 of
   write_u32_le (n/2^32). hi_byte0 is reflexive after substitution. *)

let lemma_hi_byte1 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n / 4294967296) / 256) % 256 == (n / 1099511627776) % 256)
  = FStar.Math.Lemmas.division_multiplication_lemma n 4294967296 256

let lemma_hi_byte2 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n / 4294967296) / 65536) % 256 == (n / 281474976710656) % 256)
  = FStar.Math.Lemmas.division_multiplication_lemma n 4294967296 65536

let lemma_hi_byte3 (n : nat{n < 18446744073709551616})
  : Lemma (ensures ((n / 4294967296) / 16777216) % 256 == (n / 72057594037927936) % 256)
  = FStar.Math.Lemmas.division_multiplication_lemma n 4294967296 16777216

(* Decomposition: write_u64_le n == write_u32_le lo @ write_u32_le hi
   where lo = n%2^32, hi = n/2^32. The seven byte-equalities above
   give SMT enough to discharge cons-list equality byte-by-byte. *)
let lemma_write_u64_le_decompose (n : nat{n < 18446744073709551616})
  : Lemma (requires True)
          (ensures (
            let lo : nat = n % 4294967296 in
            let hi : nat = n / 4294967296 in
            lo < 4294967296 /\ hi < 4294967296 /\
            write_u64_le n == FStar.List.Tot.append (write_u32_le lo) (write_u32_le hi)))
  = lemma_lo_byte0 n;
    lemma_lo_byte1 n;
    lemma_lo_byte2 n;
    lemma_lo_byte3 n;
    lemma_hi_byte1 n;
    lemma_hi_byte2 n;
    lemma_hi_byte3 n

(* Bridge: parsing 8 bytes as u64 = parsing first 4 as u32 + parsing
   next 4 as u32 scaled by 2^32. Pure pattern-matching; closes in ms. *)
let lemma_parse_u64_decompose
  (b0 b1 b2 b3 b4 b5 b6 b7 : byte) (rest : bytes)
  : Lemma (ensures (
      match parse_u32_le [b0; b1; b2; b3] with
      | Some (lo, _) ->
        (match parse_u32_le [b4; b5; b6; b7] with
         | Some (hi, _) ->
           parse_u64_le (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest)
             == Some (lo + hi `op_Multiply` 4294967296, rest)
         | None -> False)
      | None -> False))
  = ()

(* The target lemma — composes everything. Verifies in ~9s under
   z3 4.13.3 with default rlimit. *)
let lemma_parse_write_u64_le_inverse
  (n : nat{n < 18446744073709551616}) (rest : bytes)
  : Lemma (ensures parse_u64_le (FStar.List.Tot.append (write_u64_le n) rest)
                   == Some (n, rest))
  = let lo : nat = n % 4294967296 in
    let hi : nat = n / 4294967296 in
    (* Decompose write_u64_le into the two write_u32_le slabs. *)
    lemma_write_u64_le_decompose n;
    (* Re-associate: (lo @ hi) @ rest = lo @ (hi @ rest). The right
       associativity is what parse_u64_le's pattern needs. *)
    FStar.List.Tot.Properties.append_assoc
      (write_u32_le lo) (write_u32_le hi) rest;
    (* Two applications of the u32 inverse — peel lo, then peel hi. *)
    lemma_parse_write_u32_le_inverse lo (FStar.List.Tot.append (write_u32_le hi) rest);
    lemma_parse_write_u32_le_inverse hi rest;
    (* Bridge: parse_u64_le's 8-byte sum factors as parse_u32_le-on-lo
       + parse_u32_le-on-hi * 2^32. The match-binding gives SMT byte
       witnesses to instantiate lemma_parse_u64_decompose. *)
    (match write_u32_le lo, write_u32_le hi with
     | [b0; b1; b2; b3], [b4; b5; b6; b7] ->
        lemma_parse_u64_decompose b0 b1 b2 b3 b4 b5 b6 b7 rest
     | _ -> ());
    (* Closing arithmetic: n = (n%2^32) + (n/2^32) * 2^32. *)
    FStar.Math.Lemmas.lemma_div_mod n 4294967296

(* parse_n_bytes (length bs) (bs @ rest) == Some (bs, rest)
   for any byte sequence [bs] and any tail [rest].

   Proof: structural induction on [bs].
     Base case bs = []: length [] = 0; parse_n_bytes 0 ([] @ rest) =
       parse_n_bytes 0 rest = Some ([], rest).
     Inductive case bs = b :: bs': by IH parse_n_bytes (length bs')
       (bs' @ rest) == Some (bs', rest); then parse_n_bytes (length bs)
       ((b :: bs') @ rest) = parse_n_bytes (length bs' + 1) (b :: (bs' @ rest))
       takes b and recurses. *)
let rec lemma_parse_n_bytes_inverse (bs : bytes) (rest : bytes)
  : Lemma (ensures parse_n_bytes (FStar.List.Tot.length bs)
                                  (FStar.List.Tot.append bs rest)
                   == Some (bs, rest))
          (decreases bs)
  = match bs with
    | [] -> ()
    | _ :: bs' -> lemma_parse_n_bytes_inverse bs' rest

(* parse_string_of_length (List.Tot.length (bytes_of_string s))
     (bytes_of_string s @ rest) == Some (s, rest)
   for any string [s] and any tail [rest].

   Composes lemma_parse_n_bytes_inverse (peel exactly `length bs` bytes
   back off) with lemma_bytes_to_string_of_bytes_of_string (issue #445:
   the UTF-8 round trip, replacing the pre-fix proof's appeal to
   FStar.String.string_of_list_of_string directly — bytes_of_string is
   no longer `list_of_string`, so that lemma no longer applies here on
   its own; the UTF-8 round-trip lemma composes it internally instead). *)
let lemma_parse_string_of_length_inverse (s : string) (rest : bytes)
  : Lemma (ensures
            (let bs = bytes_of_string s in
             parse_string_of_length (FStar.List.Tot.length bs)
                                    (FStar.List.Tot.append bs rest)
               == Some (s, rest)))
  = let bs = bytes_of_string s in
    lemma_parse_n_bytes_inverse bs rest;
    lemma_bytes_to_string_of_bytes_of_string s

(* --------------------------------------------------------------------
   bytes_to_hex : the write-side counterpart of the hex-string decoders
   Parquet.Footer.fst reads a COTTAS base file's footer through
   (`hex_nibble` / `byte_at_hex`). Assurance-triage wave 1, #448,
   module 1 of 5 (Parquet.Footer): the round-trip lemma tying
   RDF.CottasStore.BaseWriter's `write_field_i32` to Parquet.Footer's
   `nth_field_hex` / `decode_varint_value_hex` needs a way to turn a
   `bytes` value into the same two-uppercase-hex-chars-per-byte string
   the real I/O realisation (`experimental_ocaml_glue/
   parquet_footer_runtime.sh`'s `__mim2_hex_encode`, `Printf.sprintf
   "%02X"`) produces. Lives here (not in Parquet.Footer.fst) so the
   build-module-list order (RDF_Bytes.ml precedes Parquet_Footer.ml)
   does not need to change; the bridge lemma connecting this encoder to
   Parquet.Footer's decoders lives in RDF.CottasStore.BaseWriter.fst,
   which already depends on both.
   -------------------------------------------------------------------- *)

(* Digit 0-9 -> '0'-'9' (48-57), digit 10-15 -> 'A'-'F' (65-70) --
   exactly the two branches `Parquet.Footer.hex_nibble` accepts (it
   also accepts lowercase 'a'-'f', but the real OCaml encoder emits
   uppercase, so this matches byte-for-byte, not just decodably). *)
let hex_digit_char (n : nat{n < 16}) : Tot FStar.Char.char =
  if n < 10 then FStar.Char.char_of_int (n + 48)
  else FStar.Char.char_of_int (n - 10 + 65)

let byte_to_hex (b : byte) : Tot string =
  let n = int_of_byte b in
  FStar.String.string_of_list [hex_digit_char (n / 16); hex_digit_char (n % 16)]

let rec bytes_to_hex (bs : bytes) : Tot string (decreases bs) =
  match bs with
  | [] -> ""
  | b :: tl -> Prims.op_Hat (byte_to_hex b) (bytes_to_hex tl)
