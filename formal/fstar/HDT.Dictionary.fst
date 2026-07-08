module HDT.Dictionary

// HDT (Header-Dictionary-Triples) Plain Front Coding (PFC) dictionary
// decoder — stage 2 of the program plan in
// docs/designissues/2026-07-06-hdt-program-plan.md. Builds on stage 1
// (HDT.Container.fst, container skeleton + section boundaries) which
// this module never modifies: HDT.Container is already registered in
// the build, and every function here is additive.
//
// Scope of this module (stage 2):
//   - CRC8 (poly 0x07, init 0x00, unreflected, MSB-first) and CRC32C
//     Castagnoli (poly 0x1EDC6F41, reflected form 0x82F63B78, init
//     0xFFFFFFFF, final xor 0xFFFFFFFF) over dictionary payload bytes
//     — the two flavours the container-level CRC16 (stage 1) does not
//     cover, since stage 1 only validates control-information blocks.
//     Both were cross-checked bit-for-bit against real fixture bytes
//     (third_party/testing/hdt/) before being written here: the PFC
//     preamble CRC8, the log-array preamble CRC8, the log-array data
//     CRC32C, and the packed-string-block CRC32C all match hdt-cpp's
//     stored values on both vendored fixtures.
//   - Log-array integer unpacking (log-width packed integers,
//     little-endian bit order within the byte stream — verified
//     against real block-start arrays, see the module's own
//     regression pins via bin/hdt-probe/check.sh).
//   - PFC block decode: first string of a block stored whole (NUL
//     terminated), subsequent strings as
//     `vbyte(common-prefix-length) suffix NUL`. Blocks start every
//     `blocksize` strings; the block-start log-array has
//     `ceil(numstrings/blocksize) + 1` entries — one per block plus a
//     trailing sentinel equal to the total packed-byte count (cross-
//     checked against fixture bytes: a 1-string, blocksize-16 section
//     stores 2 entries `[0; packed_bytes]`; a 134-string section
//     stores 10 entries for 9 blocks).
//   - Both access patterns the plan calls for: `decode_section` (full
//     dump, for testing) and `pfc_extract`/`pfc_locate` (single-ID
//     lookup / reverse lookup by binary search over block-head
//     strings, for the real API).
//   - The four-section ID space composition (shared/subjects/
//     predicates/objects) per the HDT convention: shared-section IDs
//     1..Nshared serve both the subject and object ID spaces;
//     subject IDs Nshared+1.. come from the subjects section (offset
//     by Nshared); object IDs Nshared+1.. come from the objects
//     section (offset by Nshared); predicate IDs are a section of
//     their own (predicates never participate in the shared space).
//   - Dictionary-string -> `rdf_term` mapping: a dictionary string
//     with a `_:` prefix is a blank node, a `"`-prefixed string is an
//     N-Triples-syntax literal (quote + escaped lexical form +
//     optional `@lang` or `^^<iri>` — exactly the grammar
//     `Parser.NTriples.parse_literal` already accepts), anything else
//     is a plain (unbracketed) IRI. Reuses `Parser.NTriples.parse_bnode`
//     / `parse_literal` and `RDF.Graph.Executable.is_iri` rather than
//     re-deriving the grammar — pinned against both fixtures via
//     bin/hdt-probe/check.sh (every decoded dictionary string maps to
//     a term, and the term set matches the fixture's source .nt file
//     as parsed by the project's own verified `Parser.NTriples`).
//
// Non-ASCII dictionary bytes are untested: both vendored fixtures are
// pure ASCII in every dictionary section (checked byte-by-byte during
// scoping), so this module inherits stage 1's byte-to-`FStar.Char`
// convention (`HDT.Container.bytes_to_string`) without exercising its
// behaviour above 0x7F. Flag if a future fixture needs it.
//
// I/O boundary: unchanged from stage 1 — no new assume val, no new
// OCaml glue. Every byte access goes through
// `HDT.Container.hex_byte` over the same hex-encoded whole-file
// string stage 1 already reads via `Parquet.Footer`'s generic
// byte-range reader.

open FStar.Mul
open FStar.List.Tot
open RDF.Graph.Executable
open Parser.Combinators
open Parser.NTriples

module HC  = HDT.Container
module NQ  = RDF.NQuads.Serialize

// ---------------------------------------------------------------------------
// CRC8: poly 0x07, init 0x00, unreflected (MSB-first). Used for every
// PFC-section preamble and every log-array preamble. Values are kept
// as plain naturals with the mod/div/mul identities (logand 0xFF ==
// mod 256, logand 0x80 <> 0 == (c/128) mod 2 = 1, shift_left == *2)
// and XOR via HC.nat_xor, so this extracts to js_of_ocaml-friendly
// integer arithmetic instead of the unrealised stdint Uint32
// externals that abort the in-browser HDT reader.
// ---------------------------------------------------------------------------

let crc8_step (c:nat) : nat =
  if (c / 128) % 2 = 1
  then (HC.nat_xor (c * 2) 0x07 32) % 256
  else (c * 2) % 256

let crc8_byte (crc:nat) (b:nat{b < 256}) : nat =
  let c0 = HC.nat_xor crc b 32 in
  crc8_step (crc8_step (crc8_step (crc8_step
    (crc8_step (crc8_step (crc8_step (crc8_step c0)))))))

let rec crc8_range (s:string) (pos:nat) (count:nat) (crc:nat)
  : Tot (option nat) (decreases count) =
  if count = 0 then Some crc
  else
    match HC.hex_byte s pos with
    | None -> None
    | Some b -> crc8_range s (pos + 1) (count - 1) (crc8_byte crc b)

// ---------------------------------------------------------------------------
// CRC32C (Castagnoli): poly 0x1EDC6F41, reflected form 0x82F63B78,
// init 0xFFFFFFFF, final xor 0xFFFFFFFF. Used for every log-array
// data payload and every PFC packed-string-block payload. Same
// nat-arithmetic representation as CRC8/CRC16 (shift_right == /2,
// logand ...1 == mod 2) for js_of_ocaml compatibility.
// ---------------------------------------------------------------------------

let crc32c_step (c:nat) : nat =
  if c % 2 = 1
  then HC.nat_xor (c / 2) 0x82F63B78 32
  else c / 2

let crc32c_byte (crc:nat) (b:nat{b < 256}) : nat =
  let c0 = HC.nat_xor crc b 32 in
  crc32c_step (crc32c_step (crc32c_step (crc32c_step
    (crc32c_step (crc32c_step (crc32c_step (crc32c_step c0)))))))

let rec crc32c_range (s:string) (pos:nat) (count:nat) (crc:nat)
  : Tot (option nat) (decreases count) =
  if count = 0 then Some crc
  else
    match HC.hex_byte s pos with
    | None -> None
    | Some b -> crc32c_range s (pos + 1) (count - 1) (crc32c_byte crc b)

let crc32c_of_range (s:string) (pos:nat) (count:nat) : option nat =
  match crc32c_range s pos count 0xFFFFFFFF with
  | None -> None
  | Some c -> Some (HC.nat_xor c 0xFFFFFFFF 32)

// ---------------------------------------------------------------------------
// Small readers for stored CRC values.
// ---------------------------------------------------------------------------

let read_u8 (s:string) (pos:nat) : option nat =
  match HC.hex_byte s pos with
  | None -> None
  | Some b -> Some (b <: nat)

let read_u32_le (s:string) (pos:nat) : option nat =
  match HC.hex_byte s pos, HC.hex_byte s (pos + 1),
        HC.hex_byte s (pos + 2), HC.hex_byte s (pos + 3) with
  | Some b0, Some b1, Some b2, Some b3 ->
    Some (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3)
  | _ -> None

// ---------------------------------------------------------------------------
// CRC validation over a decoded PFC section, using stage 1's
// `hdt_pfc_section` / `hdt_log_array_info` byte-offset records to
// locate every checked range without re-deriving them.
// ---------------------------------------------------------------------------

// Saturating subtraction: every offset computed below is structurally
// non-negative (byte ranges only ever grow), but that fact isn't
// visible to the type-checker from the plain `nat` field types alone
// — saturate instead of asking Z3 to re-derive container invariants.
let nat_sub (a:nat) (b:nat) : nat = if a >= b then a - b else 0

let la_preamble_len (la:HC.hdt_log_array_info) : nat =
  nat_sub (nat_sub la.HC.la_data_start 1) la.HC.la_start

let la_preamble_crc8_pos (la:HC.hdt_log_array_info) : nat =
  nat_sub la.HC.la_data_start 1

let la_crc32_pos (la:HC.hdt_log_array_info) : nat =
  nat_sub la.HC.la_end 4

let la_preamble_crc8_ok (s:string) (la:HC.hdt_log_array_info) : bool =
  match crc8_range s la.HC.la_start (la_preamble_len la) 0,
        read_u8 s (la_preamble_crc8_pos la) with
  | Some c, Some stored -> c = stored
  | _, _ -> false

let la_data_crc32_ok (s:string) (la:HC.hdt_log_array_info) : bool =
  match crc32c_of_range s la.HC.la_data_start la.HC.la_data_bytes,
        read_u32_le s (la_crc32_pos la) with
  | Some c, Some stored -> c = stored
  | _, _ -> false

let pfc_preamble_len (sec:HC.hdt_pfc_section) : nat =
  nat_sub (nat_sub sec.HC.pfc_blocks.HC.la_start 1) sec.HC.pfc_start

let pfc_preamble_crc8_pos (sec:HC.hdt_pfc_section) : nat =
  nat_sub sec.HC.pfc_blocks.HC.la_start 1

let pfc_preamble_crc8_ok (s:string) (sec:HC.hdt_pfc_section) : bool =
  match crc8_range s sec.HC.pfc_start (pfc_preamble_len sec) 0,
        read_u8 s (pfc_preamble_crc8_pos sec) with
  | Some c, Some stored -> c = stored
  | _, _ -> false

let pfc_packed_crc32_ok (s:string) (sec:HC.hdt_pfc_section) : bool =
  match crc32c_of_range s sec.HC.pfc_packed_start sec.HC.pfc_packed_bytes,
        read_u32_le s (nat_sub sec.HC.pfc_end 4) with
  | Some c, Some stored -> c = stored
  | _, _ -> false

// All four CRC checks a PFC section carries: its own preamble (CRC8),
// its block-start log-array's preamble (CRC8) and data (CRC32C), and
// its packed string bytes (CRC32C).
let pfc_section_crc_ok (s:string) (sec:HC.hdt_pfc_section) : bool =
  pfc_preamble_crc8_ok s sec &&
  la_preamble_crc8_ok s sec.HC.pfc_blocks &&
  la_data_crc32_ok s sec.HC.pfc_blocks &&
  pfc_packed_crc32_ok s sec

// ---------------------------------------------------------------------------
// Log-array integer unpacking: entry `idx` is `numbits` bits starting
// at global bit offset `idx * numbits` within the data byte range,
// little-endian bit order (bit 0 = LSB of the first data byte) —
// verified against real fixture block-start arrays during scoping.
// ---------------------------------------------------------------------------

let bit_divisor (b:nat{b < 8}) : pos =
  if b = 0 then 1
  else if b = 1 then 2
  else if b = 2 then 4
  else if b = 3 then 8
  else if b = 4 then 16
  else if b = 5 then 32
  else if b = 6 then 64
  else 128

let rec la_bits_acc (s:string) (data_start:nat) (bitpos:nat) (nbits:nat)
  (mult:pos) (acc:nat)
  : Tot (option nat) (decreases nbits) =
  if nbits = 0 then Some acc
  else
    let byte_idx = data_start + bitpos / 8 in
    let shift = bitpos % 8 in
    match HC.hex_byte s byte_idx with
    | None -> None
    | Some b ->
      let bitval = (b / bit_divisor shift) % 2 in
      la_bits_acc s data_start (bitpos + 1) (nbits - 1) (mult * 2)
        (acc + bitval * mult)

// Entry `idx` (0-based) of a log-array, or None past end of data.
let la_entry (s:string) (la:HC.hdt_log_array_info) (idx:nat) : option nat =
  la_bits_acc s la.HC.la_data_start (idx * la.HC.la_numbits) la.HC.la_numbits 1 0

// Number of PFC blocks: the block-start log-array carries one entry
// per block plus a trailing sentinel (= total packed-byte count).
let hdt_pfc_num_blocks (sec:HC.hdt_pfc_section) : nat =
  if sec.HC.pfc_blocks.HC.la_numentries = 0 then 0
  else sec.HC.pfc_blocks.HC.la_numentries - 1

// Absolute byte offset (into the hex-encoded file) of PFC block `b`.
let pfc_block_abs_start (s:string) (sec:HC.hdt_pfc_section) (b:nat) : option nat =
  match la_entry s sec.HC.pfc_blocks b with
  | None -> None
  | Some rel -> Some (sec.HC.pfc_packed_start + rel)

// ---------------------------------------------------------------------------
// Single-string decode primitives.
// ---------------------------------------------------------------------------

// The first (whole, NUL-terminated) string of a block.
let pfc_read_first (s:string) (pos:nat) : option (string & nat) =
  match HC.scan_nul s pos (String.length s) with
  | None -> None
  | Some nul_pos ->
    match HC.bytes_to_string s pos (nul_pos - pos) with
    | None -> None
    | Some str -> Some (str, nul_pos + 1)

// A front-coded suffix entry: vbyte(common-prefix-length) suffix NUL.
let pfc_read_suffix (s:string) (pos:nat) (prev:string) : option (string & nat) =
  match HC.vbyte_decode s pos with
  | None -> None
  | Some (plen, p1) ->
    if plen > String.length prev then None
    else
      match HC.scan_nul s p1 (String.length s) with
      | None -> None
      | Some nul_pos ->
        match HC.bytes_to_string s p1 (nul_pos - p1) with
        | None -> None
        | Some suffix ->
          let prefix = FStar.String.sub prev 0 plen in
          Some (prefix ^ suffix, nul_pos + 1)

// Walk `remaining` suffix entries starting at `pos` (with `prev` the
// most recently decoded string), returning the LAST one decoded.
let rec pfc_walk_suffixes (s:string) (at:nat) (prev:string) (remaining:pos)
  : Tot (option string) (decreases remaining) =
  match pfc_read_suffix s at prev with
  | None -> None
  | Some (str, at') ->
    if remaining = 1 then Some str
    else pfc_walk_suffixes s at' str (remaining - 1)

// ---------------------------------------------------------------------------
// Whole-block decode (first string + up to blocksize-1 suffixes).
// ---------------------------------------------------------------------------

let rec decode_block_acc (s:string) (pos:nat) (prev:string) (remaining:nat)
  (acc:list string)
  : Tot (option (list string)) (decreases remaining) =
  if remaining = 0 then Some (List.Tot.rev acc)
  else
    match pfc_read_suffix s pos prev with
    | None -> None
    | Some (str, pos') -> decode_block_acc s pos' str (remaining - 1) (str :: acc)

// Decode `count` strings (>= 1) of a single block starting at its
// absolute byte offset.
let decode_block (s:string) (block_start:nat) (count:nat) : option (list string) =
  if count = 0 then None
  else
    match pfc_read_first s block_start with
    | None -> None
    | Some (first, pos1) -> decode_block_acc s pos1 first (count - 1) [first]

// ---------------------------------------------------------------------------
// Full-section decode (dump every string in ID order — used for
// testing; `pfc_extract`/`pfc_locate` below are the real lookup API).
// ---------------------------------------------------------------------------

let block_string_count (sec:HC.hdt_pfc_section) (numblocks:nat) (b:nat) : nat =
  if b + 1 = numblocks
  then nat_sub sec.HC.pfc_numstrings (b * sec.HC.pfc_blocksize)
  else sec.HC.pfc_blocksize

let rec decode_section_acc (s:string) (sec:HC.hdt_pfc_section) (block_idx:nat)
  (numblocks:nat) (acc:list string)
  : Tot (option (list string)) (decreases (numblocks - block_idx)) =
  if block_idx >= numblocks then Some acc
  else
    match pfc_block_abs_start s sec block_idx with
    | None -> None
    | Some bstart ->
      let count = block_string_count sec numblocks block_idx in
      match decode_block s bstart count with
      | None -> None
      | Some strs -> decode_section_acc s sec (block_idx + 1) numblocks (acc @ strs)

// Dump the whole section's strings in ID order (ID `i` = 1-based
// index into this list, i.e. `List.Tot.nth` at `i - 1`).
let decode_section (s:string) (sec:HC.hdt_pfc_section) : option (list string) =
  if sec.HC.pfc_numstrings = 0 then Some []
  else decode_section_acc s sec 0 (hdt_pfc_num_blocks sec) []

// ---------------------------------------------------------------------------
// Locate-by-ID: the real single-lookup API. IDs are 1-based.
// ---------------------------------------------------------------------------

let pfc_extract (s:string) (sec:HC.hdt_pfc_section) (id:pos) : option string =
  if id > sec.HC.pfc_numstrings || sec.HC.pfc_blocksize = 0 then None
  else
    let rank = id - 1 in
    let block_idx = rank / sec.HC.pfc_blocksize in
    let offset = rank % sec.HC.pfc_blocksize in
    match pfc_block_abs_start s sec block_idx with
    | None -> None
    | Some bstart ->
      match pfc_read_first s bstart with
      | None -> None
      | Some (first, pos1) ->
        if offset = 0 then Some first
        else pfc_walk_suffixes s pos1 first offset

// ---------------------------------------------------------------------------
// Locate-by-term (reverse lookup): binary search over block-head
// strings (PFC blocks are stored in ascending lexicographic order),
// then a linear scan within the located block.
// ---------------------------------------------------------------------------

let pfc_block_first_string (s:string) (sec:HC.hdt_pfc_section) (block_idx:nat)
  : option string =
  match pfc_block_abs_start s sec block_idx with
  | None -> None
  | Some bstart ->
    match pfc_read_first s bstart with
    | None -> None
    | Some (first, _) -> Some first

let rec pfc_index_of (target:string) (strs:list string) (idx:nat)
  : Tot (option nat) (decreases strs) =
  match strs with
  | [] -> None
  | x :: rest -> if x = target then Some idx else pfc_index_of target rest (idx + 1)

// Largest block index `k` in `[lo, hi]` whose first string is <=
// `target` (predecessor search over the sorted block heads).
let rec pfc_find_block (s:string) (sec:HC.hdt_pfc_section) (target:string)
  (lo:nat) (hi:nat{hi >= lo})
  : Tot (option nat) (decreases (hi - lo)) =
  if lo >= hi then Some lo
  else
    let mid = (lo + hi + 1) / 2 in
    match pfc_block_first_string s sec mid with
    | None -> None
    | Some head ->
      if head = target || string_lt head target
      then pfc_find_block s sec target mid hi
      else pfc_find_block s sec target lo (mid - 1)

let pfc_locate (s:string) (sec:HC.hdt_pfc_section) (target:string) : option pos =
  let numblocks = hdt_pfc_num_blocks sec in
  if numblocks = 0 then None
  else
    match pfc_find_block s sec target 0 (numblocks - 1) with
    | None -> None
    | Some block_idx ->
      let count = block_string_count sec numblocks block_idx in
      match pfc_block_abs_start s sec block_idx with
      | None -> None
      | Some bstart ->
        match decode_block s bstart count with
        | None -> None
        | Some strs ->
          match pfc_index_of target strs 0 with
          | None -> None
          | Some k -> Some (block_idx * sec.HC.pfc_blocksize + k + 1)

// ---------------------------------------------------------------------------
// Dictionary string <-> rdf_term. HDT dictionary strings are stored in
// N-Triples surface syntax except plain IRIs are unbracketed; the
// leading byte distinguishes the three cases. Reuses the verified
// N-Triples grammar (`Parser.NTriples.parse_bnode` / `parse_literal`)
// and `RDF.Graph.Executable.is_iri` rather than re-deriving it.
// ---------------------------------------------------------------------------

let hdt_term_of_string (s:string) : option rdf_term =
  let len = String.length s in
  if len = 0 then None
  else
    let c0 = String.index s 0 in
    if FStar.Char.int_of_char c0 = 0x5F && len > 1 &&
       FStar.Char.int_of_char (String.index s 1) = 0x3A
    then
      match parse_bnode s 0 with
      | ParseOk b pos -> if pos = len then Some (T_BNode b) else None
      | ParseFail _ _ -> None
    else if FStar.Char.int_of_char c0 = 0x22
    then
      match parse_literal s 0 with
      | ParseOk l pos -> if pos = len then Some (T_Literal l) else None
      | ParseFail _ _ -> None
    else if is_iri s then Some (T_IRI s)
    else None

// Inverse of `hdt_term_of_string`: the dictionary surface form of a
// term. Literals and blank nodes reuse `RDF.NQuads.Serialize`'s
// N-Triples-object serializer verbatim (same quoting/escaping rules
// the dictionary's own bytes satisfy, per `parse_literal` decoding
// them successfully); a plain IRI is unbracketed in the dictionary,
// unlike the wire-format `<iri>` that serializer produces for it.
let hdt_string_of_term (t:rdf_term) : string =
  match t with
  | T_IRI i -> i
  | _ -> NQ.nq_term_to_string t

// ---------------------------------------------------------------------------
// Four-section ID-space composition (the HDT dictionary convention):
// shared IDs 1..Nshared serve both subject and object spaces; subject
// IDs continue at Nshared+1 into the subjects section; object IDs
// continue at Nshared+1 into the objects section; predicates are a
// separate space entirely.
// ---------------------------------------------------------------------------

type hdt_role =
  | Role_Subject
  | Role_Predicate
  | Role_Object

let hdt_id_to_term (s:string) (inv:HC.hdt_inventory) (role:hdt_role) (id:pos)
  : option rdf_term =
  let nshared = inv.HC.inv_dict_shared.HC.pfc_numstrings in
  let extracted =
    match role with
    | Role_Predicate -> pfc_extract s inv.HC.inv_dict_predicates id
    | Role_Subject ->
      if id <= nshared then pfc_extract s inv.HC.inv_dict_shared id
      else pfc_extract s inv.HC.inv_dict_subjects (id - nshared)
    | Role_Object ->
      if id <= nshared then pfc_extract s inv.HC.inv_dict_shared id
      else pfc_extract s inv.HC.inv_dict_objects (id - nshared)
  in
  match extracted with
  | None -> None
  | Some str -> hdt_term_of_string str

let hdt_term_to_id (s:string) (inv:HC.hdt_inventory) (role:hdt_role) (term:rdf_term)
  : option pos =
  let dstr = hdt_string_of_term term in
  let nshared = inv.HC.inv_dict_shared.HC.pfc_numstrings in
  match role with
  | Role_Predicate -> pfc_locate s inv.HC.inv_dict_predicates dstr
  | Role_Subject ->
    (match pfc_locate s inv.HC.inv_dict_shared dstr with
     | Some id -> Some id
     | None ->
       match pfc_locate s inv.HC.inv_dict_subjects dstr with
       | None -> None
       | Some id -> Some (nshared + id))
  | Role_Object ->
    (match pfc_locate s inv.HC.inv_dict_shared dstr with
     | Some id -> Some id
     | None ->
       match pfc_locate s inv.HC.inv_dict_objects dstr with
       | None -> None
       | Some id -> Some (nshared + id))

// Highest valid ID in a role's ID space — the probe consumer's loop
// bound for a full-space round-trip check.
let hdt_role_max_id (inv:HC.hdt_inventory) (role:hdt_role) : nat =
  let nshared = inv.HC.inv_dict_shared.HC.pfc_numstrings in
  match role with
  | Role_Predicate -> inv.HC.inv_dict_predicates.HC.pfc_numstrings
  | Role_Subject -> nshared + inv.HC.inv_dict_subjects.HC.pfc_numstrings
  | Role_Object -> nshared + inv.HC.inv_dict_objects.HC.pfc_numstrings
