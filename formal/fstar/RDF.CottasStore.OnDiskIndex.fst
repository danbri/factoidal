module RDF.CottasStore.OnDiskIndex

// Vav3 (issue #100, 2026-04-26) — Persistent mmap'd companion indexes
// for the on-disk COTTAS backend.
//
// Background: today's COTTAS engine pre-warms 4 column dictionaries +
// 3 per-row-group presence Hashtbls at boot. On the parliament corpus
// (3.14M quads, 26 row groups) this is ~107 s and ~1.4 GB RSS — pure
// waste, since every byte is a deterministic function of the .cottas
// file.
//
// This module replaces that pre-warm with persistent companion files
// sibling to the .cottas:
//
//   data.cottas.s.dict       Sorted token dictionary for subjects
//   data.cottas.s.presence   Per-rg presence bitmap for subjects
//   data.cottas.p.dict       Sorted token dictionary for predicates
//   data.cottas.p.presence   Per-rg presence bitmap for predicates
//   data.cottas.o.dict       Sorted token dictionary for objects
//   data.cottas.o.presence   Per-rg presence bitmap for objects
//   data.cottas.g.dict       Sorted token dictionary for graphs
//   data.cottas.g.presence   Per-rg presence bitmap for graphs
//
// File formats (little-endian throughout):
//
//   .dict (token dictionary):
//     [ magic       : u32   ASCII 'COTD' = 0x44544f43 ]
//     [ version     : u32   layout version, currently 1 ]
//     [ num_tokens  : u32 ]
//     [ pad         : u32   alignment to 8-byte boundary ]
//     [ ids_offset  : u64   byte offset of ids[] from file start ]
//     [ tokens_offset : u64 byte offset of token_offs[] from file start ]
//     [ ids[]            : u32 * num_tokens
//                          where ids[i] = the token-id whose token_data
//                          slice sorts at ascending position i.
//                          Allows O(log num_tokens) binary search
//                          encode (token_str -> token_id). ]
//     [ token_offs[]     : u64 * (num_tokens+1)
//                          token_data byte offset of each token's start
//                          (and one trailing entry for the end of the
//                          last token) — used for both encode+decode. ]
//     [ token_data       : utf-8 bytes, no separators ]
//
//   .presence (per-rg bitmap):
//     [ magic       : u32   ASCII 'COTP' = 0x50544f43 ]
//     [ version     : u32   layout version, currently 1 ]
//     [ num_rgs     : u32 ]
//     [ num_tokens  : u32 ]
//     [ bitmap      : ceil(num_rgs * num_tokens / 8) bytes
//                     row-major: bit at position (rg*num_tokens + tok)
//                     is set iff rg contains a row with that token. ]
//
// Lookup functions (F*-pure, extracted to OCaml):
//   - companion_magic_ok : header magic + version verifier
//   - dict_decode_token  : id -> option string  (one offsets read + one byte-range read)
//   - dict_encode_token  : string -> option nat (binary search on ids[])
//   - presence_test_bit  : (rg, tok) -> bool   (one byte read + bit test)
//
// All byte-range I/O is `assume val`. Mirrors Mim2 / Bet7 phase B/C
// discipline. The companion file format itself is fully F*-specified
// here, so any reader extracts byte-identical results.

open Parquet.Footer
open FStar.Mul

// ------------------------------------------------------------------
// Magic numbers (32-bit little-endian).
// ASCII 'C', 'O', 'T', 'D' = 0x43, 0x4f, 0x54, 0x44 -> LE u32 = 0x44544f43
// ASCII 'C', 'O', 'T', 'P' = 0x43, 0x4f, 0x54, 0x50 -> LE u32 = 0x50544f43
// ------------------------------------------------------------------

let cotd_magic_u32 : nat = 0x44544f43
let cotp_magic_u32 : nat = 0x50544f43
let layout_version : nat = 1

// ------------------------------------------------------------------
// I/O primitives (assume val). The OCaml glue mmap's the companion
// file at boot and these primitives read u32/u64 little-endian or a
// byte-range from the mapping. Path is the companion-file path string;
// callers thread the path through.
//
// Discipline: the assume val layer NEVER decides what bytes mean —
// only how to read them. All semantic decisions (magic check, sort-
// edness, binary-search invariants) live in F* below.
// ------------------------------------------------------------------

assume val mmap_companion_open :
  path:string -> Tot (option nat)
  // Returns the file's byte length on success (presence of the mmap is
  // implied by the OCaml glue keeping a Bigarray.Array1.t alive keyed
  // by path). None means the file does not exist or is too small.

assume val mmap_companion_close :
  path:string -> Tot unit

assume val read_companion_u32_le :
  path:string -> offset:nat -> Tot (option nat)
  // Read 4 bytes at `offset` as little-endian unsigned 32-bit integer.
  // None if the offset+4 is out of bounds (callers should verify length
  // first). The OCaml glue reads from the mmap'd region.

assume val read_companion_u64_le :
  path:string -> offset:nat -> Tot (option nat)
  // Read 8 bytes at `offset` as little-endian unsigned 64-bit integer.

assume val read_companion_byte :
  path:string -> offset:nat -> Tot (option (b:nat { b < 256 }))
  // Read 1 byte at `offset`.

assume val read_companion_string :
  path:string -> offset:nat -> count:nat -> Tot (option string)
  // Read `count` bytes at `offset` and return as a UTF-8 string. None
  // if out of bounds.

// File existence + size only — no content interpretation.
assume val companion_file_size :
  path:string -> Tot (option nat)

// ------------------------------------------------------------------
// Header layouts (refinement-typed records). Reading them invokes the
// I/O primitives, but the *interpretation* — magic check, version
// gate — is F*-pure.
// ------------------------------------------------------------------

type dict_header = {
  dh_magic : nat;
  dh_version : nat;
  dh_num_tokens : nat;
  dh_ids_offset : nat;
  dh_tokens_offset : nat;
}

type presence_header = {
  ph_magic : nat;
  ph_version : nat;
  ph_num_rgs : nat;
  ph_num_tokens : nat;
}

// dict header layout (in bytes):
//   off  0:  magic     u32
//   off  4:  version   u32
//   off  8:  num_tokens u32
//   off 12:  pad       u32
//   off 16:  ids_offset u64
//   off 24:  tokens_offset u64
//   total header = 32 bytes
let dict_header_size : nat = 32

let read_dict_header (path : string) : Tot (option dict_header) =
  match read_companion_u32_le path 0 with
  | None -> None
  | Some magic ->
    match read_companion_u32_le path 4 with
    | None -> None
    | Some version ->
      match read_companion_u32_le path 8 with
      | None -> None
      | Some num_tokens ->
        match read_companion_u64_le path 16 with
        | None -> None
        | Some ids_offset ->
          match read_companion_u64_le path 24 with
          | None -> None
          | Some tokens_offset ->
            Some {
              dh_magic = magic;
              dh_version = version;
              dh_num_tokens = num_tokens;
              dh_ids_offset = ids_offset;
              dh_tokens_offset = tokens_offset;
            }

// presence header layout (in bytes):
//   off  0:  magic       u32
//   off  4:  version     u32
//   off  8:  num_rgs     u32
//   off 12:  num_tokens  u32
//   total header = 16 bytes
let presence_header_size : nat = 16

let read_presence_header (path : string) : Tot (option presence_header) =
  match read_companion_u32_le path 0 with
  | None -> None
  | Some magic ->
    match read_companion_u32_le path 4 with
    | None -> None
    | Some version ->
      match read_companion_u32_le path 8 with
      | None -> None
      | Some num_rgs ->
        match read_companion_u32_le path 12 with
        | None -> None
        | Some num_tokens ->
          Some {
            ph_magic = magic;
            ph_version = version;
            ph_num_rgs = num_rgs;
            ph_num_tokens = num_tokens;
          }

// Companion magic + version validators. Returns true iff the header
// declares the expected layout.
let dict_header_ok (h : dict_header) : Tot bool =
  h.dh_magic = cotd_magic_u32 && h.dh_version = layout_version

let presence_header_ok (h : presence_header) : Tot bool =
  h.ph_magic = cotp_magic_u32 && h.ph_version = layout_version

// ------------------------------------------------------------------
// dict_decode_token: id -> token string.
// One u64 read for the start offset, one u64 read for the end offset,
// then a byte-range read for the slice.
// ------------------------------------------------------------------

let dict_decode_token (path : string) (h : dict_header) (id : nat)
  : Tot (option string) =
  if id >= h.dh_num_tokens then None
  else
    let eight : nat = 8 in
    let off_pos_start : nat = h.dh_tokens_offset + eight * id in
    let off_pos_end   : nat = h.dh_tokens_offset + eight * (id + 1) in
    match read_companion_u64_le path off_pos_start with
    | None -> None
    | Some token_start ->
      match read_companion_u64_le path off_pos_end with
      | None -> None
      | Some token_end ->
        if token_end < token_start then None
        else
          let len : nat = token_end - token_start in
          read_companion_string path token_start len

// ------------------------------------------------------------------
// dict_encode_token: token string -> id (binary search).
//
// The .dict's `ids[]` array is sorted s.t. tokens[ids[i]] is
// ascending. We binary-search by reading ids[mid], then comparing the
// query token against tokens[ids[mid]]. Total: O(log num_tokens) random
// reads of a 4-byte ids cell + a token-byte-range slice.
//
// Termination: `lo + (hi - lo)` strictly decreases by at least one each
// step (hi-lo halves; we use fuel = hi-lo+1 as the explicit decreases
// witness for F*'s totality checker).
// ------------------------------------------------------------------

let read_id_at (path : string) (h : dict_header) (i : nat)
  : Tot (option nat) =
  if i >= h.dh_num_tokens then None
  else
    let four : nat = 4 in
    let pos : nat = h.dh_ids_offset + four * i in
    read_companion_u32_le path pos

// Compare query token against the token whose id is ids[mid].
// Returns: -1 if query < token-at-mid, 0 if equal, 1 if query > token.
// On any read error, returns 0 (caller treats as match candidate; if
// the actual lookup proves it isn't a match, encode returns None).
//
// We can't use FStar.String.compare directly with a (-1/0/1) result
// shape, so we implement our own three-way over the equality+lex
// helpers we have.
let compare_string (a b : string) : Tot int =
  // F* doesn't expose a built-in 3-way string comparator on Tot. We
  // approximate via prefix walk: stop at first differing char; if one
  // is a prefix of the other, the shorter is smaller.
  let la = String.length a in
  let lb = String.length b in
  let rec loop (i : nat) : Tot int (decreases (la + lb - i)) =
    if i >= la && i >= lb then 0
    else if i >= la then -1
    else if i >= lb then 1
    else
      let ca = FStar.Char.int_of_char (String.index a i) in
      let cb = FStar.Char.int_of_char (String.index b i) in
      if ca < cb then -1
      else if ca > cb then 1
      else if i + 1 > la + lb then 0  // unreachable, satisfies decreases
      else loop (i + 1) in
  if la + lb = 0 then 0 else loop 0

// Binary-search loop. `lo` and `hi` are inclusive bounds (with the
// convention that lo > hi means "not found"). Fuel = hi - lo + 1.
let rec bsearch_loop
  (path : string) (h : dict_header) (query : string)
  (lo : nat) (hi : nat) (fuel : nat)
  : Tot (option nat) (decreases fuel) =
  if fuel = 0 then None
  else if lo > hi then None
  else
    let mid : nat = lo + (hi - lo) / 2 in
    match read_id_at path h mid with
    | None -> None
    | Some id_at_mid ->
      match dict_decode_token path h id_at_mid with
      | None -> None
      | Some tok ->
        let c = compare_string query tok in
        if c = 0 then Some id_at_mid
        else if c < 0 then
          if mid = 0 then None
          else bsearch_loop path h query lo (mid - 1) (fuel - 1)
        else
          bsearch_loop path h query (mid + 1) hi (fuel - 1)

let dict_encode_token (path : string) (h : dict_header) (query : string)
  : Tot (option nat) =
  if h.dh_num_tokens = 0 then None
  else bsearch_loop path h query 0 (h.dh_num_tokens - 1) (h.dh_num_tokens + 1)

// ------------------------------------------------------------------
// presence_test_bit: (rg, tok) -> bool.
// One byte read + one bit test. The bitmap starts at offset 16
// (presence_header_size).
// ------------------------------------------------------------------

let presence_test_bit
  (path : string) (h : presence_header) (rg : nat) (tok : nat)
  : Tot bool =
  if rg >= h.ph_num_rgs || tok >= h.ph_num_tokens then false
  else
    let nt : nat = h.ph_num_tokens in
    let bit_index : nat = rg * nt + tok in
    let eight : nat = 8 in
    let byte_index : nat = bit_index / eight in
    let bit_in_byte : nat = bit_index % eight in
    let off : nat = presence_header_size + byte_index in
    match read_companion_byte path off with
    | None -> true  // safe fallback: include rg
    | Some b ->
      // Test bit `bit_in_byte` (LSB-first ordering). One of {1,2,4,8,16,32,64,128}.
      let mask : nat =
        if bit_in_byte = 0 then 1
        else if bit_in_byte = 1 then 2
        else if bit_in_byte = 2 then 4
        else if bit_in_byte = 3 then 8
        else if bit_in_byte = 4 then 16
        else if bit_in_byte = 5 then 32
        else if bit_in_byte = 6 then 64
        else 128 in
      (b / mask) % 2 = 1

// ------------------------------------------------------------------
// Companion-set boot helpers. Open all 8 (4 dicts + 4 presence) by
// path; verify each's magic + version. If any verification fails,
// the caller (OCaml glue) falls back to building the companions.
//
// The actual mmap is held in OCaml-glue Bigarray.Array1.t storage
// keyed by path; the F* side just walks the headers via the I/O
// primitives, and consults the same primitives at lookup time.
// ------------------------------------------------------------------

type companion_status = {
  cs_dict_path : string;
  cs_presence_path : string;
  cs_dict_header : option dict_header;
  cs_presence_header : option presence_header;
}

let companion_status_ok (cs : companion_status) : Tot bool =
  match cs.cs_dict_header, cs.cs_presence_header with
  | Some dh, Some ph ->
    dict_header_ok dh && presence_header_ok ph &&
    // dict.num_tokens must match presence.num_tokens for the same column
    dh.dh_num_tokens = ph.ph_num_tokens
  | _ -> false

let load_companion_status (dict_path presence_path : string)
  : Tot companion_status = {
  cs_dict_path = dict_path;
  cs_presence_path = presence_path;
  cs_dict_header = read_dict_header dict_path;
  cs_presence_header = read_presence_header presence_path;
}

// ------------------------------------------------------------------
// High-level lookups. These compose the primitives above into the
// shape the OCaml runtime needs.
// ------------------------------------------------------------------

// Encode a raw column-token string -> token-id (or None if absent).
// Used by the bound-translation layer: bound_subj_iri -> "<iri>" (raw
// token) -> id, then id passed to cottas_ondisk_search.
let companion_encode (cs : companion_status) (tok : string) : Tot (option nat) =
  match cs.cs_dict_header with
  | None -> None
  | Some dh ->
    if not (dict_header_ok dh) then None
    else dict_encode_token cs.cs_dict_path dh tok

// Decode a token-id -> raw column-token string.
let companion_decode (cs : companion_status) (id : nat) : Tot (option string) =
  match cs.cs_dict_header with
  | None -> None
  | Some dh ->
    if not (dict_header_ok dh) then None
    else dict_decode_token cs.cs_dict_path dh id

// Per-rg presence test. Yod6/Tet3's runtime helper.
let companion_rg_could_contain
  (cs : companion_status) (rg : nat) (tok_id : nat)
  : Tot bool =
  match cs.cs_presence_header with
  | None -> true   // safe fallback: include rg when no presence info
  | Some ph ->
    if not (presence_header_ok ph) then true
    else presence_test_bit cs.cs_presence_path ph rg tok_id
