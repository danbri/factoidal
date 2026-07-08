module HDT.Container

// HDT (Header-Dictionary-Triples) container reader — stage 1 of the
// program plan in docs/designissues/2026-07-06-hdt-program-plan.md.
//
// Scope of this module (stage 1): parse the container skeleton of an
// HDT v1 file as written by the reference implementation hdt-cpp
// 1.3.x — the Global control information ('$HDT' cookie, format IRI,
// properties, CRC16), the Header section (control information +
// N-Triples metadata text, decoded with the verified
// Parser.NTriples), the Dictionary control information plus the byte
// boundaries of its four Plain-Front-Coding sections (skipped by
// header arithmetic, strings NOT decoded until stage 2), and the
// Triples control information. Every control-information block's
// CRC16 is validated here, in pure F* (blocks are tens of bytes;
// bitwise reflected CRC-16/ANSI, no table). CRC8 / CRC32C guard
// section payloads this stage does not decode; they are validated in
// stages 2-3 alongside payload decoding (program plan, stage list).
//
// Naming: follows the Parquet.Footer precedent — binary container
// modules are named by format. The Parser.* namespace stays reserved
// for W3C concrete text syntaxes; Parser.BallyhooHDT remains the
// store-boundary interface until stage 4 supersedes it.
//
// I/O boundary: NO new assume val and NO new OCaml glue. File bytes
// arrive through Parquet.Footer's existing generic byte-range reader
// `parquet_read_range_hex` (path + start + count -> hex string),
// whose OCaml realisation is a whole-file byte cache with O(count)
// slicing — the path IS the region handle. The file size is not
// exposed by that boundary, so `hdt_file_size` discovers it with an
// exponential-probe + binary-search over read attempts — O(log n)
// probes. The successful probes hex-encode and memoize up to ~4x the
// file in the glue's range cache; acceptable at fixture scale, and a
// dedicated file-size assume val is the flagged stage-1.5 upgrade if
// corpus-scale HDT files make it matter.
//
// Byte-layout provenance: rdfhdt.org "HDT binary format" draft
// (03/07/2015) cross-checked against the vendored hdt-cpp-1.3.3
// sources (see third_party/testing/hdt/README.md). Where they
// disagree, hdt-cpp wins; the discrepancy list lives in the program
// plan doc.

open FStar.Mul
open FStar.List.Tot
open RDF.Graph.Executable

module PF  = Parquet.Footer

// ---------------------------------------------------------------------------
// Bitwise XOR over unbounded naturals, LSB-first, bounded by `fuel`
// bit positions. For operands below 2^fuel this is the exact bitwise
// xor. Used only by the CRC helpers below (16/32-bit operands, so
// fuel 32 is always exact). Kept in plain nat arithmetic on purpose:
// it extracts to OCaml integer ops (division/mod/mul), which the
// js_of_ocaml + zarith_stubs_js bundle realises natively — unlike
// FStar.UInt32, whose stdint externals (uint32_xor, ...) have no JS
// realisation and abort the in-browser HDT reader. See the CRC note.
// ---------------------------------------------------------------------------

let rec nat_xor (a:nat) (b:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then 0
  else
    let low = (if a % 2 = b % 2 then 0 else 1) in
    low + 2 * nat_xor (a / 2) (b / 2) (fuel - 1)

// ---------------------------------------------------------------------------
// Hex-encoded byte access. Offsets are in BYTES; the backing string
// is the hex encoding (2 chars per byte), same representation as
// Parquet.Footer.
// ---------------------------------------------------------------------------

let hex_byte (s:string) (i:nat) : option (b:nat{b < 256}) =
  if 2 * i + 1 < String.length s then PF.byte_at_hex s (2 * i)
  else None

// Total number of whole bytes representable by the hex string.
let hex_len_bytes (s:string) : nat = String.length s / 2

// ---------------------------------------------------------------------------
// CRC-16/ANSI ("ARC"): poly 0x8005 reflected (0xA001), init 0x0000,
// xorout 0x0000 — the parameters printed in hdt-cpp's crc16.h header
// and used for every control-information block. Bitwise reflected
// form; small inputs, so no table needed. Values are kept as plain
// naturals masked to 16 bits (logand 0xFFFF == mod 65536, shift_right
// == /2, logand ...1 == mod 2) so the code extracts to js_of_ocaml-
// friendly integer arithmetic rather than the unrealised stdint
// Uint32 externals.
// ---------------------------------------------------------------------------

let crc16_step (c:nat) : nat =
  if c % 2 = 1
  then nat_xor (c / 2) 0xA001 32
  else c / 2

let crc16_byte (crc:nat) (b:nat{b < 256}) : nat =
  let c0 = (nat_xor crc b 32) % 65536 in
  crc16_step (crc16_step (crc16_step (crc16_step
    (crc16_step (crc16_step (crc16_step (crc16_step c0)))))))

// CRC16 over the byte range [pos, pos+count) of hex string s.
let rec crc16_range (s:string) (pos:nat) (count:nat) (crc:nat)
  : Tot (option nat) (decreases count) =
  if count = 0 then Some crc
  else
    match hex_byte s pos with
    | None -> None
    | Some b -> crc16_range s (pos + 1) (count - 1) (crc16_byte crc b)

// ---------------------------------------------------------------------------
// VByte, HDT flavour (hdt-cpp libdcs/VByte.cpp): little-endian 7-bit
// groups; continuation bytes have the high bit CLEAR and the FINAL
// byte has the high bit SET — the inverse of the protobuf/Parquet
// varint convention. Returns (value, offset-after).
// ---------------------------------------------------------------------------

let rec vbyte_decode_acc (s:string) (pos:nat) (fuel:nat) (mult:Prims.pos) (acc:nat)
  : Tot (option (nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match hex_byte s pos with
    | None -> None
    | Some b ->
      if b >= 128 then Some (acc + (b - 128) * mult, pos + 1)
      else vbyte_decode_acc s (pos + 1) (fuel - 1) (mult * 128) (acc + b * mult)

// 10 groups cover any u64.
let vbyte_decode (s:string) (pos:nat) : option (nat & nat) =
  vbyte_decode_acc s pos 10 1 0

// ---------------------------------------------------------------------------
// Small string utilities over decoded bytes.
// ---------------------------------------------------------------------------

// Offset of the next NUL byte at or after pos (fuel-bounded scan).
let rec scan_nul (s:string) (pos:nat) (fuel:nat)
  : Tot (option (n:nat{n >= pos})) (decreases fuel) =
  if fuel = 0 then None
  else
    match hex_byte s pos with
    | None -> None
    | Some 0 -> Some pos
    | Some _ ->
      (match scan_nul s (pos + 1) (fuel - 1) with
       | None -> None
       | Some n -> Some n)

// Decode the byte range [pos, pos+count) as a string, one char per
// byte (Latin-1-style; ASCII in practice for control blocks, and the
// header N-Triples text carries UTF-8 bytes exactly as the file-based
// parser path does).
let rec bytes_to_string_acc (s:string) (pos:nat) (count:nat)
  (acc:list FStar.Char.char)
  : Tot (option string) (decreases count) =
  if count = 0 then Some (FStar.String.string_of_list (List.Tot.rev acc))
  else
    match hex_byte s pos with
    | None -> None
    | Some b ->
      bytes_to_string_acc s (pos + 1) (count - 1)
        (Parser.NTriples.safe_char_of_int b :: acc)

let bytes_to_string (s:string) (pos:nat) (count:nat) : option string =
  bytes_to_string_acc s pos count []

// Split a decoded properties string "k1=v1;k2=v2;" into pairs.
let rec split_on_semi (cs:list FStar.Char.char) (cur:list FStar.Char.char)
  : Tot (list (list FStar.Char.char)) (decreases cs) =
  match cs with
  | [] -> (match cur with | [] -> [] | _ -> [List.Tot.rev cur])
  | c :: rest ->
    if FStar.Char.int_of_char c = 59 // ';'
    then (List.Tot.rev cur) :: split_on_semi rest []
    else split_on_semi rest (c :: cur)

let rec split_on_eq (cs:list FStar.Char.char) (acc:list FStar.Char.char)
  : Tot (list FStar.Char.char & list FStar.Char.char) (decreases cs) =
  match cs with
  | [] -> (List.Tot.rev acc, [])
  | c :: rest ->
    if FStar.Char.int_of_char c = 61 // '='
    then (List.Tot.rev acc, rest)
    else split_on_eq rest (c :: acc)

let kv_of_chars (p:list FStar.Char.char) : (string & string) =
  let (k, v) = split_on_eq p [] in
  (FStar.String.string_of_list k, FStar.String.string_of_list v)

let parse_properties (raw:string) : list (string & string) =
  List.Tot.map kv_of_chars (split_on_semi (FStar.String.list_of_string raw) [])

let rec prop_lookup (props:list (string & string)) (key:string)
  : Tot (option string) (decreases props) =
  match props with
  | [] -> None
  | (k, v) :: rest -> if k = key then Some v else prop_lookup rest key

let rec nat_of_digits (cs:list FStar.Char.char) (acc:nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> Some acc
  | c :: rest ->
    let d = FStar.Char.int_of_char c in
    if d >= 48 && d <= 57 then nat_of_digits rest (acc * 10 + (d - 48))
    else None

let nat_of_string (s:string) : option nat =
  match FStar.String.list_of_string s with
  | [] -> None
  | cs -> nat_of_digits cs 0

let prop_nat (props:list (string & string)) (key:string) : option nat =
  match prop_lookup props key with
  | None -> None
  | Some v -> nat_of_string v

// ---------------------------------------------------------------------------
// Control information blocks.
//
//   '$HDT'(4) type(1) format NUL properties NUL crc16(2 LE)
//
// with the CRC16 computed over cookie..second-NUL inclusive
// (ControlInformation::save/load in hdt-cpp).
// ---------------------------------------------------------------------------

type hdt_ci_type =
  | CI_Unknown
  | CI_Global
  | CI_Header
  | CI_Dictionary
  | CI_Triples
  | CI_Index

let ci_type_of_byte (b:nat) : hdt_ci_type =
  if b = 1 then CI_Global
  else if b = 2 then CI_Header
  else if b = 3 then CI_Dictionary
  else if b = 4 then CI_Triples
  else if b = 5 then CI_Index
  else CI_Unknown

type hdt_control_info = {
  hci_start : nat;                       // byte offset of '$HDT'
  hci_type : hdt_ci_type;
  hci_format : string;                   // format URI / name (no NUL)
  hci_props : list (string & string);
  hci_props_raw : string;
  hci_crc_stored : nat;
  hci_crc_computed : nat;
  hci_crc_ok : bool;
  hci_end : nat;                         // offset just past the CRC16
}

let parse_control_info (s:string) (pos:nat) : option hdt_control_info =
  match hex_byte s pos, hex_byte s (pos + 1),
        hex_byte s (pos + 2), hex_byte s (pos + 3) with
  | Some b0, Some b1, Some b2, Some b3 ->
    if not (b0 = 0x24 && b1 = 0x48 && b2 = 0x44 && b3 = 0x54) // "$HDT"
    then None
    else
    (match hex_byte s (pos + 4) with
     | None -> None
     | Some ty ->
       (match scan_nul s (pos + 5) (String.length s) with
        | None -> None
        | Some fmt_nul ->
          (match scan_nul s (fmt_nul + 1) (String.length s) with
           | None -> None
           | Some props_nul ->
             (match bytes_to_string s (pos + 5) (fmt_nul - (pos + 5)),
                    bytes_to_string s (fmt_nul + 1) (props_nul - (fmt_nul + 1)) with
              | Some fmt, Some raw ->
                (match crc16_range s pos (props_nul + 1 - pos) 0 with
                 | None -> None
                 | Some crc ->
                   (match hex_byte s (props_nul + 1), hex_byte s (props_nul + 2) with
                    | Some lo, Some hi ->
                      let stored : nat = lo + 256 * hi in
                      Some {
                        hci_start = pos;
                        hci_type = ci_type_of_byte ty;
                        hci_format = fmt;
                        hci_props = parse_properties raw;
                        hci_props_raw = raw;
                        hci_crc_stored = stored;
                        hci_crc_computed = crc;
                        hci_crc_ok = (crc = stored);
                        hci_end = props_nul + 3;
                      }
                    | _, _ -> None))
              | _, _ -> None))))
  | _, _, _, _ -> None

// ---------------------------------------------------------------------------
// Section skippers — stage 1 computes byte boundaries only, from the
// self-describing preambles. Payload decode is stage 2/3.
//
// Log-array (hdt-cpp LogSequence2::save):
//   type(1)=1  numbits(1)  vbyte(numentries)  crc8(1)
//   data[ceil(numbits*numentries/8)]  crc32(4)
//
// Bitmap (hdt-cpp BitSequence375::save):
//   type(1)=1  vbyte(numbits)  crc8(1)
//   data[bits=0 ? 1 : ceil(numbits/8)]  crc32(4)
//   -- note the 1-byte floor for the empty bitmap.
//
// PFC dictionary section (hdt-cpp CSD_PFC::save; type byte 2 = PFC —
// ONE byte, not the spec page's u32):
//   type(1)=2  vbyte(numstrings)  vbyte(packed-bytes)  vbyte(blocksize)
//   crc8(1)  log-array(block starts)  packed-blocks[packed-bytes]  crc32(4)
// ---------------------------------------------------------------------------

type hdt_log_array_info = {
  la_start : nat;
  la_numbits : nat;
  la_numentries : nat;
  la_data_start : nat;
  la_data_bytes : nat;
  la_end : nat;
}

let parse_log_array_info (s:string) (pos:nat) : option hdt_log_array_info =
  match hex_byte s pos with
  | Some 1 ->
    (match hex_byte s (pos + 1) with
     | None -> None
     | Some numbits ->
       (match vbyte_decode s (pos + 2) with
        | None -> None
        | Some (numentries, p_crc8) ->
          let data_start = p_crc8 + 1 in
          let data_bytes = (numbits * numentries + 7) / 8 in
          Some {
            la_start = pos;
            la_numbits = numbits;
            la_numentries = numentries;
            la_data_start = data_start;
            la_data_bytes = data_bytes;
            la_end = data_start + data_bytes + 4;
          }))
  | _ -> None

type hdt_bitmap_info = {
  bm_start : nat;
  bm_numbits : nat;
  bm_data_start : nat;
  bm_data_bytes : nat;
  bm_end : nat;
}

let parse_bitmap_info (s:string) (pos:nat) : option hdt_bitmap_info =
  match hex_byte s pos with
  | Some 1 ->
    (match vbyte_decode s (pos + 1) with
     | None -> None
     | Some (numbits, p_crc8) ->
       let data_start = p_crc8 + 1 in
       let data_bytes = if numbits = 0 then 1 else ((numbits - 1) / 8) + 1 in
       Some {
         bm_start = pos;
         bm_numbits = numbits;
         bm_data_start = data_start;
         bm_data_bytes = data_bytes;
         bm_end = data_start + data_bytes + 4;
       })
  | _ -> None

type hdt_pfc_section = {
  pfc_start : nat;
  pfc_type : nat;                        // 2 = Plain Front Coding
  pfc_numstrings : nat;
  pfc_packed_bytes : nat;
  pfc_blocksize : nat;
  pfc_blocks : hdt_log_array_info;       // block-start offsets
  pfc_packed_start : nat;
  pfc_end : nat;
}

let parse_pfc_section (s:string) (pos:nat) : option hdt_pfc_section =
  match hex_byte s pos with
  | Some 2 ->
    (match vbyte_decode s (pos + 1) with
     | None -> None
     | Some (numstrings, p1) ->
       (match vbyte_decode s p1 with
        | None -> None
        | Some (packed_bytes, p2) ->
          (match vbyte_decode s p2 with
           | None -> None
           | Some (blocksize, p3) ->
             // p3 points at the CRC8 of the preamble; blocks follow it.
             (match parse_log_array_info s (p3 + 1) with
              | None -> None
              | Some la ->
                Some {
                  pfc_start = pos;
                  pfc_type = 2;
                  pfc_numstrings = numstrings;
                  pfc_packed_bytes = packed_bytes;
                  pfc_blocksize = blocksize;
                  pfc_blocks = la;
                  pfc_packed_start = la.la_end;
                  pfc_end = la.la_end + packed_bytes + 4;
                }))))
  | _ -> None

// ---------------------------------------------------------------------------
// Whole-container inventory.
// ---------------------------------------------------------------------------

type hdt_inventory = {
  inv_global : hdt_control_info;
  inv_header_ci : hdt_control_info;
  inv_header_data_start : nat;
  inv_header_data_len : nat;
  inv_dict_ci : hdt_control_info;
  inv_dict_shared : hdt_pfc_section;
  inv_dict_subjects : hdt_pfc_section;
  inv_dict_predicates : hdt_pfc_section;
  inv_dict_objects : hdt_pfc_section;
  inv_triples_ci : hdt_control_info;
  inv_triples_data_start : nat;
}

// Parse the container skeleton from offset 0 of a hex-encoded HDT
// file. Loud None on: wrong cookie, wrong section type byte, any CI
// CRC16 mismatch, missing header `length` property, non-PFC
// dictionary section type (stage 2 will widen), or truncation.
let hdt_parse_inventory_hex (s:string) : option hdt_inventory =
  match parse_control_info s 0 with
  | None -> None
  | Some g ->
    if not (CI_Global? g.hci_type && g.hci_crc_ok) then None
    else
      (match parse_control_info s g.hci_end with
       | None -> None
       | Some h ->
         if not (CI_Header? h.hci_type && h.hci_crc_ok) then None
         else
           (match prop_nat h.hci_props "length" with
            | None -> None
            | Some hlen ->
              let hdata = h.hci_end in
              (match parse_control_info s (hdata + hlen) with
               | None -> None
               | Some d ->
                 if not (CI_Dictionary? d.hci_type && d.hci_crc_ok) then None
                 else
                   (match parse_pfc_section s d.hci_end with
                    | None -> None
                    | Some sec_sh ->
                      (match parse_pfc_section s sec_sh.pfc_end with
                       | None -> None
                       | Some sec_su ->
                         (match parse_pfc_section s sec_su.pfc_end with
                          | None -> None
                          | Some sec_pr ->
                            (match parse_pfc_section s sec_pr.pfc_end with
                             | None -> None
                             | Some sec_ob ->
                               (match parse_control_info s sec_ob.pfc_end with
                                | None -> None
                                | Some t ->
                                  if not (CI_Triples? t.hci_type && t.hci_crc_ok)
                                  then None
                                  else
                                    Some {
                                      inv_global = g;
                                      inv_header_ci = h;
                                      inv_header_data_start = hdata;
                                      inv_header_data_len = hlen;
                                      inv_dict_ci = d;
                                      inv_dict_shared = sec_sh;
                                      inv_dict_subjects = sec_su;
                                      inv_dict_predicates = sec_pr;
                                      inv_dict_objects = sec_ob;
                                      inv_triples_ci = t;
                                      inv_triples_data_start = t.hci_end;
                                    }))))))))

// Header metadata, decoded as N-Triples through the verified parser.
let hdt_header_text_hex (s:string) (inv:hdt_inventory) : option string =
  bytes_to_string s inv.inv_header_data_start inv.inv_header_data_len

let hdt_header_triples_hex (s:string) (inv:hdt_inventory)
  : option (list triple) =
  match hdt_header_text_hex s inv with
  | None -> None
  | Some text -> Some (Parser.NTriples.parse_ntriples text)

// Declared triples order (1 = SPO) from the Triples control info.
let hdt_triples_order (inv:hdt_inventory) : option nat =
  prop_nat inv.inv_triples_ci.hci_props "order"

// ---------------------------------------------------------------------------
// File-level entry points, on the existing Parquet.Footer byte-range
// I/O boundary (see module banner for the size-probe rationale).
// ---------------------------------------------------------------------------

// Find (largest-successful, first-failing) whole-file read lengths by
// doubling. read_range 0 n succeeds iff n <= file size.
let rec hdt_probe_fail_pow (path:string) (n:pos) (fuel:nat)
  : Tot (option (nat & nat)) (decreases fuel) =
  if fuel = 0 then None
  else
    match PF.parquet_read_range_hex path 0 n with
    | None -> Some (n / 2, n)
    | Some _ -> hdt_probe_fail_pow path (n * 2) (fuel - 1)

// Binary search: read(0,lo) succeeds, read(0,hi) fails; returns the
// largest count that succeeds, i.e. the file size.
let rec hdt_size_bsearch (path:string) (lo:nat) (hi:nat) (fuel:nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 || hi - lo <= 1 then lo
  else
    let mid = (lo + hi) / 2 in
    match PF.parquet_read_range_hex path 0 mid with
    | Some _ -> hdt_size_bsearch path mid hi (fuel - 1)
    | None -> hdt_size_bsearch path lo mid (fuel - 1)

let hdt_file_size (path:string) : option nat =
  match PF.parquet_read_range_hex path 0 0 with
  | None -> None                         // file absent
  | Some _ ->
    (match hdt_probe_fail_pow path 1 64 with
     | None -> None
     | Some (lo, hi) -> Some (hdt_size_bsearch path lo hi 64))

let hdt_read_file_hex (path:string) : option string =
  match hdt_file_size path with
  | None -> None
  | Some sz -> PF.parquet_read_range_hex path 0 sz

// Open + inventory. Returns the hex bytes too so callers (probe,
// stage-2 lookups) decode further sections without re-reading.
let hdt_read_inventory (path:string) : option (string & hdt_inventory) =
  match hdt_read_file_hex path with
  | None -> None
  | Some hex ->
    (match hdt_parse_inventory_hex hex with
     | None -> None
     | Some inv -> Some (hex, inv))
