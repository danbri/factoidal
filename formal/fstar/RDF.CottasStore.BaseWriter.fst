module RDF.CottasStore.BaseWriter

// Native F* writer for the COTTAS base Parquet file (the 4-column SPOG
// schema RDF.CottasStore.OnDiskRuntime / Parquet.Footer read). Closes the
// "why is Python still needed to write it" gap (owner challenge,
// 2026-07-06): until now, store creation and compaction always shelled
// out to pycottas/DuckDB for the base file; only the delta log had a
// native F* writer.
//
// Per CLAUDE.md rule #11, byte assembly lives here as
// `serialize_cottas : list cottas_quad -> Tot (list u8)`; the OCaml side
// (a new experimental_ocaml_glue script, house style per
// cottas_ondisk_zzzzz_ondisk_index.sh's write_dict_file /
// write_presence_file) reduces to converting the byte list to a string
// and atomic-writing it -- no assume val needed, matching the existing
// dict/presence/offsets writer pattern (they are NOT wired through an
// `assume val`; the OCaml glue calls the extracted serializer directly).
//
// Design decisions (see docs/designissues/2026-07-06-native-cottas-
// writer.md companion note in the PR description for the full writeup):
//
//   * Encoding: DELTA_LENGTH_BYTE_ARRAY (DLBA) for all four columns,
//     not RLE_DICTIONARY. Our reader (Parquet.Footer.fst) already fully
//     decodes both, and pycottas dictionary-encodes p/g for size, but
//     DLBA is correct for ANY cardinality and is the simpler encoder to
//     get bit-exact on the first pass (single DELTA_BINARY_PACKED block
//     covering the whole page, values_per_miniblock=32 per spec,
//     min_delta computed as the true block minimum so negative deltas
//     -- a longer IRI followed by a shorter one -- pack correctly).
//     RLE_DICTIONARY for p/g is tracked as follow-up (smaller files,
//     not a correctness requirement).
//   * Codec: UNCOMPRESSED, not ZSTD. Parquet.Footer's
//     `probe_parquet_column_decompressed_payload_hex` unconditionally
//     zstd-decompresses every page regardless of declared codec; this
//     change (see the Parquet.Footer.fst edit in the same commit) adds
//     the missing UNCOMPRESSED branch so both our reader AND any
//     spec-compliant reader (DuckDB) can read pages this writer emits
//     without our needing a from-scratch zstd encoder.
//   * All four columns are declared Parquet-OPTIONAL (repetition_type=1)
//     to match what DuckDB/pycottas actually write (SQL NOT NULL on s/p/o
//     does not become Parquet REQUIRED in their output) and what our own
//     reader assumes (`probe_parquet_column_delta_length_byte_array_
//     values_offset` unconditionally reads a leading 4-byte-length-
//     prefixed definition-level section for every column). No quad ever
//     has a genuinely-null term: default-graph quads store the literal
//     sentinel string "DEFAULT" for `g` (matching
//     cottas_ondisk_runtime.sh's collect_distinct_graph convention), so
//     every definition level is 1 and each page's def-level section is
//     a single trivial RLE run -- no bit-packing needed there.
//   * Row groups: 122,880 rows (Parquet/DuckDB's own default, matching
//     corpus_pipeline.py's `row_group_size` default and
//     docs/designissues/2026-07-05-disk-backed-db-perf-review.md's
//     finding that smaller row groups regress query latency on this
//     reader).
//   * Row order: this module takes an ALREADY-SORTED `list cottas_quad`.
//     Per CLAUDE.md rule #11, sorting a list of already-parsed strings by
//     (s,p,o,g) is not RDF/SPARQL semantic logic -- it is exactly the
//     kind of plain data-shuffling the same rule explicitly assigns to
//     "Consumer tools (CLI, runners, HTTP entry points)"; the CLI
//     (bin/factoidal-cli, `factoidal import`) sorts in OCaml before
//     calling into this module. Characteristic-set clustering
//     (`--row-order cs`) is NOT implemented by the CLI import path yet;
//     only the SPOG lexicographic default (`pycottas.rdf2cottas`'s
//     `index=spog` order) is produced. Tracked as follow-up.
//   * No page/column CRCs: PageHeader.crc (field 4) is optional and
//     Parquet.Footer.fst never reads it, so it is omitted entirely
//     (mirrors "CRCs or their absence per what the reader checks").
//
// Verification scope: total, pure, no `assume val`, no `--lax`. The
// general parse-after-serialize round trip is NOT proven as an F* lemma
// here (DELTA_BINARY_PACKED bit-packing interacting with
// Parquet.Footer's decode recursion is a large proof commensurate with
// DictWriter's own still-admitted general case); instead this follows
// the same documented, house-style tradeoff DictWriter.fst uses: an
// empirical CI round-trip test (tests/unit/cottas_base_writer_
// roundtrip.ml pattern) exercises serialize_cottas -> Parquet.Footer's
// own probes end-to-end on real fixtures.

open FStar.List.Tot

module B  = RDF.Bytes
module Lh = RDF.List.Helpers
module PF = Parquet.Footer

// ===========================================================================
// Quad record + top-level constants
// ===========================================================================

type cottas_quad = {
  cq_s : string;
  cq_p : string;
  cq_o : string;
  cq_g : string;   // "DEFAULT" sentinel for the default graph -- never the
                    // empty string, matching cottas_ondisk_runtime.sh.
}

// Parquet/DuckDB's own default; corpus_pipeline.py's row_group_size
// default and the perf-review doc's measured floor (see banner above).
let row_group_size : nat = 122880

// DELTA_BINARY_PACKED requires values_per_mini_block to be a multiple of
// 32 (parquet-format spec); we always use exactly one block per page, so
// this is also the per-block miniblock capacity.
let values_per_miniblock : nat = 32

// Parquet type / encoding ids used by this writer. These MIRROR
// Parquet.Footer's own vocabulary (parquet_encoding_name /
// parquet_compression_codec_name); kept as separate small constants here
// (not re-exported from Parquet.Footer) because Parquet.Footer defines
// them as *decode* helpers (nat -> string) rather than named constants,
// so there is nothing to share without inventing a name Parquet.Footer
// doesn't have. The numeric values themselves are the Parquet spec's,
// not ours to duplicate-drift on: BYTE_ARRAY=6, OPTIONAL=1,
// DELTA_LENGTH_BYTE_ARRAY=6 (encoding, coincidentally also 6), RLE=3,
// UNCOMPRESSED=0, DATA_PAGE=0.
let parquet_type_byte_array : nat = 6
let parquet_repetition_optional : nat = 1
let parquet_encoding_dlba : nat = 6
let parquet_encoding_rle : nat = 3
let parquet_codec_uncompressed : nat = 0
let parquet_page_type_data_page : nat = 0

// ===========================================================================
// Thrift compact-protocol primitives (write side). Mirrors the decode
// half in Parquet.Footer.fst (nth_field_hex / skip_compact_value_hex /
// decode_compact_list_info_hex) closely enough that every design choice
// below cites the matching decoder.
// ===========================================================================

let rec write_uvarint_rev (n : nat) (acc : list B.byte) : Tot (list B.byte) (decreases n) =
  if n < 128 then B.byte_of_int n :: acc
  else write_uvarint_rev (n / 128) (B.byte_of_int ((128 + (n % 128)) % 256) :: acc)

// Unsigned LEB128 varint, exactly what Parquet.Footer's
// `decode_varint_value_with_end_hex` consumes (used directly, with no
// zigzag, for binary/list lengths -- see `decode_compact_binary_hex` and
// `decode_compact_list_info_hex`).
let write_uvarint (n : nat) : Tot B.bytes =
  List.Tot.rev (write_uvarint_rev n [])

// zigzag(n) for a value known non-negative: 2n. Matches
// `zigzag_decode_nat raw = raw / 2` used for every plain-nat compact
// field (row counts, sizes, offsets, enum ids).
let zigzag_encode_nat (n : nat) : nat = n + n

// zigzag(v) for a possibly-negative int, matching
// `zigzag_decode_int raw`'s two branches exactly (used for
// DELTA_BINARY_PACKED's first_value / min_delta, which can be negative).
let zigzag_encode_int (v : int) : nat =
  if v >= 0 then v + v else (0 - v) + (0 - v) - 1

// Thrift compact field header: short form (delta<<4 | type) when
// 1 <= (field_id - prev_id) <= 15 -- the only form this module ever
// needs, since every struct below has <=10 ascending small field ids --
// else the long form (type nibble alone, then the zigzag field id).
// Mirrors `nth_field_hex`'s decode of `header`/`delta`/`prev_id`.
let write_field_header (field_type : nat) (field_id : nat) (prev_id : nat) : Tot B.bytes =
  if field_id > prev_id && field_id - prev_id <= 15 then
    let fld_delta : nat = field_id - prev_id in
    let hdr : nat = (fld_delta % 16) `op_Multiply` 16 + field_type in
    [B.byte_of_int (hdr % 256)]
  else
    B.byte_of_int (field_type % 256) :: write_uvarint (zigzag_encode_nat field_id)

let write_field_i32 (field_id : nat) (prev_id : nat) (v : nat) : Tot B.bytes =
  Lh.append_tr (write_field_header PF.compact_t_i32 field_id prev_id)
    (write_uvarint (zigzag_encode_nat v))

let write_field_i64 (field_id : nat) (prev_id : nat) (v : nat) : Tot B.bytes =
  Lh.append_tr (write_field_header PF.compact_t_i64 field_id prev_id)
    (write_uvarint (zigzag_encode_nat v))

// Binary/string field: length as a PLAIN (non-zigzag) varint, matching
// `decode_compact_binary_hex`'s direct (unzigzagged) varint-length read.
let write_field_binary (field_id : nat) (prev_id : nat) (s : string) : Tot B.bytes =
  Lh.append_tr (write_field_header PF.compact_t_binary field_id prev_id)
    (Lh.append_tr (write_uvarint (String.length s)) (B.bytes_of_string s))

// List header: short form (count<<4 | etype) for count<15, else long
// form with a plain varint count. Matches
// `decode_compact_list_info_hex`.
let write_list_header (count : nat) (etype : nat) : Tot B.bytes =
  if count < 15 then
    let hdr : nat = (count % 16) `op_Multiply` 16 + etype in
    [B.byte_of_int (hdr % 256)]
  else
    let hdr : nat = 240 + etype in
    B.byte_of_int (hdr % 256) :: write_uvarint count

let write_field_list_header (field_id : nat) (prev_id : nat) (count : nat) (etype : nat) : Tot B.bytes =
  Lh.append_tr (write_field_header PF.compact_t_list field_id prev_id)
    (write_list_header count etype)

let write_stop : B.bytes = [B.byte_of_int 0]

// ===========================================================================
// Small list helpers (kept local; the extraction-semantics traps in
// fstar-module-style forbid List.Tot.splitAt-style stdlib calls whose
// OCaml realisation silently differs from the F* total semantics, so
// every recursive helper here is written out explicitly and decreases on
// direct structural sub-terms).
// ===========================================================================

// Stack-safety note (extraction trap, fstar-module-style skill):
// F*-verified totality is NOT OCaml stack-safety. Every helper below
// whose recursion depth is once-per-ROW (row groups hold up to 122,880
// rows, and bit lists reach ~740k elements) is written accumulator-
// style with a final List.Tot.rev. The plain-cons originals blew the
// 8 MB native stack at the 888,949-quad gene corpus (measured
// 2026-07-06). Helpers whose depth is per-ROW-GROUP (single digits)
// or per-miniblock (thousands) keep the simpler direct recursion.

// Tail-recursive length: F* stdlib List.Tot.length extracts to a plain
// `1 + length tl` recursion, whose depth on a multi-megabyte page byte
// list is millions of frames. Use this for any list that scales with
// rows or bytes.
let rec list_len_acc (#a:Type) (xs : list a) (acc : nat) : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | _ :: tl -> list_len_acc tl (acc + 1)

let list_len (#a:Type) (xs : list a) : Tot nat = list_len_acc xs 0

let rec concat_bytes_list (xs : list B.bytes) : Tot B.bytes (decreases xs) =
  match xs with
  | [] -> []
  | hd :: tl -> Lh.append_tr hd (concat_bytes_list tl)

let rec string_lengths_acc (vs : list string) (acc : list nat)
  : Tot (list nat) (decreases vs) =
  match vs with
  | [] -> List.Tot.rev acc
  | v :: tl -> string_lengths_acc tl (String.length v :: acc)

let string_lengths (vs : list string) : Tot (list nat) =
  string_lengths_acc vs []

// Consecutive differences: [l0;l1;l2;...] -> [l1-l0; l2-l1; ...].
// Length = max (length lengths - 1) 0.
let rec consecutive_deltas_acc (lengths : list nat) (acc : list int)
  : Tot (list int) (decreases lengths) =
  match lengths with
  | [] -> List.Tot.rev acc
  | [_] -> List.Tot.rev acc
  | a :: b :: rest -> consecutive_deltas_acc (b :: rest) ((b - a) :: acc)

let consecutive_deltas (lengths : list nat) : Tot (list int) =
  consecutive_deltas_acc lengths []

let rec list_min_int_acc (xs : list int) (cur : int) : Tot int (decreases xs) =
  match xs with
  | [] -> cur
  | x :: tl -> list_min_int_acc tl (if x < cur then x else cur)

let min_of_int_list (xs : list int) : Tot int =
  match xs with
  | [] -> 0
  | x :: tl -> list_min_int_acc tl x

let rec list_max_nat_acc (xs : list nat) (cur : nat) : Tot nat (decreases xs) =
  match xs with
  | [] -> cur
  | x :: tl -> list_max_nat_acc tl (if x > cur then x else cur)

let max_of_nat_list (xs : list nat) : Tot nat =
  match xs with
  | [] -> 0
  | x :: tl -> list_max_nat_acc tl x

// Smallest bit width w such that v < 2^w (0 when v = 0).
let rec bits_needed (v : nat) : Tot nat (decreases v) =
  if v = 0 then 0 else 1 + bits_needed (v / 2)

// Clamp a (mathematically always-non-negative, but not refined) int down
// to nat defensively -- avoids a refinement-type proof burden analogous
// to DictWriter's documented "empirically tested, general lemma
// deferred" tradeoff.
let clamp_nonneg (x : int) : nat = if x < 0 then 0 else x

let rec map_clamp_nonneg_acc (xs : list int) (acc : list nat)
  : Tot (list nat) (decreases xs) =
  match xs with
  | [] -> List.Tot.rev acc
  | x :: tl -> map_clamp_nonneg_acc tl (clamp_nonneg x :: acc)

let map_clamp_nonneg (xs : list int) : Tot (list nat) =
  map_clamp_nonneg_acc xs []

let rec pad_to_length_acc (xs : list nat) (target : nat) (filler : nat) (acc : list nat)
  : Tot (list nat) (decreases target) =
  if target = 0 then List.Tot.rev acc
  else
    match xs with
    | [] -> pad_to_length_acc [] (target - 1) filler (filler :: acc)
    | hd :: tl -> pad_to_length_acc tl (target - 1) filler (hd :: acc)

let pad_to_length (xs : list nat) (target : nat) (filler : nat) : Tot (list nat) =
  pad_to_length_acc xs target filler []

let rec repeat_byte (v : nat) (count : nat) : Tot B.bytes (decreases count) =
  if count = 0 then [] else B.byte_of_int (v % 256) :: repeat_byte v (count - 1)

// Bottom-up fixed-size chunking, single linear pass, no take/drop
// termination proof needed (structural recursion directly on `rows`).
let rec chunk_rows_acc
  (rows : list cottas_quad) (cap : nat)
  (cur : list cottas_quad) (cur_n : nat) (acc : list (list cottas_quad))
  : Tot (list (list cottas_quad)) (decreases rows) =
  match rows with
  | [] ->
    if cur_n = 0 then List.Tot.rev acc
    else List.Tot.rev (List.Tot.rev cur :: acc)
  | hd :: tl ->
    if cap = 0 || cur_n + 1 >= cap then
      chunk_rows_acc tl cap [] 0 (List.Tot.rev (hd :: cur) :: acc)
    else
      chunk_rows_acc tl cap (hd :: cur) (cur_n + 1) acc

let chunk_rows (rows : list cottas_quad) (cap : nat) : Tot (list (list cottas_quad)) =
  chunk_rows_acc rows cap [] 0 []

// ===========================================================================
// Bit-packing (LSB-first within each byte), matching
// `packed_lsb_value_hex`'s read convention exactly: byte k's bit j
// (j=0 LSB) equals bitstream position k*8+j.
// ===========================================================================

let rec bits_of_nat_lsb (v : nat) (width : nat) : Tot (list nat) (decreases width) =
  if width = 0 then [] else (v % 2) :: bits_of_nat_lsb (v / 2) (width - 1)

// Per-row recursion + up-to-740k-element output at gene scale: build
// REVERSED with rev_acc per value, single final rev.
let rec bits_of_nat_list_racc (vs : list nat) (width : nat) (racc : list nat)
  : Tot (list nat) (decreases vs) =
  match vs with
  | [] -> List.Tot.rev racc
  | v :: tl ->
    bits_of_nat_list_racc tl width
      (List.Tot.rev_acc (bits_of_nat_lsb v width) racc)

let bits_of_nat_list (vs : list nat) (width : nat) : Tot (list nat) =
  bits_of_nat_list_racc vs width []

// Single-level cons recursion (not an 8-deep destructuring match) so the
// termination checker sees a plain structural decrease on `bits`;
// `collected` accumulates up to 7 prior bits (most-recent-first) between
// byte boundaries. Output accumulator `out` is reversed at the end
// (depth was up to ~92k byte frames on gene, over the stack budget).
let rec pack_bits_to_bytes_acc (bits : list nat) (collected : list nat) (count : nat)
  (out : B.bytes)
  : Tot B.bytes (decreases bits) =
  match bits with
  | [] -> List.Tot.rev out
  | hd :: tl ->
    if count = 7 then
      match List.Tot.rev (hd :: collected) with
      | [b0; b1; b2; b3; b4; b5; b6; b7] ->
        let v = b0 + 2 `op_Multiply` b1 + 4 `op_Multiply` b2 + 8 `op_Multiply` b3
                  + 16 `op_Multiply` b4 + 32 `op_Multiply` b5 + 64 `op_Multiply` b6
                  + 128 `op_Multiply` b7 in
        pack_bits_to_bytes_acc tl [] 0 (B.byte_of_int (v % 256) :: out)
      | _ -> List.Tot.rev out  // unreachable: exactly 8 elements by construction
    else
      pack_bits_to_bytes_acc tl (hd :: collected) (count + 1) out

// Every call site pads its bit list to a multiple of 8 (block_size is
// always a multiple of values_per_miniblock=32, and 32*any bit_width is
// a multiple of 8), so `bits` is consumed exactly, with no leftover.
let pack_bits_to_bytes (bits : list nat) : Tot B.bytes =
  pack_bits_to_bytes_acc bits [] 0 []

// ===========================================================================
// DELTA_LENGTH_BYTE_ARRAY length-block encoder (the "first level" of a
// DLBA page's values section, consumed by Parquet.Footer's
// `probe_parquet_column_delta_length_byte_array_page_cache`). One block,
// covering the whole page: block_size = miniblocks*32,
// miniblocks = ceil((value_count-1)/32), min_delta = true block minimum
// (so negative deltas -- a shorter value following a longer one -- pack
// as non-negative "adjusted" values, per spec).
// ===========================================================================

// acc-based (d - min_delta) map; List.Tot.map extracts non-tail.
let rec map_sub_min_acc (xs : list int) (min_delta : int) (acc : list int)
  : Tot (list int) (decreases xs) =
  match xs with
  | [] -> List.Tot.rev acc
  | x :: tl -> map_sub_min_acc tl min_delta ((x - min_delta) :: acc)

let build_dlba_length_block (values : list string) : Tot (nat & B.bytes) =
  let lengths = string_lengths values in
  let value_count = list_len lengths in
  match lengths with
  | [] ->
    let header =
      Lh.append_tr (write_uvarint values_per_miniblock)
        (Lh.append_tr (write_uvarint 1)
          (Lh.append_tr (write_uvarint 0)
            (Lh.append_tr (write_uvarint (zigzag_encode_nat 0))
              (write_uvarint (zigzag_encode_int 0))))) in
    (0, Lh.append_tr header [B.byte_of_int 0])
  | first_length :: _ ->
    let deltas = consecutive_deltas lengths in
    let num_deltas = list_len deltas in
    let min_delta = min_of_int_list deltas in
    let adjusted_int = map_sub_min_acc deltas min_delta [] in
    let adjusted = map_clamp_nonneg adjusted_int in
    let bit_width = bits_needed (max_of_nat_list adjusted) in
    let miniblocks = if num_deltas = 0 then 1 else (num_deltas + values_per_miniblock - 1) / values_per_miniblock in
    let block_size = miniblocks `op_Multiply` values_per_miniblock in
    let padded = pad_to_length adjusted block_size 0 in
    let bits = bits_of_nat_list padded bit_width in
    let packed = pack_bits_to_bytes bits in
    let widths = repeat_byte bit_width miniblocks in
    let header =
      Lh.append_tr (write_uvarint block_size)
        (Lh.append_tr (write_uvarint miniblocks)
          (Lh.append_tr (write_uvarint value_count)
            (Lh.append_tr (write_uvarint (zigzag_encode_nat first_length))
              (write_uvarint (zigzag_encode_int min_delta))))) in
    (value_count, Lh.append_tr header (Lh.append_tr widths packed))

// Per-row recursion; reversed-accumulator per the module's stack-safety
// note (value bytes reach tens of MB at gene scale).
let rec concat_strings_bytes_racc (vs : list string) (racc : B.bytes)
  : Tot B.bytes (decreases vs) =
  match vs with
  | [] -> List.Tot.rev racc
  | v :: tl ->
    concat_strings_bytes_racc tl (List.Tot.rev_acc (B.bytes_of_string v) racc)

let concat_strings_bytes (vs : list string) : Tot B.bytes =
  concat_strings_bytes_racc vs []

// ===========================================================================
// Definition-level section. Every row's term is present (default-graph
// quads store the "DEFAULT" sentinel, never a real Parquet null), so this
// is always exactly one RLE run of `value_count` copies of level 1.
// ===========================================================================

let build_def_level_section (value_count : nat) : Tot B.bytes =
  // RLE run header = (run_length << 1) | mode, mode=0 (RLE); run_length =
  // value_count (every level is 1, i.e. present). Body is a single
  // ceil(1/8)=1 byte value.
  let rle_bytes =
    if value_count = 0 then []
    else Lh.append_tr (write_uvarint (value_count + value_count)) [B.byte_of_int 1] in
  let section_len = List.Tot.length rle_bytes in
  if section_len >= 4294967296 then []
  else Lh.append_tr (B.write_u32_le section_len) rle_bytes

// ===========================================================================
// Page header + column page assembly.
// ===========================================================================

// `encoding` (writer v2, 2026-07-06): parameterised over the data page's
// declared value-encoding so the same header builder serves both DLBA
// columns (v1, unchanged behaviour when called with
// `parquet_encoding_dlba`) and RLE_DICTIONARY columns (v2, below). The
// definition-level / repetition-level encodings (fields 3/4) stay RLE
// regardless -- those describe the def/rep-level sections, which use the
// same trivial single-run RLE shape either way (see
// `build_def_level_section`'s banner).
let build_page_header (encoding : nat) (num_values : nat) (uncompressed_size : nat) (compressed_size : nat) : Tot B.bytes =
  let f1 = write_field_i32 1 0 parquet_page_type_data_page in
  let f2 = write_field_i32 2 1 uncompressed_size in
  let f3 = write_field_i32 3 2 compressed_size in
  let d1 = write_field_i32 1 0 num_values in
  let d2 = write_field_i32 2 1 encoding in
  let d3 = write_field_i32 3 2 parquet_encoding_rle in
  let d4 = write_field_i32 4 3 parquet_encoding_rle in
  let dph = Lh.append_tr d1 (Lh.append_tr d2 (Lh.append_tr d3 (Lh.append_tr d4 write_stop))) in
  let f5 = Lh.append_tr (write_field_header PF.compact_t_struct 5 3) dph in
  Lh.append_tr f1 (Lh.append_tr f2 (Lh.append_tr f3 (Lh.append_tr f5 write_stop)))

// Returns (num_values, total page byte length, page bytes = header ++ payload).
let build_column_page (values : list string) : Tot (nat & nat & B.bytes) =
  let value_count = list_len values in
  let def_section = build_def_level_section value_count in
  let (_dlba_value_count, length_block) = build_dlba_length_block values in
  let value_bytes = concat_strings_bytes values in
  let payload = Lh.append_tr def_section (Lh.append_tr length_block value_bytes) in
  let payload_len = list_len payload in
  let header = build_page_header parquet_encoding_dlba value_count payload_len payload_len in
  let page_bytes = Lh.append_tr header payload in
  (value_count, list_len page_bytes, page_bytes)

// ===========================================================================
// ColumnMetaData / ColumnChunk / SchemaElement / RowGroup / FileMetaData.
// Field ids below are the real parquet.thrift ids (ColumnMetaData: 1 type,
// 2 encodings, 3 path_in_schema, 4 codec, 5 num_values,
// 6 total_uncompressed_size, 7 total_compressed_size, 9 data_page_offset;
// ColumnChunk: 2 file_offset, 3 meta_data; SchemaElement: 1 type,
// 3 repetition_type, 4 name, 5 num_children; RowGroup: 1 columns,
// 2 total_byte_size, 3 num_rows; FileMetaData: 1 version, 2 schema,
// 3 num_rows, 4 row_groups) -- the same ids Parquet.Footer.fst's probes
// already assume (the #98 field-11-not-14 lesson), so writing against
// the real spec keeps writer and reader in lockstep without duplicating
// a single magic number Parquet.Footer doesn't already define.
// ===========================================================================

let build_column_metadata (name : string) (num_values : nat) (page_len : nat) (data_page_offset : nat) : Tot B.bytes =
  let f1 = write_field_i32 1 0 parquet_type_byte_array in
  let f2 = write_field_list_header 2 1 1 PF.compact_t_i32 in
  let f2v = write_uvarint (zigzag_encode_nat parquet_encoding_dlba) in
  let f3 = write_field_list_header 3 2 1 PF.compact_t_binary in
  let f3v = Lh.append_tr (write_uvarint (String.length name)) (B.bytes_of_string name) in
  let f4 = write_field_i32 4 3 parquet_codec_uncompressed in
  let f5 = write_field_i64 5 4 num_values in
  let f6 = write_field_i64 6 5 page_len in
  let f7 = write_field_i64 7 6 page_len in
  let f9 = write_field_i64 9 7 data_page_offset in
  Lh.append_tr f1 (Lh.append_tr f2 (Lh.append_tr f2v (Lh.append_tr f3 (Lh.append_tr f3v
    (Lh.append_tr f4 (Lh.append_tr f5 (Lh.append_tr f6 (Lh.append_tr f7 (Lh.append_tr f9 write_stop)))))))))

let build_column_chunk (name : string) (num_values : nat) (page_len : nat) (data_page_offset : nat) : Tot B.bytes =
  let f2 = write_field_i64 2 0 data_page_offset in
  let meta = build_column_metadata name num_values page_len data_page_offset in
  let f3 = Lh.append_tr (write_field_header PF.compact_t_struct 3 2) meta in
  Lh.append_tr f2 (Lh.append_tr f3 write_stop)

// SchemaElement leaf: type BYTE_ARRAY (field 1), repetition OPTIONAL
// (field 3), name (field 4), converted_type UTF8 = 0 (field 6 -- without
// it DuckDB presents the column as BLOB instead of VARCHAR; found by the
// parquet_scan cross-check, 2026-07-06; pycottas/DuckDB-written stores
// carry the annotation, so ours must too for schema parity).
let build_schema_leaf (name : string) : Tot B.bytes =
  let f1 = write_field_i32 1 0 parquet_type_byte_array in
  let f3 = write_field_i32 3 1 parquet_repetition_optional in
  let f4 = write_field_binary 4 3 name in
  let f6 = write_field_i32 6 4 0 in
  Lh.append_tr f1 (Lh.append_tr f3 (Lh.append_tr f4 (Lh.append_tr f6 write_stop)))

let build_schema_root (num_children : nat) : Tot B.bytes =
  let f4 = write_field_binary 4 0 "schema" in
  let f5 = write_field_i32 5 4 num_children in
  Lh.append_tr f4 (Lh.append_tr f5 write_stop)

// Returns (element count including the root, concatenated element bytes).
let build_schema_list (names : list string) : Tot (nat & B.bytes) =
  let root = build_schema_root (List.Tot.length names) in
  let leaves = Lh.concatMap_tr build_schema_leaf names in
  (1 + List.Tot.length names, Lh.append_tr root leaves)

// Per-row projections; accumulator-style per the module's stack-safety note.
let rec map_cq_s_acc (rows : list cottas_quad) (acc : list string)
  : Tot (list string) (decreases rows) =
  match rows with [] -> List.Tot.rev acc | r :: tl -> map_cq_s_acc tl (r.cq_s :: acc)
let map_cq_s (rows : list cottas_quad) : Tot (list string) = map_cq_s_acc rows []
let rec map_cq_p_acc (rows : list cottas_quad) (acc : list string)
  : Tot (list string) (decreases rows) =
  match rows with [] -> List.Tot.rev acc | r :: tl -> map_cq_p_acc tl (r.cq_p :: acc)
let map_cq_p (rows : list cottas_quad) : Tot (list string) = map_cq_p_acc rows []
let rec map_cq_o_acc (rows : list cottas_quad) (acc : list string)
  : Tot (list string) (decreases rows) =
  match rows with [] -> List.Tot.rev acc | r :: tl -> map_cq_o_acc tl (r.cq_o :: acc)
let map_cq_o (rows : list cottas_quad) : Tot (list string) = map_cq_o_acc rows []
let rec map_cq_g_acc (rows : list cottas_quad) (acc : list string)
  : Tot (list string) (decreases rows) =
  match rows with [] -> List.Tot.rev acc | r :: tl -> map_cq_g_acc tl (r.cq_g :: acc)
let map_cq_g (rows : list cottas_quad) : Tot (list string) = map_cq_g_acc rows []

// Returns (next_file_offset, row-group page bytes, row-group metadata
// struct bytes, num_rows).
let build_row_group (start_offset : nat) (rows : list cottas_quad) : Tot (nat & B.bytes & B.bytes & nat) =
  let num_rows = list_len rows in
  let (nv_s, len_s, bytes_s) = build_column_page (map_cq_s rows) in
  let off_s = start_offset in
  let off_p = off_s + len_s in
  let (nv_p, len_p, bytes_p) = build_column_page (map_cq_p rows) in
  let off_o = off_p + len_p in
  let (nv_o, len_o, bytes_o) = build_column_page (map_cq_o rows) in
  let off_g = off_o + len_o in
  let (nv_g, len_g, bytes_g) = build_column_page (map_cq_g rows) in
  let next_offset = off_g + len_g in
  let page_bytes = Lh.append_tr bytes_s (Lh.append_tr bytes_p (Lh.append_tr bytes_o bytes_g)) in
  let chunk_s = build_column_chunk "s" nv_s len_s off_s in
  let chunk_p = build_column_chunk "p" nv_p len_p off_p in
  let chunk_o = build_column_chunk "o" nv_o len_o off_o in
  let chunk_g = build_column_chunk "g" nv_g len_g off_g in
  let columns_list =
    Lh.append_tr (write_list_header 4 PF.compact_t_struct)
      (Lh.append_tr chunk_s (Lh.append_tr chunk_p (Lh.append_tr chunk_o chunk_g))) in
  let f1 = Lh.append_tr (write_field_header PF.compact_t_list 1 0) columns_list in
  let total_byte_size = len_s + len_p + len_o + len_g in
  let f2 = write_field_i64 2 1 total_byte_size in
  let f3 = write_field_i64 3 2 num_rows in
  let rg_meta = Lh.append_tr f1 (Lh.append_tr f2 (Lh.append_tr f3 write_stop)) in
  (next_offset, page_bytes, rg_meta, num_rows)

let rec build_row_groups_acc (start_offset : nat) (groups : list (list cottas_quad))
  : Tot (nat & B.bytes & list B.bytes & nat) (decreases groups) =
  match groups with
  | [] -> (start_offset, [], [], 0)
  | g :: rest ->
    let (off1, pbytes, rgmeta, nrows) = build_row_group start_offset g in
    let (off2, rest_pbytes, rest_rgmeta, rest_nrows) = build_row_groups_acc off1 rest in
    (off2, Lh.append_tr pbytes rest_pbytes, rgmeta :: rest_rgmeta, nrows + rest_nrows)

let build_file_metadata (num_rows : nat) (rg_metas : list B.bytes) : Tot B.bytes =
  let f1 = write_field_i32 1 0 1 in
  let (schema_count, schema_elems) = build_schema_list ["s"; "p"; "o"; "g"] in
  let f2 =
    Lh.append_tr (write_field_header PF.compact_t_list 2 1)
      (Lh.append_tr (write_list_header schema_count PF.compact_t_struct) schema_elems) in
  let f3 = write_field_i64 3 2 num_rows in
  let num_rg = List.Tot.length rg_metas in
  let rg_list =
    Lh.append_tr (write_list_header num_rg PF.compact_t_struct) (concat_bytes_list rg_metas) in
  let f4 = Lh.append_tr (write_field_header PF.compact_t_list 4 3) rg_list in
  Lh.append_tr f1 (Lh.append_tr f2 (Lh.append_tr f3 (Lh.append_tr f4 write_stop)))

// ===========================================================================
// Top-level entry point.
// ===========================================================================

let magic_header : B.bytes = B.bytes_of_string PF.parquet_magic

// serialize_cottas sorted_rows
//   Produces the full COTTAS base-file byte sequence for an
//   already-(s,p,o,g)-sorted quad list. Caller (bin/factoidal-cli's
//   `import` subcommand, an out-of-boundary CONSUMER per rule #11)
//   is responsible for sorting.
let serialize_cottas (rows : list cottas_quad) : Tot B.bytes =
  let groups = chunk_rows rows row_group_size in
  let (_final_offset, page_bytes, rg_metas, num_rows) =
    build_row_groups_acc (List.Tot.length magic_header) groups in
  let metadata = build_file_metadata num_rows rg_metas in
  let metadata_len = list_len metadata in
  if metadata_len >= 4294967296 then Lh.append_tr magic_header page_bytes
  else
    Lh.append_tr magic_header
      (Lh.append_tr page_bytes
        (Lh.append_tr metadata
          (Lh.append_tr (B.write_u32_le metadata_len) magic_header)))

// ===========================================================================
// Writer v2: RLE_DICTIONARY encoding (closing the v1-disclosed ~60x size
// premium vs pycottas ZSTD, 2026-07-06).
//
// v1 (4f8fc95) always writes DELTA_LENGTH_BYTE_ARRAY: correct for any
// cardinality but pays the full string bytes on every row, every column,
// even for p/g whose whole point is massive repetition. v2 adds
// RLE_DICTIONARY (dictionary page + hybrid-RLE index stream), matching
// exactly the byte shapes Parquet.Footer's decoder consumes (issue #98's
// hardened section above: PLAIN dictionary entries are LE-u32-length-
// prefixed BYTE_ARRAY values; the data page opens with the same
// definition-level section every column already has, THEN a 1-byte
// index bit-width, THEN a hybrid RLE/bit-packed index stream).
//
// Encoding-choice policy (the "crossover"):
//   * p and g are ALWAYS dictionary-encoded (`encode_column_forced_dict`)
//     -- matching pycottas/DuckDB's own convention and RDF's structural
//     reality (predicate and graph vocabularies are small closed sets
//     relative to row count in every corpus we carry).
//   * s and o use `encode_column_choose_smaller`: this writer builds
//     BOTH the DLBA and the RLE_DICTIONARY encoding for the column and
//     keeps whichever is fewer bytes, per row group. This is deliberately
//     NOT a hardcoded "cardinality < X%" threshold -- picking a single
//     fixed percentage would either leave size on the table (too
//     conservative) or blow up on a corpus whose subject/object
//     cardinality profile doesn't match the corpus the threshold was
//     tuned on (too aggressive). Comparing actual encoded byte counts is
//     strictly at least as good on every corpus, and the tests/local
//     measurement run reports where the two costs actually cross on the
//     real corpora (see the writer-v2 measurement note in the PR
//     description) so the "crossover" claim is falsifiable instead of
//     asserted.
//   * Complexity: both the dictionary build (merge sort + dedup, O(n log
//     n)) and the choose-smaller comparison are safe to run
//     UNCONDITIONALLY, even on a high-cardinality column where dictionary
//     encoding will lose -- there is no O(n * distinct) blowup path here
//     (see `dict_tree_of_sorted`/`dict_tree_find` below), unlike a naive
//     linear-scan "is this value already in the dictionary?" approach,
//     which would be quadratic on exactly the columns (s/o) where
//     cardinality is least predictable.
//
// RLE-only run policy: this encoder ALWAYS uses hybrid-RLE "mode 0" (RLE)
// runs for the index stream, never "mode 1" (bit-packed) runs. Parquet's
// hybrid format allows freely mixing both, and bit-packed runs pack
// slightly tighter for a column with almost no local repetition (a
// handful of bits/value instead of ~2-3 bytes/run-header+body). But mode
// 1 runs are REQUIRED to represent an exact multiple of 8 values (a
// "group of 8"), and any run that isn't the last one in the page cannot
// be padded (the reader always advances past a run's FULL declared body,
// so padding a non-final run would inject bogus indices into the middle
// of the decoded stream). Achieving the extra bit-packing win without
// that correctness hazard needs interleaved run-splitting logic
// (flush-current-bitpack-batch-before-emitting-an-RLE-run); RLE-only is
// the simpler, still fully spec-compliant first cut -- every run length
// (including runs of length 1) is exactly representable with no padding
// math, and it already captures the dominant win (replacing full string
// values with small integer indices) even where there's no repetition to
// exploit. Tightening the tail with bit-packed runs is a follow-up, not
// a correctness requirement.
// ===========================================================================

let parquet_encoding_plain : nat = 0
let parquet_encoding_rle_dictionary : nat = 8
let parquet_page_type_dictionary_page : nat = 2

// --- Local total string sort + dedup ---------------------------------------
// Self-contained copy of RDF.Canonical.fst's proven no-worst-case-blowup
// merge sort shape (split-by-POSITION, never by pivot value, so no input
// ordering -- sorted, reverse-sorted, many-duplicate-prefix -- can
// degrade it to O(n^2) or blow the OCaml stack the way a first-element-
// pivot quicksort can). Kept local (not `open RDF.Canonical`) to keep
// this module's dependency footprint scoped to what it actually needs --
// RDF.Canonical is a large, unrelated (RDFC-1.0 canonicalization) module.

let str_lt (a b : string) : bool = String.compare a b < 0
let str_le (a b : string) : bool = String.compare a b <= 0

let rec str_list_len_acc (xs : list string) (acc : nat) : Tot nat (decreases xs) =
  match xs with
  | [] -> acc
  | _ :: tl -> str_list_len_acc tl (acc + 1)

let str_list_len (xs : list string) : nat = str_list_len_acc xs 0

let rec split_pos_str_acc (n : nat) (xs : list string) (acc : list string)
  : Tot (list string & list string) (decreases xs) =
  match xs with
  | [] -> (List.Tot.rev acc, [])
  | hd :: tl -> if n = 0 then (List.Tot.rev acc, xs) else split_pos_str_acc (n - 1) tl (hd :: acc)

let rec merge_sorted_str_acc (xs ys : list string) (fuel : nat) (acc : list string)
  : Tot (list string) (decreases fuel) =
  if fuel = 0 then List.Tot.rev acc `Lh.append_tr` (xs `Lh.append_tr` ys)
  else
    match xs, ys with
    | [], [] -> List.Tot.rev acc
    | [], hd :: tl -> merge_sorted_str_acc [] tl (fuel - 1) (hd :: acc)
    | hd :: tl, [] -> merge_sorted_str_acc tl [] (fuel - 1) (hd :: acc)
    | hx :: tx, hy :: ty ->
      if str_le hx hy
      then merge_sorted_str_acc tx ys (fuel - 1) (hx :: acc)
      else merge_sorted_str_acc xs ty (fuel - 1) (hy :: acc)

// `depth_fuel` is a totality device (as in RDF.Canonical's identical
// idiom): seeded generously above the ~log2(n) levels the split
// recursion actually needs, so `depth_fuel = 0` is unreachable for any
// real input.
let rec merge_sort_strings_fuel (xs : list string) (depth_fuel : nat)
  : Tot (list string) (decreases depth_fuel) =
  match xs with
  | [] -> []
  | [_] -> xs
  | _ :: _ :: _ ->
    if depth_fuel = 0 then xs
    else
      let n = str_list_len xs in
      let (left, right) = split_pos_str_acc (n / 2) xs [] in
      let sl = merge_sort_strings_fuel left (depth_fuel - 1) in
      let sr = merge_sort_strings_fuel right (depth_fuel - 1) in
      let fuel = str_list_len sl + str_list_len sr in
      merge_sorted_str_acc sl sr fuel []

let merge_sort_strings (xs : list string) : Tot (list string) =
  merge_sort_strings_fuel xs (str_list_len xs + 1)

let rec dedup_sorted_str_acc (xs : list string) (acc : list string)
  : Tot (list string) (decreases xs) =
  match xs with
  | [] -> List.Tot.rev acc
  | [x] -> List.Tot.rev (x :: acc)
  | x :: y :: tl -> if x = y then dedup_sorted_str_acc (y :: tl) acc else dedup_sorted_str_acc (y :: tl) (x :: acc)

let dedup_sorted_str (xs : list string) : Tot (list string) = dedup_sorted_str_acc xs []

let rec zip_with_index_acc (xs : list string) (i : nat) (acc : list (string & nat))
  : Tot (list (string & nat)) (decreases xs) =
  match xs with
  | [] -> List.Tot.rev acc
  | hd :: tl -> zip_with_index_acc tl (i + 1) ((hd, i) :: acc)

let zip_with_index (xs : list string) : Tot (list (string & nat)) = zip_with_index_acc xs 0 []

// --- Balanced lookup tree (value -> dictionary index), O(log d) find ------
// Same shape as RDF.Canonical.fst's `bn_lookup_tree` (split by position
// from an already-sorted list, so the tree is balanced regardless of
// input order) -- built ONCE per column per row group (O(d log d)), then
// `dict_tree_find` is O(log d) per row, giving O(n log d) total instead
// of a naive linear-scan-per-row O(n * d). This is what makes it safe to
// run the dictionary build unconditionally on s/o (see the banner above):
// even a high-cardinality column (d close to n) costs O(n log n), never
// O(n^2).

type dict_lookup_tree =
  | DLT_Leaf
  | DLT_Node of dict_lookup_tree * string * nat * dict_lookup_tree

let rec split_pos_pair_acc (n : nat) (xs : list (string & nat)) (acc : list (string & nat))
  : Tot (list (string & nat) & list (string & nat)) (decreases xs) =
  match xs with
  | [] -> (List.Tot.rev acc, [])
  | hd :: tl -> if n = 0 then (List.Tot.rev acc, xs) else split_pos_pair_acc (n - 1) tl (hd :: acc)

let rec dict_tree_of_sorted (xs : list (string & nat)) (n : nat) : Tot dict_lookup_tree (decreases n) =
  if n = 0 then DLT_Leaf
  else
    let mid = n / 2 in
    let (left, rest) = split_pos_pair_acc mid xs [] in
    match rest with
    | [] -> DLT_Leaf  // unreachable: `xs` has `n` elements by construction
    | (k, v) :: right ->
      DLT_Node (dict_tree_of_sorted left mid, k, v, dict_tree_of_sorted right (n - mid - 1))

let rec dict_tree_find (v : string) (t : dict_lookup_tree) : Tot (option nat) (decreases t) =
  match t with
  | DLT_Leaf -> None
  | DLT_Node (l, k, idx, r) ->
    if v = k then Some idx
    else if str_lt v k then dict_tree_find v l
    else dict_tree_find v r

// Per-row lookup walk; tail-recursive per the module's stack-safety note
// (row-group scale, up to 122,880 elements).
let rec lookup_indices_acc (values : list string) (t : dict_lookup_tree) (acc : list nat)
  : Tot (list nat) (decreases values) =
  match values with
  | [] -> List.Tot.rev acc
  | v :: tl ->
    let idx = (match dict_tree_find v t with Some i -> i | None -> 0) in  // None unreachable: v is drawn from the same values the tree was built from
    lookup_indices_acc tl t (idx :: acc)

let lookup_indices (values : list string) (t : dict_lookup_tree) : Tot (list nat) =
  lookup_indices_acc values t []

// --- Maximal-run grouping (for RLE-only hybrid encoding) -------------------

let rec group_runs_acc (indices : list nat) (cur_val : nat) (cur_count : nat) (acc : list (nat & nat))
  : Tot (list (nat & nat)) (decreases indices) =
  match indices with
  | [] -> List.Tot.rev ((cur_val, cur_count) :: acc)
  | v :: tl ->
    if v = cur_val then group_runs_acc tl cur_val (cur_count + 1) acc
    else group_runs_acc tl v 1 ((cur_val, cur_count) :: acc)

let group_runs (indices : list nat) : Tot (list (nat & nat)) =
  match indices with
  | [] -> []
  | v :: tl -> group_runs_acc tl v 1 []

// --- Hybrid RLE run byte assembly ------------------------------------------
// Matches Parquet.Footer's `decode_hybrid_rle_runs` mode-0 (RLE) branch
// exactly: header = plain (non-zigzag) varint of (run_length << 1 | 0),
// body = the single value as `ceil(bit_width / 8)` little-endian bytes.

let rec write_le_uint_bytes_acc (v : nat) (nbytes : nat) (acc : list B.byte)
  : Tot B.bytes (decreases nbytes) =
  if nbytes = 0 then List.Tot.rev acc
  else write_le_uint_bytes_acc (v / 256) (nbytes - 1) (B.byte_of_int (v % 256) :: acc)

let write_le_uint_bytes (v : nat) (nbytes : nat) : Tot B.bytes =
  write_le_uint_bytes_acc v nbytes []

// Per-run recursion (depth = number of maximal runs, up to row-group
// scale in the degenerate all-distinct case) -- accumulator style per
// the module's stack-safety note.
let rec build_rle_runs_acc (body_nbytes : nat) (runs : list (nat & nat)) (racc : B.bytes)
  : Tot B.bytes (decreases runs) =
  match runs with
  | [] -> List.Tot.rev racc
  | (value, count) :: tl ->
    let header = write_uvarint (count + count) in  // mode 0 (RLE): (run_length << 1) | 0
    let body = write_le_uint_bytes value body_nbytes in
    build_rle_runs_acc body_nbytes tl (List.Tot.rev_acc (Lh.append_tr header body) racc)

let build_rle_runs (body_nbytes : nat) (runs : list (nat & nat)) : Tot B.bytes =
  build_rle_runs_acc body_nbytes runs []

// --- Dictionary page assembly -----------------------------------------------
// PLAIN encoding for BYTE_ARRAY: LE u32 length prefix + raw bytes, no
// varint (matches `decode_one_plain_dictionary_entry`'s `le_u32_at_hex`
// read, NOT a varint-length read like DLBA's length block).

let write_dict_entry (e : string) : Tot B.bytes =
  let len = String.length e in
  if len >= 4294967296 then []  // unreachable for real corpora; keeps F* honest per DictWriter.fst's house style
  else Lh.append_tr (B.write_u32_le len) (B.bytes_of_string e)

let rec build_dict_entries_acc (entries : list string) (racc : B.bytes)
  : Tot B.bytes (decreases entries) =
  match entries with
  | [] -> List.Tot.rev racc
  | e :: tl -> build_dict_entries_acc tl (List.Tot.rev_acc (write_dict_entry e) racc)

let build_dict_page_payload (entries : list string) : Tot B.bytes =
  build_dict_entries_acc entries []

// DictionaryPageHeader: field 1 num_values, field 2 encoding (PLAIN).
// PageHeader: field 1 type=DICTIONARY_PAGE, field 2/3 sizes, field 7
// dictionary_page_header struct (matches
// `parquet_dictionary_page_num_values_at`'s field7->field1 read).
let build_dictionary_page_header (num_values : nat) (uncompressed_size : nat) (compressed_size : nat) : Tot B.bytes =
  let f1 = write_field_i32 1 0 parquet_page_type_dictionary_page in
  let f2 = write_field_i32 2 1 uncompressed_size in
  let f3 = write_field_i32 3 2 compressed_size in
  let d1 = write_field_i32 1 0 num_values in
  let d2 = write_field_i32 2 1 parquet_encoding_plain in
  let dph = Lh.append_tr d1 (Lh.append_tr d2 write_stop) in
  let f7 = Lh.append_tr (write_field_header PF.compact_t_struct 7 3) dph in
  Lh.append_tr f1 (Lh.append_tr f2 (Lh.append_tr f3 (Lh.append_tr f7 write_stop)))

// --- RLE_DICTIONARY data-page payload ---------------------------------------
// Same def-level section every column has, then the 1-byte index
// bit-width, then the RLE-only hybrid index stream (matches
// `decode_rle_dictionary_data_page`'s "byte 0 = bit_width, rest = hybrid
// RLE/bit-packed stream" contract exactly, using only mode-0 runs).

let build_rle_dictionary_page_payload (value_count : nat) (bit_width : nat) (runs : list (nat & nat)) : Tot B.bytes =
  let def_section = build_def_level_section value_count in
  let body_nbytes = (bit_width + 7) / 8 in
  let runs_bytes = build_rle_runs body_nbytes runs in
  Lh.append_tr def_section (Lh.append_tr [B.byte_of_int (bit_width % 256)] runs_bytes)

// --- Column-level encoding choice -------------------------------------------

type column_encoding =
  | CE_DLBA
  | CE_RleDictionary

// ce_dict_page_len is 0 for CE_DLBA (no dictionary page at all);
// ce_total_len is the FULL byte length of this column's page(s)
// (dictionary page + data page for CE_RleDictionary, just the data page
// for CE_DLBA) -- exactly what `build_row_group`'s cumulative-offset
// arithmetic already expects from a column encoder.
type col_encoded = {
  ce_kind : column_encoding;
  ce_num_values : nat;
  ce_dict_page_len : nat;
  ce_total_len : nat;
  ce_bytes : B.bytes;
}

let build_column_page_dlba_v2 (values : list string) : Tot col_encoded =
  let (nv, len, bytes) = build_column_page values in
  { ce_kind = CE_DLBA; ce_num_values = nv; ce_dict_page_len = 0; ce_total_len = len; ce_bytes = bytes }

// Builds the full RLE_DICTIONARY encoding (dictionary page ++ data page)
// for one column's values in one row group. See the module-level banner
// above for the complexity argument (O(n log n), never O(n * distinct)).
let build_column_page_rle_dict (values : list string) : Tot col_encoded =
  let value_count = list_len values in
  if value_count = 0 then
    let dict_header = build_dictionary_page_header 0 0 0 in
    let dict_len = list_len dict_header in
    let data_payload = build_rle_dictionary_page_payload 0 0 [] in
    let data_payload_len = list_len data_payload in
    let data_header = build_page_header parquet_encoding_rle_dictionary 0 data_payload_len data_payload_len in
    let data_bytes = Lh.append_tr data_header data_payload in
    let data_len = list_len data_bytes in
    {
      ce_kind = CE_RleDictionary;
      ce_num_values = 0;
      ce_dict_page_len = dict_len;
      ce_total_len = dict_len + data_len;
      ce_bytes = Lh.append_tr dict_header data_bytes;
    }
  else
    let sorted = merge_sort_strings values in
    let distinct = dedup_sorted_str sorted in
    let dict_size = list_len distinct in
    let indexed = zip_with_index distinct in
    let tree = dict_tree_of_sorted indexed dict_size in
    let indices = lookup_indices values tree in
    let max_index = if dict_size = 0 then 0 else dict_size - 1 in
    let bit_width = bits_needed max_index in
    let runs = group_runs indices in
    let data_payload = build_rle_dictionary_page_payload value_count bit_width runs in
    let data_payload_len = list_len data_payload in
    let data_header = build_page_header parquet_encoding_rle_dictionary value_count data_payload_len data_payload_len in
    let data_bytes = Lh.append_tr data_header data_payload in
    let dict_payload = build_dict_page_payload distinct in
    let dict_payload_len = list_len dict_payload in
    let dict_header = build_dictionary_page_header dict_size dict_payload_len dict_payload_len in
    let dict_bytes = Lh.append_tr dict_header dict_payload in
    let dict_len = list_len dict_bytes in
    let data_len = list_len data_bytes in
    {
      ce_kind = CE_RleDictionary;
      ce_num_values = value_count;
      ce_dict_page_len = dict_len;
      ce_total_len = dict_len + data_len;
      ce_bytes = Lh.append_tr dict_bytes data_bytes;
    }

// p/g: always dictionary-encoded (see module banner).
let encode_column_forced_dict (values : list string) : Tot col_encoded =
  build_column_page_rle_dict values

// s/o: build both, keep whichever is smaller (the "crossover" is this
// comparison itself, not a hardcoded threshold -- see module banner).
let encode_column_choose_smaller (values : list string) : Tot col_encoded =
  let dlba = build_column_page_dlba_v2 values in
  let dict = build_column_page_rle_dict values in
  if dict.ce_total_len < dlba.ce_total_len then dict else dlba

// --- ColumnMetaData / ColumnChunk, encoding-aware ---------------------------
// CE_DLBA reuses the v1 builders unchanged (identical byte shape: no
// dictionary_page_offset field, one declared encoding). CE_RleDictionary
// adds: encodings list of 2 ([PLAIN, RLE_DICTIONARY] -- the dictionary
// page's own encoding, then the data page's), and field 11
// (dictionary_page_offset) pointing at the START of the column chunk
// (the dictionary page always comes first); field 9 (data_page_offset)
// is shifted past the dictionary page's length, per the #98 bug-history
// note on `probe_parquet_column_dictionary_page_offset` (field9 = the
// DATA page, field11 = the DICT page -- our reader treats them as
// distinct offsets, matching real pycottas/DuckDB output).
let build_column_metadata_v2 (name : string) (ce : col_encoded) (chunk_start_offset : nat) : Tot B.bytes =
  match ce.ce_kind with
  | CE_DLBA -> build_column_metadata name ce.ce_num_values ce.ce_total_len chunk_start_offset
  | CE_RleDictionary ->
    let data_page_offset = chunk_start_offset + ce.ce_dict_page_len in
    let f1 = write_field_i32 1 0 parquet_type_byte_array in
    let f2 = write_field_list_header 2 1 2 PF.compact_t_i32 in
    let f2v =
      Lh.append_tr (write_uvarint (zigzag_encode_nat parquet_encoding_plain))
        (write_uvarint (zigzag_encode_nat parquet_encoding_rle_dictionary)) in
    let f3 = write_field_list_header 3 2 1 PF.compact_t_binary in
    let f3v = Lh.append_tr (write_uvarint (String.length name)) (B.bytes_of_string name) in
    let f4 = write_field_i32 4 3 parquet_codec_uncompressed in
    let f5 = write_field_i64 5 4 ce.ce_num_values in
    let f6 = write_field_i64 6 5 ce.ce_total_len in
    let f7 = write_field_i64 7 6 ce.ce_total_len in
    let f9 = write_field_i64 9 7 data_page_offset in
    let f11 = write_field_i64 11 9 chunk_start_offset in
    Lh.append_tr f1 (Lh.append_tr f2 (Lh.append_tr f2v (Lh.append_tr f3 (Lh.append_tr f3v
      (Lh.append_tr f4 (Lh.append_tr f5 (Lh.append_tr f6 (Lh.append_tr f7 (Lh.append_tr f9 (Lh.append_tr f11 write_stop))))))))))

let build_column_chunk_v2 (name : string) (ce : col_encoded) (chunk_start_offset : nat) : Tot B.bytes =
  let f2 = write_field_i64 2 0 chunk_start_offset in
  let meta = build_column_metadata_v2 name ce chunk_start_offset in
  let f3 = Lh.append_tr (write_field_header PF.compact_t_struct 3 2) meta in
  Lh.append_tr f2 (Lh.append_tr f3 write_stop)

// --- Row group / top-level entry point, v2 ----------------------------------

let build_row_group_v2 (start_offset : nat) (rows : list cottas_quad) : Tot (nat & B.bytes & B.bytes & nat) =
  let num_rows = list_len rows in
  let ce_s = encode_column_choose_smaller (map_cq_s rows) in
  let off_s = start_offset in
  let off_p = off_s + ce_s.ce_total_len in
  let ce_p = encode_column_forced_dict (map_cq_p rows) in
  let off_o = off_p + ce_p.ce_total_len in
  let ce_o = encode_column_choose_smaller (map_cq_o rows) in
  let off_g = off_o + ce_o.ce_total_len in
  let ce_g = encode_column_forced_dict (map_cq_g rows) in
  let next_offset = off_g + ce_g.ce_total_len in
  let page_bytes = Lh.append_tr ce_s.ce_bytes (Lh.append_tr ce_p.ce_bytes (Lh.append_tr ce_o.ce_bytes ce_g.ce_bytes)) in
  let chunk_s = build_column_chunk_v2 "s" ce_s off_s in
  let chunk_p = build_column_chunk_v2 "p" ce_p off_p in
  let chunk_o = build_column_chunk_v2 "o" ce_o off_o in
  let chunk_g = build_column_chunk_v2 "g" ce_g off_g in
  let columns_list =
    Lh.append_tr (write_list_header 4 PF.compact_t_struct)
      (Lh.append_tr chunk_s (Lh.append_tr chunk_p (Lh.append_tr chunk_o chunk_g))) in
  let f1 = Lh.append_tr (write_field_header PF.compact_t_list 1 0) columns_list in
  let total_byte_size = ce_s.ce_total_len + ce_p.ce_total_len + ce_o.ce_total_len + ce_g.ce_total_len in
  let f2 = write_field_i64 2 1 total_byte_size in
  let f3 = write_field_i64 3 2 num_rows in
  let rg_meta = Lh.append_tr f1 (Lh.append_tr f2 (Lh.append_tr f3 write_stop)) in
  (next_offset, page_bytes, rg_meta, num_rows)

let rec build_row_groups_acc_v2 (start_offset : nat) (groups : list (list cottas_quad))
  : Tot (nat & B.bytes & list B.bytes & nat) (decreases groups) =
  match groups with
  | [] -> (start_offset, [], [], 0)
  | g :: rest ->
    let (off1, pbytes, rgmeta, nrows) = build_row_group_v2 start_offset g in
    let (off2, rest_pbytes, rest_rgmeta, rest_nrows) = build_row_groups_acc_v2 off1 rest in
    (off2, Lh.append_tr pbytes rest_pbytes, rgmeta :: rest_rgmeta, nrows + rest_nrows)

// serialize_cottas_v2 sorted_rows
//   Same contract as `serialize_cottas` (caller sorts by s,p,o,g first)
//   but with p/g always RLE_DICTIONARY-encoded and s/o encoded with
//   whichever of DLBA/RLE_DICTIONARY is smaller per row group. This is
//   the function the CLI's `import`/`compact --native-writer` paths call
//   as of writer v2 -- `serialize_cottas` (v1) stays as-is for its own
//   pinned round-trip test, not superseded.
let serialize_cottas_v2 (rows : list cottas_quad) : Tot B.bytes =
  let groups = chunk_rows rows row_group_size in
  let (_final_offset, page_bytes, rg_metas, num_rows) =
    build_row_groups_acc_v2 (List.Tot.length magic_header) groups in
  let metadata = build_file_metadata num_rows rg_metas in
  let metadata_len = list_len metadata in
  if metadata_len >= 4294967296 then Lh.append_tr magic_header page_bytes
  else
    Lh.append_tr magic_header
      (Lh.append_tr page_bytes
        (Lh.append_tr metadata
          (Lh.append_tr (B.write_u32_le metadata_len) magic_header)))
