module RDF.CottasStore.DictWriter

(* Pure-F\* serialiser for the COTTAS .dict companion file.

   #200 PR2, Section B kickoff (2026-05-09). Migrates the byte
   assembly out of formal/fstar/experimental_ocaml_glue/
   cottas_ondisk_zzzzz_ondisk_index.sh's `write_dict_file`
   function, which is a Section E VIOLATION (byte layout in
   OCaml; rule #11 forbids).

   On-disk format (little-endian throughout):

     Header (32 bytes):
       [ magic    : u32  'COKD' = 0x444b4f43 (LE) ]
       [ version  : u32  layout version, currently 1 ]
       [ n        : u32  number of tokens ]
       [ pad      : u32  reserved 0 ]
       [ ids_offs : u64  byte offset of ids[]    section ]
       [ tok_offs : u64  byte offset of tokens[] section ]

     ids[] (4 \* n bytes):
       For each i in 0..n-1, write u32_le i (because tokens are
       sorted lexicographically and ids are assigned in sorted
       order, ids[i] = i).

     token_offs[] (8 \* (n+1) bytes):
       Cumulative byte offsets into the token_data section, plus
       a trailing sentinel = total token_data length.

     token_data:
       Concatenation of all sorted_tokens[i] strings.

   The OCaml caller is responsible for:
     1. Sorting the tokens.
     2. Calling [serialize_dict] to produce the byte payload.
     3. Writing the payload via [atomic_write] (rule #11(a) I/O).

   Round-trip witness: a future commit will add `parse_dict` and
   prove `parse_dict (serialize_dict tokens) == Some tokens` for
   sorted tokens whose total length fits in u64. *)

open FStar.List.Tot

module Lh = RDF.List.Helpers

(* --- Header constants ------------------------------------------------- *)

let dict_magic    : nat = 0x444b4f43      (* 'COKD' little-endian *)
let dict_version  : nat = 1
let header_size   : nat = 32
let id_size       : nat = 4
let offset_size   : nat = 8

(* --- ids[] section --------------------------------------------------- *)

(* For sorted tokens, ids[i] = i. Build a 4*n-byte sequence holding
   the n u32_le values 0..n-1. Recursive build to keep the proof
   manageable. *)
let rec build_ids_acc (i : nat) (n : nat{i <= n /\ n < 4294967296})
  : Tot (RDF.Bytes.bytes) (decreases n - i) =
  if i = n then []
  else Lh.append_tr (RDF.Bytes.write_u32_le i) (build_ids_acc (i + 1) n)

let build_ids (n : nat{n < 4294967296}) : Tot (RDF.Bytes.bytes) =
  build_ids_acc 0 n

(* --- token_offs[] section -------------------------------------------- *)

(* Walk the token list, emitting cumulative-offset u64s. The first
   offset is the byte offset where token_data starts (relative to
   start of file); each subsequent offset adds String.length of the
   prior token. The last entry is a sentinel = total token_data
   length (added relative to the same base). *)
let rec build_offs_acc
  (cur : nat) (tokens : list string)
  : Tot (cur:nat & RDF.Bytes.bytes) (decreases tokens) =
  match tokens with
  | [] ->
    (* Trailing sentinel handled by caller. *)
    (| cur, [] |)
  | t :: rest ->
    if cur >= 18446744073709551616 then (| cur, [] |)
    else
      let cur' = cur + String.length t in
      let (| cur'', rest_bytes |) = build_offs_acc cur' rest in
      let head = RDF.Bytes.write_u64_le cur in
      (| cur'', Lh.append_tr head rest_bytes |)

let build_offs (token_data_offset : nat) (tokens : list string)
  : Tot RDF.Bytes.bytes
  =
  if token_data_offset >= 18446744073709551616 then []
  else
    let (| final, body |) = build_offs_acc token_data_offset tokens in
    if final >= 18446744073709551616 then body
    else Lh.append_tr body (RDF.Bytes.write_u64_le final)

(* --- token_data section ----------------------------------------------- *)

let rec build_data (tokens : list string) : Tot RDF.Bytes.bytes (decreases tokens) =
  match tokens with
  | [] -> []
  | t :: rest -> Lh.append_tr (RDF.Bytes.bytes_of_string t) (build_data rest)

(* --- Header ----------------------------------------------------------- *)

let build_header
  (n : nat{n < 4294967296})
  (ids_offset : nat{ids_offset < 18446744073709551616})
  (tokens_offset : nat{tokens_offset < 18446744073709551616})
  : Tot RDF.Bytes.bytes
  =
  Lh.append_tr (RDF.Bytes.write_u32_le dict_magic)
    (Lh.append_tr (RDF.Bytes.write_u32_le dict_version)
      (Lh.append_tr (RDF.Bytes.write_u32_le n)
        (Lh.append_tr (RDF.Bytes.write_u32_le 0)
          (Lh.append_tr (RDF.Bytes.write_u64_le ids_offset)
            (RDF.Bytes.write_u64_le tokens_offset)))))

(* --- Top-level serialiser -------------------------------------------- *)

(* serialize_dict sorted_tokens
     Produces the full .dict file byte sequence for the given list
     of tokens. Caller must sort beforehand (tokens are stored in
     ascending lexicographic order; ids[i] = i relies on this).

     Returns [] if n >= 2^32 (token count must fit u32) or the total
     token data exceeds u64. Both are practical impossibilities for
     real corpora but the precondition keeps F\* honest about
     overflow.

   Layout offsets:
     ids_offset    = header_size = 32
     tokens_offset = ids_offset + 4*n
     data_offset   = tokens_offset + 8*(n+1)
*)
let serialize_dict (sorted_tokens : list string) : Tot RDF.Bytes.bytes =
  let n = length sorted_tokens in
  if n >= 4294967296 then []
  else
    let ids_offset = header_size in
    let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
    let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
    if data_offset >= 18446744073709551616 then []
    else
      let header = build_header n ids_offset tokens_offset in
      let ids = build_ids n in
      let offs = build_offs data_offset sorted_tokens in
      let data = build_data sorted_tokens in
      Lh.append_tr header
        (Lh.append_tr ids
          (Lh.append_tr offs data))
