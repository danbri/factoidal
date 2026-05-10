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

(* --- Round-trip parser ------------------------------------------------ *)

(* parse_n_offsets k bs
     Read k u64_le values from the front of bs. Used to consume the
     token_offs[] cumulative-offset array. *)
let rec parse_n_offsets (k : nat) (bs : RDF.Bytes.bytes)
  : Tot (option (list nat & RDF.Bytes.bytes)) (decreases k) =
  if k = 0 then Some ([], bs)
  else
    match RDF.Bytes.parse_u64_le bs with
    | None -> None
    | Some (o, rest) ->
      match parse_n_offsets (k - 1) rest with
      | None -> None
      | Some (offs, after) -> Some (o :: offs, after)

(* parse_tokens_from_offsets offsets bs
     Given cumulative byte offsets [o0; o1; ...; on] (n+1 entries —
     the trailing entry is the sentinel = total token_data length)
     and a byte sequence positioned at the start of token_data, peel
     off n strings whose lengths are the consecutive offset
     differences. Empty token_data (n=0) → single-element offset list,
     handled by the [_] base case. *)
let rec parse_tokens_from_offsets
  (offsets : list nat) (bs : RDF.Bytes.bytes)
  : Tot (option (list string)) (decreases (length offsets)) =
  match offsets with
  | [] -> Some []
  | [_] -> Some []
  | o0 :: o1 :: rest_offs ->
    if o1 < o0 then None
    else
      let len : nat = o1 - o0 in
      match RDF.Bytes.parse_string_of_length len bs with
      | None -> None
      | Some (tok, after) ->
        match parse_tokens_from_offsets (o1 :: rest_offs) after with
        | None -> None
        | Some toks -> Some (tok :: toks)

(* parse_dict bs
     Inverse of [serialize_dict]. Reads the COKD header, skips the
     trivially-redundant ids[] block (ids[i] = i for sorted tokens),
     reads the (n+1)-element cumulative-offsets array, and slices the
     token_data section into n strings.

     Returns [None] if any of:
       - magic mismatch ('COKD' = 0x444b4f43)
       - version mismatch (currently 1)
       - input shorter than declared by header
       - cumulative offsets non-monotonic

     The caller's expectation (round-trip witness):
       parse_dict (serialize_dict sorted_tokens) == Some sorted_tokens
     for any sorted_tokens with [length sorted_tokens < 2^32] and
     [data_offset < 2^64] (the same bounds [serialize_dict] enforces).

     Formal lemma proof attempt: see [lemma_parse_serialize_dict]
     below. The CI hash-roundtrip test in
     tests/unit/dict_writer_roundtrip.ml provides empirical evidence
     while the SMT-resistant pieces of the proof move to a tracking
     issue. *)
let parse_dict (bs : RDF.Bytes.bytes) : Tot (option (list string)) =
  match RDF.Bytes.parse_u32_le bs with
  | None -> None
  | Some (m, after_magic) ->
    if not (m = dict_magic) then None
    else
      match RDF.Bytes.parse_u32_le after_magic with
      | None -> None
      | Some (v, after_version) ->
        if not (v = dict_version) then None
        else
          match RDF.Bytes.parse_u32_le after_version with
          | None -> None
          | Some (n, after_n) ->
            match RDF.Bytes.parse_u32_le after_n with
            | None -> None
            | Some (_pad, after_pad) ->
              match RDF.Bytes.parse_u64_le after_pad with
              | None -> None
              | Some (_ids_off, after_ids_off) ->
                match RDF.Bytes.parse_u64_le after_ids_off with
                | None -> None
                | Some (_tok_off, after_header) ->
                  let ids_bytes_count : nat = id_size `op_Multiply` n in
                  match RDF.Bytes.parse_n_bytes ids_bytes_count after_header with
                  | None -> None
                  | Some (_ids, after_ids) ->
                    match parse_n_offsets (n + 1) after_ids with
                    | None -> None
                    | Some (offsets, after_offsets) ->
                      parse_tokens_from_offsets offsets after_offsets

(* --- Round-trip lemma (attempted; admit-pending until tracker) ------- *)

(* lemma_parse_serialize_dict tokens
     The structural-induction round-trip property for the .dict
     companion-file format.

     Statement:
       parse_dict (serialize_dict tokens) == Some tokens
     under the same overflow preconditions [serialize_dict] requires
     ([length tokens < 2^32] and the cumulative token-data offset
     fits in u64).

     Proof strategy: structural induction over [tokens], discharged
     by composing four lower-level lemmas:
       (a) parse_u32_le (write_u32_le n @ rest) == Some (n, rest)
           for n < 2^32 — byte-LE inverse on the header / ids[] entries.
       (b) parse_u64_le (write_u64_le n @ rest) == Some (n, rest)
           for n < 2^64 — byte-LE inverse on the offset entries.
       (c) parse_n_bytes (length bs) (bs @ rest) == Some (bs, rest)
           — frame-rule for the ids[] / token_data slice.
       (d) parse_string_of_length (String.length s) (bytes_of_string s
             @ rest) == Some (s, rest)
           — relies on the F* stdlib lemma `string_of_list_of_string`.

     Lemmas (a)-(d) are the foundations; once they exist as proven
     facts in [RDF.Bytes], the [serialize_dict] round-trip composes
     them at each header / ids[] / offsets / data section boundary
     plus an induction over the token list for the offsets and data
     pieces.

     Status: ADMITTED for the general case. The empty-tokens base case
     `lemma_parse_serialize_dict_empty_case` (below) is fully proven
     via assert_norm — z3 unfolds the concrete byte-layout for `[]`
     and discharges. The general case needs induction over the token
     list with the four foundation lemmas in `RDF.Bytes`
     (lemma_parse_write_u32_le_inverse, lemma_parse_write_u64_le_inverse,
     lemma_parse_n_bytes_inverse, lemma_parse_string_of_length_inverse,
     all proven post-#252) plus structural sub-lemmas for build_ids /
     build_offs / build_data. The CI hash-roundtrip test in
     tests/unit/dict_writer_roundtrip.ml provides 4-fixture empirical
     evidence for the general case meanwhile. *)

(* Base case: parse_dict (serialize_dict []) == Some [].

   Verifies in <1s — z3 normalises the entire concrete byte sequence
   (40 bytes: 32-byte header + 8-byte sentinel offset, no ids[] or
   token_data) and discharges the parse-walk symbolically. *)
let lemma_parse_serialize_dict_empty_case ()
  : Lemma (ensures parse_dict (serialize_dict []) == Some [])
  = assert_norm (parse_dict (serialize_dict []) == Some [])

(* --- Structural sub-lemmas for the cons case round-trip proof ------- *)

(* build_ids length: build_ids n produces 4*n bytes. Pure structural
   induction on (n - i). *)
let rec lemma_build_ids_acc_length (i : nat) (n : nat{i <= n /\ n < 4294967296})
  : Lemma (ensures FStar.List.Tot.length (build_ids_acc i n) == 4 `op_Multiply` (n - i))
          (decreases n - i) =
  if i = n then ()
  else begin
    lemma_build_ids_acc_length (i + 1) n;
    Lh.lemma_append_tr_eq (RDF.Bytes.write_u32_le i) (build_ids_acc (i + 1) n);
    FStar.List.Tot.Properties.append_length
      (RDF.Bytes.write_u32_le i) (build_ids_acc (i + 1) n)
  end

let lemma_build_ids_length (n : nat{n < 4294967296})
  : Lemma (ensures FStar.List.Tot.length (build_ids n) == 4 `op_Multiply` n) =
  lemma_build_ids_acc_length 0 n

(* Value-level model of build_offs_acc's cumulative offsets.
   `cum_offs cur tokens` = the list of u64 offsets emitted (one per token).
   `cum_final cur tokens` = the final offset after walking all tokens. *)
let rec cum_offs (cur : nat) (tokens : list string)
  : Tot (list nat) (decreases tokens) =
  match tokens with
  | [] -> []
  | t :: rest ->
    if cur >= 18446744073709551616 then []
    else cur :: cum_offs (cur + String.length t) rest

let rec cum_final (cur : nat) (tokens : list string)
  : Tot nat (decreases tokens) =
  match tokens with
  | [] -> cur
  | t :: rest ->
    if cur >= 18446744073709551616 then cur
    else cum_final (cur + String.length t) rest

let rec lemma_cum_final_mono (cur : nat) (tokens : list string)
  : Lemma (ensures cum_final cur tokens >= cur) (decreases tokens) =
  match tokens with
  | [] -> ()
  | t :: rest ->
    if cur >= 18446744073709551616 then ()
    else lemma_cum_final_mono (cur + String.length t) rest

let rec lemma_build_offs_acc_final
  (cur : nat) (tokens : list string)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures (
        let (| final, _ |) = build_offs_acc cur tokens in
        final == cum_final cur tokens))
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest;
      lemma_build_offs_acc_final cur' rest

let rec lemma_parse_n_offsets_build_offs_acc
  (cur : nat) (tokens : list string) (rest : RDF.Bytes.bytes)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures (
        let (| _, body |) = build_offs_acc cur tokens in
        parse_n_offsets (length tokens) (FStar.List.Tot.append body rest)
        == Some (cum_offs cur tokens, rest)))
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest_tokens ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest_tokens;
      lemma_parse_n_offsets_build_offs_acc cur' rest_tokens rest;
      let (| _, rest_body |) = build_offs_acc cur' rest_tokens in
      let head = RDF.Bytes.write_u64_le cur in
      Lh.lemma_append_tr_eq head rest_body;
      FStar.List.Tot.Properties.append_assoc head rest_body rest;
      RDF.Bytes.lemma_parse_write_u64_le_inverse cur (FStar.List.Tot.append rest_body rest)

let rec lemma_parse_tokens_from_offsets_build_data
  (cur : nat) (tokens : list string) (rest : RDF.Bytes.bytes)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures (
        let offsets = FStar.List.Tot.append
                        (cum_offs cur tokens)
                        [cum_final cur tokens] in
        parse_tokens_from_offsets offsets
                                  (FStar.List.Tot.append (build_data tokens) rest)
        == Some tokens))
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest_tokens ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest_tokens;
      lemma_parse_tokens_from_offsets_build_data cur' rest_tokens rest;
      let head_bytes = RDF.Bytes.bytes_of_string t in
      let tail_data = build_data rest_tokens in
      Lh.lemma_append_tr_eq head_bytes tail_data;
      FStar.List.Tot.Properties.append_assoc head_bytes tail_data rest;
      RDF.Bytes.lemma_parse_string_of_length_inverse t
        (FStar.List.Tot.append tail_data rest);
      FStar.String.list_of_string_of_list (RDF.Bytes.bytes_of_string t);
      ()

let rec lemma_cum_offs_length
  (cur : nat) (tokens : list string)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures length (cum_offs cur tokens) == length tokens)
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest;
      lemma_cum_offs_length cur' rest

(* Append-stability for parse_*_le. General-purpose facts; could move
   to RDF.Bytes in a future cleanup. *)
let lemma_parse_u64_le_append
  (front rear : RDF.Bytes.bytes)
  : Lemma
      (requires Some? (RDF.Bytes.parse_u64_le front))
      (ensures (
        let Some (o, front_rest) = RDF.Bytes.parse_u64_le front in
        RDF.Bytes.parse_u64_le (FStar.List.Tot.append front rear)
        == Some (o, FStar.List.Tot.append front_rest rear)))
  = match front with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest -> ()

let lemma_parse_u32_le_append
  (front rear : RDF.Bytes.bytes)
  : Lemma
      (requires Some? (RDF.Bytes.parse_u32_le front))
      (ensures (
        let Some (o, front_rest) = RDF.Bytes.parse_u32_le front in
        RDF.Bytes.parse_u32_le (FStar.List.Tot.append front rear)
        == Some (o, FStar.List.Tot.append front_rest rear)))
  = match front with
    | b0 :: b1 :: b2 :: b3 :: rest -> ()

let rec lemma_parse_n_offsets_append
  (k : nat) (front rear : RDF.Bytes.bytes)
  : Lemma
      (requires Some? (parse_n_offsets k front))
      (ensures (
        let Some (l, mid) = parse_n_offsets k front in
        parse_n_offsets k (FStar.List.Tot.append front rear)
        == Some (l, FStar.List.Tot.append mid rear)))
      (decreases k)
  = if k = 0 then ()
    else
      match RDF.Bytes.parse_u64_le front with
      | None -> ()
      | Some (o, front_rest) ->
        lemma_parse_u64_le_append front rear;
        match parse_n_offsets (k - 1) front_rest with
        | None -> ()
        | Some (l_tail, mid') ->
          lemma_parse_n_offsets_append (k - 1) front_rest rear

(* build_offs cons unfolding: build_offs base (t :: rest) =
   write_u64_le base ++ build_offs (base + len t) rest. *)
let lemma_build_offs_cons
  (base : nat) (t : string) (rest_tokens : list string)
  : Lemma
      (requires base < 18446744073709551616
                /\ cum_final base (t :: rest_tokens) < 18446744073709551616)
      (ensures (
        let cur' = base + String.length t in
        build_offs base (t :: rest_tokens)
        == FStar.List.Tot.append (RDF.Bytes.write_u64_le base) (build_offs cur' rest_tokens)))
  = let cur' = base + String.length t in
    lemma_cum_final_mono cur' rest_tokens;
    lemma_build_offs_acc_final base (t :: rest_tokens);
    lemma_build_offs_acc_final cur' rest_tokens;
    let (| _, rest_bytes |) = build_offs_acc cur' rest_tokens in
    let head = RDF.Bytes.write_u64_le base in
    let final = cum_final base (t :: rest_tokens) in
    Lh.lemma_append_tr_eq head rest_bytes;
    Lh.lemma_append_tr_eq (FStar.List.Tot.append head rest_bytes)
                          (RDF.Bytes.write_u64_le final);
    Lh.lemma_append_tr_eq rest_bytes (RDF.Bytes.write_u64_le final);
    Lh.lemma_append_tr_eq head
                          (FStar.List.Tot.append rest_bytes (RDF.Bytes.write_u64_le final));
    FStar.List.Tot.Properties.append_assoc head rest_bytes (RDF.Bytes.write_u64_le final)

let lemma_cum_offs_cons
  (base : nat) (t : string) (rest_tokens : list string)
  : Lemma
      (requires base < 18446744073709551616)
      (ensures (
        let cur' = base + String.length t in
        cum_offs base (t :: rest_tokens)
        == base :: cum_offs cur' rest_tokens))
  = ()

let lemma_cum_final_cons
  (base : nat) (t : string) (rest_tokens : list string)
  : Lemma
      (requires base < 18446744073709551616)
      (ensures (
        let cur' = base + String.length t in
        cum_final base (t :: rest_tokens) == cum_final cur' rest_tokens))
  = ()

(* parse_n_offsets on (build_offs base tokens ++ rest) yields the
   cumulative-offset list (n+1 entries, last = cum_final). Direct
   induction over tokens. *)
#push-options "--z3rlimit 30"
let rec lemma_parse_n_offsets_build_offs
  (base : nat) (tokens : list string) (rest : RDF.Bytes.bytes)
  : Lemma
      (requires base < 18446744073709551616
                /\ cum_final base tokens < 18446744073709551616)
      (ensures (
        parse_n_offsets (length tokens + 1)
                        (FStar.List.Tot.append (build_offs base tokens) rest)
        == Some (FStar.List.Tot.append (cum_offs base tokens) [cum_final base tokens], rest)))
      (decreases tokens)
  = match tokens with
    | [] ->
      let body : RDF.Bytes.bytes = [] in
      Lh.lemma_append_tr_eq body (RDF.Bytes.write_u64_le base);
      FStar.List.Tot.Properties.append_l_nil (RDF.Bytes.write_u64_le base);
      RDF.Bytes.lemma_parse_write_u64_le_inverse base rest
    | t :: rest_tokens ->
      let cur' = base + String.length t in
      lemma_cum_final_mono cur' rest_tokens;
      lemma_parse_n_offsets_build_offs cur' rest_tokens rest;
      lemma_build_offs_cons base t rest_tokens;
      let head = RDF.Bytes.write_u64_le base in
      let inner = build_offs cur' rest_tokens in
      FStar.List.Tot.Properties.append_assoc head inner rest;
      RDF.Bytes.lemma_parse_write_u64_le_inverse base (FStar.List.Tot.append inner rest);
      lemma_cum_offs_cons base t rest_tokens;
      lemma_cum_final_cons base t rest_tokens
#pop-options

(* The cons branch of the round-trip lemma. Strengthened precondition:
   we additionally require the cumulative sum of token data lengths to
   fit in u64. The original `data_offset < 2^64` says only that the
   START of token-data fits in u64; if `data_offset + sum_lengths`
   overflows, build_offs silently truncates and the round-trip fails.
   See the design doc for the discussion. *)
#push-options "--z3rlimit 30"
let lemma_parse_serialize_dict_cons
  (sorted_tokens : list string)
  : Lemma
      (requires (
        let n = length sorted_tokens in
        let ids_offset = header_size in
        let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
        let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
        n < 4294967296
        /\ data_offset < 18446744073709551616
        /\ cum_final data_offset sorted_tokens < 18446744073709551616))
      (ensures parse_dict (serialize_dict sorted_tokens) == Some sorted_tokens)
  = let n = length sorted_tokens in
    let ids_offset = header_size in
    let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
    let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
    let header = build_header n ids_offset tokens_offset in
    let ids = build_ids n in
    let offs = build_offs data_offset sorted_tokens in
    let data = build_data sorted_tokens in
    let offs_data = FStar.List.Tot.append offs data in
    Lh.lemma_append_tr_eq offs data;
    let ids_offs_data = FStar.List.Tot.append ids offs_data in
    Lh.lemma_append_tr_eq ids offs_data;
    Lh.lemma_append_tr_eq header ids_offs_data;
    let m_bytes = RDF.Bytes.write_u32_le dict_magic in
    let v_bytes = RDF.Bytes.write_u32_le dict_version in
    let n_bytes = RDF.Bytes.write_u32_le n in
    let p_bytes = RDF.Bytes.write_u32_le 0 in
    let i_bytes = RDF.Bytes.write_u64_le ids_offset in
    let t_bytes = RDF.Bytes.write_u64_le tokens_offset in
    let i_t = FStar.List.Tot.append i_bytes t_bytes in
    Lh.lemma_append_tr_eq i_bytes t_bytes;
    let p_i_t = FStar.List.Tot.append p_bytes i_t in
    Lh.lemma_append_tr_eq p_bytes i_t;
    let n_p_i_t = FStar.List.Tot.append n_bytes p_i_t in
    Lh.lemma_append_tr_eq n_bytes p_i_t;
    let v_n_p_i_t = FStar.List.Tot.append v_bytes n_p_i_t in
    Lh.lemma_append_tr_eq v_bytes n_p_i_t;
    Lh.lemma_append_tr_eq m_bytes v_n_p_i_t;
    let suffix1 = FStar.List.Tot.append v_n_p_i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc m_bytes v_n_p_i_t ids_offs_data;
    RDF.Bytes.lemma_parse_write_u32_le_inverse dict_magic suffix1;
    let suffix2 = FStar.List.Tot.append n_p_i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc v_bytes n_p_i_t ids_offs_data;
    RDF.Bytes.lemma_parse_write_u32_le_inverse dict_version suffix2;
    let suffix3 = FStar.List.Tot.append p_i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc n_bytes p_i_t ids_offs_data;
    RDF.Bytes.lemma_parse_write_u32_le_inverse n suffix3;
    let suffix4 = FStar.List.Tot.append i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc p_bytes i_t ids_offs_data;
    RDF.Bytes.lemma_parse_write_u32_le_inverse 0 suffix4;
    let suffix5 = FStar.List.Tot.append t_bytes ids_offs_data in
    FStar.List.Tot.Properties.append_assoc i_bytes t_bytes ids_offs_data;
    RDF.Bytes.lemma_parse_write_u64_le_inverse ids_offset suffix5;
    let suffix6 = ids_offs_data in
    RDF.Bytes.lemma_parse_write_u64_le_inverse tokens_offset suffix6;
    let after_ids = offs_data in
    FStar.List.Tot.Properties.append_assoc ids offs data;
    lemma_build_ids_length n;
    RDF.Bytes.lemma_parse_n_bytes_inverse ids after_ids;
    lemma_parse_n_offsets_build_offs data_offset sorted_tokens data;
    FStar.List.Tot.Properties.append_l_nil data;
    lemma_parse_tokens_from_offsets_build_data data_offset sorted_tokens [];
    ()
#pop-options

(* Top-level lemma. The strengthened precondition (cum_final < 2^64)
   is what the cons branch genuinely needs. *)
let lemma_parse_serialize_dict
  (sorted_tokens : list string)
  : Lemma
      (requires (let n = length sorted_tokens in
                 let ids_offset = header_size in
                 let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
                 let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
                 n < 4294967296
                 /\ data_offset < 18446744073709551616
                 /\ cum_final data_offset sorted_tokens < 18446744073709551616))
      (ensures parse_dict (serialize_dict sorted_tokens) == Some sorted_tokens)
  = match sorted_tokens with
    | [] -> lemma_parse_serialize_dict_empty_case ()
    | _ -> lemma_parse_serialize_dict_cons sorted_tokens
