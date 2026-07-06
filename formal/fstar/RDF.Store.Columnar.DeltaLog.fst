module RDF.Store.Columnar.DeltaLog

(* Durable-UPDATE delta-log entry format — stage 1 of
   docs/designissues/2026-07-06-durable-update-design.md §3.1.

   Per CLAUDE.md rule #11 and the hash-witness pattern in
   docs/designissues/2026-05-07-io-verification-and-third-party.md:
   the byte layout of every durable companion file is specified in
   F*, `Tot`, no `assume val`. This module owns *only* the pure
   byte format for one delta-log entry (and the framing around it
   that lets a reader re-synchronize after a corrupted/truncated
   tail — §3.3's crash-recovery replay story). The fsync/rename
   I/O protocol (`delta_log_append`, `delta_log_fsync`, ...) is
   stage 2 (§3.3) and is out of scope here: this module is pure,
   `Tot` throughout, no `ML` effect anywhere.

   Term encoding — deliberate divergence from the design doc's
   "reuse the existing term encoding" suggestion (§3.1): the only
   existing RDF term serializer in this tree is
   RDF.NQuads.Serialize's `nq_term_to_string`, which produces
   *escaped Turtle/N-Quads text* ("<iri>", "_:b",
   "\"lex\"^^<dt>@lang") — parsing that back would require a full
   N-Quads-literal lexer (backslash-escape unescaping, quote/angle-
   bracket scanning with no length prefixes) inside this module,
   which is exactly the "dependency tangle" the task brief's escape
   hatch anticipates. Per that escape hatch, this module defines its
   own minimal length-prefixed binary term encoding instead (tag
   byte + u32-length-prefixed UTF-8 strings, built from the same
   `RDF.Bytes` primitives DictWriter/PresenceWriter/OffsetsWriter
   already use for companion-file byte layout). If a later stage
   needs the two encodings to converge, that is a separate,
   deliberate migration — not a silent drift, since this note calls
   it out.

   On-disk framing per delta-log entry (little-endian throughout,
   mirrors the DictWriter header pattern — shared constants defined
   ONCE below, not duplicated at any call site per the 4b9fd72
   magic-drift lesson):

     [ magic    : u32   0x31454C44  ('D','L','E','1' in file order) ]
     [ version  : u32   1                                          ]
     [ length   : u32   byte length of the tag+payload section     ]
     [ payload  : length bytes  (tag byte + constructor fields)     ]
     [ checksum : u32   simple_checksum(payload)                    ]

   The checksum is a plain additive mod-2^32 check, NOT a
   cryptographic digest — it exists only to let `parse_delta_entry`
   reject a torn/corrupted individual record without decoding it,
   the same "detectable and truncatable at next-open replay" need
   §3.3 describes for a partial append-then-crash. It is a distinct
   mechanism from the sha256 hash-witness pattern (io-verification
   doc), which is the whole-log/whole-batch drift check between the
   F*-computed bytes and what actually landed on disk; that witness
   is layered on top of `serialize_delta_entry`'s output by a future
   `expected_digest`, not reimplemented here. *)

open FStar.List.Tot

module B = RDF.Bytes
module T = RDF.Term
module Tr = RDF.Triple

(* ======================================================================
   0. Shared framing constants — defined once.
   ====================================================================== *)

let delta_entry_magic   : nat = 0x31454C44  (* 'DLE1' LE: bytes 44 4C 45 31 *)
let delta_entry_version : nat = 1

(* Tag bytes. Each tag space (term / subject / entry) is a disjoint,
   small nat < 256 so a single byte suffices. *)

let term_tag_iri     : nat = 0
let term_tag_bnode    : nat = 1
let term_tag_literal  : nat = 2

let subj_tag_iri      : nat = 0
let subj_tag_bnode     : nat = 1

let de_tag_add     : nat = 0
let de_tag_remove  : nat = 1
let de_tag_clear   : nat = 2
let de_tag_drop    : nat = 3
let de_tag_create  : nat = 4

(* ======================================================================
   1. delta_entry — the five constructors from the design doc §3.1.
   ====================================================================== *)

noeq type delta_entry =
  | DE_Add    : quad:Tr.triple -> graph:option T.iri -> delta_entry
  | DE_Remove : quad:Tr.triple -> graph:option T.iri -> delta_entry
  | DE_Clear  : graph:option T.iri -> delta_entry   // None = default graph
  | DE_Drop   : graph:T.iri -> delta_entry
  | DE_Create : graph:T.iri -> delta_entry

(* ======================================================================
   2. Byte-level primitives layered on RDF.Bytes.
   ====================================================================== *)

(* --- single-byte tags --------------------------------------------------- *)

let write_u8 (n : nat{n < 256}) : Tot B.bytes =
  [B.byte_of_int n]

let parse_u8 (bs : B.bytes) : Tot (option (nat & B.bytes)) =
  match bs with
  | b :: rest -> Some (B.int_of_byte b, rest)
  | [] -> None

let lemma_u8_roundtrip (n : nat{n < 256}) (rest : B.bytes)
  : Lemma (ensures parse_u8 (append (write_u8 n) rest) == Some (n, rest))
  = ()

(* --- length-prefixed UTF-8 strings -------------------------------------

   `serialize_lstring` guards the overflow precondition defensively
   (returns [] — an unparseable sentinel — rather than failing to
   typecheck) exactly like DictWriter's `serialize_dict`; the
   round-trip lemma below states the precondition under which the
   guard is not taken. *)

let serialize_lstring (s : string) : Tot B.bytes =
  let n = String.length s in
  if n >= 4294967296 then []
  else append (B.write_u32_le n) (B.bytes_of_string s)

let parse_lstring (bs : B.bytes) : Tot (option (string & B.bytes)) =
  match B.parse_u32_le bs with
  | None -> None
  | Some (n, rest) -> B.parse_string_of_length n rest

let lemma_lstring_roundtrip (s : string) (rest : B.bytes)
  : Lemma
      (requires String.length s < 4294967296)
      (ensures parse_lstring (append (serialize_lstring s) rest) == Some (s, rest))
  = let n = String.length s in
    let u = B.write_u32_le n in
    let sb = B.bytes_of_string s in
    FStar.List.Tot.Properties.append_assoc u sb rest;
    B.lemma_parse_write_u32_le_inverse n (append sb rest);
    B.lemma_parse_string_of_length_inverse s rest

(* ======================================================================
   3. Term / subject / triple encoding.
   ====================================================================== *)

let serialize_term (t : T.rdf_term) : Tot B.bytes =
  match t with
  | T.T_IRI i -> append (write_u8 term_tag_iri) (serialize_lstring i)
  | T.T_BNode b -> append (write_u8 term_tag_bnode) (serialize_lstring b)
  | T.T_Literal l ->
    append (write_u8 term_tag_literal)
      (append (serialize_lstring l.T.lexical_form)
        (append (serialize_lstring l.T.datatype)
          (match l.T.lang_tag with
           | None -> write_u8 0
           | Some tag -> append (write_u8 1) (serialize_lstring tag))))

let parse_term (bs : B.bytes) : Tot (option (T.rdf_term & B.bytes)) =
  match parse_u8 bs with
  | None -> None
  | Some (tag, after_tag) ->
    if tag = term_tag_iri then
      match parse_lstring after_tag with
      | None -> None
      | Some (i, rest) -> if T.is_iri i then Some (T.T_IRI i, rest) else None
    else if tag = term_tag_bnode then
      match parse_lstring after_tag with
      | None -> None
      | Some (b, rest) -> Some (T.T_BNode b, rest)
    else if tag = term_tag_literal then
      match parse_lstring after_tag with
      | None -> None
      | Some (lex, after_lex) ->
        match parse_lstring after_lex with
        | None -> None
        | Some (dt, after_dt) ->
          if not (T.is_iri dt) then None
          else
            match parse_u8 after_dt with
            | None -> None
            | Some (flag, after_flag) ->
              if flag = 0 then
                let l : T.literal = { T.lexical_form = lex; T.datatype = dt; T.lang_tag = None } in
                if T.literal_wf l then Some (T.T_Literal l, after_flag) else None
              else if flag = 1 then
                match parse_lstring after_flag with
                | None -> None
                | Some (tag_str, rest) ->
                  let l : T.literal = { T.lexical_form = lex; T.datatype = dt; T.lang_tag = Some tag_str } in
                  if T.literal_wf l then Some (T.T_Literal l, rest) else None
              else None
    else None

let serialize_subject (s : T.subject) : Tot B.bytes =
  match s with
  | T.S_IRI i -> append (write_u8 subj_tag_iri) (serialize_lstring i)
  | T.S_BNode b -> append (write_u8 subj_tag_bnode) (serialize_lstring b)

let parse_subject (bs : B.bytes) : Tot (option (T.subject & B.bytes)) =
  match parse_u8 bs with
  | None -> None
  | Some (tag, after_tag) ->
    if tag = subj_tag_iri then
      match parse_lstring after_tag with
      | None -> None
      | Some (i, rest) -> if T.is_iri i then Some (T.S_IRI i, rest) else None
    else if tag = subj_tag_bnode then
      match parse_lstring after_tag with
      | None -> None
      | Some (b, rest) -> Some (T.S_BNode b, rest)
    else None

let serialize_triple (tr : Tr.triple) : Tot B.bytes =
  append (serialize_subject tr.Tr.s)
    (append (serialize_lstring tr.Tr.p) (serialize_term tr.Tr.o))

let parse_triple (bs : B.bytes) : Tot (option (Tr.triple & B.bytes)) =
  match parse_subject bs with
  | None -> None
  | Some (s, after_s) ->
    match parse_lstring after_s with
    | None -> None
    | Some (p, after_p) ->
      if not (T.is_iri p) then None
      else
        match parse_term after_p with
        | None -> None
        | Some (o, rest) -> Some ({ Tr.s = s; Tr.p = p; Tr.o = o }, rest)

(* Graph names are plain `T.iri` (an unrefined string — the default
   graph and graph-management targets are not required to satisfy
   `wf_iri`; see RDF.CottasStore.fst's own comment on the empty-IRI
   default graph). No `is_iri` check on parse. *)

let serialize_graph_opt (g : option T.iri) : Tot B.bytes =
  match g with
  | None -> write_u8 0
  | Some i -> append (write_u8 1) (serialize_lstring i)

let parse_graph_opt (bs : B.bytes) : Tot (option (option T.iri & B.bytes)) =
  match parse_u8 bs with
  | None -> None
  | Some (0, rest) -> Some (None, rest)
  | Some (1, after) ->
    (match parse_lstring after with
     | None -> None
     | Some (i, rest) -> Some (Some i, rest))
  | Some (_, _) -> None

(* ======================================================================
   4. delta_entry payload (tag + fields, no framing).
   ====================================================================== *)

let serialize_delta_entry_payload (e : delta_entry) : Tot B.bytes =
  match e with
  | DE_Add q g ->
    append (write_u8 de_tag_add) (append (serialize_triple q) (serialize_graph_opt g))
  | DE_Remove q g ->
    append (write_u8 de_tag_remove) (append (serialize_triple q) (serialize_graph_opt g))
  | DE_Clear g ->
    append (write_u8 de_tag_clear) (serialize_graph_opt g)
  | DE_Drop g ->
    append (write_u8 de_tag_drop) (serialize_lstring g)
  | DE_Create g ->
    append (write_u8 de_tag_create) (serialize_lstring g)

let parse_delta_entry_payload (bs : B.bytes) : Tot (option (delta_entry & B.bytes)) =
  match parse_u8 bs with
  | None -> None
  | Some (tag, after_tag) ->
    if tag = de_tag_add then
      match parse_triple after_tag with
      | None -> None
      | Some (q, after_q) ->
        (match parse_graph_opt after_q with
         | None -> None
         | Some (g, rest) -> Some (DE_Add q g, rest))
    else if tag = de_tag_remove then
      match parse_triple after_tag with
      | None -> None
      | Some (q, after_q) ->
        (match parse_graph_opt after_q with
         | None -> None
         | Some (g, rest) -> Some (DE_Remove q g, rest))
    else if tag = de_tag_clear then
      match parse_graph_opt after_tag with
      | None -> None
      | Some (g, rest) -> Some (DE_Clear g, rest)
    else if tag = de_tag_drop then
      match parse_lstring after_tag with
      | None -> None
      | Some (g, rest) -> Some (DE_Drop g, rest)
    else if tag = de_tag_create then
      match parse_lstring after_tag with
      | None -> None
      | Some (g, rest) -> Some (DE_Create g, rest)
    else None

(* ======================================================================
   5. Framed entry — magic + version + length + payload + checksum.
   ====================================================================== *)

(* Non-cryptographic corruption check (see module banner). Sum of
   byte values mod 2^32 — plain nat arithmetic, no bitwise fanciness,
   so the parser-side recomputation is trivially equal to the
   writer-side value for identical bytes. *)

let rec simple_checksum_acc (acc : nat) (bs : B.bytes) : Tot (n:nat{n < 4294967296}) (decreases bs) =
  match bs with
  | [] -> acc % 4294967296
  | b :: rest -> simple_checksum_acc ((acc + B.int_of_byte b) % 4294967296) rest

let simple_checksum (bs : B.bytes) : Tot (n:nat{n < 4294967296}) =
  simple_checksum_acc 0 bs

let serialize_delta_entry (e : delta_entry) : Tot B.bytes =
  let payload = serialize_delta_entry_payload e in
  let len = length payload in
  if len >= 4294967296 then []
  else
    append (B.write_u32_le delta_entry_magic)
      (append (B.write_u32_le delta_entry_version)
        (append (B.write_u32_le len)
          (append payload (B.write_u32_le (simple_checksum payload)))))

let parse_delta_entry (bs : B.bytes) : Tot (option (delta_entry & B.bytes)) =
  match B.parse_u32_le bs with
  | None -> None
  | Some (magic, after_magic) ->
    if magic <> delta_entry_magic then None
    else
      match B.parse_u32_le after_magic with
      | None -> None
      | Some (ver, after_ver) ->
        if ver <> delta_entry_version then None
        else
          match B.parse_u32_le after_ver with
          | None -> None
          | Some (len, after_len) ->
            match B.parse_n_bytes len after_len with
            | None -> None
            | Some (payload, after_payload) ->
              match B.parse_u32_le after_payload with
              | None -> None
              | Some (chk, rest) ->
                if chk <> simple_checksum payload then None
                else
                  match parse_delta_entry_payload payload with
                  | Some (e, []) -> Some (e, rest)
                  | _ -> None


(* ======================================================================
   6. Round-trip lemma — the module's whole value.
   ====================================================================== *)

(* Well-formedness bound on individual string fields. Deliberately a
   fixed constant well under 2^32 (not "whatever fits") so that (a)
   every `serialize_lstring` call in this module provably takes its
   non-guarded branch — see `lemma_lstring_length` below — and (b) the
   *sum* of the handful of fields in one delta_entry never approaches
   the u32 frame-length budget, without needing per-constructor sum
   arithmetic beyond the concrete check in `delta_entry_frame_ok`.
   256 MiB per field is generous for any real RDF term. *)

let max_field_chars : nat = 268435456  (* 2^28 *)

let term_ok (t : T.rdf_term) : bool =
  match t with
  | T.T_IRI i -> String.length i < max_field_chars
  | T.T_BNode b -> String.length b < max_field_chars
  | T.T_Literal l ->
    String.length l.T.lexical_form < max_field_chars &&
    String.length l.T.datatype < max_field_chars &&
    (match l.T.lang_tag with
     | None -> true
     | Some tg -> String.length tg < max_field_chars)

let subject_ok (s : T.subject) : bool =
  match s with
  | T.S_IRI i -> String.length i < max_field_chars
  | T.S_BNode b -> String.length b < max_field_chars

let triple_ok (tr : Tr.triple) : bool =
  subject_ok tr.Tr.s && String.length tr.Tr.p < max_field_chars && term_ok tr.Tr.o

let graph_opt_ok (g : option T.iri) : bool =
  match g with
  | None -> true
  | Some i -> String.length i < max_field_chars

let delta_entry_ok (e : delta_entry) : bool =
  match e with
  | DE_Add q g -> triple_ok q && graph_opt_ok g
  | DE_Remove q g -> triple_ok q && graph_opt_ok g
  | DE_Clear g -> graph_opt_ok g
  | DE_Drop g -> String.length g < max_field_chars
  | DE_Create g -> String.length g < max_field_chars

(* --- exact-length facts, bottom-up ------------------------------------- *)

(* `String.length` unfolds to `List.Tot.length (String.list_of_string s)`
   (FStar.String.fsti: `let strlen s = List.length (list_of_string s)`;
   `let length s = strlen s`); `RDF.Bytes.bytes_of_string` is literally
   `String.list_of_string`. Both sides normalize to the same term. *)
let lemma_bytes_of_string_length (s : string)
  : Lemma (length (B.bytes_of_string s) == String.length s)
  = ()

let lemma_lstring_length (s : string{String.length s < max_field_chars})
  : Lemma (length (serialize_lstring s) == 4 + String.length s)
  = let n = String.length s in
    let u = B.write_u32_le n in
    let sb = B.bytes_of_string s in
    FStar.List.Tot.Properties.append_length u sb;
    lemma_bytes_of_string_length s

let lemma_term_length (t : T.rdf_term{term_ok t})
  : Lemma (length (serialize_term t) <= 1 + 3 `op_Multiply` (4 + max_field_chars))
  = match t with
    | T.T_IRI i ->
      lemma_lstring_length i;
      FStar.List.Tot.Properties.append_length (write_u8 term_tag_iri) (serialize_lstring i)
    | T.T_BNode b ->
      lemma_lstring_length b;
      FStar.List.Tot.Properties.append_length (write_u8 term_tag_bnode) (serialize_lstring b)
    | T.T_Literal l ->
      let lexb = serialize_lstring l.T.lexical_form in
      let dtb = serialize_lstring l.T.datatype in
      let tailb =
        match l.T.lang_tag with
        | None -> write_u8 0
        | Some tg -> append (write_u8 1) (serialize_lstring tg) in
      lemma_lstring_length l.T.lexical_form;
      lemma_lstring_length l.T.datatype;
      (match l.T.lang_tag with
       | None -> ()
       | Some tg ->
         lemma_lstring_length tg;
         FStar.List.Tot.Properties.append_length (write_u8 1) (serialize_lstring tg));
      FStar.List.Tot.Properties.append_length dtb tailb;
      FStar.List.Tot.Properties.append_length lexb (append dtb tailb);
      FStar.List.Tot.Properties.append_length (write_u8 term_tag_literal)
        (append lexb (append dtb tailb))

(* --- round-trip, bottom-up: each layer requires the `_ok` predicate
   directly on the SOURCE value (never derived from an output length —
   the defensive `if len >= 2^32 then []` guards make that direction
   unsound: a guarded-away oversized field also serializes to length
   0, which would otherwise "prove" an oversized field is small). --- *)

let lemma_term_roundtrip (t : T.rdf_term) (rest : B.bytes)
  : Lemma
      (requires term_ok t)
      (ensures parse_term (append (serialize_term t) rest) == Some (t, rest))
  = match t with
    | T.T_IRI i ->
      lemma_lstring_roundtrip i rest;
      lemma_u8_roundtrip term_tag_iri (append (serialize_lstring i) rest)
    | T.T_BNode b ->
      lemma_lstring_roundtrip b rest;
      lemma_u8_roundtrip term_tag_bnode (append (serialize_lstring b) rest)
    | T.T_Literal l ->
      let lexb = serialize_lstring l.T.lexical_form in
      let dtb = serialize_lstring l.T.datatype in
      let tailb =
        match l.T.lang_tag with
        | None -> write_u8 0
        | Some tg -> append (write_u8 1) (serialize_lstring tg) in
      (* Innermost: the lang-tag flag/value, prefixed to `rest`. *)
      (match l.T.lang_tag with
       | None -> lemma_u8_roundtrip 0 rest
       | Some tg ->
         lemma_lstring_roundtrip tg rest;
         lemma_u8_roundtrip 1 (append (serialize_lstring tg) rest));
      (* Next layer out: datatype, prefixed to (tailb @ rest). *)
      lemma_lstring_roundtrip l.T.datatype (append tailb rest);
      FStar.List.Tot.Properties.append_assoc dtb tailb rest;
      (* Next: lexical_form, prefixed to (dtb @ (tailb @ rest)). *)
      lemma_lstring_roundtrip l.T.lexical_form (append dtb (append tailb rest));
      FStar.List.Tot.Properties.append_assoc lexb dtb (append tailb rest);
      FStar.List.Tot.Properties.append_assoc lexb (append dtb tailb) rest;
      (* Outermost: the literal tag byte. *)
      lemma_u8_roundtrip term_tag_literal (append lexb (append dtb (append tailb rest)));
      FStar.List.Tot.Properties.append_assoc (write_u8 term_tag_literal)
        (append lexb (append dtb tailb)) rest;
      (* Reconstructed literal is `l` by construction (same field
         projections); `literal_wf` holds because `l : T.wf_literal`
         already carries that refinement. *)
      T.lemma_literal_eq_refl l

let lemma_subject_roundtrip (s : T.subject) (rest : B.bytes)
  : Lemma
      (requires subject_ok s)
      (ensures parse_subject (append (serialize_subject s) rest) == Some (s, rest))
  = match s with
    | T.S_IRI i ->
      lemma_lstring_roundtrip i rest;
      lemma_u8_roundtrip subj_tag_iri (append (serialize_lstring i) rest)
    | T.S_BNode b ->
      lemma_lstring_roundtrip b rest;
      lemma_u8_roundtrip subj_tag_bnode (append (serialize_lstring b) rest)

let lemma_triple_roundtrip (tr : Tr.triple) (rest : B.bytes)
  : Lemma
      (requires triple_ok tr)
      (ensures parse_triple (append (serialize_triple tr) rest) == Some (tr, rest))
  = let sbytes = serialize_subject tr.Tr.s in
    let pbytes = serialize_lstring tr.Tr.p in
    let obytes = serialize_term tr.Tr.o in
    lemma_term_roundtrip tr.Tr.o rest;
    lemma_lstring_roundtrip tr.Tr.p (append obytes rest);
    FStar.List.Tot.Properties.append_assoc pbytes obytes rest;
    lemma_subject_roundtrip tr.Tr.s (append pbytes (append obytes rest));
    FStar.List.Tot.Properties.append_assoc sbytes pbytes (append obytes rest);
    FStar.List.Tot.Properties.append_assoc sbytes (append pbytes obytes) rest

let lemma_graph_opt_roundtrip (g : option T.iri) (rest : B.bytes)
  : Lemma
      (requires graph_opt_ok g)
      (ensures parse_graph_opt (append (serialize_graph_opt g) rest) == Some (g, rest))
  = match g with
    | None -> lemma_u8_roundtrip 0 rest
    | Some i ->
      lemma_lstring_roundtrip i rest;
      lemma_u8_roundtrip 1 (append (serialize_lstring i) rest)

(* --- delta_entry payload round-trip ------------------------------------ *)

let lemma_delta_entry_payload_roundtrip (e : delta_entry) (rest : B.bytes)
  : Lemma
      (requires delta_entry_ok e)
      (ensures parse_delta_entry_payload (append (serialize_delta_entry_payload e) rest)
               == Some (e, rest))
  = match e with
    | DE_Add q g ->
      let qbytes = serialize_triple q in
      let gbytes = serialize_graph_opt g in
      lemma_graph_opt_roundtrip g rest;
      lemma_triple_roundtrip q (append gbytes rest);
      FStar.List.Tot.Properties.append_assoc qbytes gbytes rest;
      lemma_u8_roundtrip de_tag_add (append qbytes (append gbytes rest))
    | DE_Remove q g ->
      let qbytes = serialize_triple q in
      let gbytes = serialize_graph_opt g in
      lemma_graph_opt_roundtrip g rest;
      lemma_triple_roundtrip q (append gbytes rest);
      FStar.List.Tot.Properties.append_assoc qbytes gbytes rest;
      lemma_u8_roundtrip de_tag_remove (append qbytes (append gbytes rest))
    | DE_Clear g ->
      lemma_graph_opt_roundtrip g rest;
      lemma_u8_roundtrip de_tag_clear (append (serialize_graph_opt g) rest)
    | DE_Drop g ->
      lemma_lstring_roundtrip g rest;
      lemma_u8_roundtrip de_tag_drop (append (serialize_lstring g) rest)
    | DE_Create g ->
      lemma_lstring_roundtrip g rest;
      lemma_u8_roundtrip de_tag_create (append (serialize_lstring g) rest)

(* Exact per-field length facts + explicit additive chains — spelled
   out with named lets and `assert`s (rather than leaving the SMT
   solver to compose several loose `append_length` facts on its own)
   so each step is a small, checkable arithmetic goal. A single
   generous bound (`10 * (max_field_chars + 10)`) covers every
   constructor with slack to spare, keeping the final numeric checks
   trivial regardless of which constructor's exact worst case is
   largest. *)

let payload_len_bound : nat = 10 `op_Multiply` (max_field_chars + 10)

let lemma_subject_length_bound (s : T.subject{subject_ok s})
  : Lemma (length (serialize_subject s) <= 1 + 4 + max_field_chars)
  = match s with
    | T.S_IRI i ->
      lemma_lstring_length i;
      FStar.List.Tot.Properties.append_length (write_u8 subj_tag_iri) (serialize_lstring i)
    | T.S_BNode b ->
      lemma_lstring_length b;
      FStar.List.Tot.Properties.append_length (write_u8 subj_tag_bnode) (serialize_lstring b)

let lemma_graph_opt_length_bound (g : option T.iri{graph_opt_ok g})
  : Lemma (length (serialize_graph_opt g) <= 1 + 4 + max_field_chars)
  = match g with
    | None -> ()
    | Some i ->
      lemma_lstring_length i;
      FStar.List.Tot.Properties.append_length (write_u8 1) (serialize_lstring i)

#push-options "--z3rlimit 100"
let lemma_triple_length_bound (tr : Tr.triple{triple_ok tr})
  : Lemma (length (serialize_triple tr) <= (1 + 4 + max_field_chars) + (4 + max_field_chars)
                                            + (1 + 3 `op_Multiply` (4 + max_field_chars)))
  = let sbytes = serialize_subject tr.Tr.s in
    let pbytes = serialize_lstring tr.Tr.p in
    let obytes = serialize_term tr.Tr.o in
    lemma_subject_length_bound tr.Tr.s;
    lemma_lstring_length tr.Tr.p;
    lemma_term_length tr.Tr.o;
    FStar.List.Tot.Properties.append_length pbytes obytes;
    FStar.List.Tot.Properties.append_length sbytes (append pbytes obytes);
    assert (length (serialize_triple tr) == length sbytes + length pbytes + length obytes)

let lemma_delta_entry_payload_length (e : delta_entry{delta_entry_ok e})
  : Lemma (length (serialize_delta_entry_payload e) <= payload_len_bound)
  = match e with
    | DE_Add q g ->
      let qbytes = serialize_triple q in
      let gbytes = serialize_graph_opt g in
      lemma_triple_length_bound q;
      lemma_graph_opt_length_bound g;
      FStar.List.Tot.Properties.append_length qbytes gbytes;
      FStar.List.Tot.Properties.append_length (write_u8 de_tag_add) (append qbytes gbytes);
      assert (length (serialize_delta_entry_payload e) == 1 + length qbytes + length gbytes)
    | DE_Remove q g ->
      let qbytes = serialize_triple q in
      let gbytes = serialize_graph_opt g in
      lemma_triple_length_bound q;
      lemma_graph_opt_length_bound g;
      FStar.List.Tot.Properties.append_length qbytes gbytes;
      FStar.List.Tot.Properties.append_length (write_u8 de_tag_remove) (append qbytes gbytes);
      assert (length (serialize_delta_entry_payload e) == 1 + length qbytes + length gbytes)
    | DE_Clear g ->
      lemma_graph_opt_length_bound g;
      FStar.List.Tot.Properties.append_length (write_u8 de_tag_clear) (serialize_graph_opt g);
      assert (length (serialize_delta_entry_payload e) == 1 + length (serialize_graph_opt g))
    | DE_Drop g ->
      lemma_lstring_length g;
      FStar.List.Tot.Properties.append_length (write_u8 de_tag_drop) (serialize_lstring g);
      assert (length (serialize_delta_entry_payload e) == 1 + length (serialize_lstring g))
    | DE_Create g ->
      lemma_lstring_length g;
      FStar.List.Tot.Properties.append_length (write_u8 de_tag_create) (serialize_lstring g);
      assert (length (serialize_delta_entry_payload e) == 1 + length (serialize_lstring g))
#pop-options

(* --- framed round-trip (the top-level, exported guarantee) ------------ *)

(* Well-formedness precondition for the whole framed entry: every
   string field is within `max_field_chars`. This is what a real
   caller checks once (any actual RDF term is nowhere near 256 MiB);
   under it, `delta_entry_frame_ok` — the guard `serialize_delta_entry`
   itself branches on — always holds, by the concrete arithmetic
   bound `lemma_delta_entry_payload_length` establishes. *)

let delta_entry_frame_ok (e : delta_entry) : bool =
  length (serialize_delta_entry_payload e) < 4294967296

let lemma_delta_entry_frame_ok (e : delta_entry{delta_entry_ok e})
  : Lemma (delta_entry_frame_ok e)
  = lemma_delta_entry_payload_length e

(* parse_delta_entry (serialize_delta_entry e ++ rest) == Some (e, rest)

   This is the module's whole value: any bytes `serialize_delta_entry`
   produces, followed by arbitrary trailing bytes from the rest of the
   log stream, parse back to exactly `e` and the untouched trailing
   bytes — never a different entry, never a partial decode. *)
let lemma_delta_entry_roundtrip (e : delta_entry) (rest : B.bytes)
  : Lemma
      (requires delta_entry_ok e)
      (ensures parse_delta_entry (append (serialize_delta_entry e) rest) == Some (e, rest))
  = lemma_delta_entry_frame_ok e;
    let payload = serialize_delta_entry_payload e in
    let len = length payload in
    let magic_b = B.write_u32_le delta_entry_magic in
    let ver_b = B.write_u32_le delta_entry_version in
    let len_b = B.write_u32_le len in
    let chk_b = B.write_u32_le (simple_checksum payload) in
    let tail0 = append ver_b (append len_b (append payload chk_b)) in
    let tail1 = append len_b (append payload chk_b) in
    let tail2 = append payload chk_b in
    FStar.List.Tot.Properties.append_assoc magic_b tail0 rest;
    B.lemma_parse_write_u32_le_inverse delta_entry_magic (append tail0 rest);
    FStar.List.Tot.Properties.append_assoc ver_b tail1 rest;
    B.lemma_parse_write_u32_le_inverse delta_entry_version (append tail1 rest);
    FStar.List.Tot.Properties.append_assoc len_b tail2 rest;
    B.lemma_parse_write_u32_le_inverse len (append tail2 rest);
    FStar.List.Tot.Properties.append_assoc payload chk_b rest;
    B.lemma_parse_n_bytes_inverse payload (append chk_b rest);
    B.lemma_parse_write_u32_le_inverse (simple_checksum payload) rest;
    lemma_delta_entry_payload_roundtrip e [];
    FStar.List.Tot.Properties.append_l_nil payload
