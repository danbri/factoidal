module RDF.Store.Columnar.DeltaLog

(* Durable-UPDATE delta-log entry format — stage 1 of
   docs/designissues/2026-07-06-durable-update-design.md §3.1, EXTENDED
   with stage 2 (§3.3: the delta-log FILE, atomic append, crash safety).

   Per CLAUDE.md rule #11 and the hash-witness pattern in
   docs/designissues/2026-05-07-io-verification-and-third-party.md:
   the byte layout of every durable companion file is specified in
   F*, `Tot`, no `assume val`. Section 1-6 below (stage 1, unchanged)
   own *only* the pure byte format for one delta-log entry (and the
   framing around it that lets a reader re-synchronize after a
   corrupted/truncated tail — §3.3's crash-recovery replay story).
   Sections 7+ (stage 2, this extension) add: the `delta_batch`
   record (§3.1's original sketch, deferred out of stage 1's scope),
   its own framing distinct from the per-entry framing above, a
   log-file header, `serialize_log`/`parse_log` streaming over
   `parse_delta_entry` batch-by-batch, a round-trip lemma extending
   stage 1's to the whole log, and — at the very end — the five
   `ML`-effect `assume val`s that are the actual fsync/rename I/O
   boundary (§3.3's protocol). Everything above that final section
   remains pure `Tot`; the module's ONLY `ML` surface is those five
   declarations.

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
open FStar.All

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

(* `noextract`: this constant is a proof-only bound (only referenced by
   `lemma_delta_entry_payload_length`'s `ensures` clause below, a Lemma —
   erased at extraction, never called at runtime). Its VALUE
   (10 * (2^28 + 10) ≈ 2.68e9) exceeds krml's default 32-bit
   `krml_checked_int_t` compat-mode range for `Prims.nat`
   (`formal/karamel/include/krml/internal/compat.h`), which would abort
   `krmlinit_globals()` with a spurious overflow at C-program startup if
   this were extracted as a global — a KaRaMeL-compat-only concern (OCaml
   `int` is 63-bit and never had this problem). `noextract` drops it from
   both extraction targets; nothing outside this module references it
   (grepped), and the lemma it appears in continues to verify against the
   same literal arithmetic either way. *)
noextract
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

(* ======================================================================
   7. delta_batch — one committed batch of ops (§3.1's original
   sketch, deferred out of stage 1's scope). A batch groups the ops
   belonging to one SPARQL Update request under a monotonic sequence
   number (`db_seq` — the log's total order) and a compaction epoch
   (`db_epoch` — §3.3 step 5's "compacted through epoch N" skip-on-
   replay guard). Batch framing has its OWN magic/version, distinct
   from the per-entry framing above (section 5), so a reader can
   tell "this looks like a batch header" from "this looks like a
   bare entry" even in a corrupted stream where the two might
   otherwise be confused.
   ====================================================================== *)

noeq type delta_batch = {
  db_seq   : nat;
  db_epoch : nat;
  db_ops   : list delta_entry;
}

let delta_batch_magic   : nat = 0x31424C44  (* 'DLB1' LE: bytes 44 4C 42 31 *)
let delta_batch_version : nat = 1

(* --- ops list: N delta_entries back to back, reusing section 5's
   per-entry framing/checksum unchanged (each op is independently
   re-synchronizable, same crash-recovery property section 5 already
   established). --------------------------------------------------- *)

let rec serialize_ops (ops : list delta_entry) : Tot B.bytes (decreases ops) =
  match ops with
  | [] -> []
  | e :: rest -> append (serialize_delta_entry e) (serialize_ops rest)

let rec parse_n_delta_entries (n : nat) (bs : B.bytes)
  : Tot (option (list delta_entry & B.bytes)) (decreases n) =
  if n = 0 then Some ([], bs)
  else
    match parse_delta_entry bs with
    | None -> None
    | Some (e, rest) ->
      (match parse_n_delta_entries (n - 1) rest with
       | None -> None
       | Some (es, rest2) -> Some (e :: es, rest2))

(* --- batch well-formedness -------------------------------------------

   `db_seq`/`db_epoch` bounded to fit `write_u64_le`'s precondition;
   `db_ops`' count and total serialized size bounded to fit the u32
   frame-length field, mirroring `delta_entry_ok`/`delta_entry_frame_ok`
   above (section 6). Computed directly against the batch's actual op
   list (not derived from a separate small-field bound) since a
   batch's op count is the real scaling knob here — the design doc's
   §4.2 sizes an uncompacted delta at "thousands to low tens of
   thousands" of entries, nowhere near the u32 boundary. *)

let rec delta_batch_ops_ok (ops : list delta_entry) : bool =
  match ops with
  | [] -> true
  | e :: rest -> delta_entry_ok e && delta_batch_ops_ok rest

(* `u64_max_nat`: 2^64 - 1, spelled as `<= u64_max_nat` rather than the
   more obvious `< 18446744073709551616` (2^64) below. Semantically
   identical for a `nat` (`n < 2^64 <=> n <= 2^64 - 1`), but the literal
   2^64 itself cannot be written as a plain C integer constant at all —
   it is one past `ULLONG_MAX`, the largest value any standard C integer
   type (signed or unsigned, up to 64-bit) can hold, so a KaRaMeL-
   extracted C build silently mis-parses that literal at the call site
   (confirmed empirically: `gcc -Wall` on the krml-extracted build warns
   "integer constant is too large for its type" here and nowhere else in
   this module, and the check evaluates wrong at runtime as a result).
   2^64 - 1 has no such problem — it fits exactly in `unsigned long
   long`/`uint64_t`, so it extracts correctly to every backend (OCaml,
   krml/C) instead of just OCaml. See
   tools/karamel-c-build.sh --group-c and its dry-run history for the
   krml reproduction. *)
let u64_max_nat : nat = 18446744073709551615

let delta_batch_ok (b : delta_batch) : bool =
  b.db_seq <= u64_max_nat &&
  b.db_epoch <= u64_max_nat &&
  length b.db_ops < 4294967296 &&
  delta_batch_ops_ok b.db_ops &&
  length (serialize_ops b.db_ops) < 4294967276  (* 2^32 - 20: seq(8)+epoch(8)+count(4) header *)

(* --- serialize / parse: body (seq+epoch+count+ops, no outer frame) --- *)

let serialize_delta_batch_body (b : delta_batch) : Tot B.bytes =
  if b.db_seq > u64_max_nat || b.db_epoch > u64_max_nat
     || length b.db_ops >= 4294967296
  then []
  else
    append (B.write_u64_le b.db_seq)
      (append (B.write_u64_le b.db_epoch)
        (append (B.write_u32_le (length b.db_ops)) (serialize_ops b.db_ops)))

let parse_delta_batch_body (bs : B.bytes) : Tot (option (delta_batch & B.bytes)) =
  match B.parse_u64_le bs with
  | None -> None
  | Some (sq, after_seq) ->
    (match B.parse_u64_le after_seq with
     | None -> None
     | Some (ep, after_epoch) ->
       (match B.parse_u32_le after_epoch with
        | None -> None
        | Some (n, after_n) ->
          (match parse_n_delta_entries n after_n with
           | None -> None
           | Some (ops, rest) -> Some ({ db_seq = sq; db_epoch = ep; db_ops = ops }, rest))))

(* --- serialize / parse: full framed batch (magic+version+length+
   body+checksum — same shape as section 5's entry framing, one level
   up) ------------------------------------------------------------- *)

let serialize_delta_batch (b : delta_batch) : Tot B.bytes =
  let body = serialize_delta_batch_body b in
  let len = length body in
  if len >= 4294967296 then []
  else
    append (B.write_u32_le delta_batch_magic)
      (append (B.write_u32_le delta_batch_version)
        (append (B.write_u32_le len)
          (append body (B.write_u32_le (simple_checksum body)))))

let parse_delta_batch (bs : B.bytes) : Tot (option (delta_batch & B.bytes)) =
  match B.parse_u32_le bs with
  | None -> None
  | Some (magic, after_magic) ->
    if magic <> delta_batch_magic then None
    else
      (match B.parse_u32_le after_magic with
       | None -> None
       | Some (ver, after_ver) ->
         if ver <> delta_batch_version then None
         else
           (match B.parse_u32_le after_ver with
            | None -> None
            | Some (len, after_len) ->
              (match B.parse_n_bytes len after_len with
               | None -> None
               | Some (body, after_body) ->
                 (match B.parse_u32_le after_body with
                  | None -> None
                  | Some (chk, rest) ->
                    if chk <> simple_checksum body then None
                    else
                      (match parse_delta_batch_body body with
                       | Some (b, []) -> Some (b, rest)
                       | _ -> None)))))

(* ======================================================================
   8. Batch round-trip lemmas — same proof shape as section 6,
   composed bottom-up: ops-list, then body, then the full frame.
   ====================================================================== *)

let rec lemma_ops_roundtrip (ops : list delta_entry) (rest : B.bytes)
  : Lemma
      (requires delta_batch_ops_ok ops)
      (ensures parse_n_delta_entries (length ops) (append (serialize_ops ops) rest) == Some (ops, rest))
      (decreases ops)
  = match ops with
    | [] -> ()
    | e :: more ->
      let more_bytes = serialize_ops more in
      lemma_delta_entry_roundtrip e (append more_bytes rest);
      FStar.List.Tot.Properties.append_assoc (serialize_delta_entry e) more_bytes rest;
      lemma_ops_roundtrip more rest

(* Reuse RDF.Bytes's own `lemma_write_u64_le_decompose` (write_u64_le n
   == write_u32_le lo @ write_u32_le hi, lo/hi the 32-bit halves)
   rather than unfolding the raw 8-element list literal — `write_u32_le`
   already carries a `{length b == 4}` refinement in its return type,
   so `append_length` gives 4+4=8 with no further reduction needed. *)
let lemma_write_u64_le_length (n : nat{n < 18446744073709551616})
  : Lemma (length (B.write_u64_le n) == 8)
  = B.lemma_write_u64_le_decompose n;
    FStar.List.Tot.Properties.append_length
      (B.write_u32_le (n % 4294967296)) (B.write_u32_le (n / 4294967296))

let lemma_batch_body_length (b : delta_batch{delta_batch_ok b})
  : Lemma (length (serialize_delta_batch_body b) == 20 + length (serialize_ops b.db_ops))
  = let seqb = B.write_u64_le b.db_seq in
    let epochb = B.write_u64_le b.db_epoch in
    let nb = B.write_u32_le (length b.db_ops) in
    let opsb = serialize_ops b.db_ops in
    lemma_write_u64_le_length b.db_seq;
    lemma_write_u64_le_length b.db_epoch;
    FStar.List.Tot.Properties.append_length nb opsb;
    FStar.List.Tot.Properties.append_length epochb (append nb opsb);
    FStar.List.Tot.Properties.append_length seqb (append epochb (append nb opsb))

let lemma_delta_batch_frame_ok (b : delta_batch{delta_batch_ok b})
  : Lemma (length (serialize_delta_batch_body b) < 4294967296)
  = lemma_batch_body_length b

let lemma_delta_batch_body_roundtrip (b : delta_batch)
  : Lemma
      (requires delta_batch_ok b)
      (ensures parse_delta_batch_body (serialize_delta_batch_body b) == Some (b, []))
  = let n = length b.db_ops in
    let opsb = serialize_ops b.db_ops in
    let nb = B.write_u32_le n in
    lemma_ops_roundtrip b.db_ops [];
    FStar.List.Tot.Properties.append_l_nil opsb;
    B.lemma_parse_write_u32_le_inverse n opsb;
    FStar.List.Tot.Properties.append_assoc nb opsb [];
    B.lemma_parse_write_u64_le_inverse b.db_epoch (append nb opsb);
    FStar.List.Tot.Properties.append_assoc (B.write_u64_le b.db_epoch) nb opsb;
    B.lemma_parse_write_u64_le_inverse b.db_seq
      (append (B.write_u64_le b.db_epoch) (append nb opsb))

#push-options "--z3rlimit 300"
let lemma_delta_batch_roundtrip (b : delta_batch) (rest : B.bytes)
  : Lemma
      (requires delta_batch_ok b)
      (ensures parse_delta_batch (append (serialize_delta_batch b) rest) == Some (b, rest))
  = lemma_delta_batch_frame_ok b;
    let body = serialize_delta_batch_body b in
    let len = length body in
    let magic_b = B.write_u32_le delta_batch_magic in
    let ver_b = B.write_u32_le delta_batch_version in
    let len_b = B.write_u32_le len in
    let chk_b = B.write_u32_le (simple_checksum body) in
    let tail0 = append ver_b (append len_b (append body chk_b)) in
    let tail1 = append len_b (append body chk_b) in
    let tail2 = append body chk_b in
    FStar.List.Tot.Properties.append_assoc magic_b tail0 rest;
    B.lemma_parse_write_u32_le_inverse delta_batch_magic (append tail0 rest);
    FStar.List.Tot.Properties.append_assoc ver_b tail1 rest;
    B.lemma_parse_write_u32_le_inverse delta_batch_version (append tail1 rest);
    FStar.List.Tot.Properties.append_assoc len_b tail2 rest;
    B.lemma_parse_write_u32_le_inverse len (append tail2 rest);
    FStar.List.Tot.Properties.append_assoc body chk_b rest;
    B.lemma_parse_n_bytes_inverse body (append chk_b rest);
    B.lemma_parse_write_u32_le_inverse (simple_checksum body) rest;
    lemma_delta_batch_body_roundtrip b;
    FStar.List.Tot.Properties.append_l_nil body
#pop-options

(* ======================================================================
   9. The log file — header, once, then batches back to back.

   [ log_magic   : u32  0x474F4C44 ('DLOG')            ]
   [ log_version : u32  1                              ]
   [ batch_0 (section 7 framing) ]
   [ batch_1 (section 7 framing) ]
   ...

   `parse_log_batches` streams over the tail: it decodes as many
   WHOLE, checksum-valid batches as it can and stops — without
   erroring — at the first byte that doesn't start a complete batch
   frame. That "accept a prefix, never a torn entry" contract is
   exactly what §3.3's crash-recovery story needs: a process killed
   mid-append leaves a torn tail batch (bad length/checksum/magic),
   which `parse_delta_batch` rejects, so `parse_log_batches` simply
   stops there and returns every batch fully committed before the
   crash, plus the raw undecoded suffix (for a caller that wants to
   report/discard it, not for this module to interpret).
   ====================================================================== *)

let delta_log_magic   : nat = 0x474F4C44  (* 'DLOG' LE: bytes 44 4C 4F 47 *)
let delta_log_version : nat = 1

let serialize_log_header : B.bytes =
  append (B.write_u32_le delta_log_magic) (B.write_u32_le delta_log_version)

let parse_log_header (bs : B.bytes) : Tot (option B.bytes) =
  match B.parse_u32_le bs with
  | None -> None
  | Some (magic, after_magic) ->
    if magic <> delta_log_magic then None
    else
      (match B.parse_u32_le after_magic with
       | None -> None
       | Some (ver, rest) -> if ver <> delta_log_version then None else Some rest)

let lemma_log_header_roundtrip (rest : B.bytes)
  : Lemma (parse_log_header (append serialize_log_header rest) == Some rest)
  = let magic_b = B.write_u32_le delta_log_magic in
    let ver_b = B.write_u32_le delta_log_version in
    FStar.List.Tot.Properties.append_assoc magic_b ver_b rest;
    B.lemma_parse_write_u32_le_inverse delta_log_magic (append ver_b rest);
    B.lemma_parse_write_u32_le_inverse delta_log_version rest

(* --- shrink lemma: parsing a batch strictly consumes bytes, the
   structural-recursion measure `parse_log_batches` needs. Walks the
   same nested-match cascade as `parse_delta_batch` itself so each
   `B.parse_u32_le`/`B.parse_n_bytes` call's length fact lines up
   with the corresponding step there; the final checksum/body check
   is irrelevant to the length arithmetic, so this establishes the
   bound whether or not `parse_delta_batch` ultimately returns
   `Some` or falls through to `None` on that check (the `None` arm
   of this lemma's own conclusion is trivially true either way). --- *)

let lemma_parse_u32_le_length (bs : B.bytes)
  : Lemma (match B.parse_u32_le bs with
           | Some (_, rest) -> length bs == length rest + 4
           | None -> True)
  = match bs with
    | _ :: _ :: _ :: _ :: _ -> ()
    | _ -> ()

let rec lemma_parse_n_bytes_length (n : nat) (bs : B.bytes)
  : Lemma (ensures (match B.parse_n_bytes n bs with
                     | Some (_, rest) -> length bs == length rest + n
                     | None -> True))
          (decreases n)
  = if n = 0 then ()
    else
      match bs with
      | [] -> ()
      | _ :: rest -> lemma_parse_n_bytes_length (n - 1) rest

let lemma_parse_delta_batch_shrinks (bs : B.bytes)
  : Lemma (match parse_delta_batch bs with
           | Some (_, rest) -> length rest < length bs
           | None -> True)
  = match B.parse_u32_le bs with
    | None -> ()
    | Some (magic, after_magic) ->
      lemma_parse_u32_le_length bs;
      if magic <> delta_batch_magic then ()
      else
        (match B.parse_u32_le after_magic with
         | None -> ()
         | Some (ver, after_ver) ->
           lemma_parse_u32_le_length after_magic;
           if ver <> delta_batch_version then ()
           else
             (match B.parse_u32_le after_ver with
              | None -> ()
              | Some (len, after_len) ->
                lemma_parse_u32_le_length after_ver;
                (match B.parse_n_bytes len after_len with
                 | None -> ()
                 | Some (body, after_body) ->
                   lemma_parse_n_bytes_length len after_len;
                   (match B.parse_u32_le after_body with
                    | None -> ()
                    | Some (chk, rest) -> lemma_parse_u32_le_length after_body))))

let rec parse_log_batches (bs : B.bytes) : Tot (list delta_batch & B.bytes) (decreases (length bs)) =
  match parse_delta_batch bs with
  | None -> ([], bs)
  | Some (b, rest) ->
    lemma_parse_delta_batch_shrinks bs;
    let (more, tail) = parse_log_batches rest in
    (b :: more, tail)

let rec serialize_delta_batches (bs : list delta_batch) : Tot B.bytes (decreases bs) =
  match bs with
  | [] -> []
  | b :: rest -> append (serialize_delta_batch b) (serialize_delta_batches rest)

let rec delta_batches_ok (bs : list delta_batch) : bool =
  match bs with
  | [] -> true
  | b :: rest -> delta_batch_ok b && delta_batches_ok rest

let serialize_log (bs : list delta_batch) : Tot B.bytes =
  append serialize_log_header (serialize_delta_batches bs)

let parse_log (bs : B.bytes) : Tot (option (list delta_batch & B.bytes)) =
  match parse_log_header bs with
  | None -> None
  | Some rest -> Some (parse_log_batches rest)

(* ======================================================================
   10. The log round-trip lemma — extends section 8's single-batch
   lemma to a whole log: appending a list of well-formed batches
   after the header and parsing the result back recovers exactly
   those batches, in order, with nothing left over. This is stage
   2's whole value, the direct analogue of section 6's
   `lemma_delta_entry_roundtrip` one layer up the format.
   ====================================================================== *)

let rec lemma_parse_log_batches_roundtrip (bs : list delta_batch)
  : Lemma
      (requires delta_batches_ok bs)
      (ensures parse_log_batches (serialize_delta_batches bs) == (bs, []))
      (decreases bs)
  = match bs with
    | [] -> ()
    | b :: rest ->
      let rest_bytes = serialize_delta_batches rest in
      lemma_delta_batch_roundtrip b rest_bytes;
      lemma_parse_log_batches_roundtrip rest

let lemma_log_roundtrip (bs : list delta_batch)
  : Lemma
      (requires delta_batches_ok bs)
      (ensures parse_log (serialize_log bs) == Some (bs, []))
  = let batch_bytes = serialize_delta_batches bs in
    lemma_log_header_roundtrip batch_bytes;
    lemma_parse_log_batches_roundtrip bs

(* ======================================================================
   11. Hash-witness surface (io-verification doc pattern) — thin by
   design. This module exposes only the BYTES to hash
   (`expected_digest_bytes`), not a call to `sha256` itself.

   Why: the project's only wired sha256 realisation is
   `Fstar_pure_hashes.sha256` (issue #63's patch, applied to
   SPARQL11_Algebra.ml / RDF_Canonical.ml). `build-ocaml.sh`'s
   hardcoded native-compile order links `fstar_pure_hashes.ml`
   *after* `RDF_Store_Columnar_DeltaLog.ml` (see the `.ml` compile
   list: "RDF_Store_Columnar_OffsetIndex.ml RDF_Store_Columnar_DeltaLog.ml"
   appears well before "fstar_pure_hashes.ml"). An `assume val
   hash_sha256` realised in THIS module would need
   `Fstar_pure_hashes` available at THIS module's compile step,
   which the current link order does not provide — and this task's
   brief instructs not to edit build-ocaml.sh's registration/compile
   order. Rather than duplicate the ~90-line SHA-256 implementation
   into a second glue patch (drift risk with zero benefit), the
   hash-witness comparison happens one layer up: the crash harness /
   unit test calls the ALREADY-wired `Fstar_pure_hashes.sha256`
   directly on the bytes this function produces, and compares against
   `Fstar_pure_hashes.sha256` of the on-disk bytes read back after a
   real append+fsync+read cycle. Same property the io-verification
   doc's pattern asks for (F*-computed bytes hashed and compared
   against on-disk bytes hashed) — the hash call itself just lives at
   the test-driver layer instead of inside this `Tot` module. If
   `fstar_pure_hashes.ml`'s link position ever moves earlier than
   this module's, inlining a real `assume val hash_sha256` call here
   is the natural follow-up.
   ====================================================================== *)

val expected_digest_bytes : delta_batch -> Tot B.bytes
let expected_digest_bytes b = serialize_delta_batch b

(* ======================================================================
   12. The fsync/rename atomicity protocol (§3.3) — the ONLY `ML`
   surface in this module. Five assume vals, all pure I/O per rule
   #11(a): no branching on delta_batch contents beyond "write these
   bytes then fsync" / "rename this path" / "read this whole file
   back". The *decision* of what bytes to write (`serialize_log`,
   `serialize_delta_batch`, `serialize_log_header`, all `Tot` above)
   and the commit-sequence prose (append -> fsync -> report success
   -> ... -> compaction's rename + fsync_dir) both live in the design
   doc's §3.3, not re-encoded here as executable logic.

   Realised in
   formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/NNN_delta_log_io.sh
   (NNN: open-issue number TBD — see this task's report) with plain
   OCaml `Unix` I/O: `Unix.openfile` + `O_APPEND` writes for
   `delta_log_append`, `Unix.fsync` for `delta_log_fsync`/`fsync_dir`,
   `Unix.rename` for `atomic_rename`, and a whole-file read for
   `delta_log_read_all`. *)

assume val delta_log_append   : path:string -> bytes:B.bytes -> ML unit
assume val delta_log_fsync    : path:string -> ML unit
assume val delta_log_read_all : path:string -> ML B.bytes
assume val atomic_rename      : from_path:string -> to_path:string -> ML unit
assume val fsync_dir          : path:string -> ML unit

(* ======================================================================
   13. Compacted-epoch companion file — stage 4 (compaction), durable-
   update-design.md §3.3 step 5 / open decision 6.

   Disclosed decision (open decision 6): a SEPARATE companion file
   (`data.compacted-epoch`, sitting next to a compacted `.cottas` base,
   this format), NOT a header field folded into an existing sidecar --
   picked so the compactor never has to understand/rewrite an existing
   sidecar's own format to record this one small fact, and so a reader
   indifferent to compaction (pycottas, `factoidal --explain`, etc.)
   never has to parse it. Same magic+version+length+checksum framing
   shape as sections 5/7 above.

   Semantics: the value recorded is "every delta_batch with db_epoch
   <= this value has ALREADY been folded into this base and MUST be
   skipped on replay" -- the crash-recovery idempotence guard for the
   window between a compaction's base-rename and its delta-log
   truncation (design doc §3.3 step 5's own prose: "a batch whose
   epoch is at or below the base file's own recorded 'compacted
   through epoch N' marker ... is skipped on replay rather than
   re-applied"). `filter_batches_since_epoch` below is that skip,
   applied wherever a parsed batch list is about to be folded
   (SPARQL11.Store.fst's `cottas_with_delta_dataset_backend`).

   Caller contract (stated here since this is the one place both
   producer and consumer of the value meet): a writer appending a
   NEW batch after a compaction has recorded epoch CE must stamp that
   batch's own `db_epoch` as CE+1 or higher, or the batch will be
   silently treated as already-folded and ignored at merge-on-read
   time -- a disclosed sharp edge, not a silent-wrong-answer risk,
   since "wrongly skip a stale-tagged write" is the safe failure
   direction (never double-applies a write), not the dangerous one. *)

let compacted_epoch_magic   : nat = 0x31504543  (* 'CEP1' LE: bytes 43 45 50 31 *)
let compacted_epoch_version : nat = 1

let serialize_compacted_epoch (n : nat{n < 18446744073709551616}) : Tot B.bytes =
  let body = B.write_u64_le n in
  let len = length body in
  append (B.write_u32_le compacted_epoch_magic)
    (append (B.write_u32_le compacted_epoch_version)
      (append (B.write_u32_le len)
        (append body (B.write_u32_le (simple_checksum body)))))

let parse_compacted_epoch (bs : B.bytes) : Tot (option nat) =
  match B.parse_u32_le bs with
  | None -> None
  | Some (magic, after_magic) ->
    if magic <> compacted_epoch_magic then None
    else
      match B.parse_u32_le after_magic with
      | None -> None
      | Some (ver, after_ver) ->
        if ver <> compacted_epoch_version then None
        else
          match B.parse_u32_le after_ver with
          | None -> None
          | Some (len, after_len) ->
            match B.parse_n_bytes len after_len with
            | None -> None
            | Some (body, after_body) ->
              match B.parse_u32_le after_body with
              | None -> None
              | Some (chk, _rest) ->
                if chk <> simple_checksum body then None
                else
                  (match B.parse_u64_le body with
                   | Some (n, []) -> Some n
                   | _ -> None)

#push-options "--z3rlimit 200"
let lemma_compacted_epoch_roundtrip (n : nat{n < 18446744073709551616})
  : Lemma (parse_compacted_epoch (serialize_compacted_epoch n) == Some n)
  = let body = B.write_u64_le n in
    let len = length body in
    lemma_write_u64_le_length n;
    let magic_b = B.write_u32_le compacted_epoch_magic in
    let ver_b = B.write_u32_le compacted_epoch_version in
    let len_b = B.write_u32_le len in
    let chk_b = B.write_u32_le (simple_checksum body) in
    let tail0 = append ver_b (append len_b (append body chk_b)) in
    let tail1 = append len_b (append body chk_b) in
    let tail2 = append body chk_b in
    FStar.List.Tot.Properties.append_assoc magic_b tail0 [];
    FStar.List.Tot.Properties.append_l_nil tail0;
    B.lemma_parse_write_u32_le_inverse compacted_epoch_magic tail0;
    FStar.List.Tot.Properties.append_assoc ver_b tail1 [];
    FStar.List.Tot.Properties.append_l_nil tail1;
    B.lemma_parse_write_u32_le_inverse compacted_epoch_version tail1;
    FStar.List.Tot.Properties.append_assoc len_b tail2 [];
    FStar.List.Tot.Properties.append_l_nil tail2;
    B.lemma_parse_write_u32_le_inverse len tail2;
    FStar.List.Tot.Properties.append_assoc body chk_b [];
    FStar.List.Tot.Properties.append_l_nil chk_b;
    FStar.List.Tot.Properties.append_l_nil body;
    B.lemma_parse_n_bytes_inverse body chk_b;
    B.lemma_parse_write_u32_le_inverse (simple_checksum body) [];
    B.lemma_parse_write_u64_le_inverse n []
#pop-options

(* ======================================================================
   14. Epoch-skip filter — the fold_delta_batches input, filtered.
   Pure `Tot`, no I/O; called once at store-open/refresh time with
   whatever `parse_compacted_epoch` returned for the live base's
   companion file (`None` if the store has never been compacted --
   nothing to skip, every batch is fresh). *)

let rec filter_batches_since_epoch (threshold : option nat) (batches : list delta_batch)
  : Tot (list delta_batch) (decreases batches) =
  match batches with
  | [] -> []
  | b :: rest ->
    let keep = match threshold with
      | None -> true
      | Some ce -> b.db_epoch > ce
    in
    if keep
    then b :: filter_batches_since_epoch threshold rest
    else filter_batches_since_epoch threshold rest
