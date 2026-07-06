(* delta_log_roundtrip.ml — round-trip witness for the durable-UPDATE
   delta-log entry format.

   serialize_delta_entry / parse_delta_entry in
   formal/fstar/RDF.Store.Columnar.DeltaLog.fst are proved inverses
   (lemma_delta_entry_roundtrip, under the delta_entry_ok precondition
   that every string field stays under max_field_chars — any real RDF
   term). This test exercises that property empirically at the
   extracted-OCaml layer: every constructor, corner-case string
   content (empty, non-ASCII UTF-8, long literals, datatype+langtag,
   blank nodes), framing corruption (truncated / bad magic / bad
   checksum / bad version must all parse to None, never a wrong
   entry), and a multi-entry stream.

   Per docs/designissues/2026-07-06-durable-update-design.md's stage-1
   task: this is the module's whole value made empirical. Stage 2
   (fsync/rename I/O) is out of scope — nothing here touches disk. *)

let passed = ref 0
let failed = ref 0

let check ~name ok =
  if ok then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

(* --- fixture builders --------------------------------------------------- *)

let iri s : RDF_Term.wf_iri = s   (* caller supplies a colon-bearing string *)

let lit ?lang ~datatype lex : RDF_Term.rdf_term =
  RDF_Term.T_Literal { RDF_Term.lexical_form = lex; RDF_Term.datatype = datatype;
                        RDF_Term.lang_tag = lang }

let plain_lit lex : RDF_Term.rdf_term = lit ~datatype:RDF_Term.xsd_string lex

let lang_lit lex tag : RDF_Term.rdf_term =
  lit ~lang:tag ~datatype:RDF_Term.rdf_lang_string lex

let triple s p o : RDF_Triple.triple =
  { RDF_Triple.s; RDF_Triple.p = p; RDF_Triple.o = o }

(* --- round-trip + corruption assertion helpers -------------------------- *)

let entry_name (e : RDF_Store_Columnar_DeltaLog.delta_entry) : string =
  match e with
  | RDF_Store_Columnar_DeltaLog.DE_Add _ -> "DE_Add"
  | RDF_Store_Columnar_DeltaLog.DE_Remove _ -> "DE_Remove"
  | RDF_Store_Columnar_DeltaLog.DE_Clear _ -> "DE_Clear"
  | RDF_Store_Columnar_DeltaLog.DE_Drop _ -> "DE_Drop"
  | RDF_Store_Columnar_DeltaLog.DE_Create _ -> "DE_Create"

(* Round-trip an entry with an arbitrary trailing tail appended, to
   exercise the "streaming: returns the remainder" contract — the
   parser must hand back exactly the untouched suffix. *)
let assert_roundtrip ~name ?(tail : RDF_Bytes.bytes = []) e =
  let bs = RDF_Store_Columnar_DeltaLog.serialize_delta_entry e in
  let framed = bs @ tail in
  match RDF_Store_Columnar_DeltaLog.parse_delta_entry framed with
  | None ->
    check ~name:(name ^ " [" ^ entry_name e ^ ", parse]") false
  | Some (e', rest) ->
    check ~name:(name ^ " [" ^ entry_name e ^ ", parse]") true;
    check ~name:(name ^ " [" ^ entry_name e ^ ", value]") (e' = e);
    check ~name:(name ^ " [" ^ entry_name e ^ ", remainder]") (rest = tail)

let assert_parses_to_none ~name (bs : RDF_Bytes.bytes) =
  match RDF_Store_Columnar_DeltaLog.parse_delta_entry bs with
  | None -> check ~name true
  | Some _ -> check ~name false

(* Flip one byte (mod 256) at position [i] of a byte list. *)
let flip_at (bs : RDF_Bytes.bytes) (i : int) : RDF_Bytes.bytes =
  List.mapi (fun j b -> if j = i then (b + 1) mod 256 else b) bs

let take (n : int) (bs : RDF_Bytes.bytes) : RDF_Bytes.bytes =
  let rec go n bs = match n, bs with
    | 0, _ | _, [] -> []
    | n, b :: rest -> b :: go (n - 1) rest
  in go n bs

(* --- fixtures ------------------------------------------------------------ *)

let s_alice = RDF_Term.S_IRI (iri "http://example.org/alice")
let s_blank = RDF_Term.S_BNode "b0"
let p_knows = iri "http://example.org/knows"
let g_named = iri "http://example.org/graph1"

let () =
  Printf.printf "== delta_log_roundtrip ==\n";

  (* 1-4: DE_Add, varied subject/object/graph shapes. *)
  assert_roundtrip ~name:"add.iri-iri.no-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice p_knows (RDF_Term.T_IRI (iri "http://example.org/bob")), None));
  assert_roundtrip ~name:"add.bnode-bnode.some-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_blank p_knows (RDF_Term.T_BNode "b1"), Some g_named));
  assert_roundtrip ~name:"add.plain-literal"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/name") (plain_lit "Alice"), None));
  assert_roundtrip ~name:"add.lang-literal"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/name") (lang_lit "Alice" "en"), Some g_named));

  (* 5-6: DE_Remove, mirroring Add's shapes. *)
  assert_roundtrip ~name:"remove.iri-iri.no-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Remove
       (triple s_alice p_knows (RDF_Term.T_IRI (iri "http://example.org/bob")), None));
  assert_roundtrip ~name:"remove.lang-literal.some-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Remove
       (triple s_blank (iri "http://example.org/name") (lang_lit "Bob" "en-US"), Some g_named));

  (* 7-9: DE_Clear (default and named graph), DE_Drop, DE_Create. *)
  assert_roundtrip ~name:"clear.default-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Clear None);
  assert_roundtrip ~name:"clear.named-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Clear (Some g_named));
  assert_roundtrip ~name:"drop.named-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Drop g_named);
  assert_roundtrip ~name:"create.named-graph"
    (RDF_Store_Columnar_DeltaLog.DE_Create g_named);

  (* 10-13: empty strings in every field position that allows them
     (bnode ids, lexical form; datatype/predicate/subject-iri/graph
     must stay well-formed, i.e. non-empty with a colon, so those are
     exercised at their shortest legal form instead). *)
  assert_roundtrip ~name:"empty.bnode-subject-and-object"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple (RDF_Term.S_BNode "") p_knows (RDF_Term.T_BNode ""), None));
  assert_roundtrip ~name:"empty.lexical-form"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/note") (plain_lit ""), None));
  assert_roundtrip ~name:"empty.lang-tag-value-nonempty-required"
    (* lang tag itself must be a real (non-empty by convention) BCP-47
       tag; exercise the shortest realistic one instead of "". *)
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/note") (lang_lit "" "en"), None));
  assert_roundtrip ~name:"empty.graph-name-in-drop"
    (RDF_Store_Columnar_DeltaLog.DE_Drop "");

  (* 14-16: non-ASCII UTF-8 in IRI, bnode label, lexical form, and lang
     tag — including a string with an astral-plane codepoint (emoji)
     to stress BatUTF8's multi-byte handling. *)
  assert_roundtrip ~name:"utf8.iri-object"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice p_knows
          (RDF_Term.T_IRI (iri "http://example.org/caf\xc3\xa9")), None));
  assert_roundtrip ~name:"utf8.bnode-label"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple (RDF_Term.S_BNode "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e") p_knows
          (RDF_Term.T_IRI (iri "http://example.org/x")), None));
  assert_roundtrip ~name:"utf8.literal-with-lang"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/greeting")
          (lang_lit "\xe3\x81\x93\xe3\x82\x93\xe3\x81\xab\xe3\x81\xa1\xe3\x81\xaf" "ja"), None));
  assert_roundtrip ~name:"utf8.astral-emoji"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/reaction")
          (plain_lit "party \xf0\x9f\x8e\x89 time"), None));

  (* 17: a long literal (~100 KB) — exercises the u32 length prefix on
     a non-trivial payload, not just the framing's own small fields. *)
  let long_lex = String.make 100_000 'x' in
  assert_roundtrip ~name:"long-literal"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/blob") (plain_lit long_lex), None));

  (* 18: datatype+langtag combination sanity (already covered above,
     repeated here with a distinct BCP-47 region tag to broaden
     coverage — case-insensitive lang matching is a term-equality
     concern, not this module's; here it's plain bytes). *)
  assert_roundtrip ~name:"lang-tag.region-subtag"
    (RDF_Store_Columnar_DeltaLog.DE_Add
       (triple s_alice (iri "http://example.org/name") (lang_lit "Bob" "en-US"), Some g_named));

  (* 19: streaming contract — parse_delta_entry must return the exact
     untouched trailing bytes when more data follows in the log. *)
  assert_roundtrip ~name:"streaming.tail-bytes-preserved"
    ~tail:(RDF_Bytes.bytes_of_string "NEXT-ENTRY-PLACEHOLDER")
    (RDF_Store_Columnar_DeltaLog.DE_Create g_named);

  (* 20: multi-entry stream round-trip — concatenate several distinct
     entries and drain them with repeated parse_delta_entry calls. *)
  let stream_entries = [
    RDF_Store_Columnar_DeltaLog.DE_Add
      (triple s_alice p_knows (RDF_Term.T_IRI (iri "http://example.org/bob")), None);
    RDF_Store_Columnar_DeltaLog.DE_Clear (Some g_named);
    RDF_Store_Columnar_DeltaLog.DE_Add
      (triple s_blank (iri "http://example.org/name") (lang_lit "X" "fr"), Some g_named);
    RDF_Store_Columnar_DeltaLog.DE_Drop g_named;
    RDF_Store_Columnar_DeltaLog.DE_Create (iri "urn:graph:reborn");
  ] in
  let stream_bytes =
    List.concat_map RDF_Store_Columnar_DeltaLog.serialize_delta_entry stream_entries in
  let rec drain bs acc =
    match RDF_Store_Columnar_DeltaLog.parse_delta_entry bs with
    | None -> List.rev acc, bs
    | Some (e, rest) -> drain rest (e :: acc)
  in
  let decoded, leftover = drain stream_bytes [] in
  check ~name:"multi-entry-stream.decoded-matches" (decoded = stream_entries);
  check ~name:"multi-entry-stream.leftover-empty" (leftover = []);

  (* 21-27: framing corruption must parse to None, never a wrong
     entry. Built off one well-formed serialized entry. *)
  let good_entry =
    RDF_Store_Columnar_DeltaLog.DE_Add
      (triple s_alice p_knows (plain_lit "corruption-fixture"), Some g_named) in
  let good_bytes = RDF_Store_Columnar_DeltaLog.serialize_delta_entry good_entry in
  let good_len = List.length good_bytes in

  assert_parses_to_none ~name:"corrupt.empty-input" [];
  assert_parses_to_none ~name:"corrupt.truncated-header"
    (take 3 good_bytes);
  assert_parses_to_none ~name:"corrupt.truncated-mid-payload"
    (take (good_len - 5) good_bytes);
  assert_parses_to_none ~name:"corrupt.truncated-last-byte"
    (take (good_len - 1) good_bytes);
  assert_parses_to_none ~name:"corrupt.bad-magic"
    (flip_at good_bytes 0);
  assert_parses_to_none ~name:"corrupt.bad-version"
    (flip_at good_bytes 4);
  assert_parses_to_none ~name:"corrupt.bad-checksum-field"
    (flip_at good_bytes (good_len - 2));
  (* Corrupt a byte inside the payload itself (index 16 is just past
     the 16-byte magic+version+length header, guaranteed inside the
     payload for this non-trivial fixture) — the checksum field is
     untouched but no longer matches the mutated payload, so this
     must also parse to None. Distinct code path from corrupting the
     checksum field directly above. *)
  assert_parses_to_none ~name:"corrupt.bad-payload-byte"
    (flip_at good_bytes 16);

  (* 28: corrupting the fixture must not silently decode as some
     *other* valid-looking entry — re-assert the good bytes still
     decode to the original untouched (control, alongside the
     corrupted variants above never decoding at all). *)
  (match RDF_Store_Columnar_DeltaLog.parse_delta_entry good_bytes with
   | Some (e, []) -> check ~name:"corrupt.control-still-decodes" (e = good_entry)
   | _ -> check ~name:"corrupt.control-still-decodes" false);

  (* ==========================================================
     29+: stage 2 — delta_batch / log-file round-trip witness.
     formal/fstar/RDF.Store.Columnar.DeltaLog.fst sections 7-10
     (serialize_delta_batch/parse_delta_batch,
     serialize_log/parse_log). Same discipline as the entry-level
     tests above: round-trip every shape, then corrupt and confirm
     rejection (never a torn/wrong decode). *)

  let module DL = RDF_Store_Columnar_DeltaLog in
  (* db_seq/db_epoch are Prims.nat (= Z.t after extraction) — plain
     OCaml int literals must go through Z.of_int, same convention as
     compound_presence_writer_roundtrip.ml / offsets_writer_roundtrip.ml. *)
  let mk_batch (seq : int) (epoch : int) ops : DL.delta_batch =
    { DL.db_seq = Z.of_int seq; DL.db_epoch = Z.of_int epoch; DL.db_ops = ops } in
  let mk_batch_z (seq : Z.t) (epoch : Z.t) ops : DL.delta_batch =
    { DL.db_seq = seq; DL.db_epoch = epoch; DL.db_ops = ops } in

  let assert_batch_roundtrip ~name (b : DL.delta_batch) =
    let bs = DL.serialize_delta_batch b in
    match DL.parse_delta_batch bs with
    | None -> check ~name:(name ^ " [parse]") false
    | Some (b', rest) ->
      check ~name:(name ^ " [parse]") true;
      check ~name:(name ^ " [value]") (b' = b);
      check ~name:(name ^ " [remainder-empty]") (rest = [])
  in

  let op1 =
    DL.DE_Add (triple s_alice p_knows (RDF_Term.T_IRI (iri "http://example.org/bob")), None) in
  let op2 = DL.DE_Clear (Some g_named) in
  let op3 =
    DL.DE_Add (triple s_blank (iri "http://example.org/name") (lang_lit "X" "fr"), Some g_named) in

  assert_batch_roundtrip ~name:"batch.empty-ops" (mk_batch 0 0 []);
  assert_batch_roundtrip ~name:"batch.single-op" (mk_batch 1 0 [op1]);
  assert_batch_roundtrip ~name:"batch.multi-op" (mk_batch 42 3 [op1; op2; op3]);
  assert_batch_roundtrip ~name:"batch.large-seq-epoch"
    (mk_batch_z (Z.of_string "18446744073709551615") (Z.of_string "18446744073709551615") [op1]);

  (* streaming: a batch's parse must hand back the exact trailing
     bytes, same "remainder preserved" contract as entries. *)
  (let b = mk_batch 5 0 [op1; op3] in
   let bs = DL.serialize_delta_batch b in
   let tail = RDF_Bytes.bytes_of_string "AFTER-BATCH" in
   match DL.parse_delta_batch (bs @ tail) with
   | Some (b', rest) ->
     check ~name:"batch.streaming.value" (b' = b);
     check ~name:"batch.streaming.remainder" (rest = tail)
   | None -> check ~name:"batch.streaming" false);

  (* batch-level corruption: bad magic / bad version / bad checksum /
     truncated must all reject, never mis-decode. *)
  (let good_batch = mk_batch 7 1 [op1; op2] in
   let good_bytes = DL.serialize_delta_batch good_batch in
   let good_len = List.length good_bytes in
   let assert_batch_none ~name bs =
     match DL.parse_delta_batch bs with
     | None -> check ~name true
     | Some _ -> check ~name false
   in
   assert_batch_none ~name:"batch.corrupt.empty" [];
   assert_batch_none ~name:"batch.corrupt.truncated-header" (take 3 good_bytes);
   assert_batch_none ~name:"batch.corrupt.truncated-tail" (take (good_len - 1) good_bytes);
   assert_batch_none ~name:"batch.corrupt.bad-magic" (flip_at good_bytes 0);
   assert_batch_none ~name:"batch.corrupt.bad-version" (flip_at good_bytes 4);
   assert_batch_none ~name:"batch.corrupt.bad-checksum" (flip_at good_bytes (good_len - 2));
   assert_batch_none ~name:"batch.corrupt.bad-body-byte" (flip_at good_bytes 16);
   (match DL.parse_delta_batch good_bytes with
    | Some (b, []) -> check ~name:"batch.corrupt.control-still-decodes" (b = good_batch)
    | _ -> check ~name:"batch.corrupt.control-still-decodes" false));

  (* --- log-file level: header + several batches, round-trip and
     the "accept a prefix, never a torn entry" crash-recovery
     contract (a truncated/corrupt trailing batch must not stop the
     earlier, complete batches from being recovered). --- *)

  let log_batches = [
    mk_batch 1 0 [op1];
    mk_batch 2 0 [op2; op3];
    mk_batch 3 0 [];
    mk_batch 4 1 [op1; op2; op3];
  ] in
  let log_bytes = DL.serialize_log log_batches in

  (match DL.parse_log log_bytes with
   | Some (bs, []) ->
     check ~name:"log.roundtrip.value" (bs = log_batches);
   | _ -> check ~name:"log.roundtrip" false);

  (* Bad log header (wrong magic) must reject outright. *)
  check ~name:"log.corrupt.bad-header" (DL.parse_log (flip_at log_bytes 0) = None);

  (* Truncate the log so only a PARTIAL final batch remains: the
     earlier, complete batches must still be recovered exactly, and
     the torn tail must never be accepted as a (wrong) decoded
     batch. This is the same property the crash harness
     (tests/local/delta_log_crash_harness.sh) exercises against a
     real killed process — this is its pure, in-process control. *)
  (let full_len = List.length log_bytes in
   let torn_len = full_len - 7 in (* lop off the last batch's tail *)
   let torn_bytes = take torn_len log_bytes in
   match DL.parse_log torn_bytes with
   | None -> check ~name:"log.torn-tail.header-still-parses" false
   | Some (bs, leftover) ->
     check ~name:"log.torn-tail.recovers-complete-prefix"
       (bs = [mk_batch 1 0 [op1]; mk_batch 2 0 [op2; op3]; mk_batch 3 0 []]);
     check ~name:"log.torn-tail.leftover-is-undecoded-suffix" (leftover <> []));

  (* expected_digest_bytes is exactly serialize_delta_batch — the
     hash-witness surface's whole contract (section 11 of the .fst). *)
  (let b = mk_batch 9 0 [op1] in
   check ~name:"expected_digest_bytes.matches-serialize"
     (DL.expected_digest_bytes b = DL.serialize_delta_batch b));

  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
