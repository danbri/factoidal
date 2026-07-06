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

  Printf.printf
    "== summary: %d pass, %d fail (out of %d) ==\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1 else exit 0
