(* fulltext_slice1_unit.ml — pins the semantics of SPARQL_FullText, the
   fulltext SPARQL Slice 1 module (design doc
   docs/designissues/2026-07-05-fulltext-sparql-design.md, §2.2/§6).

   Covers the pieces that are pure F* and reachable without going
   through the CLI (tests/local/fulltext_slice1.sh exercises the full
   text:query surface end-to-end against the real binary; this file
   pins the tokenizer, the object-argument codec, match_tokens' AND
   semantics, and the limit-truncation helper the two eval hooks call
   directly): *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

let check_str_list ~name expected actual =
  check ~name expected actual

let () =
  (* --- default_tokenizer: edge cases ------------------------------- *)
  check_str_list ~name:"tokenizer: empty string" []
    (SPARQL_FullText.default_tokenizer "");
  check_str_list ~name:"tokenizer: all punctuation" []
    (SPARQL_FullText.default_tokenizer "...!!!???");
  check_str_list ~name:"tokenizer: single word" ["panel"]
    (SPARQL_FullText.default_tokenizer "panel");
  check_str_list ~name:"tokenizer: mixed case folds to lowercase"
    ["solar"; "panel"]
    (SPARQL_FullText.default_tokenizer "Solar PANEL");
  check_str_list ~name:"tokenizer: punctuation splits words"
    ["solar"; "panel"; "array"]
    (SPARQL_FullText.default_tokenizer "solar-panel, array!");
  check_str_list ~name:"tokenizer: whitespace runs collapse"
    ["a"; "b"]
    (SPARQL_FullText.default_tokenizer "  a   b  ");
  check_str_list ~name:"tokenizer: digits are alnum (kept in-token)"
    ["panel2"]
    (SPARQL_FullText.default_tokenizer "panel2");
  (* ASCII floor (design doc §2.1/§2.2, task brief's stated slice-1
     scope): non-ASCII bytes act as word separators rather than being
     folded/preserved -- documented behavior, not a bug. A Unicode-aware
     analyzer is the doc's slice-3 ASSUME-HOST seam, not this module. *)
  check_str_list ~name:"tokenizer: non-ASCII bytes act as separators (documented floor)"
    ["caf"]
    (SPARQL_FullText.default_tokenizer "caf\xc3\xa9");

  (* --- match_tokens: AND (all-tokens) semantics, design doc §7 ------ *)
  check ~name:"match_tokens: all query tokens present" true
    (SPARQL_FullText.match_tokens ["solar"; "panel"] ["solar"; "panel"; "array"]);
  check ~name:"match_tokens: one query token missing" false
    (SPARQL_FullText.match_tokens ["solar"; "panel"] ["battery"; "storage"; "panel"]);
  check ~name:"match_tokens: candidate token order/duplicates don't matter" true
    (SPARQL_FullText.match_tokens ["panel"; "solar"] ["array"; "panel"; "panel"; "solar"]);
  check ~name:"match_tokens: empty candidate never matches a nonempty query" false
    (SPARQL_FullText.match_tokens ["solar"] []);

  (* --- literal_matches_query: tokenizes both sides through the same
     default_tokenizer before match_tokens ------------------------- *)
  let mk_literal lex =
    { RDF_Term.lexical_form = lex;
      RDF_Term.datatype = "http://www.w3.org/2001/XMLSchema#string";
      RDF_Term.lang_tag = FStar_Pervasives_Native.None }
  in
  let ftq_no_field terms limit =
    { SPARQL_FullText.ftq_field = FStar_Pervasives_Native.None;
      SPARQL_FullText.ftq_terms = terms;
      SPARQL_FullText.ftq_limit = limit }
  in
  check ~name:"literal_matches_query: multi-token AND match"
    true
    (SPARQL_FullText.literal_matches_query (ftq_no_field "solar panel" FStar_Pervasives_Native.None)
       (mk_literal "Solar panel array"));
  check ~name:"literal_matches_query: stemming-off baseline (\"panels\" != \"panel\")"
    false
    (SPARQL_FullText.literal_matches_query (ftq_no_field "panel" FStar_Pervasives_Native.None)
       (mk_literal "Extra panels installed"));

  (* --- encode_fulltext_literal / decode_fulltext_literal round trip - *)
  let field_iri = "http://www.w3.org/2000/01/rdf-schema#label" in
  let roundtrip ftq =
    SPARQL_FullText.decode_fulltext_literal (SPARQL_FullText.encode_fulltext_literal ftq)
  in
  check ~name:"codec round trip: 2-arity (no field, no limit)"
    (FStar_Pervasives_Native.Some (ftq_no_field "solar panel" FStar_Pervasives_Native.None))
    (roundtrip (ftq_no_field "solar panel" FStar_Pervasives_Native.None));
  check ~name:"codec round trip: field restriction, no limit"
    (FStar_Pervasives_Native.Some
       { SPARQL_FullText.ftq_field = FStar_Pervasives_Native.Some field_iri;
         SPARQL_FullText.ftq_terms = "panel";
         SPARQL_FullText.ftq_limit = FStar_Pervasives_Native.None })
    (roundtrip
       { SPARQL_FullText.ftq_field = FStar_Pervasives_Native.Some field_iri;
         SPARQL_FullText.ftq_terms = "panel";
         SPARQL_FullText.ftq_limit = FStar_Pervasives_Native.None });
  check ~name:"codec round trip: field restriction + limit"
    (FStar_Pervasives_Native.Some
       { SPARQL_FullText.ftq_field = FStar_Pervasives_Native.Some field_iri;
         SPARQL_FullText.ftq_terms = "panel";
         SPARQL_FullText.ftq_limit = FStar_Pervasives_Native.Some (Z.of_int 2) })
    (roundtrip
       { SPARQL_FullText.ftq_field = FStar_Pervasives_Native.Some field_iri;
         SPARQL_FullText.ftq_terms = "panel";
         SPARQL_FullText.ftq_limit = FStar_Pervasives_Native.Some (Z.of_int 2) });
  check ~name:"decode_fulltext_literal: non-fulltext literal decodes to None"
    FStar_Pervasives_Native.None
    (SPARQL_FullText.decode_fulltext_literal (mk_literal "just a plain literal"));

  (* --- object_matches_query: non-literal objects never match -------- *)
  check ~name:"object_matches_query: IRI object never matches"
    false
    (SPARQL_FullText.object_matches_query (ftq_no_field "panel" FStar_Pervasives_Native.None)
       (RDF_Term.T_IRI "http://example.org/panel"));

  (* --- limit handling: the take-n helpers both eval hooks call after
     the field-restricted/unrestricted candidate scan (SPARQL11.Algebra's
     `list_take`, SPARQL11.Store's `list_take_n` -- same shape, one per
     dispatch-point module per design doc §3) ----------------------- *)
  check ~name:"limit handling: SPARQL11_Algebra.list_take truncates"
    [1; 2]
    (SPARQL11_Algebra.list_take (Z.of_int 2) [1; 2; 3; 4]);
  check ~name:"limit handling: SPARQL11_Algebra.list_take n > length is a no-op"
    [1; 2; 3]
    (SPARQL11_Algebra.list_take (Z.of_int 10) [1; 2; 3]);
  check ~name:"limit handling: SPARQL11_Algebra.list_take 0 yields empty"
    []
    (SPARQL11_Algebra.list_take Z.zero [1; 2; 3]);
  check ~name:"limit handling: SPARQL11_Store.list_take_n truncates"
    [1; 2]
    (SPARQL11_Store.list_take_n (Z.of_int 2) [1; 2; 3; 4]);

  Printf.printf "fulltext_slice1_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
