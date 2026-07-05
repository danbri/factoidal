(* jld_jcs_and_list_unit.ml — pins Parser.JSONLD.fst behaviors fixed
   during the 2026-07-05 JSON-LD IRI-resolution/JCS/skip-policy pass
   and the follow-up goal-wave pass (predicate well-formedness +
   compound-literal rdfDirection):

   1. jcanon_number's RFC 8785 (JCS) number serialization — the
      ECMAScript Number::toString notation rules (fixed vs. exponential
      by magnitude, explicit "+"/"-" exponent sign, general trailing-
      zero stripping), reusing the same digit-normalization pass as
      jld_number_canonicalize. Covers exactly the toRdf/js12 fixture's
      four notation-only numbers (no binary64 rounding needed) plus a
      few extra magnitude-threshold boundary cases. The one js12 number
      needing genuine double rounding ("333333333.33333329") is NOT
      pinned as passing here — see Parser.JSONLD.fst's jcanon_number
      banner for that acknowledged gap.

   2. jld_expand_list's JSON-LD 1.1 API §8.3 "List to RDF Conversion"
      fix: a @list array member whose value fails to become an RDF term
      (e.g. a @type:@id-coerced string that isn't a well-formed
      absolute IRI) still gets its OWN rdf:first/rdf:rest cell — only
      the rdf:first triple for that cell is omitted — instead of the
      cell being dropped outright (which wrongly collapsed a single-
      item list straight to rdf:nil). Pinned end-to-end via
      Parser_JSONLD.parse_jsonld + RDF_Canonical, mirroring toRdf/li12.

   3. jld_predicate_iri_wf (toRdf/e068, e075, e038, t0118 "generalized
      RDF" battery): a property whose EXPANDED-FORM key is a blank-node
      identifier ("_:property", or "@vocab": "_:" concatenated onto a
      plain term) is DROPPED at triple emission — this codebase has no
      generalized-RDF-aware N-Quads serializer, so it never emits the
      previously-bogus pseudo-IRI predicate `<_:property>`.

   4. jld_iri_wf's "at most one fragment delimiter" gate (toRdf/e111,
      e112): a vocab-relative property-key expansion that concatenates
      a vocab mapping ENDING in "#" onto a key STARTING with "#"
      produces a doubly-fragmented string ("...#...#...") that is not
      a well-formed IRI reference and must be dropped as a predicate,
      not emitted.

   5. jld_compound_literal_term (toRdf/di11, di12): rdfDirection=
      "compound-literal" turns a @direction-bearing value object into a
      FRESH BLANK NODE carrying rdf:value/rdf:direction/rdf:language
      triples instead of a single literal term. *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if String.equal expected actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %S got %S\n" name expected actual
  end

(* --- Part 1: jcanon_number (JCS number notation) --- *)

let () =
  let n = Parser_JSONLD.jcanon_number in
  check ~name:"jcs 1E30 -> 1e+30 (large magnitude, exponential, explicit +)"
    "1e+30" (n "1E30");
  check ~name:"jcs 4.50 -> 4.5 (general trailing-zero strip, not just all-zero)"
    "4.5" (n "4.50");
  check ~name:"jcs 2e-3 -> 0.002 (small-magnitude exponential collapses to fixed)"
    "0.002" (n "2e-3");
  check ~name:"jcs 0.000...001 (27 zeros) -> 1e-27 (below -6 threshold, exponential)"
    "1e-27" (n "0.000000000000000000000000001");
  check ~name:"jcs 0 -> 0" "0" (n "0");
  check ~name:"jcs -0 -> 0 (JCS negative-zero rule)" "0" (n "-0.0e5");
  check ~name:"jcs 100 -> 100 (k<=n<=21 fixed, zero-padded, no dot)"
    "100" (n "1e2");
  check ~name:"jcs 123.456 -> 123.456 (already-shortest passthrough)"
    "123.456" (n "123.456");
  check ~name:"jcs 1e21 -> 1e+21 (n=22 exceeds fixed-notation ceiling)"
    "1e+21" (n "1e21");
  check ~name:"jcs 1e20 -> 100000000000000000000 (n=21, still fixed)"
    "100000000000000000000" (n "1e20");
  check ~name:"jcs 1e-6 -> 0.000001 (n=-5, still fixed, just inside -6<n<=0)"
    "0.000001" (n "1e-6");
  check ~name:"jcs 1e-7 -> 1e-7 (n=-6, crosses to exponential)"
    "1e-7" (n "1e-7")

(* --- Part 2: jld_expand_list's per-item list-cell allocation --- *)

let canon_ds ds = RDF_Canonical.canonicalize_to_nquads ds

let parse_or_fail ~name input =
  match
    Parser_JSONLD.parse_jsonld input FStar_Pervasives_Native.None
      FStar_Pervasives_Native.None FStar_Pervasives_Native.None
      FStar_Pervasives_Native.None
  with
  | FStar_Pervasives_Native.Some ds -> Some ds
  | FStar_Pervasives_Native.None ->
    incr failed;
    Printf.printf "  FAIL  %s: parse_jsonld returned None\n" name;
    None

let () =
  (* Mirrors toRdf/li12 exactly: a @type:@id-coerced single-item @list
     whose item value ("test") resolves, via the ill-formed-but-present
     "@base", to a string that fails Parser.JSONLD's jld_iri_wf check
     (the "<" "/" ">" bytes RFC 3987 excludes), so it fails to become a
     term. Using an ILL-FORMED-BUT-PRESENT base (not an absent one) is
     load-bearing here: an absent base hits a DIFFERENT (JSONLD.Expand-
     side, not ours) bug where the item is dropped at expansion time
     entirely, which would not exercise this fix at all — see
     Parser.JSONLD.fst's jld_expand_list banner / this file's own
     banner for why li12 (this shape) passes while li14 (absent base)
     still doesn't, pending a sibling-owned fix. *)
  let input =
    {|{
      "@context": {
        "@base": "http://invalid/<>/",
        "list": { "@id": "foo:bar", "@container": "@list", "@type": "@id" }
      },
      "list": ["test"]
    }|}
  in
  match parse_or_fail ~name:"list-gap parses" input with
  | None -> ()
  | Some ds ->
    let got = canon_ds ds in
    (* Canonical form: one blank node subject for "foo:bar"'s object,
       linked rdf:rest -> rdf:nil, with NO rdf:first triple anywhere —
       i.e. exactly 2 triples total (foo:bar link + rdf:rest), never a
       direct "foo:bar -> rdf:nil" collapse (which would be 1 triple). *)
    let ntriples =
      List.length (String.split_on_char '\n' (String.trim got))
    in
    check ~name:"list-gap: cell count (2 triples: foo:bar link + rdf:rest, not a nil collapse)"
      "2" (string_of_int ntriples);
    let mentions_first =
      let needle = "22-rdf-syntax-ns#first" in
      let hay = got in
      let nlen = String.length needle and hlen = String.length hay in
      let rec go i = i + nlen <= hlen && (String.sub hay i nlen = needle || go (i + 1)) in
      go 0
    in
    check ~name:"list-gap: no rdf:first triple for the dropped item"
      "false" (string_of_bool mentions_first)

(* --- Shared substring helper (Parts 3-5) --- *)

let contains ~needle hay =
  let nlen = String.length needle and hlen = String.length hay in
  let rec go i = i + nlen <= hlen && (String.sub hay i nlen = needle || go (i + 1)) in
  go 0

let ntriples_of got =
  if String.trim got = "" then 0
  else List.length (String.split_on_char '\n' (String.trim got))

let parse_or_fail_dir ~name ~rdf_direction input =
  match
    Parser_JSONLD.parse_jsonld input FStar_Pervasives_Native.None
      rdf_direction FStar_Pervasives_Native.None
      FStar_Pervasives_Native.None
  with
  | FStar_Pervasives_Native.Some ds -> Some ds
  | FStar_Pervasives_Native.None ->
    incr failed;
    Printf.printf "  FAIL  %s: parse_jsonld returned None\n" name;
    None

(* --- Part 3: jld_predicate_iri_wf — blank-node predicates dropped --- *)

let () =
  (* toRdf/e068-style: a property key that is itself a blank-node
     identifier ("_:property") is dropped; only the @type triple
     (rdf:type's object CAN be a blank node — that is not a predicate)
     survives. *)
  let input =
    {|{
      "@id": "_:node1",
      "@type": "_:type",
      "_:property": "dropped"
    }|}
  in
  match parse_or_fail_dir ~name:"bnode-predicate (e068-style) parses"
          ~rdf_direction:FStar_Pervasives_Native.None input with
  | None -> ()
  | Some ds ->
    let got = canon_ds ds in
    check ~name:"bnode-predicate (e068-style): only the @type triple survives"
      "1" (string_of_int (ntriples_of got));
    check ~name:"bnode-predicate (e068-style): no <_: pseudo-IRI predicate emitted"
      "false" (string_of_bool (contains ~needle:"<_:" got))

let () =
  (* toRdf/e075-style: "@vocab": "_:" makes every ordinary term a
     blank-node identifier; every resulting property is dropped (zero
     triples), never emitted as a bogus `<_:b1>` pseudo-IRI predicate. *)
  let input =
    {|{
      "@context": {"@vocab": "_:"},
      "@id": "http://example.com/node1",
      "b1": "blank node property 1",
      "b2": "blank node property 1"
    }|}
  in
  match parse_or_fail_dir ~name:"bnode-predicate (e075-style, @vocab: '_:') parses"
          ~rdf_direction:FStar_Pervasives_Native.None input with
  | None -> ()
  | Some ds ->
    let got = canon_ds ds in
    check ~name:"bnode-predicate (e075-style): both properties dropped (zero triples)"
      "0" (string_of_int (ntriples_of got))

(* --- Part 4: jld_iri_wf's at-most-one-fragment gate --- *)

let () =
  (* toRdf/e111-style: @vocab "http://example.com/vocabulary/./rel2#"
     (already ending in "#") concatenated with a property key that
     itself starts with "#" ("#fragment-works") produces a doubly-
     fragmented, non-well-formed predicate IRI — dropped, not emitted. *)
  let input =
    {|{
      "@context": {"@vocab": "http://example.com/vocabulary/./rel2#"},
      "@id": "http://example.com/node1",
      "#fragment-works": "dropped",
      "link": "kept"
    }|}
  in
  match parse_or_fail_dir ~name:"double-fragment predicate (e111-style) parses"
          ~rdf_direction:FStar_Pervasives_Native.None input with
  | None -> ()
  | Some ds ->
    let got = canon_ds ds in
    check ~name:"double-fragment predicate (e111-style): only the well-formed property survives"
      "1" (string_of_int (ntriples_of got));
    check ~name:"double-fragment predicate (e111-style): no doubly-fragmented predicate emitted"
      "false" (string_of_bool (contains ~needle:"rel2##" got))

(* --- Part 5: jld_compound_literal_term (rdfDirection=compound-literal) --- *)

let () =
  (* Mirrors toRdf/di11: no @language. Expect a fresh blank node
     carrying rdf:value + rdf:direction (2 triples for the value
     object) plus the 1 linking triple = 3 total; no rdf:language. *)
  let input = {|{"http://example.org/label": {"@value": "no language", "@direction": "rtl"}}|} in
  match parse_or_fail_dir ~name:"compound-literal no-language (di11-style) parses"
          ~rdf_direction:(FStar_Pervasives_Native.Some "compound-literal") input with
  | None -> ()
  | Some ds ->
    let got = canon_ds ds in
    check ~name:"compound-literal no-language (di11-style): 3 triples (link + value + direction)"
      "3" (string_of_int (ntriples_of got));
    check ~name:"compound-literal no-language (di11-style): rdf:value present"
      "true" (string_of_bool (contains ~needle:"22-rdf-syntax-ns#value> \"no language\"" got));
    check ~name:"compound-literal no-language (di11-style): rdf:direction present"
      "true" (string_of_bool (contains ~needle:"22-rdf-syntax-ns#direction> \"rtl\"" got));
    check ~name:"compound-literal no-language (di11-style): no rdf:language triple"
      "false" (string_of_bool (contains ~needle:"22-rdf-syntax-ns#language" got))

let () =
  (* Mirrors toRdf/di12: @language "en-US" present -> rdf:language
     "en-us" (LOWERCASED), lexical form keeps its original casing. 4
     triples total (link + value + direction + language). *)
  let input =
    {|{"http://example.org/label": {"@value": "en-US", "@language": "en-US", "@direction": "rtl"}}|}
  in
  match parse_or_fail_dir ~name:"compound-literal with-language (di12-style) parses"
          ~rdf_direction:(FStar_Pervasives_Native.Some "compound-literal") input with
  | None -> ()
  | Some ds ->
    let got = canon_ds ds in
    check ~name:"compound-literal with-language (di12-style): 4 triples"
      "4" (string_of_int (ntriples_of got));
    check ~name:"compound-literal with-language (di12-style): rdf:value keeps original casing"
      "true" (string_of_bool (contains ~needle:"22-rdf-syntax-ns#value> \"en-US\"" got));
    check ~name:"compound-literal with-language (di12-style): rdf:language is lowercased"
      "true" (string_of_bool (contains ~needle:"22-rdf-syntax-ns#language> \"en-us\"" got))

let () =
  Printf.printf "jld_jcs_and_list_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
