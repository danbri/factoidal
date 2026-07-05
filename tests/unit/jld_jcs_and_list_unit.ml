(* jld_jcs_and_list_unit.ml — pins two Parser.JSONLD.fst behaviors fixed
   during the 2026-07-05 JSON-LD IRI-resolution/JCS/skip-policy pass:

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
      Parser_JSONLD.parse_jsonld + RDF_Canonical, mirroring toRdf/li12. *)

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

let () =
  Printf.printf "jld_jcs_and_list_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
