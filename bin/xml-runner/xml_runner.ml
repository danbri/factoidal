(* W3C XML Conformance Test Suite ("xmlconf") runner for
   formal/fstar/Parser.XML.fst + formal/fstar/XML.Wellformedness.fst.

   Owner directive (2026-07-05): assess the EXISTING generic XML
   parser + wellformedness module against the real W3C xmlconf
   corpus (third_party/testing/xml/xmlconf/, vendored 2026-07-05 —
   see its README.md for provenance). This supersedes the bigger
   from-scratch XML.Core/Parser.XMLDoc plan sketched in
   docs/designissues/2026-05-07-xml-fstar-phase0-audit.md — that plan
   was never built; Parser.XML.fst is the real, currently-extracted
   generic XML parser (it already underlies Parser.RDFXML and
   Parser.RIFXML), so it is what gets assessed here.

   !! THIS IS I/O GLUE — NO XML PARSING LOGIC LIVES HERE !! Every
   structural decision about whether a document is well-formed comes
   from `Parser_XML.parse_xml_document` (extracted from
   formal/fstar/Parser.XML.fst) and, informationally only,
   `XML_Wellformedness.is_valid_ncname` (extracted from
   formal/fstar/XML.Wellformedness.fst). This file does file I/O,
   AST tree-walking via Parser_XML's own accessor functions
   (element_tag/element_attrs/element_children/find_attr/
   text_content), manifest-entity-path discovery (a textual scan for
   file-path references, not an XML/DTD parser — see "Manifest
   dogfooding" below), encoding/BOM sniffing, and tallying. Per
   CLAUDE.md iron rule #11 / anti-pattern #15.

   ------------------------------------------------------------------
   Manifest dogfooding

   third_party/testing/xml/xmlconf/xmlconf.xml is the master manifest:
   a DOCTYPE with an internal subset declaring one general entity per
   sub-manifest file, whose body then references those entities.
   Parser.XML.fst has NO DOCTYPE production at all (confirmed by
   reading parse_xml_document: skip_misc only skips whitespace and
   comments) — so parse_xml_document on xmlconf.xml's raw bytes always
   returns None. This runner tries that dogfood parse first (and
   reports the result honestly), then falls back to a targeted
   textual scan for `<!ENTITY name SYSTEM "path">` declarations to
   discover the ~19 leaf manifest files. Each LEAF manifest file
   (xmltest/xmltest.xml, sun/sun-valid.xml, ibm/ibm_oasis_valid.xml,
   the eduni/* files, ...) has no DOCTYPE of its own, so it DOES parse
   via the real extracted parser, and every <TEST> entry is discovered
   by walking that parsed AST with Parser_XML's own accessors — this
   part is genuinely dogfooded, not regexed.

   ------------------------------------------------------------------
   Scoring semantics (owner-specified, 2026-07-05)

   TYPE="invalid" | "error": always SKIP "no DTD validation (by
   design)" — this project's XML parser does not implement DTD/schema
   validation, so these tests (which require a validating processor
   to catch, or whose behavior W3C itself does not mandate) cannot be
   meaningfully scored pass/fail here.

   TYPE="valid": PASS ("wf-accept" bucket — a parse-clean result only
   exercises well-formedness, NOT DTD validity, which we don't
   implement) when the document contains no DOCTYPE, its declared
   encoding (if any) is one this byte-oriented parser can safely treat
   as UTF-8/ASCII, and Parser_XML.parse_xml_document returns Some.
   SKIP "DOCTYPE/DTD not parsed" when the document contains a DOCTYPE
   (Parser.XML.fst structurally cannot get past ANY `<!DOCTYPE`, so
   this is never a real parser defect — it's an acknowledged missing
   feature). SKIP "encoding X not decoded" for BOM/declared-encoding
   values outside the safe set. Otherwise, a None result is a genuine
   FAIL (the parser rejected a document the suite says is
   well-formed) — a real defect, clustered by SECTIONS.

   TYPE="not-wf": the suite's own testcases.dtd documents the
   sanctioned exemption: "No parser should accept a 'not-wf' testcase
   unless it's a nonvalidating parser and the test contains external
   entities that the parser doesn't read." This runner is
   nonvalidating and reads NO external entities at all, so it uses the
   test's own ENTITIES attribute directly: ENTITIES != "none" and the
   parser accepted the document -> SKIP (exempted), never FAIL.
   ENTITIES = "none" and the parser accepted -> genuine FAIL (real
   defect, clustered by SECTIONS). Any None (reject) result -> PASS,
   regardless of ENTITIES — a reject always satisfies a not-wf test,
   whether or not the parser could see the specific violation. When
   the rejection is structurally guaranteed by an unrelated gap (the
   document contains a DOCTYPE our parser can never get past), the
   PASS is flagged "vacuous" in a side counter so the report doesn't
   overstate what was actually exercised.

   Also SKIP, before any of the above: test input file not found;
   encodings this parser doesn't decode (UTF-16 with or without BOM,
   non-ASCII-compatible declared encodings).

   XML_Wellformedness.fst's checks (NCName validation, RDF/XML
   forbidden-element-name lists, rdf:parseType/rdf:resource conflict
   rules) are RDF/XML-domain-specific, not generic XML conformance
   checks — is_valid_ncname's NCName production explicitly EXCLUDES
   ':' from name-start/name chars, so applying it as a generic
   well-formedness gate would wrongly reject plain XML 1.0 documents
   that legally use ':' in element/attribute names outside a
   Namespaces-aware context (exactly what several xmltest/ cases
   exercise on purpose, predating Namespaces in XML). This runner
   therefore calls is_valid_ncname informationally only, over every
   accepted document's element tags, and reports the finding rather
   than gating on it. This finding — that the wellformedness module
   does not generically apply — is itself one of this assessment's
   results.

   Usage:
     ./xml_runner                  Run the full vendored suite
     ./xml_runner <xmlconf-dir>    Run from an explicit xmlconf/ dir
     ./xml_runner -v|--verbose     Print every FAIL line as it runs
     ./xml_runner --help           Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (same pattern as bin/vc-runner/vc_runner.ml). *)

let find_repo_root () =
  let rec walk d =
    if d = "/" || d = "" then None
    else if Sys.file_exists (Filename.concat d "CLAUDE.md") then Some d
    else walk (Filename.dirname d)
  in
  let start =
    try Filename.dirname (Sys.executable_name)
    with _ -> Sys.getcwd ()
  in
  match walk start with
  | Some r -> r
  | None ->
    (match walk (Sys.getcwd ()) with
     | Some r -> r
     | None -> Sys.getcwd ())

let default_xmlconf_dir () =
  let repo_root = find_repo_root () in
  let candidates =
    [ Filename.concat repo_root "third_party/testing/xml/xmlconf";
      "third_party/testing/xml/xmlconf";
      "../../third_party/testing/xml/xmlconf" ]
  in
  try List.find Sys.file_exists candidates
  with Not_found -> Filename.concat repo_root "third_party/testing/xml/xmlconf"

(* ------------------------------------------------------------------ *)
(* File I/O. *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

(* ------------------------------------------------------------------ *)
(* Manifest-entity discovery: a textual scan for
   `<!ENTITY name SYSTEM "path">` declarations in xmlconf.xml's
   internal DTD subset. This is file-path discovery, not XML/DTD
   parsing — it never inspects, validates, or decides anything about
   the *content* of the referenced files; it just locates them so the
   real extracted parser (Parser_XML.parse_xml_document) can be run
   on each one, per the module comment above. *)

let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let skip_ws s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && is_ws s.[!j] do incr j done;
  !j

let read_token s i =
  let n = String.length s in
  let j = ref i in
  while !j < n && not (is_ws s.[!j]) do incr j done;
  (String.sub s i (!j - i), !j)

let has_prefix_at s i pre =
  let pn = String.length pre and n = String.length s in
  i + pn <= n && String.sub s i pn = pre

let find_substring_from s pat from_idx =
  let n = String.length s and m = String.length pat in
  if m = 0 then Some from_idx
  else
    let rec go i =
      if i + m > n then None
      else if String.sub s i m = pat then Some i
      else go (i + 1)
    in
    go (max 0 from_idx)

(* Returns (entity_name, system_path) list, in declaration order. *)
let discover_manifest_entities (content : string) : (string * string) list =
  let n = String.length content in
  let rec scan i acc =
    match find_substring_from content "<!ENTITY" i with
    | None -> List.rev acc
    | Some start ->
      let p = skip_ws content (start + 8) in
      let (name, p) = read_token content p in
      let p = skip_ws content p in
      if has_prefix_at content p "SYSTEM" then begin
        let p = skip_ws content (p + 6) in
        if p < n && (content.[p] = '"' || content.[p] = '\'') then begin
          let q = content.[p] in
          let p2 = p + 1 in
          match String.index_from_opt content p2 q with
          | Some qend ->
            let path = String.sub content p2 (qend - p2) in
            scan (qend + 1) ((name, path) :: acc)
          | None -> scan (start + 8) acc
        end else scan (start + 8) acc
      end else scan (start + 8) acc
  in
  scan 0 []

(* ------------------------------------------------------------------ *)
(* Collection bucketing: the first path segment of the LEAF manifest's
   own relative path (relative to xmlconf/), not the individual
   test's URI. *)

let collection_of_leaf (leaf_rel_path : string) : string =
  match String.split_on_char '/' leaf_rel_path with
  | "xmltest" :: _ -> "jclark"
  | "sun" :: _ -> "sun"
  | "ibm" :: _ -> "ibm"
  | "oasis" :: _ -> "oasis"
  | "eduni" :: _ -> "eduni"
  | "japanese" :: _ -> "japanese"
  | seg :: _ -> seg
  | [] -> "?"

(* ------------------------------------------------------------------ *)
(* Leaf-manifest normalization: some leaf manifests (sun/sun-valid.xml,
   sun/sun-invalid.xml, sun/sun-not-wf.xml) are a bare, unwrapped
   sequence of sibling <TEST> elements with no single root element —
   they are only well-formed XML in the context they were written for
   (entity-included inside the master manifest's own <TESTCASES>
   wrapper). Standalone, they are not well-formed XML at all (multiple
   top-level elements) — confirmed independently: Python's
   xml.etree.ElementTree also rejects them standalone ("junk after
   document element"). Parser.XML.fst's parse_xml_document has no
   "reject trailing content after the root" check (documented in the
   phase-0 audit as a known gap), so it silently parses ONLY the
   first <TEST> as "the whole document" and stops — which would
   silently drop every other test in that file from this runner's
   count, a real bug caught while building this harness (sun-valid.xml
   alone has 28 <TEST> entries, all but one would vanish).
   Fix: wrap every leaf manifest's post-prolog body in a synthetic
   <TESTCASES>...</TESTCASES> before feeding it to
   Parser_XML.parse_xml_document, exactly the "pure textual
   reshaping, not new parsing capability" pattern
   bin/rif-runner/rif_runner.ml already uses for its own manifest
   shape mismatches (wrap_bare_fact_in_group / ensure_group_present).
   Harmless for the files that already have their own TESTCASES root
   (TESTCASES may contain TESTCASES per testcases.dtd, and
   collect_tests already recurses through nested TESTCASES) — so this
   is applied uniformly to all 21 leaf files, not conditionally. This
   wrapping is manifest-bookkeeping only: the actual conformance test
   INPUT documents (read via rt_uri) are always parsed raw/unwrapped —
   that's the real subject under test. *)
let wrap_manifest_body (content : string) : string =
  let prolog_end =
    if has_prefix_at content 0 "<?xml" then
      match find_substring_from content "?>" 5 with
      | Some i -> i + 2
      | None -> 0
    else 0
  in
  let prolog = String.sub content 0 prolog_end in
  let rest = String.sub content prolog_end (String.length content - prolog_end) in
  prolog ^ "<TESTCASES>" ^ rest ^ "</TESTCASES>"

(* ------------------------------------------------------------------ *)
(* Raw test-entry record, discovered by walking a leaf manifest's
   parsed AST via Parser_XML's own accessors. *)

type raw_test = {
  rt_id : string;
  rt_type : string;          (* "valid" | "invalid" | "not-wf" | "error" *)
  rt_entities : string;      (* "none" | "general" | "parameter" | "both" *)
  rt_uri : string;
  rt_sections : string;
  rt_description : string;
  rt_leaf : string;          (* leaf manifest's relative path *)
  rt_collection : string;
}

let attr_or_default name default_val attrs =
  match Parser_XML.find_attr name attrs with
  | Some v -> v
  | None -> default_val

let rec collect_tests leaf_rel node acc =
  match Parser_XML.element_tag node with
  | Some "TEST" ->
    let attrs = Parser_XML.element_attrs node in
    let t = {
      rt_id = attr_or_default "ID" "?" attrs;
      rt_type = attr_or_default "TYPE" "?" attrs;
      rt_entities = attr_or_default "ENTITIES" "none" attrs;
      rt_uri = attr_or_default "URI" "" attrs;
      rt_sections = attr_or_default "SECTIONS" "" attrs;
      rt_description = String.trim (Parser_XML.text_content node);
      rt_leaf = leaf_rel;
      rt_collection = collection_of_leaf leaf_rel;
    } in
    t :: acc
  | Some "TESTCASES" ->
    List.fold_left (fun acc child -> collect_tests leaf_rel child acc)
      acc (Parser_XML.element_children node)
  | _ -> acc

(* Fallback for a leaf manifest that (unexpectedly) fails to
   dogfood-parse: a plain textual scan for `<TEST ...>` opening tags,
   pulling attribute values out with the same manual scanner used for
   entity discovery. Not expected to fire for any of the 19 known leaf
   files (verified while building this runner — none carry a DOCTYPE),
   but present so a future suite update that adds one doesn't silently
   drop that collection's tests. *)
let fallback_scan_tests leaf_rel content =
  let n = String.length content in
  let read_attr_value s i =
    if i < String.length s && (s.[i] = '"' || s.[i] = '\'') then
      let q = s.[i] in
      match String.index_from_opt s (i + 1) q with
      | Some e -> Some (String.sub s (i + 1) (e - i - 1), e + 1)
      | None -> None
    else None
  in
  let rec parse_attrs_from s start stop =
    let rec go i acc =
      let i = skip_ws s i in
      if i >= stop then acc
      else
        let (name, i) = read_token_until_eq s i in
        if name = "" then acc
        else
          let i = skip_ws s i in
          if i < stop && s.[i] = '=' then
            match read_attr_value s (i + 1) with
            | Some (v, i') -> go i' ((name, v) :: acc)
            | None -> acc
          else acc
    in
    go start []
  and read_token_until_eq s i =
    let n = String.length s in
    let j = ref i in
    while !j < n && s.[!j] <> '=' && not (is_ws s.[!j]) && s.[!j] <> '>' do incr j done;
    (String.sub s i (!j - i), !j)
  in
  let rec scan i acc =
    match find_substring_from content "<TEST " i with
    | None -> acc
    | Some start ->
      let close =
        match find_substring_from content ">" (start + 6) with
        | Some c -> c | None -> n
      in
      let attrs = parse_attrs_from content (start + 5) close in
      let get k d = try List.assoc k attrs with Not_found -> d in
      let desc_end =
        match find_substring_from content "</TEST>" close with
        | Some e -> e | None -> close
      in
      let desc =
        if desc_end > close then String.trim (String.sub content (close + 1) (desc_end - close - 1))
        else ""
      in
      let t = {
        rt_id = get "ID" "?"; rt_type = get "TYPE" "?";
        rt_entities = get "ENTITIES" "none"; rt_uri = get "URI" "";
        rt_sections = get "SECTIONS" ""; rt_description = desc;
        rt_leaf = leaf_rel; rt_collection = collection_of_leaf leaf_rel;
      } in
      scan (close + 1) (t :: acc)
  in
  scan 0 []

(* ------------------------------------------------------------------ *)
(* Encoding / BOM sniffing. Byte-level only — Parser.XML.fst treats
   input as a byte-indexed string (Parser.FastString), so anything
   that isn't ASCII-superset UTF-8 must be flagged, not silently
   mis-decoded. *)

let byte_at s i = if i < String.length s then Some (Char.code s.[i]) else None

let detect_bom_or_utf16 content : string option =
  let b i = match byte_at content i with Some x -> x | None -> -1 in
  if b 0 = 0xEF && b 1 = 0xBB && b 2 = 0xBF then Some "UTF-8 byte-order-mark (parser doesn't skip a BOM prefix)"
  else if b 0 = 0xFE && b 1 = 0xFF then Some "UTF-16BE (BOM detected)"
  else if b 0 = 0xFF && b 1 = 0xFE then Some "UTF-16LE (BOM detected)"
  else if b 0 = 0x00 && b 1 = 0x3C && b 2 = 0x00 && b 3 = 0x3F then Some "UTF-16BE (no BOM, null-padded '<?' detected)"
  else if b 0 = 0x3C && b 1 = 0x00 && b 2 = 0x3F && b 3 = 0x00 then Some "UTF-16LE (no BOM, null-padded '<?' detected)"
  else None

let supported_encodings = ["utf-8"; "utf8"; "us-ascii"; "ascii"]

let detect_declared_encoding content : string option =
  let scan_window = min (String.length content) 300 in
  let window = String.sub content 0 scan_window in
  let try_at kw =
    match find_substring_from window kw 0 with
    | None -> None
    | Some i ->
      let vstart = i + String.length kw in
      if vstart < String.length window && (window.[vstart] = '"' || window.[vstart] = '\'') then
        let q = window.[vstart] in
        (match String.index_from_opt window (vstart + 1) q with
         | Some e -> Some (String.sub window (vstart + 1) (e - vstart - 1))
         | None -> None)
      else None
  in
  match try_at "encoding=" with
  | Some v -> Some v
  | None -> None

let encoding_skip_reason content : string option =
  match detect_bom_or_utf16 content with
  | Some reason -> Some reason
  | None ->
    (match detect_declared_encoding content with
     | None -> None
     | Some enc ->
       let norm = String.lowercase_ascii (String.trim enc) in
       if List.mem norm supported_encodings then None
       else Some (Printf.sprintf "declared encoding %S not decoded (byte-oriented parser assumes UTF-8/ASCII)" enc))

let has_doctype content =
  find_substring_from content "<!DOCTYPE" 0 <> None

(* ------------------------------------------------------------------ *)
(* Outcome classification. *)

type outcome =
  | Pass of string
  | PassVacuous of string   (* not-wf pass caused by a structural gap (DOCTYPE), not the documented construct *)
  | Fail of string
  | Skip of string

let classify (base_dir : string) (t : raw_test) : outcome =
  if t.rt_type = "invalid" || t.rt_type = "error" then
    Skip "no DTD validation (by design)"
  else begin
    let path = Filename.concat base_dir t.rt_uri in
    match read_file path with
    | None -> Skip (Printf.sprintf "test input file not found: %s" t.rt_uri)
    | Some content ->
      match encoding_skip_reason content with
      | Some reason -> Skip reason
      | None ->
        let doctype = has_doctype content in
        if t.rt_type = "valid" then begin
          if doctype then Skip "DOCTYPE/DTD not parsed (Parser.XML.fst has no DOCTYPE production)"
          else
            match Parser_XML.parse_xml_document content with
            | Some _ -> Pass "parsed cleanly (wf-accept)"
            | None ->
              Fail (Printf.sprintf "parser rejected a document listed VALID — SECTIONS %s: %s"
                      t.rt_sections t.rt_description)
        end else if t.rt_type = "not-wf" then begin
          match Parser_XML.parse_xml_document content with
          | None ->
            if doctype then PassVacuous "rejected (vacuous: DOCTYPE present, parser can't parse any DOCTYPE at all)"
            else Pass "rejected"
          | Some _ ->
            if t.rt_entities <> "none" then
              Skip (Printf.sprintf
                      "parser accepted, but test requires external %s entities not read (exempted per testcases.dtd's TYPE=not-wf clause)"
                      t.rt_entities)
            else
              Fail (Printf.sprintf "parser incorrectly ACCEPTED a not-wf document — SECTIONS %s: %s"
                      t.rt_sections t.rt_description)
        end else
          Skip (Printf.sprintf "unrecognized TYPE %S" t.rt_type)
  end

(* ------------------------------------------------------------------ *)
(* XML_Wellformedness — informational only. See module comment: its
   NCName check excludes ':' from name-start/name characters, so it is
   RDF/XML-domain-specific and would wrongly reject plain XML 1.0
   documents that legally use ':' in Names outside a Namespaces-aware
   reading. We record how often it WOULD have flagged something, on
   accepted documents only, without gating any outcome above. *)

let rec collect_tags node acc =
  match node with
  | Parser_XML.XElement (tag, _attrs, children) ->
    List.fold_left (fun acc c -> collect_tags c acc) (tag :: acc) children
  | _ -> acc

let ncname_informational_check root =
  let tags = collect_tags root [] in
  List.fold_left
    (fun (checked, would_reject) tag ->
       (checked + 1, if XML_Wellformedness.is_valid_ncname tag then would_reject else would_reject + 1))
    (0, 0) tags

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "W3C XML Conformance Test Suite runner for Parser.XML.fst / XML.Wellformedness.fst.\n\
     \n\
     Usage:\n\
     \  ./xml_runner                Run the full vendored suite\n\
     \  ./xml_runner <xmlconf-dir>  Run from an explicit xmlconf/ dir\n\
     \  ./xml_runner -v|--verbose   Print every FAIL line as it runs\n\
     \  ./xml_runner --help         Show this help\n\
     \n\
     Scoring: TYPE=invalid/error always SKIP (no DTD validation, by\n\
     design). TYPE=valid PASS (labelled wf-accept) requires no DOCTYPE,\n\
     a decodable declared encoding, and a clean parse; a DOCTYPE or\n\
     unsupported encoding is SKIP, not FAIL. TYPE=not-wf PASS means the\n\
     parser rejected the document (regardless of why); an accept is\n\
     SKIP if the test's own ENTITIES attribute says it needs external\n\
     entities this nonvalidating parser doesn't read (testcases.dtd's\n\
     own exemption), else a genuine FAIL.\n"

module SMap = Map.Make (String)

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let dir = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | p :: rest when !dir = None -> dir := Some p; loop rest
    | _ -> Printf.eprintf "xml_runner: unexpected arguments; try --help\n"; exit 2
  in
  loop args;
  let xmlconf_dir = match !dir with Some p -> p | None -> default_xmlconf_dir () in
  Printf.printf "=== W3C XML Conformance Test Suite Runner ===\n";
  Printf.printf "xmlconf dir: %s\n\n" xmlconf_dir;
  if not (Sys.file_exists xmlconf_dir) then begin
    Printf.eprintf "xml_runner: xmlconf dir not found at %s\n" xmlconf_dir;
    exit 2
  end;
  let master_path = Filename.concat xmlconf_dir "xmlconf.xml" in
  let master_content = match read_file master_path with
    | Some c -> c
    | None -> Printf.eprintf "xml_runner: cannot read %s\n" master_path; exit 2
  in
  (* Dogfood attempt on the master manifest itself. *)
  let master_dogfood = Parser_XML.parse_xml_document master_content in
  (match master_dogfood with
   | Some _ ->
     Printf.printf "Manifest dogfood: xmlconf.xml parsed cleanly via Parser_XML (unexpected — report this as a finding).\n\n"
   | None ->
     Printf.printf
       "Manifest dogfood: xmlconf.xml parse -> None (expected: its DOCTYPE internal\n\
        subset has no production in Parser.XML.fst). Falling back to a textual scan\n\
        for <!ENTITY name SYSTEM \"path\"> declarations to discover leaf manifests.\n\n");
  let entities = discover_manifest_entities master_content in
  if entities = [] then begin
    Printf.eprintf "xml_runner: found zero <!ENTITY ... SYSTEM \"...\"> declarations in %s\n" master_path;
    exit 2
  end;
  Printf.printf "Discovered %d leaf manifest files via entity-declaration scan.\n\n" (List.length entities);
  (* Walk every leaf manifest, dogfooding Parser_XML on each. *)
  let leaf_dogfood_ok = ref 0 and leaf_dogfood_fallback = ref 0 in
  let all_tests =
    List.fold_left
      (fun acc (_name, leaf_rel) ->
         let leaf_path = Filename.concat xmlconf_dir leaf_rel in
         match read_file leaf_path with
         | None ->
           Printf.eprintf "  ! leaf manifest not found: %s (declared as %s)\n" leaf_path _name;
           acc
         | Some content ->
           let wrapped = wrap_manifest_body content in
           match Parser_XML.parse_xml_document wrapped with
           | Some root ->
             incr leaf_dogfood_ok;
             collect_tests leaf_rel root acc
           | None ->
             incr leaf_dogfood_fallback;
             Printf.eprintf
               "  ! leaf manifest %s did NOT dogfood-parse (even after TESTCASES-wrapping) — falling back to a regex scan for this file only\n"
               leaf_rel;
             fallback_scan_tests leaf_rel content @ acc)
      [] entities
  in
  Printf.printf "Leaf manifests dogfood-parsed cleanly: %d; needed textual fallback: %d (of %d).\n\n"
    !leaf_dogfood_ok !leaf_dogfood_fallback (List.length entities);
  let total = List.length all_tests in
  Printf.printf "Total <TEST> entries discovered: %d\n\n" total;
  if total = 0 then begin
    Printf.eprintf "xml_runner: discovered zero TEST entries; nothing to run\n";
    exit 2
  end;
  (* Run every test. *)
  let vacuous_count = ref 0 in
  let ncname_checked = ref 0 and ncname_would_reject = ref 0 in
  let results =
    List.map
      (fun t ->
         let base_dir = Filename.dirname (Filename.concat xmlconf_dir t.rt_leaf) in
         let outcome = classify base_dir t in
         (match outcome with
          | PassVacuous _ -> incr vacuous_count
          | _ -> ());
         (* Informational NCName pass over accepted documents only. *)
         (match outcome with
          | Pass _ | PassVacuous _ ->
            let path = Filename.concat base_dir t.rt_uri in
            (match read_file path with
             | Some content ->
               (match Parser_XML.parse_xml_document content with
                | Some root ->
                  let (c, r) = ncname_informational_check root in
                  ncname_checked := !ncname_checked + c;
                  ncname_would_reject := !ncname_would_reject + r
                | None -> ())
             | None -> ())
          | _ -> ());
         if !verbose then begin
           match outcome with
           | Fail msg -> Printf.eprintf "FAIL %s (%s): %s\n" t.rt_id t.rt_leaf msg
           | _ -> ()
         end;
         (t, outcome))
      all_tests
  in
  (* ---------------------------------------------------------------- *)
  (* Tally helpers. *)
  let tally_bucket key_fn results =
    List.fold_left
      (fun m (t, o) ->
         let key = key_fn t in
         let (p, f, s) = try SMap.find key m with Not_found -> (0, 0, 0) in
         let (p, f, s) = match o with
           | Pass _ | PassVacuous _ -> (p + 1, f, s)
           | Fail _ -> (p, f + 1, s)
           | Skip _ -> (p, f, s + 1)
         in
         SMap.add key (p, f, s) m)
      SMap.empty results
  in
  let print_bucket_table title key_fn =
    let m = tally_bucket key_fn results in
    Printf.printf "-- %s --\n" title;
    SMap.iter
      (fun key (p, f, s) ->
         Printf.printf "  %-12s pass:%-5d fail:%-5d skip:%-5d (of %d)\n" key p f s (p + f + s))
      m;
    Printf.printf "\n"
  in
  print_bucket_table "Per collection" (fun t -> t.rt_collection);
  print_bucket_table "Per TYPE bucket" (fun t -> t.rt_type);
  (* ---------------------------------------------------------------- *)
  (* Fail cluster table: group by (TYPE, SECTIONS), show a couple of
     example IDs + descriptions per cluster rather than every
     filename. *)
  let fails = List.filter_map (fun (t, o) -> match o with Fail msg -> Some (t, msg) | _ -> None) results in
  Printf.printf "-- FAIL cluster table (%d total FAILs) --\n" (List.length fails);
  let cluster_key (t, _msg) = Printf.sprintf "%-8s SECTIONS %s" t.rt_type t.rt_sections in
  let clusters =
    List.fold_left
      (fun m ((t, _msg) as entry) ->
         let key = cluster_key entry in
         let existing = try SMap.find key m with Not_found -> [] in
         SMap.add key (entry :: existing) m)
      SMap.empty fails
  in
  let cluster_list = SMap.bindings clusters |> List.map (fun (k, v) -> (k, List.rev v)) in
  let cluster_list = List.sort (fun (_, a) (_, b) -> compare (List.length b) (List.length a)) cluster_list in
  List.iter
    (fun (key, entries) ->
       Printf.printf "  [%d] %s\n" (List.length entries) key;
       List.iteri
         (fun i (t, _msg) ->
            if i < 3 then
              Printf.printf "        e.g. %s (%s): %s\n" t.rt_id t.rt_leaf
                (if String.length t.rt_description > 100
                 then String.sub t.rt_description 0 100 ^ "..."
                 else t.rt_description))
         entries)
    cluster_list;
  Printf.printf "\n";
  (* ---------------------------------------------------------------- *)
  (* SKIP reason breakdown. Most reasons are fixed constant strings
     (grouped as-is); the two with per-test interpolated text
     ("declared encoding %S not decoded" and "test input file not
     found: <uri>") are explicitly normalized here rather than via a
     naive "split on first ':' or '\"'" scan — several encoding
     VALUES themselves contain ':' or other punctuation (e.g. the
     not-wf encoding-name tests ibm81n05..09's "UTF~8"/"UTF#8"/
     "UTF;8"/"UTF/8", sun/not-wf/encoding04.xml's "utf:8"), and a
     naive scan mis-split inside the quoted value, producing a
     truncated, misleading bucket label — caught while building this
     report. *)
  let has_prefix s pre =
    let pn = String.length pre and n = String.length s in
    n >= pn && String.sub s 0 pn = pre
  in
  let skip_key msg =
    if has_prefix msg "declared encoding " then
      (match String.index_opt msg '"' with
       | Some i1 ->
         (match String.index_from_opt msg (i1 + 1) '"' with
          | Some i2 -> "declared encoding " ^ String.sub msg i1 (i2 - i1 + 1) ^ " not decoded"
          | None -> "declared encoding <unparsed> not decoded")
       | None -> "declared encoding <unparsed> not decoded")
    else if has_prefix msg "test input file not found" then "test input file not found"
    else if String.length msg > 70 then String.sub msg 0 70 ^ "..."
    else msg
  in
  let skips = List.filter_map (fun (_t, o) -> match o with Skip msg -> Some msg | _ -> None) results in
  Printf.printf "-- SKIP reason breakdown (%d total SKIPs) --\n" (List.length skips);
  let skip_buckets =
    List.fold_left
      (fun m msg ->
         let key = skip_key msg in
         let n = try SMap.find key m with Not_found -> 0 in
         SMap.add key (n + 1) m)
      SMap.empty skips
  in
  SMap.bindings skip_buckets
  |> List.sort (fun (_, a) (_, b) -> compare b a)
  |> List.iter (fun (key, n) -> Printf.printf "  %-6d %s\n" n key);
  Printf.printf "\n";
  (* ---------------------------------------------------------------- *)
  (* Grand total. *)
  let pass = List.length (List.filter (fun (_, o) -> match o with Pass _ | PassVacuous _ -> true | _ -> false) results) in
  let fail = List.length fails in
  let skip = List.length skips in
  Printf.printf "========================================\n";
  Printf.printf "TOTAL: %d pass, %d fail, %d skip (of %d)\n" pass fail skip total;
  Printf.printf "  of which %d not-wf PASSes are vacuous (rejection forced by an unrelated\n" !vacuous_count;
  Printf.printf "  DOCTYPE-not-supported gap, not necessarily the test's documented construct)\n";
  Printf.printf
    "XML_Wellformedness.is_valid_ncname (informational only, see module comment):\n\
    \  checked %d element tags across accepted documents; %d would have been\n\
    \  rejected by the NCName production (expected — it excludes ':' from Name\n\
    \  start/continue characters, which is an RDF/XML-domain rule, not generic\n\
    \  XML conformance; plain XML 1.0 legally allows ':' in Names).\n"
    !ncname_checked !ncname_would_reject;
  Printf.printf "========================================\n";
  Printf.printf "xml-conformance: %d pass, %d fail, %d skip (of %d)\n" pass fail skip total;
  if fail > 0 then exit 1
