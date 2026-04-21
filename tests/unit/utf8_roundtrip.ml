(* utf8_roundtrip.ml — UTF-8 byte preservation through
   N-Triples parse -> F* in-memory term -> result serialiser.

   This exercises issue #91 (UTF-8 corruption in js engine output). We run
   NATIVELY here (ocamlfind ocamlopt), so if every assertion passes, that
   LOCATES the bug as js_of_ocaml-runtime-only — useful diagnostic
   information for whoever picks up #91.

   Each case goes:
     1. Build an N-Triples line with the literal as its object.
     2. Parse it with Parser_NTriples.parse_ntriples.
     3. Pull the parsed literal's lexical_form bytes and compare them
        byte-for-byte to the original UTF-8 input.
     4. Emit the literal as a JSON results row using the same json_term
        formatting that factoidal_cli uses, capture into a Buffer, and
        assert the original bytes appear verbatim in the JSON output.

   Two of the six cases (the emoji and the CJK string) live at the
   boundary of OCaml's byte-oriented string API and the F* extraction;
   historically these are where issue #91 surfaced. They are asserted as
   PASS on the native path — a regression would flip them to FAIL. *)

open RDF_Graph_Executable

let passed = ref 0
let failed = ref 0
let expected_failures = ref 0

let check ~name ~expected_pass ok_bool =
  if ok_bool then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else if not expected_pass then begin
    incr expected_failures;
    Printf.printf "  XFAIL %s  (documented limitation)\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

(* Minimal JSON serialiser, kept in sync with factoidal_cli.print_results_json.
   We only need the term half; the surrounding {"head": ..., "results": ...}
   envelope is tested by its inclusion in factoidal_cli and is not what #91
   is about. *)
let json_escape s =
  let b = Buffer.create (String.length s) in
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | '\n' -> Buffer.add_string b "\\n"
    | '\r' -> Buffer.add_string b "\\r"
    | '\t' -> Buffer.add_string b "\\t"
    | c when Char.code c < 0x20 ->
        Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c
  ) s;
  Buffer.contents b

let json_term t =
  match t with
  | T_IRI i -> Printf.sprintf "{\"type\":\"uri\",\"value\":\"%s\"}" (json_escape i)
  | T_BNode b -> Printf.sprintf "{\"type\":\"bnode\",\"value\":\"%s\"}" (json_escape b)
  | T_Literal l ->
      let xsd_string = "http://www.w3.org/2001/XMLSchema#string" in
      (match l.lang_tag with
       | Some tag ->
           Printf.sprintf "{\"type\":\"literal\",\"value\":\"%s\",\"xml:lang\":\"%s\"}"
             (json_escape l.lexical_form) (json_escape tag)
       | None ->
           if l.datatype = "" || l.datatype = xsd_string then
             Printf.sprintf "{\"type\":\"literal\",\"value\":\"%s\"}"
               (json_escape l.lexical_form)
           else
             Printf.sprintf "{\"type\":\"literal\",\"value\":\"%s\",\"datatype\":\"%s\"}"
               (json_escape l.lexical_form) (json_escape l.datatype))

let build_ntriples lit lang =
  let obj =
    if lang = "" then Printf.sprintf "\"%s\"" lit
    else Printf.sprintf "\"%s\"@%s" lit lang
  in
  Printf.sprintf "<http://ex/s> <http://ex/p> %s .\n" obj

let extract_lit triples =
  match triples with
  | [] -> None
  | t :: _ ->
      (match t.o with
       | T_Literal l -> Some l
       | _ -> None)

let run_case ~name ~expected_pass lit lang =
  let nt = build_ntriples lit lang in
  let triples = Parser_NTriples.parse_ntriples nt in
  (match extract_lit triples with
   | None ->
       check ~name:(name ^ " [parse]") ~expected_pass false
   | Some l ->
       check ~name:(name ^ " [lexical-bytes-roundtrip]") ~expected_pass
         (l.lexical_form = lit);
       let j = json_term (T_Literal l) in
       let contains hay needle =
         let hl = String.length hay and nl = String.length needle in
         let rec scan i =
           if i + nl > hl then false
           else if String.sub hay i nl = needle then true
           else scan (i + 1)
         in
         scan 0
       in
       check ~name:(name ^ " [bytes-in-json-output]") ~expected_pass
         (contains j lit))

let () =
  Printf.printf "== utf8_roundtrip ==\n";
  let cases = [
    "umlaut-de",      "Eve M\xc3\xbcller",               "de";   (* U+00FC *)
    "french-grave",   "Cafeti\xc3\xa8re",                "";     (* U+00E8 *)
    "umlaut-bare",    "Ralf H\xc3\xbctter",              "";
    "umlaut-mixed",   "G\xc3\xb6del, Escher, Bach",      "";     (* U+00F6 *)
    "cjk",            "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e", "ja";  (* 日本語 *)
    "emoji-music",    "\xf0\x9f\x8e\xb5",                "";     (* U+1F3B5 🎵 *)
  ] in
  List.iter (fun (name, lit, lang) ->
    run_case ~name ~expected_pass:true lit lang
  ) cases;
  Printf.printf "summary: %d pass, %d expected-fail, %d unexpected fail\n"
    !passed !expected_failures !failed;
  if !failed > 0 then exit 1
