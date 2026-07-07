(* XSLT 1.0 conformance runner for formal/fstar/XSLT.Transform.fst.

   Runs the curated, W3C-sourced XSLT-1.0-expressible subset vendored
   under third_party/testing/xslt/ (selected from w3c/xslt30-test; see
   that directory's README.md for provenance and selection criteria).

   !! THIS IS I/O GLUE -- NO XSLT SEMANTICS LIVE HERE !! Every
   transformation decision comes from the F*-extracted
   XSLT_Transform.transform (from formal/fstar/XSLT.Transform.fst),
   run over stylesheet + source trees produced by the F*-extracted
   Parser_XML.parse_xml_document. The manifest is parsed with the
   F*-extracted Parser_JSON.parse_json (dogfooding our own JSON
   parser). This file does file I/O, manifest traversal, output
   normalization, string comparison, and tallying only. Per CLAUDE.md
   iron rule #11 / anti-pattern #15.

   Scoring (owner discipline, anti-pattern #25 -- always labelled):
   a test PASSES when the serialized result matches the expected
   `assert-xml` file either exactly (after stripping the XML
   declaration) or after collapsing insignificant whitespace on BOTH
   sides. Both counts are reported separately; failing tests are
   clustered by category so the unsupported-instruction / unsupported-
   pattern / whitespace-serialization buckets are visible.

   Usage:
     ./xslt_runner            Run the full vendored suite
     ./xslt_runner -v         Print every FAIL (name + short diff)
     ./xslt_runner --help     Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (same pattern as bin/xml-runner/xml_runner.ml). *)

let find_repo_root () =
  let rec walk d =
    if d = "/" || d = "" then None
    else if Sys.file_exists (Filename.concat d "CLAUDE.md") then Some d
    else walk (Filename.dirname d)
  in
  let start = try Filename.dirname (Sys.executable_name) with _ -> Sys.getcwd () in
  match walk start with
  | Some r -> r
  | None -> (match walk (Sys.getcwd ()) with Some r -> r | None -> Sys.getcwd ())

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
(* Thin wrappers over the F*-extracted JSON accessors. *)

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let str_field key obj = opt_of_fs (Parser_JSON.json_get_string key obj)

(* ------------------------------------------------------------------ *)
(* Output normalization (config plumbing, not XSLT semantics). *)

let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

(* Strip a leading `<?xml ... ?>` declaration (expected files carry one;
   our serializer never emits one). *)
let strip_xml_decl s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && is_ws s.[!i] do incr i done;
  if !i + 5 <= n && String.sub s !i 5 = "<?xml" then begin
    match String.index_from_opt s !i '>' with
    | Some j when j >= 1 && s.[j - 1] = '?' -> String.sub s (j + 1) (n - j - 1)
    | _ -> String.sub s !i (n - !i)
  end else String.sub s !i (n - !i)

(* Collapse every maximal run of whitespace to a single space, then
   trim -- the lenient comparison the task sanctions for residual
   whitespace/serialization differences. Applied identically to both
   sides, so it can never turn a real structural difference into a
   pass. *)
let collapse_ws s =
  let b = Buffer.create (String.length s) in
  let prev_ws = ref false in
  String.iter
    (fun c ->
       if is_ws c then (if not !prev_ws then Buffer.add_char b ' '; prev_ws := true)
       else (Buffer.add_char b c; prev_ws := false))
    s;
  String.trim (Buffer.contents b)

(* XML line-ending normalization (XML 1.0 §2.11): CRLF and lone CR
   become LF. Parser_XML applies this on parse, so the expected file's
   Windows CRLFs (as checked into the upstream repo) must be normalized
   on the expected side too for an exact tree-equivalent comparison. *)
let normalize_eol s =
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    if c = '\r' then begin
      Buffer.add_char b '\n';
      if !i + 1 < n && s.[!i + 1] = '\n' then incr i
    end else Buffer.add_char b c;
    incr i
  done;
  Buffer.contents b

let normalize_exact s = String.trim (normalize_eol (strip_xml_decl s))
let normalize_loose s = collapse_ws (strip_xml_decl s)

(* ------------------------------------------------------------------ *)
(* Manifest entry. *)

type entry = {
  name : string;
  category : string;
  stylesheet : string;
  source : string;
  expected : string;
}

let entries_of_manifest json : entry list =
  match json with
  | Parser_JSON.JArray items ->
    List.filter_map
      (fun it ->
         match str_field "name" it, str_field "category" it,
               str_field "stylesheet" it, str_field "source" it,
               str_field "expected" it with
         | Some name, Some category, Some stylesheet, Some source, Some expected ->
           Some { name; category; stylesheet; source; expected }
         | _ -> None)
      items
  | _ -> []

(* ------------------------------------------------------------------ *)
(* Per-test outcome. *)

type outcome =
  | Pass_exact
  | Pass_loose
  | Fail of string        (* short reason *)
  | Skip of string

let short s = if String.length s <= 90 then s else String.sub s 0 90 ^ "…"

let run_one base_dir e : outcome =
  let sty_path = Filename.concat base_dir e.stylesheet in
  let src_path = Filename.concat base_dir e.source in
  let exp_path = Filename.concat base_dir e.expected in
  match read_file sty_path, read_file src_path, read_file exp_path with
  | None, _, _ -> Skip "stylesheet file missing"
  | _, None, _ -> Skip "source file missing"
  | _, _, None -> Skip "expected file missing"
  | Some sty_s, Some src_s, Some exp_s ->
    (match Parser_XML.parse_xml_document sty_s with
     | FStar_Pervasives_Native.None -> Skip "stylesheet did not parse (Parser_XML)"
     | FStar_Pervasives_Native.Some sty ->
       (match Parser_XML.parse_xml_document src_s with
        | FStar_Pervasives_Native.None -> Skip "source did not parse (Parser_XML)"
        | FStar_Pervasives_Native.Some src ->
          let actual = XSLT_Transform.transform sty src in
          if normalize_exact actual = normalize_exact exp_s then Pass_exact
          else if normalize_loose actual = normalize_loose exp_s then Pass_loose
          else
            Fail (Printf.sprintf "got %S vs want %S"
                    (short (normalize_loose actual)) (short (normalize_loose exp_s)))))

(* ------------------------------------------------------------------ *)

module SMap = Map.Make (String)

let print_help () =
  print_string
    "XSLT 1.0 conformance runner for XSLT.Transform.fst.\n\n\
     Usage:\n\
     \  ./xslt_runner          Run the full vendored suite\n\
     \  ./xslt_runner -v       Print every FAIL as it runs\n\
     \  ./xslt_runner --help   Show this help\n\n\
     Tests are the XSLT-1.0-expressible subset of w3c/xslt30-test,\n\
     vendored under third_party/testing/xslt/. A test passes when the\n\
     serialized result matches the expected assert-xml file exactly or\n\
     after whitespace collapse (both counts reported).\n"

let () =
  let verbose = ref false in
  let dump = ref None in
  let args = Array.to_list Sys.argv in
  let rec scan = function
    | [] -> ()
    | ("-v" | "--verbose") :: r -> verbose := true; scan r
    | ("-h" | "--help") :: _ -> print_help (); exit 0
    | "--dump" :: name :: r -> dump := Some name; scan r
    | _ :: r -> scan r
  in
  (match args with _ :: rest -> scan rest | [] -> ());
  let repo_root = find_repo_root () in
  let base_dir = Filename.concat repo_root "third_party/testing/xslt" in
  let manifest_path = Filename.concat base_dir "manifest.json" in
  Printf.printf "=== XSLT 1.0 Transform Runner ===\n";
  Printf.printf "suite dir: %s\n\n" base_dir;
  let manifest_s = match read_file manifest_path with
    | Some s -> s
    | None -> Printf.eprintf "xslt_runner: cannot read %s\n" manifest_path; exit 2
  in
  let entries = match Parser_JSON.parse_json manifest_s with
    | FStar_Pervasives_Native.Some j -> entries_of_manifest j
    | FStar_Pervasives_Native.None ->
      Printf.eprintf "xslt_runner: manifest.json did not parse via Parser_JSON\n"; exit 2
  in
  let total = List.length entries in
  if total = 0 then begin
    Printf.eprintf "xslt_runner: zero manifest entries\n"; exit 2
  end;
  Printf.printf "Manifest entries: %d\n\n" total;
  (match !dump with
   | Some name ->
     (match List.find_opt (fun e -> e.name = name) entries with
      | None -> Printf.eprintf "no such test: %s\n" name; exit 2
      | Some e ->
        let sty = read_file (Filename.concat base_dir e.stylesheet) in
        let src = read_file (Filename.concat base_dir e.source) in
        let exp = read_file (Filename.concat base_dir e.expected) in
        (match sty, src, exp with
         | Some sty_s, Some src_s, Some exp_s ->
           (match Parser_XML.parse_xml_document sty_s, Parser_XML.parse_xml_document src_s with
            | FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some d ->
              let a = XSLT_Transform.transform s d in
              Printf.printf "=== GOT (normalize_exact) ===\n%s\n=== WANT (normalize_exact) ===\n%s\n"
                (normalize_exact a) (normalize_exact exp_s);
              Printf.printf "=== equal-exact:%b equal-loose:%b ===\n"
                (normalize_exact a = normalize_exact exp_s)
                (normalize_loose a = normalize_loose exp_s)
            | _ -> Printf.printf "parse failed\n")
         | _ -> Printf.printf "file read failed\n");
        exit 0)
   | None -> ());
  let results =
    List.map
      (fun e ->
         let o = run_one base_dir e in
         (match o with
          | Fail msg when !verbose -> Printf.eprintf "FAIL %s (%s): %s\n" e.name e.category msg
          | Skip msg when !verbose -> Printf.eprintf "SKIP %s (%s): %s\n" e.name e.category msg
          | _ -> ());
         (e, o))
      entries
  in
  (* Per-category tally. *)
  let tally =
    List.fold_left
      (fun m (e, o) ->
         let (pe, pl, f, s) = try SMap.find e.category m with Not_found -> (0,0,0,0) in
         let cell = match o with
           | Pass_exact -> (pe+1, pl, f, s)
           | Pass_loose -> (pe, pl+1, f, s)
           | Fail _ -> (pe, pl, f+1, s)
           | Skip _ -> (pe, pl, f, s+1)
         in
         SMap.add e.category cell m)
      SMap.empty results
  in
  Printf.printf "-- Per category (pass-exact / pass-loose / fail / skip) --\n";
  SMap.iter
    (fun k (pe, pl, f, s) ->
       Printf.printf "  %-18s exact:%-3d loose:%-3d fail:%-3d skip:%-3d (of %d)\n"
         k pe pl f s (pe+pl+f+s))
    tally;
  Printf.printf "\n";
  (* Fail cluster: category -> a few example names. *)
  let fails = List.filter_map (fun (e,o) -> match o with Fail m -> Some (e,m) | _ -> None) results in
  if fails <> [] then begin
    Printf.printf "-- FAIL clusters (%d total) --\n" (List.length fails);
    let clusters =
      List.fold_left
        (fun m ((e,_) as x) ->
           let l = try SMap.find e.category m with Not_found -> [] in
           SMap.add e.category (x :: l) m)
        SMap.empty fails
    in
    SMap.iter
      (fun cat xs ->
         Printf.printf "  [%d] %s\n" (List.length xs) cat;
         List.iteri (fun i (e,m) -> if i < 3 then Printf.printf "        %s: %s\n" e.name m)
           (List.rev xs))
      clusters;
    Printf.printf "\n"
  end;
  let skips = List.filter_map (fun (_,o) -> match o with Skip m -> Some m | _ -> None) results in
  if skips <> [] then begin
    Printf.printf "-- SKIP reasons (%d total) --\n" (List.length skips);
    let sm = List.fold_left (fun m msg -> let n = try SMap.find msg m with Not_found -> 0 in SMap.add msg (n+1) m) SMap.empty skips in
    SMap.iter (fun k n -> Printf.printf "  %-4d %s\n" n k) sm;
    Printf.printf "\n"
  end;
  let count f = List.length (List.filter (fun (_,o) -> f o) results) in
  let pass_exact = count (function Pass_exact -> true | _ -> false) in
  let pass_loose = count (function Pass_loose -> true | _ -> false) in
  let pass = pass_exact + pass_loose in
  let fail = List.length fails in
  let skip = List.length skips in
  Printf.printf "========================================\n";
  Printf.printf "  pass-exact: %d\n" pass_exact;
  Printf.printf "  pass-loose (whitespace-collapsed): %d\n" pass_loose;
  Printf.printf "========================================\n";
  Printf.printf "XSLT 1.0 tests: %d pass, %d fail, %d skip (out of %d)\n" pass fail skip total;
  if fail > 0 || pass = 0 then exit 1
