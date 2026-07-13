(* EECC VC/DID interop fixture runner — Track B1 of
   docs/designissues/2026-07-11-vc-canivc-eecc-plan.md.

   Mirrors bin/vc-runner/vc_runner.ml's pattern (an offline OCaml
   consumer driving F*-extracted VC modules directly against vendored
   fixture files, no HTTP, no toolchain needed at test time) but over
   the EECC fixtures vendored at third_party/testing/eecc/ (see that
   directory's PROVENANCE.md for exactly what was vendored and why).

   Two Apache-2.0 EECC repos are vendored there:
     - vc-verifier-rules — 4 real, DataIntegrityProof-signed W3C VCDM
       2.0 credentials (src/tests/example_chain/*.json), a JWT-VC
       example, and 6 JSON Schema files.
     - webuild-attestations — SD-JWT / mdoc schema + sample-data JSON
       (a different credential serialization entirely, not JSON-LD).

   Classification (path-based, not content-sniffed — the vendored set
   is small and curated, and PROVENANCE.md documents exactly which
   file is which, so this runner encodes the same classification
   rather than re-deriving it heuristically):

     - "vc-verifier-rules/src/tests/example_chain/*.json" (4 files) is
       the ONLY set classified VCDM_Credential: real W3C VCDM 2.0
       JSON-LD credentials, each carrying an eddsa-rdfc-2022
       DataIntegrityProof. For these, TWO checks are scored per file:
         1. structural — VC_Credential.vc_check_from_string (the same
            Stage-1 checker vc_runner scores 117/0 with). Expected
            PASS: these are real, currently-valid GS1 credentials, not
            adversarial test vectors.
         2. crypto — SKIPPED, not attempted. Every fixture's
            verificationMethod is a did:web URL; resolving it to an
            actual Ed25519 public key needs live HTTPS DID resolution,
            which this offline runner does not do (no network I/O in a
            test runner — offline-reproducible per CLAUDE.md), and no
            public key material is bundled in the fixture JSON itself.
            This is the "unverifiable-by-design" case: the structural
            shape is fully checkable offline, the signature is not,
            without fabricating key material nobody vendored.

     - Every other vendored *.json / *.jwt file (JSON Schemas, SD-JWT
       claim sets, mdoc claim sets, the one JWT-VC example) is SKIPPED
       with reason "not a W3C VCDM JSON-LD credential" — feeding a
       JSON Schema document or an SD-JWT claims object through the
       JSON-LD structural checker would produce a spurious FAIL (no
       @context, no type: VerifiableCredential) that misreports a
       FORMAT mismatch as a structural defect. Honest skip, not a
       guessed verdict.

   !! THIS IS I/O GLUE — NO VC STRUCTURAL-VALIDATION OR CRYPTO LOGIC !!
   Every check lives in formal/fstar/VC.Credential.fst /
   VC.DataIntegrity.fst. This file only does file I/O, directory
   traversal, path-based classification, and tallying — per CLAUDE.md
   iron rule #11 / anti-pattern #15.

   Usage:
     ./eecc_runner                Run the default fixture directory
     ./eecc_runner <dir>          Run fixtures from a specific directory
     ./eecc_runner --list         List classified fixtures (no execution)
     ./eecc_runner --json <path>  Also write a flat JSON result file
                                   (same shape as tests/vc-di-eddsa's
                                   run.sh output — pass/fail/skip/total
                                   — for generate-report.sh's
                                   scrape_json_result)
     ./eecc_runner --help         Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to vc_runner.ml). *)

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

let fixture_dir_candidates () =
  let repo_root = find_repo_root () in
  [ Filename.concat repo_root "third_party/testing/eecc";
    "third_party/testing/eecc";
    "../../third_party/testing/eecc";
    "../../../third_party/testing/eecc" ]

let default_fixture_dir () =
  try List.find Sys.file_exists (fixture_dir_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ()) "third_party/testing/eecc"

(* ------------------------------------------------------------------ *)
(* File I/O + directory walk (same shape as vc_runner.ml). *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let rec collect_fixture_files dir =
  match Sys.readdir dir with
  | exception Sys_error _ -> []
  | entries ->
    Array.to_list entries
    |> List.sort compare
    |> List.concat_map (fun name ->
      let path = Filename.concat dir name in
      if Sys.is_directory path then collect_fixture_files path
      else if Filename.check_suffix name ".json"
           || Filename.check_suffix name ".jwt" then [ path ]
      else [])

(* ------------------------------------------------------------------ *)
(* Path-based classification (see header comment). *)

type kind =
  | VCDM_Credential          (* structural + crypto both scored *)
  | Non_VCDM of string       (* skip reason *)

let has_substring ~needle hay =
  let nl = String.length needle and hl = String.length hay in
  if nl = 0 then true
  else
    let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
    go 0

let classify path =
  if has_substring ~needle:"vc-verifier-rules/src/tests/example_chain/" path
     && Filename.check_suffix path ".json"
  then VCDM_Credential
  else if Filename.check_suffix path ".jwt" then
    Non_VCDM "JWT-VC compact serialization (JWS), not JSON-LD Data \
              Integrity — VC.Credential.fst / VC.DataIntegrity.fst \
              target W3C VCDM JSON-LD credentials only"
  else if has_substring ~needle:"json-schema/" path
       || has_substring ~needle:"data-schemas/" path
          && not (has_substring ~needle:"sample-data/" path)
  then
    Non_VCDM "JSON Schema document (a credential SHAPE definition), \
              not a credential instance — nothing to structurally check"
  else
    Non_VCDM "not a W3C VCDM JSON-LD credential (SD-JWT / mdoc claim \
              set) — outside VC.Credential.fst's structural-checker \
              scope, which targets JSON-LD credentials with @context \
              + type: VerifiableCredential"

(* ------------------------------------------------------------------ *)
(* Vendored VCDM v2 base context loader (identical to vc_runner.ml —
   see that file's comment for why this is I/O glue, not logic). *)

let v2_context_path_candidates () =
  let repo_root = find_repo_root () in
  [ Filename.concat repo_root "third_party/contexts/credentials-v2.jsonld";
    "third_party/contexts/credentials-v2.jsonld";
    "../../third_party/contexts/credentials-v2.jsonld";
    "../../../third_party/contexts/credentials-v2.jsonld" ]

let load_v2_context () =
  let path =
    try List.find Sys.file_exists (v2_context_path_candidates ())
    with Not_found ->
      Printf.eprintf
        "eecc_runner: vendored VCDM v2 context not found (third_party/contexts/credentials-v2.jsonld)\n";
      exit 2
  in
  match read_file path with
  | None ->
    Printf.eprintf "eecc_runner: could not read vendored v2 context at %s\n" path; exit 2
  | Some txt ->
    (match Parser_JSON.parse_json txt with
     | Some v -> v
     | None ->
       Printf.eprintf "eecc_runner: vendored v2 context at %s is not well-formed JSON\n" path;
       exit 2)

(* ------------------------------------------------------------------ *)
(* Outcome + per-check execution. Each VCDM_Credential fixture yields
   TWO scored units (structural, crypto); each Non_VCDM fixture yields
   ONE (format-mismatch skip). *)

type outcome = Pass | Fail of string | Skip of string

type unit_result = { fixture : string; check : string; outcome : outcome }

let run_structural v2ctx path content =
  match VC_Credential.vc_check_from_string v2ctx content with
  | VC_Credential.VC_Pass -> Pass
  | VC_Credential.VC_Fail reason ->
    Fail (Printf.sprintf "structural check rejected a real-world EECC \
                           credential (%s): %s" (Filename.basename path) reason)

let crypto_skip_reason =
  "verificationMethod is a did:web URL — resolving it to an actual \
   Ed25519 public key needs live HTTPS DID resolution, which this \
   offline, network-free runner does not perform, and no public key \
   material is bundled in the vendored fixture; unverifiable-by-design \
   offline, not a failed verification"

let run_fixture v2ctx path : unit_result list =
  match classify path with
  | Non_VCDM reason ->
    [ { fixture = path; check = "format"; outcome = Skip reason } ]
  | VCDM_Credential ->
    (match read_file path with
     | None ->
       [ { fixture = path; check = "structural"; outcome = Fail "could not read file" } ]
     | Some content ->
       [ { fixture = path; check = "structural"; outcome = run_structural v2ctx path content };
         { fixture = path; check = "crypto"; outcome = Skip crypto_skip_reason } ])

(* ------------------------------------------------------------------ *)
(* JSON result-file writer (optional --json flag), same flat shape as
   tests/vc-di-eddsa/run.sh's Python-written JSON — read by
   formal/fstar/generate-report.sh's scrape_json_result. Pure
   formatting/I/O glue, not a new result format invented ad hoc: same
   keys (spec/suite/runner/retrieved_at/pass/fail/skip/total/present),
   additive only. *)

let json_escape s =
  let b = Buffer.create (String.length s + 8) in
  String.iter
    (fun c ->
       match c with
       | '"' -> Buffer.add_string b "\\\""
       | '\\' -> Buffer.add_string b "\\\\"
       | '\n' -> Buffer.add_string b "\\n"
       | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
       | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let write_json_result path ~pass ~fail ~skip ~total (results : unit_result list) =
  let oc = open_out path in
  let now =
    let t = Unix.gmtime (Unix.time ()) in
    Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02dZ"
      (t.Unix.tm_year + 1900) (t.Unix.tm_mon + 1) t.Unix.tm_mday
      t.Unix.tm_hour t.Unix.tm_min t.Unix.tm_sec
  in
  Printf.fprintf oc "{\n";
  Printf.fprintf oc "  \"spec\": \"https://github.com/european-epc-competence-center\",\n";
  Printf.fprintf oc "  \"suite\": \"eecc-interop (vendored vc-verifier-rules + webuild-attestations fixtures)\",\n";
  Printf.fprintf oc "  \"runner\": \"bin/eecc-runner/eecc_runner.ml\",\n";
  Printf.fprintf oc "  \"retrieved_at\": \"%s\",\n" now;
  Printf.fprintf oc "  \"pass\": %d,\n" pass;
  Printf.fprintf oc "  \"fail\": %d,\n" fail;
  Printf.fprintf oc "  \"skip\": %d,\n" skip;
  Printf.fprintf oc "  \"total\": %d,\n" total;
  Printf.fprintf oc "  \"present\": true,\n";
  let fails =
    List.filter (fun r -> match r.outcome with Fail _ -> true | _ -> false) results
  in
  Printf.fprintf oc "  \"failures\": [\n";
  List.iteri
    (fun i r ->
       let msg = match r.outcome with Fail m -> m | _ -> "" in
       Printf.fprintf oc "    {\"fixture\": \"%s\", \"check\": \"%s\", \"message\": \"%s\"}%s\n"
         (json_escape (Filename.basename r.fixture)) (json_escape r.check) (json_escape msg)
         (if i = List.length fails - 1 then "" else ","))
    fails;
  Printf.fprintf oc "  ]\n";
  Printf.fprintf oc "}\n";
  close_out oc

(* ------------------------------------------------------------------ *)
(* Suite run. *)

let run_suite ~verbose ~list_only ~json_out fixture_dir =
  Printf.printf "=== EECC VC/DID Interop Fixture Runner (Track B1) ===\n";
  Printf.printf "Fixture dir: %s\n\n" fixture_dir;
  let files = collect_fixture_files fixture_dir in
  let total_files = List.length files in
  Printf.printf "Totals: %d vendored fixture files\n\n" total_files;
  if total_files = 0 then begin
    Printf.eprintf "eecc_runner: no fixtures found under %s\n" fixture_dir;
    Printf.eprintf "  (vendored third_party/testing/eecc/ missing? see its PROVENANCE.md)\n";
    exit 2
  end;
  if list_only then
    List.iter
      (fun path ->
         let label = match classify path with
           | VCDM_Credential -> "vcdm-cred"
           | Non_VCDM _ -> "non-vcdm "
         in
         Printf.printf "  [%s] %s\n" label
           (Filename.concat (Filename.basename (Filename.dirname path)) (Filename.basename path)))
      files
  else begin
    let v2ctx = load_v2_context () in
    let results = List.concat_map (run_fixture v2ctx) files in
    List.iter
      (fun r ->
         let name = Filename.basename r.fixture in
         match r.outcome with
         | Pass -> Printf.printf "  PASS [%s]: %s\n" r.check name
         | Fail msg -> Printf.printf "  FAIL [%s]: %s — %s\n" r.check name msg
         | Skip msg -> if verbose then Printf.printf "  skip [%s]: %s — %s\n" r.check name msg)
      results;
    let pass, fail, skip =
      List.fold_left
        (fun (p, f, s) r ->
           match r.outcome with
           | Pass -> (p + 1, f, s)
           | Fail _ -> (p, f + 1, s)
           | Skip _ -> (p, f, s + 1))
        (0, 0, 0) results
    in
    let total = List.length results in
    Printf.printf "\n========================================\n";
    Printf.printf "TOTAL: %d pass, %d fail, %d skip (out of %d checks, over %d fixture files)\n"
      pass fail skip total total_files;
    Printf.printf "========================================\n";
    (* Tagged final line for generate-report.sh's generic score-line
       scraper, mirroring vc_runner's own tagged line. *)
    Printf.printf "eecc-interop: %d pass, %d fail, %d skip (out of %d)\n"
      pass fail skip total;
    (match json_out with
     | Some path ->
       write_json_result path ~pass ~fail ~skip ~total results;
       Printf.printf "Wrote JSON result: %s\n" path
     | None -> ());
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "EECC VC/DID interop fixture runner — Track B1 of\n\
     docs/designissues/2026-07-11-vc-canivc-eecc-plan.md.\n\
     \n\
     Usage:\n\
     \  ./eecc_runner                Run the default fixture directory\n\
     \  ./eecc_runner <dir>          Run fixtures from a specific directory\n\
     \  ./eecc_runner --list         List classified fixtures (no execution)\n\
     \  ./eecc_runner --json <path>  Also write a flat JSON result file\n\
     \  ./eecc_runner -v|--verbose   Show SKIP reasons too (FAIL always shown)\n\
     \  ./eecc_runner --help         Show this help\n\
     \n\
     Vendored fixtures: third_party/testing/eecc/ (see its PROVENANCE.md).\n\
     4 real W3C VCDM 2.0 credentials from vc-verifier-rules get a\n\
     structural check (VC_Credential.vc_check_from_string) and a\n\
     crypto-verify SKIP (did:web verificationMethod not resolvable\n\
     offline). Every other vendored file (JSON Schemas, SD-JWT/mdoc\n\
     claim sets, the one JWT-VC example) is a format-mismatch SKIP.\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let list_only = ref false in
  let json_out = ref None in
  let dir = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--list" :: rest -> list_only := true; loop rest
    | "--json" :: p :: rest -> json_out := Some p; loop rest
    | "--json" :: [] ->
      Printf.eprintf "eecc_runner: --json requires a path argument\n"; exit 2
    | p :: rest when !dir = None -> dir := Some p; loop rest
    | _ ->
      Printf.eprintf "eecc_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  let fixture_dir = match !dir with
    | Some p -> p
    | None -> default_fixture_dir ()
  in
  run_suite ~verbose:!verbose ~list_only:!list_only ~json_out:!json_out fixture_dir
