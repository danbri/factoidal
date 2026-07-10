(* Verifiable Credentials (VC) Data Model 2.0 — structural fixture runner.
   Stage 1 of the VC program
   (docs/designissues/2026-07-05-vc-program-plan.md).

   The upstream w3c/vc-data-model-2.0-test-suite (vendored at
   third_party/testing/vc, git submodule) is a mocha suite whose test
   files (tests/*.js) call TestEndpoints.issue()/verify() over HTTP
   against a configured implementation — there is no offline "just run
   it" mode. What IS reusable without that HTTP harness: every test file
   loads its input from tests/input/*.json, and every one of those 120
   fixtures is named with an explicit "-ok"/"-fail" suffix encoding the
   expected structural verdict (credential-no-subject-fail.json,
   credential-ok.json, ...). This runner is the bespoke, non-HTTP
   consumer the plan calls for: it walks tests/input/ (and its
   names-and-descriptions/ subdirectory), classifies each fixture by its
   filename suffix, runs the F*-extracted VC_Credential.vc_check_from_string
   against the raw file bytes, and scores the result against the
   filename's own verdict.

   Suffix classification (see VC.Credential.fst's header for exactly
   which structural checks Stage 1 implements):
     - "*-ok.json"   -> expect a PASS (VC_Pass).
     - "*-fail.json" -> expect a FAIL (VC_Fail _), any reason.
     - "*-fail-or-inject.json" (3 fixtures) -> expect a FAIL. The
       upstream `injectOrReject` assertion (tests/assertions.js)
       gives an ISSUER endpoint two compliant behaviors: inject the
       missing/incomplete @context and return a repaired VC, or
       reject. Factoidal's checker is a validator — it has no issue()
       operation and never injects — so for this implementation the
       upstream assertion reduces to: MUST reject. Scored, not
       skipped.
     - the 3 "presentation-self-asserted-vc-*" fixtures without a
       suffix -> SKIP, each with a per-fixture reason (see
       skip_reason_for below). Short version: they are UNSIGNED
       templates for the holder-claims tests that upstream REMOVED as
       unsound (w3c/vc-data-model-2.0-test-suite commit 52b25a8,
       2025-02-09 "Remove self asserted claims (holder claims) vp
       statements" — present in the vendored submodule's history;
       the vendored checkout is a descendant, so the official suite
       does not exercise these fixtures at all). They cannot be
       refereed offline: the mismatch fixtures are shape-identical to
       `presentation-holder-ok.json` (embedded VC without its own
       proof, holder <> issuer), which MUST pass — only the upstream
       harness's runtime signing step (`createLocalVp`) distinguished
       them, and that step itself overwrites the fixture's issuer
       (`_signCredentials`), which is why upstream withdrew the tests.
       Skips are scored separately, never folded into the pass/fail
       denominator.

   Fixture preparation (string-level, before the engine sees bytes —
   rule-#11 glue, no validation semantics): the two temporality
   fixtures carry literal placeholder text ("PAST DATE"/"FUTURE DATE")
   that the upstream harness's `testTemporality` helper
   (tests/assertions.js) overwrites with computed timestamps
   (`createTimeStamp`, now -/+ 1 year) before issuing. This runner
   replicates that substitution with DETERMINISTIC values
   (2020-01-01T00:00:00Z / 2099-01-01T00:00:00Z) so the F* checker
   sees the same shape the official harness produces: the `-ok`
   fixture gets validFrom in the past + validUntil in the future, the
   `-fail` fixture the swapped (validFrom AFTER validUntil) pair its
   filename verdict requires. Applied uniformly to every fixture read
   (only those two files carry the placeholders today).

   !! THIS IS I/O GLUE — NO VC STRUCTURAL-VALIDATION LOGIC !! Every
   check (the @context sentinel, type membership, credentialSubject
   non-emptiness, embedded verifiableCredential dispatch) lives in
   formal/fstar/VC.Credential.fst. This file only does file I/O,
   directory traversal, filename classification, and tallying — per
   CLAUDE.md iron rule #11 / anti-pattern #15.

   Usage:
     ./vc_runner                 Run the default fixture directory
     ./vc_runner <dir>            Run fixtures from a specific directory
     ./vc_runner --list           List classified fixtures (no execution)
     ./vc_runner -v|--verbose     Show SKIP reasons too (FAIL always shown)
     ./vc_runner --help           Show this help
*)

(* ------------------------------------------------------------------ *)
(* Repo-root resolution (parallel to jsonld_runner.ml / rdfc10_runner.ml). *)

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
  [ Filename.concat repo_root "third_party/testing/vc/tests/input";
    "third_party/testing/vc/tests/input";
    "../../third_party/testing/vc/tests/input";
    "../../../third_party/testing/vc/tests/input" ]

let default_fixture_dir () =
  try List.find Sys.file_exists (fixture_dir_candidates ())
  with Not_found ->
    Filename.concat (find_repo_root ()) "third_party/testing/vc/tests/input"

(* ------------------------------------------------------------------ *)
(* File I/O + a small bounded-depth directory walk (the corpus is only
   two levels deep: tests/input/*.json plus tests/input/names-and-
   descriptions/*.json — but the walk itself has no depth limit beyond
   what Sys.readdir's own DAG-free filesystem naturally terminates on,
   since directories cannot contain themselves). *)

let read_file path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let rec collect_json_files dir =
  match Sys.readdir dir with
  | exception Sys_error _ -> []
  | entries ->
    Array.to_list entries
    |> List.sort compare
    |> List.concat_map (fun name ->
      let path = Filename.concat dir name in
      if Sys.is_directory path then collect_json_files path
      else if Filename.check_suffix name ".json" then [ path ]
      else [])

(* ------------------------------------------------------------------ *)
(* Filename-suffix classification. *)

type expected = Expect_Pass | Expect_Fail | Expect_Ambiguous

let strip_suffix ~suffix s =
  let slen = String.length suffix and n = String.length s in
  n >= slen && String.sub s (n - slen) slen = suffix

let classify_path path =
  let base = Filename.remove_extension (Filename.basename path) in
  if strip_suffix ~suffix:"-ok" base then Expect_Pass
  else if strip_suffix ~suffix:"-fail" base then Expect_Fail
  else if strip_suffix ~suffix:"-fail-or-inject" base then
    (* Upstream injectOrReject: an issuer may inject the missing
       @context or reject. A validator that never injects MUST
       reject — scored as expect-FAIL for this implementation. *)
    Expect_Fail
  else Expect_Ambiguous

(* Per-fixture skip reasons for the 3 unsuffixed fixtures. These are
   precise statements of what is missing, not a deferral: the eddsa-
   rdfc-2022 verify stage EXISTS (VC.DataIntegrity.fst, exercised by
   --crypto below), but these fixtures carry nothing it could verify. *)
let skip_reason_for path =
  match Filename.basename path with
  | "presentation-self-asserted-vc-no-holder.json" ->
    Some "unsigned template (no proof anywhere in the fixture) for the \
          upstream holder-claims test removed as unsound in \
          w3c/vc-data-model-2.0-test-suite@52b25a8 (2025-02-09); the \
          raw shape (VP embedding a proof-less VC, no holder) is \
          identical to presentation-multiple-vc-ok.json / \
          presentation-vc-ok.json, which MUST pass — only the removed \
          harness's runtime signing step distinguished them"
  | "presentation-self-asserted-vc-holder-mismatch.json"
  | "presentation-self-asserted-vc-issuer-mismatch.json" ->
    Some "unsigned template (no proof anywhere in the fixture) for the \
          upstream holder-claims test removed as unsound in \
          w3c/vc-data-model-2.0-test-suite@52b25a8 (2025-02-09); the \
          raw shape (holder <> embedded proof-less VC's issuer) is \
          identical to presentation-holder-ok.json, which MUST pass — \
          and the removed harness's own preparation (_signCredentials) \
          overwrote the fixture's issuer, destroying the mismatch \
          under test, which is why upstream withdrew the test"
  | _ -> None

let expected_label = function
  | Expect_Pass -> "ok"
  | Expect_Fail -> "fail"
  | Expect_Ambiguous -> "ambiguous"

(* ------------------------------------------------------------------ *)
(* Vendored VCDM v2 base context loader.

   The F*-extracted VC_Credential.vc_check_from_string is PURE: it does
   no I/O and carries no assume val. The VCDM v2 base context it needs
   for type-value resolution (protected-term redefinition detection,
   non-URL-mapped type terms, @vocab-nullified unmapped terms — see
   VC.Context.fst) is therefore parsed HERE, once, from the vendored
   third_party/contexts/credentials-v2.jsonld, and passed in as an
   already-decoded Parser_JSON.json_val. This is I/O + parse GLUE only —
   all resolution logic lives in VC.Context.fst (iron rule #11). *)

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
        "vc_runner: vendored VCDM v2 context not found (third_party/contexts/credentials-v2.jsonld)\n";
      exit 2
  in
  match read_file path with
  | None ->
    Printf.eprintf "vc_runner: could not read vendored v2 context at %s\n" path; exit 2
  | Some txt ->
    (match Parser_JSON.parse_json txt with
     | Some v -> v
     | None ->
       Printf.eprintf "vc_runner: vendored v2 context at %s is not well-formed JSON\n" path;
       exit 2)

(* ------------------------------------------------------------------ *)
(* Outcome + per-fixture execution. *)

type outcome = Pass | Fail of string | Skip of string | Withdrawn of string

(* Fixture preparation: replicate the upstream harness's
   testTemporality placeholder substitution (tests/assertions.js) with
   deterministic timestamps. String-level glue applied before the
   engine sees the bytes; the validity-period semantics live in
   VC.Credential.fst (rule #11). *)
let substitute_placeholders content =
  let sub placeholder value s =
    Str.global_replace (Str.regexp_string placeholder) value s in
  content
  |> sub "PAST DATE" "2020-01-01T00:00:00Z"
  |> sub "FUTURE DATE" "2099-01-01T00:00:00Z"

let run_fixture v2ctx path =
  match skip_reason_for path with
  | Some reason -> Withdrawn reason
  | None ->
    (match classify_path path with
     | Expect_Ambiguous ->
       Skip "filename has neither -ok nor -fail suffix and no recorded \
             per-fixture disposition — refusing to guess a verdict"
     | expected ->
    (match read_file path with
     | None -> Fail "could not read file"
     | Some raw ->
       let content = substitute_placeholders raw in
       (match VC_Credential.vc_check_from_string v2ctx content with
        | VC_Credential.VC_Pass ->
          (match expected with
           | Expect_Pass -> Pass
           | Expect_Fail -> Fail "expected a structural FAIL, got Pass"
           | Expect_Ambiguous -> assert false)
        | VC_Credential.VC_Fail reason ->
          (match expected with
           | Expect_Fail -> Pass
           | Expect_Pass -> Fail (Printf.sprintf "expected Pass, got FAIL — %s" reason)
           | Expect_Ambiguous -> assert false))))

(* ------------------------------------------------------------------ *)
(* Suite run. *)

let run_suite ~verbose ~list_only fixture_dir =
  Printf.printf "=== VC Data Model 2.0 Structural Fixture Runner (Stage 1) ===\n";
  Printf.printf "Fixture dir: %s\n\n" fixture_dir;
  let files = collect_json_files fixture_dir in
  let total = List.length files in
  Printf.printf "Totals: %d fixture files\n\n" total;
  if total = 0 then begin
    Printf.eprintf "vc_runner: no fixtures found under %s\n" fixture_dir;
    Printf.eprintf "  (submodule uninitialized? try:\n";
    Printf.eprintf "   git submodule update --init --depth 1 third_party/testing/vc)\n";
    exit 2
  end;
  if list_only then
    List.iter
      (fun path ->
         Printf.printf "  [%-9s] %s\n" (expected_label (classify_path path))
           (Filename.basename path))
      files
  else begin
    let v2ctx = load_v2_context () in
    let n = ref 0 in
    let results =
      List.map
        (fun path ->
           incr n;
           let name = Filename.basename path in
           Printf.eprintf "  [%d/%d] %s%!" !n total name;
           let o = run_fixture v2ctx path in
           let tag = match o with Pass -> "ok" | Fail _ -> "FAIL" | Skip _ -> "skip" | Withdrawn _ -> "withdrawn" in
           Printf.eprintf " %s\n%!" tag;
           (path, o))
        files
    in
    List.iter
      (fun (path, o) ->
         let name = Filename.basename path in
         match o with
         | Pass -> Printf.printf "  PASS: %s\n" name
         | Fail msg -> Printf.printf "  FAIL: %s — %s\n" name msg
         | Skip msg -> if verbose then Printf.printf "  skip: %s — %s\n" name msg
         | Withdrawn msg -> if verbose then Printf.printf "  withdrawn-upstream: %s — %s\n" name msg)
      results;
    Printf.printf "\n========================================\n";
    let pass, fail, skip, wd =
      List.fold_left
        (fun (p, f, s, w) (_, o) ->
           match o with
           | Pass -> (p + 1, f, s, w)
           | Fail _ -> (p, f + 1, s, w)
           | Skip _ -> (p, f, s + 1, w)
           | Withdrawn _ -> (p, f, s, w + 1))
        (0, 0, 0, 0) results
    in
    let scorable = total - wd in
    if wd > 0 then
      Printf.printf
        "withdrawn-upstream: %d vendored fixture(s) excluded from the scorable set (removed as unsound in w3c/vc-data-model-2.0-test-suite@52b25a8; run with -v for per-fixture detail)\n"
        wd;
    Printf.printf "TOTAL: %d pass, %d fail, %d skip (out of %d scorable)\n" pass fail skip scorable;
    Printf.printf "========================================\n";
    (* Exact final-line format for generate-report.sh's generic "N pass,
       M fail (out of K)" score-line regex, mirroring jsonld_runner's
       own tagged final line. Withdrawn-upstream fixtures are NOT skips:
       a skip is actionable debt, a withdrawn test is nobody's debt —
       they are excluded from the scorable denominator entirely. *)
    Printf.printf "vc-credential-structural: %d pass, %d fail, %d skip (out of %d)\n"
      pass fail skip scorable;
    if fail > 0 then exit 1
  end

(* ------------------------------------------------------------------ *)
(* Crypto mode — eddsa-rdfc-2022 Data Integrity roundtrip (Stage 5).

   Exercises the F*-extracted VC_DataIntegrity pipeline end to end:
   RDFC-1.0 transform (RDF_Canonical) -> SHA-256 (HACL-star) -> Ed25519
   sign/verify (HACL-star) -> multibase-z proofValue (VC_Multibase).  The
   crypto seam routes to the vendored HACL* C (third_party/hacl/); there
   is no offline W3C cryptosuite fixture directory (the vc-di-eddsa suite
   is live-endpoint driven), so this is a self-contained roundtrip:
   generate a keypair, sign a credential dataset, verify it, and confirm
   a wrong key / tampered proof is rejected.

   !! I/O + orchestration GLUE ONLY — all crypto + hashing + canonicalize
   logic lives in formal/fstar/VC.DataIntegrity.fst, VC.Multibase.fst, and
   RDF.Canonical.fst. This block only builds inputs, calls extracted F*,
   and tallies. *)

let crypto_check name cond =
  Printf.printf "  [%s] %s\n" (if cond then "PASS" else "FAIL") name;
  cond

let run_crypto () =
  Printf.printf "=== VC Data Integrity eddsa-rdfc-2022 roundtrip (crypto mode) ===\n\n";
  (* A fixed 32-byte Ed25519 secret key (hex). Any valid 32-byte key works
     for a roundtrip; this one is deterministic for reproducibility. *)
  let sk = "9d61b19deffebc3a4a3c9d0b3b0f8f0e7a5b6c4d2e1f00112233445566778899" in
  let pk = VC_DataIntegrity.ed25519_secret_to_public sk in
  (* A different key, for the negative (wrong-key) test. *)
  let sk2 = "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20" in
  let pk2 = VC_DataIntegrity.ed25519_secret_to_public sk2 in
  (* The unsecured credential, as an RDF dataset (N-Quads in, canonicalized
     by RDFC-1.0 inside the pipeline). Bnode present so canonicalization is
     genuinely exercised, not a no-op. *)
  let doc_nq =
    "<urn:credential:1> <https://www.w3.org/2018/credentials#issuer> <urn:issuer:acme> .\n\
     <urn:credential:1> <http://schema.org/credentialSubject> _:b0 .\n\
     _:b0 <http://schema.org/name> \"Alice\" .\n" in
  (* The proof-options dataset (proof block minus proofValue), as RDF. *)
  let cfg_nq =
    "_:pc <http://www.w3.org/ns/data-integrity#cryptosuite> \"eddsa-rdfc-2022\" .\n\
     _:pc <http://www.w3.org/ns/data-integrity#proofPurpose> \"assertionMethod\" .\n" in
  (* A DIFFERENT document, for the wrong-document negative test. *)
  let doc_nq2 =
    "<urn:credential:1> <https://www.w3.org/2018/credentials#issuer> <urn:issuer:acme> .\n\
     <urn:credential:1> <http://schema.org/credentialSubject> _:b0 .\n\
     _:b0 <http://schema.org/name> \"Mallory\" .\n" in
  let ds   = Parser_NQuads.parse_nquads doc_nq in
  let ds2  = Parser_NQuads.parse_nquads doc_nq2 in
  let cfg  = Parser_NQuads.parse_nquads cfg_nq in
  let ok_keypair =
    crypto_check "Ed25519 keypair derived (HACL* secret_to_public)"
      (String.length pk = 64 && String.length pk2 = 64 && pk <> pk2) in
  match VC_DataIntegrity.eddsa_rdfc_2022_create sk ds cfg with
  | None ->
    ignore (crypto_check "eddsa-rdfc-2022 create produced a proofValue" false);
    false
  | Some proof_value ->
    let is_multibase_z = String.length proof_value > 1 && proof_value.[0] = 'z' in
    let c_created = crypto_check "create produced a multibase-z proofValue" is_multibase_z in
    (* multibase roundtrip (VC_Multibase) *)
    let c_mb =
      crypto_check "multibase-z proofValue decodes back to signature hex"
        (match VC_Multibase.multibase_z_to_hex proof_value with
         | Some h -> String.length h = 128
         | None -> false) in
    let c_verify =
      crypto_check "verify with correct key + document + proof = true"
        (VC_DataIntegrity.eddsa_rdfc_2022_verify pk ds cfg proof_value) in
    let c_wrongkey =
      crypto_check "verify with WRONG public key = false"
        (not (VC_DataIntegrity.eddsa_rdfc_2022_verify pk2 ds cfg proof_value)) in
    let c_wrongdoc =
      crypto_check "verify against a DIFFERENT document = false"
        (not (VC_DataIntegrity.eddsa_rdfc_2022_verify pk ds2 cfg proof_value)) in
    (* tamper: swap two chars of the proofValue body *)
    let tampered =
      let b = Bytes.of_string proof_value in
      if Bytes.length b > 3 then begin
        let c1 = Bytes.get b 1 and c2 = Bytes.get b 2 in
        Bytes.set b 1 c2; Bytes.set b 2 c1
      end;
      Bytes.to_string b in
    let c_tamper =
      crypto_check "verify with a TAMPERED proofValue = false"
        (not (VC_DataIntegrity.eddsa_rdfc_2022_verify pk ds cfg tampered)) in
    (* verification-method multikey + proof-block serialization *)
    let vm = match VC_Multibase.ed25519_pubkey_to_multikey pk with
      | Some s -> "did:key:" ^ s ^ "#" ^ s | None -> "" in
    let proof =
      VC_DataIntegrity.make_eddsa_proof vm "assertionMethod" "" proof_value in
    let proof_json = VC_DataIntegrity.serialize_proof proof in
    let c_proofblock =
      crypto_check "DataIntegrityProof block serializes with proofValue"
        (let has s = try ignore (Str.search_forward (Str.regexp_string s) proof_json 0); true
                     with Not_found -> false in
         has "\"DataIntegrityProof\"" && has "\"eddsa-rdfc-2022\""
         && has proof_value && String.length vm > 8) in
    let all = ok_keypair && c_created && c_mb && c_verify && c_wrongkey
              && c_wrongdoc && c_tamper && c_proofblock in
    Printf.printf "\n========================================\n";
    let npass = List.fold_left (fun a b -> if b then a+1 else a) 0
                  [ok_keypair; c_created; c_mb; c_verify; c_wrongkey;
                   c_wrongdoc; c_tamper; c_proofblock] in
    Printf.printf "vc-dataintegrity-eddsa-rdfc-2022: %d pass, %d fail (out of 8)\n"
      npass (8 - npass);
    Printf.printf "========================================\n";
    all

(* ------------------------------------------------------------------ *)
(* Main. *)

let print_help () =
  print_string
    "VC Data Model 2.0 structural fixture runner — Stage 1 of the VC program.\n\
     \n\
     Usage:\n\
     \  ./vc_runner                Run the default fixture directory\n\
     \  ./vc_runner <dir>          Run fixtures from a specific directory\n\
     \  ./vc_runner --list         List classified fixtures (no execution)\n\
     \  ./vc_runner --crypto       Run the eddsa-rdfc-2022 Data Integrity roundtrip\n\
     \                             (HACL* Ed25519 + SHA-256, self-contained)\n\
     \  ./vc_runner -v|--verbose   Show SKIP reasons too (FAIL always shown)\n\
     \  ./vc_runner --help         Show this help\n\
     \n\
     Status: structural checks (see formal/fstar/VC.Credential.fst's\n\
     header for the exact rule set). Scored against the 120 vendored\n\
     tests/input/*.json fixtures from w3c/vc-data-model-2.0-test-suite.\n\
     -fail-or-inject fixtures are scored as expect-FAIL (a validator\n\
     that cannot inject MUST reject); the two temporality fixtures'\n\
     placeholders are substituted with concrete dates before checking,\n\
     as the upstream harness does; the 3 unsigned self-asserted-vc\n\
     fixtures (holder-claims tests upstream removed as unsound) are\n\
     SKIPped with per-fixture reasons, not guessed.\n"

let () =
  let args = Array.to_list Sys.argv |> List.tl in
  let verbose = ref false in
  let list_only = ref false in
  let crypto = ref false in
  let dir = ref None in
  let rec loop = function
    | [] -> ()
    | ("-v" | "--verbose") :: rest -> verbose := true; loop rest
    | ("--help" | "-h") :: _ -> print_help (); exit 0
    | "--crypto" :: rest -> crypto := true; loop rest
    | "--list" :: rest -> list_only := true; loop rest
    | p :: rest when !dir = None -> dir := Some p; loop rest
    | _ ->
      Printf.eprintf "vc_runner: unexpected arguments; try --help\n";
      exit 2
  in
  loop args;
  if !crypto then begin
    if run_crypto () then exit 0 else exit 1
  end;
  let fixture_dir = match !dir with
    | Some p -> p
    | None -> default_fixture_dir ()
  in
  run_suite ~verbose:!verbose ~list_only:!list_only fixture_dir
