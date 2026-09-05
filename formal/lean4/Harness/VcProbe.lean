/-
Harness/VcProbe — run the Verifiable Credentials Data Integrity stage
(`L4Factoidal/VC/`, `L4Factoidal/Crypto/Ed25519.lean`) against the
fixtures the F* tree's runners read, plus the W3C specification test
vectors, and print score lines in the `bin/*-runner` grammar.

This is a HARNESS, not part of the verified library: it does file I/O,
calls the HACL* externs, and prints. Five sections, each one score line:

  1. `ed25519-rfc8032` — RFC 8032 §7.1 TEST 1, 2, 3, 1024 through the
     three `@[extern]` bindings. `#guard` cannot evaluate an extern, so
     THIS is the measurement that the binding computes Ed25519 at all:
     public key from secret key, the (deterministic) signature, verify
     on the published triple, verify on a one-byte-flipped signature,
     and the two length refusals.
  2. `did:key` — the same three `tests/did/*.did` → `*.nt` vectors and
     the same five rejection cases `bin/did-runner/did_runner.ml` runs
     (F*: `did:key: 8 pass, 0 fail (out of 8)`). Lines are compared as
     sorted sets of trimmed N-Triples lines, exactly as that runner does.
  3. `vc-dataintegrity-eddsa-rdfc-2022` — the eight checks of
     `bin/vc-runner/vc_runner.ml --crypto` on its exact N-Quads inputs
     and keys (F*: `8 pass, 0 fail (out of 8)`).
  4. `vc-di-eddsa-spec-vectors` — https://www.w3.org/TR/vc-di-eddsa/
     §3.4, eddsa-rdfc-2022: the unsigned credential and proof options
     through JSON-LD toRdf (vendored contexts, loader built here) and
     RDFC-1.0 must reproduce the spec's canonical N-Quads, hashes,
     signature and proofValue; then the document-level API must secure
     the credential to the spec's proof and verify it, and must REFUSE
     a tampered proofValue, a tampered claim, a wrong purpose, and an
     unresolvable verification method. The F* tree has no offline
     run of these vectors (its `vc_di_eddsa` score, 31 pass, is the
     live-endpoint mocha suite through the Node VC-API shim).
  5. `sha256 differential` — the OTHER HACL* extern,
     `Crypto/SHA2Native.lean`'s `sha256Hacl`, compared with the pure
     Lean `Crypto.sha256` on the FIPS 180-4 vectors, the empty input,
     the SHA-256 block and padding boundaries (1, 55, 56, 63, 64, 65
     bytes) and a 1 MiB deterministic pseudo-random buffer. The storage
     host passes the HACL* hasher into `Storage/BlockMerkle.lean` for
     Merkle admission, so this equality is what makes that substitution
     sound; the probe exits non-zero when it breaks.

Usage: `lake exe l4vc-probe` from `formal/lean4`, or the built binary
from anywhere — the repository root is found by walking up from the
working directory to the directory holding `CLAUDE.md`, as the F*
runners do.
-/
import L4Factoidal.Crypto.Ed25519
import L4Factoidal.Crypto.SHA2Native
import Harness.NativeHasher
import L4Factoidal.VC.DataIntegrity
import L4Factoidal.VC.Tests
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NTriples
import L4Factoidal.JSON.Parser

open L4Factoidal.RDF
open L4Factoidal.Crypto
open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.Syntax
open L4Factoidal.VC.Multibase
open L4Factoidal.VC.DidKey
open L4Factoidal.VC.Context
open L4Factoidal.VC.DataIntegrity
open L4Factoidal.VC.Tests (specSkMultikey specPkMultikey specVm specCanonicalDoc specCanonicalCfg
  specDocHash specCfgHash specSigHex specProofValue)

namespace VcProbe

/-! ## Tally -/

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  failures : List String := []

def check (t : IO.Ref Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"  [PASS] {name}"
    t.modify fun s => { s with pass := s.pass + 1 }
  else
    IO.println s!"  [FAIL] {name}{if detail.isEmpty then "" else " — " ++ detail}"
    t.modify fun s => { s with fail := s.fail + 1, failures := s.failures ++ [name] }

def scoreLine (suite : String) (t : Tally) : String :=
  s!"{suite}: {t.pass} pass, {t.fail} fail (out of {t.pass + t.fail})"

/-! ## Repository root and file helpers -/

partial def findRepoRoot (d : System.FilePath) : IO (Option System.FilePath) := do
  if ← (d / "CLAUDE.md").pathExists then return some d
  match d.parent with
  | some p => if p == d then return none else findRepoRoot p
  | none => return none

def readOpt (p : System.FilePath) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ => pure none

def hexBytes! (s : String) : ByteArray := (byteArrayOfHex? s).getD ByteArray.empty

/-- Flip the low bit of byte `i` (no-op if out of range). -/
def flipByte (a : ByteArray) (i : Nat) : ByteArray :=
  if i < a.size then a.set! i (a.get! i ^^^ 1) else a

/-! ## 1. RFC 8032 §7.1 vectors through the extern -/

structure Rfc8032Vector where
  name : String
  sk   : String
  pk   : String
  msg  : String
  sig  : String
  deriving Inhabited

/-- TEST 1024's message is 1023 bytes; only its leading bytes are
transcribed here and the signature check for it is over a prefix, so it
is NOT a vector check — it is omitted rather than faked. -/
def test1 : Rfc8032Vector :=
  { name := "TEST 1 (empty message)",
    sk := "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
    pk := "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
    msg := "",
    sig := "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b" }

def test2 : Rfc8032Vector :=
  { name := "TEST 2 (1-byte message)",
    sk := "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
    pk := "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
    msg := "72",
    sig := "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00" }

def test3 : Rfc8032Vector :=
  { name := "TEST 3 (2-byte message)",
    sk := "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
    pk := "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
    msg := "af82",
    sig := "6291d657deec24024827e69c3abe01a30ce548a284743a445e3680d7db5ac3ac18ff9b538d16f290ae67f760984dc6594a7c15e9716ed28dc027beceea1ec40a" }

def rfc8032 : List Rfc8032Vector := [test1, test2, test3]

def runRfc8032 : IO Tally := do
  IO.println "=== 1. Ed25519 via HACL* extern — RFC 8032 §7.1 test vectors ==="
  let t ← IO.mkRef ({} : Tally)
  for v in rfc8032 do
    let sk := hexBytes! v.sk
    let msg := hexBytes! v.msg
    let pk := Ed25519.secretToPublic sk
    check t s!"{v.name}: secretToPublic matches published public key"
      (hexOfByteArray pk == v.pk) (hexOfByteArray pk)
    let sg := Ed25519.sign sk msg
    check t s!"{v.name}: sign matches published signature (deterministic)"
      (hexOfByteArray sg == v.sig) (hexOfByteArray sg)
    check t s!"{v.name}: verify accepts the published (pk, msg, sig)"
      (Ed25519.verify (hexBytes! v.pk) msg (hexBytes! v.sig))
    check t s!"{v.name}: verify REJECTS the signature with byte 0 flipped"
      (!Ed25519.verify (hexBytes! v.pk) msg (flipByte (hexBytes! v.sig) 0))
    check t s!"{v.name}: verify REJECTS the signature with byte 63 flipped"
      (!Ed25519.verify (hexBytes! v.pk) msg (flipByte (hexBytes! v.sig) 63))
    let otherPk := if v.pk == test3.pk then test1.pk else test3.pk
    check t s!"{v.name}: verify REJECTS under a different public key"
      (!Ed25519.verify (hexBytes! otherPk) msg (hexBytes! v.sig))
  check t "secretToPublic refuses a 31-byte key (empty result)"
    ((Ed25519.secretToPublic (hexBytes! "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f")).size == 0)
  check t "sign refuses a 31-byte key (empty result)"
    ((Ed25519.sign (hexBytes! "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f") ByteArray.empty).size == 0)
  check t "verify refuses a 63-byte signature"
    (!Ed25519.verify (hexBytes! test1.pk) ByteArray.empty
       (hexBytes! (test1.sig.dropRight 2)))
  check t "verify refuses a 31-byte public key"
    (!Ed25519.verify (hexBytes! (test1.pk.dropRight 2)) ByteArray.empty
       (hexBytes! test1.sig))
  t.get

/-! ## 2. did:key vectors (`tests/did/`) -/

def sortedLines (s : String) : List String :=
  Canonical.sortStrings ((s.splitOn "\n").map String.trim |>.filter
    (fun l => !l.isEmpty && !l.startsWith "#"))

def rejectionCases : List (String × String) := [
  ("no did:key: prefix", "did:example:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK"),
  ("empty string", ""),
  ("did:key: with empty multibase value", "did:key:"),
  ("multibase not 'z' (base64url 'm')", "did:key:mAbCdEfGhIjKlMnOpQrStUvWxYz"),
  ("wrong multicodec (secp256k1)", "did:key:zQ3shokFTS3brHcDQrn82RUDfCZESWL1ZdCEJwekUDPQiYBme") ]

def runDidKey (root : System.FilePath) : IO Tally := do
  IO.println "\n=== 2. did:key resolution vectors (tests/did) ==="
  let t ← IO.mkRef ({} : Tally)
  let dir := root / "tests" / "did"
  let entries ← try dir.readDir catch _ => pure #[]
  let dids := (entries.toList.map (·.fileName)).filter (·.endsWith ".did")
  let dids := Canonical.sortStrings dids
  if dids.isEmpty then
    check t "tests/did has *.did vectors" false s!"none under {dir}"
  for name in dids do
    let base := name.dropRight 4
    match ← readOpt (dir / name), ← readOpt (dir / (base ++ ".nt")) with
    | some didTxt, some ntTxt =>
      let did := didTxt.trim
      match didKeyDocument did with
      | none => check t base false s!"didKeyDocument returned none for {did}"
      | some triples =>
        let got := Canonical.sortStrings
          (triples.filterMap (fun tr => (Triple.toNTriples .rdf11 tr).toOption.map String.trim))
        let expected := sortedLines ntTxt
        let missing := expected.filter (fun l => !got.contains l)
        let extra := got.filter (fun l => !expected.contains l)
        check t base (got == expected)
          s!"missing {missing.length} expected line(s), {extra.length} unexpected"
    | _, _ => check t base false "could not read vector pair"
  for (label, input) in rejectionCases do
    check t s!"reject — {label}" ((parseDidKey input).isNone)
  t.get

/-! ## 3. The `vc_runner --crypto` roundtrip, same inputs -/

def docNq : String :=
  "<urn:credential:1> <https://www.w3.org/2018/credentials#issuer> <urn:issuer:acme> .\n" ++
  "<urn:credential:1> <http://schema.org/credentialSubject> _:b0 .\n" ++
  "_:b0 <http://schema.org/name> \"Alice\" .\n"

def cfgNq : String :=
  "_:pc <http://www.w3.org/ns/data-integrity#cryptosuite> \"eddsa-rdfc-2022\" .\n" ++
  "_:pc <http://www.w3.org/ns/data-integrity#proofPurpose> \"assertionMethod\" .\n"

def docNq2 : String :=
  "<urn:credential:1> <https://www.w3.org/2018/credentials#issuer> <urn:issuer:acme> .\n" ++
  "<urn:credential:1> <http://schema.org/credentialSubject> _:b0 .\n" ++
  "_:b0 <http://schema.org/name> \"Mallory\" .\n"

def parseNq! (s : String) : Dataset :=
  match parseNQuads s .rdf11 with
  | .ok ds => ds
  | .error _ => Dataset.empty

def swapChars (s : String) (i j : Nat) : String :=
  let cs := s.toList.toArray
  if i < cs.size ∧ j < cs.size then
    let a := cs[i]!; let b := cs[j]!
    String.ofList ((cs.set! i b).set! j a).toList
  else s

def runRoundtrip : IO Tally := do
  IO.println "\n=== 3. eddsa-rdfc-2022 roundtrip — the vc_runner --crypto checks ==="
  let t ← IO.mkRef ({} : Tally)
  let sk := hexBytes! "9d61b19deffebc3a4a3c9d0b3b0f8f0e7a5b6c4d2e1f00112233445566778899"
  let sk2 := hexBytes! "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
  let pk := Ed25519.secretToPublic sk
  let pk2 := Ed25519.secretToPublic sk2
  let ds := parseNq! docNq
  let ds2 := parseNq! docNq2
  let cfg := parseNq! cfgNq
  check t "Ed25519 keypair derived (HACL* secret_to_public)"
    (pk.size == 32 && pk2.size == 32 && pk != pk2)
  match createProofValue Ed25519.sign .sha256 sk ds cfg with
  | none => check t "eddsa-rdfc-2022 create produced a proofValue" false
  | some pv =>
    IO.println s!"  proofValue = {pv}"
    check t "create produced a multibase-z proofValue" (pv.length > 1 && pv.startsWith "z")
    check t "multibase-z proofValue decodes back to signature hex"
      ((multibaseZToHex? pv).map String.length == some 128)
    check t "verify with correct key + document + proof = true"
      (verifyProofValue Ed25519.verify .sha256 pk ds cfg pv)
    check t "verify with WRONG public key = false"
      (!verifyProofValue Ed25519.verify .sha256 pk2 ds cfg pv)
    check t "verify against a DIFFERENT document = false"
      (!verifyProofValue Ed25519.verify .sha256 pk ds2 cfg pv)
    check t "verify with a TAMPERED proofValue = false"
      (!verifyProofValue Ed25519.verify .sha256 pk ds cfg (swapChars pv 1 2))
    let vm := verificationMethodOfPublicKey (ofByteArray pk)
    let proofJson := serializeProof (makeEddsaProof vm "assertionMethod" "" pv)
    check t "DataIntegrityProof block serializes with proofValue"
      ((proofJson.splitOn "\"DataIntegrityProof\"").length > 1 &&
       (proofJson.splitOn "\"eddsa-rdfc-2022\"").length > 1 &&
       (proofJson.splitOn pv).length > 1 && vm.length > 8)
  t.get

/-! ## 4. W3C vc-di-eddsa §3.4 test vectors, end to end -/

def specCredentialJson : String :=
"{
    \"@context\": [
        \"https://www.w3.org/ns/credentials/v2\",
        \"https://www.w3.org/ns/credentials/examples/v2\"
    ],
    \"id\": \"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",
    \"type\": [\"VerifiableCredential\", \"AlumniCredential\"],
    \"name\": \"Alumni Credential\",
    \"description\": \"A minimum viable example of an Alumni Credential.\",
    \"issuer\": \"https://vc.example/issuers/5678\",
    \"validFrom\": \"2023-01-01T00:00:00Z\",
    \"credentialSubject\": {
        \"id\": \"did:example:abcdefgh\",
        \"alumniOf\": \"The School of Examples\"
    }
}"

def specCreated : String := "2023-02-24T23:36:38Z"

/-- The spec's proof options, verbatim (its `@context` is the
credential's). -/
def specProofOptionsJson : String :=
"{
  \"type\": \"DataIntegrityProof\",
  \"cryptosuite\": \"eddsa-rdfc-2022\",
  \"created\": \"2023-02-24T23:36:38Z\",
  \"verificationMethod\": \"" ++ specVm ++ "\",
  \"proofPurpose\": \"assertionMethod\",
  \"@context\": [
    \"https://www.w3.org/ns/credentials/v2\",
    \"https://www.w3.org/ns/credentials/examples/v2\"
  ]
}"

/-- Build the loader: the vendored `third_party/contexts/` files under
the IRIs `VC/Context.lean` records, then the context cache's index. -/
def buildLoader (root : System.FilePath) : IO Loader := do
  let mut table : List (String × String) := []
  for (iri, file) in vendoredContextFiles do
    match ← readOpt (root / "third_party" / "contexts" / file) with
    | some body => table := table ++ [(iri, body)]
    | none => IO.println s!"  warning: vendored context {file} not found"
  let cacheDir := root / "third_party" / "jsonld-context-cache"
  let mut cached := 0
  match ← readOpt (cacheDir / "index.json") with
  | some idxTxt =>
    match parseJson idxTxt with
    | .ok idx =>
      for ce in cacheTableOfIndex idx do
        match ← readOpt (cacheDir / ce.path) with
        | some body => table := table ++ [(ce.url, body)]; cached := cached + 1
        | none => pure ()
    | .error _ => pure ()
  | none => pure ()
  IO.println s!"  loader: {vendoredContextFiles.length} vendored context(s), {cached} cached remote context(s)"
  pure (vcLoader table)

def firstDiff (a b : String) : String :=
  let la := a.splitOn "\n"; let lb := b.splitOn "\n"
  match (la.zip lb).find? (fun (x, y) => x != y) with
  | some (x, y) => s!"first differing line:\n    got: {x}\n    exp: {y}"
  | none => s!"line counts {la.length} vs {lb.length}"

def swapLines (s : String) (i j : Nat) : String :=
  let ls := (s.splitOn "\n").toArray
  if i < ls.size ∧ j < ls.size then
    let a := ls[i]!; let b := ls[j]!
    "\n".intercalate ((ls.set! i b).set! j a).toList
  else s

def runSpecVectors (root : System.FilePath) : IO Tally := do
  IO.println "\n=== 4. W3C vc-di-eddsa §3.4 test vectors (eddsa-rdfc-2022), end to end ==="
  let t ← IO.mkRef ({} : Tally)
  let loader ← buildLoader root
  let sk := toByteArray ((multikeyToEd25519SecretKey? specSkMultikey).getD [])
  let pk := toByteArray ((multikeyToEd25519PublicKey? specPkMultikey).getD [])
  check t "spec secretKeyMultibase decodes to 32 bytes; publicKeyMultibase to 32 bytes"
    (sk.size == 32 && pk.size == 32)
  check t "HACL* secretToPublic(spec secret key) = spec public key"
    (Ed25519.secretToPublic sk == pk) (hexOfByteArray (Ed25519.secretToPublic sk))
  -- Transformation
  let credJson := (parseJson specCredentialJson).toOption.getD .null
  let optsJson := (parseJson specProofOptionsJson).toOption.getD .null
  let canonDoc ← match canonicalizeJsonLd loader credJson with
    | .ok s => pure s
    | .error e => check t "JSON-LD toRdf + RDFC-1.0 of the credential" false e; pure ""
  let canonCfg ← match canonicalizeJsonLd loader optsJson with
    | .ok s => pure s
    | .error e => check t "JSON-LD toRdf + RDFC-1.0 of the proof options" false e; pure ""
  check t "canonical N-Quads of the credential = spec's (8 lines)"
    (canonDoc == specCanonicalDoc) (firstDiff canonDoc specCanonicalDoc)
  check t "canonical N-Quads of the proof options = spec's (5 lines)"
    (canonCfg == specCanonicalCfg) (firstDiff canonCfg specCanonicalCfg)
  -- Hashing
  check t "SHA-256(canonical credential) = spec documentHash"
    (hashHex .sha256 canonDoc == specDocHash)
  check t "SHA-256(canonical proof options) = spec proofConfigHash"
    (hashHex .sha256 canonCfg == specCfgHash)
  check t "hashData = proofConfigHash ++ documentHash"
    (hashDataHex .sha256 canonDoc canonCfg == specCfgHash ++ specDocHash)
  -- Proof serialization
  let sig := Ed25519.sign sk (hashData .sha256 canonDoc canonCfg)
  check t "Ed25519(sk, hashData) = spec signature (hex)"
    (hexOfByteArray sig == specSigHex) (hexOfByteArray sig)
  check t "createFromCanonical = spec proofValue"
    (createFromCanonical Ed25519.sign .sha256 sk canonDoc canonCfg == some specProofValue)
  check t "verifyFromCanonical(spec pk, canonical forms, spec proofValue) = true"
    (verifyFromCanonical Ed25519.verify .sha256 pk canonDoc canonCfg specProofValue)
  -- Document level
  let secured ← match secureDocument loader Ed25519.sign sk specVm "assertionMethod" specCreated credJson with
    | .ok j => pure j
    | .error e => check t "secureDocument" false e; pure .null
  let pvOut := (secured.field? "proof").bind (fun p => p.getString? "proofValue")
  check t "secureDocument attaches the spec's proofValue" (pvOut == some specProofValue)
    (pvOut.getD "<none>")
  check t "verifyDocument(secured) = ok"
    (verifyDocument loader Ed25519.verify secured == .ok ())
    (match verifyDocument loader Ed25519.verify secured with
     | .ok _ => "" | .error e => e.describe)
  -- Refusals
  let tamperedPv := swapChars specProofValue 5 6
  let tamperedProof := setField "proof"
    (setField "proofValue" (.string tamperedPv) ((secured.field? "proof").getD .null)) secured
  check t "verifyDocument REFUSES a tampered proofValue (signatureRejected)"
    (verifyDocument loader Ed25519.verify tamperedProof == .error .signatureRejected)
  let tamperedClaim := setFieldFirst "name" (.string "Alumni Credential (forged)") secured
  check t "verifyDocument REFUSES a changed claim (signatureRejected)"
    (verifyDocument loader Ed25519.verify tamperedClaim == .error .signatureRejected)
  check t "verifyDocument REFUSES the wrong proofPurpose"
    (verifyDocument loader Ed25519.verify secured (expectedPurpose := "authentication")
       == .error (.wrongPurpose "assertionMethod" "authentication"))
  let badVm := setField "proof"
    (setField "verificationMethod" (.string "did:web:example.com#key-1")
      ((secured.field? "proof").getD .null)) secured
  check t "verifyDocument REFUSES a non-did:key verificationMethod"
    (verifyDocument loader Ed25519.verify badVm
       == .error (.unresolvableVerificationMethod "did:web:example.com#key-1"))
  check t "verifyDocument REFUSES the unsecured credential (noProof)"
    (verifyDocument loader Ed25519.verify credJson == .error .noProof)
  -- The canonical form is what is signed: input quad order is
  -- irrelevant (RDFC-1.0 sorts), corrupting the canonical form is not.
  let ds := parseNq! specCanonicalDoc
  let dsSwapped := parseNq! (swapLines specCanonicalDoc 0 1)
  check t "RDFC-1.0: swapping two input quads leaves the canonical form unchanged"
    (transformDataset ds == transformDataset dsSwapped && transformDataset ds == specCanonicalDoc)
  check t "corrupting the canonical form (two lines swapped) changes the hash"
    (hashHex .sha256 (swapLines specCanonicalDoc 0 1) != specDocHash)
  check t "… and the spec signature no longer verifies over it"
    (!verifyFromCanonical Ed25519.verify .sha256 pk (swapLines specCanonicalDoc 0 1) canonCfg specProofValue)
  t.get

/-! ## 5. HACL* SHA-256 against the pure Lean specification

`Crypto/SHA2Native.lean` binds `Hacl_Hash_SHA2_hash_256` so a storage
host can admit tens of megabytes of public block bytes at C speed
(`Storage/BlockMerkle.lean`'s `Hasher` parameter, `Harness.nativeHasher`).
The pure Lean `Crypto.sha256` remains the specification and remains what
every `#guard` and every theorem evaluates, so the two MUST agree on
every input. An extern does not evaluate at compile time, so that
agreement cannot be a `#guard`; this section is the measurement, and the
probe exits non-zero when it fails. -/

/-- `n` copies of one byte. -/
private def repeatByte (n : Nat) (b : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate n b)

/-- Deterministic pseudo-random bytes from a 32-bit xorshift, so the large
case is reproducible across runs and machines and carries none of the
structure a repeated-byte buffer has. -/
private def prngBytes (n : Nat) : ByteArray := Id.run do
  let mut x : UInt32 := 0x9e3779b9
  let mut out : Array UInt8 := #[]
  for _ in [0:n] do
    x := x ^^^ (x <<< 13)
    x := x ^^^ (x >>> 17)
    x := x ^^^ (x <<< 5)
    out := out.push (UInt8.ofNat (x.toNat % 256))
  return ByteArray.mk out

/-- The FIPS 180-4 two-block SHA-256 example message (56 bytes). -/
private def fips56 : String :=
  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"

/-- The FIPS 180-4 two-block SHA-384/512 example message (112 bytes); a
SHA-256 input of that length is still a useful multi-block case. -/
private def fips112 : String :=
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
  "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

/-- Split a buffer into consecutive chunks of at most `n` bytes. -/
private def chunksOf (n : Nat) (b : ByteArray) : List ByteArray :=
  if n == 0 then [b]
  else (List.range ((b.size + n - 1) / n)).map
        (fun i => b.extract (i * n) (min ((i + 1) * n) b.size))

/-- The incremental SHA-256 of a buffer fed in `n`-byte chunks, with a given
block fold. With `Crypto.pureBlockFold256` this is `Sha256Stream` itself;
with `Harness.nativeBlockFold256` it is the HACL* walk the shard packer's
source identity uses. -/
private def streamDigestWith (fold : L4Factoidal.Crypto.BlockFold256) (n : Nat)
    (b : ByteArray) : ByteArray :=
  ((chunksOf n b).foldl (fun st c => st.updateWith fold c) Sha256Stream.init).finishWith fold

def runSha256Native : IO Tally := do
  IO.println "\n=== 5. SHA-256 via HACL* extern — differential against pure Lean ==="
  let t ← IO.mkRef ({} : Tally)
  let cases : List (String × ByteArray) :=
    [ ("empty message", ByteArray.empty)
    , ("FIPS 180-4 \"abc\"", "abc".toUTF8)
    , ("FIPS 180-4 56-byte two-block example", fips56.toUTF8)
    , ("FIPS 180-4 112-byte example", fips112.toUTF8)
    , ("non-ASCII UTF-8 (\"Ünïcödé\")", "Ünïcödé".toUTF8)
    , ("1 byte", repeatByte 1 0x61)
    , ("55 bytes (last length with padding in one block)", repeatByte 55 0x61)
    , ("56 bytes (padding forces a second block)", repeatByte 56 0x61)
    , ("63 bytes", repeatByte 63 0x61)
    , ("64 bytes (exactly one block)", repeatByte 64 0x61)
    , ("65 bytes", repeatByte 65 0x61)
    , ("FIPS 180-4 1,000,000 × 'a'", repeatByte 1000000 0x61)
    , ("1 MiB deterministic pseudo-random buffer", prngBytes 1048576) ]
  for (name, bytes) in cases do
    let expected := sha256 bytes
    let got := sha256Hacl bytes
    check t s!"sha256Hacl == sha256 — {name} ({bytes.size} bytes)" (got == expected)
      s!"pure {bytesToHex expected} vs HACL* {bytesToHex got}"
  -- The STREAMING walk. `sha256BlocksHacl` is the second SHA-256 extern and
  -- the one the shard packer's source identity runs on, so it needs its own
  -- differential. Feeding the same message in several chunk sizes exercises
  -- the carried under-64-byte tail, which is where a block-walk binding gets
  -- an offset wrong, and the final padded block, which `finishWith` supplies.
  for (name, bytes) in cases do
    let sizes := if bytes.size > 200 then [64, 65536] else [1, 7, 64, 65536]
    for size in sizes do
      let expected := sha256 bytes
      let got := streamDigestWith Harness.nativeBlockFold256 size bytes
      check t s!"native block fold == sha256 — {name} ({bytes.size} bytes, {size}-byte chunks)"
        (got == expected)
        s!"pure {bytesToHex expected} vs HACL* stream {bytesToHex got}"
  t.get

/-! ## Main -/

def main (_ : List String) : IO UInt32 := do
  let cwd ← IO.currentDir
  let root ← match ← findRepoRoot cwd with
    | some r => pure r
    | none => IO.println s!"l4vc-probe: no CLAUDE.md above {cwd}; fixtures unavailable"; pure cwd
  let t1 ← runRfc8032
  let t2 ← runDidKey root
  let t3 ← runRoundtrip
  let t4 ← runSpecVectors root
  let t5 ← runSha256Native
  IO.println "\n========================================"
  IO.println (scoreLine "ed25519-rfc8032" t1)
  IO.println (scoreLine "did:key" t2)
  IO.println (scoreLine "vc-dataintegrity-eddsa-rdfc-2022" t3)
  IO.println (scoreLine "vc-di-eddsa-spec-vectors" t4)
  IO.println (scoreLine "sha256 differential" t5)
  let total := { pass := t1.pass + t2.pass + t3.pass + t4.pass + t5.pass,
                 fail := t1.fail + t2.fail + t3.fail + t4.fail + t5.fail,
                 failures := t1.failures ++ t2.failures ++ t3.failures ++ t4.failures ++ t5.failures : Tally }
  IO.println (scoreLine "TOTAL" total)
  IO.println "========================================"
  pure (if total.fail == 0 then 0 else 1)

end VcProbe

def main (args : List String) : IO UInt32 := VcProbe.main args
