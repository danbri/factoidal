/-
Harness/JoseProbe — run the JOSE layer (`L4Factoidal/JOSE/`) and its
three HACL* primitives against published test corpora, and print score
lines in the `bin/*-runner` grammar.

This is a HARNESS, not part of the verified library: it does file I/O,
calls the `@[extern]` opaques, and prints. It exists because a `#guard`
runs in the Lean interpreter, which cannot call an extern, so nothing
that touches a real signature can be a build-time check. Everything the
pure layers decide IS a `#guard`, in the modules themselves; what is
left for this probe is exactly the part that needs HACL*.

Sections, each one score line:

  1. `jose-rfc-fixtures` — RFC 7515 Appendix A.2 (RS256) and A.3
     (ES256), and RFC 7520 §4.1 (RS256), verified end to end with the
     HACL* primitives; §4.2 (PS384) and §4.3 (ES512) refused by the
     allowlist, which is the correct outcome for two algorithms this
     project cannot check. Each verifying example is also run with one
     bit flipped in the signature, one bit flipped in the payload, and
     against the other example's key.

  2. `wycheproof-ecdsa-secp256r1-sha256-p1363` — every vector of
     `ecdsa_secp256r1_sha256_p1363_test.json`. The `_p1363` file is the
     one to use: it encodes signatures as raw `r || s`, which is what
     JWS ES256 uses (RFC 7518 §3.4). The DER file would test a parser
     this project deliberately does not have.

  3-5. `wycheproof-rsa-2048-sha256`, `-3072-`, `-4096-` — every vector
     of the three `rsa_signature_<bits>_sha256_test.json` files, through
     `Pkcs1.rs256Verify` over the HACL* public operation.

  6. `dpop-rfc9449` — the signatures of the RFC 9449 Figure 2 and
     Figure 13 proofs, checked against the key each proof carries in its
     own `jwk` header, plus the §6.1 thumbprint binding of Figure 13.

Every Wycheproof flag is honoured. A vector whose `result` is `valid`
must verify; a vector whose `result` is `invalid` must NOT verify — an
`invalid` vector that verifies is a FAIL, not a curiosity. A vector
whose `result` is `acceptable` is counted separately and named, never
folded into either bucket: `acceptable` means the vector is legal under
some readings of the specification, so neither answer is a defect, and
counting it as a pass would inflate the score.

Usage:
  lake exe l4jose-probe                run every section
  lake exe l4jose-probe --jsonl        read verification requests as
                                       JSON lines on standard input and
                                       print one JSON line per request.
                                       This is the mode
                                       `tests/jose/webcrypto-differential.mjs`
                                       drives.
-/
import L4Factoidal.JOSE.DPoP
import L4Factoidal.Crypto.P256Native
import L4Factoidal.Crypto.RsaNative
import L4Factoidal.Crypto.Ed25519
import L4Factoidal.Solid.Server.Auth

namespace JoseProbe

open L4Factoidal.JSON
open L4Factoidal.JOSE
open L4Factoidal.Crypto

/-! ## Score plumbing (the `Harness/VcProbe.lean` shape) -/

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  acceptable : Nat := 0
  failures : List String := []

def check (t : IO.Ref Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    t.modify fun s => { s with pass := s.pass + 1 }
  else
    IO.println s!"  [FAIL] {name}{if detail.isEmpty then "" else " — " ++ detail}"
    t.modify fun s => { s with fail := s.fail + 1, failures := s.failures ++ [name] }

def scoreLine (suite : String) (t : Tally) : String :=
  let total := t.pass + t.fail + t.acceptable
  if t.acceptable == 0 then
    s!"{suite}: {t.pass} pass, {t.fail} fail (out of {total})"
  else
    s!"{suite}: {t.pass} pass, {t.fail} fail, {t.acceptable} acceptable (out of {total})"

/-! ## The native verifiers

This is the ONLY place the three `@[extern]` opaques are combined into
the `Verifiers` record the library takes as a parameter. Nothing in
`L4Factoidal/JOSE/` mentions them. -/

def nativeVerifiers : Verifiers :=
  { es256 := fun pubXY msg sig => P256.p256VerifySha256 pubXY msg sig
    rs256 := fun n e sig msg => Pkcs1.rs256Verify Rsa.rsaPublicOp n e sig msg
    eddsa := fun pk msg sig => L4Factoidal.Crypto.Ed25519.verify pk msg sig }

/-! ## Hex, for the Wycheproof vectors

Wycheproof carries messages, signatures and key coordinates as
lowercase hex. This is harness plumbing over test data, not a codec the
library uses; base64url is the library's encoding and lives in
`L4Factoidal/JOSE/Base64Url.lean` with its theorems. -/

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexToBytesAux : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest =>
      match hexDigit? a, hexDigit? b with
      | some x, some y => (hexToBytesAux rest).map (UInt8.ofNat (x * 16 + y) :: ·)
      | _, _ => none

def hexToBytes? (s : String) : Option ByteArray :=
  (hexToBytesAux s.toList).map fun bs => ⟨bs.toArray⟩

/-- Left-pad a big-endian byte string to `n` bytes; `none` if it is
already longer. Wycheproof prints EC coordinates as minimal-length hex,
so a coordinate with a leading zero octet arrives short. -/
def padLeft (n : Nat) (b : ByteArray) : Option ByteArray :=
  if b.size > n then none
  else some (⟨(List.replicate (n - b.size) (0 : UInt8)).toArray⟩ ++ b)

/-! ## Repository root

A fuel-bounded walk rather than a `partial def`: the hygiene audit's
`partial def` baseline must not increase. Thirty-two levels is more
than any checkout this runs in. -/

def findRepoRootAux : Nat → System.FilePath → IO (Option System.FilePath)
  | 0, _ => pure none
  | fuel + 1, d => do
      if ← (d / "CLAUDE.md").pathExists then return some d
      match d.parent with
      | none => return none
      | some p => if p == d then return none else findRepoRootAux fuel p

def findRepoRoot (d : System.FilePath) : IO (Option System.FilePath) :=
  findRepoRootAux 32 d

/-! ## Section 1: the RFC fixtures

Every string below was transcribed from the RFC's own text (the
`.txt` from rfc-editor.org), with RFC 8792 line wrapping and display
line breaks removed by script. Writing one out by hand produced a
string that decoded to garbage on the first attempt at the RFC 9449
example, which is why none of these is typed by hand. RFC documents are
IETF Trust material and their examples may be reproduced. -/

private def rfc7515A2Jws : String :=
  "eyJhbGciOiJSUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGx" ++
  "lLmNvbS9pc19yb290Ijp0cnVlfQ.cC4hiUPoj9Eetdgtv3hF80EGrhuB__dzERat0XF9g2VtQgr9PJbu3XOiZj5R" ++
  "Zmh7AAuHIm4Bh-0Qc_lF5YKt_O8W2Fp5jujGbds9uJdbF9CUAr7t1dnZcAcQjbKBYNX4BAynRFdiuB--f_nZLgrn" ++
  "byTyWzO75vRK5h6xBArLIARNPvkSjtQBMHlb1L07Qe7K0GarZRmB_eSN9383LcOLn6_dO--xi12jzDwusC-eOkHW" ++
  "EsqtFZESc6BfI7noOPqvhJ1phCnvWh6IeYI2w9QOYEUipUTI8np6LbgGY9Fs98rqVt5AXLIhWkWywlVmtVrBp0ig" ++
  "cN_IoypGlUPQGe77Rw"

private def rfc7515A2N : String :=
  "ofgWCuLjybRlzo0tZWJjNiuSfb4p4fAkd_wWJcyQoTbji9k0l8W26mPddxHmfHQp-Vaw-4qPCJrcS2mJPMEzP1Pt" ++
  "0Bm4d4QlL-yRT-SFd2lZS-pCgNMsD1W_YpRPEwOWvG6b32690r2jZ47soMZo9wGzjb_7OMg0LOL-bSf63kpaSHSX" ++
  "ndS5z5rexMdbBYUsLA9e-KXBdQOS-UTo7WTBEMa2R2CapHg665xsmtdVMTBQY4uDZlxvb3qCo5ZwKh9kG4LT6_I5" ++
  "IhlJH7aGhyxXFvUK-DWNmoudF8NAco9_h9iaGNj8q2ethFkMLs91kzk2PAcDTW9gb54h4FRWyuXpoQ"

private def rfc7515A3Jws : String :=
  "eyJhbGciOiJFUzI1NiJ9.eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFtcGx" ++
  "lLmNvbS9pc19yb290Ijp0cnVlfQ.DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8I" ++
  "SlSApmWQxfKTUJqPP3-Kg6NU1Q"

private def rfc7520Sec41Jws : String :=
  "eyJhbGciOiJSUzI1NiIsImtpZCI6ImJpbGJvLmJhZ2dpbnNAaG9iYml0b24uZXhhbXBsZSJ9.SXTigJlzIGEgZGF" ++
  "uZ2Vyb3VzIGJ1c2luZXNzLCBGcm9kbywgZ29pbmcgb3V0IHlvdXIgZG9vci4gWW91IHN0ZXAgb250byB0aGUgcm9" ++
  "hZCwgYW5kIGlmIHlvdSBkb24ndCBrZWVwIHlvdXIgZmVldCwgdGhlcmXigJlzIG5vIGtub3dpbmcgd2hlcmUgeW9" ++
  "1IG1pZ2h0IGJlIHN3ZXB0IG9mZiB0by4.MRjdkly7_-oTPTS3AXP41iQIGKa80A0ZmTuV5MEaHoxnW2e5CZ5NlKt" ++
  "ainoFmKZopdHM1O2U4mwzJdQx996ivp83xuglII7PNDi84wnB-BDkoBwA78185hX-Es4JIwmDLJK3lfWRa-XtL0R" ++
  "nltuYv746iYTh_qHRD68BNt1uSNCrUCTJDt5aAE6x8wW1Kt9eRo4QPocSadnHXFxnt8Is9UzpERV0ePPQdLuW3IS" ++
  "_de3xyIrDaLGdjluPxUAhb6L2aXic1U12podGU0KLUQSE_oI-ZnmKJ3F4uOZDnd6QZWJushZ41Axf_fcIe8u9ipH" ++
  "84ogoree7vjbU5y18kDquDg"

private def rfc7520Sec42Jws : String :=
  "eyJhbGciOiJQUzM4NCIsImtpZCI6ImJpbGJvLmJhZ2dpbnNAaG9iYml0b24uZXhhbXBsZSJ9.SXTigJlzIGEgZGF" ++
  "uZ2Vyb3VzIGJ1c2luZXNzLCBGcm9kbywgZ29pbmcgb3V0IHlvdXIgZG9vci4gWW91IHN0ZXAgb250byB0aGUgcm9" ++
  "hZCwgYW5kIGlmIHlvdSBkb24ndCBrZWVwIHlvdXIgZmVldCwgdGhlcmXigJlzIG5vIGtub3dpbmcgd2hlcmUgeW9" ++
  "1IG1pZ2h0IGJlIHN3ZXB0IG9mZiB0by4.cu22eBqkYDKgIlTpzDXGvaFfz6WGoz7fUDcfT0kkOy42miAh2qyBzk1" ++
  "xEsnk2IpN6-tPid6VrklHkqsGqDqHCdP6O8TTB5dDDItllVo6_1OLPpcbUrhiUSMxbbXUvdvWXzg-UD8biiReQFl" ++
  "fz28zGWVsdiNAUf8ZnyPEgVFn442ZdNqiVJRmBqrYRXe8P_ijQ7p8Vdz0TTrxUeT3lm8d9shnr2lfJT8ImUjvAA2" ++
  "Xez2Mlp8cBE5awDzT0qI0n6uiP1aCN_2_jLAeQTlqRHtfa64QQSUmFAAjVKPbByi7xho0uTOcbH510a6GYmJUAfm" ++
  "WjwZ6oD4ifKo8DYM-X72Eaw"

private def rfc7520Sec43Jws : String :=
  "eyJhbGciOiJFUzUxMiIsImtpZCI6ImJpbGJvLmJhZ2dpbnNAaG9iYml0b24uZXhhbXBsZSJ9.SXTigJlzIGEgZGF" ++
  "uZ2Vyb3VzIGJ1c2luZXNzLCBGcm9kbywgZ29pbmcgb3V0IHlvdXIgZG9vci4gWW91IHN0ZXAgb250byB0aGUgcm9" ++
  "hZCwgYW5kIGlmIHlvdSBkb24ndCBrZWVwIHlvdXIgZmVldCwgdGhlcmXigJlzIG5vIGtub3dpbmcgd2hlcmUgeW9" ++
  "1IG1pZ2h0IGJlIHN3ZXB0IG9mZiB0by4.AE_R_YZCChjn4791jSQCrdPZCNYqHXCTZH0-JZGYNlaAjP2kqaluUII" ++
  "UnC9qvbu9Plon7KRTzoNEuT4Va2cmL1eJAQy3mtPBu_u_sDDyYjnAMDxXPn7XrT0lw-kvAD890jl8e2puQens_IE" ++
  "KBpHABlsbEPX6sFY8OcGDqoRuBomu9xQ2"

private def rfc7520N : String :=
  "n4EPtAOCc9AlkeQHPzHStgAbgs7bTZLwUBZdR8_KuKPEHLd4rHVTeT-O-XV2jRojdNhxJWTDvNd7nqQ0VEiZQHz_" ++
  "AJmSCpMaJMRBSFKrKb2wqVwGU_NsYOYL-QtiWN2lbzcEe6XC0dApr5ydQLrHqkHHig3RBordaZ6Aj-oBHqFEHYpP" ++
  "e7Tpe-OfVfHd1E6cS6M1FZcD1NNLYD5lFHpPI9bTwJlsde3uhGqC0ZCuEHg8lhzwOHrtIQbS0FVbb9k3-tVTU4fg" ++
  "_3L_vniUFAKwuCLqKnS2BYwdq_mzSnbLY7h_qixoR7jig3__kRhuaxwUkRz5iaiQkqgc5gHdrNP5zw"


private def rfc9449Fig2 : String :=
  "eyJ0eXAiOiJkcG9wK2p3dCIsImFsZyI6IkVTMjU2IiwiandrIjp7Imt0eSI6IkVDIiwieCI6Imw4dEZyaHgtMzR0Vj" ++
  "NoUklDUkRZOXpDa0RscEJoRjQyVVFVZldWQVdCRnMiLCJ5IjoiOVZFNGpmX09rX282NHpiVFRsY3VOSmFqSG10NnY5" ++
  "VERWclUwQ2R2R1JEQSIsImNydiI6IlAtMjU2In19.eyJqdGkiOiItQndDM0VTYzZhY2MybFRjIiwiaHRtIjoiUE9TV" ++
  "CIsImh0dSI6Imh0dHBzOi8vc2VydmVyLmV4YW1wbGUuY29tL3Rva2VuIiwiaWF0IjoxNTYyMjYyNjE2fQ.2-GxA6T8" ++
  "lP4vfrg8v-FdWP0A0zdrj8igiMLvqRMUvwnQg4PtFLbdLXiOSsX0x7NVY-FNyJK70nfbV37xRZT3Lg"

private def rfc9449Fig13 : String :=
  "eyJ0eXAiOiJkcG9wK2p3dCIsImFsZyI6IkVTMjU2IiwiandrIjp7Imt0eSI6IkVDIiwieCI6Imw4dEZyaHgtMzR0Vj" ++
  "NoUklDUkRZOXpDa0RscEJoRjQyVVFVZldWQVdCRnMiLCJ5IjoiOVZFNGpmX09rX282NHpiVFRsY3VOSmFqSG10NnY5" ++
  "VERWclUwQ2R2R1JEQSIsImNydiI6IlAtMjU2In19.eyJqdGkiOiJlMWozVl9iS2ljOC1MQUVCIiwiaHRtIjoiR0VUI" ++
  "iwiaHR1IjoiaHR0cHM6Ly9yZXNvdXJjZS5leGFtcGxlLm9yZy9wcm90ZWN0ZWRyZXNvdXJjZSIsImlhdCI6MTU2MjI" ++
  "2MjYxOCwiYXRoIjoiZlVIeU8ycjJaM0RaNTNFc05yV0JiMHhXWG9hTnk1OUlpS0NBcWtzbVFFbyJ9.2oW9RP35yRqz" ++
  "hrtNP86L-Ey71EOptxRimPPToA1plemAgR6pxHF8y6-yqyVnmcw6Fy1dqd-jfxSYoMxhAJpLjA"

/-- The RFC 7515 Appendix A.2 RSA public key, `e` = 65537 (`AQAB`). -/
private def rfc7515A2Key : Jwk :=
  (parseJwkString? ("{\"kty\":\"RSA\",\"e\":\"AQAB\",\"n\":\"" ++ rfc7515A2N ++ "\"}")).getD
    (.okp ByteArray.empty)

/-- The RFC 7515 Appendix A.3.1 EC public key (the private `d` member of
the RFC's key is dropped: this is a verifier). -/
private def rfc7515A3Key : Jwk :=
  (parseJwkString? ("{\"kty\":\"EC\",\"crv\":\"P-256\"," ++
    "\"x\":\"f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU\"," ++
    "\"y\":\"x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0\"}")).getD (.okp ByteArray.empty)

/-- The RFC 7520 §3.3 RSA public key ("bilbo.baggins@hobbiton.example"). -/
private def rfc7520Key : Jwk :=
  (parseJwkString? ("{\"kty\":\"RSA\",\"e\":\"AQAB\",\"n\":\"" ++ rfc7520N ++ "\"}")).getD
    (.okp ByteArray.empty)

/-- Flip the last character of a compact JWS's signature part to a
different alphabet character, keeping the token well formed. -/
private def tamperSignature (jws : String) : String :=
  match jws.splitOn "." with
  | [h, p, s] =>
      let cs := s.toList
      match cs.reverse with
      | [] => jws
      | last :: rest =>
          let replacement := if last == 'A' then 'B' else 'A'
          h ++ "." ++ p ++ "." ++ String.ofList (replacement :: rest).reverse
  | _ => jws

/-- Change the payload without touching the signature. -/
private def tamperPayload (jws : String) : String :=
  match jws.splitOn "." with
  | [h, _, s] => h ++ "." ++ Base64Url.encodeUtf8 "{\"iss\":\"eve\"}" ++ "." ++ s
  | _ => jws

def runRfcFixtures : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- jose-rfc-fixtures"
  -- The keys parsed.
  check t "RFC 7515 A.2 RSA key parses" (rfc7515A2Key.kty == .rsa)
  check t "RFC 7515 A.3 EC key parses" (rfc7515A3Key.kty == .ec)
  check t "RFC 7520 3.3 RSA key parses" (rfc7520Key.kty == .rsa)
  -- The three verifying examples.
  check t "RFC 7515 A.2 RS256 verifies"
    (verifyCompact nativeVerifiers rfc7515A2Key rfc7515A2Jws == .verified)
    s!"{repr (verifyCompact nativeVerifiers rfc7515A2Key rfc7515A2Jws)}"
  check t "RFC 7515 A.3 ES256 verifies"
    (verifyCompact nativeVerifiers rfc7515A3Key rfc7515A3Jws == .verified)
    s!"{repr (verifyCompact nativeVerifiers rfc7515A3Key rfc7515A3Jws)}"
  check t "RFC 7520 4.1 RS256 verifies"
    (verifyCompact nativeVerifiers rfc7520Key rfc7520Sec41Jws == .verified)
    s!"{repr (verifyCompact nativeVerifiers rfc7520Key rfc7520Sec41Jws)}"
  -- A tampered signature and a tampered payload are refused.
  check t "RFC 7515 A.2 tampered signature refused"
    (verifyCompact nativeVerifiers rfc7515A2Key (tamperSignature rfc7515A2Jws) != .verified)
  check t "RFC 7515 A.2 tampered payload refused"
    (verifyCompact nativeVerifiers rfc7515A2Key (tamperPayload rfc7515A2Jws) != .verified)
  check t "RFC 7515 A.3 tampered signature refused"
    (verifyCompact nativeVerifiers rfc7515A3Key (tamperSignature rfc7515A3Jws) != .verified)
  check t "RFC 7515 A.3 tampered payload refused"
    (verifyCompact nativeVerifiers rfc7515A3Key (tamperPayload rfc7515A3Jws) != .verified)
  check t "RFC 7520 4.1 tampered signature refused"
    (verifyCompact nativeVerifiers rfc7520Key (tamperSignature rfc7520Sec41Jws) != .verified)
  -- The wrong RSA key for the right algorithm.
  check t "RFC 7515 A.2 under the RFC 7520 key refused"
    (verifyCompact nativeVerifiers rfc7520Key rfc7515A2Jws != .verified)
  check t "RFC 7520 4.1 under the RFC 7515 A.2 key refused"
    (verifyCompact nativeVerifiers rfc7515A2Key rfc7520Sec41Jws != .verified)
  -- The wrong key TYPE.
  check t "RFC 7515 A.2 under an EC key is a key-type mismatch"
    (verifyCompact nativeVerifiers rfc7515A3Key rfc7515A2Jws == .keyTypeMismatch)
  check t "RFC 7515 A.3 under an RSA key is a key-type mismatch"
    (verifyCompact nativeVerifiers rfc7515A2Key rfc7515A3Jws == .keyTypeMismatch)
  -- Two RFC 7520 examples this project cannot check are REFUSED by the
  -- allowlist rather than mis-verified. PS384 and ES512 are real
  -- algorithms; a verifier that silently accepted them would be
  -- claiming a check it does not perform.
  check t "RFC 7520 4.2 PS384 refused by the allowlist"
    (verifyCompact nativeVerifiers rfc7520Key rfc7520Sec42Jws == .refused (.algNotAllowed "PS384"))
  check t "RFC 7520 4.3 ES512 refused by the allowlist"
    (verifyCompact nativeVerifiers rfc7515A3Key rfc7520Sec43Jws
      == .refused (.algNotAllowed "ES512"))
  t.get

/-! ## Wycheproof -/

/-- One Wycheproof expectation. `acceptable` is its own bucket: the
project's answer is not a defect either way, so folding it into `pass`
would inflate the score and folding it into `fail` would invent one. -/
inductive Expect where
  | valid
  | invalid
  | acceptable
  deriving DecidableEq, Repr

def expectOf? (s : String) : Option Expect :=
  match s with
  | "valid" => some .valid
  | "invalid" => some .invalid
  | "acceptable" => some .acceptable
  | _ => none

def readJsonFile (p : System.FilePath) : IO (Option Json) := do
  if !(← p.pathExists) then return none
  let text ← IO.FS.readFile p
  return parseJson? text

/-- Drop leading zero octets. -/
def stripLeadingZeros (b : ByteArray) : ByteArray :=
  ⟨(b.data.toList.dropWhile (· == 0)).toArray⟩

/-- The group's public key, in the encoding this project consumes.

`publicKeyJwk` is present for most groups and is exactly a JWK. Nine of
the 112 groups of `ecdsa_secp256r1_sha256_p1363_test.json` have no
`publicKeyJwk` at all — they are the special-case public keys Wycheproof
constructs to probe point validation, which JWK cannot express — so the
raw `publicKey.wx` / `.wy` hex is the fallback. Those coordinates are
printed at minimal length and can carry an ASN.1 leading zero octet, so
they are stripped and left-padded to 32.

A group whose key cannot be built at all is NOT skipped: `none` here
means the verifier refuses every vector in the group, and each vector is
still scored against its own expectation. Skipping them would drop 10
`invalid` vectors out of the denominator, which is exactly the kind of
silent cap that makes a green score meaningless. -/
def ecGroupKey? (g : Json) : Option Jwk :=
  match (g.field? "publicKeyJwk").bind parseJwk? with
  | some k => some k
  | none =>
      match g.field? "publicKey" with
      | none => none
      | some pk =>
          match (pk.getString? "wx").bind hexToBytes?,
                (pk.getString? "wy").bind hexToBytes? with
          | some wx, some wy =>
              match padLeft 32 (stripLeadingZeros wx), padLeft 32 (stripLeadingZeros wy) with
              | some x, some y => some (.ec x y)
              | _, _ => none
          | _, _ => none

/-- Run one ECDSA P1363 vector file. -/
def runEcdsaFile (path : System.FilePath) (label : String) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println s!"-- {label}"
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [FAIL] {label}: cannot read {path}"
      t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
      return (← t.get)
  | some j =>
      let groups := (j.getArray? "testGroups").getD []
      if groups.isEmpty then
        IO.println s!"  [FAIL] {label}: no testGroups in {path}"
        t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
        return (← t.get)
      for g in groups do
        let key? := ecGroupKey? g
        for tc in (g.getArray? "tests").getD [] do
          let id := (tc.field? "tcId").map (fun v => match v with
                      | .number n => n | _ => "?") |>.getD "?"
          let name := s!"{label} tcId={id}"
          match expectOf? ((tc.getString? "result").getD ""),
                hexToBytes? ((tc.getString? "msg").getD ""),
                hexToBytes? ((tc.getString? "sig").getD "") with
          | some e, some msg, some sig =>
              let accepted :=
                match key? with
                | none => false
                | some key => verifyWith nativeVerifiers .es256 key msg sig == some true
              match e with
              | .valid => check t name accepted "expected valid, verifier refused"
              | .invalid => check t name (!accepted) "expected invalid, verifier ACCEPTED"
              | .acceptable =>
                  IO.println s!"  [ACCEPTABLE] {name} — verifier answered {if accepted then "accept" else "refuse"}"
                  t.modify fun s => { s with acceptable := s.acceptable + 1 }
          | _, _, _ => check t name false "unreadable vector"
      t.get

/-- Run one RSASSA-PKCS1-v1_5 vector file. The key comes from each
group's `keyJwk`. -/
def runRsaFile (path : System.FilePath) (label : String) : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println s!"-- {label}"
  match ← readJsonFile path with
  | none =>
      IO.println s!"  [FAIL] {label}: cannot read {path}"
      t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
      return (← t.get)
  | some j =>
      let groups := (j.getArray? "testGroups").getD []
      if groups.isEmpty then
        IO.println s!"  [FAIL] {label}: no testGroups in {path}"
        t.modify fun s => { s with fail := s.fail + 1, failures := [label] }
        return (← t.get)
      for g in groups do
        let keyJson := (g.field? "keyJwk").getD .null
        match parseJwk? keyJson with
        | none => check t s!"{label}: group key parses" false "keyJwk not an accepted RSA key"
        | some key =>
            for tc in (g.getArray? "tests").getD [] do
              let id := (tc.field? "tcId").map (fun v => match v with
                          | .number n => n | _ => "?") |>.getD "?"
              let name := s!"{label} tcId={id}"
              match expectOf? ((tc.getString? "result").getD ""),
                    hexToBytes? ((tc.getString? "msg").getD ""),
                    hexToBytes? ((tc.getString? "sig").getD "") with
              | some e, some msg, some sig =>
                  let got := verifyWith nativeVerifiers .rs256 key msg sig
                  let accepted := got == some true
                  match e with
                  | .valid => check t name accepted "expected valid, verifier refused"
                  | .invalid => check t name (!accepted) "expected invalid, verifier ACCEPTED"
                  | .acceptable =>
                      IO.println s!"  [ACCEPTABLE] {name} — verifier answered {if accepted then "accept" else "refuse"}"
                      t.modify fun s => { s with acceptable := s.acceptable + 1 }
              | _, _, _ => check t name false "unreadable vector"
      t.get

/-! ## Section 6: the RFC 9449 proofs, signature and binding -/

private def headerOf (tk : String) : Json :=
  ((preKey tk).toOption.map (fun ch => ch.2.json)).getD .null

def runDPoP : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- dpop-rfc9449"
  for (label, tk) in [("Figure 2", rfc9449Fig2), ("Figure 13", rfc9449Fig13)] do
    match (headerOf tk).field? "jwk" >>= parsePublicJwk? with
    | none => check t s!"RFC 9449 {label}: jwk header is a public key" false ""
    | some key =>
        check t s!"RFC 9449 {label}: signature verifies under its own jwk"
          (verifyCompact nativeVerifiers key tk == .verified)
          s!"{repr (verifyCompact nativeVerifiers key tk)}"
        check t s!"RFC 9449 {label}: tampered signature refused"
          (verifyCompact nativeVerifiers key (tamperSignature tk) != .verified)
        check t s!"RFC 9449 {label}: §6.1 thumbprint"
          (thumbprint key == "0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I")
  -- Figure 13 end to end: the proof, the access token it carries the
  -- hash of, and the cnf.jkt the token is bound to.
  let tok := "Kz~8mXK1EalYznwH-LC-1fBAo.4Ljp~zsPE_NeO.gxU".toUTF8
  let pol : ProofPolicy :=
    { now := 1562262618, iatWindow := 60, jtiFresh := fun _ => true }
  let req : ProofRequest :=
    { method := "GET", uri := "https://resource.example.org/protectedresource" }
  let jkt := "0ZcOCORZNYy-DWpqq30jZyJGHTN0d2HglBV3uiguA4I"
  check t "RFC 9449 Figure 13: full proof validation"
    (validateProof nativeVerifiers pol req (some tok) (some jkt) rfc9449Fig13 == .ok)
    s!"{repr (validateProof nativeVerifiers pol req (some tok) (some jkt) rfc9449Fig13)}"
  check t "RFC 9449 Figure 13: another token's cnf.jkt refused"
    (validateProof nativeVerifiers pol req (some tok)
      (some "kPrK_qmxVWaYVA9wwBF6Iuo3vVzz7TxHCTwXBygrS4k") rfc9449Fig13
      == .keyThumbprintMismatch)
  check t "RFC 9449 Figure 13: another access token refused"
    (validateProof nativeVerifiers pol req (some "different".toUTF8) (some jkt) rfc9449Fig13
      == .athMismatch)
  check t "RFC 9449 Figure 13: another request URI refused"
    (validateProof nativeVerifiers pol
      { req with uri := "https://resource.example.org/other" } (some tok) (some jkt)
      rfc9449Fig13 == .htuMismatch)
  check t "RFC 9449 Figure 13: a replayed jti refused"
    (validateProof nativeVerifiers { pol with jtiFresh := fun _ => false } req
      (some tok) (some jkt) rfc9449Fig13 == .jtiReplayed)
  t.get

/-! ## Section 7: Solid-OIDC authentication, end to end

`L4Factoidal/Solid/Server/Auth.lean` decides whether a request carries a
valid Solid-OIDC identity. Checking that needs a SIGNED access token and
a SIGNED DPoP proof, so this section mints both with the one signing
primitive the tree has — HACL* Ed25519 — and runs
`Solid.Server.authenticate` over a synthetic request.

Ed25519 rather than ES256 because HACL*'s ECDSA signing entry takes a
caller-supplied nonce and this project binds only the verification side
(`Crypto/P256Native.lean` exposes no signer, deliberately). `EdDSA` is
in the JWS allowlist and Solid-OIDC does not forbid it, so the chain
exercised here is the same chain an `ES256` token takes: allowlist, key
type, signature, claims, DPoP binding. -/

private def edSecret : ByteArray :=
  ⟨(List.replicate 32 (0x42 : UInt8)).toArray⟩

private def edPublic : ByteArray := L4Factoidal.Crypto.Ed25519.secretToPublic edSecret

private def edJwkJson : String :=
  "{\"kty\":\"OKP\",\"crv\":\"Ed25519\",\"x\":\"" ++ Base64Url.encode edPublic ++ "\"}"

private def edJwk : Jwk := (parseJwkString? edJwkJson).getD (.okp ByteArray.empty)

/-- Mint a compact JWS with Ed25519. Harness plumbing: the library
never signs. -/
private def signEd (header payload : String) : String :=
  let h := Base64Url.encodeUtf8 header
  let p := Base64Url.encodeUtf8 payload
  let sig := L4Factoidal.Crypto.Ed25519.sign edSecret (h ++ "." ++ p).toUTF8
  h ++ "." ++ p ++ "." ++ Base64Url.encode sig

def runSolidOidc : IO Tally := do
  let t ← IO.mkRef ({} : Tally)
  IO.println "-- solid-oidc"
  check t "the harness Ed25519 key is a usable OKP JWK" (edJwk.kty == .okp)
  let jkt := thumbprint edJwk
  let now : Int := 1700000000
  let token := signEd "{\"alg\":\"EdDSA\"}"
    ("{\"iss\":\"https://idp.example/\",\"sub\":\"https://alice.example/card#me\"," ++
     "\"webid\":\"https://alice.example/card#me\",\"aud\":\"https://storage.example/\"," ++
     "\"exp\":1700000600,\"iat\":1700000000,\"cnf\":{\"jkt\":\"" ++ jkt ++ "\"}}")
  let ath := athFor token.toUTF8
  let proof := signEd ("{\"typ\":\"dpop+jwt\",\"alg\":\"EdDSA\",\"jwk\":" ++ edJwkJson ++ "}")
    ("{\"jti\":\"j-1\",\"htm\":\"GET\",\"htu\":\"https://storage.example/r\"," ++
     "\"iat\":1700000000,\"ath\":\"" ++ ath ++ "\"}")
  let cfg : L4Factoidal.Solid.Server.ServerConfig :=
    { lws := { baseIri := "https://storage.example/" },
      auth := { enforceAuth := true, idpKeys := [edJwk],
                policy := { now := now, leeway := 60, issuer := "https://idp.example/",
                            audience := "https://storage.example/" },
                proofPolicy := { now := now, iatWindow := 60, jtiFresh := fun _ => true } } }
  let mkReq (headers : List (String × String)) : L4Factoidal.HTTP.Request :=
    { method := "GET", path := "/r", queryStr := "", headers := headers }
  let good := mkReq [("authorization", "DPoP " ++ token), ("dpop", proof)]
  let got := L4Factoidal.Solid.Server.authenticate nativeVerifiers cfg good
  check t "a valid DPoP-bound token authenticates"
    (got == .authenticated "https://alice.example/card#me" jkt) s!"{repr got}"
  -- The same token as a bearer credential is refused.
  check t "the same token as Bearer is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers cfg
      (mkReq [("authorization", "Bearer " ++ token)]) == .refused (.wrongScheme "Bearer"))
  -- No proof.
  check t "no DPoP header is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers cfg
      (mkReq [("authorization", "DPoP " ++ token)]) == .refused .missingProof)
  let otherPath := { good with path := "/other" }
  check t "a proof whose htu is another path is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers cfg otherPath
      == .refused (.proofRefused .htuMismatch))
  -- The request method changed.
  check t "a proof whose htm is another method is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers cfg { good with method := "PUT" }
      == .refused (.proofRefused .htmMismatch))
  -- The clock moved past the expiry.
  let lateCfg := { cfg with auth := { cfg.auth with
    policy := { cfg.auth.policy with now := 1700000700 } } }
  check t "an expired token is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers lateCfg good
      == .refused (.claimsRefused .expired))
  -- Another issuer.
  let otherIss := { cfg with auth := { cfg.auth with
    policy := { cfg.auth.policy with issuer := "https://evil.example/" } } }
  check t "a token from another issuer is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers otherIss good
      == .refused (.claimsRefused .issuerMismatch))
  -- A replayed jti.
  let replay := { cfg with auth := { cfg.auth with
    proofPolicy := { cfg.auth.proofPolicy with jtiFresh := fun _ => false } } }
  check t "a replayed jti is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers replay good
      == .refused (.proofRefused .jtiReplayed))
  -- The identity provider's key list is empty.
  let noKeys := { cfg with auth := { cfg.auth with idpKeys := [] } }
  check t "no configured identity-provider key refuses, it does not fall open"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers noKeys good
      == .refused (.noTrustedKey []))
  -- A token signed by a key the identity provider did not publish.
  let strangerJwk : Jwk :=
    (parseJwkString? ("{\"kty\":\"OKP\",\"crv\":\"Ed25519\"," ++
      "\"x\":\"11qYAYKxCrfVS_7TyWQHOg7hcvPapiMlrwIaaPcHURo\"}")).getD (.okp ByteArray.empty)
  let strangerCfg := { cfg with auth := { cfg.auth with idpKeys := [strangerJwk] } }
  check t "a token signed by an unpublished key is refused"
    (match L4Factoidal.Solid.Server.authenticate nativeVerifiers strangerCfg good with
     | .refused (.noTrustedKey _) => true
     | _ => false)
  -- A token bound to a DIFFERENT key than the proof's.
  let wrongBindToken := signEd "{\"alg\":\"EdDSA\"}"
    ("{\"iss\":\"https://idp.example/\",\"sub\":\"https://alice.example/card#me\"," ++
     "\"webid\":\"https://alice.example/card#me\",\"aud\":\"https://storage.example/\"," ++
     "\"exp\":1700000600,\"iat\":1700000000," ++
     "\"cnf\":{\"jkt\":\"kPrK_qmxVWaYVA9wwBF6Iuo3vVzz7TxHCTwXBygrS4k\"}}")
  let wrongAth := athFor wrongBindToken.toUTF8
  let wrongProof := signEd
    ("{\"typ\":\"dpop+jwt\",\"alg\":\"EdDSA\",\"jwk\":" ++ edJwkJson ++ "}")
    ("{\"jti\":\"j-2\",\"htm\":\"GET\",\"htu\":\"https://storage.example/r\"," ++
     "\"iat\":1700000000,\"ath\":\"" ++ wrongAth ++ "\"}")
  check t "a token bound to another key is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers cfg
      (mkReq [("authorization", "DPoP " ++ wrongBindToken), ("dpop", wrongProof)])
      == .refused (.proofRefused .keyThumbprintMismatch))
  -- A proof whose ath is another token's.
  check t "a proof carrying another token's ath is refused"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers cfg
      (mkReq [("authorization", "DPoP " ++ token), ("dpop", wrongProof)])
      == .refused (.proofRefused .athMismatch))
  -- With enforcement off, the same request is `disabled` and the
  -- handle configuration's WebID stands.
  check t "with enforceAuth off the decision is disabled"
    (L4Factoidal.Solid.Server.authenticate nativeVerifiers
      { cfg with auth := { cfg.auth with enforceAuth := false } } good == .disabled)
  t.get

/-! ## The `--jsonl` mode

One JSON object per input line; one JSON object per output line, in the
same order. This is the interface `tests/jose/webcrypto-differential.mjs`
drives: Node generates keys and signatures with WebCrypto, and this
binary says whether the JOSE layer accepts each one.

Request:  {"alg":"ES256","key":{JWK},"msg":"<hex>","sig":"<hex>"}
Response: {"ok":true|false} or {"error":"<reason>"}
-/

def handleJsonLine (line : String) : String :=
  match parseJson? line with
  | none => "{\"error\":\"unparseable request\"}"
  | some j =>
      match j.getString? "alg", j.field? "key",
            (j.getString? "msg").bind hexToBytes?,
            (j.getString? "sig").bind hexToBytes? with
      | some algName, some keyJson, some msg, some sig =>
          match algOfString? algName, parseJwk? keyJson with
          | none, _ => "{\"error\":\"alg not in the allowlist\"}"
          | _, none => "{\"error\":\"key not accepted\"}"
          | some alg, some key =>
              match verifyWith nativeVerifiers alg key msg sig with
              | none => "{\"error\":\"key type does not match alg\"}"
              | some b => if b then "{\"ok\":true}" else "{\"ok\":false}"
      | _, _, _, _ => "{\"error\":\"missing or unreadable field\"}"

def runJsonl : IO UInt32 := do
  let stdin ← IO.getStdin
  let rec loop (fuel : Nat) : IO Unit := do
    match fuel with
    | 0 => IO.eprintln "l4jose-probe: --jsonl input cap reached"
    | fuel + 1 =>
        let line ← stdin.getLine
        if line.isEmpty then return ()
        let trimmed := line.trimAscii.toString
        if trimmed.isEmpty then loop fuel
        else
          IO.println (handleJsonLine trimmed)
          loop fuel
  loop 1000000
  pure 0

/-! ## Entry point -/

def main (args : List String) : IO UInt32 := do
  if args.contains "--jsonl" then return (← runJsonl)
  let cwd ← IO.currentDir
  let root ← match ← findRepoRoot cwd with
    | some r => pure r
    | none =>
        IO.println s!"l4jose-probe: no CLAUDE.md above {cwd}; Wycheproof vectors unavailable"
        pure cwd
  let wp := root / "third_party" / "testing" / "wycheproof" / "testvectors_v1"
  let t1 ← runRfcFixtures
  let t2 ← runEcdsaFile (wp / "ecdsa_secp256r1_sha256_p1363_test.json")
             "wycheproof-ecdsa-secp256r1-sha256-p1363"
  let t3 ← runRsaFile (wp / "rsa_signature_2048_sha256_test.json")
             "wycheproof-rsa-2048-sha256"
  let t4 ← runRsaFile (wp / "rsa_signature_3072_sha256_test.json")
             "wycheproof-rsa-3072-sha256"
  let t5 ← runRsaFile (wp / "rsa_signature_4096_sha256_test.json")
             "wycheproof-rsa-4096-sha256"
  let t6 ← runDPoP
  let t7 ← runSolidOidc
  IO.println "\n========================================"
  IO.println (scoreLine "jose-rfc-fixtures" t1)
  IO.println (scoreLine "wycheproof-ecdsa-secp256r1-sha256-p1363" t2)
  IO.println (scoreLine "wycheproof-rsa-2048-sha256" t3)
  IO.println (scoreLine "wycheproof-rsa-3072-sha256" t4)
  IO.println (scoreLine "wycheproof-rsa-4096-sha256" t5)
  IO.println (scoreLine "dpop-rfc9449" t6)
  IO.println (scoreLine "solid-oidc" t7)
  let ts := [t1, t2, t3, t4, t5, t6, t7]
  let total : Tally :=
    { pass := (ts.map Tally.pass).foldl (· + ·) 0,
      fail := (ts.map Tally.fail).foldl (· + ·) 0,
      acceptable := (ts.map Tally.acceptable).foldl (· + ·) 0,
      failures := (ts.map Tally.failures).flatten }
  IO.println (scoreLine "TOTAL" total)
  IO.println "========================================"
  pure (if total.fail == 0 then 0 else 1)

end JoseProbe

def main (args : List String) : IO UInt32 := JoseProbe.main args
