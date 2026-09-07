/-
L4Factoidal.XMPP.Scram — the SCRAM-SHA-256 server-side COMPUTATION
(RFC 5802 sections 2.2 and 3, with the hash pinned to SHA-256 by
RFC 7677 section 3).

`L4Factoidal.XMPP.Sasl` covers the message GRAMMAR. This module covers
the arithmetic the grammar carries: SaltedPassword, ClientKey,
StoredKey, ServerKey, AuthMessage, and the two checks a server makes —
recover ClientKey from the ClientProof and compare its hash to
StoredKey, then emit the ServerSignature.

  SaltedPassword := PBKDF2 (password, salt, i, 32)
  ClientKey      := HMAC (SaltedPassword, "Client Key")
  StoredKey      := H (ClientKey)
  ServerKey      := HMAC (SaltedPassword, "Server Key")
  AuthMessage    := client-first-bare ++ "," ++ server-first ++ "," ++
                    client-final-without-proof
  ClientSignature := HMAC (StoredKey, AuthMessage)
  ClientProof    := ClientKey XOR ClientSignature
  ServerSignature := HMAC (ServerKey, AuthMessage)

A server never holds the password when it holds StoredKey and ServerKey,
so both entry points below come in two forms: one that starts from a
password (what a first-slice server with a plaintext account file has)
and one that starts from the stored keys (what a real deployment stores).
The password form calls the stored-key form; there is one verification
path, not two.

Base64 is `L4Factoidal.XSD.base64OfBytes` / `parseBase64Lex` —
the RFC 4648 standard alphabet with padding, which is what SCRAM uses
and what that module already implements for `xsd:base64Binary`. No
second base64 is defined here.

Test vectors: the RFC 7677 section 3 exchange (username "user",
password "pencil") — the published ClientProof verifies and the
published ServerSignature is reproduced. See the note above those
`#guard`s for why the stored keys are constants and where the 4096-
iteration derivation is exercised instead.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Crypto.Hmac
import L4Factoidal.XSD.Datatypes
import L4Factoidal.XMPP.Sasl

namespace L4Factoidal.XMPP.Scram

open L4Factoidal.Crypto (hmacSha256 pbkdf2Sha256 sha256 xorBytes sha256DigestBytes)

/-- The bytes of a base64 text, or `none` when it is not base64. -/
def b64Decode (s : String) : Option ByteArray :=
  (L4Factoidal.XSD.parseBase64Lex s).map
    (fun ns => ByteArray.mk (ns.map UInt8.ofNat).toArray)

/-- The RFC 4648 standard-alphabet, padded encoding of some bytes. -/
def b64Encode (b : ByteArray) : String :=
  L4Factoidal.XSD.base64OfBytes (b.toList.map UInt8.toNat)

/-- The two RFC 5802 key-derivation constants, as bytes. -/
def clientKeyLabel : ByteArray := "Client Key".toUTF8
def serverKeyLabel : ByteArray := "Server Key".toUTF8

/-- What a server stores for one account: RFC 5802 section 3's
`StoredKey` and `ServerKey`, with the salt and iteration count it must
echo in the server-first message. The password itself is not part of
this record — that is the point of SCRAM. -/
structure StoredCredentials where
  /-- The salt, as the base64 text sent in `s=`. -/
  saltB64 : String
  iterationCount : Nat
  storedKey : ByteArray
  serverKey : ByteArray

/-- Derive the two stored keys from a plaintext password. A deployment
runs this once, at account creation, and keeps only the result. -/
def credentialsOfPassword (password : String) (saltB64 : String)
    (iterationCount : Nat) : Option StoredCredentials :=
  match b64Decode saltB64 with
  | none => none
  | some salt =>
    if iterationCount == 0 then none else
    let saltedPassword := pbkdf2Sha256 password.toUTF8 salt iterationCount sha256DigestBytes
    let clientKey := hmacSha256 saltedPassword clientKeyLabel
    some {
      saltB64 := saltB64
      iterationCount := iterationCount
      storedKey := sha256 clientKey
      serverKey := hmacSha256 saltedPassword serverKeyLabel }

/-- RFC 5802 section 3's AuthMessage. The three parts are the exact
strings that went over the wire, not re-rendered ones — a server that
re-renders them can compute a different AuthMessage from the client's
and reject a correct proof, so the caller passes the received text. -/
def authMessage (clientFirstBare serverFirst clientFinalNoProof : String) : String :=
  clientFirstBare ++ "," ++ serverFirst ++ "," ++ clientFinalNoProof

/-- The `n=<user>,r=<nonce>` tail of the client-first message — the
"bare" part AuthMessage uses, without the gs2 header. -/
def clientFirstBare (m : Sasl.ClientFirstMessage) : String :=
  s!"n={m.username},r={m.clientNonce}"

/-- The client-final message with its `,p=...` removed, which is the
third component of AuthMessage. -/
def clientFinalNoProof (m : Sasl.ClientFinalMessage) : String :=
  s!"c={m.channelBinding},r={m.nonce}"

/-- Verify a client's proof against stored credentials, and return the
ServerSignature to send back in `v=` on success.

The check is RFC 5802 section 3 run backwards: `ClientKey` is recovered
as `ClientProof XOR HMAC (StoredKey, AuthMessage)`, and the candidate is
accepted exactly when `H (ClientKey)` equals the stored `StoredKey`. A
proof of the wrong length, or one that is not base64, is a failure and
never an acceptance. -/
def verifyClientProof (cred : StoredCredentials) (auth : String)
    (proofB64 : String) : Option String :=
  match b64Decode proofB64 with
  | none => none
  | some proof =>
    if proof.size != sha256DigestBytes then none else
    let clientSignature := hmacSha256 cred.storedKey auth.toUTF8
    let clientKey := xorBytes proof clientSignature
    if sha256 clientKey == cred.storedKey then
      some (b64Encode (hmacSha256 cred.serverKey auth.toUTF8))
    else none

/-- The `r=<nonce>,s=<salt>,i=<count>` server-first message for these
credentials and a combined nonce. -/
def serverFirstOf (cred : StoredCredentials) (combinedNonce : String) : String :=
  Sasl.ServerFirstMessage.render
    { nonce := combinedNonce, salt := cred.saltB64, iterationCount := cred.iterationCount }

/-- Bytes from lowercase hex. `none` on an odd length or a non-hex
character, so a mistyped constant is a build error and not a silent
short key. -/
def bytesOfHex (s : String) : Option ByteArray :=
  let digit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - 48)
    else if c ≥ 'a' && c ≤ 'f' then some (c.toNat - 87)
    else none
  let rec go : List Char → List UInt8 → Option (List UInt8)
    | [], acc => some acc.reverse
    | [_], _ => none
    | a :: b :: rest, acc =>
      match digit a, digit b with
      | some x, some y => go rest (UInt8.ofNat (x * 16 + y) :: acc)
      | _, _ => none
  (go s.toList []).map (fun l => ByteArray.mk l.toArray)

/-! ## RFC 7677 section 3, the published exchange

Username "user", password "pencil", salt `W22ZaJ0SNY7soEsUEjb6gQ==`,
i=4096.

The stored keys are written here as literal constants rather than
derived by `credentialsOfPassword` in the check itself. Reason, measured
2026-09-07: one 4096-iteration `pbkdf2Sha256` in the Lean INTERPRETER
takes about seventy seconds, so deriving them at elaboration time cost
352 seconds of `lake build` for this one module. The constants are not
self-produced — they come from CPython's `hashlib.pbkdf2_hmac` and
`hmac`, an independent implementation, and the guards below then
reproduce the ClientProof and ServerSignature that RFC 7677 section 3
PUBLISHES from them. A wrong constant therefore fails the build; it
cannot silently agree with itself.

The derivation path itself (`credentialsOfPassword` at 4096 iterations)
is exercised at RUNTIME instead, by the live SCRAM-SHA-256 login in
`tests/xmpp/server.mjs`, where it runs compiled rather than
interpreted. -/

private def rfc7677Salt : String := "W22ZaJ0SNY7soEsUEjb6gQ=="
private def rfc7677Nonce : String :=
  "rOprNGfwEbeRWgbNEkqO%hvYDpWUa2RaTCAfuxFIlj)hNlF$k0"

private def rfc7677Cred : Option StoredCredentials :=
  match bytesOfHex "586e5df283e6dceb5c3e791d8b8528ec191e664045ce971792e2e6b5bb13e2a6",
        bytesOfHex "c1f3cbc1c13a9d35a14c0990eed97629ea225863e566a4314ab99f3f00e5d9d5" with
  | some stored, some server =>
    some { saltB64 := rfc7677Salt, iterationCount := 4096
           storedKey := stored, serverKey := server }
  | _, _ => none

private def rfc7677Auth : String :=
  authMessage "n=user,r=rOprNGfwEbeRWgbNEkqO"
    ("r=" ++ rfc7677Nonce ++ ",s=" ++ rfc7677Salt ++ ",i=4096")
    ("c=biws,r=" ++ rfc7677Nonce)

-- The published server-first message is reproduced from the credentials.
#guard (rfc7677Cred.map (fun c => serverFirstOf c rfc7677Nonce))
  == some ("r=" ++ rfc7677Nonce ++ ",s=W22ZaJ0SNY7soEsUEjb6gQ==,i=4096")

-- The ClientProof RFC 7677 section 3 publishes verifies against the
-- stored key, and yields the ServerSignature the same section
-- publishes. One line pins HMAC, SHA-256, the XOR recovery, base64 both
-- ways and the AuthMessage assembly.
#guard (rfc7677Cred.bind (fun c =>
    verifyClientProof c rfc7677Auth "dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="))
  == some "6rriTRBi23WpRR/wtup+mMhUZUn/dB5nLTJRsjl95G4="

-- A proof that is one base64 character different is REFUSED. A verifier
-- that accepted everything would pass the line above too.
#guard (rfc7677Cred.bind (fun c =>
    verifyClientProof c rfc7677Auth "eHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="))
  == none

-- The right proof against the WRONG AuthMessage is refused: replaying a
-- proof under a different nonce does not authenticate.
#guard (rfc7677Cred.bind (fun c =>
    verifyClientProof c (rfc7677Auth ++ "x") "dHzbZapWIk4jUhN+Ute9ytag9zjfMHgsqmmiz7AndVQ="))
  == none

-- Text that is not base64 at all is refused rather than treated as an
-- empty proof.
#guard (rfc7677Cred.bind (fun c => verifyClientProof c rfc7677Auth "not base64!"))
  == none

-- A proof of the right shape but the wrong LENGTH is refused.
#guard (rfc7677Cred.bind (fun c => verifyClientProof c rfc7677Auth "AAAA")) == none

-- `credentialsOfPassword` refuses a zero iteration count and a salt that
-- is not base64, rather than deriving a weak key. Both are cheap: the
-- refusal happens before PBKDF2 runs.
#guard (credentialsOfPassword "pencil" rfc7677Salt 0).isNone
#guard (credentialsOfPassword "pencil" "not base64!" 4096).isNone

-- Round-trips of the base64 pair actually used above.
#guard b64Encode "Client Key".toUTF8 == "Q2xpZW50IEtleQ=="
#guard (b64Decode "Q2xpZW50IEtleQ==").map (·.toList) == some "Client Key".toUTF8.toList

end L4Factoidal.XMPP.Scram
