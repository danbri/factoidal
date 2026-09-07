/-
Wasm.Ops.Crypto — the AEAD and HPKE ops surface, over
`L4Factoidal.Crypto.ChaChaPoly` and `L4Factoidal.Crypto.Hpke`.

Byte fields cross this ABI as LOWERCASE HEX, because the dispatch is a
JSON string in and a JSON string out and JSON has no byte type. The same
choice `Wasm.Ops.Support`'s `bytesOfHex?` / `hexOfBytes` already make
for every other byte-carrying op. An odd-length or non-hex field is an
error envelope, never a truncated buffer.

  aeadSeal({"alg":"chacha20-poly1305","key":hex32,"nonce":hex12,
            "aad":hex,"plaintext":hex})
    -> {"ok":true,"ciphertext":hex}
       `ciphertext` is `ciphertext || tag`, 16 bytes longer than the
       plaintext (RFC 8439 §2.8). The tag is NOT a separate member: this
       tree's calling convention appends it, and splitting it here would
       let a caller reassemble the two in the wrong order.

  aeadOpen({"alg":"chacha20-poly1305","key":hex32,"nonce":hex12,
            "aad":hex,"ciphertext":hex})
    -> {"ok":true,"plaintext":hex}
       An error envelope covers BOTH a length refusal and a tag that
       does not authenticate, and says which of those two it is only in
       the message text — never in a machine-readable member, because a
       caller must not branch on it.

  hpkeSeal({"skE":hex32,"pkR":hex32,"info":hex,"aad":hex,"plaintext":hex})
    -> {"ok":true,"message":hex,"enc":hex32,"ciphertext":hex}
       `message` is the whole `enc || ciphertext || tag` buffer, which is
       what `hpkeOpen` takes back; `enc` and `ciphertext` are the same
       bytes split for a caller that transmits them separately, as
       RFC 9180 §6.1 does.

  hpkeOpen({"skR":hex32,"info":hex,"aad":hex,"message":hex})
    -> {"ok":true,"plaintext":hex}

`alg` is required on the two AEAD ops and its ONLY accepted value is
`chacha20-poly1305`. It is required rather than defaulted so that adding
AES-GCM later (https://github.com/danbri/factoidal/issues/677) cannot
silently change what an existing caller gets; a caller naming
`aes-128-gcm` today receives an error envelope that names that issue.

`skE` on `hpkeSeal` is the EPHEMERAL private key and MUST be fresh
random bytes from the host's CSPRNG for every call. It is an argument,
not generated here, because this ABI has no entropy source and because
the RFC 9180 Appendix A.2 vectors have to be reproducible. A caller that
reuses one destroys the security of every message sealed under it.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Crypto.ChaChaPoly
import L4Factoidal.Crypto.Hpke

namespace L4Wasm.Ops

open L4Factoidal.JSON

/-- Read a required hex-encoded byte field. -/
private def hexField (j : Json) (key : String) : Except String ByteArray :=
  match j.getString? key with
  | none => .error s!"missing string member \"{key}\""
  | some s =>
      match bytesOfHex? s with
      | none => .error s!"member \"{key}\" is not lowercase hex of whole bytes"
      | some b => .ok b

/-- Read an optional hex field, defaulting to the empty byte string.
`aad` and `info` are legitimately empty in RFC 8439 and RFC 9180. -/
private def hexFieldOpt (j : Json) (key : String) : Except String ByteArray :=
  match j.getString? key with
  | none => .ok ByteArray.empty
  | some s =>
      match bytesOfHex? s with
      | none => .error s!"member \"{key}\" is not lowercase hex of whole bytes"
      | some b => .ok b

/-- The AEAD algorithm name. Only one is implemented. -/
private def checkAlg (j : Json) : Except String Unit :=
  match j.getString? "alg" with
  | none => .error "missing string member \"alg\"; the only value is \"chacha20-poly1305\""
  | some "chacha20-poly1305" => .ok ()
  | some "aes-128-gcm" | some "aes-256-gcm" =>
      .error ("AES-GCM is not implemented: the pinned HACL* release has no portable " ++
        "AES-GCM. See https://github.com/danbri/factoidal/issues/677")
  | some a => .error s!"unknown alg \"{a}\"; the only value is \"chacha20-poly1305\""

/-- `aeadSeal({"alg":…,"key":…,"nonce":…,"aad":…,"plaintext":…})`. -/
def aeadSeal (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do
        checkAlg j
        let key ← hexField j "key"
        let nonce ← hexField j "nonce"
        let aad ← hexFieldOpt j "aad"
        let pt ← hexFieldOpt j "plaintext"
        match L4Factoidal.Crypto.ChaChaPoly.aeadSeal key nonce aad pt with
        | none =>
            .error s!"seal refused: key must be 32 bytes (got {key.size}) and nonce 12 (got {nonce.size})"
        | some ct => .ok ct : Except String ByteArray) with
      | .error e => errJson e
      | .ok ct => okWith [("ciphertext", .string (hexOfBytes ct))]

/-- `aeadOpen({"alg":…,"key":…,"nonce":…,"aad":…,"ciphertext":…})`. -/
def aeadOpen (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do
        checkAlg j
        let key ← hexField j "key"
        let nonce ← hexField j "nonce"
        let aad ← hexFieldOpt j "aad"
        let ct ← hexField j "ciphertext"
        match L4Factoidal.Crypto.ChaChaPoly.open? key nonce aad ct with
        | none =>
            .error ("open refused: either a length refusal (key 32, nonce 12, " ++
              "ciphertext at least 16) or the Poly1305 tag did not authenticate")
        | some pt => .ok pt : Except String ByteArray) with
      | .error e => errJson e
      | .ok pt => okWith [("plaintext", .string (hexOfBytes pt))]

/-- `hpkeSeal({"skE":…,"pkR":…,"info":…,"aad":…,"plaintext":…})`. Base
mode, single shot, DHKEM(X25519, HKDF-SHA256) / HKDF-SHA256 /
ChaCha20-Poly1305 — RFC 9180 §6.1 with the Appendix A.2 ciphersuite. -/
def hpkeSeal (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do
        let skE ← hexField j "skE"
        let pkR ← hexField j "pkR"
        let info ← hexFieldOpt j "info"
        let aad ← hexFieldOpt j "aad"
        let pt ← hexFieldOpt j "plaintext"
        match L4Factoidal.Crypto.Hpke.sealBase skE pkR info aad pt with
        | none =>
            .error ("hpkeSeal refused: skE and pkR must be 32 bytes " ++
              s!"(got {skE.size} and {pkR.size}), and pkR must be a valid X25519 public key")
        | some m => .ok m : Except String ByteArray) with
      | .error e => errJson e
      | .ok m =>
          let enc := (L4Factoidal.Crypto.Hpke.encOf? m).getD ByteArray.empty
          let ct := (L4Factoidal.Crypto.Hpke.ciphertextOf? m).getD ByteArray.empty
          okWith [("message", .string (hexOfBytes m)),
                  ("enc", .string (hexOfBytes enc)),
                  ("ciphertext", .string (hexOfBytes ct))]

/-- `hpkeOpen({"skR":…,"info":…,"aad":…,"message":…})`, over the buffer
`hpkeSeal` produced. -/
def hpkeOpen (argJson : String) : String :=
  match parseJson argJson with
  | .error e => errJson s!"argJson: {toString e}"
  | .ok j =>
      match (do
        let skR ← hexField j "skR"
        let info ← hexFieldOpt j "info"
        let aad ← hexFieldOpt j "aad"
        let m ← hexField j "message"
        match L4Factoidal.Crypto.Hpke.openBase? skR info aad m with
        | none =>
            .error ("hpkeOpen refused: either a length refusal (skR 32, message at " ++
              "least 48) or the ChaCha20-Poly1305 tag did not authenticate")
        | some pt => .ok pt : Except String ByteArray) with
      | .error e => errJson e
      | .ok pt => okWith [("plaintext", .string (hexOfBytes pt))]

end L4Wasm.Ops
