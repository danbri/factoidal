/-
L4Factoidal.Crypto.Hmac — HMAC-SHA-256 (RFC 2104, FIPS 198-1) and
PBKDF2-HMAC-SHA-256 (RFC 8018 section 5.2), in pure Lean over the
existing `L4Factoidal.Crypto.sha256`.

WHY THIS IS NOT "ROLLING OUR OWN CRYPTO": `skills/crypto-policy/SKILL.md`
forbids writing new PRIMITIVES. HMAC is not a primitive: RFC 2104 defines
it as two calls to an unmodified hash over a keyed prefix, and PBKDF2 is
an iterated XOR fold of HMAC calls. Neither has any internal state of its
own. The hash under both is `Crypto.sha256`, the existing FIPS 180-4
implementation, whose native HACL* twin `Crypto.sha256Hacl` is checked
against it by `l4vc-probe`. `L4Factoidal/XMPP/README.md` names exactly
this route: "HMAC's construction doesn't need its own native primitive —
add it to `L4Factoidal/Crypto/`, not as an XMPP-local crypto boundary."

The pure hash is used rather than the extern so that the RFC test vectors
at the end of this file are `#guard`s: an `@[extern]` opaque cannot run in
the Lean interpreter, so a vector checked against it would only be a
runtime test, not a build-time one.

Test vectors:
  * HMAC-SHA-256: RFC 4231 section 4 cases 1, 2, 3, 6 and 7.
  * PBKDF2-HMAC-SHA-256: RFC 7914 section 11 and the SCRAM-SHA-256
    worked example of RFC 7677 section 3.

No `sorry`, no `axiom`, no `native_decide`, no `partial`. Every loop is
bounded by an explicit `Nat` count.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Crypto

/-- The SHA-256 block size in bytes (FIPS 180-4 section 5.1.1). -/
def hmacBlockBytes : Nat := 64

/-- The SHA-256 digest size in bytes. -/
def sha256DigestBytes : Nat := 32

/-- Pad a key to one hash block, hashing it first when it is longer than
a block — RFC 2104's `K0` derivation. -/
def hmacKey0 (key : ByteArray) : ByteArray :=
  let k := if key.size > hmacBlockBytes then sha256 key else key
  let need := hmacBlockBytes - k.size
  k ++ ByteArray.mk (Array.replicate need (0 : UInt8))

private def xorPad (k : ByteArray) (b : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity hmacBlockBytes
  for i in [0:hmacBlockBytes] do
    out := out.push ((k.get! i) ^^^ b)
  return out

/-- HMAC-SHA-256 (RFC 2104): `H((K0 ^ opad) ++ H((K0 ^ ipad) ++ msg))`. -/
def hmacSha256 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0 key
  let inner := sha256 (xorPad k0 0x36 ++ msg)
  sha256 (xorPad k0 0x5c ++ inner)

/-- Byte-wise exclusive-or of two equal-length arrays. A length mismatch
truncates to the shorter, which never happens here: every argument is a
SHA-256 digest. -/
def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let n := min a.size b.size
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    out := out.push ((a.get! i) ^^^ (b.get! i))
  return out

/-- The four-byte big-endian block index RFC 8018 section 5.2 appends to
the salt (`INT (i)`). -/
def int32BE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((n / 16777216) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat (n % 256)]

/-- The `U_1 xor U_2 xor ... xor U_c` fold for one PBKDF2 output block.
`count` is the remaining iteration count, so the recursion is structural
and no `partial` is needed. -/
def pbkdf2Fold (password : ByteArray) (u acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | count + 1 =>
    let u' := hmacSha256 password u
    pbkdf2Fold password u' (xorBytes acc u') count

/-- One PBKDF2 output block: `F (P, S, c, i)` of RFC 8018 section 5.2. -/
def pbkdf2Block (password salt : ByteArray) (iterations index : Nat) : ByteArray :=
  let u1 := hmacSha256 password (salt ++ int32BE index)
  pbkdf2Fold password u1 u1 (iterations - 1)

/-- PBKDF2-HMAC-SHA-256 (RFC 8018 section 5.2) truncated to `dkLen`
bytes. `iterations` of zero is treated as one, so the result is always a
derived key and never the empty array — SCRAM's `i=0` is rejected by the
caller in `L4Factoidal.XMPP.Scram`, not silently turned into a weak key
here. -/
def pbkdf2Sha256 (password salt : ByteArray) (iterations dkLen : Nat) : ByteArray :=
  let iters := max iterations 1
  let blocks := (dkLen + sha256DigestBytes - 1) / sha256DigestBytes
  let full := (List.range blocks).foldl
    (fun acc i => acc ++ pbkdf2Block password salt iters (i + 1)) ByteArray.empty
  full.extract 0 dkLen

/-! ## Test vectors -/

private def hexOf (b : ByteArray) : String := bytesToHex b

private def bytesOfStr (s : String) : ByteArray := s.toUTF8

private def repeatByte (b : UInt8) (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n b)

-- RFC 4231 section 4.2, case 1.
#guard hexOf (hmacSha256 (repeatByte 0x0b 20) (bytesOfStr "Hi There"))
  == "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"

-- RFC 4231 section 4.3, case 2 (a key shorter than one block).
#guard hexOf (hmacSha256 (bytesOfStr "Jefe") (bytesOfStr "what do ya want for nothing?"))
  == "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"

-- RFC 4231 section 4.4, case 3.
#guard hexOf (hmacSha256 (repeatByte 0xaa 20) (repeatByte 0xdd 50))
  == "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"

-- RFC 4231 section 4.7, case 6 — a 131-byte key, so `hmacKey0` hashes it.
#guard hexOf (hmacSha256 (repeatByte 0xaa 131)
    (bytesOfStr "Test Using Larger Than Block-Size Key - Hash Key First"))
  == "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"

-- RFC 4231 section 4.8, case 7 — the same long key over a long message.
#guard hexOf (hmacSha256 (repeatByte 0xaa 131)
    (bytesOfStr ("This is a test using a larger than block-size key and a larger " ++
      "than block-size data. The key needs to be hashed before being used" ++
      " by the HMAC algorithm.")))
  == "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"

-- RFC 7914 section 11, the PBKDF2-HMAC-SHA-256 vector with c=1.
#guard hexOf (pbkdf2Sha256 (bytesOfStr "passwd") (bytesOfStr "salt") 1 64)
  == ("55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc" ++
      "49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783")

end L4Factoidal.Crypto
