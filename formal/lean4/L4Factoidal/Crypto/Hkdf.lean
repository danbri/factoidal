/-
L4Factoidal.Crypto.Hkdf — HKDF-SHA-256 (RFC 5869) TWICE: once in pure
Lean over `Crypto.hmacSha256`, and once as `@[extern]` opaques over
HACL*'s `Hacl_HKDF.c` / `Hacl_HMAC.c`.

## Why both, and which one to call

The crypto policy prefers HACL* for the primitive, and HACL* is what
every RUNTIME path uses (`hkdfExtractHacl`, `hkdfExpandHacl`, and HPKE,
which calls HACL*'s HKDF internally in C without passing through Lean at
all). The pure Lean pair exists for two reasons the extern cannot serve:

  1. `#guard` runs in the Lean INTERPRETER, which cannot call an
     `@[extern]` symbol. The RFC 5869 Appendix A vectors below are
     BUILD-TIME checks precisely because they run against the pure
     definitions. Against the externs they could only be run-time probe
     checks, which is what `lake exe l4crypto-probe` additionally does.
  2. The wasm and interpreter surfaces evaluate Lean, so a derivation
     reached from a `#eval`, a proof, or an evaluator path needs a
     definition Lean can unfold.

HKDF is not a new primitive: RFC 5869 §2 defines extract as one HMAC
call and expand as a chain of HMAC calls over a counter. The primitive
under both is SHA-256. This is the same reading `Crypto/Hmac.lean`
records for HMAC and PBKDF2, under the same policy.

## The obligation this module carries

`hkdfExtract` MUST agree with `hkdfExtractHacl`, and `hkdfExpand` with
`hkdfExpandHacl`, on every input, and the pure `Crypto.hmacSha256` MUST
agree with HACL*'s `hmacSha256Hacl`. None of that can be proved here —
one side of each pair is opaque — so it is MEASURED: `lake exe
l4crypto-probe`, section `hmac-hkdf-differential`, runs the RFC 4231
HMAC vectors and the RFC 5869 Appendix A vectors through BOTH
implementations and compares them byte for byte, and runs the whole
Wycheproof `hkdf_sha256_test.json` corpus through both. The probe exits
non-zero on any mismatch, so the agreement is a gate rather than an
assumption. This is the arrangement `Crypto/SHA2Native.lean` already
documents for `sha256Hacl`.

## Trust statement

The `Hacl` functions are `opaque`: Lean knows their TYPE and nothing
about their VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT THEY COMPUTE.
`#print axioms` on every theorem of the library still reports only
`propext`, `Classical.choice`, `Quot.sound`.

Trusted: HKDF-SHA-256 and HMAC-SHA-256 as implemented by HACL*
(`third_party/hacl/src/Hacl_HKDF.c` and `Hacl_HMAC.c`, entry points
`Hacl_HKDF_extract_sha2_256`, `Hacl_HKDF_expand_sha2_256`,
`Hacl_HMAC_compute_sha2_256`), extracted by KaRaMeL from F*/Low* code
proved by Project Everest; vendored unmodified from
cryspen/hacl-packages commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2
(`third_party/hacl/PROVENANCE.md`). And `ffi/hacl_kdf.c`, which is
length checks and `lean_sarray` plumbing with no arithmetic.

What we do NOT check: that `salt` is what the protocol says it is, that
`info` binds the derivation to a context, or that `ikm` was ever secret.
RFC 5869 §3.1-3.3 leaves all three to the protocol.

## Contract

  * `hkdfExtract salt ikm` → the 32-byte PRK. An EMPTY `salt` is
    legitimate and means the all-zero salt of RFC 5869 §2.2, which is
    what the vectors of Appendix A.3 and A.6 exercise.
  * `hkdfExpand prk info len` → `len` bytes of output keying material.
    RFC 5869 §2.3 caps `len` at 255 * 32 = 8160 and requires
    `prk.size ≥ 32`; outside that the answer is the EMPTY `ByteArray`,
    which is a refusal and never keying material (`len = 0` is refused
    for the same reason: an empty derivation cannot be distinguished
    from a failed one).
-/
import L4Factoidal.Crypto.Hmac

namespace L4Factoidal.Crypto

/-! ## Pure Lean, RFC 5869 -/

/-- RFC 5869 §2.2. `PRK = HMAC-Hash(salt, IKM)`. An empty `salt` is the
all-zero salt of HashLen bytes; `hmacKey0` pads a short key with zeros to
the block size, and the zero-length key and the 32-zero-byte key give the
same padded block, so no special case is needed. -/
def hkdfExtract (salt ikm : ByteArray) : ByteArray :=
  hmacSha256 salt ikm

/-- The `T(i)` chain of RFC 5869 §2.3, accumulating `T(1) || T(2) || …`.
`prev` is `T(i-1)` (empty for `T(1)`) and `i` is the one-based counter.
Structural on `steps`, so no `partial def` and no fuel argument is
exposed. -/
def hkdfExpandChain (prk info : ByteArray) (prev : ByteArray) (i : Nat)
    (acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | steps + 1 =>
      let t := hmacSha256 prk (prev ++ info ++ ByteArray.mk #[UInt8.ofNat i])
      hkdfExpandChain prk info t (i + 1) (acc ++ t) steps

/-- RFC 5869 §2.3. `len` bytes of output keying material. The EMPTY
`ByteArray` is a refusal — `len = 0`, `len > 255 * HashLen`, or a PRK
shorter than HashLen — and is never keying material. -/
def hkdfExpand (prk info : ByteArray) (len : Nat) : ByteArray :=
  if prk.size < sha256DigestBytes then ByteArray.empty
  else if len = 0 ∨ len > 255 * sha256DigestBytes then ByteArray.empty
  else
    let blocks := (len + sha256DigestBytes - 1) / sha256DigestBytes
    (hkdfExpandChain prk info ByteArray.empty 1 ByteArray.empty blocks).extract 0 len

/-! ## HACL*, the runtime path -/

/-- HMAC-SHA-256 via HACL* `Hacl_HMAC_compute_sha2_256`. Extensionally
equal to the pure `Crypto.hmacSha256`; that equality is measured by
`l4crypto-probe`, not proved. EMPTY only if an input exceeds 2^32-1
bytes, which a 32-byte MAC can never be. -/
@[extern "l4_hacl_hmac_sha256"]
opaque hmacSha256Hacl (key : @& ByteArray) (msg : @& ByteArray) : ByteArray

/-- HKDF-SHA-256 extract via HACL* `Hacl_HKDF_extract_sha2_256`.
Extensionally equal to `hkdfExtract`; measured, not proved. -/
@[extern "l4_hacl_hkdf_extract_sha256"]
opaque hkdfExtractHacl (salt : @& ByteArray) (ikm : @& ByteArray) : ByteArray

/-- HKDF-SHA-256 expand via HACL* `Hacl_HKDF_expand_sha2_256`.
Extensionally equal to `hkdfExpand`; measured, not proved. Same refusal
rule: EMPTY for `len = 0`, `len > 8160`, or a PRK under 32 bytes. -/
@[extern "l4_hacl_hkdf_expand_sha256"]
opaque hkdfExpandHaclRaw (prk : @& ByteArray) (info : @& ByteArray)
    (len : USize) : ByteArray

/-- `hkdfExpandHaclRaw` with the `Nat` length the rest of the tree uses,
refusing a length no `USize` can carry. -/
def hkdfExpandHacl (prk info : ByteArray) (len : Nat) : ByteArray :=
  if len = 0 ∨ len > 255 * sha256DigestBytes then ByteArray.empty
  else hkdfExpandHaclRaw prk info (USize.ofNat len)

/-! ## RFC 5869 Appendix A test vectors

Build-time `#guard`s, which is possible because they run against the
PURE definitions. The HACL* twins are checked against the same vectors
at run time by `lake exe l4crypto-probe`. -/

private def hkdfHex (b : ByteArray) : String := bytesToHex b

private def hkdfBytesOfHex (s : String) : ByteArray :=
  let d : Char → Nat := fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - 48
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55
    else 0
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (d a * 16 + d b) :: go rest
    | _ => []
  ByteArray.mk (go s.toList).toArray

-- Appendix A.1, basic test case with SHA-256.
private def a1Ikm : ByteArray := hkdfBytesOfHex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b"
private def a1Salt : ByteArray := hkdfBytesOfHex "000102030405060708090a0b0c"
private def a1Info : ByteArray := hkdfBytesOfHex "f0f1f2f3f4f5f6f7f8f9"

#guard hkdfHex (hkdfExtract a1Salt a1Ikm)
  == "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"

#guard hkdfHex (hkdfExpand (hkdfExtract a1Salt a1Ikm) a1Info 42)
  == ("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf" ++
      "34007208d5b887185865")

-- Appendix A.2, test with SHA-256 and longer inputs and outputs.
private def a2Ikm : ByteArray := hkdfBytesOfHex
  ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f" ++
   "202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f" ++
   "404142434445464748494a4b4c4d4e4f")
private def a2Salt : ByteArray := hkdfBytesOfHex
  ("606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f" ++
   "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f" ++
   "a0a1a2a3a4a5a6a7a8a9aaabacadaeaf")
private def a2Info : ByteArray := hkdfBytesOfHex
  ("b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecf" ++
   "d0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeef" ++
   "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff")

#guard hkdfHex (hkdfExtract a2Salt a2Ikm)
  == "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244"

#guard hkdfHex (hkdfExpand (hkdfExtract a2Salt a2Ikm) a2Info 82)
  == ("b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c" ++
      "59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71" ++
      "cc30c58179ec3e87c14c01d5c1f3434f1d87")

-- Appendix A.3, test with SHA-256 and zero-length salt and info.
#guard hkdfHex (hkdfExtract ByteArray.empty a1Ikm)
  == "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04"

#guard hkdfHex (hkdfExpand (hkdfExtract ByteArray.empty a1Ikm) ByteArray.empty 42)
  == ("8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d" ++
      "9d201395faa4b61a96c8")

-- A length outside RFC 5869 section 2.3 is a REFUSAL, never keying
-- material. Checked so a future edit cannot quietly start returning a
-- short buffer instead.
#guard (hkdfExpand (hkdfExtract a1Salt a1Ikm) a1Info 0).size == 0
#guard (hkdfExpand (hkdfExtract a1Salt a1Ikm) a1Info 8161).size == 0
#guard (hkdfExpand (hkdfBytesOfHex "00112233") a1Info 32).size == 0
#guard (hkdfExpand (hkdfExtract a1Salt a1Ikm) a1Info 8160).size == 8160

end L4Factoidal.Crypto
