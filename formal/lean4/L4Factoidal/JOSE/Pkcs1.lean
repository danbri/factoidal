/-
L4Factoidal.JOSE.Pkcs1 — EMSA-PKCS1-v1_5 with SHA-256 (RFC 8017 §9.2)
and RSASSA-PKCS1-v1_5 verification (RFC 8017 §8.2.2) as JWS `RS256`
(RFC 7518 §3.3) uses them.

## The forgery class this module excludes by construction

RFC 8017 §8.2.2 note 2 says a verifier MAY be implemented either by
comparing the recovered encoded message with a freshly generated one, or
by PARSING the recovered message and comparing the digest. It records
that the first is "the preferred". The second is where the
Bleichenbacher 2006 forgery lives, and where it has kept living: an
implementation that walks `00 01 FF…FF 00`, reads a DigestInfo, and then
stops without checking that the DigestInfo ran to the end of the block
will accept a signature in which the attacker chose the trailing bytes.
With a small public exponent the attacker can then produce a valid-looking
signature with no private key at all. The 2019 and 2021 repetitions in
other libraries were the same mistake made again.

This module implements only the first option, and there is no code path
that could implement the second:

  * `emsaEncode` GENERATES the whole `k`-byte block. It never reads one.
  * `rs256Verify` compares the recovered block with that block for FULL
    LENGTH byte equality. There is no offset, no skip, no scan, and no
    early exit.
  * `rs256Verify_iff_template` states that as a theorem: verification
    returns `true` exactly when the public operation produced a block and
    that block equals the generated template. The equivalence is stated
    in both directions, so no other accepting path can be added later
    without the theorem failing.

There is no PKCS#1 parser anywhere in this project.

## Where the pieces come from

The RSA public operation `s^e mod n` (RFC 8017 §5.2.2, RSAVP1) is
HACL*'s and is passed in as a PARAMETER, so every theorem below holds
whatever it returns and none of them depends on an opaque. The executable
edge passes `L4Factoidal.Crypto.Rsa.rsaPublicOp`; the `#guard`s below
pass a stub, which is how they can run in the Lean interpreter at all.
The digest is `L4Factoidal.Crypto.sha256`, the pure Lean SHA-256 with the
FIPS 180-4 vectors as build-time `#guard`s.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.JOSE.Pkcs1

open L4Factoidal.Crypto

/-! ## The DigestInfo for SHA-256 -/

/-- The DER encoding of `DigestInfo` with `algorithm = id-sha256` and an
absent-parameters `NULL`, from RFC 8017 §9.2 note 1, MINUS the 32-byte
digest that follows it. Nineteen bytes:

```
30 31            SEQUENCE, 49 bytes
   30 0d         SEQUENCE, 13 bytes  (AlgorithmIdentifier)
      06 09 60 86 48 01 65 03 04 02 01   OID 2.16.840.1.101.3.4.2.1
      05 00                              NULL
   04 20         OCTET STRING, 32 bytes  (the digest follows)
```

This is a CONSTANT, not a template a parser fills in. RFC 8017 §9.2 note
1 permits only this exact encoding for SHA-256; an implementation that
accepts a re-encoded equivalent (a different length form, absent
parameters instead of `NULL`) accepts more blocks than the specification
defines, which is the same leniency in a different place. -/
def sha256DigestInfo : List UInt8 :=
  [0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03,
   0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20]

#guard sha256DigestInfo.length == 19

/-- `tLen` of RFC 8017 §9.2: the DigestInfo plus the digest it announces.
51 bytes for SHA-256. -/
def tLen : Nat := 51

#guard tLen == sha256DigestInfo.length + 32

/-- The smallest modulus size EMSA-PKCS1-v1_5 with SHA-256 can encode
into. RFC 8017 §9.2 step 3 refuses `emLen < tLen + 11`, which is the
requirement that the padding string `PS` is at least eight octets. Note
that RFC 7518 §3.3 sets a much higher floor for `RS256` — 2048 bits, 256
octets — which `Crypto/RsaNative.lean` enforces; this constant is the
encoding's own limit. -/
def minEmLen : Nat := tLen + 11

#guard minEmLen == 62

/-! ## EMSA-PKCS1-v1_5 -/

/-- RFC 8017 §9.2 `EMSA-PKCS1-V1_5-ENCODE(M, emLen)`, with the digest
supplied rather than computed, so the caller chooses the hash
implementation.

`EM = 0x00 || 0x01 || PS || 0x00 || T`, where `T` is the DigestInfo
followed by the digest and `PS` is `emLen - tLen - 3` octets of `0xFF`.
The total is `2 + (k - 54) + 1 + 19 + 32 = k`.

`none` when the digest is not 32 octets (it is not a SHA-256 digest) or
when `k < 62` ("intended encoded message length too short", RFC 8017
§9.2 step 3). -/
def emsaEncodeList (h : List UInt8) (k : Nat) : Option (List UInt8) :=
  if h.length = 32 ∧ minEmLen ≤ k then
    some ((0x00 :: 0x01 :: List.replicate (k - 54) 0xFF) ++ ((0x00 :: sha256DigestInfo) ++ h))
  else none

/-- `emsaEncodeList` on `ByteArray`s. -/
def emsaEncode (h : ByteArray) (k : Nat) : Option ByteArray :=
  (emsaEncodeList h.data.toList k).map fun bs => ⟨bs.toArray⟩

/-! ## Theorems about the encoding

Each states an offset that a wrong constant would break. Together they
pin the whole block: length `k`, the two-octet prefix, the `0xFF` run of
the right length at the right place, and the `0x00 || DigestInfo ||
digest` tail. -/

/-- The encoded message is exactly `k` octets — the modulus length. A
block of any other length could not be compared to the public
operation's output at all. -/
theorem emsaEncode_length {h : List UInt8} {k : Nat} {em : List UInt8}
    (hem : emsaEncodeList h k = some em) : em.length = k := by
  unfold emsaEncodeList at hem
  split at hem
  · next hc =>
      obtain ⟨hh, hk⟩ := hc
      cases hem
      simp [List.length_append, List.length_replicate, hh, sha256DigestInfo]
      unfold minEmLen tLen at hk
      omega
  · simp at hem

/-- The block begins `00 01` (RFC 8017 §9.2). The leading zero octet is
what keeps `EM` numerically below the modulus. -/
theorem emsaEncode_prefix {h : List UInt8} {k : Nat} {em : List UInt8}
    (hem : emsaEncodeList h k = some em) : em.take 2 = [0x00, 0x01] := by
  unfold emsaEncodeList at hem
  split at hem
  · cases hem; simp
  · simp at hem

/-- The padding string is `k - 54` octets of `0xFF`, starting immediately
after the two-octet prefix. -/
theorem emsaEncode_padding {h : List UInt8} {k : Nat} {em : List UInt8}
    (hem : emsaEncodeList h k = some em) :
    (em.drop 2).take (k - 54) = List.replicate (k - 54) 0xFF := by
  unfold emsaEncodeList at hem
  split at hem
  · cases hem
    simp
  · simp at hem

/-- RFC 8017 §9.2 step 3: the padding string is at least eight octets.
A shorter one leaves room for a forger to place chosen bytes. -/
theorem emsaEncode_padding_min {h : List UInt8} {k : Nat} {em : List UInt8}
    (hem : emsaEncodeList h k = some em) : 8 ≤ k - 54 := by
  unfold emsaEncodeList at hem
  split at hem
  · next hc => obtain ⟨_, hk⟩ := hc; unfold minEmLen tLen at hk; omega
  · simp at hem

/-- Everything after the padding is the separator `0x00`, then the
SHA-256 DigestInfo, then the digest — and nothing else, because
`emsaEncode_length` fixes the total. There is no room after the digest
for the trailing bytes a Bleichenbacher forgery needs. -/
theorem emsaEncode_tail {h : List UInt8} {k : Nat} {em : List UInt8}
    (hem : emsaEncodeList h k = some em) :
    em.drop (k - 52) = (0x00 :: sha256DigestInfo) ++ h := by
  unfold emsaEncodeList at hem
  split at hem
  · next hc =>
      obtain ⟨_, hk⟩ := hc
      cases hem
      unfold minEmLen tLen at hk
      have hk2 : k - 52 = (k - 54) + 2 := by omega
      have hlen : ((0x00 : UInt8) :: 0x01 :: List.replicate (k - 54) (0xFF : UInt8)).length
          = k - 54 + 2 := by simp
      rw [hk2]
      exact List.drop_left' hlen
  · simp at hem

/-- Distinct digests give distinct encoded messages, at one modulus size.
This is what makes a signature over one message useless for another: the
block a forger must reach is a function of the digest alone. -/
theorem emsaEncode_injective {h h' : List UInt8} {k : Nat} {em : List UInt8}
    (hem : emsaEncodeList h k = some em) (hem' : emsaEncodeList h' k = some em) :
    h = h' := by
  unfold emsaEncodeList at hem hem'
  split at hem
  · next hc =>
      obtain ⟨hh, hk⟩ := hc
      split at hem'
      · next hc' =>
          obtain ⟨hh', _⟩ := hc'
          cases hem
          have hEq := Option.some.inj hem'
          have h2 := List.append_cancel_left hEq
          have h3 := List.cons.inj h2
          exact (List.append_cancel_left h3.2).symm
      · simp at hem'
  · simp at hem

/-! ## RSASSA-PKCS1-v1_5 verification -/

/-- The type of the RSA public operation, RFC 8017 §5.2.2 RSAVP1:
`pubOp n e s` is `s^e mod n` as `n.size` big-endian octets, or `none`
when the operation is refused. It is a PARAMETER so that every theorem
here is independent of HACL*, and so the `#guard`s can run a stub. -/
abbrev PublicOp := ByteArray → ByteArray → ByteArray → Option ByteArray

/-- JWS `RS256` verification (RFC 7518 §3.3, over RFC 8017 §8.2.2), by
the RFC's preferred method: recover the encoded message with the public
operation, generate the expected block, compare all `k` octets.

`n`, `e` are the modulus and public exponent as big-endian octets; `sig`
is the JWS signature; `msg` is the JWS signing input, unhashed. -/
def rs256Verify (pubOp : PublicOp) (n e sig msg : ByteArray) : Bool :=
  match pubOp n e sig with
  | none => false
  | some em =>
      match emsaEncodeList (sha256 msg).data.toList n.size with
      | none => false
      | some tmpl => em.data.toList == tmpl

/-- **There is exactly one accepting path.** `rs256Verify` returns `true`
if and only if the public operation produced a block and that block is
octet-for-octet the generated EMSA-PKCS1-v1_5 template. No parse, no
prefix match, no suffix tolerance — those cannot be added without this
equivalence failing, which is the whole point of stating it in both
directions. The Bleichenbacher 2006 class is excluded by construction. -/
theorem rs256Verify_iff_template (pubOp : PublicOp) (n e sig msg : ByteArray) :
    rs256Verify pubOp n e sig msg = true ↔
      ∃ em tmpl, pubOp n e sig = some em ∧
        emsaEncodeList (sha256 msg).data.toList n.size = some tmpl ∧
        em.data.toList = tmpl := by
  unfold rs256Verify
  cases hp : pubOp n e sig with
  | none => simp
  | some em =>
      cases ht : emsaEncodeList (sha256 msg).data.toList n.size with
      | none => simp
      | some tmpl =>
          simp only [beq_iff_eq]
          constructor
          · intro h; exact ⟨em, tmpl, rfl, rfl, h⟩
          · rintro ⟨em', tmpl', he, htt, heq⟩
            cases he; cases htt; exact heq

/-- An accepted signature recovers a block of exactly the modulus length.
A public operation that returned a shorter or longer block can never be
accepted, whatever it contains. -/
theorem rs256Verify_recovers_full_length {pubOp : PublicOp} {n e sig msg : ByteArray}
    (h : rs256Verify pubOp n e sig msg = true) :
    ∃ em, pubOp n e sig = some em ∧ em.size = n.size := by
  obtain ⟨em, tmpl, hp, ht, heq⟩ := (rs256Verify_iff_template pubOp n e sig msg).mp h
  refine ⟨em, hp, ?_⟩
  have hl : em.data.toList.length = tmpl.length := by rw [heq]
  have hsz : em.data.toList.length = em.size := by rw [Array.length_toList]; rfl
  have := emsaEncode_length ht
  omega

/-- A verifier that never recovers anything accepts nothing. Stated
because "the public operation refused" must be a rejection, never a
degradation to acceptance. -/
theorem rs256Verify_refusal_rejects (pubOp : PublicOp) (n e sig msg : ByteArray)
    (h : pubOp n e sig = none) : rs256Verify pubOp n e sig msg = false := by
  simp [rs256Verify, h]

/-! ## Fixtures

The encoded-message layout is checked here against a block written out by
hand from RFC 8017 §9.2. The end-to-end `RS256` check against the RFC 7515
Appendix A.2 example needs the RSA public operation, which is an extern
and does not evaluate at compile time; it is a section of
`lake exe l4jose-probe`. -/

-- A 2048-bit modulus is 256 octets, so `PS` is 202 octets of `0xFF`.
#guard (emsaEncodeList (List.replicate 32 (0xAB : UInt8)) 256).map List.length == some 256

#guard (emsaEncodeList (List.replicate 32 (0xAB : UInt8)) 256).map (·.take 2)
        == some [0x00, 0x01]

#guard (emsaEncodeList (List.replicate 32 (0xAB : UInt8)) 256).map (fun em => (em.drop 2).take 202)
        == some (List.replicate 202 (0xFF : UInt8))

#guard (emsaEncodeList (List.replicate 32 (0xAB : UInt8)) 256).map (·.drop 204)
        == some ((0x00 :: sha256DigestInfo) ++ List.replicate 32 (0xAB : UInt8))

-- A 3072-bit and a 4096-bit modulus, to check the padding length tracks k.
#guard (emsaEncodeList (List.replicate 32 (0x01 : UInt8)) 384).map List.length == some 384
#guard (emsaEncodeList (List.replicate 32 (0x01 : UInt8)) 512).map List.length == some 512

-- Refusals: a digest that is not SHA-256-sized, and a modulus too short
-- for eight octets of padding (RFC 8017 §9.2 step 3).
#guard emsaEncodeList (List.replicate 20 (0x00 : UInt8)) 256 == none
#guard emsaEncodeList (List.replicate 48 (0x00 : UInt8)) 256 == none
#guard emsaEncodeList (List.replicate 32 (0x00 : UInt8)) 61 == none
#guard (emsaEncodeList (List.replicate 32 (0x00 : UInt8)) 62).isSome

-- The comparison is total-length. A stub public operation returning the
-- correct template is accepted; the same block with ONE trailing octet
-- changed, and the same block truncated, are both refused. This is the
-- Bleichenbacher shape, run as a test rather than only proved.
private def stubModulus : ByteArray := ⟨(List.replicate 256 (0xFF : UInt8)).toArray⟩
private def stubSig : ByteArray := ⟨#[0x00]⟩
private def stubExp : ByteArray := ⟨#[0x01, 0x00, 0x01]⟩
private def goodEm : List UInt8 :=
  (emsaEncodeList (sha256 "jose".toUTF8).data.toList 256).getD []

#guard rs256Verify (fun _ _ _ => some ⟨goodEm.toArray⟩)
        stubModulus stubExp stubSig "jose".toUTF8 == true
#guard rs256Verify (fun _ _ _ => some ⟨(goodEm.dropLast ++ [0x00]).toArray⟩)
        stubModulus stubExp stubSig "jose".toUTF8 == false
#guard rs256Verify (fun _ _ _ => some ⟨goodEm.dropLast.toArray⟩)
        stubModulus stubExp stubSig "jose".toUTF8 == false
#guard rs256Verify (fun _ _ _ => some ⟨(goodEm ++ [0x00]).toArray⟩)
        stubModulus stubExp stubSig "jose".toUTF8 == false
#guard rs256Verify (fun _ _ _ => none)
        stubModulus stubExp stubSig "jose".toUTF8 == false
-- The same recovered block against a different message is refused.
#guard rs256Verify (fun _ _ _ => some ⟨goodEm.toArray⟩)
        stubModulus stubExp stubSig "JOSE".toUTF8 == false

end L4Factoidal.JOSE.Pkcs1
