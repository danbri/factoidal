/-
L4Factoidal.Crypto.SHA2Theorems — cheap, kernel-checked facts about
`SHA2.lean`: digest lengths and the padding-length invariant.

No `sorry`, no `axiom`, no `native_decide` — every proof below is
`rfl`/`simp`/`omega`/plain induction, per the Lean tree's proof policy
(`skills/factoidal-lean-basics/SKILL.md`).

Proof strategy (see `SHA2.lean`'s module header for the design that
makes this tractable): the digest-length theorems do NOT reason about
either internal loop (message schedule / round function) or about the
hash's arithmetic at all. They only unfold the FINAL serialisation —
a straight-line, statically-fixed-count chain of `appendWord32BE`/
`appendWord64BE` calls — so `ByteArray.size_push`'s `@[simp]` lemma
(from Lean core) closes them regardless of what value each word
actually is.

The padding-length invariant (`pad256_size`/`pad512_size`) is real
arithmetic: `pushN_size` is proved by structural induction on the
count, and the two padding functions' size then reduces to a linear
Nat fact `omega` discharges after case-splitting on the `if` that
picks the zero-fill count `k`.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Crypto

/-! ## `pushN` — size is exactly the count pushed, independent of the
byte VALUES `f` produces. -/

theorem pushN_size (acc : ByteArray) (n : Nat) (f : Nat → UInt8) :
    (pushN acc n f).size = acc.size + n := by
  induction n generalizing acc with
  | zero => simp [pushN]
  | succ k ih => simp only [pushN, ByteArray.size_push, ih]; omega

/-! ## §5.1.1/§5.1.2 padding-length invariant

The padded message is always an exact multiple of the block size —
this is what makes `processBlocks256`/`processBlocks512`'s fuel
(`padded.size / blockSize`) an EXACT block count rather than a rounded
guess, which is what the module header's "Nat-fuel-by-block-count"
totality argument for the outer loop depends on. -/

theorem pad256_size (m : ByteArray) : (pad256 m).size % 64 = 0 := by
  unfold pad256
  simp only [pushN_size, ByteArray.size_push]
  split <;> omega

theorem pad512_size (m : ByteArray) : (pad512 m).size % 128 = 0 := by
  unfold pad512
  simp only [pushN_size, ByteArray.size_push]
  split <;> omega

/-! ## Digest lengths (FIPS 180-4 §1: SHA-256 → 32 bytes, SHA-384 → 48
bytes, SHA-512 → 64 bytes). Each proof unfolds the top-level `def` and
the fixed-count `appendWord32BE`/`appendWord64BE` chain; `simp` closes
the resulting arithmetic with core's `ByteArray.size_push` /
`ByteArray.size_empty` simp set. No fact about `pad256`/`pad512`/
`processBlocks256`/`processBlocks512`'s actual VALUES is needed. -/

theorem sha256_size (m : ByteArray) : (sha256 m).size = 32 := by
  simp [sha256, appendWord32BE]

theorem sha512_size (m : ByteArray) : (sha512 m).size = 64 := by
  simp [sha512, appendWord64BE]

theorem sha384_size (m : ByteArray) : (sha384 m).size = 48 := by
  simp [sha384, appendWord64BE]

/-! ## Axiom audit — kept in the build log, matching `Tests.lean`'s
convention for the RDF/SPARQL side. Expected: exactly Lean's own
foundations, no `sorryAx`, nothing user-declared. -/

#print axioms pushN_size
#print axioms pad256_size
#print axioms pad512_size
#print axioms sha256_size
#print axioms sha384_size
#print axioms sha512_size

end L4Factoidal.Crypto
