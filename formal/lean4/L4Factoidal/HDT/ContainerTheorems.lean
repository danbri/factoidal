/-
L4Factoidal.HDT.ContainerTheorems — corruption is refused, not
reinterpreted.

Port of the two lemmas at the end of `HDT.Container.fst`
(`lemma_parse_control_info_rejects_bad_cookie`,
`lemma_bad_global_cookie_rejects_container`).

`HDT.Container` is a READER, so the writer/reader round-trip property
that applies to companion-file modules (Parquet.Footer's
`lemma_version_field_roundtrip`) has nothing to say here. The property
its consumers rely on is that a corrupted container is REFUSED rather
than accepted as some other structure. `parseControlInfo` tests the
four `$HDT` cookie bytes before it decodes anything else, and
`parseInventory` makes that test the first thing it does, so both
lemmas hold by unfolding.
-/
import L4Factoidal.HDT.Container

namespace L4Factoidal.HDT

/-- A control-information block whose leading four bytes are not
    exactly `$`, `H`, `D`, `T` (0x24 0x48 0x44 0x54) is rejected
    outright: `parseControlInfo` never goes on to decode a format,
    properties or CRC out of a mis-cookied block. -/
theorem parseControlInfo_rejects_bad_cookie
    (a : Bytes) (pos : Nat) (b0 b1 b2 b3 : Nat)
    (h0 : byteNat a pos = some b0)
    (h1 : byteNat a (pos + 1) = some b1)
    (h2 : byteNat a (pos + 2) = some b2)
    (h3 : byteNat a (pos + 3) = some b3)
    (hbad : ¬(b0 = 0x24 ∧ b1 = 0x48 ∧ b2 = 0x44 ∧ b3 = 0x54)) :
    parseControlInfo a pos = none := by
  unfold parseControlInfo
  simp [h0, h1, h2, h3]
  intro e0 e1 e2 e3
  exact absurd ⟨e0, e1, e2, e3⟩ hbad

/-- The corollary at the entry point every consumer actually calls: a
    corrupted Global cookie at file offset 0 fails the WHOLE inventory
    parse, not just the Global block on its own. `parseInventory`
    forwards `parseControlInfo a 0`'s `none` verbatim, so it can never
    go on to decode a header, dictionary or triples section out of a
    file that does not open with a valid HDT container. -/
theorem badGlobalCookie_rejects_container
    (a : Bytes) (b0 b1 b2 b3 : Nat)
    (h0 : byteNat a 0 = some b0)
    (h1 : byteNat a 1 = some b1)
    (h2 : byteNat a 2 = some b2)
    (h3 : byteNat a 3 = some b3)
    (hbad : ¬(b0 = 0x24 ∧ b1 = 0x48 ∧ b2 = 0x44 ∧ b3 = 0x54)) :
    parseInventory a = none := by
  have h := parseControlInfo_rejects_bad_cookie a 0 b0 b1 b2 b3 h0 h1 h2 h3 hbad
  unfold parseInventory
  simp [h]

/-! Axiom audit: the two theorems must rest on nothing beyond Lean's
    own three. No `sorry`, no `axiom`, no `native_decide` — the policy
    in `skills/factoidal-lean-basics/SKILL.md`. -/

#print axioms parseControlInfo_rejects_bad_cookie
#print axioms badGlobalCookie_rejects_container

end L4Factoidal.HDT
