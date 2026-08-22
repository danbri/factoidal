/-
L4Factoidal.VC.Theorems — what the VC Data Integrity stage proves.

  1. base58btc is injective on its image: `base58Decode?_base58Encode`
     — the lemma `VC.Multibase.fst`'s banner declines to state ("a
     disproportionate proof burden"). With it, `multibaseDecode?_encode`
     and `parseDidKey_didKeyOfPublicKey` (a 32-byte public key survives
     the trip through `did:key:z6Mk…`).
  2. The hash input is a function of the canonical forms only:
     `hashData_congr` / `verifyProofValue_of_canonical_eq` — two
     datasets with the same RDFC-1.0 canonical N-Quads yield the same
     hash data and the same verdict, whatever their blank-node labels or
     quad order.
  3. Verification is deterministic and total: `verifyFromCanonical` is a
     plain function (no state, no `IO`), so "the same inputs give the
     same verdict" is definitional; the contentful statements are the
     refusals — `verifyFromCanonical_not_multibase` (a proofValue that is
     not multibase-z is rejected before any primitive is consulted) and
     `verifyDocument_noProof`.
  4. Create-then-verify: `verifyFromCanonical_createFromCanonical` —
     under the single hypothesis that the primitive accepts its own
     signatures (`verifyF pk m (signF sk m) = true`), a proof created
     over canonical forms verifies over the same forms. The hypothesis
     is exactly what HACL* promises and this tree does not prove; it is
     a premise here, not an axiom anywhere.

`#print axioms` at the bottom: every theorem reports only `propext`,
`Classical.choice`, `Quot.sound`. The `@[extern]` opaques of
`Crypto/Ed25519.lean` are not mentioned by any theorem.
-/
import L4Factoidal.VC.DataIntegrity

namespace L4Factoidal.VC.Multibase

/-! ## Digits: nat → base-58 digits → nat -/

theorem digitsToNat58_append (acc : Nat) (xs ys : List Nat) :
    digitsToNat58 acc (xs ++ ys) = digitsToNat58 (digitsToNat58 acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons d ds ih => simp [digitsToNat58, ih]

theorem natToDigits58_zero : natToDigits58 0 = [] := by
  unfold natToDigits58; simp

theorem natToDigits58_pos (n : Nat) (h : n ≠ 0) :
    natToDigits58 n = natToDigits58 (n / 58) ++ [n % 58] := by
  conv => lhs; unfold natToDigits58
  simp [h]

theorem digitsToNat58_natToDigits58 (n : Nat) :
    digitsToNat58 0 (natToDigits58 n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; simp [natToDigits58_zero, digitsToNat58]
    · rw [natToDigits58_pos n h, digitsToNat58_append,
          ih (n / 58) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))]
      simp [digitsToNat58]
      exact Nat.div_add_mod' n 58

/-- Every digit is below 58. -/
theorem natToDigits58_lt (n : Nat) : ∀ d ∈ natToDigits58 n, d < 58 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n = 0
    · subst h; simp [natToDigits58_zero]
    · rw [natToDigits58_pos n h]
      intro d hd
      rw [List.mem_append] at hd
      rcases hd with hd | hd
      · exact ih (n / 58) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)) d hd
      · simp at hd; subst hd; exact Nat.mod_lt n (by decide)

/-- The leading digit of a non-zero number is non-zero. -/
theorem natToDigits58_head_ne_zero (n : Nat) (h : n ≠ 0) :
    ∃ d ds, natToDigits58 n = d :: ds ∧ d ≠ 0 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natToDigits58_pos n h]
    by_cases hq : n / 58 = 0
    · rw [hq, natToDigits58_zero]
      refine ⟨n % 58, [], rfl, ?_⟩
      intro hm
      have := Nat.div_add_mod' n 58
      rw [hq, hm] at this
      exact h this.symm
    · obtain ⟨d, ds, hds, hd⟩ := ih (n / 58) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)) hq
      exact ⟨d, ds ++ [n % 58], by rw [hds]; rfl, hd⟩

/-! ## Characters: the two alphabet facts, by evaluation -/

theorem base58Digit?_base58Char : ∀ d, d < 58 → base58Digit? (base58Char d) = some d := by
  decide

theorem base58Char_ne_one : ∀ d, d < 58 → d ≠ 0 → base58Char d ≠ '1' := by
  decide

theorem digitsOfChars_map (ds : List Nat) (h : ∀ d ∈ ds, d < 58) :
    digitsOfChars (ds.map base58Char) = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd : d < 58 := h d (List.mem_cons_self ..)
    have hds : ∀ x ∈ ds, x < 58 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp [digitsOfChars, base58Digit?_base58Char d hd, ih hds]

/-! ## Bytes: nat → big-endian bytes → nat -/

theorem natToBytesBE_zero : natToBytesBE 0 = [] := by
  unfold natToBytesBE; simp

theorem natToBytesBE_pos (n : Nat) (h : n ≠ 0) :
    natToBytesBE n = natToBytesBE (n / 256) ++ [UInt8.ofNat (n % 256)] := by
  conv => lhs; unfold natToBytesBE
  simp [h]

/-- `true` when the list is empty or its head is not zero. -/
def firstNonzero : Bytes → Bool
  | [] => true
  | b :: _ => b != 0

theorem toNat_lt_256 (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt b

/-- The accumulator form of the round trip: decoding after a non-zero
accumulator, or onto a list with a non-zero head, re-encodes to the
accumulator's bytes followed by the list. -/
theorem natToBytesBE_bytesToNatAcc (t : Bytes) :
    ∀ acc, (acc ≠ 0 ∨ firstNonzero t = true) →
      natToBytesBE (bytesToNatAcc acc t) = natToBytesBE acc ++ t := by
  induction t with
  | nil => intro acc _; simp [bytesToNatAcc]
  | cons b t ih =>
    intro acc hacc
    have hb := toNat_lt_256 b
    have hne : acc * 256 + b.toNat ≠ 0 := by
      rcases hacc with h | h
      · omega
      · simp [firstNonzero] at h
        have : b.toNat ≠ 0 := by
          intro h0; apply h; exact UInt8.toNat.inj (by simpa using h0)
        omega
    rw [bytesToNatAcc, ih (acc * 256 + b.toNat) (Or.inl hne), natToBytesBE_pos _ hne]
    have h1 : (acc * 256 + b.toNat) / 256 = acc := by omega
    have h2 : (acc * 256 + b.toNat) % 256 = b.toNat := by omega
    rw [h1, h2, UInt8.ofNat_toNat, List.append_assoc]
    rfl

theorem natToBytesBE_bytesToNat (t : Bytes) (h : firstNonzero t = true) :
    natToBytesBE (bytesToNat t) = t := by
  have := natToBytesBE_bytesToNatAcc t 0 (Or.inr h)
  rw [natToBytesBE_zero] at this
  simpa [bytesToNat] using this

/-! ## Leading zeros -/

theorem firstNonzero_dropWhile (bs : Bytes) :
    firstNonzero (bs.dropWhile (fun b => b == 0)) = true := by
  induction bs with
  | nil => rfl
  | cons b t ih =>
    by_cases hb : b = 0
    · subst hb; simpa [List.dropWhile] using ih
    · have : (b == 0) = false := by simpa using hb
      simp [List.dropWhile, this, firstNonzero, hb]

theorem mem_takeWhile_sat {α : Type} (p : α → Bool) (l : List α) :
    ∀ a ∈ l.takeWhile p, p a = true := by
  induction l with
  | nil => intro a h; simp at h
  | cons x xs ih =>
    intro a h
    by_cases hx : p x = true
    · rw [List.takeWhile_cons_of_pos hx] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact hx
      · exact ih a h'
    · rw [List.takeWhile_cons_of_neg hx] at h; simp at h

theorem takeWhile_eq_replicate (bs : Bytes) :
    bs.takeWhile (fun b => b == 0) = List.replicate (leadingZeroCount bs) 0 := by
  rw [List.eq_replicate_iff]
  refine ⟨rfl, ?_⟩
  intro b hb
  have := mem_takeWhile_sat _ bs b hb
  simpa using this

/-- `takeWhile` walks through a run of satisfying elements. -/
theorem takeWhile_replicate_append {α : Type} (p : α → Bool) (a : α) (hp : p a = true) (z : Nat)
    (l : List α) : (List.replicate z a ++ l).takeWhile p = List.replicate z a ++ l.takeWhile p := by
  induction z with
  | zero => rfl
  | succ z ih => simp [List.replicate, List.takeWhile_cons_of_pos hp, ih]

theorem dropWhile_replicate_append {α : Type} (p : α → Bool) (a : α) (hp : p a = true) (z : Nat)
    (l : List α) : (List.replicate z a ++ l).dropWhile p = l.dropWhile p := by
  induction z with
  | zero => rfl
  | succ z ih => simp [List.replicate, List.dropWhile_cons_of_pos hp, ih]

/-! ## The round trip -/

/-- The decode of an encoding, with the leading-zero run and the
non-zero remainder named explicitly. -/
theorem base58Decode?_ofParts (z : Nat) (rest : Bytes) (hrest : firstNonzero rest = true) :
    base58Decode? (String.ofList (List.replicate z '1' ++
        (natToDigits58 (bytesToNat rest)).map base58Char)) = some (List.replicate z 0 ++ rest) := by
  have hdigits : ∀ d ∈ natToDigits58 (bytesToNat rest), d < 58 := natToDigits58_lt _
  -- the body's head character is never '1'
  have hbody_head : ∀ c cs, (natToDigits58 (bytesToNat rest)).map base58Char = c :: cs →
      (c == '1') = false := by
    intro c cs hmap
    by_cases hn0 : bytesToNat rest = 0
    · rw [hn0, natToDigits58_zero] at hmap; simp at hmap
    · obtain ⟨d, ds, hds, hd⟩ := natToDigits58_head_ne_zero _ hn0
      rw [hds] at hmap
      simp at hmap
      have hd58 : d < 58 := hdigits d (by rw [hds]; exact List.mem_cons_self ..)
      have := base58Char_ne_one d hd58 hd
      rw [← hmap.1]
      simpa using this
  have htake : (List.replicate z '1' ++ (natToDigits58 (bytesToNat rest)).map base58Char).takeWhile
      (fun c => c == '1') = List.replicate z '1' := by
    rw [takeWhile_replicate_append _ _ rfl]
    cases hm : (natToDigits58 (bytesToNat rest)).map base58Char with
    | nil => simp
    | cons c cs =>
      rw [List.takeWhile_cons_of_neg (by simp [hbody_head c cs hm])]
      simp
  have hdrop : (List.replicate z '1' ++ (natToDigits58 (bytesToNat rest)).map base58Char).dropWhile
      (fun c => c == '1') = (natToDigits58 (bytesToNat rest)).map base58Char := by
    rw [dropWhile_replicate_append _ _ rfl]
    cases hm : (natToDigits58 (bytesToNat rest)).map base58Char with
    | nil => simp
    | cons c cs =>
      rw [List.dropWhile_cons_of_neg (by simp [hbody_head c cs hm])]
  simp only [base58Decode?, String.toList_ofList, htake, hdrop, digitsOfChars_map _ hdigits,
    List.length_replicate]
  rw [digitsToNat58_natToDigits58, natToBytesBE_bytesToNat rest hrest]

theorem base58Decode?_base58Encode (bs : Bytes) : base58Decode? (base58Encode bs) = some bs := by
  have hsplit : bs = List.replicate (leadingZeroCount bs) 0 ++ bs.dropWhile (fun b => b == 0) := by
    conv => lhs; rw [← List.takeWhile_append_dropWhile (p := fun b => b == 0) (l := bs)]
    rw [takeWhile_eq_replicate]
  have := base58Decode?_ofParts (leadingZeroCount bs) (bs.dropWhile (fun b => b == 0))
    (firstNonzero_dropWhile bs)
  unfold base58Encode
  rw [this, ← hsplit]

theorem multibaseDecode?_encode (bs : Bytes) :
    multibaseDecode? (multibaseEncodeBase58btc bs) = some bs := by
  unfold multibaseDecode? multibaseEncodeBase58btc
  have : ("z" ++ base58Encode bs).toList = 'z' :: (base58Encode bs).toList := by
    simp [String.toList_append]
  rw [this]
  simp only
  rw [String.ofList_toList]
  exact base58Decode?_base58Encode bs

theorem multibaseZToHex?_hexToMultibaseZ? (hex : String) (bs : Bytes)
    (h : bytesOfHex? hex = some bs) :
    (hexToMultibaseZ? hex).bind multibaseZToHex? = some (hexOfBytes bs) := by
  simp [hexToMultibaseZ?, multibaseZToHex?, h, multibaseDecode?_encode]

theorem bytesPrefixEq_append (pre rest : Bytes) : bytesPrefixEq pre (pre ++ rest) = true := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp [bytesPrefixEq, ih]

theorem multikeyToEd25519PublicKey?_of_key (pk : Bytes) (h : pk.length = 32) :
    multikeyToEd25519PublicKey? (ed25519PublicKeyToMultikey pk) = some pk := by
  unfold multikeyToEd25519PublicKey? multikeyToKey? ed25519PublicKeyToMultikey
  rw [multibaseDecode?_encode]
  have hp := bytesPrefixEq_append ed25519PubPrefix pk
  simp only [hp]
  simp [ed25519PubPrefix, h]

end L4Factoidal.VC.Multibase

namespace L4Factoidal.VC.DidKey

open L4Factoidal.VC.Multibase

theorem stripPrefixChars_append (pre rest : List Char) :
    stripPrefixChars pre (pre ++ rest) = some rest := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp [stripPrefixChars, ih]

/-- A 32-byte public key survives `did:key:` encoding and parsing. -/
theorem parseDidKey_didKeyOfPublicKey (pk : Bytes) (h : pk.length = 32) :
    (parseDidKey (didKeyOfPublicKey pk)).map Ed25519Did.pubkey = some pk := by
  unfold parseDidKey didKeyOfPublicKey didKeyPrefix parseDidKeyChars
  rw [String.toList_append, String.toList_ofList, stripPrefixChars_append]
  simp only [String.ofList_toList, multikeyToEd25519PublicKey?_of_key pk h]
  rfl

end L4Factoidal.VC.DidKey

namespace L4Factoidal.VC.DataIntegrity

open L4Factoidal.RDF
open L4Factoidal.Crypto
open L4Factoidal.VC.Multibase

/-! ## The hash input depends on the canonical forms only -/

theorem hashData_congr (alg : HashAlgorithm) {d₁ d₂ c₁ c₂ : String}
    (hd : d₁ = d₂) (hc : c₁ = c₂) : hashData alg d₁ c₁ = hashData alg d₂ c₂ := by
  rw [hd, hc]

/-- Two datasets with the same RDFC-1.0 canonical form — however their
blank nodes are labelled, however their quads are ordered — produce the
same proof value under the same key … -/
theorem createProofValue_of_canonical_eq (signF : SignFn) (alg : HashAlgorithm) (sk : ByteArray)
    {doc₁ doc₂ cfg₁ cfg₂ : Dataset}
    (hd : doc₁.canonicalNQuads .sha256 = doc₂.canonicalNQuads .sha256)
    (hc : cfg₁.canonicalNQuads .sha256 = cfg₂.canonicalNQuads .sha256) :
    createProofValue signF alg sk doc₁ cfg₁ = createProofValue signF alg sk doc₂ cfg₂ := by
  unfold createProofValue transformDataset
  rw [hd, hc]

/-- … and the same verdict on any proof value. -/
theorem verifyProofValue_of_canonical_eq (verifyF : VerifyFn) (alg : HashAlgorithm) (pk : ByteArray)
    {doc₁ doc₂ cfg₁ cfg₂ : Dataset} (pv : String)
    (hd : doc₁.canonicalNQuads .sha256 = doc₂.canonicalNQuads .sha256)
    (hc : cfg₁.canonicalNQuads .sha256 = cfg₂.canonicalNQuads .sha256) :
    verifyProofValue verifyF alg pk doc₁ cfg₁ pv = verifyProofValue verifyF alg pk doc₂ cfg₂ pv := by
  unfold verifyProofValue transformDataset
  rw [hd, hc]

/-! ## Refusals -/

/-- A proofValue that is not multibase-z is rejected without consulting
the primitive (whatever the primitive would say). -/
theorem verifyFromCanonical_not_multibase (verifyF : VerifyFn) (alg : HashAlgorithm)
    (pk : ByteArray) (doc cfg pv : String) (h : multibaseDecode? pv = none) :
    verifyFromCanonical verifyF alg pk doc cfg pv = false := by
  simp [verifyFromCanonical, h]

/-- A document without a `proof` field is refused as `noProof`, for every
loader and every primitive. -/
theorem verifyDocument_noProof (loader : JSONLD.Loader) (verifyF : VerifyFn) (doc : JSON.Json)
    (purpose : String) (alg : HashAlgorithm) (h : doc.field? "proof" = none) :
    verifyDocument loader verifyF doc purpose alg = .error .noProof := by
  unfold verifyDocument
  rw [h]
  rfl

/-! ## Create, then verify -/

theorem toByteArray_ofByteArray (a : ByteArray) : toByteArray (ofByteArray a) = a := by
  cases a with
  | mk data => simp [toByteArray, ofByteArray]

/-- If the primitive accepts its own signature on the hash data, a proof
created over canonical forms verifies over the same canonical forms. The
primitive's correctness is the HYPOTHESIS `hsig` — what HACL* promises
and this tree does not prove. -/
theorem verifyFromCanonical_createFromCanonical (signF : SignFn) (verifyF : VerifyFn)
    (alg : HashAlgorithm) (sk pk : ByteArray) (doc cfg pv : String)
    (hcreate : createFromCanonical signF alg sk doc cfg = some pv)
    (hsig : verifyF pk (hashData alg doc cfg) (signF sk (hashData alg doc cfg)) = true) :
    verifyFromCanonical verifyF alg pk doc cfg pv = true := by
  unfold createFromCanonical at hcreate
  simp only at hcreate
  split at hcreate
  · exact absurd hcreate (by simp)
  · have hpv : pv = multibaseEncodeBase58btc (ofByteArray (signF sk (hashData alg doc cfg))) := by
      simpa using hcreate.symm
    unfold verifyFromCanonical
    rw [hpv, multibaseDecode?_encode]
    simp only [toByteArray_ofByteArray]
    exact hsig

end L4Factoidal.VC.DataIntegrity

/-! ## Axiom audit -/

#print axioms L4Factoidal.VC.Multibase.base58Decode?_base58Encode
#print axioms L4Factoidal.VC.Multibase.multibaseDecode?_encode
#print axioms L4Factoidal.VC.DidKey.parseDidKey_didKeyOfPublicKey
#print axioms L4Factoidal.VC.DataIntegrity.verifyProofValue_of_canonical_eq
#print axioms L4Factoidal.VC.DataIntegrity.verifyFromCanonical_createFromCanonical
#print axioms L4Factoidal.VC.DataIntegrity.verifyDocument_noProof
