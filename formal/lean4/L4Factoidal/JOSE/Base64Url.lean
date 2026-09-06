/-
L4Factoidal.JOSE.Base64Url — base64url WITHOUT padding, RFC 7515 §2 and
RFC 4648 §5, as JOSE uses it.

This is not a general base64 codec and must not become one. RFC 7515 §2
defines `BASE64URL(OCTETS)` as base64url encoding "with all trailing '='
characters omitted … and without the inclusion of any line breaks,
whitespace, or other additional characters", and defines
`BASE64URL-DECODE` as the inverse "with the addition of appropriate
trailing '=' characters" — that is, a decoder that accepts a padded or
whitespace-decorated string is accepting something the specification does
not define. Every JOSE value that reaches a signature check travels
through this module, so leniency here is a signature-verification
weakness, not a convenience.

What is REFUSED, and why each refusal is in the specification:

  * `=` anywhere. RFC 7515 §2 omits padding. `=` is not in the RFC 4648
    §5 alphabet either, so the refusal falls out of the alphabet check.
  * Any character outside `A-Z a-z 0-9 - _`. Standard-alphabet `+` and
    `/` are refused: RFC 7515 §2 is URL-safe base64url, and accepting
    both alphabets would give two encodings of one octet string.
  * Whitespace and line breaks, by the same alphabet check.
  * A length of `4k+1` characters, which encodes no whole number of
    octets.
  * A final group whose unused low bits are not zero — the
    "non-canonical" encodings, for example `"QQ=="`'s unpadded form
    `"QR"`, which no encoder emits but which a lenient decoder maps onto
    the same octet as `"QQ"`. Refusing them makes the encoding
    INJECTIVE in both directions: `decode` is a partial inverse of
    `encode` (`decode_encode`) and `encode` is a left inverse of
    `decode` on everything `decode` accepts (`encode_decode`). Without
    this, two distinct `protected` header strings could decode to the
    same header, and a token could be re-serialised without invalidating
    its signature.

## Structure, and why it is shaped for proof

Encoding is split into two stages with the arithmetic in `Nat`:
`encodeToDigits` turns octets into six-bit digit values, and
`encodeDigit` turns one digit into one character. Decoding inverts each
stage separately (`digitsOf?`, `decodeDigits`). The arithmetic is
multiplication, division and remainder by numeric literals, which `omega`
decides; a formulation in terms of `UInt8` shifts and masks would not be
decidable without a bitvector tactic. The character stage is a bounded
statement over the 64 digits, closed by `decide`.
-/

namespace L4Factoidal.JOSE.Base64Url

/-! ## Stage 1: one six-bit digit ↔ one character (RFC 4648 §5, Table 2) -/

/-- The RFC 4648 §5 "URL and Filename safe" alphabet, as arithmetic on
codepoints rather than a table lookup: `A-Z` = 0-25, `a-z` = 26-51,
`0-9` = 52-61, `-` = 62, `_` = 63. A digit at or above 64 is not in the
domain; `encodeDigit` is nevertheless TOTAL, and answers `'_'` there.
No caller reaches that case — `digitLt64` proves every digit
`encodeToDigits` produces is below 64. -/
def encodeDigit (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n)
  else if n < 52 then Char.ofNat (97 + (n - 26))
  else if n < 62 then Char.ofNat (48 + (n - 52))
  else if n == 62 then '-'
  else '_'

/-- The inverse. `none` for every character outside the RFC 4648 §5
alphabet — which includes `=` (padding), `+` and `/` (the standard
alphabet), and every whitespace character. -/
def decodeDigit? (c : Char) : Option Nat :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then some (c.toNat - 65)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then some (c.toNat - 97 + 26)
  else if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48 + 52)
  else if c.toNat == 45 then some 62
  else if c.toNat == 95 then some 63
  else none

/-- Membership of the RFC 4648 §5 alphabet. -/
def isBase64UrlChar (c : Char) : Bool := (decodeDigit? c).isSome

/-- The character stage round-trips on its whole domain. Closed by
`decide` over the 64 digits: each case is codepoint arithmetic, so the
kernel evaluates it without a table search. -/
theorem decodeDigit_encodeDigit (n : Nat) (h : n < 64) :
    decodeDigit? (encodeDigit n) = some n := by
  have hb : (List.range 64).all (fun m => decodeDigit? (encodeDigit m) == some m) = true := by
    decide
  have hm := (List.all_eq_true.mp hb) n (List.mem_range.mpr h)
  simpa using hm

/-- `=` is not in the alphabet, so no padded string decodes. This is the
RFC 7515 §2 requirement restated as a fact about `decodeDigit?`, and it
is what `decode_refuses_padding` below lifts to whole strings. -/
theorem decodeDigit_padding : decodeDigit? '=' = none := by decide

/-- Nor are the standard-alphabet characters, so there is exactly one
alphabet in play. -/
theorem decodeDigit_standard_alphabet :
    decodeDigit? '+' = none ∧ decodeDigit? '/' = none := by decide

/-- Nor is any of the whitespace RFC 7515 §2 excludes. -/
theorem decodeDigit_whitespace :
    decodeDigit? ' ' = none ∧ decodeDigit? '\n' = none ∧
    decodeDigit? '\r' = none ∧ decodeDigit? '\t' = none := by decide

/-! ## Stage 2: octets ↔ six-bit digits -/

/-- Octets to six-bit digits. Three octets become four digits; a final
group of one or two octets becomes two or three digits whose unused low
bits are zero, which is the unpadded form RFC 7515 §2 requires. -/
def encodeToDigits : List UInt8 → List Nat
  | [] => []
  | [a] =>
      [a.toNat * 16 / 64, a.toNat * 16 % 64]
  | [a, b] =>
      [(a.toNat * 256 + b.toNat) * 4 / 4096,
       (a.toNat * 256 + b.toNat) * 4 / 64 % 64,
       (a.toNat * 256 + b.toNat) * 4 % 64]
  | a :: b :: c :: rest =>
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 262144 ::
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 4096 % 64 ::
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) / 64 % 64 ::
      (a.toNat * 65536 + b.toNat * 256 + c.toNat) % 64 :: encodeToDigits rest

/-- Six-bit digits back to octets. `none` on a length of `4k+1`, and on
a final group whose unused low bits are set (the non-canonical
encodings; see the module header). -/
def decodeDigits : List Nat → Option (List UInt8)
  | [] => some []
  | [_] => none
  | [d0, d1] =>
      if (d0 * 64 + d1) % 16 == 0 then some [UInt8.ofNat ((d0 * 64 + d1) / 16)] else none
  | [d0, d1, d2] =>
      if (d0 * 4096 + d1 * 64 + d2) % 4 == 0 then
        some [UInt8.ofNat ((d0 * 4096 + d1 * 64 + d2) / 1024),
              UInt8.ofNat ((d0 * 4096 + d1 * 64 + d2) / 4 % 256)]
      else none
  | d0 :: d1 :: d2 :: d3 :: rest =>
      (decodeDigits rest).map fun tl =>
        UInt8.ofNat ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 65536) ::
        UInt8.ofNat ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 256 % 256) ::
        UInt8.ofNat ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) % 256) :: tl

/-- Characters to six-bit digits, refusing the whole string as soon as
one character is outside the alphabet. -/
def digitsOf? : List Char → Option (List Nat)
  | [] => some []
  | c :: cs =>
      match decodeDigit? c with
      | none => none
      | some d => (digitsOf? cs).map (d :: ·)

/-! ## The codec -/

/-- RFC 7515 §2 `BASE64URL(OCTETS)`. -/
def encodeChars (bs : List UInt8) : List Char := (encodeToDigits bs).map encodeDigit

/-- RFC 7515 §2 `BASE64URL-DECODE(STRING)`, strict on both stages. -/
def decodeChars (cs : List Char) : Option (List UInt8) :=
  (digitsOf? cs).bind decodeDigits

/-! ## Theorems -/

/-- Every digit the encoder produces is a six-bit value, so
`encodeDigit` is never reached outside its domain. -/
theorem digitLt64 : ∀ (bs : List UInt8), ∀ d ∈ encodeToDigits bs, d < 64
  | [], d, hd => by simp [encodeToDigits] at hd
  | [a], d, hd => by
      have ha := a.toNat_lt
      simp [encodeToDigits] at hd
      rcases hd with h | h <;> omega
  | [a, b], d, hd => by
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      simp [encodeToDigits] at hd
      rcases hd with h | h | h <;> omega
  | a :: b :: c :: rest, d, hd => by
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      have hc := c.toNat_lt
      simp only [encodeToDigits, List.mem_cons] at hd
      rcases hd with h | h | h | h | h
      · omega
      · omega
      · omega
      · omega
      · exact digitLt64 rest d h

/-- The character stage round-trips on any list of six-bit digits. -/
theorem digitsOf_map_encodeDigit :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 64) →
      digitsOf? (ds.map encodeDigit) = some ds
  | [], _ => by simp [digitsOf?]
  | d :: ds, h => by
      have hd : d < 64 := h d (by simp)
      have hrest : digitsOf? (ds.map encodeDigit) = some ds :=
        digitsOf_map_encodeDigit ds (fun x hx => h x (by simp [hx]))
      simp [digitsOf?, decodeDigit_encodeDigit d hd, hrest]

/-- The octet stage round-trips. All of it is division and remainder by
literals over values bounded by `UInt8.toNat_lt`, so `omega` decides
each group. -/
theorem decodeDigits_encodeToDigits :
    ∀ (bs : List UInt8), decodeDigits (encodeToDigits bs) = some bs
  | [] => by simp [encodeToDigits, decodeDigits]
  | [a] => by
      have ha := a.toNat_lt
      have h1 : (a.toNat * 16 / 64 * 64 + a.toNat * 16 % 64) % 16 = 0 := by omega
      have h2 : (a.toNat * 16 / 64 * 64 + a.toNat * 16 % 64) / 16 = a.toNat := by omega
      simp [encodeToDigits, decodeDigits, h1, h2, UInt8.ofNat_toNat]
  | [a, b] => by
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      generalize hn : (a.toNat * 256 + b.toNat) * 4 = n at *
      have h1 : (n / 4096 * 4096 + n / 64 % 64 * 64 + n % 64) % 4 = 0 := by omega
      have h2 : (n / 4096 * 4096 + n / 64 % 64 * 64 + n % 64) / 1024 = a.toNat := by omega
      have h3 : (n / 4096 * 4096 + n / 64 % 64 * 64 + n % 64) / 4 % 256 = b.toNat := by omega
      simp [encodeToDigits, decodeDigits, hn, h1, h2, h3, UInt8.ofNat_toNat]
  | a :: b :: c :: rest => by
      have ha := a.toNat_lt
      have hb := b.toNat_lt
      have hc := c.toNat_lt
      generalize hn : a.toNat * 65536 + b.toNat * 256 + c.toNat = n at *
      have h1 : (n / 262144 * 262144 + n / 4096 % 64 * 4096 + n / 64 % 64 * 64 + n % 64)
          / 65536 = a.toNat := by omega
      have h2 : (n / 262144 * 262144 + n / 4096 % 64 * 4096 + n / 64 % 64 * 64 + n % 64)
          / 256 % 256 = b.toNat := by omega
      have h3 : (n / 262144 * 262144 + n / 4096 % 64 * 4096 + n / 64 % 64 * 64 + n % 64)
          % 256 = c.toNat := by omega
      have hrest := decodeDigits_encodeToDigits rest
      simp [encodeToDigits, decodeDigits, hn, h1, h2, h3, hrest, UInt8.ofNat_toNat]

/-- **RFC 7515 §2 round trip.** `BASE64URL-DECODE(BASE64URL(x)) = x` for
every octet string `x`. -/
theorem decode_encode (bs : List UInt8) : decodeChars (encodeChars bs) = some bs := by
  unfold decodeChars encodeChars
  rw [digitsOf_map_encodeDigit _ (digitLt64 bs)]
  simpa using decodeDigits_encodeToDigits bs

/-- Encoding is injective, so two different octet strings never share a
`protected` header or a payload serialisation. -/
theorem encodeChars_injective {x y : List UInt8} (h : encodeChars x = encodeChars y) : x = y := by
  have hx := decode_encode x
  have hy := decode_encode y
  rw [h, hy] at hx
  exact (Option.some.inj hx).symm

/-! ### The other direction: `encode` is a left inverse of `decode`

Strictness on the final group is what buys this. Without it, `"Zg"` and
`"Zh"` would both decode to the single octet `0x66` and only one of them
would re-encode, so a JWS `protected` header could be re-spelled without
changing the octets the signature covers. -/

/-- Every digit `decodeDigit?` produces is a six-bit value. -/
theorem decodeDigit_lt64 {c : Char} {d : Nat} (h : decodeDigit? c = some d) : d < 64 := by
  unfold decodeDigit? at h
  split at h
  · next hr => cases h; omega
  · split at h
    · next _ hr => cases h; omega
    · split at h
      · next _ _ hr => cases h; omega
      · split at h
        · cases h; omega
        · split at h
          · cases h; omega
          · simp at h

/-- The character stage is injective: a character in the alphabet is
recovered from its digit. -/
theorem encodeDigit_decodeDigit {c : Char} {d : Nat} (h : decodeDigit? c = some d) :
    encodeDigit d = c := by
  unfold decodeDigit? at h
  split at h
  · next hr =>
      obtain ⟨h1, h2⟩ := hr
      cases h
      unfold encodeDigit
      have : c.toNat - 65 < 26 := by omega
      simp only [if_pos this]
      have he : 65 + (c.toNat - 65) = c.toNat := by omega
      rw [he, Char.ofNat_toNat]
  · split at h
    · next _ hr =>
        obtain ⟨h1, h2⟩ := hr
        cases h
        unfold encodeDigit
        have hn : ¬ (c.toNat - 97 + 26 < 26) := by omega
        have hn2 : c.toNat - 97 + 26 < 52 := by omega
        simp only [if_neg hn, if_pos hn2]
        have he : 97 + (c.toNat - 97 + 26 - 26) = c.toNat := by omega
        rw [he, Char.ofNat_toNat]
    · split at h
      · next _ _ hr =>
          obtain ⟨h1, h2⟩ := hr
          cases h
          unfold encodeDigit
          have hn : ¬ (c.toNat - 48 + 52 < 26) := by omega
          have hn2 : ¬ (c.toNat - 48 + 52 < 52) := by omega
          have hn3 : c.toNat - 48 + 52 < 62 := by omega
          simp only [if_neg hn, if_neg hn2, if_pos hn3]
          have he : 48 + (c.toNat - 48 + 52 - 52) = c.toNat := by omega
          rw [he, Char.ofNat_toNat]
      · split at h
        · next _ _ _ hr =>
            cases h
            have hv : c.toNat = 45 := by simpa using hr
            have : c = '-' := by
              rw [← Char.ofNat_toNat c, hv]
            simpa [encodeDigit] using this.symm
        · split at h
          · next _ _ _ _ hr =>
              cases h
              have hv : c.toNat = 95 := by simpa using hr
              have : c = '_' := by
                rw [← Char.ofNat_toNat c, hv]
              simpa [encodeDigit] using this.symm
          · simp at h

/-- Digits recovered from characters are six-bit values. -/
theorem digitsOf_lt64 :
    ∀ (cs : List Char) (ds : List Nat), digitsOf? cs = some ds → ∀ d ∈ ds, d < 64
  | [], ds, h, d, hd => by
      unfold digitsOf? at h; cases h; simp at hd
  | c :: cs, ds, h, d, hd => by
      unfold digitsOf? at h
      cases hc : decodeDigit? c with
      | none => rw [hc] at h; simp at h
      | some d0 =>
          rw [hc] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ds', hds', hde⟩ := h
          subst hde
          rcases List.mem_cons.mp hd with rfl | hmem
          · exact decodeDigit_lt64 hc
          · exact digitsOf_lt64 cs ds' hds' d hmem

/-- The character stage is a bijection onto the alphabet. -/
theorem map_encodeDigit_digitsOf :
    ∀ (cs : List Char) (ds : List Nat), digitsOf? cs = some ds → ds.map encodeDigit = cs
  | [], ds, h => by unfold digitsOf? at h; cases h; simp
  | c :: cs, ds, h => by
      unfold digitsOf? at h
      cases hc : decodeDigit? c with
      | none => rw [hc] at h; simp at h
      | some d0 =>
          rw [hc] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ds', hds', hde⟩ := h
          subst hde
          simp [encodeDigit_decodeDigit hc, map_encodeDigit_digitsOf cs ds' hds']

/-- The octet stage is injective on six-bit digit lists. The bound is a
real hypothesis: `decodeDigits` does not range-check its input, and
`digitsOf?` is what guarantees the bound in the composite. -/
theorem encodeToDigits_decodeDigits :
    ∀ (ds : List Nat) (bs : List UInt8), (∀ d ∈ ds, d < 64) →
      decodeDigits ds = some bs → encodeToDigits bs = ds
  | [], bs, _, h => by unfold decodeDigits at h; cases h; rfl
  | [_], bs, _, h => by unfold decodeDigits at h; simp at h
  | [d0, d1], bs, hb, h => by
      have h0 : d0 < 64 := hb d0 (by simp)
      have h1 : d1 < 64 := hb d1 (by simp)
      unfold decodeDigits at h
      split at h
      · next hm =>
          cases h
          have hm' : (d0 * 64 + d1) % 16 = 0 := by simpa using hm
          have hlt : (d0 * 64 + d1) / 16 < 256 := by omega
          simp only [encodeToDigits]
          have ht : (UInt8.ofNat ((d0 * 64 + d1) / 16)).toNat = (d0 * 64 + d1) / 16 := by
            simp; omega
          rw [ht]
          have e0 : (d0 * 64 + d1) / 16 * 16 / 64 = d0 := by omega
          have e1 : (d0 * 64 + d1) / 16 * 16 % 64 = d1 := by omega
          rw [e0, e1]
      · simp at h
  | [d0, d1, d2], bs, hb, h => by
      have h0 : d0 < 64 := hb d0 (by simp)
      have h1 : d1 < 64 := hb d1 (by simp)
      have h2 : d2 < 64 := hb d2 (by simp)
      unfold decodeDigits at h
      split at h
      · next hm =>
          cases h
          have hm' : (d0 * 4096 + d1 * 64 + d2) % 4 = 0 := by simpa using hm
          simp only [encodeToDigits]
          have ta : (UInt8.ofNat ((d0 * 4096 + d1 * 64 + d2) / 1024)).toNat
              = (d0 * 4096 + d1 * 64 + d2) / 1024 := by simp; try omega
          have tb : (UInt8.ofNat ((d0 * 4096 + d1 * 64 + d2) / 4 % 256)).toNat
              = (d0 * 4096 + d1 * 64 + d2) / 4 % 256 := by simp; try omega
          rw [ta, tb]
          have e0 : ((d0 * 4096 + d1 * 64 + d2) / 1024 * 256
              + (d0 * 4096 + d1 * 64 + d2) / 4 % 256) * 4 / 4096 = d0 := by omega
          have e1 : ((d0 * 4096 + d1 * 64 + d2) / 1024 * 256
              + (d0 * 4096 + d1 * 64 + d2) / 4 % 256) * 4 / 64 % 64 = d1 := by omega
          have e2 : ((d0 * 4096 + d1 * 64 + d2) / 1024 * 256
              + (d0 * 4096 + d1 * 64 + d2) / 4 % 256) * 4 % 64 = d2 := by omega
          rw [e0, e1, e2]
      · simp at h
  | d0 :: d1 :: d2 :: d3 :: rest, bs, hb, h => by
      have h0 : d0 < 64 := hb d0 (by simp)
      have h1 : d1 < 64 := hb d1 (by simp)
      have h2 : d2 < 64 := hb d2 (by simp)
      have h3 : d3 < 64 := hb d3 (by simp)
      unfold decodeDigits at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨tl, htl, hbs⟩ := h
      subst hbs
      have hrest := encodeToDigits_decodeDigits rest tl
        (fun d hd => hb d (by simp [hd])) htl
      simp only [encodeToDigits]
      have ta : (UInt8.ofNat ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 65536)).toNat
          = (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 65536 := by simp; try omega
      have tb : (UInt8.ofNat ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 256 % 256)).toNat
          = (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 256 % 256 := by simp; try omega
      have tc : (UInt8.ofNat ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) % 256)).toNat
          = (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) % 256 := by simp; try omega
      rw [ta, tb, tc, hrest]
      have e0 : ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 65536 * 65536
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 256 % 256 * 256
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) % 256) / 262144 = d0 := by omega
      have e1 : ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 65536 * 65536
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 256 % 256 * 256
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) % 256) / 4096 % 64 = d1 := by omega
      have e2 : ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 65536 * 65536
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 256 % 256 * 256
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) % 256) / 64 % 64 = d2 := by omega
      have e3 : ((d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 65536 * 65536
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) / 256 % 256 * 256
          + (d0 * 262144 + d1 * 4096 + d2 * 64 + d3) % 256) % 64 = d3 := by omega
      rw [e0, e1, e2, e3]

/-- **`encode` is a left inverse of `decode`.** Every string this module
accepts is the encoding of the octets it decodes to, so an accepted
base64url string is the ONLY spelling of those octets. A JWS `protected`
header cannot be re-serialised without changing the signing input. -/
theorem encode_decode {cs : List Char} {bs : List UInt8}
    (h : decodeChars cs = some bs) : encodeChars bs = cs := by
  unfold decodeChars at h
  cases hd : digitsOf? cs with
  | none => rw [hd] at h; simp at h
  | some ds =>
      rw [hd] at h
      unfold encodeChars
      rw [encodeToDigits_decodeDigits ds bs (digitsOf_lt64 cs ds hd) h]
      exact map_encodeDigit_digitsOf cs ds hd

/-- **Every accepted character is in the RFC 4648 §5 alphabet.** This is
the single statement that carries the padding, standard-alphabet and
whitespace refusals: `=`, `+`, `/`, space, tab, CR and LF are all outside
`isBase64UrlChar` (`decodeDigit_padding` and the two theorems beside
it). -/
theorem digitsOf_alphabet :
    ∀ (cs : List Char) (ds : List Nat), digitsOf? cs = some ds →
      ∀ c ∈ cs, isBase64UrlChar c = true
  | [], _, _, c, hc => by simp at hc
  | c0 :: cs, ds, h, c, hc => by
      unfold digitsOf? at h
      cases hd : decodeDigit? c0 with
      | none => rw [hd] at h; simp at h
      | some d =>
          rw [hd] at h
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨ds', hds', _⟩ := h
          rcases List.mem_cons.mp hc with rfl | hmem
          · simp [isBase64UrlChar, hd]
          · exact digitsOf_alphabet cs ds' hds' c hmem

/-- **A string containing padding never decodes** (RFC 7515 §2). -/
theorem decode_refuses_padding (cs : List Char) (h : '=' ∈ cs) :
    decodeChars cs = none := by
  unfold decodeChars
  cases hd : digitsOf? cs with
  | none => simp
  | some ds =>
      exact absurd (digitsOf_alphabet cs ds hd '=' h) (by decide)

/-- **A string containing any non-alphabet character never decodes.**
`+` and `/` (the standard alphabet), whitespace and line breaks are
instances. -/
theorem decode_refuses_non_alphabet (cs : List Char) (c : Char)
    (hmem : c ∈ cs) (hbad : isBase64UrlChar c = false) :
    decodeChars cs = none := by
  unfold decodeChars
  cases hd : digitsOf? cs with
  | none => simp
  | some ds =>
      have := digitsOf_alphabet cs ds hd c hmem
      rw [hbad] at this
      exact absurd this (by decide)

/-! ## ByteArray and String surface

The theorems above are stated on `List UInt8` and `List Char`, which is
where the induction lives. These are the wrappers every JOSE module
calls; they are definitionally the list functions composed with the
standard conversions, and carry no logic of their own. -/

/-- RFC 7515 §2 `BASE64URL(OCTETS)` on a `ByteArray`. -/
def encode (b : ByteArray) : String := String.ofList (encodeChars b.data.toList)

/-- RFC 7515 §2 `BASE64URL-DECODE(STRING)` on a `String`. -/
def decode (s : String) : Option ByteArray :=
  (decodeChars s.toList).map fun bs => ⟨bs.toArray⟩

/-- Encode a UTF-8 string's octets. JOSE headers and payloads are
sequences of octets that happen to be UTF-8 JSON; this names that. -/
def encodeUtf8 (s : String) : String := encode s.toUTF8

/-- Decode to a `String` by reading the octets as UTF-8. `none` when the
base64url is invalid; `none` is NOT returned for invalid UTF-8, because
`String.fromUTF8?` is applied and its failure is propagated. -/
def decodeUtf8 (s : String) : Option String :=
  (decode s).bind String.fromUTF8?

/-! ## Fixtures

RFC 4648 §10 gives the base64 test vectors. They are reproduced here in
their base64url unpadded form — the alphabet differs from §4 only in the
62nd and 63rd characters, which none of these vectors reaches, and the
padding is dropped per RFC 7515 §2. The `=`-padded right-hand sides of
RFC 4648 §10 are shown in the comment beside each. RFC 4648 is an IETF
Trust document and its examples may be reproduced. -/

#guard encodeUtf8 "" == ""                  -- RFC 4648 §10: BASE64("") = ""
#guard encodeUtf8 "f" == "Zg"               -- "Zg=="
#guard encodeUtf8 "fo" == "Zm8"             -- "Zm8="
#guard encodeUtf8 "foo" == "Zm9v"           -- "Zm9v"
#guard encodeUtf8 "foob" == "Zm9vYg"        -- "Zm9vYg=="
#guard encodeUtf8 "fooba" == "Zm9vYmE"      -- "Zm9vYmE="
#guard encodeUtf8 "foobar" == "Zm9vYmFy"    -- "Zm9vYmFy"

#guard decodeUtf8 "" == some ""
#guard decodeUtf8 "Zg" == some "f"
#guard decodeUtf8 "Zm8" == some "fo"
#guard decodeUtf8 "Zm9v" == some "foo"
#guard decodeUtf8 "Zm9vYg" == some "foob"
#guard decodeUtf8 "Zm9vYmE" == some "fooba"
#guard decodeUtf8 "Zm9vYmFy" == some "foobar"

-- Padding is refused (RFC 7515 §2), including the exact §10 spellings.
#guard decode "Zg==" == none
#guard decode "Zm8=" == none
#guard decode "Zm9vYg==" == none
-- The standard alphabet is refused: these are the two characters that
-- differ between RFC 4648 §4 and §5.
#guard decode "+w" == none
#guard decode "/w" == none
#guard decode "-w" != none
#guard decode "_w" != none
-- Whitespace and line breaks are refused.
#guard decode "Zm9v Zm9v" == none
#guard decode "Zm9v\nZm9v" == none
-- A length of 4k+1 encodes no whole number of octets.
#guard decode "Z" == none
#guard decode "Zm9vZ" == none
-- Non-canonical final groups are refused: "Zg" and "Zh" would otherwise
-- both decode to the single octet 0x66.
#guard decode "Zg" != none
#guard decode "Zh" == none
#guard decode "Zm9vYg" != none
#guard decode "Zm9vYh" == none

-- The RFC 7515 Appendix A.1 payload, which every JWS example uses.
#guard decodeUtf8 "eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9leGFt\
cGxlLmNvbS9pc19yb290Ijp0cnVlfQ" ==
  some "{\"iss\":\"joe\",\r\n \"exp\":1300819380,\r\n \"http://example.com/is_root\":true}"

end L4Factoidal.JOSE.Base64Url
