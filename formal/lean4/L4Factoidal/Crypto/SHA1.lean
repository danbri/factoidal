/-
L4Factoidal.Crypto.SHA1 — SHA-1 (FIPS 180-4 §6.1), in pure Lean, for
the SPARQL 1.1 §17.4.4.8 `SHA1` builtin.

WHY A HAND-WRITTEN DIGEST IS ALLOWED HERE: `skills/crypto-policy/
SKILL.md`'s two-tier rule for `formal/lean4/`, tier 1 — a hash over
PUBLIC data (the argument of the SPARQL `SHA1()` function). No secret
is involved and no signature derives from it, so a pure Lean
implementation is PERMITTED by that policy; it is a codec, not a
security boundary. SHA-1 is deprecated for collision resistance and
is ported ONLY because the SPARQL 1.1 Recommendation lists it; nothing
in this tree may use it for integrity or authentication.

The F* tree assumes this function (`SPARQL11.Algebra.fst`
`assume val hash_sha1 : string -> string`); the Lean purity doctrine
replaces the assumption by this definition.

Shape: FIPS 180-4 §6.1.2. Padding is §5.1.1 — the SAME rule SHA-256
uses — so `pad256` is reused from `Crypto/SHA2.lean`; only the message
schedule, the round functions and the five-word state differ. Output
is the 20-byte digest as 40 LOWERCASE hex characters. Total: fixed
loops over `[0:80]`, block loop on an explicit fuel.

Test vectors: FIPS 180-4 / NIST "SHA-1 examples" (`"abc"`, the
two-block 56-byte message) as `#guard`s at the end of the file, plus
block-boundary lengths.
-/
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.MD5

namespace L4Factoidal.Crypto

/-- FIPS 180-4 §5.3.1 initial hash value `H(0)`. -/
def H_SHA1_0 : Array UInt32 :=
  #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

/-- §4.2.1 round constants `K_t`, one per 20-round quarter. -/
def K_SHA1 (t : Nat) : UInt32 :=
  if t < 20 then 0x5a827999
  else if t < 40 then 0x6ed9eba1
  else if t < 60 then 0x8f1bbcdc
  else 0xca62c1d6

/-- §4.1.1 round functions `f_t(x, y, z)`: Ch, Parity, Maj, Parity. -/
def f_SHA1 (t : Nat) (x y z : UInt32) : UInt32 :=
  if t < 20 then (x &&& y) ^^^ ((~~~x) &&& z)
  else if t < 40 then x ^^^ y ^^^ z
  else if t < 60 then (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
  else x ^^^ y ^^^ z

/-- §6.1.2 step 1: the 80-word message schedule; words 16..79 are
`ROTL^1(W[t-3] ^ W[t-8] ^ W[t-14] ^ W[t-16])` (eq. 6.2). -/
def buildScheduleSHA1 (block : ByteArray) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for t in [0:16] do
    w := w.push (bytesToWordBE32 block (t * 4))
  for t in [16:80] do
    w := w.push (rotl32 (w[t - 3]! ^^^ w[t - 8]! ^^^ w[t - 14]! ^^^ w[t - 16]!) 1)
  pure w

/-- §6.1.2 steps 2–4: compress one 64-byte block into the 5-word state. -/
def sha1CompressBlock (h : Array UInt32) (block : ByteArray) : Array UInt32 := Id.run do
  let w := buildScheduleSHA1 block
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  for t in [0:80] do
    let tmp := rotl32 a 5 + f_SHA1 t b c d + e + K_SHA1 t + w[t]!
    e := d
    d := c
    c := rotl32 b 30
    b := a
    a := tmp
  pure #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e]

/-- Fold over every 64-byte block; `fuel` is the exact block count. -/
def processBlocksSHA1 (h0 : Array UInt32) (data : ByteArray) (fuel : Nat) : Array UInt32 :=
  match fuel with
  | 0 => h0
  | fuel + 1 =>
      let block := data.extract 0 64
      let rest := data.extract 64 data.size
      processBlocksSHA1 (sha1CompressBlock h0 block) rest fuel

/-- FIPS 180-4 §6.1 SHA-1 of an arbitrary `ByteArray`: 20 bytes, the
five state words big-endian. -/
def sha1 (m : ByteArray) : ByteArray :=
  let padded := pad256 m
  let hFinal := processBlocksSHA1 H_SHA1_0 padded (padded.size / 64)
  ByteArray.empty
    |> (appendWord32BE · hFinal[0]!)
    |> (appendWord32BE · hFinal[1]!)
    |> (appendWord32BE · hFinal[2]!)
    |> (appendWord32BE · hFinal[3]!)
    |> (appendWord32BE · hFinal[4]!)

/-- SHA-1 of the UTF-8 encoding of `s` as lowercase hex — the SPARQL
§17.4.4.8 `SHA1(string)` result (port target: F* `hash_sha1`). -/
def sha1Hex (s : String) : String := bytesToHex (sha1 s.toUTF8)

/-! ## FIPS 180-4 / NIST example vectors (build-time `#guard`s) -/

#guard sha1Hex "" == "da39a3ee5e6b4b0d3255bfef95601890afd80709"
#guard sha1Hex "abc" == "a9993e364706816aba3e25717850c26c9cd0d89d"
#guard sha1Hex "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
  == "84983e441c3bd26ebaae4aa1f95129e5e54670f1"
#guard sha1Hex "message digest" == "c12252ceda8be8994d5fa0290a47231c1d16aae3"
-- Block-boundary lengths: every padding branch.
#guard sha1Hex (String.ofList (List.replicate 55 'a')) == "c1c8bbdc22796e28c0e15163d20899b65621d65a"
#guard sha1Hex (String.ofList (List.replicate 56 'a')) == "c2db330f6083854c99d4b5bfb6e8f29f201be699"
#guard sha1Hex (String.ofList (List.replicate 64 'a')) == "0098ba824b5c16427bd7a1122a5a442a25ec644d"
#guard sha1Hex (String.ofList (List.replicate 65 'a')) == "11655326c708d70319be2610e8a57d9a5b959d3b"
-- Non-ASCII input hashes its UTF-8 bytes.
#guard sha1Hex "日本語" == "c12140a0ffb4e56481b4fe0a7a25040c2eafa9ca"
#guard (sha1 ByteArray.empty).size == 20

end L4Factoidal.Crypto
