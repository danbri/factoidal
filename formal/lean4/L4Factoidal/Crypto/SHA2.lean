/-
L4Factoidal.Crypto.SHA2 — FIPS 180-4 SHA-256/384/512, pure Lean 4.

Crypto-policy amendment (skills/crypto-policy/SKILL.md, "Lean 4 tree
amendment", owner-approved 2026-08-22): a pure Lean implementation of
a HASH FUNCTION OVER PUBLIC DATA is permitted — RDFC-1.0
canonicalisation hashing (`RDF.Canonical.fst`'s `hash_sha256`/
`hash_sha384` assume vals), VC Data Integrity's `hash_sha256_hex`, and
the SPARQL §17.4.4 SHA256/SHA384/SHA512 builtins are all hashes of
PUBLIC data, never secrets or MACs, so there is no side channel to
protect and no constant-time requirement. This module is NOT approved
for, and MUST NOT be used for, any signature, key-derivation,
password, or MAC computation — those go through HACL* via `@[extern]`
FFI only (the Lean tree's single permitted extern family; see
crypto-policy §"Lean 4 tree amendment" item 2). MD5 and SHA-1 remain
unported (out of scope for this landing; see `PORT_NOTES.md`).

Implements FIPS PUB 180-4 (Secure Hash Standard, 2015-08):
  §5.1.1  padding for the 512-bit-block (SHA-256) message schedule
  §5.1.2  padding for the 1024-bit-block (SHA-384/512) message schedule
  §5.3.2  SHA-256 initial hash value H(0)
  §5.3.3  SHA-512 initial hash value H(0)
  §5.3.4  SHA-384 initial hash value H(0)
  §6.2.2  SHA-256 hash computation (message schedule + compression)
  §6.4.2  SHA-512 hash computation (message schedule + compression)
  §6.5    SHA-384 = the SHA-512 algorithm with a different H(0) and a
          truncated (384-bit / 6-word) output

Structural discipline: total functions only, no `partial def`.
  - The outer, message-length-dependent block loop
    (`processBlocks256`/`processBlocks512`) uses Nat-fuel-by-block-
    count: padding fixes the EXACT block count before recursion
    starts (`(pad256 m).size / 64`, always exact by `pad256_size`
    below), so the fuel is a precise value, not a guess, and the
    recursion is structural on that fuel.
  - The two FIXED-length inner loops per block (message-schedule
    extension: 48/64 extra words; the round function: 64/80 rounds)
    use core Lean's `for _ in [a:b] do` over a compile-time-constant
    range — a total, non-`partial` construct from `Init.Data.Range`.
  - `pushN` (padding zero-fill and length-field bytes) is written as
    an explicit Nat-structural recursion so its size behaviour
    (`pushN_size` in `SHA2Theorems.lean`) is provable by plain
    induction, independent of the pushed byte VALUES.
  - The final digest serialisation (`appendWord32BE`/`appendWord64BE`,
    and the digest-assembly `let`-chains in `sha256`/`sha384`/
    `sha512`) is a straight-line sequence of `ByteArray.push` calls
    with a statically fixed count (4 or 8 per word, 8 or 6 words) —
    not a loop — so the digest-length theorems in `SHA2Theorems.lean`
    need only unfold that fixed chain, never reason about either
    internal loop's contents or about the hash's actual arithmetic.
-/
namespace L4Factoidal.Crypto

/-! ## §4.2.2 SHA-256 constants (K) — fractional parts of the cube
roots of the first 64 primes, ×2^32, truncated. Derived independently
in-session with Python arbitrary-precision integer arithmetic (not
copied from a published table) and cross-checked against the
well-known published value K[0] = 0x428a2f98. -/

def K256 : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-! ## §5.3.2 SHA-256 initial hash value H(0) — fractional parts of
the square roots of the first 8 primes, ×2^32, truncated. Cross-checked
against the well-known H0[0] = 0x6a09e667. -/

def H256_0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-! ## §4.2.3 SHA-384/512 constants (K) — fractional parts of the
cube roots of the first 80 primes, ×2^64, truncated. -/

def K512 : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817 ]

/-! ## §5.3.3 SHA-512 initial hash value H(0). Cross-checked against
the well-known H0[0] = 0x6a09e667f3bcc908. -/

def H512_0 : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179 ]

/-! ## §5.3.4 SHA-384 initial hash value H(0) — the second-8-primes
variant (primes 9..16), distinct from SHA-512's. Cross-checked against
the well-known H0[0] = 0xcbbb9d5dc1059ed8. -/

def H384_0 : Array UInt64 := #[
  0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
  0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4 ]

/-! ## Bit-rotation primitives (§3.2 operations ROTR, SHR are the
`>>>`/`<<<`/`|||` combination below; SHR alone is plain `>>>`). -/

/-- Right rotation of a 32-bit word, `0 < n < 32` in every call site
below (§3.2 `ROTR^n`). -/
def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Right rotation of a 64-bit word, `0 < n < 64` in every call site
below (§3.2 `ROTR^n`). -/
def rotr64 (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-! ## Big-endian byte ⟷ word conversions (§5.1's message block is a
sequence of big-endian words; §5.3's output words are serialised
big-endian in the hex encodings §5.4's examples use). -/

/-- Read 4 big-endian bytes starting at `off` as one `UInt32` word. -/
def bytesToWordBE32 (a : ByteArray) (off : Nat) : UInt32 :=
  (a.get! off).toUInt32       <<< 24 |||
  (a.get! (off + 1)).toUInt32 <<< 16 |||
  (a.get! (off + 2)).toUInt32 <<< 8  |||
  (a.get! (off + 3)).toUInt32

/-- Read 8 big-endian bytes starting at `off` as one `UInt64` word. -/
def bytesToWordBE64 (a : ByteArray) (off : Nat) : UInt64 :=
  (a.get! off).toUInt64       <<< 56 |||
  (a.get! (off + 1)).toUInt64 <<< 48 |||
  (a.get! (off + 2)).toUInt64 <<< 40 |||
  (a.get! (off + 3)).toUInt64 <<< 32 |||
  (a.get! (off + 4)).toUInt64 <<< 24 |||
  (a.get! (off + 5)).toUInt64 <<< 16 |||
  (a.get! (off + 6)).toUInt64 <<< 8  |||
  (a.get! (off + 7)).toUInt64

/-- Append the 4 big-endian bytes of `x` to `acc`. A straight-line
4-push chain (NOT a loop), so `(appendWord32BE acc x).size = acc.size
+ 4` unconditionally, for every `acc`/`x` — the fact `SHA2Theorems`
uses to prove digest lengths without touching the hash arithmetic. -/
def appendWord32BE (acc : ByteArray) (x : UInt32) : ByteArray :=
  acc |>.push (x >>> 24).toUInt8
      |>.push (x >>> 16).toUInt8
      |>.push (x >>> 8).toUInt8
      |>.push x.toUInt8

/-- Append the 8 big-endian bytes of `x` to `acc`. A straight-line
8-push chain (NOT a loop); see `appendWord32BE`. -/
def appendWord64BE (acc : ByteArray) (x : UInt64) : ByteArray :=
  acc |>.push (x >>> 56).toUInt8
      |>.push (x >>> 48).toUInt8
      |>.push (x >>> 40).toUInt8
      |>.push (x >>> 32).toUInt8
      |>.push (x >>> 24).toUInt8
      |>.push (x >>> 16).toUInt8
      |>.push (x >>> 8).toUInt8
      |>.push x.toUInt8

/-! ## §6.2.2 step 1 — SHA-256 message schedule -/

/-- Expand one 64-byte message block into the 64-word SHA-256 message
schedule `W_0 .. W_63` (FIPS 180-4 §6.2.2 step 1). The first 16 words
are the block read big-endian; words 16..63 extend via `σ0`/`σ1`
(§4.1.2 eq. 4.6/4.7). The extension loop runs a compile-time-fixed 48
iterations over `[16:64]` — total, not `partial`. -/
def buildSchedule256 (block : ByteArray) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for t in [0:16] do
    w := w.push (bytesToWordBE32 block (t * 4))
  for t in [16:64] do
    let x15 := w[t - 15]!
    let x2  := w[t - 2]!
    let s0 := rotr32 x15 7 ^^^ rotr32 x15 18 ^^^ (x15 >>> 3)
    let s1 := rotr32 x2 17 ^^^ rotr32 x2 19  ^^^ (x2 >>> 10)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  pure w

/-! ## §6.4.2 step 1 — SHA-384/512 message schedule -/

/-- Expand one 128-byte message block into the 80-word SHA-512 message
schedule (FIPS 180-4 §6.4.2 step 1; §4.1.3 eq. 4.13/4.14 for `σ0`/`σ1`).
The extension loop runs a compile-time-fixed 64 iterations over
`[16:80]` — total, not `partial`. -/
def buildSchedule512 (block : ByteArray) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := #[]
  for t in [0:16] do
    w := w.push (bytesToWordBE64 block (t * 8))
  for t in [16:80] do
    let x15 := w[t - 15]!
    let x2  := w[t - 2]!
    let s0 := rotr64 x15 1  ^^^ rotr64 x15 8  ^^^ (x15 >>> 7)
    let s1 := rotr64 x2 19  ^^^ rotr64 x2 61  ^^^ (x2 >>> 6)
    w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
  pure w

/-! ## §6.2.2 step 3 — SHA-256 compression -/

/-- Compress one 64-byte block into the running 8-word state (FIPS
180-4 §6.2.2 steps 2–4: message schedule, the 64-round working-variable
update using `Σ0`/`Σ1`/`Ch`/`Maj` §4.1.2, and the final feed-forward
addition). The round loop runs a compile-time-fixed 64 iterations over
`[0:64]` — total, not `partial`. Always returns an explicit 8-element
array literal, independent of `h`/`block`'s values (the fact
`SHA2Theorems` needs, though — per the module header — the digest
length proofs go through the OUTPUT serialisation instead, so this
particular invariant is not separately theorem-ised). -/
def sha256CompressBlock (h : Array UInt32) (block : ByteArray) : Array UInt32 := Id.run do
  let w := buildSchedule256 block
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [0:64] do
    let bigS1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + bigS1 + ch + K256[t]! + w[t]!
    let bigS0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := bigS0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  pure #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
         h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-! ## §6.4.2 step 3 — SHA-384/512 compression -/

/-- Compress one 128-byte block into the running 8-word state (FIPS
180-4 §6.4.2 steps 2–4, the 64-bit analogue of `sha256CompressBlock`
with 80 rounds over `[0:80]` — total, not `partial`). Shared by
SHA-512 and SHA-384 (§6.5): only the initial `H(0)` and the output
truncation differ. -/
def sha512CompressBlock (h : Array UInt64) (block : ByteArray) : Array UInt64 := Id.run do
  let w := buildSchedule512 block
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for t in [0:80] do
    let bigS1 := rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + bigS1 + ch + K512[t]! + w[t]!
    let bigS0 := rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := bigS0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  pure #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
         h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-! ## §5.1 padding -/

/-- Push `n` bytes onto `acc`, byte `i` given by `f i`. Explicit
Nat-structural recursion on `n` (not a `for` loop, not `partial def`)
so `pushN_size` (`SHA2Theorems.lean`) is a one-line induction. -/
def pushN (acc : ByteArray) (n : Nat) (f : Nat → UInt8) : ByteArray :=
  match n with
  | 0 => acc
  | k + 1 => (pushN acc k f).push (f k)

/-- The `i`-th (0 = most significant) of `width` big-endian bytes of
`n`'s low `8*width` bits. -/
def natByteBE (n width i : Nat) : UInt8 :=
  UInt8.ofNat ((n / (256 ^ (width - 1 - i))) % 256)

/-- FIPS 180-4 §5.1.1: pad a message to a multiple of the 512-bit
(64-byte) SHA-256 block size — append `0x80`, then the minimal number
of `0x00` bytes so the length (mod 64) is 56, then the 8-byte
big-endian bit-length field. `pad256_size` (`SHA2Theorems.lean`)
proves the padded size actually IS a multiple of 64 for every `m`. -/
def pad256 (m : ByteArray) : ByteArray :=
  let l := m.size
  let r := (l + 1) % 64
  let k := if r ≤ 56 then 56 - r else 120 - r
  let lenBits := l * 8
  pushN (pushN (m.push 0x80) k (fun _ => 0)) 8 (fun i => natByteBE lenBits 8 i)

/-- FIPS 180-4 §5.1.2: the SHA-384/512 analogue of `pad256` — 1024-bit
(128-byte) blocks, target remainder 112, and a 16-byte big-endian
bit-length field (128-bit length, per the spec; `Nat` has no overflow
so this is exact for every message length that actually fits in
memory). -/
def pad512 (m : ByteArray) : ByteArray :=
  let l := m.size
  let r := (l + 1) % 128
  let k := if r ≤ 112 then 112 - r else 240 - r
  let lenBits := l * 8
  pushN (pushN (m.push 0x80) k (fun _ => 0)) 16 (fun i => natByteBE lenBits 16 i)

/-! ## Outer block loop — Nat-fuel-by-block-count -/

/-- Fold `sha256CompressBlock` over every 64-byte block of `data`,
`fuel` times. `fuel` is always called with the EXACT block count
(`data.size / 64`, and `data` already padded to a multiple of 64), so
this is not a guessed bound — it is structural recursion on `fuel`,
which the equation compiler accepts directly (no `termination_by`
needed: `fuel + 1 → fuel` decreases). -/
def processBlocks256 (h0 : Array UInt32) (data : ByteArray) (fuel : Nat) : Array UInt32 :=
  match fuel with
  | 0 => h0
  | fuel + 1 =>
      let block := data.extract 0 64
      let rest := data.extract 64 data.size
      processBlocks256 (sha256CompressBlock h0 block) rest fuel

/-- The positioned form of the SHA-256 block fold. Unlike
    `processBlocks256`, it never constructs successively shorter suffixes of a
    large input: each iteration copies just its 64-byte compression block.
    This is the form used by the streaming public-data checksum API below. -/
def processBlocks256At (h0 : Array UInt32) (data : ByteArray) (offset fuel : Nat) : Array UInt32 :=
  match fuel with
  | 0 => h0
  | fuel + 1 =>
      let block := data.extract offset (offset + 64)
      processBlocks256At (sha256CompressBlock h0 block) data (offset + 64) fuel

/-- The SHA-384/512 analogue of `processBlocks256`, 128-byte blocks. -/
def processBlocks512 (h0 : Array UInt64) (data : ByteArray) (fuel : Nat) : Array UInt64 :=
  match fuel with
  | 0 => h0
  | fuel + 1 =>
      let block := data.extract 0 128
      let rest := data.extract 128 data.size
      processBlocks512 (sha512CompressBlock h0 block) rest fuel

/-! ## Public API — §6.2.2/§6.4.2/§6.5 top-level hash functions -/

/-- FIPS 180-4 §6.2 SHA-256 of an arbitrary `ByteArray`. Output is
always 32 bytes (`SHA2Theorems.sha256_size`). -/
def sha256 (m : ByteArray) : ByteArray :=
  let padded := pad256 m
  let hFinal := processBlocks256 H256_0 padded (padded.size / 64)
  ByteArray.empty
    |> (appendWord32BE · hFinal[0]!)
    |> (appendWord32BE · hFinal[1]!)
    |> (appendWord32BE · hFinal[2]!)
    |> (appendWord32BE · hFinal[3]!)
    |> (appendWord32BE · hFinal[4]!)
    |> (appendWord32BE · hFinal[5]!)
    |> (appendWord32BE · hFinal[6]!)
    |> (appendWord32BE · hFinal[7]!)

/-! ## Incremental SHA-256

`Sha256Stream` is for immutable public byte artifacts such as an RDF source
being ingested. It retains at most one incomplete compression block, so a
file-backed loader can commit the same SHA-256 source identity as the
whole-buffer reference encoder without retaining the source bytes for hashing.
It is not a MAC, KDF, password primitive or signature operation. -/

/-- Running state for an incremental SHA-256 digest. `pending` contains fewer
    than 64 bytes after `update`; that invariant follows directly from the
    complete-block split in the constructor. -/
structure Sha256Stream where
  h : Array UInt32 := H256_0
  pending : ByteArray := ByteArray.empty
  bytes : Nat := 0

/-- Empty incremental SHA-256 state. -/
def Sha256Stream.init : Sha256Stream := {}

/-- Absorb a byte chunk, retaining only its final incomplete 64-byte block. -/
def Sha256Stream.update (stream : Sha256Stream) (chunk : ByteArray) : Sha256Stream :=
  let combined := stream.pending ++ chunk
  let complete := combined.size / 64
  let consumed := complete * 64
  { h := processBlocks256At stream.h combined 0 complete
  , pending := combined.extract consumed combined.size
  , bytes := stream.bytes + chunk.size }

/-- Serialize a completed SHA-256 chaining state. -/
private def sha256Digest (hFinal : Array UInt32) : ByteArray :=
  ByteArray.empty
    |> (appendWord32BE · hFinal[0]!)
    |> (appendWord32BE · hFinal[1]!)
    |> (appendWord32BE · hFinal[2]!)
    |> (appendWord32BE · hFinal[3]!)
    |> (appendWord32BE · hFinal[4]!)
    |> (appendWord32BE · hFinal[5]!)
    |> (appendWord32BE · hFinal[6]!)
    |> (appendWord32BE · hFinal[7]!)

/-- Finalize a public-artifact SHA-256 stream using the complete input length
    carried separately from its under-64-byte tail. -/
def Sha256Stream.finish (stream : Sha256Stream) : ByteArray :=
  let r := (stream.pending.size + 1) % 64
  let zeros := if r ≤ 56 then 56 - r else 120 - r
  let padded := pushN (pushN (stream.pending.push 0x80) zeros (fun _ => 0)) 8
    (fun i => natByteBE (stream.bytes * 8) 8 i)
  sha256Digest (processBlocks256At stream.h padded 0 (padded.size / 64))

/-- FIPS 180-4 §6.4 SHA-512 of an arbitrary `ByteArray`. Output is
always 64 bytes (`SHA2Theorems.sha512_size`). -/
def sha512 (m : ByteArray) : ByteArray :=
  let padded := pad512 m
  let hFinal := processBlocks512 H512_0 padded (padded.size / 128)
  ByteArray.empty
    |> (appendWord64BE · hFinal[0]!)
    |> (appendWord64BE · hFinal[1]!)
    |> (appendWord64BE · hFinal[2]!)
    |> (appendWord64BE · hFinal[3]!)
    |> (appendWord64BE · hFinal[4]!)
    |> (appendWord64BE · hFinal[5]!)
    |> (appendWord64BE · hFinal[6]!)
    |> (appendWord64BE · hFinal[7]!)

/-- FIPS 180-4 §6.5 SHA-384: the SHA-512 algorithm with `H384_0` in
place of `H512_0`, truncated to the first 6 words (384 bits / 48
bytes) of output (`SHA2Theorems.sha384_size`). -/
def sha384 (m : ByteArray) : ByteArray :=
  let padded := pad512 m
  let hFinal := processBlocks512 H384_0 padded (padded.size / 128)
  ByteArray.empty
    |> (appendWord64BE · hFinal[0]!)
    |> (appendWord64BE · hFinal[1]!)
    |> (appendWord64BE · hFinal[2]!)
    |> (appendWord64BE · hFinal[3]!)
    |> (appendWord64BE · hFinal[4]!)
    |> (appendWord64BE · hFinal[5]!)

/-! ## Hex encoding — the string-in/hex-out forms the F* `assume val`s
need (`hash_sha256 : string -> string`, RDFC-1.0 hashes UTF-8 strings
and returns lowercase hex). Not cryptography, a plain codec. -/

/-- The 16 lowercase hex digits, index 0..15. -/
def hexDigits : Array Char :=
  #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

/-- One byte as two lowercase hex characters. -/
def byteToHex (b : UInt8) : String :=
  String.ofList [hexDigits[(b.toNat / 16)]!, hexDigits[(b.toNat % 16)]!]

/-- A `ByteArray` as a lowercase hex string, most-significant byte
first (matches every published SHA-2 test vector's presentation). -/
def bytesToHex (a : ByteArray) : String :=
  (a.toList.map byteToHex).foldl (· ++ ·) ""

/-- SHA-256 of the UTF-8 encoding of `s`, as lowercase hex — the exact
shape of `RDF.Canonical.fst`'s `hash_sha256 : string ->
(r:string{FStar.String.length r == 64})`. -/
def sha256Hex (s : String) : String := bytesToHex (sha256 s.toUTF8)

/-- SHA-384 of the UTF-8 encoding of `s`, as lowercase hex — the exact
shape of `RDF.Canonical.fst`'s `hash_sha384`. -/
def sha384Hex (s : String) : String := bytesToHex (sha384 s.toUTF8)

/-- SHA-512 of the UTF-8 encoding of `s`, as lowercase hex (SPARQL
§17.4.4 `SHA512`; no F* `assume val` port target yet, ported ahead of
need since the SHA-384/512 machinery is shared). -/
def sha512Hex (s : String) : String := bytesToHex (sha512 s.toUTF8)

/-! ## Hash agility

Owner directive (2026-08-22, verbatim): "wherever we use SHA-256 maybe
we should prep the next one, since it sooner or later will fall and we
want to be ready." Every CONSUMER of this module — RDFC-1.0
canonicalisation (whose spec, `RDF.Canonical.fst`'s `hash_algorithm`
type, already parameterises the hash with SHA-256 as default and
SHA-384 as the tested alternate), VC Data Integrity, and the SPARQL
§17.4.4 hash builtins — MUST take a `HashAlgorithm` and call
`hashBytes`/`hashHex`, never call `sha256`/`sha256Hex` etc. directly.
This is what makes swapping in a future algorithm (or retiring SHA-256
if it is broken) a one-branch change here instead of a call-site grep
across the tree. -/

/-- The hash algorithms this module realises. Room is left for a
future SHA-3 family member (`sha3_256`/`shake256`) — NOT added yet
(would need a Keccak-f permutation, a different construction from
Merkle–Damgård/FIPS 180-4, and its own test vectors); adding a
constructor here is the whole migration once that lands. -/
inductive HashAlgorithm
  | sha256
  | sha384
  | sha512
  -- future: | sha3_256 | shake256 (FIPS 202; not ported)
  deriving DecidableEq, Repr

/-- Dispatch to the selected algorithm's byte-in/byte-out digest. -/
def hashBytes (alg : HashAlgorithm) (m : ByteArray) : ByteArray :=
  match alg with
  | .sha256 => sha256 m
  | .sha384 => sha384 m
  | .sha512 => sha512 m

/-- Dispatch to the selected algorithm's string-in/lowercase-hex-out
digest — the form every F* `assume val` port target and every SPARQL
§17.4.4 builtin needs. -/
def hashHex (alg : HashAlgorithm) (s : String) : String :=
  match alg with
  | .sha256 => sha256Hex s
  | .sha384 => sha384Hex s
  | .sha512 => sha512Hex s

end L4Factoidal.Crypto
