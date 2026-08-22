/-
L4Factoidal.Crypto.MD5 — the MD5 message digest (RFC 1321), in pure
Lean, for the SPARQL 1.1 §17.4.4.7 `MD5` builtin.

WHY A HAND-WRITTEN DIGEST IS ALLOWED HERE: `skills/crypto-policy/
SKILL.md` forbids rolling our own cryptography, with a two-tier rule
for `formal/lean4/`. This module is tier 1 — a hash over PUBLIC data
(the argument of the SPARQL `MD5()` function, which the query itself
names). No secret is involved, no signature is derived from it, so a
pure Lean implementation is PERMITTED by that policy; it is a codec,
not a security boundary. MD5 is cryptographically broken (collisions
are cheap) and is ported ONLY because the SPARQL 1.1 Recommendation
lists it; nothing in this tree may use it for integrity or
authentication.

The F* tree assumes this function (`SPARQL11.Algebra.fst`
`assume val hash_md5 : string -> string`, realised by OCaml glue);
the Lean purity doctrine (`skills/factoidal-lean-basics/SKILL.md`)
replaces the assumption by this definition.

Shape: RFC 1321 §3. Input is the UTF-8 encoding of the string; output
is the 16-byte digest as 32 LOWERCASE hex characters, the form
§17.4.4.7's example (`MD5("abc") = "900150983cd24fb0d6963f7d28e17f72"`)
shows. Everything is total: fixed-count loops over `[0:64]`, and a
block loop on an explicit fuel equal to the block count. No `partial`,
no `sorry`, no `axiom`, no `native_decide`.

Test vectors: RFC 1321 appendix A.5, as `#guard`s at the end of the
file, plus block-boundary lengths (55, 56, 63, 64, 65 bytes) that
exercise every padding branch.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Crypto

/-! ## RFC 1321 §3.4 constants -/

/-- `T[i] = floor(2^32 · |sin(i + 1)|)`, `i = 0 .. 63` (RFC 1321 §3.4).
Generated, not transcribed: `int(abs(math.sin(i+1)) * 2**32)`. -/
def K_MD5 : Array UInt32 := #[
  0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
  0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
  0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
  0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
  0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
  0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
  0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
  0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391]

/-- Per-round left-rotation amounts `s[i]` (RFC 1321 §3.4, the four
rounds' `[7 12 17 22]`, `[5 9 14 20]`, `[4 11 16 23]`, `[6 10 15 21]`). -/
def S_MD5 : Array UInt32 := #[
  7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
  5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20, 5,  9, 14, 20,
  4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
  6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21]

/-- RFC 1321 §3.3 initial state `A B C D`, as 32-bit words. -/
def H_MD5_0 : Array UInt32 := #[0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476]

/-! ## Little-endian word helpers (RFC 1321 §2: "a sequence of bytes
... low-order byte first") -/

/-- Left rotation of a 32-bit word, `0 < n < 32` at every call site. -/
def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/-- Read 4 LITTLE-endian bytes at `off` as one word. -/
def bytesToWordLE32 (a : ByteArray) (off : Nat) : UInt32 :=
  (a.get! off).toUInt32 |||
  (a.get! (off + 1)).toUInt32 <<< 8 |||
  (a.get! (off + 2)).toUInt32 <<< 16 |||
  (a.get! (off + 3)).toUInt32 <<< 24

/-- Append the 4 little-endian bytes of `x`. -/
def appendWord32LE (acc : ByteArray) (x : UInt32) : ByteArray :=
  acc |>.push x.toUInt8
      |>.push (x >>> 8).toUInt8
      |>.push (x >>> 16).toUInt8
      |>.push (x >>> 24).toUInt8

/-- The `i`-th (0 = LEAST significant) of `width` little-endian bytes
of `n`'s low `8*width` bits. -/
def natByteLE (n width i : Nat) : UInt8 :=
  if i < width then UInt8.ofNat ((n / (256 ^ i)) % 256) else 0

/-! ## RFC 1321 §3.1–§3.2 padding -/

/-- Append `0x80`, then zeros to 56 (mod 64), then the 64-bit
LITTLE-endian bit length. Same block geometry as SHA-256's `pad256`,
differing only in the endianness of the length field. -/
def padMD5 (m : ByteArray) : ByteArray :=
  let l := m.size
  let r := (l + 1) % 64
  let k := if r ≤ 56 then 56 - r else 120 - r
  let lenBits := l * 8
  pushN (pushN (m.push 0x80) k (fun _ => 0)) 8 (fun i => natByteLE lenBits 8 i)

/-! ## RFC 1321 §3.4 — one block -/

/-- Compress one 64-byte block into the 4-word state: 64 rounds, each
the auxiliary function `F`/`G`/`H`/`I` of its quarter, the message
word index `g` of its quarter, the constant `T[i]`, and the rotation
`s[i]`. Fixed loop over `[0:64]` — total. -/
def md5CompressBlock (h : Array UInt32) (block : ByteArray) : Array UInt32 := Id.run do
  let mut m : Array UInt32 := #[]
  for j in [0:16] do
    m := m.push (bytesToWordLE32 block (j * 4))
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  for i in [0:64] do
    let (f, g) :=
      if i < 16 then ((b &&& c) ||| ((~~~b) &&& d), i)
      else if i < 32 then ((d &&& b) ||| ((~~~d) &&& c), (5 * i + 1) % 16)
      else if i < 48 then (b ^^^ c ^^^ d, (3 * i + 5) % 16)
      else (c ^^^ (b ||| (~~~d)), (7 * i) % 16)
    let f' := f + a + K_MD5[i]! + m[g]!
    a := d
    d := c
    c := b
    b := b + rotl32 f' S_MD5[i]!
  pure #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d]

/-- Fold `md5CompressBlock` over every 64-byte block; `fuel` is the
exact block count (structural recursion, as `processBlocks256`). -/
def processBlocksMD5 (h0 : Array UInt32) (data : ByteArray) (fuel : Nat) : Array UInt32 :=
  match fuel with
  | 0 => h0
  | fuel + 1 =>
      let block := data.extract 0 64
      let rest := data.extract 64 data.size
      processBlocksMD5 (md5CompressBlock h0 block) rest fuel

/-! ## Public API -/

/-- RFC 1321 MD5 of an arbitrary `ByteArray`: 16 bytes, the state
words `A B C D` each serialised little-endian (§3.5). -/
def md5 (m : ByteArray) : ByteArray :=
  let padded := padMD5 m
  let hFinal := processBlocksMD5 H_MD5_0 padded (padded.size / 64)
  ByteArray.empty
    |> (appendWord32LE · hFinal[0]!)
    |> (appendWord32LE · hFinal[1]!)
    |> (appendWord32LE · hFinal[2]!)
    |> (appendWord32LE · hFinal[3]!)

/-- MD5 of the UTF-8 encoding of `s` as lowercase hex — the SPARQL
§17.4.4.7 `MD5(string)` result (port target: F* `hash_md5`). -/
def md5Hex (s : String) : String := bytesToHex (md5 s.toUTF8)

/-! ## RFC 1321 appendix A.5 test vectors (build-time `#guard`s) -/

#guard md5Hex "" == "d41d8cd98f00b204e9800998ecf8427e"
#guard md5Hex "a" == "0cc175b9c0f1b6a831c399e269772661"
#guard md5Hex "abc" == "900150983cd24fb0d6963f7d28e17f72"
#guard md5Hex "message digest" == "f96b697d7cb7938d525a2f31aaf161d0"
#guard md5Hex "abcdefghijklmnopqrstuvwxyz" == "c3fcd3d76192e4007dfb496cca67e13b"
#guard md5Hex "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
  == "d174ab98d277d9f5a5611c2c9f419d9f"
#guard md5Hex "12345678901234567890123456789012345678901234567890123456789012345678901234567890"
  == "57edf4a22be3c955ac49da2e2107b67a"
-- Block-boundary lengths: every padding branch (one block with room
-- for the length; one block with none; two blocks).
#guard md5Hex (String.ofList (List.replicate 55 'a')) == "ef1772b6dff9a122358552954ad0df65"
#guard md5Hex (String.ofList (List.replicate 56 'a')) == "3b0c8ac703f828b04c6c197006d17218"
#guard md5Hex (String.ofList (List.replicate 63 'a')) == "b06521f39153d618550606be297466d5"
#guard md5Hex (String.ofList (List.replicate 64 'a')) == "014842d480b571495a4a0363793f7367"
#guard md5Hex (String.ofList (List.replicate 65 'a')) == "c743a45e0d2e6a95cb859adae0248435"
-- Non-ASCII input hashes its UTF-8 bytes (the W3C `md5-02` fixture
-- value is checked end to end by the sparql11 harness).
#guard md5Hex "日本語" == "00110af8b4393ef3f72c50be5b332bec"
#guard (md5 ByteArray.empty).size == 16

end L4Factoidal.Crypto
