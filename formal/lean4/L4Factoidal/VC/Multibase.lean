/-
L4Factoidal.VC.Multibase — hex, base58btc, multibase and the Ed25519
multicodec prefixes used by Verifiable Credentials Data Integrity and
did:key. Port of `formal/fstar/VC.Multibase.fst`.

This is BYTE ENCODING, not cryptography (`skills/crypto-policy/SKILL.md`:
"Encoding layers (multibase, multihash, base58/base64url) are NOT crypto
— implement those in pure F* like any other codec"). Nothing here
touches a curve, a digest or a signature; it is arbitrary-precision
arithmetic on `Nat` over lists of bytes.

Specifications:
  * base58btc — the Bitcoin alphabet
    `123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz`, as
    referenced by the Multibase draft
    (https://datatracker.ietf.org/doc/draft-multiformats-multibase/,
    table entry `z`). Leading zero BYTES are rendered as leading `1`
    characters, one each; the remaining bytes are one big-endian number
    written in base 58, most significant digit first, with no digits at
    all for the number zero.
  * multibase — a one-character prefix naming the base: `z` = base58btc.
    Only `z` is decoded here, because eddsa-rdfc-2022 (`proofValue`) and
    did:key / Multikey (`publicKeyMultibase`, `secretKeyMultibase`) use
    nothing else. The F* source also carries a lenient base64(-url)
    decoder for `VC.Credential`'s `relatedResource` digest checks; that
    structural-validation module is not ported in this stage, so neither
    is the decoder.
  * multicodec — the unsigned-varint tag prefixed to raw key bytes
    (https://github.com/multiformats/multicodec, table `ed25519-pub` =
    0xed → varint `ed 01`; `ed25519-priv` = 0x1300 → varint `80 26`).
    The Multikey form of an Ed25519 public key is `z` + base58btc(`ed 01`
    ++ 32 key bytes), which always starts `z6Mk`; the secret-key form
    starts `z3u2`.

## What the F* declines to prove, and this port proves

`VC.Multibase.fst`'s banner says a `decode (encode bs) == Some bs` lemma
"is intentionally NOT stated here because a full base58 bijection proof
(leading-zero handling + nat↔bytes↔base58 inverses) is a disproportionate
proof burden". `VC/Theorems.lean` states and proves exactly that lemma
(`base58Decode?_base58Encode`, and through it `multibaseDecode?_encode`
and `parseDidKey_didKeyOfPublicKey`). To make the proof structural the
definitions below differ from the F* in SHAPE, not in value:

  * nat→digits / nat→bytes are written most-significant-first with an
    explicit `termination_by` on the quotient, and the digits→nat /
    bytes→nat folds carry an accumulator (the F* computes `b * 256^len`
    per position);
  * the leading-zero run is `takeWhile`/`dropWhile`, so the core lemma
    `takeWhile_append_dropWhile` gives the decomposition for free.

Every function is total; decoders return `Option`.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.VC.Multibase

/-- A byte list — the codec's working representation. `ByteArray` is the
FFI boundary type; conversions are at the bottom of this file. -/
abbrev Bytes := List UInt8

/-! ## Hex ↔ bytes (lowercase out; either case in) -/

/-- Value of one hex digit, either case. Port of `hex_digit_val`. -/
def hexDigitVal? (c : Char) : Option Nat :=
  let x := c.toNat
  if 0x30 ≤ x ∧ x ≤ 0x39 then some (x - 0x30)
  else if 0x61 ≤ x ∧ x ≤ 0x66 then some (x - 0x61 + 10)
  else if 0x41 ≤ x ∧ x ≤ 0x46 then some (x - 0x41 + 10)
  else none

/-- Lowercase hex digit of a value below 16 (`'0'` otherwise, to stay
total — callers pass `n / 16` and `n % 16` of a byte). -/
def hexChar (d : Nat) : Char :=
  (Crypto.hexDigits[d]?).getD '0'

def hexOfByte (b : UInt8) : String :=
  String.ofList [hexChar (b.toNat / 16), hexChar (b.toNat % 16)]

/-- Lowercase hex of a byte list. Port of `bytes_to_hex`. -/
def hexOfBytes (bs : Bytes) : String :=
  bs.foldl (fun acc b => acc ++ hexOfByte b) ""

/-- Pairs of hex digits to bytes; `none` on an odd count or a non-hex
character. Port of `chars_to_bytes`. -/
def bytesOfHexChars : List Char → Option Bytes
  | [] => some []
  | [_] => none
  | hi :: lo :: rest =>
    match hexDigitVal? hi, hexDigitVal? lo, bytesOfHexChars rest with
    | some h, some l, some t => some (UInt8.ofNat (h * 16 + l) :: t)
    | _, _, _ => none

/-- Port of `hex_to_bytes`. -/
def bytesOfHex? (s : String) : Option Bytes := bytesOfHexChars s.toList

/-! ## Big-endian bytes ↔ `Nat`

Most-significant byte first, no leading zero bytes on the way out
(`natToBytesBE 0 = []`). -/

/-- `bytesToNatAcc acc bs` = `acc * 256^|bs| + value(bs)`; the
accumulator form makes the round-trip proof a plain induction. -/
def bytesToNatAcc (acc : Nat) : Bytes → Nat
  | [] => acc
  | b :: t => bytesToNatAcc (acc * 256 + b.toNat) t

/-- Big-endian value of a byte list. Port of `bytes_to_nat`. -/
def bytesToNat (bs : Bytes) : Nat := bytesToNatAcc 0 bs

/-- Big-endian bytes of a number, no leading zeros; `0 ↦ []`. Port of
`nat_to_bytes_be`. -/
def natToBytesBE (n : Nat) : Bytes :=
  if _h : n = 0 then []
  else natToBytesBE (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n
decreasing_by omega

/-! ## base58btc -/

/-- The Bitcoin base58 alphabet, index = digit value. Spelled out as a
list literal (not `"…".toList`) so `decide` can evaluate the two facts
about it that the proofs need. -/
def base58Alphabet : List Char :=
  ['1','2','3','4','5','6','7','8','9',
   'A','B','C','D','E','F','G','H','J','K','L','M','N','P','Q','R','S','T','U','V','W','X','Y','Z',
   'a','b','c','d','e','f','g','h','i','j','k','m','n','o','p','q','r','s','t','u','v','w','x','y','z']

/-- Character of a base58 digit (`'1'` for an out-of-range digit, which
no caller produces: every digit is a `% 58`). Port of `base58_char_of`. -/
def base58Char (d : Nat) : Char := (base58Alphabet[d]?).getD '1'

/-- Index of `c` in `cs`, counting from `i`. Port of `find_index_aux`. -/
def indexOfChar (c : Char) : List Char → Nat → Option Nat
  | [], _ => none
  | h :: t, i => if h == c then some i else indexOfChar c t (i + 1)

/-- Digit value of a base58 character. Port of `base58_digit_of`. -/
def base58Digit? (c : Char) : Option Nat := indexOfChar c base58Alphabet 0

/-- Base-58 digits of a number, most significant first; `0 ↦ []`. Port of
`nat_to_base58_chars`, one step earlier (digits, not characters). -/
def natToDigits58 (n : Nat) : List Nat :=
  if _h : n = 0 then []
  else natToDigits58 (n / 58) ++ [n % 58]
termination_by n
decreasing_by omega

/-- `digitsToNat58 acc ds` = `acc * 58^|ds| + value(ds)`. Port of
`base58_chars_to_nat`, over digits. -/
def digitsToNat58 (acc : Nat) : List Nat → Nat
  | [] => acc
  | d :: ds => digitsToNat58 (acc * 58 + d) ds

/-- Characters to digits; `none` at the first non-alphabet character. -/
def digitsOfChars : List Char → Option (List Nat)
  | [] => some []
  | c :: cs =>
    match base58Digit? c, digitsOfChars cs with
    | some d, some ds => some (d :: ds)
    | _, _ => none

/-- Number of leading zero bytes. Port of `count_leading_zero_bytes`. -/
def leadingZeroCount (bs : Bytes) : Nat := (bs.takeWhile (fun b => b == 0)).length

/-- base58btc encoding: one `'1'` per leading zero byte, then the
big-endian value of the rest in base 58. Port of `base58btc_encode`. -/
def base58Encode (bs : Bytes) : String :=
  let ones := List.replicate (leadingZeroCount bs) '1'
  let body := (natToDigits58 (bytesToNat (bs.dropWhile (fun b => b == 0)))).map base58Char
  String.ofList (ones ++ body)

/-- base58btc decoding: one zero byte per leading `'1'`, then the rest
read as a base-58 number. `none` on a non-alphabet character. Port of
`base58btc_decode`. -/
def base58Decode? (s : String) : Option Bytes :=
  let cs := s.toList
  let ones := (cs.takeWhile (fun c => c == '1')).length
  match digitsOfChars (cs.dropWhile (fun c => c == '1')) with
  | none => none
  | some ds => some (List.replicate ones 0 ++ natToBytesBE (digitsToNat58 0 ds))

/-! ## Multibase (`z` = base58btc) -/

/-- Port of `multibase_encode_base58btc`. -/
def multibaseEncodeBase58btc (bs : Bytes) : String := "z" ++ base58Encode bs

/-- Decode a multibase string; only the `z` (base58btc) base is
accepted, as in the F* source. Port of `multibase_decode`. -/
def multibaseDecode? (s : String) : Option Bytes :=
  match s.toList with
  | 'z' :: rest => base58Decode? (String.ofList rest)
  | _ => none

/-- Hex signature bytes → multibase-z `proofValue`. Port of
`hex_to_multibase_z`. -/
def hexToMultibaseZ? (hex : String) : Option String :=
  (bytesOfHex? hex).map multibaseEncodeBase58btc

/-- multibase-z `proofValue` → lowercase hex. Port of `multibase_z_to_hex`. -/
def multibaseZToHex? (mb : String) : Option String :=
  (multibaseDecode? mb).map hexOfBytes

/-! ## Multicodec prefixes for Ed25519 keys -/

/-- `ed25519-pub` (0xed) as an unsigned varint. Port of
`ed25519_multicodec_prefix`. -/
def ed25519PubPrefix : Bytes := [0xed, 0x01]

/-- `ed25519-priv` (0x1300) as an unsigned varint — the `z3u2…`
`secretKeyMultibase` form of the Data Integrity EdDSA test vectors. Not
in the F* source (it never handles a multibase SECRET key). -/
def ed25519PrivPrefix : Bytes := [0x80, 0x26]

/-- Raw 32-byte public key → Multikey (`z6Mk…`). Total: no length check
here, callers that need one use `multikeyToEd25519PublicKey?` as the
inverse. Port of `ed25519_pubkey_to_multikey` over bytes. -/
def ed25519PublicKeyToMultikey (pk : Bytes) : String :=
  multibaseEncodeBase58btc (ed25519PubPrefix ++ pk)

/-- Does `pre` prefix `bs`? Port of `DID.Key.bytes_prefix_eq`. -/
def bytesPrefixEq : Bytes → Bytes → Bool
  | [], _ => true
  | p :: pt, b :: bt => p == b && bytesPrefixEq pt bt
  | _ :: _, [] => false

/-- Decode a Multikey and strip a given 2-byte multicodec prefix,
requiring exactly 32 key bytes after it (so 34 decoded bytes). -/
def multikeyToKey? (pre : Bytes) (mk : String) : Option Bytes :=
  match multibaseDecode? mk with
  | some bs => if bytesPrefixEq pre bs && bs.length == 34 then some (bs.drop 2) else none
  | none => none

/-- `z6Mk…` → the 32 raw Ed25519 public-key bytes. -/
def multikeyToEd25519PublicKey? (mk : String) : Option Bytes :=
  multikeyToKey? ed25519PubPrefix mk

/-- `z3u2…` → the 32 raw Ed25519 secret-key bytes. -/
def multikeyToEd25519SecretKey? (mk : String) : Option Bytes :=
  multikeyToKey? ed25519PrivPrefix mk

/-! ## `ByteArray` boundary -/

/-- Byte list → `ByteArray` (the FFI / hash boundary type). -/
def toByteArray (bs : Bytes) : ByteArray := ⟨⟨bs⟩⟩

/-- `ByteArray` → byte list. -/
def ofByteArray (a : ByteArray) : Bytes := a.data.toList

/-- Hex → `ByteArray`. -/
def byteArrayOfHex? (s : String) : Option ByteArray := (bytesOfHex? s).map toByteArray

/-- `ByteArray` → lowercase hex (agrees with `Crypto.bytesToHex`). -/
def hexOfByteArray (a : ByteArray) : String := hexOfBytes (ofByteArray a)

end L4Factoidal.VC.Multibase
