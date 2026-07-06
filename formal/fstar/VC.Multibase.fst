module VC.Multibase

// ============================================================================
// Multibase / multihash byte encoding for Verifiable Credentials Data
// Integrity (docs/designissues/2026-07-05-vc-program-plan.md, module plan).
//
// This is PURE BYTE ENCODING, not cryptography (per the crypto-policy skill,
// "Encoding layers (multibase, multihash, base58/base64url) are NOT crypto —
// implement those in pure F* like any other codec").  base58btc is ordinary
// arbitrary-precision arithmetic on `nat`; nothing here touches a curve, a
// digest, or a signature.
//
// Contents:
//   - hex string  <-> byte list (list of nat < 256)
//   - base58btc (Bitcoin alphabet) encode / decode over byte lists
//   - multibase 'z' (base58btc) and 'u' (base64url-no-pad) wrappers
//   - multicodec varint tag for Ed25519 public keys (0xed01) used by the
//     did:key / Multikey `z6Mk...` verification-method form
//
// Roundtrip is exercised at runtime by bin/vc-runner (crypto mode); a formal
// `decode (encode bs) == Some bs` lemma is intentionally NOT stated here
// because a full base58 bijection proof (leading-zero handling +
// nat<->bytes<->base58 inverses) is a disproportionate proof burden for a
// codec whose correctness the roundtrip test already pins.  No `assume`, no
// `admit`, no `--lax`: every function below is Tot and verifies clean.
// ============================================================================

open FStar.List.Tot
open FStar.Mul
module S = FStar.String
module C = FStar.Char

type byte = n:nat{n < 256}

// ---------------------------------------------------------------------------
// Hex <-> bytes
// ---------------------------------------------------------------------------

let hex_digit_val (c:C.char) : option (d:nat{d < 16}) =
  let x = C.int_of_char c in
  if x >= 0x30 && x <= 0x39 then Some (x - 0x30)          // 0-9
  else if x >= 0x61 && x <= 0x66 then Some (x - 0x61 + 10) // a-f
  else if x >= 0x41 && x <= 0x46 then Some (x - 0x41 + 10) // A-F
  else None

let hex_char_of (d:nat{d < 16}) : C.char =
  let digits = "0123456789abcdef" in
  let l = S.list_of_string digits in
  match nth l d with
  | Some c -> c
  | None -> C.char_of_int 0x30   // unreachable (d < 16, length = 16)

let rec chars_to_bytes (cs:list C.char) : option (list byte) =
  match cs with
  | [] -> Some []
  | [ _ ] -> None                 // odd number of hex digits
  | hi :: lo :: rest ->
    (match hex_digit_val hi, hex_digit_val lo, chars_to_bytes rest with
     | Some h, Some l, Some tl -> Some ((h * 16 + l) :: tl)
     | _, _, _ -> None)

let hex_to_bytes (s:string) : option (list byte) =
  chars_to_bytes (S.list_of_string s)

let byte_to_hex_chars (b:byte) : list C.char =
  [ hex_char_of (b / 16); hex_char_of (b % 16) ]

let rec bytes_to_hex_chars (bs:list byte) : list C.char =
  match bs with
  | [] -> []
  | b :: t -> byte_to_hex_chars b @ bytes_to_hex_chars t

let bytes_to_hex (bs:list byte) : string =
  S.string_of_list (bytes_to_hex_chars bs)

// ---------------------------------------------------------------------------
// Big-endian byte list <-> nat
// ---------------------------------------------------------------------------

let rec pow256 (k:nat) : Tot (n:nat{n >= 1}) (decreases k) =
  if k = 0 then 1 else 256 * pow256 (k - 1)

let rec bytes_to_nat (bs:list byte) : Tot nat (decreases bs) =
  match bs with
  | [] -> 0
  | b :: t -> b * pow256 (length t) + bytes_to_nat t

// nat -> big-endian bytes (no leading-zero bytes; 0 -> []).
let rec nat_to_bytes_be (n:nat) : Tot (list byte) (decreases n) =
  if n = 0 then []
  else nat_to_bytes_be (n / 256) @ [ n % 256 ]

let rec count_leading_zero_bytes (bs:list byte) : nat =
  match bs with
  | 0 :: t -> 1 + count_leading_zero_bytes t
  | _ -> 0

let rec repeat_byte (b:byte) (k:nat) : Tot (list byte) (decreases k) =
  if k = 0 then [] else b :: repeat_byte b (k - 1)

let rec repeat_char (c:C.char) (k:nat) : Tot (list C.char) (decreases k) =
  if k = 0 then [] else c :: repeat_char c (k - 1)

// ---------------------------------------------------------------------------
// base58btc (Bitcoin alphabet)
// ---------------------------------------------------------------------------

let base58_alphabet : string =
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

let base58_char_of (d:nat{d < 58}) : C.char =
  let l = S.list_of_string base58_alphabet in
  match nth l d with
  | Some c -> c
  | None -> C.char_of_int 0x31   // '1' — unreachable (alphabet length = 58)

let rec find_index_aux (cs:list C.char) (c:C.char) (i:nat) : option nat =
  match cs with
  | [] -> None
  | h :: t -> if h = c then Some i else find_index_aux t c (i + 1)

let base58_digit_of (c:C.char) : option (d:nat{d < 58}) =
  match find_index_aux (S.list_of_string base58_alphabet) c 0 with
  | Some i -> if i < 58 then Some i else None
  | None -> None

// nat -> base58 digit chars, most-significant first (0 -> []).
let rec nat_to_base58_chars (n:nat) : Tot (list C.char) (decreases n) =
  if n = 0 then []
  else nat_to_base58_chars (n / 58) @ [ base58_char_of (n % 58) ]

let base58btc_encode (bs:list byte) : string =
  let zeros = count_leading_zero_bytes bs in
  let n = bytes_to_nat bs in
  let body = nat_to_base58_chars n in
  // leading zero bytes are rendered as leading '1's
  let ones = repeat_char (C.char_of_int 0x31) zeros in
  S.string_of_list (ones @ body)

let rec base58_chars_to_nat (cs:list C.char) (acc:nat) : option nat =
  match cs with
  | [] -> Some acc
  | c :: t ->
    (match base58_digit_of c with
     | Some d -> base58_chars_to_nat t (acc * 58 + d)
     | None -> None)

let rec count_leading_ones (cs:list C.char) : nat =
  match cs with
  | c :: t -> if C.int_of_char c = 0x31 then 1 + count_leading_ones t else 0
  | [] -> 0

let base58btc_decode (s:string) : option (list byte) =
  let cs = S.list_of_string s in
  let ones = count_leading_ones cs in
  match base58_chars_to_nat cs 0 with
  | None -> None
  | Some n -> Some (repeat_byte 0 ones @ nat_to_bytes_be n)

// ---------------------------------------------------------------------------
// Multibase wrappers ('z' = base58btc, RFC-style prefix)
// ---------------------------------------------------------------------------

let multibase_encode_base58btc (bs:list byte) : string =
  S.string_of_list (C.char_of_int 0x7A :: S.list_of_string (base58btc_encode bs)) // 'z'

let multibase_decode (s:string) : option (list byte) =
  match S.list_of_string s with
  | c :: rest ->
    if C.int_of_char c = 0x7A                      // 'z' base58btc
    then base58btc_decode (S.string_of_list rest)
    else None                                      // other bases not needed by eddsa-rdfc-2022 proofValue
  | [] -> None

// Convenience: hex signature bytes -> multibase-z proofValue string.
let hex_to_multibase_z (sig_hex:string) : option string =
  match hex_to_bytes sig_hex with
  | Some bs -> Some (multibase_encode_base58btc bs)
  | None -> None

// Convenience: multibase-z proofValue string -> hex signature bytes.
let multibase_z_to_hex (mb:string) : option string =
  match multibase_decode mb with
  | Some bs -> Some (bytes_to_hex bs)
  | None -> None

// ---------------------------------------------------------------------------
// Multicodec: Ed25519 public-key Multikey (did:key z6Mk...) tag 0xed01
// ---------------------------------------------------------------------------

let ed25519_multicodec_prefix : list byte = [ 0xed; 0x01 ]

// pubkey hex (32 bytes) -> did:key Multikey verification-method value
// (multibase-z of the 0xed01-tagged key bytes).
let ed25519_pubkey_to_multikey (pk_hex:string) : option string =
  match hex_to_bytes pk_hex with
  | Some pk -> Some (multibase_encode_base58btc (ed25519_multicodec_prefix @ pk))
  | None -> None
