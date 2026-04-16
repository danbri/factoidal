module Parser.BallyhooBloom

open FStar.List.Tot
open FStar.String
open RDF.Graph.Executable

// BallyhooBloom is an experimental F* representation of the Bloom-style
// summary structures we keep next to HDT graph artifacts. It is intended to
// cover in-memory use, sidecar reasoning, and subset rollups without relying
// on external Bloom implementations.

type bloom_bits = list bool

noeq type predicate_bloom = {
  pb_bit_count  : nat;
  pb_hash_count : nat;
  pb_bits       : bloom_bits;
}

let rec make_false_bits (n : nat) : Tot bloom_bits (decreases n) =
  if n = 0 then []
  else false :: make_false_bits (n - 1)

let bloom_empty (bit_count hash_count : nat) : predicate_bloom = {
  pb_bit_count = bit_count;
  pb_hash_count = hash_count;
  pb_bits = make_false_bits bit_count;
}

let rec list_nth_bool (bits : bloom_bits) (idx : nat) : Tot bool (decreases bits) =
  match bits with
  | [] -> false
  | b :: rest -> if idx = 0 then b else list_nth_bool rest (idx - 1)

let rec list_set_bool (bits : bloom_bits) (idx : nat) : Tot bloom_bits (decreases bits) =
  match bits with
  | [] -> []
  | b :: rest ->
    if idx = 0 then true :: rest
    else b :: list_set_bool rest (idx - 1)

let rec list_or_bool (xs ys : bloom_bits) : Tot bloom_bits (decreases xs) =
  match xs, ys with
  | [], [] -> []
  | x :: xs', y :: ys' -> (x || y) :: list_or_bool xs' ys'
  | _, _ -> []

let rec all_true_at_positions (bits : bloom_bits) (positions : list nat)
  : Tot bool (decreases positions) =
  match positions with
  | [] -> true
  | p :: rest -> list_nth_bool bits p && all_true_at_positions bits rest

let rec set_true_at_positions (bits : bloom_bits) (positions : list nat)
  : Tot bloom_bits (decreases positions) =
  match positions with
  | [] -> bits
  | p :: rest -> set_true_at_positions (list_set_bool bits p) rest

let rec reduce_mod (n m fuel : nat) : Tot nat (decreases fuel) =
  if m = 0 then 0
  else if fuel = 0 then 0
  else if n < m then n
  else reduce_mod (n - m) m (fuel - 1)

let rec hash_string_mod_from (s : string) (seed : nat) (idx : nat) (fuel : nat) (m : nat)
  : Tot nat (decreases fuel) =
  if m = 0 then 0
  else if fuel = 0 then seed
  else if idx >= String.length s then seed
  else
    let code = FStar.Char.int_of_char (String.index s idx) in
    let raw = seed + code + idx + 1 in
    let next = reduce_mod raw m (raw + 1) in
    hash_string_mod_from s next (idx + 1) (fuel - 1) m

let hash_string_mod (s : string) (seed : nat) (m : nat) : nat =
  hash_string_mod_from s seed 0 (String.length s + 1) m

let bloom_position (value : string) (bit_count : nat) (i : nat) : nat =
  if bit_count = 0 then 0
  else
    let h1 = hash_string_mod value 17 bit_count in
    let h2 = hash_string_mod value 131 bit_count in
    let raw = h1 + i + h2 + 1 in
    reduce_mod raw bit_count (raw + 1)

let rec bloom_positions_from (value : string) (bit_count : nat) (i : nat) (k : nat)
  : Tot (list nat) (decreases k) =
  if k = 0 then []
  else bloom_position value bit_count i :: bloom_positions_from value bit_count (i + 1) (k - 1)

let bloom_positions (value : string) (bit_count hash_count : nat) : list nat =
  bloom_positions_from value bit_count 0 hash_count

let bloom_insert (bf : predicate_bloom) (value : string) : predicate_bloom =
  let positions = bloom_positions value bf.pb_bit_count bf.pb_hash_count in
  { bf with pb_bits = set_true_at_positions bf.pb_bits positions }

let bloom_might_contain (bf : predicate_bloom) (value : string) : bool =
  let positions = bloom_positions value bf.pb_bit_count bf.pb_hash_count in
  all_true_at_positions bf.pb_bits positions

let bloom_union (a b : predicate_bloom) : option predicate_bloom =
  if a.pb_bit_count = b.pb_bit_count && a.pb_hash_count = b.pb_hash_count
  then Some {
    pb_bit_count = a.pb_bit_count;
    pb_hash_count = a.pb_hash_count;
    pb_bits = list_or_bool a.pb_bits b.pb_bits;
  }
  else None

let bloom_predicate_present (bf : predicate_bloom) (p : wf_iri) : bool =
  bloom_might_contain bf p
