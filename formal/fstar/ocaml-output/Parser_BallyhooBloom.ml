open Prims
type bloom_bits = Prims.bool Prims.list
type predicate_bloom =
  {
  pb_bit_count: Prims.nat ;
  pb_hash_count: Prims.nat ;
  pb_bits: bloom_bits }
let __proj__Mkpredicate_bloom__item__pb_bit_count
  (projectee : predicate_bloom) : Prims.nat=
  match projectee with
  | { pb_bit_count; pb_hash_count; pb_bits;_} -> pb_bit_count
let __proj__Mkpredicate_bloom__item__pb_hash_count
  (projectee : predicate_bloom) : Prims.nat=
  match projectee with
  | { pb_bit_count; pb_hash_count; pb_bits;_} -> pb_hash_count
let __proj__Mkpredicate_bloom__item__pb_bits (projectee : predicate_bloom) :
  bloom_bits=
  match projectee with | { pb_bit_count; pb_hash_count; pb_bits;_} -> pb_bits
let rec make_false_bits (n : Prims.nat) : bloom_bits=
  if n = Prims.int_zero
  then []
  else false :: (make_false_bits (n - Prims.int_one))
let bloom_empty (bit_count : Prims.nat) (hash_count : Prims.nat) :
  predicate_bloom=
  {
    pb_bit_count = bit_count;
    pb_hash_count = hash_count;
    pb_bits = (make_false_bits bit_count)
  }
let rec list_nth_bool (bits : bloom_bits) (idx : Prims.nat) : Prims.bool=
  match bits with
  | [] -> false
  | b::rest ->
      if idx = Prims.int_zero
      then b
      else list_nth_bool rest (idx - Prims.int_one)
let rec list_set_bool (bits : bloom_bits) (idx : Prims.nat) : bloom_bits=
  match bits with
  | [] -> []
  | b::rest ->
      if idx = Prims.int_zero
      then true :: rest
      else b :: (list_set_bool rest (idx - Prims.int_one))
let rec list_or_bool (xs : bloom_bits) (ys : bloom_bits) : bloom_bits=
  match (xs, ys) with
  | ([], []) -> []
  | (x::xs', y::ys') -> (x || y) :: (list_or_bool xs' ys')
  | (uu___, uu___1) -> []
let rec all_true_at_positions (bits : bloom_bits)
  (positions : Prims.nat Prims.list) : Prims.bool=
  match positions with
  | [] -> true
  | p::rest -> (list_nth_bool bits p) && (all_true_at_positions bits rest)
let rec set_true_at_positions (bits : bloom_bits)
  (positions : Prims.nat Prims.list) : bloom_bits=
  match positions with
  | [] -> bits
  | p::rest -> set_true_at_positions (list_set_bool bits p) rest
let rec reduce_mod (n : Prims.nat) (m : Prims.nat) (fuel : Prims.nat) :
  Prims.nat=
  if m = Prims.int_zero
  then Prims.int_zero
  else
    if fuel = Prims.int_zero
    then Prims.int_zero
    else if n < m then n else reduce_mod (n - m) m (fuel - Prims.int_one)
let rec hash_string_mod_from (s : Prims.string) (seed : Prims.nat)
  (idx : Prims.nat) (fuel : Prims.nat) (m : Prims.nat) : Prims.nat=
  if m = Prims.int_zero
  then Prims.int_zero
  else
    if fuel = Prims.int_zero
    then seed
    else
      if idx >= (FStar_String.strlen s)
      then seed
      else
        (let code = FStar_Char.int_of_char (FStar_String.index s idx) in
         let raw = ((seed + code) + idx) + Prims.int_one in
         let next = reduce_mod raw m (raw + Prims.int_one) in
         hash_string_mod_from s next (idx + Prims.int_one)
           (fuel - Prims.int_one) m)
let hash_string_mod (s : Prims.string) (seed : Prims.nat) (m : Prims.nat) :
  Prims.nat=
  hash_string_mod_from s seed Prims.int_zero
    ((FStar_String.strlen s) + Prims.int_one) m
let bloom_position (value : Prims.string) (bit_count : Prims.nat)
  (i : Prims.nat) : Prims.nat=
  if bit_count = Prims.int_zero
  then Prims.int_zero
  else
    (let h1 = hash_string_mod value (Prims.of_int (17)) bit_count in
     let h2 = hash_string_mod value (Prims.of_int (131)) bit_count in
     let raw = ((h1 + i) + h2) + Prims.int_one in
     reduce_mod raw bit_count (raw + Prims.int_one))
let rec bloom_positions_from (value : Prims.string) (bit_count : Prims.nat)
  (i : Prims.nat) (k : Prims.nat) : Prims.nat Prims.list=
  if k = Prims.int_zero
  then []
  else (bloom_position value bit_count i) ::
    (bloom_positions_from value bit_count (i + Prims.int_one)
       (k - Prims.int_one))
let bloom_positions (value : Prims.string) (bit_count : Prims.nat)
  (hash_count : Prims.nat) : Prims.nat Prims.list=
  bloom_positions_from value bit_count Prims.int_zero hash_count
let bloom_insert (bf : predicate_bloom) (value : Prims.string) :
  predicate_bloom=
  let positions = bloom_positions value bf.pb_bit_count bf.pb_hash_count in
  {
    pb_bit_count = (bf.pb_bit_count);
    pb_hash_count = (bf.pb_hash_count);
    pb_bits = (set_true_at_positions bf.pb_bits positions)
  }
let bloom_might_contain (bf : predicate_bloom) (value : Prims.string) :
  Prims.bool=
  let positions = bloom_positions value bf.pb_bit_count bf.pb_hash_count in
  all_true_at_positions bf.pb_bits positions
let bloom_union (a : predicate_bloom) (b : predicate_bloom) :
  predicate_bloom FStar_Pervasives_Native.option=
  if (a.pb_bit_count = b.pb_bit_count) && (a.pb_hash_count = b.pb_hash_count)
  then
    FStar_Pervasives_Native.Some
      {
        pb_bit_count = (a.pb_bit_count);
        pb_hash_count = (a.pb_hash_count);
        pb_bits = (list_or_bool a.pb_bits b.pb_bits)
      }
  else FStar_Pervasives_Native.None
let bloom_predicate_present (bf : predicate_bloom)
  (p : RDF_Graph_Executable.wf_iri) : Prims.bool= bloom_might_contain bf p
