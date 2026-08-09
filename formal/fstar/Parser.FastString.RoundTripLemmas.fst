module Parser.FastString.RoundTripLemmas

open Parser.FastString
open Parser.FastString.Axioms

(** ======================================================================== **)
(** Proved consequences of `Parser.FastString.Axioms` -- issue #358.         **)
(**                                                                          **)
(** NO new axioms below: everything here is a `let`/`Lemma` proved from the  **)
(** six facts in `Parser.FastString.Axioms.fsti` (plus ordinary F* string    **)
(** literal reduction, e.g. `"a" ^ "b" == "ab"`, which the normalizer        **)
(** already handles with no help -- confirmed empirically while writing      **)
(** this module).                                                            **)
(** ======================================================================== **)

/// Demo consequence requested by #358: the length-homomorphism + ASCII-
/// singleton axioms are enough to compute a concrete literal's byte
/// length, something that was flatly unprovable before this module
/// (`SPARQL.Protocol.RoundTrip.fst`'s banner records the same fact
/// failing with Error 19 against the bare `assume val`s).
let demo_fs_byte_length_ab ()
  : Lemma (fs_byte_length "ab" == 2)
  =
  fs_byte_length_ascii_singleton "a" (FStar.Char.char_of_int 97);
  fs_byte_length_ascii_singleton "b" (FStar.Char.char_of_int 98);
  fs_byte_length_concat "a" "b";
  assert ("a" ^ "b" == "ab")

/// What the SRJ text round-trip needs (per `SPARQL.Protocol.RoundTrip.fst`'s
/// banner, "the missing bridging fact" category): once a parser has
/// consumed a known `prefix` of the input, reading byte `i` of whatever
/// comes next (`rest`) at the shifted physical position
/// `fs_byte_length prefix + i` agrees with reading byte `i` directly out
/// of `rest`. This is the fact a recursive-descent scanner over
/// `prefix ^ rest` relies on implicitly every time it advances its
/// position counter past a literal it just matched.
let lemma_byte_at_after_prefix (prefix rest : string) (i : nat)
  : Lemma (requires i < fs_byte_length rest)
          (ensures  fs_byte_at (prefix ^ rest) (fs_byte_length prefix + i) == fs_byte_at rest i)
  =
  fs_byte_length_concat prefix rest;
  fs_byte_at_concat prefix rest (fs_byte_length prefix + i)
