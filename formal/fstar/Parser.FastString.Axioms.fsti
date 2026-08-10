module Parser.FastString.Axioms

open Parser.FastString

/// Specification axioms for `Parser.FastString`'s four byte/codepoint
/// primitives -- acknowledged GAP under iron rule #3(a), tracked by
/// GitHub issue #358.
///
/// WHY THIS EXISTS. `Parser.FastString.fst` declares `fs_byte_length`,
/// `fs_byte_at`, `fs_byte_sub`, `fs_cp_at` (plus `fs_find_byte`,
/// `fs_cp_len`) as `assume val`s realised in OCaml
/// (`minimal_regrettable_glue_code_each_with_an_open_issue/
/// 89_fast_string_primitives.sh`) directly against `String.length`,
/// `String.unsafe_get`, `String.sub` -- genuine O(1)/O(len) byte
/// operations, but with NO F*-visible equations connecting them to
/// string structure. `SPARQL.Protocol.RoundTrip.fst` hit this wall
/// building the SRJ text round-trip theorem: even
/// `fs_byte_length "ab" == 2` is unprovable with zero axioms (Error
/// 19, confirmed empirically both there and again while writing this
/// module -- see the probes this module's proofs are built from).
///
/// This module axiomatizes the SMALLEST set of facts that make
/// text-level round-trip theorems statable, following the same
/// pattern as `RDF.Indexed.StringOrder.fsti` (issue #347): an
/// `.fsti`-only module (no companion `.fst`), so every `val` below is
/// implicitly assumed for any consumer that `open`s this module, and
/// the assumption lives in exactly one named place instead of being
/// scattered as ad-hoc `assume`s in proof files.
///
/// TRUST SURFACE. Eight facts. Each is checked below against the ACTUAL
/// OCaml realisation in `89_fast_string_primitives.sh` (not against
/// what the primitive "should" do) -- an axiom that does not match
/// the realisation is a silent hole per iron rule #3(b), so none is
/// stated unless the OCaml body was read and matches line for line.
///
///   1. `fs_byte_length_empty`    -- length "" = 0.
///   2. `fs_byte_length_concat`   -- length (a ^ b) = length a + length b
///                                   (the length-homomorphism half of a
///                                   monoid homomorphism to nat; identity
///                                   is fact 1).
///   3. `fs_byte_length_ascii_singleton` -- a string whose ONE codepoint
///                                   is ASCII has byte length 1.
///   4. `fs_byte_at_concat`       -- indexing a concatenation reads from
///                                   the left operand below its length,
///                                   from the right operand (shifted)
///                                   at or above it.
///   5. `fs_byte_sub_concat_left` / `fs_byte_sub_concat_right` -- the
///                                   slicing analogue of (4), restricted
///                                   to ranges that lie wholly within one
///                                   operand (the range spanning the
///                                   join point is deliberately NOT
///                                   characterised -- narrower is safer,
///                                   and no current consumer needs it).
///   6. `fs_cp_at_ascii`          -- on a byte < 0x80, the codepoint
///                                   decoder agrees with the byte reader:
///                                   one ASCII byte IS one codepoint.
///   7. `fs_byte_at_ascii_singleton` -- the VALUE-level sibling of fact
///                                   3: for a one-ASCII-codepoint
///                                   string, the byte AT position 0 IS
///                                   that codepoint's numeric code.
///   8. `fs_byte_sub_self`        -- slicing a string from 0 across its
///                                   whole byte length returns the
///                                   string itself unchanged.
///
/// JUSTIFICATION AGAINST THE OCAML REALISATION (89_fast_string_primitives.sh)
/// --------------------------------------------------------------------------
///
/// `fs_byte_length s = Z.of_int (String.length s)`. OCaml's `String.length`
/// on native (non-jsoo) strings counts BYTES, and OCaml's `^` (used to
/// realise F*'s `strcat`/`op_Hat` -- `ulib/ml/app/Prims.ml`:
/// `let strcat x y = x ^ y`, `ulib/ml/app/FStar_String.ml`:
/// `let strcat s t = s ^ t`) is byte-level concatenation that copies `a`'s
/// bytes followed by `b`'s bytes with no reinterpretation. So
/// `String.length (a ^ b) = String.length a + String.length b` and
/// `String.length "" = 0` hold unconditionally of OCaml's string
/// semantics -- facts 1 and 2 are exact restatements of that, not
/// approximations.
///
/// `fs_byte_at s i = Char.code (String.unsafe_get s i)`. Because `a ^ b`
/// is byte-copy concatenation, `(a ^ b).[i]` is literally `a.[i]` for
/// `i < String.length a` and `b.[i - String.length a]` otherwise -- the
/// standard OCaml string-indexing-over-concatenation identity. Fact 4
/// restates it for `fs_byte_at`.
///
/// `fs_byte_sub s start len` clamps then calls `String.sub s start len`.
/// `String.sub` on a byte-copy concatenation restricted to a range wholly
/// inside one operand returns exactly that operand's own `String.sub` at
/// the (possibly shifted) offset -- again because concatenation performs
/// no byte reinterpretation. Facts 5a/5b restate the two single-operand
/// cases; the cross-boundary case is left unstated (see above).
///
/// `fs_cp_at` (via `fs_cp_at_impl`) begins with `if b0 < 0x80 then (b0, 1)`
/// where `b0 = Char.code (String.unsafe_get s p)` -- textually the same
/// expression `fs_byte_at` computes. Fact 6 is a direct restatement of
/// that first branch: on an ASCII lead byte, `fs_cp_at` returns exactly
/// `(fs_byte_at s pos, 1)`.
///
/// `fs_byte_length_ascii_singleton` needs one more link: a string literal
/// like `"a"` has to connect to `fs_byte_length s == 1` via SOME finite
/// witness of "this is one ASCII codepoint", since `fs_byte_length` has
/// no equation for `FStar.String.list_of_string`/`strlen` at all (they are
/// a completely separate opaque primitive pair -- ulib's own `strlen`
/// wraps `list_of_string`, itself unimplemented in `FStar.String.fsti`
/// and only reducible by the normalizer on CONCRETE literals). The
/// hypothesis `list_of_string s == [c]` is exactly that witness -- for a
/// literal like `"a"`, `list_of_string "a" == [FStar.Char.char_of_int 97]`
/// is provable by F*'s own normalizer with no help (confirmed empirically:
/// `let _ : Lemma (FStar.String.list_of_string "a" == [FStar.Char.char_of_int 97]) = ()`
/// verifies). One ASCII codepoint UTF-8-encodes to exactly one byte
/// (RFC 3629 sec. 3, table): the OCaml side of a single-ASCII-character
/// F* string literal IS the one-byte OCaml string, so `fs_byte_length`
/// on it is genuinely `1`, not merely plausible.
///
/// DO NOT WIDEN. Add no further axioms here without reopening #358 and
/// re-checking each new fact against `89_fast_string_primitives.sh` line
/// by line, the same way the six above were checked. In particular:
/// no axiom about `fs_find_byte`, `fs_cp_len`, or the boundary-spanning
/// `fs_byte_sub` case -- none was needed by the round-trip work that
/// opened #358, and each would need its own realisation check. Anything
/// derivable from these six (e.g. length of a two-codepoint ASCII
/// literal, byte position after consuming a known prefix) must be
/// PROVED in a consumer module -- see `Parser.FastString.RoundTripLemmas.fst`
/// for the two the round-trip work needs.
///
/// FACTS 7/8 PROMOTED (owner authorization 2026-08-09, verbatim "Yes
/// approve the two FastString axioms", issue #358 comment of that date).
/// Found continuing #358 toward the SRJ TEXT-level round trip, session
/// 2026-08-09: `SPARQL.Protocol.RoundTrip.fst`'s literal-lexing step
/// ("parse of a quoted escape-free string literal consumes exactly its
/// bytes and yields the string") needs the recursive-descent scanner to
/// know what `fs_byte_at`/`fs_byte_sub` actually RETURN for a given
/// string -- and facts 1-6 are all *relational* (concat homomorphism,
/// index/slice-into-concat, cp_at agreeing with an ALREADY-KNOWN byte_at
/// value); none of them bottoms out at a base case tying a return value
/// to string content. Confirmed empirically before either fact below was
/// added (probes run and discarded, not committed -- each failed Error
/// 19, "Could not prove post-condition", exactly like the `fs_byte_length
/// "ab" == 2` probe in the FINDING above):
///   `let _ : Lemma (fs_byte_at "a" 0 == 97) = ()`                    -- FAILED
///   `let _ (s:string) : Lemma (fs_byte_sub s 0 (fs_byte_length s) == s) = ()` -- FAILED
/// Without fact 7, no branch of `json_parse_value` / `json_parse_string`
/// / `json_parse_object` / `json_parse_array` is provable at all -- every
/// one of them dispatches on the concrete VALUE `fs_byte_at` returns
/// (is this byte `"`? `{`? `:`? `,`? a control character?), and facts 1-6
/// supply that value for no string whatsoever. This blocked step 1 of the
/// text-bridge chain outright, before framing (step 2) or composition
/// (step 3) could even be attempted -- see `SPARQL.Protocol.RoundTrip.fst`'s
/// banner for how the promoted facts are used, and for a NEW finding from
/// the SAME session: a separate wall, past the JSON string body, in
/// `FStar.String.concat` (a different module's primitive, out of scope for
/// this file's eight-fact trust surface) that still blocks the literal
/// `json_parse_string` theorem even with all eight facts landed.

/// Fact 1: the empty string has zero bytes.
val fs_byte_length_empty (_:unit)
  : Lemma (fs_byte_length "" == 0)

/// Fact 2: `fs_byte_length` is a monoid homomorphism from `(string, ^, "")`
/// to `(nat, +, 0)` on the length side (identity element handled by fact 1).
val fs_byte_length_concat (a b : string)
  : Lemma (fs_byte_length (a ^ b) == fs_byte_length a + fs_byte_length b)

/// Fact 3: a string whose codepoint list is a single ASCII character has
/// byte length exactly 1.
val fs_byte_length_ascii_singleton (s : string) (c : FStar.Char.char)
  : Lemma (requires FStar.String.list_of_string s == [c] /\
                    FStar.Char.int_of_char c < 128)
          (ensures  fs_byte_length s == 1)

/// Fact 4: reading a byte from a concatenation reads from the left
/// operand below its length, from the right operand (index shifted by
/// the left operand's length) at or above it.
val fs_byte_at_concat (a b : string) (i : nat)
  : Lemma (requires i < fs_byte_length (a ^ b))
          (ensures  (if i < fs_byte_length a
                     then fs_byte_at (a ^ b) i == fs_byte_at a i
                     else fs_byte_at (a ^ b) i == fs_byte_at b (i - fs_byte_length a)))

/// Fact 5a: slicing a concatenation over a range wholly inside the left
/// operand is the same as slicing the left operand directly.
val fs_byte_sub_concat_left (a b : string) (start len : nat)
  : Lemma (requires start + len <= fs_byte_length a)
          (ensures  fs_byte_sub (a ^ b) start len == fs_byte_sub a start len)

/// Fact 5b: slicing a concatenation over a range wholly inside the right
/// operand is the same as slicing the right operand at the shifted
/// offset. The range spanning the join point (start < len a < start+len)
/// is deliberately left uncharacterised.
val fs_byte_sub_concat_right (a b : string) (start len : nat)
  : Lemma (requires start >= fs_byte_length a /\ start + len <= fs_byte_length (a ^ b))
          (ensures  fs_byte_sub (a ^ b) start len == fs_byte_sub b (start - fs_byte_length a) len)

/// Fact 6: on an ASCII lead byte, the codepoint decoder agrees with the
/// byte reader -- one ASCII byte is one codepoint of advance 1.
val fs_cp_at_ascii (s : string) (pos : nat)
  : Lemma (requires fs_byte_at s pos < 0x80)
          (ensures  fs_cp_at s pos == (fs_byte_at s pos, 1))

/// Fact 7: the VALUE-level sibling of fact 3 (which only gives LENGTH):
/// for a one-ASCII-codepoint string, the byte at position 0 IS that
/// codepoint's numeric code. Justification (checked against
/// `89_fast_string_primitives.sh`, same shape as fact 3's): `fs_byte_at
/// s 0 = Char.code (String.unsafe_get s 0)`; for a one-ASCII-codepoint
/// literal the OCaml string IS the one-byte UTF-8 encoding, so that
/// byte's code equals `int_of_char c`.
val fs_byte_at_ascii_singleton (s : string) (c : FStar.Char.char)
  : Lemma (requires FStar.String.list_of_string s == [c] /\
                    FStar.Char.int_of_char c < 128)
          (ensures  fs_byte_at s 0 == FStar.Char.int_of_char c)

/// Fact 8: self-recovery of a full-length slice -- slicing a string
/// from 0 across its whole byte length returns the string itself
/// unchanged. Justification (checked against
/// `89_fast_string_primitives.sh`): `fs_byte_sub s 0 (fs_byte_length s)`
/// clamps to `String.sub s 0 (String.length s)`, an OCaml full-string
/// copy, structurally equal to `s`.
val fs_byte_sub_self (s : string)
  : Lemma (fs_byte_sub s 0 (fs_byte_length s) == s)
