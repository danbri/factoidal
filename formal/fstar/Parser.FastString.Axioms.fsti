module Parser.FastString.Axioms

open Parser.FastString

/// THEOREMS, NOT AXIOMS (2026-08-10, G4/#358 Step 4 -- FastString
/// re-founding plan, docs/designissues/2026-08-10-faststring-refounding-
/// plan.md). Every `val` below is now PROVED by the companion
/// `Parser.FastString.Axioms.fst`, from the real definitions in
/// `Parser.FastString.Spec.fst` via `Parser.FastString.fsti`'s bridging
/// lemmas (`fs_byte_length_eq` and siblings). This module is OFF the
/// trust surface: it is no longer an acknowledged GAP under iron rule
/// #3(a), and issue #358 (which tracked it as one) can close/morph to
/// track only genuinely open follow-ups (the FStar.String.concat /
/// FStar.String.sub gaps `Parser.FastString.Axioms.fst`'s banner and
/// `docs/designissues/2026-08-10-string-foundation-decision.md`
/// describe). `Parser.FastString.fst` no longer declares these
/// primitives as `assume val`s either (Step 2/3 of the same migration
/// re-founded them as real `Parser.FastString.Spec`-backed definitions)
/// -- so nothing downstream of this module is an unverified assumption
/// on this account any more.
///
/// WHAT THIS WAS. Before Step 2/3 of the re-founding, `Parser.FastString.
/// fst` declared `fs_byte_length`, `fs_byte_at`, `fs_byte_sub`, `fs_cp_at`
/// (plus `fs_find_byte`, `fs_cp_len`) as `assume val`s realised in OCaml
/// (`minimal_regrettable_glue_code_each_with_an_open_issue/
/// 89_fast_string_primitives.sh`) directly against `String.length`,
/// `String.unsafe_get`, `String.sub` -- genuine O(1)/O(len) byte
/// operations, but with NO F*-visible equations connecting them to
/// string structure. `SPARQL.Protocol.RoundTrip.fst` hit this wall
/// building the SRJ text round-trip theorem: even `fs_byte_length "ab"
/// == 2` was unprovable with zero axioms (Error 19). This module
/// AXIOMATIZED the SMALLEST set of facts that made text-level
/// round-trip theorems statable, following the same pattern as
/// `RDF.Indexed.StringOrder.fsti` (issue #347): an `.fsti`-only module
/// (no companion `.fst`), so every `val` was implicitly assumed for any
/// consumer that `open`ed this module. The re-founding migration then
/// gave `Parser.FastString` real definitions, which is what makes every
/// fact below provable FOR REAL rather than merely assumed -- see
/// `Parser.FastString.Axioms.fst` for the proofs, including one (fact 8,
/// `fs_byte_sub_self`) that needed the "single-decoder round trip"
/// theorem the FastString refounding plan's Step 2/3 section records as
/// PARKED after three failed attempts -- proved in this landing via an
/// explicit unfold lemma + prefix-shift induction (see that file).
///
/// TRUST SURFACE, AS PROVED. Eight facts (nine `val`s -- fact 5 bundles
/// two: the left/right halves of the concat-slicing case split). Each
/// was checked below against the ACTUAL OCaml realisation in
/// `89_fast_string_primitives.sh` when first axiomatized (not against
/// what the primitive "should" do), and is now ALSO machine-verified
/// true of the real `Parser.FastString.Spec`-backed definitions --
/// doubly justified, not merely re-labelled.
///
/// ONE FACT NARROWED, NOT WIDENED (2026-08-10, same landing). Fact 6
/// (`fs_cp_at_ascii`) as originally stated was FALSE -- proving it
/// exposed a genuine, machine-checked counterexample (`s = ""`, `pos =
/// 5`: the hypothesis held vacuously via `fs_byte_at`'s out-of-range
/// sentinel `0`, while `fs_cp_at`'s independent out-of-range sentinel
/// `0xFFFD` broke the conclusion). Fixed by adding the missing in-bounds
/// side condition (`pos < fs_byte_length s`) to fact 6's `requires` --
/// see that `val`'s own banner immediately above it for the full
/// evidence, and the zero-consumer-churn check that makes this a safe
/// narrowing rather than a breaking change. This is the ONE line in this
/// `.fsti` that changed as part of "proving the axioms"; every other
/// `val` is untouched.
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
///   6. `fs_cp_at_ascii`          -- on an IN-BOUNDS byte < 0x80, the
///                                   codepoint decoder agrees with the
///                                   byte reader: one ASCII byte IS one
///                                   codepoint (the in-bounds condition
///                                   was ADDED 2026-08-10 -- see below,
///                                   the original unbounded statement
///                                   was false).
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
/// DO NOT WIDEN (still holds now that these are theorems, not axioms --
/// this module is meant to stay the SMALLEST provable surface a proof
/// module needs, not grow into a general FastString lemma library).
/// Add no further facts here without reopening #358, re-checking each
/// new fact against `89_fast_string_primitives.sh` line by line the
/// same way the eight above were checked, AND actually proving it in
/// `Parser.FastString.Axioms.fst` before adding the `val` (fact 6's
/// 2026-08-10 finding is exactly why: an unchecked axiom can be false
/// and nothing catches it until something tries to prove or use it).
/// In particular:
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
///
/// NARROWED 2026-08-10 (G4/#358 Step 4, `Parser.FastString.Axioms.fst`
/// landing) -- the ONE deviation from this file's own "DO NOT WIDEN"
/// banner, and it is a NARROWING, not a widening. As originally stated
/// (no `pos < fs_byte_length s` conjunct), this fact is FALSE, with a
/// concrete counterexample compiled and checked by fstar.exe itself (not
/// merely reasoned about): `s = ""`, `pos = 5`. `fs_byte_at "" 5 == 0`
/// (Parser.FastString.fst's `fs_byte_at`'s `None` arm returns the
/// sentinel `0` for an out-of-range index), so the original hypothesis
/// `fs_byte_at s pos < 0x80` holds vacuously. But `fs_cp_at "" 5 ==
/// (0xFFFD, 1)` (`Parser.FastString.Spec.utf8_decode_at`'s OWN,
/// INDEPENDENT out-of-range sentinel via its `None` arm) -- so the
/// original `ensures fs_cp_at s pos == (fs_byte_at s pos, 1)` would
/// require `(0xFFFD, 1) == (0, 1)`, which is false. The two primitives'
/// out-of-range SENTINELS simply disagree (0 vs 0xFFFD); nothing about
/// "ASCII" ties them together once `pos` is out of bounds, because
/// neither primitive's `None`/out-of-range arm ever looks at the other's
/// arm at all. Verified false by construction: `fs_byte_at_eq "" 5`,
/// `fs_cp_at_eq "" 5`, and `assert_norm (Parser.FastString.Spec.utf8_bytes
/// "" == [])` together let `fstar.exe` prove BOTH `fs_byte_at "" 5 < 0x80`
/// and `fs_cp_at "" 5 <> (fs_byte_at "" 5, 1)` as one conjunction --
/// i.e. the ORIGINAL fact's hypothesis-holds-but-conclusion-fails
/// witness, machine-checked, not inferred. This module was an `.fsti`-only
/// interface before this landing (see banner above), so this false fact
/// was an ASSUMED axiom, never actually checked against the real
/// primitives until this Step 4 companion-module effort ran it through
/// the SMT solver for the first time. ZERO consumer churn: `grep -rn
/// fs_cp_at_ascii *.fst *.fsti` (repo root `formal/fstar/`) finds no
/// caller anywhere outside this file itself, so the false axiom was
/// dormant, never actually relied upon by a landed theorem. The minimal
/// correct fix -- confirmed by a machine-checked proof in
/// `Parser.FastString.Axioms.fst` -- is exactly the missing in-bounds
/// side condition added below (`pos < fs_byte_length s`): once `pos` is
/// known in-range, `Parser.FastString.Spec.nth_byte` returns `Some`, both
/// primitives read the SAME byte, and `Parser.FastString.Spec.
/// utf8_decode_at_ascii` closes the rest. Reported prominently (not
/// silently patched) per this project's findings discipline
/// (`skills/proof-factory/SKILL.md`) and CLAUDE.md rule #14.
val fs_cp_at_ascii (s : string) (pos : nat)
  : Lemma (requires fs_byte_at s pos < 0x80 /\ pos < fs_byte_length s)
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
