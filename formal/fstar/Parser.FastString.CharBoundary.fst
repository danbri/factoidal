module Parser.FastString.CharBoundary

// ============================================================================
// U+D7FF boundary escape hatch -- split out of Parser.FastString by the
// Step 2/3 re-founding (docs/designissues/2026-08-10-faststring-refounding-
// plan.md). unsafe_char_of_d7ff is the SOLE assume val surviving that
// migration -- every other Parser.FastString primitive (fs_byte_length,
// fs_byte_at, fs_byte_sub, fs_find_byte, fs_cp_at, fs_cp_len) now has a real
// Parser.FastString.Spec-backed definition. This one cannot: it exists
// because `FStar.Char.char_of_int` is typed
// `i: nat{i < 0xd7ff \/ (i >= 0xe000 /\ i <= 0x10ffff)}` -- the STRICT `<`
// excludes U+D7FF, which IS a valid Unicode scalar (the surrogate gap is
// U+D800..U+DFFF inclusive, not D7FF..DFFF). No F* term can inhabit
// `i:int{i = 0xD7FF} -> FStar.Char.char` without either violating that
// precondition or reaching for an escape hatch (`admit`/`magic`), both
// forbidden by iron rule #10. See Parser.FastString.fst's original 2026-05-11
// banner (issue #68) for the full history; that text is preserved verbatim
// in this module below.
//
// WHY A SEPARATE MODULE (not just `assume val` inside Parser.FastString.fst
// itself, as before). Parser.FastString now carries a REAL `.fsti`
// (Parser.FastString.fsti) that makes its six primitives opaque to
// consumers' SMT contexts (the whole point of the Step 2/3 re-founding).
// F*'s interface-conformance rule requires every `val` an `.fsti` declares
// to have an actual `let`-implementation in the matching `.fst` --
// `assume val` in the `.fst` does NOT satisfy an `.fsti`'s `val` (confirmed
// empirically: a minimal two-file probe with `val f` in the `.fsti` and
// `assume val f` in the `.fst` fails with Error 98, "Some interface
// elements were not implemented"). An axiom therefore cannot live directly
// inside a module that also carries its own restrictive `.fsti`.
//
// The fix is the standard F* idiom for exactly this shape: a small
// `.fst`-only companion module (no `.fsti` of its own, so its `val` is
// implicitly-assumed the same way `Parser.FastString.Axioms.fsti` already
// is elsewhere in this tree) holding just the one axiom, `include`d into
// `Parser.FastString.fsti`. `include` re-exports `unsafe_char_of_d7ff`
// under the `Parser.FastString.` namespace -- `Parser.NTriples.fst`'s
// existing call site `Parser.FastString.unsafe_char_of_d7ff cp` keeps
// compiling completely unchanged (verified with a standalone F* probe
// before landing this, same include-and-qualify shape). No new SMT
// assumption is introduced beyond the ONE this module already carried
// before the split; it has simply moved to its own file, and the OCaml
// realisation patch (below) moves with it.
//
// OCAML REALISATION: `minimal_regrettable_glue_code_each_with_an_open_issue/
// 89_fast_string_primitives.sh` now targets `Parser_FastString_CharBoundary.ml`
// (this module's extraction output) for the one-line body -- in the OCaml
// runtime `FStar_Char.char` is just `int` and `char_of_int = Z.to_int`, no
// runtime check at all (`/root/.opam/fstar/lib/fstar/ulib/ml/app/FStar_Char.ml`),
// so the realisation is `let unsafe_char_of_d7ff (_ : Z.t) : FStar_Char.char
// = 0xD7FF`.
//
// Tracking: docs/designissues/2026-05-10-issue-68-options.md (subagent
// report). Optional upstream-track suggestion: file an F* issue against
// `ulib/FStar.Char.fsti` lines 38 and 57 -- both should read `<= 0xd7ff`.
// We don't block on it.
assume val unsafe_char_of_d7ff : i:int{i = 0xD7FF} -> Tot FStar.Char.char
