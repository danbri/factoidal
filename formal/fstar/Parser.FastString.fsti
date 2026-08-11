module Parser.FastString

// ============================================================================
// Parser.FastString interface -- Step 2/3 of the FastString re-founding
// migration (docs/designissues/2026-08-10-faststring-refounding-plan.md).
//
// PURPOSE. Before this file existed, Parser.FastString.fst had no `.fsti`
// at all: its six hot-path primitives (fs_byte_length, fs_byte_at,
// fs_byte_sub, fs_find_byte, fs_cp_at, fs_cp_len) were bare `assume val`s,
// which are OPAQUE to every consumer's SMT context by construction -- there
// is no body to unfold, so nothing about their behaviour leaks into a
// caller's proof obligations beyond the declared type.
//
// Step 2 replaces those six `assume val`s with real, Parser.FastString.Spec-
// backed DEFINITIONS in Parser.FastString.fst (so the module is no longer
// carrying six acknowledged gaps under iron rule #3(a) -- it is now a real
// spec, with the fast OCaml returning in Step 3 as a rule-11(b) Option-B
// realisation). Giving them real bodies would, WITHOUT this `.fsti`, make
// them transparently unfoldable by every one of the 31 consumer modules
// that `open Parser.FastString` -- exactly the fuel-blowup risk the
// migration plan's Risks section names ("`.fsti` opacity against verify-
// time fuel blowups (#273's verify-time analogue)"). This file is what
// keeps them opaque again: same names, same signatures, no bodies, so
// every consumer's SMT context sees exactly what it saw before this
// migration (nothing) unless it explicitly invokes one of the bridging
// lemmas below.
//
// SAME NAMES, SAME SIGNATURES. Every `val` below is copied byte-for-byte
// from the `assume val` it replaces in the pre-migration
// Parser.FastString.fst (lines 50-158 there) -- the 31 consumer modules
// that reference `Parser.FastString.fs_*` compile completely unchanged.
//
// unsafe_char_of_d7ff: re-exported via `include Parser.FastString.
// CharBoundary` rather than declared directly here -- see that module's
// banner for why an assume val cannot live in a module that also carries
// a restrictive `.fsti` of its own, and why `include` is the correct F*
// idiom for this shape (verified via a standalone probe before landing).
// The `Parser.FastString.unsafe_char_of_d7ff` qualified name Parser.
// NTriples.fst already uses keeps resolving unchanged.
include Parser.FastString.CharBoundary

// ----------------------------------------------------------------------
// The six re-founded primitives (Spec-backed `let`s in the .fst; opaque
// here). See Parser.FastString.fst's own banner for the cost model --
// unchanged from the pre-migration doc, since Step 3's OCaml realisation
// patch restores the same O(1)/O(len) shapes.
// ----------------------------------------------------------------------

val fs_byte_length : string -> nat

val fs_byte_at : s:string -> i:nat -> n:nat{n < 256}

val fs_byte_sub : s:string -> start:nat -> len:nat -> string

val fs_find_byte : s:string -> b:nat -> start:nat -> nat

val fs_cp_at : s:string -> pos:nat -> nat & nat

val fs_cp_len : s:string -> pos:nat -> nat

// ----------------------------------------------------------------------
// Spec twins (rule-11(b) Option-B pattern, #g4-faststring-step23).
//
// Each `fs_*_spec` is an INDEPENDENT F*-verified function computing the
// exact same Parser.FastString.Spec formula as its `fs_*` sibling, under
// its own name. They exist so the Step 3 OCaml realisation patch
// (experimental_ocaml_glue/) can override `fs_*` with today's fast OCaml
// body while `fs_*_spec` stays reachable and unmodified -- the equivalence
// test (tests/unit/parser_fast_string_equivalence.ml) links against BOTH
// through this same `.fsti`-gated interface and asserts `fs_* == fs_*_spec`
// on generated inputs. Deletability: delete the Step 3 patch and `fs_*`
// falls back to computing literally the same thing `fs_*_spec` computes
// (same Spec formula) -- slower, never wrong.
//
// DEVIATION FROM THE PLAN'S LITERAL WORDING, recorded here per CLAUDE.md
// rule #14: the migration plan describes the OCaml patch "renaming
// extracted bodies to fs_*_spec" (i.e. a purely OCaml-side textual
// rename). That mechanism does not survive contact with THIS `.fsti`:
// once Parser.FastString has a real interface, F* also emits a matching
// `Parser_FastString.mli` restricting the extracted module's external
// OCaml surface to exactly what THIS file declares -- a patch-invented
// `fs_byte_length_spec` binding that exists only via an in-place OCaml
// rename is invisible to any OTHER compilation unit (like the equivalence
// test), because `ocamlfind ocamlopt` type-checks external references
// against the `.mli`-derived `.cmi`, not against the raw `.ml` text
// (confirmed empirically: an unexported name is a hard "Unbound value"
// at the test's compile step, regardless of what the `.ml` actually
// contains). Declaring `fs_*_spec` as genuine F* functions here sidesteps
// that: they are legitimately part of the interface, so the `.mli` exports
// them, and the equivalence test can call them like any other primitive.
// It also removes an ordering hazard the literal rename would have
// carried (a naive append-fast-body-at-file-end patch would leave
// Parser.FastString.fst's OWN internal caller, fs_codepoints_of_string_aux,
// still bound to the pre-patch fs_cp_at -- see that function's own comment
// in the .fst for the full argument).
// ----------------------------------------------------------------------

val fs_byte_length_spec : string -> nat
val fs_byte_at_spec : s:string -> i:nat -> n:nat{n < 256}
val fs_byte_sub_spec : s:string -> start:nat -> len:nat -> string
val fs_find_byte_spec : s:string -> b:nat -> start:nat -> nat
val fs_cp_at_spec : s:string -> pos:nat -> nat & nat
val fs_cp_len_spec : s:string -> pos:nat -> nat

// ----------------------------------------------------------------------
// Bridging lemmas -- give proof modules computational power over these
// primitives WITHOUT `friend` (which would fully unfold them, reopening
// the fuel-blowup risk this `.fsti` exists to close). Each is a direct
// restatement of the primitive's own Parser.FastString.Spec formula, so a
// proof module that needs e.g. "what IS fs_byte_at s i" can invoke the
// matching lemma and reason from the Spec-level expression instead of
// treating fs_byte_at as fully featureless. Proved by unfolding in
// Parser.FastString.fst (`= ()` throughout -- each `fs_*` definition IS
// the RHS these lemmas state, so no real proof search is needed).
// ----------------------------------------------------------------------

val fs_byte_length_eq (s:string)
  : Lemma (fs_byte_length s == FStar.List.Tot.length (Parser.FastString.Spec.utf8_bytes s))

val fs_byte_at_eq (s:string) (i:nat)
  : Lemma (fs_byte_at s i ==
           (match Parser.FastString.Spec.nth_byte (Parser.FastString.Spec.utf8_bytes s) i with
            | Some b -> b
            | None -> 0))

// byte_sub bridging lemma: the "boundary-respecting slice, decode-reencode
// via string_of_list" design (Parser.FastString.fst's fs_byte_sub banner)
// is exactly this equation -- unconditional, because slice_bytes already
// performs patch 89's clamp structurally (drop past the end -> [],
// take past the end -> truncate) rather than via a separate branch. OFF-
// DOMAIN DIVERGENCE FROM THE PLAN (documented per the task brief): the
// plan's phrasing ("boundary-respecting slice") anticipated a STRONGER
// theorem -- that slicing on a codepoint boundary recovers exactly the
// byte-list slice of `utf8_bytes s` (a decode-then-re-encode round-trip
// identity). That stronger theorem needs an induction over
// `Parser.FastString.Spec.utf8_decode_all` composed with `utf8_enc_char`
// showing decode-then-encode is identity on any WELL-FORMED (i.e.
// F*-string-derived) UTF-8 byte sequence cut on codepoint boundaries; it
// is additional proof work, not attempted in this landing, and NOT needed
// for the definitional/computational-power purpose this lemma exists for
// (a proof module reasoning about what fs_byte_sub COMPUTES, not about a
// slice's relationship to the original string's own codepoint structure).
// Tracked as follow-up work under the same issue as this migration step.
val fs_byte_sub_eq (s:string) (start:nat) (len:nat)
  : Lemma (fs_byte_sub s start len ==
           FStar.String.string_of_list
             (Parser.FastString.Spec.utf8_decode_all
                (Parser.FastString.Spec.slice_bytes (Parser.FastString.Spec.utf8_bytes s) start len)))

val fs_find_byte_eq (s:string) (b:nat) (start:nat)
  : Lemma (fs_find_byte s b start ==
           Parser.FastString.Spec.find_byte (Parser.FastString.Spec.utf8_bytes s) b start)

val fs_cp_at_eq (s:string) (pos:nat)
  : Lemma (fs_cp_at s pos ==
           (let (cp, adv) = Parser.FastString.Spec.utf8_decode_at (Parser.FastString.Spec.utf8_bytes s) pos in
            (cp, (adv <: nat))))

val fs_cp_len_eq (s:string) (pos:nat)
  : Lemma (fs_cp_len s pos ==
           (let (_, adv) = Parser.FastString.Spec.utf8_decode_at (Parser.FastString.Spec.utf8_bytes s) pos in
            (adv <: nat)))

// ----------------------------------------------------------------------
// Convenience wrappers with external consumers (unchanged signatures).
// fs_char_at is deliberately NOT here -- grepped zero external consumers
// (`grep -rl fs_char_at *.fst` outside Parser.FastString itself), so it
// stays a private .fst-only convenience the same way it always was
// unexported before this migration (there was simply no enforcement
// mechanism before; now there is, and it still has nothing to export).
// ----------------------------------------------------------------------

val fs_byte_index : s:string -> i:nat -> FStar.Char.char

// Bridging lemma for fs_byte_index (added G4/#358 N-Triples parser-lemmas
// session, 2026-08-11 -- same rationale as the six `fs_*_eq` lemmas above:
// `fs_byte_index` is exported via this `.fsti` as a bare `val`, so its
// `Parser.FastString.fst` body (`let b = fs_byte_at s i in if b < 0xD800
// then char_of_int b else char_of_int 0`) is opaque to every consumer --
// confirmed empirically: `fs_byte_at_eq` alone does not discharge
// `fs_byte_index "a" 0 == FStar.Char.char_of_int 0x61` (Error 19, "Could
// not prove post-condition"; probe in RDF.NTriples.RoundTrip.fst's own
// commissioning session). Every N-Triples/N-Quads/Turtle/TriG parser
// dispatch reads its next byte through `fs_byte_index`, not `fs_byte_at`
// directly (see Parser.NTriples.fst's `parse_iri_raw`/`scan_iri_end`/
// `parse_triple` and siblings), so a parser-side round-trip proof needs
// this equation to turn a concrete `fs_byte_at` value (from `fs_byte_at_eq`
// + the BaseCases/Axioms facts) into the `FStar.Char.char` a `match ch with
// | ...` branch actually dispatches on. The `b < 0xD800` guard is always
// taken because `fs_byte_at` returns `n:nat{n < 256}` (its own refinement
// type, `< 256 < 0xD800` unconditionally), so this holds for every `s`/`i`
// with no side condition.
val fs_byte_index_eq (s:string) (i:nat)
  : Lemma (fs_byte_index s i == FStar.Char.char_of_int (fs_byte_at s i))

val fs_codepoints_of_string : string -> list FStar.Char.char

val fs_utf8_of_codepoint : int -> string
