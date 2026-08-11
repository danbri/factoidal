module Parser.FastString.ConcatSpec

(* ============================================================================
 * Parser.FastString.ConcatSpec -- FastString re-founding, Step 5, Task B
 * (docs/designissues/2026-08-10-faststring-refounding-plan.md).
 *
 * THE WALL THIS CLOSES. `FStar.String.concat : string -> list string -> Tot
 * string` (`FStar.String.fsti` line 76) is an opaque `val` with ZERO stated
 * equations -- confirmed by grep, no `Lemma` anywhere in that file mentions
 * it. `SPARQL.Protocol.RoundTrip.fst`'s own banner records exactly the
 * consequence: even the SINGLETON-list identity `String.concat sep [x] ==
 * x`, true unconditionally for ANY separator, is unprovable against the
 * stdlib primitive -- Error 19 on the FIRST step of the JSON string-segment
 * round-trip induction (an empty-body `""` literal, one recursive step from
 * the closing quote), which in turn blocks `json_parse_string` and
 * everything built on it, AND independently blocks composing with
 * `SPARQL.Protocol.serialise_response_json`/`json_row`/`json_var_list`,
 * whose terminal step is the SAME opaque `String.concat "" pieces` call
 * over a list whose length varies with the input.
 *
 * THE FIX, per the plan: a LOCAL, PROVED, definitionally-transparent
 * replacement -- fold over `^` -- with equations a proof module CAN use.
 * `concat_spec` computes the SAME string BatString.concat's own semantics
 * produce (separator strictly BETWEEN elements: `[]` -> `""`, a singleton
 * passes through unchanged, `n` elements get `n-1` separators) -- checked
 * against `FStar_String.ml`'s `let concat = BatString.concat` realisation,
 * the same discipline `Parser.FastString.Axioms.fsti`'s own banner uses for
 * its OCaml-realisation checks.
 *
 * NOT a claim that `concat_spec == FStar.String.concat` -- that equality is
 * exactly as unprovable as the wall above (comparing a defined function to
 * an opaque one with no equations). This module does not attempt it: it
 * REPLACES the call sites (Task B's migration), so the opaque primitive
 * stops appearing in the proof-critical paths at all, rather than trying to
 * bridge to it.
 *
 * PERFORMANCE, up front (plan's own gate): `concat_spec`'s naive right-fold
 * (`x ^ (sep ^ concat_spec sep rest)`) is the Step-1-style "pure Spec, not
 * the hot path" shape -- correctness first, matching the migration's own
 * precedent (`Parser.FastString.Spec` before the Step 3 OCaml realisation).
 * It is NOT tail-recursive and, on a list of `n` similarly-sized strings,
 * copies output proportional to the PARTIAL sum at each step (the same
 * shape as the plan's noted "pre-existing dump-nq superlinearity"), whereas
 * `BatString.concat` precomputes total length and writes once. If the
 * benchmark gate trips, that is this module's known, named cost -- the
 * plan's own contingency ("Option-B fallback for concat_spec is the NEXT
 * commit") covers it; this module does not attempt a fast realisation.
 * ============================================================================ *)

open FStar.List.Tot

(* ----------------------------------------------------------------------
 * The definition -- fold over `^`, separator strictly between elements.
 * ---------------------------------------------------------------------- *)

val concat_spec (sep : string) (l : list string) : Tot string (decreases l)
let rec concat_spec sep l =
  match l with
  | []       -> ""
  | [x]      -> x
  | x :: rest -> x ^ sep ^ concat_spec sep rest

(* ----------------------------------------------------------------------
 * The three base-shape lemmas the plan names, each a direct restatement
 * of one defining equation (proved by unfolding, `= ()` throughout --
 * `concat_spec`'s own `match` IS the equation each lemma states).
 * ---------------------------------------------------------------------- *)

val concat_spec_nil (sep : string)
  : Lemma (concat_spec sep [] == "")
let concat_spec_nil sep = ()

val concat_spec_singleton (sep x : string)
  : Lemma (concat_spec sep [x] == x)
let concat_spec_singleton sep x = ()

val concat_spec_cons (sep x : string) (rest : list string{Cons? rest})
  : Lemma (concat_spec sep (x :: rest) == x ^ sep ^ concat_spec sep rest)
let concat_spec_cons sep x rest = ()

(* ----------------------------------------------------------------------
 * SYMBOLIC strcat kit (G4 M4, session 2026-08-11).
 *
 * THE WALL THIS CLOSES. `Prims.strcat` (`^`, `Prims.fst` lines 611-613)
 * is, like `FStar.String.concat` above, an opaque `val` with NO stated
 * identity/associativity equations -- `SPARQL.Protocol.RoundTrip.fst`'s
 * Part 9 FINDING (2026-08-10) hit this precise wall composing
 * `lemma_concat_spec_two` into a SYMBOLIC (vars AND rows) statement about
 * `serialise_response_json`, naming `x ^ "" == x` for symbolic `x` as one
 * of the un-derivable steps; `RDF.NTriples.RoundTrip.fst`'s independent
 * 2026-08-11 FINDING hit the SAME wall from the N-Triples serializer side
 * (`"" ^ s == s` and `(a^b)^c == a^(b^c)` failing for symbolic strings).
 * Homed HERE rather than in `SPARQL.Protocol.RoundTrip.fst`: both callers
 * need it, and this module already carries the sibling
 * `FStar.String.concat` wall-closing lemmas above under the same
 * "opaque ulib primitive, zero axioms" shape -- one file for both
 * concatenation-primitive gaps rather than duplicating the kit per
 * caller.
 *
 * THE ROUTE. `Prims.strcat`/`^` is NOT actually unaxiomatized once you
 * leave `Prims.fst` itself: `FStar.String.fsti` states (lines 120-121)
 *   `list_of_concat (s1 s2 : string)
 *      : Lemma (list_of_string (s1 ^ s2) == list_of_string s1 @ list_of_string s2)`
 * -- i.e. `^` IS characterised, via the `list_of_string`/`string_of_list`
 * coercion pair (`string_of_list_of_string`, lines 44-45) and ordinary
 * `list`-level `@` (which DOES have real equations --
 * `FStar.List.Tot.Properties.append_nil_l`/`append_l_nil`/`append_assoc`).
 * So each identity below transports an `@`-level list fact back across
 * that coercion: unfold both sides via `list_of_concat`, close the `list`
 * goal with the relevant `List.Tot.Properties` lemma, then re-pack both
 * sides with `string_of_list_of_string` to conclude the `string` equality.
 * This is the exact route the module banner + this session's brief named
 * ("FStar.String.list_of_concat + append_l_nil/append_assoc +
 * string_of_list_of_string") -- confirmed against the stated ulib facts
 * before writing these (`FStar.String.fsti` lines 40-47, 120-121;
 * `FStar.List.Tot.Properties.fsti` lines 116-133), not assumed.
 *
 * All three verify directly with NO extra scaffolding beyond the cited
 * ulib lemmas -- no `assert_norm`, no case split, no admitted step. In
 * particular `list_of_string "" == []` (needed for the two identity
 * lemmas) is NOT stated anywhere in `FStar.String.fsti` as a named fact,
 * but the SMT encoding closes it without help once `list_of_concat` is in
 * context (`FStar.String.fsti`'s own header: "these functions ... can be
 * reduced during typechecking" -- probed standalone before landing here,
 * `/tmp/.../probe_strcat.fst` / `probe_strcat2.fst`, 2/2 and 3/3
 * deterministic passes).
 * ---------------------------------------------------------------------- *)

val lemma_strcat_empty_l (s : string)
  : Lemma (ensures "" ^ s == s)
let lemma_strcat_empty_l s =
  FStar.String.list_of_concat "" s;
  FStar.String.string_of_list_of_string ("" ^ s);
  FStar.String.string_of_list_of_string s

val lemma_strcat_empty_r (s : string)
  : Lemma (ensures s ^ "" == s)
let lemma_strcat_empty_r s =
  FStar.String.list_of_concat s "";
  FStar.List.Tot.Properties.append_l_nil (FStar.String.list_of_string s);
  FStar.String.string_of_list_of_string (s ^ "");
  FStar.String.string_of_list_of_string s

val lemma_strcat_assoc (a b c : string)
  : Lemma (ensures (a ^ b) ^ c == a ^ (b ^ c))
let lemma_strcat_assoc a b c =
  FStar.String.list_of_concat a b;
  FStar.String.list_of_concat (a ^ b) c;
  FStar.String.list_of_concat b c;
  FStar.String.list_of_concat a (b ^ c);
  FStar.List.Tot.Properties.append_assoc
    (FStar.String.list_of_string a) (FStar.String.list_of_string b) (FStar.String.list_of_string c);
  FStar.String.string_of_list_of_string ((a ^ b) ^ c);
  FStar.String.string_of_list_of_string (a ^ (b ^ c))
