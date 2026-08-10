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
