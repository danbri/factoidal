/-
L4Factoidal.SPARQL.ResultsTheorems — the SRJ N-row shape theorem and
the parse ∘ serialise round-trip.

## 1. The SRJ N-row shape theorem

`formal/fstar/SPARQL.Protocol.RoundTrip.fst`'s G4/M1 program proves
`lemma_srj_n_rows`: `serialise_response_json vars rows` equals the
FIXED wrapper text
`"{\"head\":{\"vars\":[" ^ json_var_list vars ^ "]},\"results\":
{\"bindings\":[" ^ json_rows_joined rows ^ "]}}"`
where `json_rows_joined` is the DIRECT (non-accumulator) recursive
join — as opposed to `serialise_response_json`'s own body, which for
extraction-performance reasons (a real 3M-row stack-overflow bug,
`tav5` 2026-04-26) computes the joined text via a TAIL-RECURSIVE
accumulator (`json_rows_body_acc`) plus `List.Tot.rev`. The F* lemma's
whole job is bridging those two computations of the same string.

This Lean port has no such gap to bridge: `ResultsJson.lean`'s
`QueryResult.toSrj` is defined DIRECTLY in terms of `rowsJoined`
(the Lean counterpart of `json_rows_joined` — see that file's own
module header), because this tree is the SPECIFICATION evaluator
(list scans, no tail-call/stack-depth engineering — the convention
every module in `L4Factoidal` follows, per `PORT_NOTES.md`). So
`toSrj_bindings_shape` below is the same OBSERVABLE statement
`lemma_srj_n_rows` proves, and it holds by `rfl` — which is not a
weaker theorem, it is what removing the F* tree's accumulator/reverse
detour buys back. The `rowsJoined` decomposition lemmas that follow
restate the "for N rows" content (N = 0, 1, ≥2, matching the F*
comment's own reading of the lemma: "already covers `rows = [r1;r2]`
... by instantiation") as named, individually-checkable facts.

## 2. The round-trip goal — status

Same policy as `JSON.Theorems.RoundTripGoal`/`Syntax.SyntaxTheorems`'s
skeletons: iron rule "no `sorry`, no `axiom`" means an unprovable
`theorem` is not declared, full stop — the general goal is a `def :
Prop`. What blocks it, precisely, is named below.
-/
import L4Factoidal.SPARQL.ResultsJson

namespace L4Factoidal.SPARQL.ResultsTheorems

open L4Factoidal.SPARQL

/-! ## 1. The SRJ N-row shape theorem -/

/-- Port of `lemma_srj_n_rows`'s conclusion, restated over this port's
own `toSrj`/`rowsJoined`/`varListJson`. Proved by `rfl`: unlike the F*
lemma, there is no accumulator/reverse detour to bridge — see the
module header. Holds for every `vars`/`rows`, i.e. for every N. -/
theorem toSrj_bindings_shape (vars : List VarName) (rows : SolutionSeq) :
    (QueryResult.bindings vars rows).toSrj =
      "{\"head\":{\"vars\":[" ++ varListJson vars ++ "]}," ++
      "\"results\":{\"bindings\":[" ++ rowsJoined rows ++ "]}}" := rfl

#print axioms toSrj_bindings_shape

/-! ## `rowsJoined`'s N-row decomposition — N = 0, 1, ≥2

Each is `rfl` (the equation defining `rowsJoined`), stated as named
facts so the "for N rows" reading of the theorem above is checkable
row-count by row-count, not just as one opaque general statement. -/

@[simp] theorem rowsJoined_nil : rowsJoined ([] : SolutionSeq) = "" := rfl

theorem rowsJoined_singleton (r : Binding) : rowsJoined [r] = rowJson r := rfl

theorem rowsJoined_cons_cons (r1 r2 : Binding) (rest : SolutionSeq) :
    rowsJoined (r1 :: r2 :: rest) = rowJson r1 ++ "," ++ rowsJoined (r2 :: rest) := rfl

/-- The general recursive equation, stated once as its own theorem (not
just relied on via `rfl` inside the two special cases above) — the
`r1 :: r2 :: rest` shape of `rowsJoined_cons_cons` is the SAME equation
instantiated at `rest = []`, `rest = [r3]`, … covering every N ≥ 2 by
induction one step at a time (the induction `RoundTripGoal` below names
as its own remaining gap uses exactly this equation as its step case). -/
theorem rowsJoined_cons (r : Binding) (rest : SolutionSeq) (h : rest ≠ []) :
    rowsJoined (r :: rest) = rowJson r ++ "," ++ rowsJoined rest := by
  cases rest with
  | nil => exact absurd rfl h
  | cons r2 rest' => rfl

#print axioms rowsJoined_cons

/-! ## 2. The round-trip goal

**Proved** (§1 above, and by construction): the N-row SHAPE theorem,
for every N.

**Proved as concrete instances** (compiled evaluation:
`ResultsTests.lean` §4's twelve `parseSrj (r.toSrj) = .ok r` `#guard`s,
spanning bindings/boolean, 0/1/2 rows, unbound variables, language
-tagged/directional/typed literals, blank nodes, and an RDF 1.2 triple
term). These exercise the ACTUAL compiled `parseSrj`/`toSrj`, not a
model of them.

**NOT proved as a KERNEL theorem, even for one concrete instance,**
named precisely:

`parseSrj` composes `JSON.Parser.parseJson`, whose five mutually
recursive functions (`parseValue`/`parseObject`/`parseMembers`/
`parseArray`/`parseItems`) compile via WELL-FOUNDED recursion rather
than bare structural recursion (`JSON.Theorems`'s own header records
this, empirically: `by decide`/`by rfl` get "stuck" on any goal
mentioning `parseValue` or anything that calls it). The documented
workaround — `unfold parseValue parseObject ...` (equation-lemma
rewriting) peeling exactly the layers ONE concrete input needs, then
`decide` — reaches two or three mutual-group layers for a small
top-level `Json.object` (`JSON.Theorems.roundtrip_small_object`).
An SRJ document is a strictly DEEPER instance of the same shape: even
`{"head":{},"boolean":true}` nests an object inside an object
(`"head":{}`) alongside a bindings array whose ELEMENTS are themselves
objects one layer down again (a non-empty `results.bindings` case), so
closing even ONE concrete SRJ round-trip case needs the SAME
`unfold`-then-`decide` recipe applied one to two layers deeper than
`JSON.Theorems`'s worked examples go — mechanical, in the sense that
`JSON.Theorems`'s recipe is a KNOWN, working technique, but sized past
what this landing's time budget covers. A GENERAL (∀-quantified) proof
needs the same technique repeated under an induction over
`SolutionSeq`/`Json`, which `JSON.Theorems.RoundTripGoal`'s own §5
already names as unclosed for the underlying JSON layer (items 1–3
there); this file's goal cannot be stronger than what it is built on.

None of this is a correctness DOUBT: `toSrj_bindings_shape` above is a
proved kernel theorem about the SERIALISER's shape, and every
sub-mechanism the round trip would compose (JSON string/number/array/
object parsing, the `mkResult*` constructors, `Term.eqb`) is
independently exercised by a `#guard` that runs the actual compiled
code. It is proof-engineering debt in exactly the shape
`JSON.Theorems.RoundTripGoal` already carries, inherited one layer up. -/

/-- The general SRJ round-trip goal (STATED, not proved — see the
section above for the exact gap and where to pick it up: extend
`JSON.Theorems.RoundTripGoal` first, then compose through
`headVarsJson`/`rowsFieldJson`/`parseSrjBindingValueFuel`). -/
def SrjRoundTripGoal : Prop :=
  ∀ (vars : List VarName) (rows : SolutionSeq),
    parseSrj ((QueryResult.bindings vars rows).toSrj) = .ok (QueryResult.bindings vars rows)

end L4Factoidal.SPARQL.ResultsTheorems
