/-
Wasm.Ops.Reason — owlClosure / rhoDfClosure / rhoDfFragmentCheck /
rdfsPlusClosure / owlIsConsistent / owlEntails.

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  owlClosure(nquads, mode)       -> {"ok":true,"nquads":"…"}
      mode "RDFS" | "OWL-RL"; unknown mode is the F* entry's error text.
  rhoDfClosure(nquads)           -> {"ok":true,"ntriples":"…","rounds":N}
  rhoDfFragmentCheck(nquads)     -> {"ok":true,"fragment":true|false}
  rdfsPlusClosure(nquads)        -> {"ok":true,"ntriples":"…","rounds":N}
  owlIsConsistent(nquads, optsJson)
      -> {"ok":true,"consistent":true|false|null,"reason"?:"…"}
  owlEntails(premiseNquads, conclusionNquads, optsJson)
      -> {"ok":true,"entailed":true|false|null,
          "via":"closure"|"refutation","reason"?:"…"}

Only the DEFAULT graph is closed over (the same scope cut as the F*
entry); output is N-Triples lines. `rounds` is telemetry counted by
re-driving the step function with the length test
(`Support.roundsToFixpoint`), mirroring `entry_jsoo.ml:1137`.

The "RDFS" mode runs the same closure the Lean harness's RDFS regime
path runs (`Harness/Run.lean` `closeDataset` → `Regime.rdfs.closure` →
`RDFS.fullClosure` with the minimal datatype map and the graph's own
`rdf:_n` slice).

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Datatypes
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.RDFS.RDFSPlus
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.NegationGoals
import L4Factoidal.Syntax.NQuadsFast

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- The `rdf:_n` slice of a graph — `rdf:_1` plus those the graph
mentions (the same computation as `Harness/Run.lean`'s `cmpSlice`). -/
private def cmpSlice (g : Graph) : List WfIri :=
  (L4Factoidal.RDFS.containerMembershipIn g).foldl
    (fun acc i => if acc.contains i then acc else acc ++ [i])
    [L4Factoidal.RDFS.rdf1]

/-- N-Triples lines for a default-graph closure result, or the error
envelope when a term cannot be serialised. -/
private def ntriplesEnvelope (key : String) (g : Graph)
    (extra : List (String × Json) := []) : String :=
  match Graph.toNTriples g with
  | .error e  => errJson s!"closure serialisation: {e}"
  | .ok lines => okWith (((key, Json.string lines)) :: extra)

/-- `owlClosure(nquads, mode)`. -/
def owlClosure (nq mode : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
    let g := ds.default
    match mode with
    | "RDFS" | "rdfs" =>
        ntriplesEnvelope "nquads"
          (L4Factoidal.RDFS.fullClosure (withMinimalD []) (cmpSlice g) g)
    | "OWL-RL" | "owl-rl" | "owl_rl" =>
        ntriplesEnvelope "nquads" (L4Factoidal.OWL.RL.closureFix g)
    | _ =>
        errJson s!"owlClosure: unknown mode '{mode}' (expected 'RDFS' or 'OWL-RL')"

/-- `rhoDfClosure(nquads)`. -/
def rhoDfClosure (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
    let g := ds.default
    let closed := L4Factoidal.RDFS.closureFix g
    let rounds :=
      roundsToFixpoint L4Factoidal.RDFS.step
        (L4Factoidal.RDFS.closureFuelBound g) g
    ntriplesEnvelope "ntriples" closed [("rounds", .number (toString rounds))]

/-- `rhoDfFragmentCheck(nquads)`. -/
def rhoDfFragmentCheck (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      okWith [("fragment", .bool (L4Factoidal.RDFS.isRhoDfFrag ds.default))]

/-- `rdfsPlusClosure(nquads)`. -/
def rdfsPlusClosure (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
    let g := ds.default
    let closed := L4Factoidal.RDFS.rdfsPlusClosureFix g
    let rounds :=
      roundsToFixpoint L4Factoidal.RDFS.rdfsPlusStep
        (L4Factoidal.RDFS.closureFuelBound g) g
    ntriplesEnvelope "ntriples" closed [("rounds", .number (toString rounds))]

/-! ## OWL DL reasoning by refutation (issue 586)

The chain is the F* npm entry's, engine for engine: the OWL-RL
closure of the default graph, then the three-valued clash-detecting
tableau (`L4Factoidal.OWL.Refute.tableauConsistent`, mirroring
`Tableau_Refute.tableau_consistent`). The Lean source calls this
tree's standard `OWL.RL.closureFix`; its proved `@[csimp]` equation
selects `indexedClosureFix` in compiled code. This is the same closure
that `owlClosure`'s "OWL-RL" mode serves. The F* entry reaches the
equivalent rows through `owl_rl_closure_with_reflexivity`, fuel 100.
The `none` verdict is reported as `null` with an indeterminate-limit
reason, never a silent `false`.
No reasoning logic lives here: closure, refuter and `negationGoals`
are all `L4Factoidal` library code; these ops only parse, dispatch
and shape the JSON verdict. -/

/-- The refutation budget: `optsJson` is `""` or `{"fuel":"<nat>"}`
(fuel a decimal STRING — a large budget can exceed JS's safe-integer
range, so it crosses the ABI as text, same as the F* entry). Default
20000, matching `entry_jsoo.ml`'s `owl_refute_fuel_of_opts`; any
unreadable opts document or fuel string falls back to the default. -/
def owlRefuteFuelOfOpts (optsJson : String) : Nat :=
  let defaultFuel := 20000
  if optsJson == "" then defaultFuel
  else
    match parseJson optsJson with
    | .error _ => defaultFuel
    | .ok root =>
      match root.getString? "fuel" with
      | some s => (s.toNat?).getD defaultFuel
      | none   => defaultFuel

/-- `owlIsConsistent(nquads, optsJson)`. `reason` is a plumbing-level
description of the verdict source (there is no clash-trace string in
the refuter); present on the false/null verdicts, omitted on true. -/
def owlIsConsistent (nq optsJson : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
    let closure := L4Factoidal.OWL.RL.closureFix ds.default
    let fuel := owlRefuteFuelOfOpts optsJson
    match L4Factoidal.OWL.Refute.tableauConsistent closure fuel with
    | some false =>
        okWith [("consistent", .bool false),
                ("reason", .string
                  ("the clash-detecting tableau derived a contradiction "
                   ++ "on every branch of the OWL-RL closure"))]
    | some true => okWith [("consistent", .bool true)]
    | none =>
        okWith [("consistent", .null),
                ("reason", .string
                  (s!"indeterminate: tableau visit budget {fuel} was exhausted "
                   ++ "or bounded witness construction left an unresolved "
                   ++ "obligation; no consistency verdict"))]

/-- `owlEntails(premiseNquads, conclusionNquads, optsJson)`. The two
dispatch paths are `via:"closure"` when every conclusion
triple is exactly (engine triple equality) in the OWL-RL closure of
the premise; `via:"refutation"` when the negated conclusion
(`prepareNegationGoals`) is refuted on every goal. A quiescent open
bounded expansion is not a certified model, so it cannot establish
non-entailment; every result other than closure containment or all
goals refuted is `null`. -/
def owlEntails (premiseNq conclusionNq optsJson : String) : String :=
  match parseNQuadsFast premiseNq with
  | .error e => errJson (fmtParseError e)
  | .ok dsP =>
    match parseNQuadsFast conclusionNq with
    | .error e => errJson (fmtParseError e)
    | .ok dsC =>
      let gc := dsC.default
      let closure := L4Factoidal.OWL.RL.closureFix dsP.default
      let fuel := owlRefuteFuelOfOpts optsJson
      if gc.all (fun t => Graph.mem t closure) then
        okWith [("entailed", .bool true), ("via", .string "closure")]
      else
        match L4Factoidal.OWL.Refute.prepareNegationGoals closure gc with
        | none =>
            okWith [("entailed", .null), ("via", .string "closure"),
                    ("reason", .string
                      ("not in the OWL-RL closure, and the conclusion form "
                       ++ "cannot be soundly negated for refutation; "
                       ++ "non-entailment is not established"))]
        | some (premise, goals) =>
          let results := goals.map (fun neg =>
            L4Factoidal.OWL.Refute.tableauConsistent (premise ++ neg) fuel)
          if results.all (· == some false) then
            okWith [("entailed", .bool true), ("via", .string "refutation")]
          else if results.any (· == some true) then
            okWith [("entailed", .null), ("via", .string "refutation"),
                    ("reason", .string
                      ("the bounded tableau reached a quiescent open branch "
                       ++ "but produced no model certificate; entailment "
                       ++ "remains indeterminate"))]
          else
            okWith [("entailed", .null), ("via", .string "refutation"),
                    ("reason", .string
                      (s!"indeterminate: a refutation goal exhausted visit "
                       ++ s!"budget {fuel} or retained an unresolved bounded "
                       ++ "witness obligation"))]

end L4Wasm.Ops
