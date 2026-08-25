/-
L4Factoidal.RDFS.RegimeDispatch — the experimental entailment regimes.

Port of `formal/fstar/RDF.Entailment.RegimeDispatch.fst` (53 lines).

SPARQL 1.1 Entailment Regimes is an explicit extension point: a regime
is an entailment relation plus conditions on BGP matching. Both regimes
here are materialisation-based — answers are defined as SIMPLE
entailment over the named closure of the queried graph, which is the
standard construction for a finite answer set. The `x-` prefix marks
them as experimental, non-W3C names.

Regime dispatch is engine logic and lives here per iron rules #1 and
#15, not in a CLI or an npm wrapper; consumers pass the regime string
through verbatim.

| Regime | Closure | Claim level |
|---|---|---|
| `x-rdfscore` | ρdf closure (`RDFS.closureFix`) | the definition IS a theorem: on fragment data the answers are EXACTLY the ρdf-entailed consequences, sound and complete |
| `x-rdfsplus` | `RDFS.rdfsPlusClosureFix` | every OWL row runs under proved licensing and truth lemmas; **chain-level completeness is deliberately NOT claimed** — `owl:sameAs` equality breaks the Herbrand construction |

Every other regime string falls through to the OWL closure, which owns
the W3C-named regimes.

## One difference from the F\*

The F\* fall-through calls `OWL.Closure.entailment_closure_for_query`,
which also performs the comprehension-witness strip (#346). The Lean
tree's `OWL.RL.closure` has no witness scaffolding to strip — the F\*
banner notes that the two NEW closures mint none either, so no strip is
needed on the new paths. The fall-through here is `OWL.RL.closure`
directly, and the regimes it distinguishes beyond the two below are not
yet split out; a caller asking for `"RDFS"` or `"OWL-RL"` gets the OWL RL
closure. That is a narrowing of the F\* behaviour and it is stated here
rather than left to be discovered.
-/
import L4Factoidal.RDFS.RDFSPlus

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

def regimeXRdfsCore : String := "x-rdfscore"
def regimeXRdfsPlus : String := "x-rdfsplus"

/-- The closure a regime string selects. -/
def entailmentClosureForQueryExt (regime : String) (g : Graph) (fuel : Nat) : Graph :=
  if regime == regimeXRdfsCore then RDFS.closure g fuel
  else if regime == regimeXRdfsPlus then RDFS.rdfsPlusClosure g fuel
  else L4Factoidal.OWL.RL.closure g fuel

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def di (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩
private def has (g : Graph) (t : Triple) : Bool := g.any (fun u => u.eqb t)

/-- A subclass edge plus a sameAs edge: RDFS alone derives the type,
    RDFS-Plus additionally derives the sameAs consequences. -/
private def gMixed : Graph :=
  [ ⟨.iri (di "a"), rdfType, .iri (di "C1")⟩,
    ⟨.iri (di "C1"), rdfsSubClassOf, .iri (di "C2")⟩,
    ⟨.iri (di "a"), L4Factoidal.OWL.RL.owlSameAs, .iri (di "b")⟩ ]

/-! Both regimes derive the RDFS consequence. -/

#guard has (entailmentClosureForQueryExt regimeXRdfsCore gMixed 50)
        ⟨.iri (di "a"), rdfType, .iri (di "C2")⟩
#guard has (entailmentClosureForQueryExt regimeXRdfsPlus gMixed 50)
        ⟨.iri (di "a"), rdfType, .iri (di "C2")⟩

/-! Only RDFS-Plus derives the sameAs consequence. This is what makes
    the two regimes different, and a dispatch that routed both to one
    closure would pass every check above. -/

#guard has (entailmentClosureForQueryExt regimeXRdfsPlus gMixed 50)
        ⟨.iri (di "b"), rdfType, .iri (di "C1")⟩
#guard !has (entailmentClosureForQueryExt regimeXRdfsCore gMixed 50)
        ⟨.iri (di "b"), rdfType, .iri (di "C1")⟩

/-! The names are matched EXACTLY. A near-miss must take the
    fall-through, not one of the two named regimes. `x-rdfscor` is
    checked by comparing its result with the real `x-rdfscore` result:
    if the match were a prefix test the two would be equal. -/

#guard regimeXRdfsCore != regimeXRdfsPlus
#guard (entailmentClosureForQueryExt "x-rdfscor" gMixed 50).length
        != (entailmentClosureForQueryExt regimeXRdfsCore gMixed 50).length
#guard (entailmentClosureForQueryExt "x-rdfsplusX" gMixed 50).length
        == (entailmentClosureForQueryExt "anything-else" gMixed 50).length

/-! Zero fuel is the identity, for every regime. That is what makes the
    fuel argument a budget rather than a suggestion. -/

#guard (entailmentClosureForQueryExt regimeXRdfsCore gMixed 0).length == gMixed.length
#guard (entailmentClosureForQueryExt regimeXRdfsPlus gMixed 0).length == gMixed.length
#guard (entailmentClosureForQueryExt "other" gMixed 0).length == gMixed.length

end L4Factoidal.RDFS
