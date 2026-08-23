/-
L4Factoidal.RDFS.RDFSPlus — the RDFS-Plus closure operator.

Port of `formal/fstar/RDF.Entailment.RDFSPlus.fst` (93 lines).

## The tier

RDFS plus a small practical OWL subset: `owl:sameAs` (symmetry,
transitivity, substitution into subject, object and predicate
position), `owl:inverseOf`, `owl:SymmetricProperty`,
`owl:TransitiveProperty`, `owl:FunctionalProperty`,
`owl:InverseFunctionalProperty`, `owl:equivalentClass`,
`owl:equivalentProperty`.

The names come from "RDFS-Plus" (Allemang and Hendler, *Semantic Web
for the Working Ontologist*, 2008) and "RDFS++" (Franz Inc.'s
AllegroGraph reasoner). The tier sits between core RDFS (ρdf, six
rules, full bidirectional chain proofs) and full OWL 2 RL.

## The claim level, stated plainly

Every OWL row this operator runs carries a proved licensing lemma and
truth-preservation lemma in the F\* tree
(`OWL.RL.Refinement.fst`, `OWL.Semantics.Soundness.fst`) — per-rule
certificates, e.g. `eq_sym_licensed`, `eq_trans_licensed`,
`prp_symp_licensed`. Rows covered: eq-sym, eq-trans, eq-rep-s,
eq-rep-o, eq-rep-p, prp-symp, prp-trp, prp-inv1, prp-inv2, prp-fp,
prp-ifp, cax-eqc, prp-eqp.

**NO chain-level completeness is claimed for this tier.** Unlike ρdf
closure, whose completeness theorem decides ρdf entailment,
`owl:sameAs` introduces equality reasoning and the Herbrand
construction behind that theorem does not survive quotienting by sameAs
classes. Each step's rows are individually licensed and
truth-preserving; nothing here asserts that the fixed point captures
every RDFS-Plus consequence.

## One row is deliberately absent

`eq-ref` — `x owl:sameAs x` for every node — is NOT in the step. It
manufactures one triple per node without contributing an entailment any
downstream row consumes, and including it would inflate every
intermediate graph. That is the same reason `RDFS.Closure`'s step
excludes rdfs6 and rdfs10.

## One row had no Lean counterpart until now

The F\* step calls `owl_rule_inverseOf_domain_range_flip`, which
`L4Factoidal/OWL/RLClosure.lean` did not have. It is added there, next
to prp-inv1 and prp-inv2, as `inverseOfDomRngFlipFor` — that is its home
when the rest of `OWL.Closure` lands, not this module. Dropping it
silently would have made this closure derive fewer schema triples than
the F\* one while still passing a fixed-point check.
-/
import L4Factoidal.RDFS.Closure
import L4Factoidal.OWL.RLClosure
import L4Factoidal.OWL.Vocabulary

namespace L4Factoidal.RDFS

open L4Factoidal.RDF L4Factoidal.OWL L4Factoidal.OWL.RL

/-- The RDFS step's conclusions, then the OWL rows', in the F\* source's
    order. Every function called is one `RDFS.Closure` or
    `OWL.RLClosure` already defines — no rule body is restated here. -/
def rdfsPlusConclusions (g : Graph) : List Triple :=
  let g0 := RDFS.step g
  g0.flatMap (caxEqc1For g0) ++
  g0.flatMap (caxEqc2For g0) ++
  g0.flatMap (prpEqp1For g0) ++
  g0.flatMap (prpEqp2For g0) ++
  g0.flatMap (prpSympFor g0) ++
  g0.flatMap (prpTrpFor g0) ++
  g0.flatMap (prpInv1For g0) ++
  g0.flatMap (prpInv2For g0) ++
  g0.flatMap (inverseOfDomRngFlipFor g0) ++
  g0.flatMap (prpFpFor g0) ++
  g0.flatMap (prpIfpFor g0) ++
  g0.flatMap (eqSymFor g0) ++
  g0.flatMap (eqTransFor g0) ++
  g0.flatMap (eqRepSFor g0) ++
  g0.flatMap (eqRepOFor g0) ++
  g0.flatMap (eqRepPFor g0)

/-- One round. Same fuel, dedup and length-test shape as
    `RDFS.Closure.step`. -/
def rdfsPlusStep (g : Graph) : Graph :=
  RDFS.addAll (RDFS.step g) (rdfsPlusConclusions g)

def rdfsPlusClosure (g : Graph) : Nat → Graph
  | 0     => g
  | n + 1 =>
      let g' := rdfsPlusStep g
      if g'.length = g.length then g else rdfsPlusClosure g' n

/-- The closure at `RDFS.Closure`'s own fuel bound. -/
def rdfsPlusClosureFix (g : Graph) : Graph :=
  rdfsPlusClosure g (RDFS.closureFuelBound g)

/-! ## Build-time checks -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def pi (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩
private def ps (s : String) : Subject := .iri (pi s)
private def pt (s : String) : Term := .iri (pi s)

private def has (g : Graph) (t : Triple) : Bool := g.any (fun u => u.eqb t)

/-! ### `owl:sameAs` substitutes into subject position -/

private def gSameAs : Graph :=
  [ ⟨ps "a", owlSameAs, pt "b"⟩,
    ⟨ps "a", pi "p", pt "v"⟩ ]

#guard has (rdfsPlusClosureFix gSameAs) ⟨ps "b", pi "p", pt "v"⟩
#guard has (rdfsPlusClosureFix gSameAs) ⟨ps "b", owlSameAs, pt "a"⟩

/-! ### `owl:inverseOf` gives the transposed edge AND the transposed
    schema triple — the second is what `inverseOfDomRngFlipFor` adds,
    and what would be silently missing if the row had been dropped. -/

private def gInv : Graph :=
  [ ⟨ps "parent", owlInverseOf, pt "child"⟩,
    ⟨ps "parent", rdfsDomain, pt "Person"⟩,
    ⟨ps "x", pi "parent", pt "y"⟩ ]

#guard has (rdfsPlusClosureFix gInv) ⟨ps "y", pi "child", pt "x"⟩
#guard has (rdfsPlusClosureFix gInv) ⟨ps "child", rdfsRange, pt "Person"⟩

/-! ### `owl:TransitiveProperty` and `owl:SymmetricProperty` -/

private def gTrp : Graph :=
  [ ⟨ps "r", rdfType, .iri owlTransitiveProperty⟩,
    ⟨ps "a", pi "r", pt "b"⟩,
    ⟨ps "b", pi "r", pt "c"⟩ ]

#guard has (rdfsPlusClosureFix gTrp) ⟨ps "a", pi "r", pt "c"⟩

private def gSym : Graph :=
  [ ⟨ps "r", rdfType, .iri owlSymmetricProperty⟩,
    ⟨ps "a", pi "r", pt "b"⟩ ]

#guard has (rdfsPlusClosureFix gSym) ⟨ps "b", pi "r", pt "a"⟩

/-! ### RDFS itself still runs — the tier is RDFS PLUS, not OWL only -/

private def gRdfs : Graph :=
  [ ⟨ps "a", rdfType, pt "C1"⟩,
    ⟨ps "C1", rdfsSubClassOf, pt "C2"⟩ ]

#guard has (rdfsPlusClosureFix gRdfs) ⟨ps "a", rdfType, pt "C2"⟩

/-! ### `eq-ref` is ABSENT

`x owl:sameAs x` must NOT appear for a node that has no sameAs
statement. This is the excluded row, and a check that it is excluded is
the only thing that keeps it excluded. -/

#guard !has (rdfsPlusClosureFix gRdfs) ⟨ps "a", owlSameAs, pt "a"⟩
#guard !has (rdfsPlusClosureFix gTrp) ⟨ps "a", owlSameAs, pt "a"⟩

/-! ### The closure is strictly bigger than the input on each of these,
    so none of the checks above passes vacuously. -/

#guard (rdfsPlusClosureFix gSameAs).length > gSameAs.length
#guard (rdfsPlusClosureFix gInv).length > gInv.length
#guard (rdfsPlusClosureFix gTrp).length > gTrp.length
#guard (rdfsPlusClosureFix gRdfs).length > gRdfs.length

end L4Factoidal.RDFS
