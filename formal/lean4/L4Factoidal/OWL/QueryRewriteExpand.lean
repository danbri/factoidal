/-
L4Factoidal.OWL.QueryRewriteExpand — layer 5 of the port of
`OWL.QueryRewrite`: the recursive class-expression expander.

`expandCeSubject b subj op fuel` answers "what pattern does
`subj rdf:type op` become, when `op` is a class expression?" It is the
counterpart of the F\* source's `expand_ce_subject`.

## Every arm is here

Intersection, union, existential restriction, universal restriction,
the three cardinality kinds and `owl:complementOf`, plus the leaf and
the fuel-exhaustion case. The arms are transcribed from the F\* source,
including their stated limits.

## The narrowness is reproduced, not repaired

CLAUDE.md records the shipping cardinality rewrite as sound-but-narrow
at <https://github.com/danbri/factoidal/issues/236>: the N=1 qualified
`maxQualifiedCardinality` rewrite emits an anchor triple that
MULTIPLIES rows per P-edge and drops individuals for which max-1 holds
vacuously.

This port reproduces that behaviour rather than repairing it. A repair
would make the two trees compute different things, and the differential
comparison is what makes every finding in
`docs/designissues/2026-08-24-what-the-lean-port-found.md` checkable.
Repairing it is a separate decision, better taken with both trees in
hand than during a transcription.

The other stated limits are carried across the same way: minimum
cardinality over-approximates for N >= 2, maximum cardinality falls
back to the leaf for N >= 2 and for unqualified N = 1, exact
cardinality emits the minimum side only for N >= 1, universal
restriction supports a named-class or union filler and no other shape,
and complement targets disjointness rather than absence because a
`FILTER NOT EXISTS` would be closed-world.

## What the fall-backs guarantee

Each unsupported shape emits the pre-rewrite triple, which is the F\*
source's own discipline, stated at its fuel-exhaustion case:

> at worst this is the pre-rewrite behaviour (a bnode as the object of
> rdf:type that won't bind in the data). Sound — never *adds*
> solutions.

Three theorems below pin that shape: a restriction with no IRI-valued
`owl:onProperty`, a complement whose target is not a named class, and
running out of fuel all produce the leaf.

## A guard the first pass missed

The F\* `someValuesFrom` arm requires `owl:onProperty` to be an IRI
(`Some (PT_IRI p_iri)`) and falls back to the leaf otherwise. The first
Lean version of this arm accepted any `PatternTerm` and put it in the
predicate position, so a variable-predicate restriction produced
`subj ?v ?_sv_k` where the F\* tree produced the leaf. `patternIri` is
now the guard on every arm that reads `owl:onProperty`.

## The fresh variable

The existential arm needs a variable for the anonymous filler
individual. Its name is derived from the restriction's marker key, as
in the F\* source, so two restrictions in one BGP get two distinct
variables. The `_sv_` prefix is what
`SPARQL/RewriteVarStrip.lean` later strips from the FINAL projection —
the two modules share that convention and neither works without it.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewriteRestriction
import L4Factoidal.SPARQL.RewriteVarStrip

namespace L4Factoidal.OWL.QueryRewriteCore

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.SPARQL
open L4Factoidal.OWL.RL (owlIntersectionOf owlUnionOf owlSomeValuesFrom
  owlAllValuesFrom owlComplementOf owlOnProperty owlOnClass owlDisjointWith
  owlRestriction owlMinCardinality owlMaxCardinality owlCardinality
  owlMinQualifiedCardinality owlMaxQualifiedCardinality
  owlQualifiedCardinality)

/-! ## Leaf and conjunction -/

/-- The unexpanded form: `subj rdf:type leaf`. -/
def singleTypeBgp (subj : PatternSubject) (leaf : PatternTerm) : Bgp :=
  [{ s := subj, p := .iri rdfType, o := leaf }]

/-- Conjoin patterns into a left-deep join. Zero conjuncts is the empty
pattern; one is itself — neither needs a join node. -/
def joinPatterns : List QueryPattern → QueryPattern
  | [] => .empty
  | [g] => g
  | g :: tl => tl.foldl QueryPattern.join g

/-! ## Which class expression is this term? -/

/-- The marker key and combinator for a term, covering the flat
markers of layer 3 and the restrictions of layer 4. -/
def ceCombinatorForTerm (b : Bgp) (pt : PatternTerm) :
    Option (String × Option CeCombinator × Option Restriction) :=
  match markerKey pt with
  | none => none
  | some k =>
      match (findFlatMarkers b).find? (fun e => e.1 == k) with
      | some (_, c) => some (k, some c, none)
      | none =>
          if isSvfSubject b k then some (k, none, some .someValuesFrom)
          else if isAvfSubject b k then some (k, none, some .allValuesFrom)
          else match cardSubjectCombinator b k with
               | some r => some (k, none, some r)
               | none =>
                   if isComplementOfSubject b k then some (k, none, some .complementOf)
                   else none

/-! ## The fresh variables

Every name is derived from the restriction's marker key, so two
restrictions in one BGP never collide, and every prefix is one
`SPARQL.isRewriteInternalVar` recognises. -/

def svVarName (k : String) : VarName := "_sv_" ++ k
def avAnchorVarName (k : String) : VarName := "_av_anchor_" ++ k
def avBadVarName (k : String) : VarName := "_av_bad_" ++ k
def mcVarName (k : String) : VarName := "_mc_" ++ k
def mxcVarName (k : String) : VarName := "_mxc_" ++ k
def mxqc1RestrVarName (k : String) : VarName := "_mxqc1_r_" ++ k
def mxqc1AnchorVarName (k : String) : VarName := "_mxqc1_anchor_" ++ k
def excVarName (k : String) : VarName := "_exc_" ++ k
def coVarName (k : String) : VarName := "_co_" ++ k

/-! ## Reading a restriction's parts

The F* arms all require the `owl:onProperty` value to be an IRI and
fall back to the leaf otherwise, because a variable predicate cannot be
pinned down. `patternIri` is that guard. -/

def patternIri : PatternTerm → Option WfIri
  | .iri i => some i
  | _ => none

/-- A cardinality value, tried unqualified then qualified — the F*
order. A non-literal or unparseable object yields `none`, which sends
the arm to its leaf fall-back. -/
def cardValue (b : Bgp) (k : String) (unqualified qualified : WfIri) : Option Int :=
  match bgpFindFirstObj b k unqualified with
  | some (.literal l) => SPARQL.parseIntString l.val.lexicalForm
  | _ =>
      match bgpFindFirstObj b k qualified with
      | some (.literal l) => SPARQL.parseIntString l.val.lexicalForm
      | _ => none

def xsdNonNegativeInteger : WfIri :=
  ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩

/-- `"1"^^xsd:nonNegativeInteger`, the object of the shape triple the
`maxQualifiedCardinality` 1 arm emits. -/
def oneNonNegIntegerLiteral : WfLiteral :=
  ⟨{ lexicalForm := "1", datatype := xsdNonNegativeInteger,
     langTag := none, direction := none },
   by simp [literalWf, xsdNonNegativeInteger, rdfLangString, rdfDirLangString,
            Subtype.ext_iff]⟩

/-! ## The expander -/

def expandCeSubject (b : Bgp) (subj : PatternSubject) : PatternTerm → Nat → QueryPattern
  | op, 0 => .bgp (singleTypeBgp subj op)
  | op, n + 1 =>
      match ceCombinatorForTerm b op with
      | none => .bgp (singleTypeBgp subj op)
      | some (k, some .intersect, _) =>
          match extractFlatIntersection b k with
          | none => .bgp (singleTypeBgp subj op)
          | some operands =>
              joinPatterns (operands.map (fun o => expandCeSubject b subj o n))
      | some (k, some .union, _) =>
          match extractFlatUnion b k with
          | none => .bgp (singleTypeBgp subj op)
          | some operands =>
              match operands.map (fun o => expandCeSubject b subj o n) with
              | [] => .bgp (singleTypeBgp subj op)
              | [g] => g
              | g :: tl => wrapDistinctOverPattern (unionLadder g tl)
      | some (k, none, some .someValuesFrom) =>
          -- `_:r owl:onProperty :p ; owl:someValuesFrom F` becomes
          -- `subj :p ?_sv_k` conjoined with F expanded at `?_sv_k`.
          match (bgpFindFirstObj b k owlOnProperty).bind patternIri,
                bgpFindFirstObj b k owlSomeValuesFrom with
          | some prop, some filler =>
              let v := svVarName k
              joinPatterns
                [ .bgp [{ s := subj, p := .iri prop, o := .var v }],
                  expandCeSubject b (.var v) filler n ]
          | _, _ => .bgp (singleTypeBgp subj op)
      | some (k, none, some .allValuesFrom) =>
          -- `_:r owl:onProperty :p ; owl:allValuesFrom F` becomes an
          -- anchor triple under a FILTER NOT EXISTS chain. The anchor
          -- asserts "subj has at least one :p link", which is what
          -- excludes vacuously-true subjects.
          match (bgpFindFirstObj b k owlOnProperty).bind patternIri,
                bgpFindFirstObj b k owlAllValuesFrom with
          | some prop, some filler =>
              let anchorV := avAnchorVarName k
              let badV := avBadVarName k
              let anchorPat : QueryPattern :=
                .bgp [{ s := subj, p := .iri prop, o := .var anchorV }]
              let badPat : QueryPattern :=
                .bgp [{ s := subj, p := .iri prop, o := .var badV }]
              -- A named-class filler is one branch; a union filler is
              -- one branch per operand; every other shape falls back to
              -- the leaf, as in the F* source.
              match (match ceCombinatorForTerm b filler with
                     | none => some [filler]
                     | some (kf, some .union, _) => extractFlatUnion b kf
                     | _ => none) with
              | none => .bgp (singleTypeBgp subj op)
              | some branches =>
                  .filter
                    (.notExistsPat
                      (branches.foldl
                        (fun cur br =>
                          .filter (.notExistsPat
                                    (expandCeSubject b (.var badV) br n)) cur)
                        badPat))
                    anchorPat
          | _, _ => .bgp (singleTypeBgp subj op)
      | some (k, none, some .minCardinality) =>
          -- N = 0 is trivially satisfied, so it contributes nothing.
          -- N >= 1 unqualified: re-emit the ORIGINAL pattern — the
          -- type-consumer triple plus the marker's shape triples.
          -- `QueryMaterialise.augmentForQuery` guarantees the queried
          -- graph holds a node stating this expression whose members
          -- are exactly the `Mat.isMember`-proved individuals, so the
          -- original pattern matches that node with EXACT counting.
          -- The old edge pattern `subj prop ?v` missed members whose
          -- membership is type-derived with no asserted edge (W3C
          -- `sparqldl` parent4: Alice), and over-approximated N >= 2.
          -- Qualified (owl:onClass) keeps the edge + filler route.
          match (bgpFindFirstObj b k owlOnProperty).bind patternIri,
                cardValue b k owlMinCardinality owlMinQualifiedCardinality with
          | some prop, some cardN =>
              if cardN <= 0 then .empty
              else
                let v := mcVarName k
                let propPat : QueryPattern :=
                  .bgp [{ s := subj, p := .iri prop, o := .var v }]
                match bgpFindFirstObj b k owlOnClass with
                | some filler =>
                    joinPatterns [propPat, expandCeSubject b (.var v) filler n]
                | none =>
                    .bgp (singleTypeBgp subj op ++
                          b.filter (fun tp => subjectMarkerKey tp.s == some k))
          | _, _ => .bgp (singleTypeBgp subj op)
      | some (k, none, some .maxCardinality) =>
          match (bgpFindFirstObj b k owlOnProperty).bind patternIri,
                cardValue b k owlMaxCardinality owlMaxQualifiedCardinality with
          | some prop, some cardN =>
              if cardN == 0 then
                -- FILTER NOT EXISTS { subj :p ?_mxc_k [ . ?_mxc_k a C ] },
                -- anchored on the empty pattern so the constraint is the
                -- whole group.
                let v := mxcVarName k
                let propPat : QueryPattern :=
                  .bgp [{ s := subj, p := .iri prop, o := .var v }]
                let inner : QueryPattern :=
                  match bgpFindFirstObj b k owlOnClass with
                  | some filler =>
                      joinPatterns [propPat, expandCeSubject b (.var v) filler n]
                  | none => propPat
                .filter (.notExistsPat inner) .empty
              else if cardN == 1 then
                -- N = 1 QUALIFIED only. The closure materialises a
                -- canonical restriction bnode for this shape, and the
                -- query CE carries a different, query-side bnode id, so
                -- the leaf form cannot match. Discover the canonical by
                -- its four shape triples against a fresh variable, then
                -- assert membership.
                --
                -- The anchor triple `subj :p ?_mxqc1_anchor_k` is
                -- NARROW and deliberately so: see
                -- <https://github.com/danbri/factoidal/issues/236>. It
                -- multiplies rows per :p edge and drops individuals for
                -- which max-1 holds vacuously (zero :p edges). The port
                -- reproduces the narrowness rather than repairing it,
                -- because a repair here would make the two trees
                -- compute different things.
                match (bgpFindFirstObj b k owlOnClass).bind patternIri with
                | some cIri =>
                    let rv := mxqc1RestrVarName k
                    let av := mxqc1AnchorVarName k
                    .bgp
                      [ { s := .var rv, p := .iri rdfType, o := .iri owlRestriction },
                        { s := .var rv, p := .iri owlOnProperty, o := .iri prop },
                        { s := .var rv, p := .iri owlMaxQualifiedCardinality,
                          o := .literal oneNonNegIntegerLiteral },
                        { s := .var rv, p := .iri owlOnClass, o := .iri cIri },
                        { s := subj, p := .iri rdfType, o := .var rv },
                        { s := subj, p := .iri prop, o := .var av } ]
                | none => .bgp (singleTypeBgp subj op)
              else
                -- N < 0, or N >= 2, which needs n+1 distinct variables
                -- and pairwise filters.
                .bgp (singleTypeBgp subj op)
          | _, _ => .bgp (singleTypeBgp subj op)
      | some (k, none, some .exactCardinality) =>
          -- Exact N is min N and max N. N = 0 is the max-zero
          -- constraint; N >= 1 emits the min side only, so it is sound
          -- and incomplete, as the F* source states.
          match (bgpFindFirstObj b k owlOnProperty).bind patternIri,
                cardValue b k owlCardinality owlQualifiedCardinality with
          | some prop, some cardN =>
              if cardN < 0 then .bgp (singleTypeBgp subj op)
              else
                let v := excVarName k
                let propPat : QueryPattern :=
                  .bgp [{ s := subj, p := .iri prop, o := .var v }]
                let withFiller : QueryPattern :=
                  match bgpFindFirstObj b k owlOnClass with
                  | some filler =>
                      joinPatterns [propPat, expandCeSubject b (.var v) filler n]
                  | none => propPat
                if cardN == 0 then .filter (.notExistsPat withFiller) .empty
                else withFiller
          | _, _ => .bgp (singleTypeBgp subj op)
      | some (k, none, some .complementOf) =>
          -- `subj rdf:type (complementOf C)` holds when subj is NOT a
          -- C. A FILTER NOT EXISTS would be closed-world, so the F*
          -- source targets DISJOINTNESS instead: subj has some type ?d
          -- declared disjoint from C, in either direction.
          --
          -- Sound and monotonic; incomplete, because complement can
          -- also follow from explicit negative type assertions and from
          -- closure-side disjointWith propagation, neither of which is
          -- synthesised here.
          match (complementOfTarget b k).bind patternIri with
          | some cIri =>
              let v := coVarName k
              let typeTriple : TriplePattern :=
                { s := subj, p := .iri rdfType, o := .var v }
              let forward : Bgp :=
                [ typeTriple,
                  { s := .var v, p := .iri owlDisjointWith, o := .iri cIri } ]
              let reverse : Bgp :=
                [ typeTriple,
                  { s := .iri cIri, p := .iri owlDisjointWith, o := .var v } ]
              wrapDistinctOverPattern (.union (.bgp forward) (.bgp reverse))
          | none => .bgp (singleTypeBgp subj op)
      -- a flat combinator paired with a restriction cannot arise:
      -- `ceCombinatorForTerm` fills exactly one of the two
      | some (_, _, _) => .bgp (singleTypeBgp subj op)

/-! ## What the boundary guarantees -/

/-- Out of fuel is the identity rewrite. -/
theorem expandCeSubject_zero (b : Bgp) (subj : PatternSubject) (op : PatternTerm) :
    expandCeSubject b subj op 0 = .bgp (singleTypeBgp subj op) := rfl

/-- A term that is no class expression at all is left alone. -/
theorem expandCeSubject_leaf (b : Bgp) (subj : PatternSubject) (op : PatternTerm)
    (n : Nat) (h : ceCombinatorForTerm b op = none) :
    expandCeSubject b subj op (n + 1) = .bgp (singleTypeBgp subj op) := by
  simp only [expandCeSubject, h]

/-- **A malformed restriction degrades to the identity, not to
something wrong.** Every restriction arm except `complementOf` requires
an IRI-valued `owl:onProperty`; a missing or variable predicate cannot
be pinned down, so the arm emits the pre-rewrite triple. That is the F\*
source's own stated fall-back: sound, and it never adds a solution.

`complementOf` is excluded because it reads `owl:complementOf` and
never looks at `owl:onProperty`. -/
theorem expandCeSubject_noOnProperty_is_leaf (b : Bgp) (subj : PatternSubject)
    (op : PatternTerm) (n : Nat) (k : String) (r : Restriction)
    (hr : r ≠ .complementOf)
    (h : ceCombinatorForTerm b op = some (k, none, some r))
    (hp : (bgpFindFirstObj b k owlOnProperty).bind patternIri = none) :
    expandCeSubject b subj op (n + 1) = .bgp (singleTypeBgp subj op) := by
  cases r <;>
    first
      | exact absurd rfl hr
      | simp only [expandCeSubject, h, hp]

/-- A complement whose target is not a named class also falls back to
the leaf. -/
theorem expandCeSubject_complementNonIri_is_leaf (b : Bgp) (subj : PatternSubject)
    (op : PatternTerm) (n : Nat) (k : String)
    (h : ceCombinatorForTerm b op = some (k, none, some .complementOf))
    (hc : (complementOfTarget b k).bind patternIri = none) :
    expandCeSubject b subj op (n + 1) = .bgp (singleTypeBgp subj op) := by
  simp only [expandCeSubject, h, hc]

/-- Minimum cardinality zero is trivially satisfied, so it contributes
no constraint at all — the one arm that returns the empty pattern
rather than a triple. -/
theorem expandCeSubject_minCard_zero (b : Bgp) (subj : PatternSubject)
    (op : PatternTerm) (n : Nat) (k : String) (prop : WfIri) (cardN : Int)
    (h : ceCombinatorForTerm b op = some (k, none, some .minCardinality))
    (hp : (bgpFindFirstObj b k owlOnProperty).bind patternIri = some prop)
    (hc : cardValue b k owlMinCardinality owlMinQualifiedCardinality = some cardN)
    (hz : cardN <= 0) :
    expandCeSubject b subj op (n + 1) = .empty := by
  simp only [expandCeSubject, h, hp, hc, if_pos hz]

/-! ## Build-time checks -/

private def cA : WfIri := ⟨"http://example.org/A", by decide⟩
private def cB : WfIri := ⟨"http://example.org/B", by decide⟩
private def cP : WfIri := ⟨"http://example.org/p", by decide⟩

/-! An intersection of two named classes at `?x`: two conjuncts. -/
private def interB : Bgp :=
  [ { s := .bnode "c",  p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil } ]

#guard (match expandCeSubject interB (.var "x") (.bnode "c") 5 with
        | .join (.bgp l) (.bgp r) => l.length == 1 && r.length == 1
        | _ => false)

/-! A union of two named classes: a DISTINCT-wrapped ladder. -/
private def unionB : Bgp :=
  [ { s := .bnode "c",  p := .iri owlUnionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil } ]

#guard (match expandCeSubject unionB (.var "x") (.bnode "c") 5 with
        | .subSelect _ => true
        | _ => false)

/-! An existential restriction with a named filler: the property triple
joined to the filler's leaf, and the fresh variable is `_sv_r`. -/
private def svfB : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlSomeValuesFrom, o := .iri cA } ]

#guard (match expandCeSubject svfB (.var "x") (.bnode "r") 5 with
        | .join (.bgp l) (.bgp r) => l.length == 1 && r.length == 1
        | _ => false)
#guard svVarName "r" == "_sv_r"
#guard L4Factoidal.SPARQL.isRewriteInternalVar (svVarName "r") == true

/-! A named class is a leaf. -/
#guard (match expandCeSubject interB (.var "x") (.iri cA) 5 with
        | .bgp out => out.length == 1
        | _ => false)

/-! A universal restriction with a named filler becomes the anchor
triple under a FILTER NOT EXISTS chain. The anchor is what excludes
subjects that satisfy the restriction vacuously. -/
private def avfB : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlAllValuesFrom, o := .iri cA } ]
#guard (match expandCeSubject avfB (.var "x") (.bnode "r") 5 with
        | .filter (.notExistsPat _) (.bgp anchor) => anchor.length == 1
        | _ => false)
#guard avAnchorVarName "r" == "_av_anchor_r"
#guard L4Factoidal.SPARQL.isRewriteInternalVar (avAnchorVarName "r") == true
#guard L4Factoidal.SPARQL.isRewriteInternalVar (avBadVarName "r") == true

/-! A restriction whose `owl:onProperty` is a VARIABLE falls back to
the leaf, as in the F* source. The first Lean version of the
`someValuesFrom` arm did not, and put the variable in the predicate
position instead. -/
private def svfVarPred : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .var "p" },
    { s := .bnode "r", p := .iri owlSomeValuesFrom, o := .iri cA } ]
#guard (match expandCeSubject svfVarPred (.var "x") (.bnode "r") 5 with
        | .bgp out => out == singleTypeBgp (.var "x") (.bnode "r")
        | _ => false)

/-! Minimum cardinality zero contributes nothing. -/
private def minCard0B : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlMinCardinality,
      o := .literal ⟨{ lexicalForm := "0", datatype := xsdNonNegativeInteger,
                       langTag := none, direction := none },
                     by simp [literalWf, xsdNonNegativeInteger, rdfLangString,
                              rdfDirLangString, Subtype.ext_iff]⟩ } ]
#guard (match expandCeSubject minCard0B (.var "x") (.bnode "r") 5 with
        | .empty => true | _ => false)

/-! Minimum cardinality one re-emits the original pattern: the type
triple plus the marker's two shape triples (the augmented graph's
realising node is what it matches). -/
private def minCard1B : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlMinCardinality,
      o := .literal ⟨{ lexicalForm := "1", datatype := xsdNonNegativeInteger,
                       langTag := none, direction := none },
                     by simp [literalWf, xsdNonNegativeInteger, rdfLangString,
                              rdfDirLangString, Subtype.ext_iff]⟩ } ]
#guard (match expandCeSubject minCard1B (.var "x") (.bnode "r") 5 with
        | .bgp out => out.length == 3
        | _ => false)

/-! Maximum qualified cardinality one emits the six-triple shape: four
shape triples, the membership triple, and the narrow anchor recorded at
<https://github.com/danbri/factoidal/issues/236>. -/
private def maxQc1B : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlOnClass, o := .iri cA },
    { s := .bnode "r", p := .iri owlMaxQualifiedCardinality,
      o := .literal oneNonNegIntegerLiteral } ]
#guard (match expandCeSubject maxQc1B (.var "x") (.bnode "r") 5 with
        | .bgp out => out.length == 6
        | _ => false)

/-! Maximum cardinality one UNQUALIFIED has no canonical in the data to
bind against, so it is the leaf. -/
private def maxCard1B : Bgp :=
  [ { s := .bnode "r", p := .iri owlOnProperty, o := .iri cP },
    { s := .bnode "r", p := .iri owlMaxCardinality,
      o := .literal oneNonNegIntegerLiteral } ]
#guard (match expandCeSubject maxCard1B (.var "x") (.bnode "r") 5 with
        | .bgp out => out == singleTypeBgp (.var "x") (.bnode "r")
        | _ => false)

/-! A complement of a named class becomes the two-branch disjointness
UNION, wrapped in a DISTINCT sub-select. -/
private def compB : Bgp :=
  [ { s := .bnode "r", p := .iri owlComplementOf, o := .iri cA } ]
#guard (match expandCeSubject compB (.var "x") (.bnode "r") 5 with
        | .subSelect _ => true | _ => false)
#guard L4Factoidal.SPARQL.isRewriteInternalVar (coVarName "r") == true

/-! Zero fuel is the identity. -/
#guard (match expandCeSubject interB (.var "x") (.bnode "c") 0 with
        | .bgp out => out == singleTypeBgp (.var "x") (.bnode "c")
        | _ => false)

/-! ## Axiom audit -/

#print axioms expandCeSubject_leaf
#print axioms expandCeSubject_noOnProperty_is_leaf
#print axioms expandCeSubject_complementNonIri_is_leaf
#print axioms expandCeSubject_minCard_zero
end L4Factoidal.OWL.QueryRewriteCore
