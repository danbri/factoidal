/-
L4Factoidal.OWL.QueryRewriteCore — layer 1 of the port of
`OWL.QueryRewrite` (1,799 lines, 961 of them code).

The F\* module rewrites anonymous class expressions that appear as the
object of `rdf:type` in a SPARQL WHERE clause, so the OWL-RL closure has
named-class `rdf:type` triples to match against:

    ?x rdf:type _:c .  _:c owl:intersectionOf ( :A :B ) .
      ⇒  ?x rdf:type :A .  ?x rdf:type :B .

    ?x rdf:type _:c .  _:c owl:unionOf ( :B :C ) .
      ⇒  { ?x rdf:type :B } UNION { ?x rdf:type :C }

This layer is the part underneath that: node identity for anonymous
nodes, the RDF-collection walk through a BGP, and the two flat
extractors. The rewrite itself, its nested (Phase 4) cases and the
`GraphPattern` traversal are not here, so `OWL.QueryRewrite` stays on
the not-covered list and no alias was added.

## Node keys

A marker bnode can reach the rewriter in two spellings: as a real
`PatternTerm.bnode`, or as a variable the runner already renamed to
`_bnode_<id>`. `markerKey` maps both to the same string, which is what
lets `sameAnonNode` decide whether a subject and an object denote one
anonymous node.

## Known narrowness, carried over

CLAUDE.md records that the shipping rewrite is sound-but-narrow and
tracked at <https://github.com/danbri/factoidal/issues/236>. Nothing
here changes that; this layer only decides what the operands ARE.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.SPARQL.Expr
import L4Factoidal.OWL.Vocabulary
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.OWL.QueryRewriteCore

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.SPARQL
open L4Factoidal.OWL.RL (owlIntersectionOf owlUnionOf)

/-! ## Node keys -/

/-- The prefix the runner uses when it turns a query bnode into a
variable. Port of `bnode_var_prefix`. -/
def bnodeVarPrefix : String := "_bnode_"

/-- Recover the bnode id from such a variable, if that is what it is. -/
def stripBnodePrefix (v : String) : Option String :=
  if strStartsWith v bnodeVarPrefix then
    some (String.ofList (v.toList.drop bnodeVarPrefix.length))
  else none

/-- A canonical identity for an anonymous node in subject position.
Named IRIs and literals have none — they are not anonymous. -/
def subjectMarkerKey : PatternSubject → Option String
  | .bnode b => some b
  | .var v   => stripBnodePrefix v
  | _        => none

/-- The same in object position. -/
def markerKey : PatternTerm → Option String
  | .bnode b => some b
  | .var v   => stripBnodePrefix v
  | _        => none

/-- Do a subject and an object denote the SAME anonymous node? -/
def sameAnonNode (ps : PatternSubject) (pt : PatternTerm) : Bool :=
  match subjectMarkerKey ps, markerKey pt with
  | some k1, some k2 => k1 == k2
  | _, _ => false

/-! ## Looking one triple up in a BGP -/

/-- The first object of `(subject with this key, this predicate, ?)`.
Port of `bgp_find_first_obj`. -/
def bgpFindFirstObj : Bgp → String → WfIri → Option PatternTerm
  | [], _, _ => none
  | tp :: rest, key, pred =>
      match subjectMarkerKey tp.s, tp.p with
      | some k, .iri p =>
          if k == key && p == pred then some tp.o
          else bgpFindFirstObj rest key pred
      | _, _ => bgpFindFirstObj rest key pred

/-! ## Walking an RDF collection through a BGP

Fuel-bounded by the BGP length, as in the F\* source: each step needs
one more `rdf:first`/`rdf:rest` pair, so no walk can exceed it. A
malformed or truncated collection returns what was collected rather
than failing — the caller decides whether an empty result is an
error. -/

def walkCollectionAcc (b : Bgp) : PatternTerm → List PatternTerm → Nat →
    List PatternTerm
  | _, acc, 0 => acc.reverse
  | head, acc, n + 1 =>
      match head with
      -- `rdf:nil` ends the list; any other IRI is a malformed
      -- collection. Both stop the walk.
      | .iri _ => acc.reverse
      | _ =>
          match markerKey head with
          | none => acc.reverse
          | some k =>
              match bgpFindFirstObj b k rdfFirst, bgpFindFirstObj b k rdfRest with
              | some hd, some tl => walkCollectionAcc b tl (hd :: acc) n
              | _, _ => acc.reverse

def walkCollection (b : Bgp) (head : PatternTerm) : List PatternTerm :=
  walkCollectionAcc b head [] (b.length + 1)

/-! ## The two flat extractors -/

/-- The operands of a flat `owl:intersectionOf` on the marker, or
`none` when the BGP holds no such collection. -/
def extractFlatIntersection (b : Bgp) (markerKey : String) :
    Option (List PatternTerm) :=
  match bgpFindFirstObj b markerKey owlIntersectionOf with
  | none => none
  | some listHead =>
      match walkCollection b listHead with
      | [] => none
      | operands => some operands

/-- The same for `owl:unionOf`. -/
def extractFlatUnion (b : Bgp) (markerKey : String) :
    Option (List PatternTerm) :=
  match bgpFindFirstObj b markerKey owlUnionOf with
  | none => none
  | some listHead =>
      match walkCollection b listHead with
      | [] => none
      | operands => some operands

/-! ## Properties worth having before the rewrite is built on this -/

/-- A lookup only ever returns an object that is in the BGP. -/
theorem bgpFindFirstObj_mem : ∀ (b : Bgp) (k : String) (p : WfIri) (t : PatternTerm),
    bgpFindFirstObj b k p = some t → ∃ tp ∈ b, tp.o = t
  | [], _, _, _, h => by simp [bgpFindFirstObj] at h
  | tp :: rest, k, p, t, h => by
      simp only [bgpFindFirstObj] at h
      split at h
      · split at h
        · exact ⟨tp, List.mem_cons_self, by simpa using h⟩
        · obtain ⟨u, hu, hut⟩ := bgpFindFirstObj_mem rest k p t h
          exact ⟨u, List.mem_cons_of_mem _ hu, hut⟩
      · obtain ⟨u, hu, hut⟩ := bgpFindFirstObj_mem rest k p t h
        exact ⟨u, List.mem_cons_of_mem _ hu, hut⟩

/-- The walk never invents an operand: everything it returns was an
`rdf:first` object of some triple in the BGP. This is what stops the
rewrite emitting a class the query never mentioned. -/
theorem walkCollectionAcc_mem (b : Bgp) :
    ∀ (n : Nat) (head : PatternTerm) (acc : List PatternTerm) (t : PatternTerm),
      t ∈ walkCollectionAcc b head acc n →
      t ∈ acc ∨ ∃ tp ∈ b, tp.o = t
  | 0, _, acc, t, h => Or.inl (by
      unfold walkCollectionAcc at h; simpa using h)
  | n + 1, head, acc, t, h => by
      unfold walkCollectionAcc at h
      split at h
      · exact Or.inl (by simpa using h)
      · split at h
        · exact Or.inl (by simpa using h)
        · rename_i k hk
          split at h
          · rename_i hd tl hfirst _
            rcases walkCollectionAcc_mem b n tl (hd :: acc) t h with hacc | hb
            · rcases List.mem_cons.mp hacc with rfl | hrest
              · exact Or.inr (bgpFindFirstObj_mem b k rdfFirst t hfirst)
              · exact Or.inl hrest
            · exact Or.inr hb
          · exact Or.inl (by simpa using h)

theorem walkCollection_mem {b : Bgp} {head t : PatternTerm}
    (h : t ∈ walkCollection b head) : ∃ tp ∈ b, tp.o = t := by
  rcases walkCollectionAcc_mem b (b.length + 1) head [] t h with hacc | hb
  · simp at hacc
  · exact hb

/-- Every operand an extractor returns comes from the BGP too. -/
theorem extractFlatIntersection_mem {b : Bgp} {k : String} {ops : List PatternTerm}
    {t : PatternTerm} (h : extractFlatIntersection b k = some ops) (ht : t ∈ ops) :
    ∃ tp ∈ b, tp.o = t := by
  unfold extractFlatIntersection at h
  split at h
  · exact absurd h (by simp)
  · rename_i listHead _
    split at h
    · exact absurd h (by simp)
    · have hops : walkCollection b listHead = ops := by simpa using h
      exact walkCollection_mem (by rw [hops]; exact ht)

/-! ## Build-time checks -/

private def vX : VarName := "x"
private def cA : WfIri := ⟨"http://example.org/A", by decide⟩
private def cB : WfIri := ⟨"http://example.org/B", by decide⟩

/-! `_:c owl:intersectionOf ( :A :B )` as a BGP, written the way the
runner presents it after bnode-to-variable renaming. -/
private def interBgp : Bgp :=
  [ { s := .bnode "c",  p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil } ]

#guard (extractFlatIntersection interBgp "c").map List.length == some 2
#guard extractFlatIntersection interBgp "c"
        == some [PatternTerm.iri cA, PatternTerm.iri cB]
#guard extractFlatUnion interBgp "c" == none
#guard extractFlatIntersection interBgp "nosuch" == none

/-! The `_bnode_` spelling reaches the same key. -/
#guard stripBnodePrefix "_bnode_c" == some "c"
#guard stripBnodePrefix "x" == none
#guard markerKey (PatternTerm.var "_bnode_c") == some "c"
#guard sameAnonNode (PatternSubject.bnode "c") (PatternTerm.var "_bnode_c") == true
#guard sameAnonNode (PatternSubject.iri cA) (PatternTerm.iri cA) == false

/-! A truncated collection yields what was collected, not a failure. -/
private def truncBgp : Bgp :=
  [ { s := .bnode "c",  p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA } ]
#guard extractFlatIntersection truncBgp "c" == none

/-! ## Axiom audit -/

#print axioms walkCollection_mem
#print axioms extractFlatIntersection_mem

end L4Factoidal.OWL.QueryRewriteCore
