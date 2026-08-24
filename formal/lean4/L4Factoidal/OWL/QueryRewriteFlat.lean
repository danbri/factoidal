/-
L4Factoidal.OWL.QueryRewriteFlat — layer 2 of the port of
`OWL.QueryRewrite`: the flat intersection rewrite over a BGP, and the
pieces the union branch needs.

Layer 1 (`OWL/QueryRewriteCore.lean`) decides what the OPERANDS of a
flat class expression are. This layer decides what happens to the BGP:

    ?x rdf:type _:c .  _:c owl:intersectionOf ( :A :B ) .
      ⇒  ?x rdf:type :A .  ?x rdf:type :B .

Three kinds of triple are distinguished, and every triple is exactly
one of them:

* MARKER BOOKKEEPING — `_:c owl:intersectionOf …`, `_:c owl:unionOf …`,
  `_:c rdf:type owl:Class`, and the `rdf:first`/`rdf:rest` cells of the
  collection. Deleted: they describe the class expression, not the data.
* CONSUMER — `?x rdf:type _:c`. Replaced by one triple per operand.
* Everything else — kept unchanged.

The union branch's residue and consumer collection are here too
(`rewriteBgpStripMarker`, `rewriteBgpCollectConsumers`); the ladder that
assembles them into a `UNION` chain is not, so `OWL.QueryRewrite` stays
not covered and no alias was added.

## What is proved

`rewriteBgpIntersection_mem`: every triple the rewrite emits is either a
triple of the input BGP, or `⟨s, rdf:type, o⟩` for an `s` that already
appeared as a consumer subject and an `o` that is one of the operands.

Combined with layer 1's `extractFlatIntersection_mem` — every operand is
itself an object in the BGP — that says the rewrite invents no IRI. It
is not answer-preservation, which needs the entailment regime and is
where the narrowness recorded at
<https://github.com/danbri/factoidal/issues/236> lives. It is the
weaker claim that has to hold first.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryRewriteCore

namespace L4Factoidal.OWL.QueryRewriteCore

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.SPARQL
open L4Factoidal.OWL.RL (owlIntersectionOf owlUnionOf owlClass)

/-! ## The collection's own cells

`rdf:first`/`rdf:rest` triples belong to the class expression, so the
rewrite deletes them. These are their subject keys. -/

def collectionChainKeysAcc (b : Bgp) : PatternTerm → List String → Nat → List String
  | _, acc, 0 => acc
  | head, acc, n + 1 =>
      match markerKey head with
      | none => acc
      | some k =>
          let acc' := if acc.contains k then acc else k :: acc
          match bgpFindFirstObj b k rdfRest with
          | some tl => collectionChainKeysAcc b tl acc' n
          | none => acc'

def collectionChainKeys (b : Bgp) (head : PatternTerm) : List String :=
  collectionChainKeysAcc b head [] (b.length + 1)

/-! ## The three kinds of triple -/

/-- Does this triple describe the marker rather than the data? -/
def isMarkerBookkeeping (markerK : String) (chainKeys : List String)
    (tp : TriplePattern) : Bool :=
  match subjectMarkerKey tp.s, tp.p with
  | some sk, .iri p =>
      if sk == markerK then
        p == owlIntersectionOf || p == owlUnionOf ||
        (p == rdfType && (match tp.o with
                          | .iri oi => oi == owlClass
                          | _ => false))
      else if chainKeys.contains sk then
        p == rdfFirst || p == rdfRest
      else false
  | _, _ => false

/-- `?x rdf:type _:c` — the triple the rewrite replaces. -/
def isConsumerTriple (markerK : String) (tp : TriplePattern) : Bool :=
  match tp.p with
  | .iri p =>
      p == rdfType &&
      (match markerKey tp.o with
       | some k => k == markerK
       | none => false)
  | _ => false

/-- One consumer triple becomes one triple per operand, subject kept. -/
def expandConsumerForIntersection (tp : TriplePattern) (operands : List PatternTerm) :
    List TriplePattern :=
  operands.map (fun o => { s := tp.s, p := .iri rdfType, o := o })

/-! ## The rewrite -/

def rewriteTripleIntersection (markerK : String) (chainKeys : List String)
    (operands : List PatternTerm) (tp : TriplePattern) : List TriplePattern :=
  if isMarkerBookkeeping markerK chainKeys tp then []
  else if isConsumerTriple markerK tp then expandConsumerForIntersection tp operands
  else [tp]

def rewriteBgpIntersection (markerK : String) (chainKeys : List String)
    (operands : List PatternTerm) (b : Bgp) : Bgp :=
  b.foldl (fun acc tp => acc ++ rewriteTripleIntersection markerK chainKeys operands tp) []

/-! ## The union branch's two halves

The residue is shared by every branch; the consumers supply the
subjects each branch re-types. Assembling them into a `UNION` ladder is
layer 3. -/

def rewriteBgpStripMarker (markerK : String) (chainKeys : List String) (b : Bgp) : Bgp :=
  b.foldl (fun acc tp =>
    if isMarkerBookkeeping markerK chainKeys tp then acc
    else if isConsumerTriple markerK tp then acc
    else acc ++ [tp]) []

def rewriteBgpCollectConsumers (markerK : String) (b : Bgp) : List TriplePattern :=
  b.foldl (fun acc tp => if isConsumerTriple markerK tp then acc ++ [tp] else acc) []

/-! ## The rewrite invents nothing -/

/-- Membership in a left fold that only ever appends. -/
theorem mem_foldl_append {α β : Type} (f : β → List α) :
    ∀ (l : List β) (init : List α) (x : α),
      x ∈ l.foldl (fun acc b => acc ++ f b) init → x ∈ init ∨ ∃ b ∈ l, x ∈ f b
  | [], init, x, h => Or.inl (by simpa using h)
  | b :: rest, init, x, h => by
      simp only [List.foldl_cons] at h
      rcases mem_foldl_append f rest (init ++ f b) x h with hi | ⟨c, hc, hx⟩
      · rcases List.mem_append.mp hi with h1 | h2
        · exact Or.inl h1
        · exact Or.inr ⟨b, List.mem_cons_self, h2⟩
      · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hx⟩

/-- **The rewrite emits no IRI the query did not already carry.** Every
output triple is either an input triple, or an `rdf:type` triple whose
subject came from a consumer of the input and whose object is one of the
operands. -/
theorem rewriteBgpIntersection_mem {markerK : String} {chainKeys : List String}
    {operands : List PatternTerm} {b : Bgp} {t : TriplePattern}
    (h : t ∈ rewriteBgpIntersection markerK chainKeys operands b) :
    t ∈ b ∨ (∃ tp ∈ b, t.s = tp.s ∧ t.p = .iri rdfType ∧ t.o ∈ operands) := by
  rcases mem_foldl_append _ b [] t h with hnil | ⟨tp, htp, hx⟩
  · exact absurd hnil (by simp)
  · unfold rewriteTripleIntersection at hx
    split at hx
    · exact absurd hx (by simp)
    · split at hx
      · simp only [expandConsumerForIntersection, List.mem_map] at hx
        obtain ⟨o, ho, rfl⟩ := hx
        exact Or.inr ⟨tp, htp, rfl, rfl, ho⟩
      · rw [List.mem_singleton.mp hx] at *
        exact Or.inl htp

/-- The residue is a sub-BGP of the input: the union branches share it,
and it adds nothing. -/
theorem rewriteBgpStripMarker_mem {markerK : String} {chainKeys : List String}
    {b : Bgp} {t : TriplePattern}
    (h : t ∈ rewriteBgpStripMarker markerK chainKeys b) : t ∈ b := by
  have hstep : ∀ (l : Bgp) (init : Bgp),
      t ∈ l.foldl (fun acc tp =>
            if isMarkerBookkeeping markerK chainKeys tp then acc
            else if isConsumerTriple markerK tp then acc
            else acc ++ [tp]) init → t ∈ init ∨ t ∈ l := by
    intro l
    induction l with
    | nil => intro init hh; exact Or.inl (by simpa using hh)
    | cons c rest ih =>
        intro init hh
        simp only [List.foldl_cons] at hh
        by_cases h1 : isMarkerBookkeeping markerK chainKeys c
        · rcases ih init (by simpa [h1] using hh) with hi | hr
          · exact Or.inl hi
          · exact Or.inr (List.mem_cons_of_mem _ hr)
        · by_cases h2 : isConsumerTriple markerK c
          · rcases ih init (by simpa [h1, h2] using hh) with hi | hr
            · exact Or.inl hi
            · exact Or.inr (List.mem_cons_of_mem _ hr)
          · rcases ih (init ++ [c]) (by simpa [h1, h2] using hh) with hi | hr
            · rcases List.mem_append.mp hi with ha | hb
              · exact Or.inl ha
              · exact Or.inr (by simpa using List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hb)))
            · exact Or.inr (List.mem_cons_of_mem _ hr)
  rcases hstep b [] h with hi | hr
  · exact absurd hi (by simp)
  · exact hr

/-! ## Build-time checks -/

private def cA : WfIri := ⟨"http://example.org/A", by decide⟩
private def cB : WfIri := ⟨"http://example.org/B", by decide⟩
private def cP : WfIri := ⟨"http://example.org/p", by decide⟩

/-! The worked example from the module header, plus one unrelated
triple that must survive untouched. -/
private def exBgp : Bgp :=
  [ { s := .var "x",    p := .iri rdfType, o := .bnode "c" },
    { s := .bnode "c",  p := .iri owlIntersectionOf, o := .bnode "l1" },
    { s := .bnode "l1", p := .iri rdfFirst, o := .iri cA },
    { s := .bnode "l1", p := .iri rdfRest,  o := .bnode "l2" },
    { s := .bnode "l2", p := .iri rdfFirst, o := .iri cB },
    { s := .bnode "l2", p := .iri rdfRest,  o := .iri rdfNil },
    { s := .var "x",    p := .iri cP,       o := .var "y" } ]

private def exChain : List String := collectionChainKeys exBgp (.bnode "l1")
private def exOps : List PatternTerm := (extractFlatIntersection exBgp "c").getD []

#guard exOps == [PatternTerm.iri cA, PatternTerm.iri cB]
#guard exChain.length == 2

/-! Two consumer replacements and the unrelated triple: three out. -/
#guard (rewriteBgpIntersection "c" exChain exOps exBgp).length == 3
#guard rewriteBgpIntersection "c" exChain exOps exBgp
        == [ { s := .var "x", p := .iri rdfType, o := .iri cA },
             { s := .var "x", p := .iri rdfType, o := .iri cB },
             { s := .var "x", p := .iri cP,      o := .var "y" } ]

/-! Every bookkeeping triple went, and the marker never appears again. -/
#guard (rewriteBgpIntersection "c" exChain exOps exBgp).all
         (fun tp => !isMarkerBookkeeping "c" exChain tp)
#guard (rewriteBgpIntersection "c" exChain exOps exBgp).all
         (fun tp => !isConsumerTriple "c" tp)

/-! The union halves: residue is the unrelated triple, one consumer. -/
#guard rewriteBgpStripMarker "c" exChain exBgp
        == [{ s := .var "x", p := .iri cP, o := .var "y" }]
#guard (rewriteBgpCollectConsumers "c" exBgp).length == 1

/-! A BGP with no marker is returned unchanged. -/
private def plainBgp : Bgp := [{ s := .var "x", p := .iri cP, o := .var "y" }]
#guard rewriteBgpIntersection "c" [] [] plainBgp == plainBgp

/-! ## Axiom audit -/

#print axioms rewriteBgpIntersection_mem
#print axioms rewriteBgpStripMarker_mem

end L4Factoidal.OWL.QueryRewriteCore
