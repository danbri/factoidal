/-
L4Factoidal.RIF.Saturate — RIF Core saturation of an RDF graph.

Port of the FUNCTION of `RIF.Core.Tests.fst`'s `saturate_with_program`
(parse RIF-XML rules, run the forward-chaining fixpoint over the
graph's facts, return the saturated graph) and
`materialise_import_graph` (close an imported graph under the
entailment regime its `Import` profile names, BEFORE the rules see
it). The consumers are the SPARQL 1.1 entailment-regime tests that
name `ent:RIF` (rif01 / rif03 / rif04 / rif06).

## The two directions of RIF-RDF Compatibility §3

* Triples → facts (`factsOfTriple`): a triple is a FRAME
  `s[p -> o]`; `rdf:type` is additionally MEMBERSHIP `s # o` and
  `rdfs:subClassOf` additionally SUBCLASS `s ## o`, because RIF rules
  quantify over RIF's own object model. This mapping also lives in
  `Harness/RifRun.lean` for the RIF Core conformance suite; it is
  DEFINED here (library) and the harness copy is the older twin —
  consolidation tracked with the RIF wiring work.
* Facts → triples (`tripleOfGAtom`): the derived frames, memberships
  and subclass atoms come BACK as triples so a SPARQL query can match
  them. A `pos` atom (a RIF predicate that is not a frame) has no RDF
  form and yields no triple. A constant survives the round trip only
  when its lexical form passes the RDF well-formedness checks
  (`isIri`, `literalWf`); one that does not is dropped, never
  repaired.

Blank nodes ride in `rif:local` space. Rule-local constants are
qualified with a document tag (`Engine.qualifyRule`) BEFORE
saturation, so a rule's `_x` can never capture a data blank node.
-/
import L4Factoidal.RIF.Engine
import L4Factoidal.RIF.Xml
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RIF.Saturate

open L4Factoidal.RDF
open L4Factoidal.RIF

def rdfTypeStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfsSubClassStr : String := "http://www.w3.org/2000/01/rdf-schema#subClassOf"

/-- An RDF term as a RIF constant (RIF-RDF Compatibility §3). -/
def gOfTerm : Term → Option GTerm
  | .iri i     => some (gIri i.val)
  | .literal l =>
      (match l.val.langTag with
       | some tag => some (.const (l.val.lexicalForm ++ "@" ++ tag)
                                  (rdfNs ++ "PlainLiteral"))
       | none     => some (.const l.val.lexicalForm l.val.datatype.val))
  | .bnode b   => some (.const b localSpace)
  | _          => none

def gOfSubject : Subject → GTerm
  | .iri i   => gIri i.val
  | .bnode b => .const b localSpace

/-- A triple as RIF facts. -/
def factsOfTriple (t : Triple) : List GAtom :=
  match gOfTerm t.o with
  | none => []
  | some o =>
      let s := gOfSubject t.s
      let base := [GAtom.frame s (gIri t.p.val) o]
      if t.p.val == rdfTypeStr then base ++ [GAtom.member s o]
      else if t.p.val == rdfsSubClassStr then base ++ [GAtom.sub s o]
      else base

/-- A RIF constant as an RDF term — the reverse reading. `none` when
the constant has no well-formed RDF form. -/
def termOfG : GTerm → Option Term
  | .const l sp =>
      if sp == iriSpace then
        if h : isIri l then some (.iri ⟨l, h⟩) else none
      else if sp == localSpace then some (.bnode l)
      else if sp == rdfNs ++ "PlainLiteral" then
        -- `lex@tag`, tag after the LAST `@` (a lexical form may
        -- contain `@`; a language tag may not).
        match (l.splitOn "@").reverse with
        | tag :: revParts =>
            if revParts.isEmpty then none
            else
              let lex := String.intercalate "@" revParts.reverse
              let lit : Literal := { lexicalForm := lex, datatype := rdfLangString,
                                     langTag := some tag, direction := none }
              if h : literalWf lit then some (.literal ⟨lit, h⟩) else none
        | [] => none
      else
        if h : isIri sp then
          let lit : Literal := { lexicalForm := l, datatype := ⟨sp, h⟩,
                                 langTag := none, direction := none }
          if h2 : literalWf lit then some (.literal ⟨lit, h2⟩) else none
        else none
  | _ => none

def subjectOfG : GTerm → Option Subject
  | .const l sp =>
      if sp == iriSpace then
        if h : isIri l then some (.iri ⟨l, h⟩) else none
      else if sp == localSpace then some (.bnode l)
      else none
  | _ => none

def predOfG : GTerm → Option WfIri
  | .const l sp =>
      if sp == iriSpace then
        if h : isIri l then some ⟨l, h⟩ else none
      else none
  | _ => none

def mkTriple (s p o : GTerm) : Option Triple := do
  let s ← subjectOfG s
  let p ← predOfG p
  let o ← termOfG o
  pure ⟨s, p, o⟩

/-- A derived fact as a triple. -/
def tripleOfGAtom : GAtom → Option Triple
  | .frame o p v => mkTriple o p v
  | .member o c  => do
      let s ← subjectOfG o
      let t ← termOfG c
      pure ⟨s, L4Factoidal.RDFS.rdfType, t⟩
  | .sub c d => do
      let s ← subjectOfG c
      let t ← termOfG d
      pure ⟨s, L4Factoidal.RDFS.rdfsSubClassOf, t⟩
  | .pos _ _ _ => none

/-- The fuel the F* side spends (`RIF.Core.Tests.default_fuel`). -/
def defaultRounds : Nat := 100

/-- Saturate `g` under `rules`: the graph plus every derived fact that
has a triple form and is not already present. Rule-local constants are
qualified with `docTag` first. The round cap and blocked-builtin flags
are DROPPED here, exactly as the F* `saturate_with_program` drops
them: the consumer is a SPARQL evaluation whose comparison against the
expected rows is the test's verdict. -/
def saturateGraph (docTag : String) (rules : List Rule) (g : Graph)
    (rounds : Nat := defaultRounds) : Graph :=
  let facts := g.flatMap factsOfTriple
  let qualified := rules.map (qualifyRule docTag)
  let (fs, _, _) := closure qualified facts rounds
  let derived := fs.filterMap tripleOfGAtom
  g ++ (derived.filter (fun t => !(g.contains t))).eraseDups

/-- Parse RIF-XML and saturate — the F* `saturate_with_program`.
`none` iff the RIF-XML does not parse. The caller resolves and merges
`Import` graphs into `g` first (`Xml.parseRifProgram` exposes the
import list on the parsed document). -/
def saturateWithProgram (rifXml : String) (g : Graph)
    (rounds : Nat := defaultRounds) : Option Graph :=
  match Xml.parseRifProgram rifXml with
  | none => none
  | some doc => some (saturateGraph "rules" doc.rules g rounds)

/-! ## Build-time checks -/

/-! A frame fact round-trips to its triple. -/
#guard
  (tripleOfGAtom (GAtom.frame (gIri "http://ex.org/s")
                              (gIri "http://ex.org/p")
                              (gIri "http://ex.org/o"))).isSome

/-! A `pos` atom has no RDF form. -/
#guard (tripleOfGAtom (GAtom.pos "f" iriSpace [])) == none

/-! Membership comes back as `rdf:type`. -/
#guard
  (match tripleOfGAtom (GAtom.member (gIri "http://ex.org/a")
                                     (gIri "http://ex.org/C")) with
   | some t => t.p.val == rdfTypeStr
   | none   => false)

end L4Factoidal.RIF.Saturate
