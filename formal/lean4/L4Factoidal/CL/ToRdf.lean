/-
L4Factoidal.CL.ToRdf — the CL/IKL → RDF dataset bridge.

Translates the ATOMIC fragment of a CL/IKL text (`CL.Syntax`) into an
RDF DATASET (RDF 1.1 Concepts §4), with IKL's proposition terms
becoming NAMED GRAPHS. This is the combination the two components buy
together: `(pred subj (that S))` — e.g. `(ist c (that S))`,
`(believes k (that S))` — puts S's translatable atomic content into a
named graph whose name is a deterministic proposition IRI, and links
it from the default graph with `subj pred <propIri>`, so SPARQL 1.1
`GRAPH` patterns (§13.3) quantify over IKL propositions.
Tracking: https://github.com/danbri/factoidal/issues/580

## The name → IRI mapping (documented contract)

Caller supplies a BASE string that must satisfy `RDF.isIri` (non-empty,
contains ':'; e.g. `urn:cl:`). Then:

* a CL NAME `n` maps to `<base ++ percentEncode(n)>`, where
  `percentEncode` keeps exactly RFC 3986 §2.3's unreserved bytes
  (ALPHA / DIGIT / `-` `.` `_` `~`) and %XX-encodes every other UTF-8
  byte (uppercase hex). Injective on names, and never emits a raw ':'.
* the PROPOSITION named by `(that S)` maps to
  `<base ++ "that:" ++ percentEncode(S.toClif)>` — the percent-encoding
  of the CANONICAL CLIF SERIALISATION of S, so the graph name is
  deterministic, reversible by percent-decoding, and equal for two
  that-terms exactly when their sentences serialise identically.
  The raw ':' in `"that:"` cannot appear in an encoded name, so
  proposition IRIs and name IRIs never collide.

## The translatable fragment (everything else is SKIPPED and COUNTED)

Per top-level sentence (a top-level `and` is flattened):

* `(p a b)` — binary atomic predication, `p` and `a` names, `b` a name
  or a quoted string → one triple; a quoted string becomes an
  `xsd:string` literal.
* `(P a)` — unary predication, both names → `a rdf:type P`.
* `(pred subj (that S))` — `pred`, `subj` names → the default-graph
  link triple `subj pred <propIri(S)>`, plus S's content (translatable
  atoms of S, where S is an atom or an `and` of sentences, recursively
  flattened) as triples IN THE NAMED GRAPH `<propIri(S)>`. An
  untranslatable conjunct inside S is skipped and counted; S wholly
  untranslatable still yields the link triple and an empty (absent)
  named graph — the assertion about the proposition survives, its
  content does not.
* `((that S))` — IKL's cancelling-parentheses assertion → S's
  translatable content goes to the DEFAULT graph (asserting the
  proposition is asserting S — `Semantics.sat_assert_that`).

Everything else — quantified sentences, `or` / `not` / `if` / `iff`,
equations, sequence markers, non-name subjects/predicates, functional
terms — is not translated: each such sentence (or conjunct) adds 1 to
`skipped`, never silently dropped. `count` is the number of translated
statements (link triples included); after set-semantic deduplication
the dataset may hold fewer quads than `count`.
-/

import L4Factoidal.CL.Clif
import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.CL

open L4Factoidal.RDF (isIri)

/-! ## Percent-encoding (RFC 3986 §2.1/§2.3) -/

/-- Uppercase hex digit for a nibble. -/
def hexOfNibble (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- RFC 3986 §2.3 unreserved: ALPHA / DIGIT / `-` / `.` / `_` / `~`. -/
def isUnreservedByte (b : UInt8) : Bool :=
  let n := b.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || (48 ≤ n && n ≤ 57) ||
  n == 45 || n == 46 || n == 95 || n == 126

/-- `%XX` for one byte, uppercase hex. -/
def percentEncodeByte (b : UInt8) : String :=
  let n := b.toNat
  String.ofList ['%', hexOfNibble (n / 16), hexOfNibble (n % 16)]

/-- Percent-encode a string's UTF-8 bytes, keeping unreserved bytes. -/
def percentEncode (s : String) : String :=
  s.toUTF8.toList.foldl
    (fun acc b =>
      if isUnreservedByte b then acc.push (Char.ofNat b.toNat)
      else acc ++ percentEncodeByte b)
    ""

/-! ## IRI construction -/

/-- Appending to a well-formed IRI prefix keeps `isIri` (non-emptiness
and the ':' both live in the prefix). -/
theorem isIri_append (a b : String) (h : isIri a = true) : isIri (a ++ b) = true := by
  simp only [isIri, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_true_eq] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · simp_all [String.append_eq_empty_iff]
  · simp_all [String.toList_append]

/-- A validated IRI base: the string plus its `isIri` witness, so every
IRI built from it is well-formed by `isIri_append` — no per-name
runtime check, no fallback IRI. -/
structure IriBase where
  base : String
  wf : isIri base = true

/-- `<base ++ suffix>`, well-formed by construction. -/
def IriBase.mk' (b : IriBase) (suffix : String) : RDF.WfIri :=
  ⟨b.base ++ suffix, isIri_append b.base suffix b.wf⟩

/-- The IRI of a CL name (see the module header's mapping). -/
def nameIri (b : IriBase) (n : String) : RDF.WfIri :=
  b.mk' (percentEncode n)

/-- The proposition IRI of a `that`-term's sentence (see the module
header's mapping). -/
def propIri (b : IriBase) (s : Sentence) : RDF.WfIri :=
  b.mk' ("that:" ++ percentEncode s.toClif)

/-- `rdf:type` (the unary-predication predicate). -/
def rdfTypeIri : RDF.WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

/-! ## The atomic fragment -/

/-- Object-position translation: a name → its IRI, a quoted string →
an `xsd:string` literal. Anything else (functional term, `that`) is
outside the fragment. -/
def objectTerm (b : IriBase) : Term → Option RDF.Term
  | .name n => some (.iri (nameIri b n))
  | .str s => some (.literal (RDF.Literal.string s))
  | _ => none

/-- One atomic sentence → one triple, if it is in the fragment:
`(P a)` → `a rdf:type P`; `(p a b)` → `a p b`. -/
def atomToTriple (b : IriBase) : Sentence → Option RDF.Triple
  | .atom (.name p) [.term (.name a)] =>
      some { s := .iri (nameIri b a), p := rdfTypeIri, o := .iri (nameIri b p) }
  | .atom (.name p) [.term (.name a), .term ob] =>
      (objectTerm b ob).map
        (fun o => { s := .iri (nameIri b a), p := nameIri b p, o := o })
  | _ => none

mutual

/-- The triples of a `that`-body: a translatable atom is one triple, an
`and` recurses; anything else is skipped and counted. Returns
(triples, translated, skipped). -/
def sentenceTriples (b : IriBase) : Sentence → RDF.Graph × Nat × Nat
  | .conj ss => sentencesTriples b ss
  | s =>
      match atomToTriple b s with
      | some t => ([t], 1, 0)
      | none => ([], 0, 1)

/-- `sentenceTriples` over a conjunct list, sums accumulated. -/
def sentencesTriples (b : IriBase) : List Sentence → RDF.Graph × Nat × Nat
  | [] => ([], 0, 0)
  | s :: r =>
      let (g1, c1, k1) := sentenceTriples b s
      let (g2, c2, k2) := sentencesTriples b r
      (g1 ++ g2, c1 + c2, k1 + k2)

end

/-! ## Dataset assembly -/

/-- Merge a graph into the named graph `name`, creating it if absent
(set-semantic union either way). An empty graph adds nothing — an
untranslatable proposition body leaves no empty named graph behind. -/
def addToNamed (ds : RDF.Dataset) (name : RDF.Subject) (g : RDF.Graph) :
    RDF.Dataset :=
  if g.isEmpty then ds
  else if ds.named.any (fun ng => ng.name == name) then
    { ds with named := ds.named.map (fun ng =>
        if ng.name == name then { ng with graph := RDF.Graph.union ng.graph g }
        else ng) }
  else
    { ds with named := ds.named ++ [{ name := name, graph := RDF.Graph.union [] g }] }

/-- Result of a translation: the dataset, the number of translated
statements, and the number of skipped sentences/conjuncts. -/
structure ToRdfResult where
  ds : RDF.Dataset
  count : Nat
  skipped : Nat

mutual

/-- Translate one top-level sentence into the accumulator (the module
header's fragment, clause by clause). -/
def translateTop (b : IriBase) (acc : ToRdfResult) : Sentence → ToRdfResult
  | .conj ss => translateTops b acc ss
  | .atom (.name pred) [.term (.name subj), .term (.that s)] =>
      -- The IKL clause: proposition content → named graph, link triple
      -- → default graph.
      let pIri := propIri b s
      let (g, c, k) := sentenceTriples b s
      let link : RDF.Triple :=
        { s := .iri (nameIri b subj), p := nameIri b pred, o := .iri pIri }
      { ds := addToNamed
                { acc.ds with default := acc.ds.default.add link }
                (.iri pIri) g,
        count := acc.count + 1 + c,
        skipped := acc.skipped + k }
  | .atom (.that s) [] =>
      -- Cancelling parentheses: the proposition's content is asserted
      -- outright, so it lands in the default graph.
      let (g, c, k) := sentenceTriples b s
      { ds := { acc.ds with default := RDF.Graph.union acc.ds.default g },
        count := acc.count + c,
        skipped := acc.skipped + k }
  | s =>
      match atomToTriple b s with
      | some t =>
          { acc with ds := { acc.ds with default := acc.ds.default.add t },
                     count := acc.count + 1 }
      | none => { acc with skipped := acc.skipped + 1 }

/-- `translateTop` over a top-level conjunct list. -/
def translateTops (b : IriBase) (acc : ToRdfResult) : List Sentence → ToRdfResult
  | [] => acc
  | s :: r => translateTops b (translateTop b acc s) r

end

/-- Translate a CL/IKL text (a list of sentences) into an RDF dataset
under `base`. The only error is an ill-formed base. -/
def toRdfDataset (base : String) (ss : List Sentence) : Except String ToRdfResult :=
  if h : isIri base = true then
    .ok (ss.foldl (translateTop ⟨base, h⟩) ⟨RDF.Dataset.empty, 0, 0⟩)
  else
    .error s!"base '{base}' is not an IRI (must be non-empty and contain ':')"

/-! ## Guards — the guide's `ist` example, end to end -/

/-- Parse, translate, and serialise to canonical N-Quads (test entry;
`none` on any failure). -/
def clifToNQuads (base text : String) : Option (String × Nat × Nat) :=
  match parseClifText text with
  | .error _ => none
  | .ok ss =>
      match toRdfDataset base ss with
      | .error _ => none
      | .ok r => some (Syntax.Dataset.toCanonicalNQuads r.ds, r.count, r.skipped)

-- The guide's ist shape ("Contexts and Modalities in IKL"): the
-- proposition becomes a named graph, the context assertion a
-- default-graph triple pointing at it.
#guard clifToNQuads "urn:cl:" "(ist c (that (Dead OBL)))"
  == some ("<urn:cl:c> <urn:cl:ist> <urn:cl:that:%28Dead%20OBL%29> .\n" ++
           "<urn:cl:OBL> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> " ++
           "<urn:cl:Dead> <urn:cl:that:%28Dead%20OBL%29> .\n",
           2, 0)

-- Binary predication with a name object, and with a string object.
#guard clifToNQuads "urn:cl:" "(married Jack Jill)"
  == some ("<urn:cl:Jack> <urn:cl:married> <urn:cl:Jill> .\n", 1, 0)
#guard clifToNQuads "urn:cl:" "(hasName Jack 'Jack B. Quick')"
  == some ("<urn:cl:Jack> <urn:cl:hasName> \"Jack B. Quick\" .\n", 1, 0)

-- Unary predication is rdf:type; a top-level `and` flattens.
#guard clifToNQuads "urn:cl:" "(and (Boy Bill) (owns Bill Rex))"
  == some ("<urn:cl:Bill> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> " ++
           "<urn:cl:Boy> .\n<urn:cl:Bill> <urn:cl:owns> <urn:cl:Rex> .\n",
           2, 0)

-- The assertion form ((that S)) lands S's atoms in the DEFAULT graph.
#guard clifToNQuads "urn:cl:" "((that (and (P a) (q a b))))"
  == some ("<urn:cl:a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> " ++
           "<urn:cl:P> .\n<urn:cl:a> <urn:cl:q> <urn:cl:b> .\n",
           2, 0)

-- A belief whose that-body mixes a translatable atom with a
-- quantified sentence: the atom lands in the named graph, the
-- quantified conjunct is skipped AND counted.
#guard (clifToNQuads "urn:cl:"
    "(believes K (that (and (Dog Rex) (forall (x) (P x)))))").map
    (fun r => (r.2.1, r.2.2))
  == some (2, 1)

-- A quantified sentence at top level: skipped, counted, no quads.
#guard clifToNQuads "urn:cl:" "(forall (x) (if (Boy x) (Human x)))"
  == some ("", 0, 1)

-- An ill-formed base is a named error, not a fallback.
#guard (toRdfDataset "nocolon" []).isOk == false

-- Names needing encoding stay injective and never collide with the
-- `that:` namespace (raw ':' cannot come out of percentEncode).
#guard (nameIri ⟨"urn:cl:", rfl⟩ "that:x").val == "urn:cl:that%3Ax"

end L4Factoidal.CL
