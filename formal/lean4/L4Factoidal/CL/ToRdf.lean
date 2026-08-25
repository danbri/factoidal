/-
L4Factoidal.CL.ToRdf — the CL/IKL → RDF dataset bridge.

Translates the ATOMIC fragment of a CL/IKL text (`CL.Syntax`) into an
RDF DATASET (RDF 1.1 Concepts §4) in which EVERY proposition is a
NAMED GRAPH and the default graph carries only DECORATIONS of those
graphs. Nothing is flattened: no sentence atom is copied into the
default graph (owner ruling, 2026-08-25 — statements about statements
use graphs, decorated and linked; the earlier translation flattened
plain sentences and `((that S))` assertions into default-graph
triples). What used to be flat assertion is now visible data: an
`urn:cl:def:asserts` decoration. SPARQL 1.1 `GRAPH` patterns (§13.3)
quantify over the propositions; the `x-ikl-*` regime
(`CL/IklRegime.lean`) makes ASSERTED propositions' content hold in
the default graph at query time.
Tracking: https://github.com/danbri/factoidal/issues/580 and
https://github.com/danbri/factoidal/issues/581

## The name → IRI mapping (documented contract)

Caller supplies a BASE string that must satisfy `RDF.isIri` (non-empty,
contains ':'; e.g. `urn:cl:`). Then:

* a CL NAME `n` maps to `<base ++ percentEncode(n)>`, where
  `percentEncode` keeps exactly RFC 3986 §2.3's unreserved bytes
  (ALPHA / DIGIT / `-` `.` `_` `~`) and %XX-encodes every other UTF-8
  byte (uppercase hex). Injective on names, and never emits a raw ':'.
* the PROPOSITION expressed by a sentence S maps to
  `<base ++ "that:sha256:" ++ hex>` where `hex` is the 64-character
  lowercase SHA-256 (`Crypto.hashHex`) of the UTF-8 bytes of
  `(S.alphaNorm).toClif` — the canonical CLIF serialisation of the
  ALPHA-NORMALIZED sentence (`CL/Alpha.lean`). Two sentences name one
  graph exactly when they are alpha-equivalent, the individuation
  minimum the IKL guide's Appendix B sets (bound-variable renaming
  does not change the proposition;
  https://github.com/danbri/factoidal/issues/589). The name is a
  fixed-length content address, never the sentence packed into the
  IRI; the sentence itself is DATA — see the sentence-record triple
  below. The raw ':' in `"that:"` cannot appear in an encoded name,
  so proposition IRIs and name IRIs never collide.
* inside each proposition's named graph, one SENTENCE-RECORD triple
  `<propIri> <urn:cl:def:sentence> "<(S.alphaNorm).toClif>"` (an
  `xsd:string` literal) records the proposition's canonical sentence
  as queryable data. It is the graph's carrier of any untranslatable
  remainder (a quantified conjunct is still counted in `skipped`, but
  its text is no longer lost), it makes the named graph non-empty
  even when S is wholly untranslatable, and it is NOT included in
  `count`.

## The translation rules

A top-level `and` distributes into per-conjunct sentences, each
translated on its own — sentence individuation, not flattening: each
conjunct gets its own proposition graph and its own decorations. Then
every top-level sentence S maps by exactly one of these clauses:

1. `(pred subj (that S'))`, `pred` and `subj` names — a predication
   ABOUT a proposition: S''s proposition graph is emitted (sentence
   record + S''s translatable atoms, where S' is an atom or an `and`
   of sentences, recursively), and the default graph receives the
   LINK decoration `<subj> <pred> <propIri(S')>`. S' itself is NOT
   asserted (`(believes k (that S'))` does not claim S' — only the
   `x-ikl-*` regime's assertion rule ever moves graph content into
   the default graph, and only for asserted propositions).
2. `((that S'))` — IKL's cancelling-parentheses assertion: asserting
   the proposition asserts S' (`Semantics.sat_assert_that`), so this
   is clause 3 applied to S' — the graph is the SAME graph any
   `(that S')` term names.
3. any other sentence S — an ASSERTED proposition: S's proposition
   graph is emitted (sentence record + S's translatable atoms), and
   the default graph receives the ASSERTION decoration
   `<urn:cl:kb> <urn:cl:def:asserts> <propIri(S)>`. An S wholly
   outside the translatable fragment still gets its graph (record
   only) and its assertion decoration — the sentence is preserved as
   data, and `skipped` counts what was not translated.

Additionally, whenever a proposition graph is emitted (clauses 1–3)
and its sentence is a SINGLE translatable atomic sentence with
translation triple `t`, the default graph receives the RDF-STAR
BRIDGE decoration `<propIri> rdf:reifies <<t>>` — RDF 1.2
`rdf:reifies` with the TRIPLE TERM of `t` as object (RDF 1.2 Concepts
§triple terms; the module header of `Syntax/NTriples.lean` carries
the `<<( … )>>` grammar). A triple term is not asserted by being
mentioned, so the bridge, like every decoration, adds no claim about
the world — it links the proposition to the one RDF statement its
sentence translates to. (The header's rule statement generalises the
binary `(p a b)` case to unary `(P a)` as well: the condition is
"translates to exactly one triple", tested by `atomToTriple`.)

## The translatable fragment (everything else is SKIPPED and COUNTED)

Inside a proposition graph:

* `(p a b)` — binary atomic predication, `p` and `a` names, `b` a name
  or a quoted string → one triple; a quoted string becomes an
  `xsd:string` literal.
* `(P a)` — unary predication, both names → `a rdf:type P`.
* an `and` of sentences distributes, recursively.

Everything else — quantified sentences, `or` / `not` / `if` / `iff`,
equations, sequence markers, non-name subjects/predicates, functional
terms, a nested `(that …)` argument — is not translated: each such
sentence (or conjunct) adds 1 to `skipped`, never silently dropped.
`count` is the number of translated statements: graph-content triples
PLUS default-graph decorations (assertion, link, and bridge triples);
sentence-record triples are excluded. After set-semantic
deduplication the dataset may hold fewer quads than `count` (two
alpha-equivalent asserted sentences produce one graph and one
assertion decoration).
-/

import L4Factoidal.CL.Alpha
import L4Factoidal.Crypto.SHA2
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

/-- The proposition-name hash. Per the Crypto module's hash-agility
directive the algorithm is named ONCE here (with its IRI label
`propHashLabel`) and reached through `Crypto.hashHex` — retiring
SHA-256 is a two-def change plus the documented IRI-format bump. -/
def propHashAlg : L4Factoidal.Crypto.HashAlgorithm := .sha256

/-- The algorithm label inside proposition IRIs (`that:sha256:`). -/
def propHashLabel : String := "sha256"

/-- The canonical sentence text a proposition is keyed and recorded
by: the CLIF serialisation of the alpha-normalized sentence
(`CL/Alpha.lean`; IKL guide Appendix B individuation, issue 589). -/
def propNormClif (s : Sentence) : String := s.alphaNorm.toClif

/-- The proposition IRI of a sentence (see the module header's
mapping): `<base ++ "that:sha256:" ++ hex64>`, a fixed-length content
address over `propNormClif`. Well-formedness is by `isIri_append`
exactly as for name IRIs — the suffix's shape (64 lowercase hex
characters, no raw ':' beyond the two separators) needs no
per-sentence reasoning. -/
def propIri (b : IriBase) (s : Sentence) : RDF.WfIri :=
  b.mk' ("that:" ++ propHashLabel ++ ":" ++
         L4Factoidal.Crypto.hashHex propHashAlg (propNormClif s))

/-- `rdf:type` (the unary-predication predicate). -/
def rdfTypeIri : RDF.WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

/-- `rdf:reifies` (RDF 1.2; the bridge-decoration predicate — see the
module header's bridge rule). -/
def rdfReifiesIri : RDF.WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies", rfl⟩

/-- The sentence-record predicate: relates a proposition's graph name
to the canonical CLIF text of its sentence (module header). A fixed
absolute IRI, deliberately outside every `<base>` namespace a caller
can occupy with names (`percentEncode` never emits ':'). -/
def clDefSentenceIri : RDF.WfIri :=
  ⟨"urn:cl:def:sentence", rfl⟩

/-- The assertion-decoration predicate (module header, clause 3). Same
fixed-namespace rationale as `clDefSentenceIri`. -/
def clDefAssertsIri : RDF.WfIri :=
  ⟨"urn:cl:def:asserts", rfl⟩

/-- The subject of assertion decorations: the knowledge base itself
(the CL text being translated). Fixed absolute IRI, same namespace
rationale as the two `urn:cl:def:` predicates. -/
def clKbIri : RDF.WfIri :=
  ⟨"urn:cl:kb", rfl⟩

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

/-- The triples of a proposition's content: a translatable atom is one
triple, an `and` recurses; anything else is skipped and counted.
Returns (triples, translated, skipped). -/
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
(set-semantic union either way). An empty graph adds nothing (the
proposition clauses below never pass one — the sentence record is
always present). -/
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
statements (graph-content triples + decorations; module header), and
the number of skipped sentences/conjuncts. -/
structure ToRdfResult where
  ds : RDF.Dataset
  count : Nat
  skipped : Nat

/-- The sentence-record triple of a proposition graph. -/
def recordTriple (pIri : RDF.WfIri) (s : Sentence) : RDF.Triple :=
  { s := .iri pIri, p := clDefSentenceIri,
    o := .literal (RDF.Literal.string (propNormClif s)) }

/-- The rdf-star bridge decoration (module header): the proposition
graph name `rdf:reifies` the RDF 1.2 triple term of its single-atom
translation. -/
def bridgeTriple (pIri : RDF.WfIri) (t : RDF.Triple) : RDF.Triple :=
  { s := .iri pIri, p := rdfReifiesIri, o := .tripleTerm t.s t.p t.o }

/-- The bridge decoration of a proposition, when its sentence is one
translatable atomic sentence (with the count of bridges emitted, for
`count`). -/
def bridgeOf (b : IriBase) (pIri : RDF.WfIri) (s : Sentence) :
    List RDF.Triple × Nat :=
  match atomToTriple b s with
  | some t => ([bridgeTriple pIri t], 1)
  | none => ([], 0)

/-- Emit proposition S's named graph (record + content) and any bridge
decoration, add `extraDecorations` (link or assertion triples) to the
default graph, and account for `count`/`skipped`. The shared engine of
the module header's clauses 1–3. -/
def emitProposition (b : IriBase) (acc : ToRdfResult) (s : Sentence)
    (extraDecorations : List RDF.Triple) : ToRdfResult :=
  let pIri := propIri b s
  let (g, c, k) := sentenceTriples b s
  let (bridges, nb) := bridgeOf b pIri s
  let newDefault :=
    (extraDecorations ++ bridges).foldl (fun d t => d.add t) acc.ds.default
  { ds := addToNamed { acc.ds with default := newDefault }
            (.iri pIri) (recordTriple pIri s :: g),
    count := acc.count + extraDecorations.length + nb + c,
    skipped := acc.skipped + k }

mutual

/-- Translate one top-level sentence into the accumulator (the module
header's clauses, in order). -/
def translateTop (b : IriBase) (acc : ToRdfResult) : Sentence → ToRdfResult
  | .conj ss => translateTops b acc ss
  | .atom (.name pred) [.term (.name subj), .term (.that s)] =>
      -- Clause 1: predication about a proposition — link decoration,
      -- no assertion.
      emitProposition b acc s
        [{ s := .iri (nameIri b subj), p := nameIri b pred,
           o := .iri (propIri b s) }]
  | .atom (.that s) [] =>
      -- Clause 2: cancelling-parentheses assertion of the proposition.
      emitProposition b acc s
        [{ s := .iri clKbIri, p := clDefAssertsIri, o := .iri (propIri b s) }]
  | s =>
      -- Clause 3: an asserted sentence.
      emitProposition b acc s
        [{ s := .iri clKbIri, p := clDefAssertsIri, o := .iri (propIri b s) }]

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
-- proposition becomes a named graph (record + content), the context
-- link and the rdf:reifies bridge decorate the default graph. The
-- graph name is the sha256 content address of the (alpha-normalized)
-- canonical CLIF — `echo -n '(Dead OBL)' | sha256sum`. Nothing about
-- OBL lands in the default graph: `ist` does not assert.
#guard clifToNQuads "urn:cl:" "(ist c (that (Dead OBL)))"
  == some ("<urn:cl:c> <urn:cl:ist> " ++
           "<urn:cl:that:sha256:627ab6c4ca999f2605c342e052ef3fe6ae4f8c9a5744df8a09ef4f66819eddd0> .\n" ++
           "<urn:cl:that:sha256:627ab6c4ca999f2605c342e052ef3fe6ae4f8c9a5744df8a09ef4f66819eddd0> " ++
           "<http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> " ++
           "<<( <urn:cl:OBL> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:cl:Dead> )>> .\n" ++
           "<urn:cl:that:sha256:627ab6c4ca999f2605c342e052ef3fe6ae4f8c9a5744df8a09ef4f66819eddd0> " ++
           "<urn:cl:def:sentence> \"(Dead OBL)\" " ++
           "<urn:cl:that:sha256:627ab6c4ca999f2605c342e052ef3fe6ae4f8c9a5744df8a09ef4f66819eddd0> .\n" ++
           "<urn:cl:OBL> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> " ++
           "<urn:cl:Dead> " ++
           "<urn:cl:that:sha256:627ab6c4ca999f2605c342e052ef3fe6ae4f8c9a5744df8a09ef4f66819eddd0> .\n",
           3, 0)

-- Alpha-variant that-terms name ONE graph (issue 589): the guide's
-- Appendix B pair, asserted, translates to byte-identical N-Quads —
-- the quantified body is skipped and counted, and the sentence
-- record (over the alpha-normal form) carries its text as data. No
-- bridge: the sentence is not a single translatable atom.
#guard clifToNQuads "urn:cl:" "(believes K (that (exists (x)(loves Jim x))))"
  == clifToNQuads "urn:cl:" "(believes K (that (exists (y)(loves Jim y))))"
#guard clifToNQuads "urn:cl:" "(believes K (that (exists (x)(loves Jim x))))"
  == some ("<urn:cl:K> <urn:cl:believes> " ++
           "<urn:cl:that:sha256:98d23403b8111bf633e55edf9b546962a7ba5aadf08e68fe14fa563f21888b65> .\n" ++
           "<urn:cl:that:sha256:98d23403b8111bf633e55edf9b546962a7ba5aadf08e68fe14fa563f21888b65> " ++
           "<urn:cl:def:sentence> \"(exists (v1) (loves Jim v1))\" " ++
           "<urn:cl:that:sha256:98d23403b8111bf633e55edf9b546962a7ba5aadf08e68fe14fa563f21888b65> .\n",
           1, 1)

-- Distinct propositions keep distinct graph names.
#guard ((clifToNQuads "urn:cl:" "(ist c (that (Dead OBL)))")
        == (clifToNQuads "urn:cl:" "(ist c (that (Alive OBL)))")) == false

-- An asserted plain sentence: its proposition graph (record +
-- content), the assertion decoration, and the bridge — no content in
-- the default graph. `echo -n '(married Jack Jill)' | sha256sum`.
#guard clifToNQuads "urn:cl:" "(married Jack Jill)"
  == some ("<urn:cl:kb> <urn:cl:def:asserts> " ++
           "<urn:cl:that:sha256:cf0776be87acf0dbf7c3954ffcefac822e218e14fab0e4edb37f5f2d06ff84c6> .\n" ++
           "<urn:cl:that:sha256:cf0776be87acf0dbf7c3954ffcefac822e218e14fab0e4edb37f5f2d06ff84c6> " ++
           "<http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> " ++
           "<<( <urn:cl:Jack> <urn:cl:married> <urn:cl:Jill> )>> .\n" ++
           "<urn:cl:that:sha256:cf0776be87acf0dbf7c3954ffcefac822e218e14fab0e4edb37f5f2d06ff84c6> " ++
           "<urn:cl:def:sentence> \"(married Jack Jill)\" " ++
           "<urn:cl:that:sha256:cf0776be87acf0dbf7c3954ffcefac822e218e14fab0e4edb37f5f2d06ff84c6> .\n" ++
           "<urn:cl:Jack> <urn:cl:married> <urn:cl:Jill> " ++
           "<urn:cl:that:sha256:cf0776be87acf0dbf7c3954ffcefac822e218e14fab0e4edb37f5f2d06ff84c6> .\n",
           3, 0)

-- A string object stays an xsd:string literal — in the graph, in the
-- record, and inside the bridge's triple term.
#guard clifToNQuads "urn:cl:" "(hasName Jack 'Jack B. Quick')"
  == some ("<urn:cl:kb> <urn:cl:def:asserts> " ++
           "<urn:cl:that:sha256:2e6ceb7063fa9c67fb0c3b7ad9b4c94cee3da057d4df5efb309ede2d5eb9db62> .\n" ++
           "<urn:cl:that:sha256:2e6ceb7063fa9c67fb0c3b7ad9b4c94cee3da057d4df5efb309ede2d5eb9db62> " ++
           "<http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> " ++
           "<<( <urn:cl:Jack> <urn:cl:hasName> \"Jack B. Quick\" )>> .\n" ++
           "<urn:cl:that:sha256:2e6ceb7063fa9c67fb0c3b7ad9b4c94cee3da057d4df5efb309ede2d5eb9db62> " ++
           "<urn:cl:def:sentence> \"(hasName Jack 'Jack B. Quick')\" " ++
           "<urn:cl:that:sha256:2e6ceb7063fa9c67fb0c3b7ad9b4c94cee3da057d4df5efb309ede2d5eb9db62> .\n" ++
           "<urn:cl:Jack> <urn:cl:hasName> \"Jack B. Quick\" " ++
           "<urn:cl:that:sha256:2e6ceb7063fa9c67fb0c3b7ad9b4c94cee3da057d4df5efb309ede2d5eb9db62> .\n",
           3, 0)

-- A top-level `and` distributes: TWO asserted propositions, each with
-- its own graph, assertion decoration and bridge (sentence
-- individuation, not flattening).
#guard (clifToNQuads "urn:cl:" "(and (Boy Bill) (owns Bill Rex))").map
    (fun r => (r.2.1, r.2.2))
  == some (6, 0)
#guard ((clifToNQuads "urn:cl:" "(and (Boy Bill) (owns Bill Rex))").map
    (fun r => r.1)).map (fun nq =>
      (nq.splitOn "<urn:cl:kb> <urn:cl:def:asserts>").length)
  == some 3   -- two assertion decorations

-- The assertion form ((that S)): the proposition is asserted — SAME
-- graph as any (that S) term names, decorated with urn:cl:def:asserts;
-- the conjunction's atoms stay in the proposition's graph. No bridge
-- (not a single atom).
#guard clifToNQuads "urn:cl:" "((that (and (P a) (q a b))))"
  == some ("<urn:cl:kb> <urn:cl:def:asserts> " ++
           "<urn:cl:that:sha256:a71ed173c46624a5f0a778e55348e5b0ecda9802af02484f2718741c35f28b3d> .\n" ++
           "<urn:cl:that:sha256:a71ed173c46624a5f0a778e55348e5b0ecda9802af02484f2718741c35f28b3d> " ++
           "<urn:cl:def:sentence> \"(and (P a) (q a b))\" " ++
           "<urn:cl:that:sha256:a71ed173c46624a5f0a778e55348e5b0ecda9802af02484f2718741c35f28b3d> .\n" ++
           "<urn:cl:a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> " ++
           "<urn:cl:P> " ++
           "<urn:cl:that:sha256:a71ed173c46624a5f0a778e55348e5b0ecda9802af02484f2718741c35f28b3d> .\n" ++
           "<urn:cl:a> <urn:cl:q> <urn:cl:b> " ++
           "<urn:cl:that:sha256:a71ed173c46624a5f0a778e55348e5b0ecda9802af02484f2718741c35f28b3d> .\n",
           3, 0)

-- A belief whose that-body mixes a translatable atom with a
-- quantified sentence: the atom lands in the named graph, the
-- quantified conjunct is skipped AND counted; count = link + content.
#guard (clifToNQuads "urn:cl:"
    "(believes K (that (and (Dog Rex) (forall (x) (P x)))))").map
    (fun r => (r.2.1, r.2.2))
  == some (2, 1)

-- A quantified sentence at top level is still ASSERTED: its graph
-- holds only the sentence record (content skipped and counted), the
-- assertion decorates the default graph — the sentence text is
-- preserved as data, nothing flattens, nothing is dropped.
-- `echo -n '(forall (v1) (if (Boy v1) (Human v1)))' | sha256sum`
#guard clifToNQuads "urn:cl:" "(forall (x) (if (Boy x) (Human x)))"
  == some ("<urn:cl:kb> <urn:cl:def:asserts> " ++
           "<urn:cl:that:sha256:b560e5608d3a91f897e945fcb053b707a8d0d2edd4d9b7f31263ac99c2a9790f> .\n" ++
           "<urn:cl:that:sha256:b560e5608d3a91f897e945fcb053b707a8d0d2edd4d9b7f31263ac99c2a9790f> " ++
           "<urn:cl:def:sentence> \"(forall (v1) (if (Boy v1) (Human v1)))\" " ++
           "<urn:cl:that:sha256:b560e5608d3a91f897e945fcb053b707a8d0d2edd4d9b7f31263ac99c2a9790f> .\n",
           1, 1)

-- An ill-formed base is a named error, not a fallback.
#guard (toRdfDataset "nocolon" []).isOk == false

-- Names needing encoding stay injective and never collide with the
-- `that:` namespace (raw ':' cannot come out of percentEncode).
#guard (nameIri ⟨"urn:cl:", rfl⟩ "that:x").val == "urn:cl:that%3Ax"

end L4Factoidal.CL
