/-
L4Factoidal.Unified.RdfEmbed — the RDF-to-CL translation of stage 1
(https://github.com/danbri/factoidal/issues/598; design document
`docs/designissues/2026-08-25-unified-semantics-lean.md` §2.3).

## The encoding

* IRI `i` → `CL.Term.name i.val` — the IRI string is the name.
* Literal → the functional term
  `funapp (name "urn:cl:def:literalValueOf") [str lex, name dtIri]`,
  a language tag as a third `str` argument, an RDF 1.2 base direction
  as a fourth (`"ltr"`/`"rtl"`). LBase §3.0's
  `LiteralValueOf('sss', TR[ddd])` made concrete.
* Blank node `b` → the bound name `bnodeName b`; a graph translates to
  ONE sentence, the existential closure over the graph's blank nodes
  of the conjunction of one binary predication per triple
  (RDF 1.1 Semantics §5.2 graph satisfaction; LBase §3.0's last row).
* RDF 1.2 triple term →
  `funapp (name "urn:cl:def:tripleTerm") [s, p, o]` — an
  uninterpreted function of the components' denotations, the same
  reading `RDF.Interp.iTt` gives it.

## Bound-name freshness — a deviation from the design document

The design document proposed the `_:` spelling for bound blank-node
names and a freshness LEMMA against the graph's IRI strings. That
spelling cannot support the hypothesis-free stage 1 gate theorem:
`RDF.isIri` accepts any non-empty string containing `:`, so
`"_:x"` IS a well-formed IRI in this tree, and a graph containing the
IRI `_:x` alongside the blank node `x` would have its IRI CAPTURED by
the closure — `unified_adequate_simple` as stated (no freshness
hypothesis) would be false. The document itself flags the looseness
("`RDF.isIri` is looser than RFC 3986").

Decided here instead: bound names are COLON-FREE by construction —
`bnodeName b = "_" ++ escape b`, where `escape` injectively rewrites
`:` to `%c` and `%` to `%p`. Every well-formed IRI contains a colon
and every `urn:cl:def:` operator name contains a colon, so no bound
name ever collides with any free name of the translation, for every
graph (`bnodeName_ne_iri`, with no side condition). The freshness
lemma the document asked for becomes unconditional.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.Theory
import L4Factoidal.RDF.Semantics

namespace L4Factoidal.Unified

/-! ## The `urn:cl:def:` operator vocabulary

The unified layer owns this namespace. The constants below are its
operators; `OWL/RLSemantics.lean` adds `listMember` and
`typedAllMembers` and treats `"urn:cl:def:"` as a RESERVED PREFIX
(`reservedIriPre`) to tell its internal IRIs from user data.

DECISION, owner, 2026-08-26: **leave the namespace as it is.** Do not
re-open this.

The question raised and answered that day: nothing blesses `urn:cl:def:`.
Checked against the IKL GUIDE and Hayes's 2009 reduction paper — neither
uses URNs at all, and where the GUIDE reaches for identifiers it reuses
`rdf:` and `xsd:` http qnames. So an http-scheme namespace would sit
closer to the source documents' own practice.

It stays anyway, and the reasoning is worth keeping: these are operator
names internal to the embedding, not vocabulary published for anyone to
use. A rename would touch six constants, their theorem statements, and
the reserved-prefix check that `OWL/RLSemantics.lean` decides
IRI-is-internal by — real churn across proved files for no change in
meaning.

This is NOT the deleted content-addressed proposition naming
(https://github.com/danbri/factoidal/issues/626), which was Claude-
invented, never asked for, and had no requirement behind it. These
constants are load-bearing: `graphAsserted` compares against
`assertsIri` directly, and `asserted_merge_sound` in
`Unified/ClBridge.lean` is stated over it. -/

/-- The literal-value operator (LBase §3.0 `LiteralValueOf`). -/
def litOp : String := "urn:cl:def:literalValueOf"

/-- The RDF 1.2 triple-term operator. -/
def ttOp : String := "urn:cl:def:tripleTerm"

/-- The dataset naming relation (design document §2.4). -/
def namesOp : String := "urn:cl:def:names"

/-- The dataset ASSERTION decoration (design document §2.4, as
repaired for https://github.com/danbri/factoidal/issues/609 item 3):
the predicate whose occurrence in the DEFAULT graph makes the named
graph it points at asserted rather than merely mentioned. -/
def assertsOp : String := "urn:cl:def:asserts"

/-- `assertsOp` as an RDF predicate. -/
def assertsIri : RDF.WfIri := ⟨assertsOp, by decide⟩

/-! ## Colon-free injective bound-name encoding -/

/-- Escape one character into a colon-free fragment: `:` → `%c`,
`%` → `%p`, anything else stands for itself. -/
def escChar (c : Char) : List Char :=
  if c = ':' then ['%', 'c'] else if c = '%' then ['%', 'p'] else [c]

/-- Escape a character list; the image never contains `:`. -/
def escape : List Char → List Char
  | [] => []
  | c :: r => escChar c ++ escape r

/-- Decode an escaped list (left inverse of `escape`). -/
def unescape : List Char → List Char
  | [] => []
  | [c] => [c]
  | a :: b :: r =>
      if a = '%' then (if b = 'c' then ':' else '%') :: unescape r
      else a :: unescape (b :: r)

theorem escChar_ne_nil (c : Char) : escChar c ≠ [] := by
  unfold escChar
  by_cases hc : c = ':' <;> by_cases hp : c = '%' <;> simp [hc, hp]

theorem escape_eq_nil {cs : List Char} (h : escape cs = []) : cs = [] := by
  cases cs with
  | nil => rfl
  | cons c r =>
      exfalso
      simp only [escape, List.append_eq_nil_iff] at h
      exact escChar_ne_nil c h.1

/-- `unescape` undoes `escape` — the injectivity of the encoding in
computable form. -/
theorem unescape_escape : ∀ cs : List Char, unescape (escape cs) = cs
  | [] => rfl
  | c :: r => by
      by_cases hc : c = ':'
      · subst hc
        simp [escape, escChar, unescape, unescape_escape r]
      · by_cases hp : c = '%'
        · subst hp
          simp [escape, escChar, unescape, unescape_escape r]
        · simp only [escape, escChar, if_neg hc, if_neg hp,
                     List.singleton_append]
          cases hr : escape r with
          | nil =>
              rw [escape_eq_nil hr]
              rfl
          | cons b r' =>
              have hu : unescape (c :: b :: r') = c :: unescape (b :: r') := by
                simp [unescape, hp]
              rw [hu, ← hr, unescape_escape r]

theorem escape_injective {cs1 cs2 : List Char}
    (h : escape cs1 = escape cs2) : cs1 = cs2 := by
  have := congrArg unescape h
  rwa [unescape_escape, unescape_escape] at this

theorem escChar_no_colon (c : Char) : ':' ∉ escChar c := by
  unfold escChar
  by_cases hc : c = ':' <;> by_cases hp : c = '%' <;>
    simp [hc, hp] <;> first
      | exact fun h => hc h.symm
      | decide

theorem escape_no_colon : ∀ cs : List Char, ':' ∉ escape cs
  | [] => by simp [escape]
  | c :: r => by
      simp only [escape, List.mem_append]
      rintro (h | h)
      · exact escChar_no_colon c h
      · exact escape_no_colon r h

/-- The bound name a blank-node label translates to: `_` followed by
the colon-escaped label. Injective, and colon-free — hence fresh with
respect to every well-formed IRI string and every operator name. -/
def bnodeName (b : RDF.BNodeId) : String :=
  String.ofList ('_' :: escape b.toList)

theorem bnodeName_toList (b : RDF.BNodeId) :
    (bnodeName b).toList = '_' :: escape b.toList := by
  simp [bnodeName]

theorem bnodeName_no_colon (b : RDF.BNodeId) :
    ':' ∉ (bnodeName b).toList := by
  rw [bnodeName_toList]
  simp only [List.mem_cons]
  rintro (h | h)
  · exact absurd h (by decide)
  · exact escape_no_colon _ h

theorem bnodeName_injective {b1 b2 : RDF.BNodeId}
    (h : bnodeName b1 = bnodeName b2) : b1 = b2 := by
  have h2 := congrArg String.toList h
  rw [bnodeName_toList, bnodeName_toList] at h2
  injection h2 with _ h3
  exact String.toList_inj.mp (escape_injective h3)

/-- Decode a bound name back to the blank-node label it encodes. -/
def bnodeNameDecode (n : String) : Option RDF.BNodeId :=
  match n.toList with
  | '_' :: r => some (String.ofList (unescape r))
  | _ => none

theorem bnodeNameDecode_bnodeName (b : RDF.BNodeId) :
    bnodeNameDecode (bnodeName b) = some b := by
  unfold bnodeNameDecode
  rw [bnodeName_toList]
  simp [unescape_escape]

/-! ## Freshness against the free names of the translation -/

theorem isIri_has_colon {s : String} (h : RDF.isIri s = true) :
    ':' ∈ s.toList := by
  simp only [RDF.isIri, Bool.and_eq_true] at h
  exact List.contains_iff_mem.mp h.2

/-- A bound name differs from every string containing a colon. -/
theorem bnodeName_ne_of_colon {n : String} (hn : ':' ∈ n.toList)
    (b : RDF.BNodeId) : bnodeName b ≠ n :=
  fun he => bnodeName_no_colon b (he ▸ hn)

/-- **The freshness lemma** (design document §2.3), unconditional: a
bound blank-node name is distinct from every well-formed IRI string —
in particular from every IRI string occurring in any graph. -/
theorem bnodeName_ne_iri (b : RDF.BNodeId) (i : RDF.WfIri) :
    bnodeName b ≠ i.val :=
  bnodeName_ne_of_colon (isIri_has_colon i.property) b

theorem bnodeName_ne_litOp (b : RDF.BNodeId) : bnodeName b ≠ litOp :=
  bnodeName_ne_of_colon (by decide) b

theorem bnodeName_ne_ttOp (b : RDF.BNodeId) : bnodeName b ≠ ttOp :=
  bnodeName_ne_of_colon (by decide) b

theorem bnodeName_ne_namesOp (b : RDF.BNodeId) : bnodeName b ≠ namesOp :=
  bnodeName_ne_of_colon (by decide) b

/-! ## Term embedding -/

/-- The argument list of a literal's functional term: lexical form,
datatype IRI, then (when present) language tag and base direction. -/
def embedLiteralArgs (l : RDF.WfLiteral) : List CL.SeqItem :=
  [.term (.str l.val.lexicalForm), .term (.name l.val.datatype.val)]
    ++ (match l.val.langTag with
        | some tag => [CL.SeqItem.term (.str tag)]
        | none => [])
    ++ (match l.val.direction with
        | some .ltr => [CL.SeqItem.term (.str "ltr")]
        | some .rtl => [CL.SeqItem.term (.str "rtl")]
        | none => [])

/-- A subject as a CL term. -/
def embedSubject : RDF.Subject → CL.Term
  | .iri i => .name i.val
  | .bnode b => .name (bnodeName b)

/-- An RDF term as a CL term (design document §2.3). -/
def embedTerm : RDF.Term → CL.Term
  | .iri i => .name i.val
  | .bnode b => .name (bnodeName b)
  | .literal l => .funapp (.name litOp) (embedLiteralArgs l)
  | .tripleTerm s p o =>
      .funapp (.name ttOp)
        [.term (embedSubject s), .term (.name p.val), .term (embedTerm o)]

/-- One triple as one binary predication, the property term in
operator position (legal because CL is unsegregated). -/
def tripleAtom (t : RDF.Triple) : CL.Sentence :=
  .atom (.name t.p.val) [.term (embedSubject t.s), .term (embedTerm t.o)]

/-- The UNSCOPED body of a graph: the conjunction of its triples'
predications, blank-node names free. The recursion vehicle of the
design document §5.2's mitigation. -/
def rdfBody (g : RDF.Graph) : CL.Sentence :=
  .conj (g.map tripleAtom)

/-- The bound-name list of a graph: its blank-node labels (in
occurrence order, duplicates preserved — shadowing is harmless under
`Sentence.ex`), each under the colon-free spelling. -/
def graphBnodeNames (g : RDF.Graph) : List String :=
  (RDF.graphBnodeIds g).map bnodeName

/-- **The stage 1 translation**: a graph is ONE sentence — the
existential closure, over the graph's blank nodes, of the conjunction
of its triples' predications (RDF 1.1 Semantics §5.2; LBase §3.0). -/
def rdfToTheory (g : RDF.Graph) : CL.Sentence :=
  .ex ((graphBnodeNames g).map .plain) (rdfBody g)

/-- The Skolem reading (RDF 1.1 Semantics §6): blank nodes as free
names, no closure. Used by BGP adequacy in stage 6. -/
def rdfToTheorySk (g : RDF.Graph) : CL.Sentence :=
  rdfBody g

/-- Every bound name of a graph's closure is colon-free — the form of
freshness the transport lemmas consume. -/
theorem graphBnodeNames_no_colon (g : RDF.Graph) :
    ∀ n ∈ graphBnodeNames g, ':' ∉ n.toList := by
  intro n hn
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hn
  exact bnodeName_no_colon b

/-! ## Build-time checks -/

section Checks

#guard escape "a:b%c".toList == "a%cb%pc".toList
#guard unescape (escape "a:b%c".toList) == "a:b%c".toList
#guard bnodeName "x" == "_x"
#guard bnodeName "x:y" == "_x%cy"
#guard bnodeNameDecode (bnodeName "x:y") == some "x:y"
#guard bnodeNameDecode "no-underscore" == none
#guard decide (bnodeName "b" ≠ litOp)

end Checks

end L4Factoidal.Unified
