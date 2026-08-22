/-
L4Factoidal.RDF.Core — the RDF 1.1/1.2 term data model.

Port of `formal/fstar/RDF.Term.fsti` + `RDF.Triple.fsti` (F*) to
Lean 4. Faithful to the F* module's semantics; the F*-specific SMT
scaffolding (`assert_norm` witnesses, `Lemma` + Z3 discharge,
`decreases` annotations) is replaced by Lean-native mechanisms
(`rfl`/`decide` proofs, `theorem`s with explicit proofs, structural
recursion).

Design correspondences (F* → Lean 4):
  - `type wf_iri = s:iri{is_iri s}`        → `WfIri := {s : String // isIri s}`
  - `noeq type literal = {...}`            → `structure Literal`
  - `type wf_literal = l:literal{...}`     → `WfLiteral := {l : Literal // literalWf l}`
  - `noeq type subject` / `rdf_term`       → `inductive Subject` / `Term`
  - reflexivity `Lemma`s                   → `@[simp] theorem`s, proved
  - `assert_norm (is_iri "...")`           → `rfl` on the decidable check

Deliberately NOT ported (F*-side pragmatics, not data model):
  - the `join_canon_term` hash-join key canonicaliser (an optimisation
    seam for the OCaml extraction's hash join);
  - `RDF.Indexed`'s bucket trees (storage pragmatics).
The rdf:XMLLiteral exclusive-c14n machinery IS ported — it is part of
`literalEq`'s semantics, not scaffolding — in `RDF.XmlCanon`.
-/
import L4Factoidal.RDF.XmlCanon

namespace L4Factoidal.RDF

/-! ## Blank nodes — RDF 1.1 Concepts §3.4 -/

/-- A blank node label: a locally-scoped identifier. -/
abbrev BNodeId := String

/-! ## IRIs — RDF 1.1 Concepts §3.2 -/

/-- An IRI, represented as a plain string. -/
abbrev Iri := String

/-- The minimal syntactic well-formedness gate the F* tree applies to
every IRI before RFC 3987 logic sees it: non-empty and contains a
colon. (Port of `RDF.Term.is_iri`; the F* fuel-bounded character walk
`string_has_colon_from` becomes a list membership test.) -/
def isIri (s : String) : Bool :=
  !s.isEmpty && s.toList.contains ':'

/-- A well-formed IRI — the type every term constructor and predicate
position requires. F*: `s:iri{is_iri s}`. -/
abbrev WfIri := { s : Iri // isIri s }

instance : Hashable WfIri := ⟨fun s => hash s.val⟩
instance : Repr WfIri := ⟨fun s n => reprPrec s.val n⟩
instance : ToString WfIri := ⟨fun s => s.val⟩

/-- `rdf:langString` — the datatype of every (non-directional)
language-tagged literal. -/
def rdfLangString : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#langString", rfl⟩

/-- `rdf:dirLangString` — RDF 1.2's datatype for a directional
language-tagged string (RDF 1.2 Concepts §3.3). -/
def rdfDirLangString : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#dirLangString", rfl⟩

/-- `rdf:XMLLiteral` — value space is exclusive canonical XML
(RDF 1.1 §5.1); `literalEq` compares its lexical forms via
canonicalisation. -/
def rdfXMLLiteral : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral", rfl⟩

/-! ## Base direction — RDF 1.2 Concepts §3.3 -/

/-- Base text direction of a directional language-tagged string. -/
inductive TextDirection where
  | ltr
  | rtl
  deriving Hashable, Repr, DecidableEq

/-! ## Literals — RDF 1.1 Concepts §3.3 / RDF 1.2 Concepts §3.3 -/

/-- A literal: lexical form + datatype IRI + (for language-tagged
strings) a language tag + (RDF 1.2, for `rdf:dirLangString` only) a
base direction. All four fields are carried unconditionally;
`literalWf` is the well-formedness rule on the combination — the same
"optional field, not a new term kind" design as the F* source. -/
structure Literal where
  lexicalForm : String
  datatype    : WfIri
  langTag     : Option String
  direction   : Option TextDirection
  deriving DecidableEq

instance : Hashable Literal :=
  ⟨fun l => hash (l.lexicalForm, l.datatype.val, l.langTag,
                  l.direction.map (fun | .ltr => 0 | .rtl => 1))⟩

instance : Repr Literal :=
  ⟨fun l n => reprPrec (l.lexicalForm, l.datatype.val, l.langTag) n⟩

/-- The three-way well-formedness rule (RDF 1.2 extension of RDF 1.1's
"language tag iff `rdf:langString`"):
  * no tag, no direction  ↔ datatype is neither langString nor dirLangString
  * tag, no direction     ↔ datatype is `rdf:langString`
  * tag and direction     ↔ datatype is `rdf:dirLangString`
  * direction without tag — always ill-formed. -/
def literalWf (l : Literal) : Bool :=
  match l.langTag, l.direction with
  | none,   none   => l.datatype != rdfLangString && l.datatype != rdfDirLangString
  | some _, none   => l.datatype == rdfLangString
  | some _, some _ => l.datatype == rdfDirLangString
  | none,   some _ => false

/-- A well-formed literal — what `Term.literal` actually carries. -/
abbrev WfLiteral := { l : Literal // literalWf l }

instance : Hashable WfLiteral := ⟨fun l => hash l.val⟩
instance : Repr WfLiteral := ⟨fun l n => reprPrec l.val n⟩

/-! ## RDF terms — RDF 1.1 Concepts §3 / RDF 1.2 Concepts §3 -/

/-- A triple's subject: an IRI or a blank node, never a literal
(RDF 1.1 Concepts §3.1). Non-recursive; declared before `Term`
because RDF 1.2's triple-term constructor uses it. -/
inductive Subject where
  | iri   (i : WfIri)
  | bnode (b : BNodeId)
  deriving DecidableEq, Hashable, Repr

/-- An RDF term: IRI, blank node, literal, or — RDF 1.2 — a triple
term `<<( s p o )>>`. The triple term bakes in two RDF 1.2
constraints structurally: its subject is a `Subject` (never a
literal) and its predicate is an IRI. Only the object slot recurses,
so structural recursion over `Term` decreases on it — the same
termination skeleton as the F* `decreases t` annotations, supplied
here by Lean automatically. -/
inductive Term where
  | iri        (i : WfIri)
  | bnode      (b : BNodeId)
  | literal    (l : WfLiteral)
  | tripleTerm (s : Subject) (p : WfIri) (o : Term)
  deriving DecidableEq, Hashable, Repr

/-! ## XSD term-algebra constants -/

def xsdString  : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#string", rfl⟩
def xsdInteger : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#integer", rfl⟩
def xsdDecimal : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#decimal", rfl⟩
def xsdDouble  : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#double", rfl⟩
def xsdBoolean : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#boolean", rfl⟩

/-- Convenience constructor: a plain string literal (RDF 1.1 assigns
`xsd:string` to un-tagged, un-typed literals). -/
def Literal.string (lex : String) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := xsdString,
     langTag := none, direction := none }, rfl⟩

/-- Convenience constructor: a language-tagged literal. -/
def Literal.langString (lex tag : String) : WfLiteral :=
  ⟨{ lexicalForm := lex, datatype := rdfLangString,
     langTag := some tag, direction := none }, rfl⟩

/-! ## Equality — the three literal-equality relations

The F* source distinguishes (and warns against conflating):
  * `literal_term_eq` — STRICT term equality (RDF 1.1 Concepts §3.3:
    every field character-by-character). In this port that is exactly
    `Eq`/`DecidableEq` on `Literal` — see
    `literalTermEq_iff_eq` below, the Lean counterpart of the F*
    `lemma_literal_term_eq_identity`.
  * `literalEq` — the COARSER comparison the SPARQL engine matches
    with: language tags case-insensitively (RDF 1.1 §3.3 permits
    lowercasing the tag value space) and `rdf:XMLLiteral` lexical
    forms via exclusive-c14n (RDF 1.1 §5.1).
  * `literalValueEq` — RDF 1.1 value equality; with well-formed
    representations (plain literals already carry `xsd:string`) it
    coincides with field comparison modulo tag case. -/

/-- Case-insensitive language-tag comparison (`@en-US` ≡ `@en-us`). -/
def langTagEq (t1 t2 : String) : Bool :=
  t1.toLower == t2.toLower

def langTagOptionEq : Option String → Option String → Bool
  | none,    none    => true
  | some a,  some b  => langTagEq a b
  | _,       _       => false

/-- Structural equality on subjects (port of `subject_eq`). -/
def Subject.eqb : Subject → Subject → Bool
  | .iri i1,   .iri i2   => i1 == i2
  | .bnode b1, .bnode b2 => b1 == b2
  | _,         _         => false

/-- Engine literal equality: lexical form + datatype exact, language
tag case-insensitive; `rdf:XMLLiteral` lexical forms via exclusive
canonical XML (port of `literal_eq`, including the
WebOnt-miscellaneous-202 XMLLiteral fix). -/
def Literal.eqb (l1 l2 : Literal) : Bool :=
  (if l1.datatype == rdfXMLLiteral && l2.datatype == rdfXMLLiteral
   then XmlCanon.xmlCanonEq l1.lexicalForm l2.lexicalForm
   else l1.lexicalForm == l2.lexicalForm) &&
  l1.datatype == l2.datatype &&
  langTagOptionEq l1.langTag l2.langTag &&
  l1.direction == l2.direction

/-- STRICT literal term equality (port of `literal_term_eq`): every
field compares exactly. -/
def Literal.termEq (l1 l2 : Literal) : Bool :=
  l1.lexicalForm == l2.lexicalForm &&
  l1.datatype == l2.datatype &&
  l1.langTag == l2.langTag &&
  l1.direction == l2.direction

/-- Engine term equality (port of `rdf_term_eq`): recursive through
triple terms, literals via the coarse `Literal.eqb`. -/
def Term.eqb : Term → Term → Bool
  | .iri i1,     .iri i2     => i1 == i2
  | .bnode b1,   .bnode b2   => b1 == b2
  | .literal l1, .literal l2 => l1.val.eqb l2.val
  | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
      s1.eqb s2 && p1 == p2 && o1.eqb o2
  | _, _ => false

/-! ## Triples — RDF 1.1 Concepts §3.1 (port of `RDF.Triple`) -/

/-- A triple: subject, predicate (always an IRI), object. -/
structure Triple where
  s : Subject
  p : WfIri
  o : Term
  deriving DecidableEq, Hashable, Repr

/-- Structural (engine) equality on triples (port of `triple_eq`). -/
def Triple.eqb (a b : Triple) : Bool :=
  a.s.eqb b.s && a.p == b.p && a.o.eqb b.o

/-- Coerce a term into a subject; literals and triple terms have no
subject form (port of `term_to_subject_opt`). -/
def Term.toSubject? : Term → Option Subject
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

/-- View a subject as a term (port of `subject_to_term`). -/
def Subject.toTerm : Subject → Term
  | .iri i   => .iri i
  | .bnode b => .bnode b

/-! ## Reflexivity and identity theorems

The F* source proves these as SMT `Lemma`s; here they are ordinary
theorems with explicit proofs — no `sorry`, no `axiom`, no solver. -/

@[simp] theorem Subject.eqb_refl (s : Subject) : s.eqb s = true := by
  cases s <;> simp [Subject.eqb]

@[simp] theorem langTagEq_refl (t : String) : langTagEq t t = true := by
  simp [langTagEq]

@[simp] theorem langTagOptionEq_refl (t : Option String) :
    langTagOptionEq t t = true := by
  cases t <;> simp [langTagOptionEq]

@[simp] theorem Literal.eqb_refl (l : Literal) : l.eqb l = true := by
  unfold Literal.eqb
  by_cases h : (l.datatype == rdfXMLLiteral && l.datatype == rdfXMLLiteral) = true <;>
    simp [h, XmlCanon.xmlCanonEq]

@[simp] theorem Literal.termEq_refl (l : Literal) : l.termEq l = true := by
  simp [Literal.termEq]

/-- Port of `lemma_literal_term_eq_identity`: the strict test decides
literal term IDENTITY — `termEq` true implies propositional equality.
(With `termEq_refl` above this makes `termEq` exactly `Eq` on
literals.) -/
theorem Literal.termEq_iff_eq (l1 l2 : Literal) :
    l1.termEq l2 = true ↔ l1 = l2 := by
  constructor
  · intro h
    unfold Literal.termEq at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hlex, hdt⟩, htag⟩, hdir⟩ := h
    cases l1; cases l2
    simp_all
  · intro h; subst h; simp

@[simp] theorem Term.eqb_refl (t : Term) : t.eqb t = true := by
  induction t with
  | iri i => simp [Term.eqb]
  | bnode b => simp [Term.eqb]
  | literal l => simp [Term.eqb]
  | tripleTerm s p o ih => simp [Term.eqb, ih]

@[simp] theorem Triple.eqb_refl (t : Triple) : t.eqb t = true := by
  simp [Triple.eqb]

end L4Factoidal.RDF
