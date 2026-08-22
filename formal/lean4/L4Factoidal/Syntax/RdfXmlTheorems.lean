/-
L4Factoidal.Syntax.RdfXmlTheorems — what the RDF/XML port proves.

Three families, each cheap because the port's state discipline was
designed to make them so. Production numbers cite **RDF 1.1 XML
Syntax**, https://www.w3.org/TR/rdf-syntax-grammar/ .

  1. The `rdf:li` ↦ `rdf:_n` counter (§5.3) is strictly increasing, so
     an ordinal is never handed out twice inside one node element.
  2. `xml:lang` (XML §2.12) INHERITS: an element carrying no `xml:lang`
     leaves the language in scope exactly as it found it, and
     `xml:lang=""` clears it rather than setting an empty one.
  3. Base resolution (XML Base §3 / RFC 3986 §5) reduces DEFINITIONALLY
     to `Syntax.resolveIri` — this port adds no IRI arithmetic of its
     own beyond the fragment strip XML Base §3.3 requires.

Plus the blank-node label claim the port's labelling scheme is designed
to give: a generated label and an `rdf:nodeID`-derived label can never
collide, so the F* source's `rdfxml_b<N>`-vs-`nodeID` hazard cannot
arise here.

No `sorry`, no user `axiom`, no `native_decide`. The `#print axioms`
audit lines at the bottom show the base every theorem here rests on.
-/
import L4Factoidal.Syntax.RdfXml

namespace L4Factoidal.Syntax.RdfXml

/-! ## Recording an error changes only the error field

`St.fail` keeps the FIRST violation, so it is a no-op once one is set;
either way it leaves every other component of the state alone. These
projections are what lets the scoped-update lemmas below be one-liners. -/

@[simp] theorem fail_base (st : St) (m : String) : (st.fail m).base = st.base := by
  simp only [St.fail]; split <;> rfl

@[simp] theorem fail_scope (st : St) (m : String) : (st.fail m).scope = st.scope := by
  simp only [St.fail]; split <;> rfl

@[simp] theorem fail_lang (st : St) (m : String) : (st.fail m).lang = st.lang := by
  simp only [St.fail]; split <;> rfl

@[simp] theorem fail_liCounter (st : St) (m : String) :
    (st.fail m).liCounter = st.liCounter := by
  simp only [St.fail]; split <;> rfl

@[simp] theorem fail_bnodeCounter (st : St) (m : String) :
    (st.fail m).bnodeCounter = st.bnodeCounter := by
  simp only [St.fail]; split <;> rfl

@[simp] theorem fail_seenIds (st : St) (m : String) :
    (st.fail m).seenIds = st.seenIds := by
  simp only [St.fail]; split <;> rfl

/-- A recorded violation is never lost: `St.fail` always leaves an
error set. This is what makes `parseRdfXml` reject rather than return a
partial graph. -/
theorem fail_err_ne_none (st : St) (m : String) : (st.fail m).err ≠ none := by
  simp only [St.fail]
  split
  · next e he => simp [he]
  · simp

/-! ## §5.3 — the `rdf:li` ordinal counter

`St.nextLi` hands out the current `liCounter` and advances it. The two
one-step facts are definitional; the interesting statement is that
running it `n` times lands on `liCounter + n`, from which "an ordinal is
never reused" follows by injectivity of `(· + ·)` on the left. -/

/-- The ordinal `nextLi` hands out is the counter's current value. -/
@[simp] theorem nextLi_fst (st : St) : st.nextLi.1 = st.liCounter := rfl

/-- … and it advances the counter by exactly one. -/
@[simp] theorem nextLi_snd_liCounter (st : St) :
    st.nextLi.2.liCounter = st.liCounter + 1 := rfl

/-- The counter STRICTLY increases at every `rdf:li`. -/
theorem nextLi_lt (st : St) : st.liCounter < st.nextLi.2.liCounter := by
  simp

/-- Two successive `rdf:li` elements get DIFFERENT ordinals — the
one-step form of "never reuses". -/
theorem nextLi_succ_ne (st : St) : st.nextLi.1 ≠ st.nextLi.2.nextLi.1 := by
  simp

/-- The state after `n` consecutive `rdf:li` property elements. -/
def liAfter : Nat → St → St
  | 0,     st => st
  | n + 1, st => liAfter n st.nextLi.2

/-- `n` `rdf:li` elements advance the counter by exactly `n`. -/
theorem liAfter_liCounter (n : Nat) (st : St) :
    (liAfter n st).liCounter = st.liCounter + n := by
  induction n generalizing st with
  | zero => simp [liAfter]
  | succ k ih =>
    simp only [liAfter, ih, nextLi_snd_liCounter]
    omega

/-- The ordinal the `n`-th `rdf:li` of one node element receives. -/
theorem liAfter_ordinal (n : Nat) (st : St) :
    (liAfter n st).nextLi.1 = st.liCounter + n := by
  rw [nextLi_fst, liAfter_liCounter]

/-- **The counter never reuses an ordinal.** Two `rdf:li` elements at
different positions in one node element's property element list receive
different `rdf:_n` predicates. -/
theorem liAfter_ordinal_injective {m n : Nat} {st : St}
    (h : (liAfter m st).nextLi.1 = (liAfter n st).nextLi.1) : m = n := by
  rw [liAfter_ordinal, liAfter_ordinal] at h
  omega

/-- Strict monotonicity in the position: a later `rdf:li` always gets a
larger ordinal. -/
theorem liAfter_ordinal_strictMono {m n : Nat} {st : St} (h : m < n) :
    (liAfter m st).nextLi.1 < (liAfter n st).nextLi.1 := by
  rw [liAfter_ordinal, liAfter_ordinal]
  omega

/-- §5.3's scoping rule: entering a node element opens a FRESH numbering
scope, so the first `rdf:li` inside it is always `rdf:_1`. -/
@[simp] theorem resetLi_liCounter (st : St) : st.resetLi.liCounter = 1 := rfl

/-- … and closing a child's scope restores the parent's counter, so a
nested node element cannot disturb the enclosing numbering (the F*
source names rdf-containers-syntax-vs-schema test004 / test007 as the
regression this prevents). -/
@[simp] theorem restoreScope_liCounter (parent child : St) :
    (restoreScope parent child).liCounter = parent.liCounter := rfl

/-! ## Blank-node freshness

The counter that mints blank-node labels is DOCUMENT-scoped: unlike
`liCounter` it survives `restoreScope`, which is what stops two sibling
node elements from minting the same label. -/

/-- Minting a blank node advances the document counter by one. -/
@[simp] theorem freshBnode_bnodeCounter (st : St) :
    st.freshBnode.2.bnodeCounter = st.bnodeCounter + 1 := rfl

/-- The blank-node counter FLOWS OUT of a closing scope (contrast
`restoreScope_liCounter`). -/
@[simp] theorem restoreScope_bnodeCounter (parent child : St) :
    (restoreScope parent child).bnodeCounter = child.bnodeCounter := rfl

/-- `[7.2.23] idAttr` uniqueness tracking is document-scoped too. -/
@[simp] theorem restoreScope_seenIds (parent child : St) :
    (restoreScope parent child).seenIds = child.seenIds := rfl

/-- The base, the namespace scope and the language are XML-scoped: they
revert to the parent's on the way out. -/
@[simp] theorem restoreScope_base (parent child : St) :
    (restoreScope parent child).base = parent.base := rfl

@[simp] theorem restoreScope_scope (parent child : St) :
    (restoreScope parent child).scope = parent.scope := rfl

@[simp] theorem restoreScope_lang (parent child : St) :
    (restoreScope parent child).lang = parent.lang := rfl

/-! ## Blank-node label spaces are disjoint

The F* source mints `rdfxml_b<N>` and uses an `rdf:nodeID` value
verbatim, so a document containing `rdf:nodeID="rdfxml_b0"` can name a
node the parser also mints. This port puts the two in label spaces that
differ in their first character, so no document can produce the
collision. Blank-node labels are document-local and graph identity is up
to renaming (RDF 1.1 Concepts §3.4), so the choice costs nothing. -/

/-- **No generated label is ever an `rdf:nodeID`-derived label.** -/
theorem genLabel_ne_nodeIdLabel (n : Nat) (x : String) :
    genLabel n ≠ nodeIdLabel x := by
  intro h
  have hd : (genLabel n).toList = (nodeIdLabel x).toList := by rw [h]
  rw [genLabel, nodeIdLabel, String.toList_append, String.toList_append] at hd
  have hb : ("b" : String).toList = ['b'] := rfl
  have hn : ("n" : String).toList = ['n'] := rfl
  rw [hb, hn] at hd
  injection hd with hc _
  exact absurd hc (by decide)

/-! ## XML §2.12 — `xml:lang` inheritance

`updateLang` is the only place the language in scope changes. The three
clauses below are the whole rule. -/

/-- **An element with no `xml:lang` inherits the language in scope.** -/
@[simp] theorem updateLang_lang_of_none {st : St} {attrs : List XML.Attribute}
    (h : findXmlAttr st "lang" attrs = none) :
    (updateLang st attrs).lang = st.lang := by
  simp [updateLang, h]

/-- An element with a non-empty `xml:lang` sets the language. -/
theorem updateLang_lang_of_some {st : St} {attrs : List XML.Attribute} {l : String}
    (h : findXmlAttr st "lang" attrs = some l) (hne : l.isEmpty = false) :
    (updateLang st attrs).lang = some l := by
  simp [updateLang, h, hne]

/-- `xml:lang=""` CLEARS the inherited language; it does not set an empty
one. -/
theorem updateLang_lang_of_empty {st : St} {attrs : List XML.Attribute}
    (h : findXmlAttr st "lang" attrs = some "") :
    (updateLang st attrs).lang = none := by
  simp [updateLang, h]

/-- Neither of the other two scoped updates touches the language, so the
inheritance clause lifts to `updateState`: an element declaring no
`xml:lang` leaves it exactly as it found it. -/
@[simp] theorem updateScope_lang (st : St) (attrs : List XML.Attribute) :
    (updateScope st attrs).lang = st.lang := by
  simp only [updateScope]
  split <;> simp

@[simp] theorem updateBase_lang (st : St) (attrs : List XML.Attribute) :
    (updateBase st attrs).lang = st.lang := by
  simp only [updateBase]
  split <;> rfl

/-- **`xml:lang` inheritance, at the level the grammar walk uses it.** -/
theorem updateState_lang_inherited {st : St} {attrs : List XML.Attribute}
    (h : findXmlAttr (updateBase (updateScope st attrs) attrs) "lang" attrs = none) :
    (updateState st attrs).lang = st.lang := by
  simp only [updateState]
  rw [updateLang_lang_of_none h, updateBase_lang, updateScope_lang]

/-! ## XML Base §3 / RFC 3986 §5 — base resolution

The port adds no IRI arithmetic of its own: resolving a reference IS
`Syntax.resolveIri` against the base in scope. The one RDF/XML-specific
step is XML Base §3.3's requirement that a base carry no fragment. -/

/-- **Base resolution reduces to `resolveIri`** — definitionally. -/
theorem resolveRef_eq_resolveIri (st : St) (r : String) :
    resolveRef st r = resolveIri st.base r := rfl

/-- An element declaring no `xml:base` inherits the base in scope. -/
@[simp] theorem updateBase_base_of_none {st : St} {attrs : List XML.Attribute}
    (h : findXmlAttr st "base" attrs = none) :
    (updateBase st attrs).base = st.base := by
  simp [updateBase, h]

/-- An element declaring `xml:base` resolves it against the base in
scope and then strips the fragment (XML Base §3.3 / RFC 3986 §5.1). -/
theorem updateBase_base_of_some {st : St} {attrs : List XML.Attribute} {b : String}
    (h : findXmlAttr st "base" attrs = some b) :
    (updateBase st attrs).base = stripFragment (resolveIri st.base b) := by
  simp [updateBase, h]

/-- The namespace update never touches the base, so the two clauses
above are also the whole base rule for `updateState`. -/
@[simp] theorem updateScope_base (st : St) (attrs : List XML.Attribute) :
    (updateScope st attrs).base = st.base := by
  simp only [updateScope]
  split <;> simp

@[simp] theorem updateLang_base (st : St) (attrs : List XML.Attribute) :
    (updateLang st attrs).base = st.base := by
  simp only [updateLang]
  split
  · split <;> rfl
  · rfl

/-! ## `[7.2.23] idAttr` uniqueness

`registerId` either records a key or reports the repeat; either way the
key set only grows, which is what makes the check monotone over a
document. -/

/-- Registering an `rdf:ID` never forgets a key already seen. -/
theorem registerId_seenIds_mono (st : St) (v : String) (k : String)
    (h : k ∈ st.seenIds) : k ∈ (registerId st v).seenIds := by
  simp only [registerId]
  split
  · simpa using h
  · exact List.mem_cons_of_mem _ h

/-- A repeat is REPORTED: registering a key already present raises the
error flag. -/
theorem registerId_err_of_dup {st : St} {v : String}
    (h : st.seenIds.contains (st.base ++ "#" ++ v) = true) :
    (registerId st v).err ≠ none := by
  simp only [registerId]
  rw [if_pos h]
  exact fail_err_ne_none _ _

/-! ## Axiom audit

Every build log shows the base these theorems rest on. The acceptable
set is exactly Lean's own foundations — `propext`, `Classical.choice`,
`Quot.sound` — and anything less. No `sorry`, no user `axiom`, no
`Lean.ofReduceBool` (which is what `native_decide` would smuggle in). -/

#print axioms liAfter_ordinal_injective
#print axioms liAfter_ordinal_strictMono
#print axioms genLabel_ne_nodeIdLabel
#print axioms updateState_lang_inherited
#print axioms resolveRef_eq_resolveIri
#print axioms updateBase_base_of_some
#print axioms registerId_err_of_dup
#print axioms fail_err_ne_none

end L4Factoidal.Syntax.RdfXml
