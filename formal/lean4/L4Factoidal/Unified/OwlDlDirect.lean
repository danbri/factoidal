/-
L4Factoidal.Unified.OwlDlDirect — the OWL 2 Direct Semantics route:
the tableau fragment's `Concept` / `Assertion` / `RoleAxioms` straight
to Common Logic sentences, with the interpretation transport pair.

Stage 5 of https://github.com/danbri/factoidal/issues/598, design
document `docs/designissues/2026-08-25-unified-semantics-lean.md`
§4.5 and §5.3.

## Scope: the SHIQ fragment of `OWL/Tableau.lean`, and why

The tree has no structural-objects AST for OWL 2.
`OWL/FunctionalSyntax.lean` is a parser that emits RDF triples;
`OWL/ClassExpr.lean` reads class expressions off graphs. The one
datatype in the tree that IS a Direct-Semantics ontology fragment is
`OWL/Tableau.lean`'s `Concept` / `Assertion` / `RoleAxioms`, together
with its native model theory (`OWL.Interp`, `OWL.Interp.sem`,
`OWL.SatAll`, `OWL.RespectsRBox`, `OWL.Consistent`). Stage 5 is scoped
to exactly that fragment. The constructs `OWL/Tableau.lean`'s header
lists as not ported — nominals (`ObjectOneOf`), datatypes, functional
roles — are outside the fragment here too, and each gets a boundary
row in `docs/theorem-registry.md` §9 rather than a silent omission.

Direct Semantics does not factor through RDF graphs (design document
§5.3): `neg`, `disj` and the counting formulae below are not the
translation of any RDF graph. This module therefore does NOT reuse
`Unified/RdfEmbed.lean`'s `rdfToTheory`; it shares only the CL
interpretation type and the colon-free/colon-carrying name discipline.

## The vocabulary decision (task point 1), and its justification

`OWL.Role` and `OWL.Ind` are `abbrev … := String`, so a tableau
individual literally named `"x"` lives in the same string space as the
COLON-FREE bound names `Unified/RdfEmbed.lean` reserves for blank
nodes, and in the same space as this module's own bound variables. Two
repairs were available. This module takes the second:

1. **Tighten `Role`/`Ind` to `RDF.WfIri`** (the `OWL/Tableau.lean`
   header invites it). REJECTED, and not only for cost. The `exWitness`
   rule MINTS a fresh individual name and `leqMerge` RENAMES one, so
   every application of those two rules would acquire an IRI
   well-formedness obligation, and the freshness side condition
   `x ∉ indsOf A` would have to be restated over a subtype. It is also
   wrong on the merits: Direct Semantics reads an individual as a
   structural entity, not as an RDF IRI (§5.3), and `OWL/Tableau.lean`,
   `OWL/TableauTheorems.lean`, `OWL/TableauTests.lean` are landed work.
2. **A colon-carrying injective encoding at the boundary** — the
   `bnodeName`/`escape` pattern of `Unified/RdfEmbed.lean` run the
   other way. ADOPTED. `dlName tag s` prefixes the fixed
   colon-carrying tag `urn:owl:dl:<t>` to the colon-ESCAPED name, where
   `t` is `i` (individual), `c` (class) or `r` (role). Consequences,
   all unconditional and all needed by the gate theorem:
   * every translated name contains a colon, so it is distinct from
     every `bnodeName` of the RDF route and from every bound variable
     of this module (`bvar`, colon-free by construction);
   * the three tag characters make the individual, class and role name
     spaces pairwise disjoint;
   * `escape` is injective, so `dlDecode` recovers the tableau name —
     which is what lets `liftInterpDL` read a predicate's identity off
     its denotation.

   The price is that no theorem here needs a freshness hypothesis: the
   stage 5 gate is a full `↔` with no side conditions.

## Bound variables

`bvar k = "_" ++ ("v" repeated k)` — unary, so injectivity is a list
length argument rather than a `Nat.repr` argument, and colon-freeness
is immediate. Cardinality needs `n + 1` simultaneous bound variables,
so the concept translation threads a next-free index `k` and the
argument position carries the invariant `OkArg k x`: the argument is
either a colon-carrying name or a bound variable already in scope.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.RdfTransport
import L4Factoidal.OWL.TableauTheorems

namespace L4Factoidal.Unified

/-! ## The `urn:owl:dl:` name space -/

/-- The shared prefix of every Direct-Semantics name. Contains a
colon, so every name built from it is colon-carrying. -/
def dlPrefix : List Char :=
  ['u', 'r', 'n', ':', 'o', 'w', 'l', ':', 'd', 'l', ':']

/-- A tableau name under a one-character tag: the prefix, the tag, and
the colon-escaped name (`escape` from `Unified/RdfEmbed.lean`). -/
def dlName (tag : Char) (s : String) : String :=
  String.ofList (dlPrefix ++ tag :: escape s.toList)

/-- Recover the tableau name from a translated name, when the tag
matches. The prefix is matched as an explicit character pattern so the
equations reduce definitionally. -/
def dlDecode (tag : Char) (n : String) : Option String :=
  match n.toList with
  | 'u' :: 'r' :: 'n' :: ':' :: 'o' :: 'w' :: 'l' :: ':' :: 'd' :: 'l' :: ':'
      :: t :: rest =>
      if t = tag then some (String.ofList (unescape rest)) else none
  | _ => none

/-- Individual names (ABox constants). -/
def indName (a : OWL.Ind) : String := dlName 'i' a

/-- Class names (the `atom` constructor of `OWL.Concept`). -/
def className (a : String) : String := dlName 'c' a

/-- Role names (object properties). -/
def roleName (r : OWL.Role) : String := dlName 'r' r

theorem dlName_toList (tag : Char) (s : String) :
    (dlName tag s).toList = dlPrefix ++ tag :: escape s.toList := by
  simp [dlName]

/-- Every translated name carries a colon — the property that keeps it
away from the colon-free bound-name space. -/
theorem dlName_has_colon (tag : Char) (s : String) :
    ':' ∈ (dlName tag s).toList := by
  rw [dlName_toList]
  exact List.mem_append_left _ (by simp [dlPrefix])

theorem indName_has_colon (a : OWL.Ind) : ':' ∈ (indName a).toList :=
  dlName_has_colon _ _

theorem className_has_colon (a : String) : ':' ∈ (className a).toList :=
  dlName_has_colon _ _

theorem roleName_has_colon (r : OWL.Role) : ':' ∈ (roleName r).toList :=
  dlName_has_colon _ _

/-- The decode is a left inverse at the matching tag. -/
theorem dlDecode_dlName (tag : Char) (s : String) :
    dlDecode tag (dlName tag s) = some s := by
  rw [dlDecode, dlName_toList]
  simp only [dlPrefix, List.cons_append, List.nil_append]
  simp [unescape_escape]

/-- The decode rejects a name built under a different tag — the three
name spaces are pairwise disjoint. -/
theorem dlDecode_dlName_ne {tag tag' : Char} (h : tag ≠ tag') (s : String) :
    dlDecode tag' (dlName tag s) = none := by
  rw [dlDecode, dlName_toList]
  simp only [dlPrefix, List.cons_append, List.nil_append]
  simp [h]

theorem dlName_injective {tag : Char} {s1 s2 : String}
    (h : dlName tag s1 = dlName tag s2) : s1 = s2 := by
  have := congrArg (dlDecode tag) h
  rw [dlDecode_dlName, dlDecode_dlName] at this
  exact Option.some.inj this

/-! ## Bound variables -/

/-- The `k`-th bound variable: `_`, then `k` copies of `v`. Unary so
that injectivity is a length argument. Colon-free by construction. -/
def bvar (k : Nat) : String := String.ofList ('_' :: List.replicate k 'v')

theorem bvar_toList (k : Nat) : (bvar k).toList = '_' :: List.replicate k 'v' := by
  simp [bvar]

theorem bvar_no_colon (k : Nat) : ':' ∉ (bvar k).toList := by
  rw [bvar_toList]
  simp only [List.mem_cons]
  rintro (h | h)
  · exact absurd h (by decide)
  · exact absurd (List.eq_of_mem_replicate h) (by decide)

theorem bvar_injective {k m : Nat} (h : bvar k = bvar m) : k = m := by
  have h1 := congrArg String.toList h
  rw [bvar_toList, bvar_toList] at h1
  have h2 := congrArg List.length (List.tail_eq_of_cons_eq h1)
  simpa using h2

/-- A bound variable is never a translated name. -/
theorem bvar_ne_dlName (k : Nat) (tag : Char) (s : String) :
    bvar k ≠ dlName tag s := by
  intro he
  exact bvar_no_colon k (he ▸ dlName_has_colon tag s)

/-- The `n` bound variables `bvar k, …, bvar (k + n - 1)`. -/
def bvars (k n : Nat) : List String :=
  (List.range n).map (fun j => bvar (k + j))

theorem bvars_length (k n : Nat) : (bvars k n).length = n := by
  simp [bvars]

theorem mem_bvars {k n : Nat} {x : String} (h : x ∈ bvars k n) :
    ∃ j, j < n ∧ x = bvar (k + j) := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  exact ⟨j, List.mem_range.mp hj, rfl⟩

theorem bvars_no_colon {k n : Nat} : ∀ x ∈ bvars k n, ':' ∉ x.toList := by
  intro x hx
  obtain ⟨j, -, rfl⟩ := mem_bvars hx
  exact bvar_no_colon _

theorem bvars_nodup (k n : Nat) : (bvars k n).Nodup := by
  unfold bvars List.Nodup
  rw [List.pairwise_map]
  refine List.nodup_range.imp ?_
  intro a b hab he
  have := bvar_injective he
  omega

/-- The argument-position invariant: the free name a concept formula
is applied to is either a translated (colon-carrying) name or a bound
variable ALREADY in scope. Everything the translation introduces at
index `k` is therefore distinct from it. -/
def OkArg (k : Nat) (x : String) : Prop :=
  ':' ∈ x.toList ∨ ∃ j, j < k ∧ x = bvar j

theorem okArg_dlName (k : Nat) (tag : Char) (s : String) :
    OkArg k (dlName tag s) := Or.inl (dlName_has_colon tag s)

theorem okArg_bvar {j k : Nat} (h : j < k) : OkArg k (bvar j) :=
  Or.inr ⟨j, h, rfl⟩

/-- The invariant's payload: an in-scope argument differs from every
bound variable the translation is about to introduce. -/
theorem okArg_ne {k j : Nat} {x : String} (hx : OkArg k x) (hj : k ≤ j) :
    x ≠ bvar j := by
  rcases hx with hcol | ⟨m, hm, rfl⟩
  · intro he
    exact bvar_no_colon j (he ▸ hcol)
  · intro he
    have := bvar_injective he
    omega

theorem okArg_not_mem_bvars {k n : Nat} {x : String} (hx : OkArg k x) :
    x ∉ bvars k n := by
  intro hmem
  obtain ⟨j, -, rfl⟩ := mem_bvars hmem
  exact okArg_ne hx (Nat.le_add_right k j) rfl

/-- An argument in scope at `k` is still in scope at any larger
index. -/
theorem okArg_mono {k k' : Nat} {x : String} (h : OkArg k x) (hk : k ≤ k') :
    OkArg k' x := by
  rcases h with hcol | ⟨j, hj, rfl⟩
  · exact Or.inl hcol
  · exact Or.inr ⟨j, Nat.lt_of_lt_of_le hj hk, rfl⟩

theorem okArg_mem_bvars {k n : Nat} {x : String} (h : x ∈ bvars k n) :
    OkArg (k + n) x := by
  obtain ⟨j, hj, rfl⟩ := mem_bvars h
  exact okArg_bvar (by omega)

/-! ## The translation

OWL 2 Direct Semantics Table 5
(https://www.w3.org/TR/owl2-direct-semantics/), restricted to the
fragment. Cardinality becomes a first-order counting formula:
`n` bound variables, pairwise inequated with `CL.Sentence.eq` under a
negation, each an `r`-successor of the argument (and, in the qualified
form, each in the filler concept). -/

/-- A role edge as a binary predication, the role name in operator
position (legal because CL is unsegregated). -/
def roleAtom (r : OWL.Role) (x y : String) : CL.Sentence :=
  .atom (.name (roleName r)) [.term (.name x), .term (.name y)]

/-- A class membership as a unary predication. -/
def classAtom (a : String) (x : String) : CL.Sentence :=
  .atom (.name (className a)) [.term (.name x)]

/-- Pairwise distinctness of a name list — the sentence family indexed
by `n` that cardinality needs. This is where equality enters the
unified theory for the first time (stages 1–4 never used
`CL.Sentence.eq`). -/
def distinctBlock : List String → List CL.Sentence
  | [] => []
  | v :: vs =>
      vs.map (fun w => CL.Sentence.neg (.eq (.name v) (.name w)))
        ++ distinctBlock vs

/-- The class-expression translation (design document §4.5's
`conceptFormula`). `x` is the free argument name; `k` is the next
unused bound-variable index. -/
def conceptFormula : OWL.Concept → String → Nat → CL.Sentence
  | .atom a, x, _ => classAtom a x
  | .top, _, _ => .conj []
  | .bot, _, _ => .disj []
  | .neg c, x, k => .neg (conceptFormula c x k)
  | .conj c d, x, k => .conj [conceptFormula c x k, conceptFormula d x k]
  | .disj c d, x, k => .disj [conceptFormula c x k, conceptFormula d x k]
  | .all r c, x, k =>
      .all [.plain (bvar k)]
        (.impl (roleAtom r x (bvar k)) (conceptFormula c (bvar k) (k + 1)))
  | .ex r c, x, k =>
      .ex [.plain (bvar k)]
        (.conj [roleAtom r x (bvar k), conceptFormula c (bvar k) (k + 1)])
  | .atLeast n r, x, k =>
      .ex ((bvars k n).map .plain)
        (.conj (distinctBlock (bvars k n)
                  ++ (bvars k n).map (fun v => roleAtom r x v)))
  | .atMost n r, x, k =>
      .neg (.ex ((bvars k (n + 1)).map .plain)
        (.conj (distinctBlock (bvars k (n + 1))
                  ++ (bvars k (n + 1)).map (fun v => roleAtom r x v))))
  | .atLeastQ n r c, x, k =>
      .ex ((bvars k n).map .plain)
        (.conj (distinctBlock (bvars k n)
                  ++ (bvars k n).map (fun v => roleAtom r x v)
                  ++ (bvars k n).map (fun v => conceptFormula c v (k + n))))
  | .atMostQ n r c, x, k =>
      .neg (.ex ((bvars k (n + 1)).map .plain)
        (.conj (distinctBlock (bvars k (n + 1))
                  ++ (bvars k (n + 1)).map (fun v => roleAtom r x v)
                  ++ (bvars k (n + 1)).map
                      (fun v => conceptFormula c v (k + (n + 1))))))
  termination_by c _ _ => sizeOf c

/-- One ABox assertion as one sentence. `diff` is
`owl:differentFrom` — a negated equation, the second entry point for
equality. -/
def assertionSentence : OWL.Assertion → CL.Sentence
  | .inst a c => conceptFormula c (indName a) 0
  | .rel r a b => roleAtom r (indName a) (indName b)
  | .diff a b => .neg (.eq (.name (indName a)) (.name (indName b)))

/-- Subrole inclusion `p ⊑ q` as a universally closed implication. -/
def subRoleSentence (p q : OWL.Role) : CL.Sentence :=
  .all [.plain (bvar 0), .plain (bvar 1)]
    (.impl (roleAtom p (bvar 0) (bvar 1)) (roleAtom q (bvar 0) (bvar 1)))

/-- Role transitivity as a universally closed implication. -/
def transSentence (r : OWL.Role) : CL.Sentence :=
  .all [.plain (bvar 0), .plain (bvar 1), .plain (bvar 2)]
    (.impl (roleAtom r (bvar 0) (bvar 1))
      (.impl (roleAtom r (bvar 1) (bvar 2)) (roleAtom r (bvar 0) (bvar 2))))

/-- The role box as sentences. -/
def roleAxiomSentences (R : OWL.RoleAxioms) : List CL.Sentence :=
  R.subRole.map (fun p => subRoleSentence p.1 p.2) ++ R.trans.map transSentence

/-- **The stage 5 translation**: the role box and the ABox as one
sentence list.

DEVIATION from the design document, which writes the gate over
`owlDlDirect R A ++ roleAxiomSentences R`. Since `owlDlDirect` already
receives `R`, appending the role-axiom sentences a second time would
duplicate them; they are included here once and the gate is stated
over `owlDlDirect R A` alone. Recorded as a stage 5 correction
note. -/
def owlDlDirect (R : OWL.RoleAxioms) (A : List OWL.Assertion) :
    List CL.Sentence :=
  roleAxiomSentences R ++ A.map assertionSentence

/-! ## List and satisfaction plumbing -/

theorem satAll_append {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (l1 l2 : List CL.Sentence) :
    CL.SatAll i ν σ (l1 ++ l2) ↔ CL.SatAll i ν σ l1 ∧ CL.SatAll i ν σ l2 := by
  rw [satAll_forall, satAll_forall, satAll_forall]
  constructor
  · intro h
    exact ⟨fun s hs => h s (List.mem_append_left _ hs),
           fun s hs => h s (List.mem_append_right _ hs)⟩
  · rintro ⟨h1, h2⟩ s hs
    rcases List.mem_append.mp hs with h | h
    · exact h1 s h
    · exact h2 s h

theorem forall_mem_map' {α β : Type} (f : α → β) (l : List α) (P : β → Prop) :
    (∀ y ∈ l.map f, P y) ↔ ∀ x ∈ l, P (f x) := by
  constructor
  · intro h x hx
    exact h _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · rintro h y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx

theorem satAll_map_iff {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (vs : List String) (g : String → CL.Sentence) :
    CL.SatAll i ν σ (vs.map g) ↔ ∀ v ∈ vs, CL.Sat i ν σ (g v) := by
  rw [satAll_forall]
  exact forall_mem_map' g vs _

/-! The `CL.Sat` clauses are compiled from a `mutual` block, so they
are not definitional equations. These are the shape lemmas the
translation's proofs rewrite with, one per constructor used. -/

theorem sat_neg' {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (a : CL.Sentence) :
    CL.Sat i ν σ (.neg a) ↔ ¬ CL.Sat i ν σ a := by simp [CL.Sat]

theorem sat_impl' {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (a b : CL.Sentence) :
    CL.Sat i ν σ (.impl a b) ↔ (CL.Sat i ν σ a → CL.Sat i ν σ b) := by
  simp [CL.Sat]

theorem sat_conj' {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (l : List CL.Sentence) :
    CL.Sat i ν σ (.conj l) ↔ CL.SatAll i ν σ l := by simp [CL.Sat]

theorem sat_disj' {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (l : List CL.Sentence) :
    CL.Sat i ν σ (.disj l) ↔ CL.SatAny i ν σ l := by simp [CL.Sat]

theorem sat_exList' {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (bs : List CL.Binding) (body : CL.Sentence) :
    CL.Sat i ν σ (.ex bs body) ↔ CL.SatExists i ν σ bs body := by simp [CL.Sat]

theorem sat_allOne {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (n : String) (body : CL.Sentence) :
    CL.Sat i ν σ (.all [.plain n] body) ↔
      ∀ y : i.dom, CL.Sat i (CL.updateInd ν n y) σ body := by
  simp [CL.Sat, CL.SatForall]

theorem sat_exOne {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (n : String) (body : CL.Sentence) :
    CL.Sat i ν σ (.ex [.plain n] body) ↔
      ∃ y : i.dom, CL.Sat i (CL.updateInd ν n y) σ body := by
  simp [CL.Sat, CL.SatExists]

theorem sat_eq' {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (a b : String) :
    CL.Sat i ν σ (.eq (.name a) (.name b)) ↔ ν a = ν b := by
  simp [CL.Sat, CL.denotTerm]

/-- `freshVal_overrideOn` over an arbitrary fresh base valuation (the
library version fixes the base at `i.iName`). -/
theorem freshVal_overrideOn' {i : CL.Interp} {ν : String → i.dom}
    (hν : FreshVal i ν) {names : List String}
    (hnames : ∀ n ∈ names, ':' ∉ n.toList) (f : String → i.dom) :
    FreshVal i (overrideOn ν names f) := by
  intro n hn
  have hnm : n ∉ names := fun hmem => hnames n hmem hn
  rw [overrideOn, if_neg hnm]
  exact hν n hn

theorem map_overrideOn_self {α : Type} (ν : String → α) (vs : List String)
    (f : String → α) : vs.map (overrideOn ν vs f) = vs.map f := by
  apply List.map_congr_left
  intro v hv
  simp [overrideOn, hv]

/-- Every list of the right length is the image of the (duplicate-free)
name list under SOME valuation — the surjectivity that turns an
existential over valuations into an existential over witness lists. -/
theorem exists_fun_map {α : Type} (dflt : α) :
    ∀ {vs : List String}, vs.Nodup → ∀ {l : List α}, l.length = vs.length →
      ∃ f : String → α, vs.map f = l
  | [], _, l, hl => ⟨fun _ => dflt, by
      cases l with
      | nil => rfl
      | cons _ _ => simp at hl⟩
  | v :: vs, hnd, l, hl => by
      cases l with
      | nil => simp at hl
      | cons y l' =>
          have hnd' : vs.Nodup := (List.nodup_cons.mp hnd).2
          have hv : v ∉ vs := (List.nodup_cons.mp hnd).1
          obtain ⟨g, hg⟩ := exists_fun_map dflt hnd' (l := l') (by simpa using hl)
          refine ⟨fun n => if n = v then y else g n, ?_⟩
          have h1 : (if v = v then y else g v) = y := by simp
          rw [List.map_cons, h1, ← hg]
          congr 1
          apply List.map_congr_left
          intro w hw
          have hwv : w ≠ v := fun he => hv (he ▸ hw)
          simp [hwv]

/-- Existential over valuations ↔ existential over witness lists. -/
theorem exists_override_map {i : CL.Interp} (ν : String → i.dom)
    {vs : List String} (hnd : vs.Nodup) (P : List i.dom → Prop) :
    (∃ f : String → i.dom, P (vs.map (overrideOn ν vs f))) ↔
      ∃ l : List i.dom, l.length = vs.length ∧ P l := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨vs.map (overrideOn ν vs f), by simp, hf⟩
  · rintro ⟨l, hl, hP⟩
    obtain ⟨g, hg⟩ := exists_fun_map i.domWit hnd hl
    exact ⟨g, by rw [map_overrideOn_self, hg]; exact hP⟩

/-- The distinctness block is satisfied exactly when the named values
are pairwise distinct. -/
theorem sat_distinctBlock {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) :
    ∀ vs : List String,
      CL.SatAll i ν σ (distinctBlock vs) ↔ (vs.map ν).Pairwise (· ≠ ·)
  | [] => by simp [distinctBlock, CL.SatAll]
  | v :: vs => by
      rw [distinctBlock, satAll_append, satAll_map_iff,
          sat_distinctBlock ν σ vs]
      simp only [List.map_cons, List.pairwise_cons, forall_mem_map']
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun w hw => by simpa [CL.Sat, CL.denotTerm] using h1 w hw, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun w hw => by simpa [CL.Sat, CL.denotTerm] using h1 w hw, h2⟩

/-! ## The transport pair

A CL interpretation and an OWL Direct-Semantics interpretation over
the SAME domain are compatible when the class and role extensions read
off the CL relation extensions of the translated names. This is the
`Unified/RdfTransport.lean` pattern with one difference: because
`OWL.Interp` carries no structure beyond two extension families, the
transfer argument can be stated ONCE against a compatibility predicate
and instantiated in both directions, instead of being run twice. -/

/-- Compatibility of a CL interpretation with an OWL interpretation
over its own domain. -/
structure DLCompat (i : CL.Interp) (I : OWL.Interp i.dom) : Prop where
  cls : ∀ a x, I.concept a x ↔ i.rel (i.iName (className a)) [x]
  rol : ∀ r x y, I.role r x y ↔ i.rel (i.iName (roleName r)) [x, y]

/-- **`restrictInterpDL`** — the OWL interpretation a CL interpretation
induces (design document §4.1's pattern for the DL route). The domain
is preserved: unlike the RDF route there is no literal operator whose
arguments must be recovered from their denotations. -/
def restrictInterpDL (i : CL.Interp) : OWL.Interp i.dom where
  concept := fun a x => i.rel (i.iName (className a)) [x]
  role := fun r x y => i.rel (i.iName (roleName r)) [x, y]

theorem dlCompat_restrict (i : CL.Interp) : DLCompat i (restrictInterpDL i) :=
  ⟨fun _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

/-- The name assignment a CL interpretation induces on ABox
constants. -/
def dlNu (i : CL.Interp) : OWL.Ind → i.dom := fun a => i.iName (indName a)

/-! ## Transfer -/

theorem sat_roleAtom {i : CL.Interp} {I : OWL.Interp i.dom} (hc : DLCompat i I)
    {ν : String → i.dom} {σ : String → List i.dom} (hν : FreshVal i ν)
    (r : OWL.Role) (x y : String) :
    CL.Sat i ν σ (roleAtom r x y) ↔ I.role r (ν x) (ν y) := by
  simp only [roleAtom, CL.Sat, CL.denotTerm, CL.denotSeq]
  rw [hν (roleName r) (roleName_has_colon r)]
  exact (hc.rol r (ν x) (ν y)).symm

theorem sat_classAtom {i : CL.Interp} {I : OWL.Interp i.dom} (hc : DLCompat i I)
    {ν : String → i.dom} {σ : String → List i.dom} (hν : FreshVal i ν)
    (a : String) (x : String) :
    CL.Sat i ν σ (classAtom a x) ↔ I.concept a (ν x) := by
  simp only [classAtom, CL.Sat, CL.denotTerm, CL.denotSeq]
  rw [hν (className a) (className_has_colon a)]
  exact (hc.cls a (ν x)).symm

/-- The counting block, characterised. `extra` carries the qualified
form's filler conjuncts; `Q` is what they say about each witness. -/
theorem sat_exBlock_card {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) {σ : String → List i.dom} {ν : String → i.dom}
    (hν : FreshVal i ν) (r : OWL.Role) (x : String) (k n : Nat)
    (hx : OkArg k x) (extra : List CL.Sentence) (Q : i.dom → Prop)
    (hextra : ∀ f : String → i.dom,
        CL.SatAll i (overrideOn ν (bvars k n) f) σ extra ↔
          ∀ y ∈ (bvars k n).map f, Q y) :
    CL.Sat i ν σ
      (.ex ((bvars k n).map .plain)
        (.conj (distinctBlock (bvars k n)
                  ++ (bvars k n).map (fun v => roleAtom r x v) ++ extra)))
      ↔ ∃ l : List i.dom, l.length = n ∧ l.Pairwise (· ≠ ·) ∧
          ∀ y ∈ l, I.role r (ν x) y ∧ Q y := by
  rw [sat_exList', satExists_plains]
  have hbody : ∀ f : String → i.dom,
      CL.Sat i (overrideOn ν (bvars k n) f) σ
          (.conj (distinctBlock (bvars k n)
                    ++ (bvars k n).map (fun v => roleAtom r x v) ++ extra))
        ↔ ((bvars k n).map (overrideOn ν (bvars k n) f)).Pairwise (· ≠ ·) ∧
            ∀ y ∈ (bvars k n).map (overrideOn ν (bvars k n) f),
              I.role r (ν x) y ∧ Q y := by
    intro f
    have hμ : FreshVal i (overrideOn ν (bvars k n) f) :=
      freshVal_overrideOn' hν (fun m hm => bvars_no_colon m hm) f
    have hxv : overrideOn ν (bvars k n) f x = ν x := by
      rw [overrideOn, if_neg (okArg_not_mem_bvars hx)]
    have hmapf : (bvars k n).map (overrideOn ν (bvars k n) f)
        = (bvars k n).map f := map_overrideOn_self _ _ _
    rw [sat_conj', satAll_append, satAll_append, sat_distinctBlock,
        satAll_map_iff, hextra f, hmapf]
    constructor
    · rintro ⟨⟨hd, hr⟩, hq⟩
      refine ⟨hd, ?_⟩
      intro y hy
      refine ⟨?_, hq y hy⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      have := (sat_roleAtom hc hμ r x v).mp (hr v hv)
      rw [hxv] at this
      have hvf : overrideOn ν (bvars k n) f v = f v := by
        rw [overrideOn, if_pos hv]
      rwa [hvf] at this
    · rintro ⟨hd, hy⟩
      refine ⟨⟨hd, ?_⟩, fun y hyy => (hy y hyy).2⟩
      intro v hv
      have hvf : overrideOn ν (bvars k n) f v = f v := by
        rw [overrideOn, if_pos hv]
      refine (sat_roleAtom hc hμ r x v).mpr ?_
      rw [hxv, hvf]
      exact (hy (f v) (List.mem_map.mpr ⟨v, hv, rfl⟩)).1
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨hd, hy⟩ := (hbody f).mp hf
    exact ⟨(bvars k n).map (overrideOn ν (bvars k n) f),
           by rw [List.length_map, bvars_length], hd, hy⟩
  · rintro ⟨l, hl, hd, hy⟩
    have hnd := bvars_nodup k n
    have := (exists_override_map ν hnd
      (fun m => m.Pairwise (· ≠ ·) ∧ ∀ y ∈ m, I.role r (ν x) y ∧ Q y)).mpr
      ⟨l, by rw [bvars_length]; exact hl, hd, hy⟩
    obtain ⟨f, hf⟩ := this
    exact ⟨f, (hbody f).mpr hf⟩

/-- The unqualified counting block (no filler conjuncts). -/
theorem sat_exBlock_card0 {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) {σ : String → List i.dom} {ν : String → i.dom}
    (hν : FreshVal i ν) (r : OWL.Role) (x : String) (k n : Nat)
    (hx : OkArg k x) :
    CL.Sat i ν σ
      (.ex ((bvars k n).map .plain)
        (.conj (distinctBlock (bvars k n)
                  ++ (bvars k n).map (fun v => roleAtom r x v))))
      ↔ ∃ l : List i.dom, l.length = n ∧ l.Pairwise (· ≠ ·) ∧
          ∀ y ∈ l, I.role r (ν x) y := by
  have h := sat_exBlock_card (σ := σ) hc hν r x k n hx [] (fun _ => True)
    (by intro f; simp [CL.SatAll])
  rw [List.append_nil] at h
  simpa using h

/-- The qualified form's filler conjuncts, characterised — the
`hextra` argument `sat_exBlock_card` expects, built from the concept
translation's induction hypothesis. -/
theorem qualBlock_iff {i : CL.Interp} {I : OWL.Interp i.dom}
    (_hc : DLCompat i I) (σ : String → List i.dom) {c : OWL.Concept}
    (ih : ∀ (k : Nat) (x : String) (ν : String → i.dom),
        FreshVal i ν → OkArg k x →
        (CL.Sat i ν σ (conceptFormula c x k) ↔ I.sem c (ν x)))
    {ν : String → i.dom} (hν : FreshVal i ν) (k n : Nat) :
    ∀ f : String → i.dom,
      CL.SatAll i (overrideOn ν (bvars k n) f) σ
          ((bvars k n).map (fun v => conceptFormula c v (k + n)))
        ↔ ∀ y ∈ (bvars k n).map f, I.sem c y := by
  intro f
  rw [satAll_map_iff, forall_mem_map']
  have hμ : FreshVal i (overrideOn ν (bvars k n) f) :=
    freshVal_overrideOn' hν (fun m hm => bvars_no_colon m hm) f
  constructor
  · intro h v hv
    have h2 := (ih (k + n) v _ hμ (okArg_mem_bvars hv)).mp (h v hv)
    rwa [overrideOn, if_pos hv] at h2
  · intro h v hv
    refine (ih (k + n) v _ hμ (okArg_mem_bvars hv)).mpr ?_
    rw [overrideOn, if_pos hv]
    exact h v hv

/-- **The transfer lemma**: a compatible pair reads the same class
expression the same way, at every fresh valuation and every in-scope
argument. Induction on the concept; the counting cases go through
`sat_exBlock_card`. -/
theorem sat_conceptFormula {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) (σ : String → List i.dom) :
    ∀ (c : OWL.Concept) (k : Nat) (x : String) (ν : String → i.dom),
      FreshVal i ν → OkArg k x →
      (CL.Sat i ν σ (conceptFormula c x k) ↔ I.sem c (ν x)) := by
  intro c
  induction c with
  | atom a =>
      intro k x ν hν _
      rw [conceptFormula, sat_classAtom hc hν a x]
      simp only [OWL.Interp.sem]
  | top =>
      intro k x ν _ _
      rw [conceptFormula, sat_conj']
      simp only [CL.SatAll, OWL.Interp.sem]
  | bot =>
      intro k x ν _ _
      rw [conceptFormula, sat_disj']
      simp only [CL.SatAny, OWL.Interp.sem]
  | neg c ih =>
      intro k x ν hν hx
      rw [conceptFormula, sat_neg', ih k x ν hν hx]
      simp only [OWL.Interp.sem]
  | conj c d ihc ihd =>
      intro k x ν hν hx
      rw [conceptFormula, sat_conj']
      simp only [CL.SatAll, and_true]
      rw [ihc k x ν hν hx, ihd k x ν hν hx]
      simp only [OWL.Interp.sem]
  | disj c d ihc ihd =>
      intro k x ν hν hx
      rw [conceptFormula, sat_disj']
      simp only [CL.SatAny, or_false]
      rw [ihc k x ν hν hx, ihd k x ν hν hx]
      simp only [OWL.Interp.sem]
  | all r c ih =>
      intro k x ν hν hx
      have hstep : ∀ y : i.dom,
          (CL.Sat i (CL.updateInd ν (bvar k) y) σ (roleAtom r x (bvar k)) →
            CL.Sat i (CL.updateInd ν (bvar k) y) σ
              (conceptFormula c (bvar k) (k + 1)))
          ↔ (I.role r (ν x) y → I.sem c y) := by
        intro y
        have hν' : FreshVal i (CL.updateInd ν (bvar k) y) := by
          intro m hm
          have hmk : m ≠ bvar k := fun he => bvar_no_colon k (he ▸ hm)
          rw [CL.updateInd, if_neg hmk]
          exact hν m hm
        have hxk : CL.updateInd ν (bvar k) y x = ν x := by
          rw [CL.updateInd, if_neg (okArg_ne hx (Nat.le_refl k))]
        have hkk : CL.updateInd ν (bvar k) y (bvar k) = y := by
          rw [CL.updateInd, if_pos rfl]
        rw [sat_roleAtom hc hν' r x (bvar k),
            ih (k + 1) (bvar k) _ hν' (okArg_bvar (Nat.lt_succ_self k)),
            hxk, hkk]
      rw [conceptFormula, sat_allOne]
      simp only [sat_impl', hstep, OWL.Interp.sem]
  | ex r c ih =>
      intro k x ν hν hx
      have hstep : ∀ y : i.dom,
          (CL.Sat i (CL.updateInd ν (bvar k) y) σ (roleAtom r x (bvar k)) ∧
            CL.Sat i (CL.updateInd ν (bvar k) y) σ
              (conceptFormula c (bvar k) (k + 1)))
          ↔ (I.role r (ν x) y ∧ I.sem c y) := by
        intro y
        have hν' : FreshVal i (CL.updateInd ν (bvar k) y) := by
          intro m hm
          have hmk : m ≠ bvar k := fun he => bvar_no_colon k (he ▸ hm)
          rw [CL.updateInd, if_neg hmk]
          exact hν m hm
        have hxk : CL.updateInd ν (bvar k) y x = ν x := by
          rw [CL.updateInd, if_neg (okArg_ne hx (Nat.le_refl k))]
        have hkk : CL.updateInd ν (bvar k) y (bvar k) = y := by
          rw [CL.updateInd, if_pos rfl]
        rw [sat_roleAtom hc hν' r x (bvar k),
            ih (k + 1) (bvar k) _ hν' (okArg_bvar (Nat.lt_succ_self k)),
            hxk, hkk]
      rw [conceptFormula, sat_exOne]
      simp only [sat_conj', CL.SatAll, and_true, hstep, OWL.Interp.sem]
  | atLeast n r =>
      intro k x ν hν hx
      rw [conceptFormula, sat_exBlock_card0 hc hν r x k n hx]
      simp only [OWL.Interp.sem, OWL.Interp.succWitness]
  | atMost n r =>
      intro k x ν hν hx
      rw [conceptFormula, sat_neg', sat_exBlock_card0 hc hν r x k (n + 1) hx]
      simp only [OWL.Interp.sem, OWL.Interp.succWitness]
  | atLeastQ n r c ih =>
      intro k x ν hν hx
      rw [conceptFormula,
          sat_exBlock_card hc hν r x k n hx _ (fun y => I.sem c y)
            (qualBlock_iff hc σ ih hν k n)]
      simp only [OWL.Interp.sem]
  | atMostQ n r c ih =>
      intro k x ν hν hx
      rw [conceptFormula, sat_neg',
          sat_exBlock_card hc hν r x k (n + 1) hx _ (fun y => I.sem c y)
            (qualBlock_iff hc σ ih hν k (n + 1))]
      simp only [OWL.Interp.sem]


/-! ## Valuation plumbing for the fixed-arity role-box sentences -/

theorem freshVal_updateInd {i : CL.Interp} {ν : String → i.dom}
    (hν : FreshVal i ν) {n : String} (hn : ':' ∉ n.toList) (y : i.dom) :
    FreshVal i (CL.updateInd ν n y) := by
  intro m hm
  have hmn : m ≠ n := fun he => hn (he ▸ hm)
  rw [CL.updateInd, if_neg hmn]
  exact hν m hm

theorem freshVal_iName (i : CL.Interp) : FreshVal i i.iName := fun _ _ => rfl

theorem updateInd_self {i : CL.Interp} (ν : String → i.dom) (n : String)
    (y : i.dom) : CL.updateInd ν n y n = y := by rw [CL.updateInd, if_pos rfl]

theorem updateInd_other {i : CL.Interp} (ν : String → i.dom) {n m : String}
    (h : m ≠ n) (y : i.dom) : CL.updateInd ν n y m = ν m := by
  rw [CL.updateInd, if_neg h]

theorem bvar_ne {k m : Nat} (h : k ≠ m) : bvar k ≠ bvar m :=
  fun he => h (bvar_injective he)

theorem sat_allTwo {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (n m : String) (body : CL.Sentence) :
    CL.Sat i ν σ (.all [.plain n, .plain m] body) ↔
      ∀ x y : i.dom,
        CL.Sat i (CL.updateInd (CL.updateInd ν n x) m y) σ body := by
  simp [CL.Sat, CL.SatForall]

theorem sat_allThree {i : CL.Interp} (ν : String → i.dom)
    (σ : String → List i.dom) (n m p : String) (body : CL.Sentence) :
    CL.Sat i ν σ (.all [.plain n, .plain m, .plain p] body) ↔
      ∀ x y z : i.dom,
        CL.Sat i (CL.updateInd (CL.updateInd (CL.updateInd ν n x) m y) p z)
          σ body := by
  simp [CL.Sat, CL.SatForall]

theorem satisfiesAll_append (i : CL.Interp) (l1 l2 : List CL.Sentence) :
    CL.SatisfiesAll i (l1 ++ l2) ↔
      CL.SatisfiesAll i l1 ∧ CL.SatisfiesAll i l2 := by
  constructor
  · intro h
    exact ⟨fun s hs => h s (List.mem_append_left _ hs),
           fun s hs => h s (List.mem_append_right _ hs)⟩
  · rintro ⟨h1, h2⟩ s hs
    rcases List.mem_append.mp hs with h | h
    · exact h1 s h
    · exact h2 s h

theorem satisfiesAll_map {α : Type} (i : CL.Interp) (l : List α)
    (g : α → CL.Sentence) :
    CL.SatisfiesAll i (l.map g) ↔ ∀ a ∈ l, CL.Satisfies i (g a) :=
  forall_mem_map' g l _

/-! ## Assertions and the role box, transferred -/

theorem satisfies_assertionSentence {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) (φ : OWL.Assertion) :
    CL.Satisfies i (assertionSentence φ) ↔ OWL.Satisfies I (dlNu i) φ := by
  have hν := freshVal_iName i
  cases φ with
  | inst a c =>
      rw [CL.Satisfies, assertionSentence,
          sat_conceptFormula hc (fun _ => []) c 0 (indName a) i.iName hν
            (okArg_dlName 0 'i' a)]
      exact Iff.rfl
  | rel r a b =>
      rw [CL.Satisfies, assertionSentence, sat_roleAtom hc hν]
      exact Iff.rfl
  | diff a b =>
      rw [CL.Satisfies, assertionSentence, sat_neg', sat_eq']
      exact Iff.rfl

theorem satAll_assertions {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) (A : List OWL.Assertion) :
    CL.SatisfiesAll i (A.map assertionSentence) ↔ OWL.SatAll I (dlNu i) A := by
  rw [satisfiesAll_map]
  constructor
  · intro h φ hφ
    exact (satisfies_assertionSentence hc φ).mp (h φ hφ)
  · intro h φ hφ
    exact (satisfies_assertionSentence hc φ).mpr (h φ hφ)

theorem satisfies_subRoleSentence {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) (p q : OWL.Role) :
    CL.Satisfies i (subRoleSentence p q) ↔
      ∀ x y : i.dom, I.role p x y → I.role q x y := by
  have hν := freshVal_iName i
  have key : ∀ x y : i.dom,
      CL.Sat i (CL.updateInd (CL.updateInd i.iName (bvar 0) x) (bvar 1) y)
          (fun _ => [])
          (.impl (roleAtom p (bvar 0) (bvar 1)) (roleAtom q (bvar 0) (bvar 1)))
        ↔ (I.role p x y → I.role q x y) := by
    intro x y
    have hν2 : FreshVal i
        (CL.updateInd (CL.updateInd i.iName (bvar 0) x) (bvar 1) y) :=
      freshVal_updateInd (freshVal_updateInd hν (bvar_no_colon 0) x)
        (bvar_no_colon 1) y
    have h0 : CL.updateInd (CL.updateInd i.iName (bvar 0) x) (bvar 1) y
        (bvar 0) = x := by
      rw [updateInd_other _ (bvar_ne (by decide)), updateInd_self]
    have h1 : CL.updateInd (CL.updateInd i.iName (bvar 0) x) (bvar 1) y
        (bvar 1) = y := updateInd_self _ _ _
    rw [sat_impl', sat_roleAtom hc hν2, sat_roleAtom hc hν2, h0, h1]
  rw [CL.Satisfies, subRoleSentence, sat_allTwo]
  simp only [key]

theorem satisfies_transSentence {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) (r : OWL.Role) :
    CL.Satisfies i (transSentence r) ↔
      ∀ x y z : i.dom, I.role r x y → I.role r y z → I.role r x z := by
  have hν := freshVal_iName i
  have key : ∀ x y z : i.dom,
      CL.Sat i (CL.updateInd (CL.updateInd (CL.updateInd i.iName (bvar 0) x)
            (bvar 1) y) (bvar 2) z) (fun _ => [])
          (.impl (roleAtom r (bvar 0) (bvar 1))
            (.impl (roleAtom r (bvar 1) (bvar 2)) (roleAtom r (bvar 0) (bvar 2))))
        ↔ (I.role r x y → I.role r y z → I.role r x z) := by
    intro x y z
    have hν3 : FreshVal i
        (CL.updateInd (CL.updateInd (CL.updateInd i.iName (bvar 0) x)
          (bvar 1) y) (bvar 2) z) :=
      freshVal_updateInd (freshVal_updateInd
        (freshVal_updateInd hν (bvar_no_colon 0) x) (bvar_no_colon 1) y)
        (bvar_no_colon 2) z
    have h0 : CL.updateInd (CL.updateInd (CL.updateInd i.iName (bvar 0) x)
        (bvar 1) y) (bvar 2) z (bvar 0) = x := by
      rw [updateInd_other _ (bvar_ne (by decide)),
          updateInd_other _ (bvar_ne (by decide)), updateInd_self]
    have h1 : CL.updateInd (CL.updateInd (CL.updateInd i.iName (bvar 0) x)
        (bvar 1) y) (bvar 2) z (bvar 1) = y := by
      rw [updateInd_other _ (bvar_ne (by decide)), updateInd_self]
    have h2 : CL.updateInd (CL.updateInd (CL.updateInd i.iName (bvar 0) x)
        (bvar 1) y) (bvar 2) z (bvar 2) = z := updateInd_self _ _ _
    rw [sat_impl', sat_impl', sat_roleAtom hc hν3, sat_roleAtom hc hν3,
        sat_roleAtom hc hν3, h0, h1, h2]
  rw [CL.Satisfies, transSentence, sat_allThree]
  simp only [key]

theorem satisfiesAll_roleAxiomSentences {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) (R : OWL.RoleAxioms) :
    CL.SatisfiesAll i (roleAxiomSentences R) ↔ OWL.RespectsRBox I R := by
  rw [roleAxiomSentences, satisfiesAll_append, satisfiesAll_map,
      satisfiesAll_map]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun p hp => (satisfies_subRoleSentence hc p.1 p.2).mp (h1 p hp),
            fun r hr => ?_⟩
    exact (satisfies_transSentence hc r).mp (h2 r hr)
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => (satisfies_subRoleSentence hc p.1 p.2).mpr (h1 p hp),
           fun r hr => (satisfies_transSentence hc r).mpr (h2 r hr)⟩

/-- **The translation transfer, stated once against compatibility.**
Both transport directions instantiate this. -/
theorem satisfiesAll_owlDlDirect_iff {i : CL.Interp} {I : OWL.Interp i.dom}
    (hc : DLCompat i I) (R : OWL.RoleAxioms) (A : List OWL.Assertion) :
    CL.SatisfiesAll i (owlDlDirect R A) ↔
      (OWL.RespectsRBox I R ∧ OWL.SatAll I (dlNu i) A) := by
  rw [owlDlDirect, satisfiesAll_append, satisfiesAll_roleAxiomSentences hc,
      satAll_assertions hc]

/-! ## `liftInterpDL` : OWL to CL

The lift cannot preserve the domain. `CL.Interp.rel` receives the
DENOTATION of the predicate term, so an interpretation over `δ` alone
cannot tell `className a` from `className b` when `δ` is a singleton.
`Unified/RdfTransport.lean` solved the same problem with a tag
component `Option String × r.idom`; that answer does NOT work here,
because the cardinality translation asks whether `n + 1` domain
elements are DISTINCT, and a product domain has distinct pairs whose
`δ`-components coincide — an `atMost` sentence would then be violated
by an interpretation whose OWL reading satisfies it.

The domain is therefore the SUM `δ ⊕ String`: the right summand
carries the name-identity, and the class and role extensions are FALSE
on it, so every witness a counting formula can use lies in the left
summand, where distinctness is exactly distinctness in `δ`. -/

/-- The OWL interpretation over the extended domain: the original one
on the left summand, empty on the right. -/
def inlInterp {δ : Type} (I : OWL.Interp δ) : OWL.Interp (δ ⊕ String) where
  concept := fun a z => match z with
    | .inl y => I.concept a y
    | .inr _ => False
  role := fun r z w => match z, w with
    | .inl y, .inl v => I.role r y v
    | _, _ => False

theorem inlInterp_concept {δ : Type} (I : OWL.Interp δ) (a : String) (y : δ) :
    (inlInterp I).concept a (.inl y) ↔ I.concept a y := Iff.rfl

theorem inlInterp_concept_inr {δ : Type} (I : OWL.Interp δ) (a : String)
    (s : String) : ¬ (inlInterp I).concept a (.inr s) := id

theorem inlInterp_role {δ : Type} (I : OWL.Interp δ) (r : OWL.Role) (y v : δ) :
    (inlInterp I).role r (.inl y) (.inl v) ↔ I.role r y v := Iff.rfl

theorem inlInterp_role_inr {δ : Type} (I : OWL.Interp δ) (r : OWL.Role)
    (y : δ) (s : String) : ¬ (inlInterp I).role r (.inl y) (.inr s) := id

/-- A list all of whose members are left injections is a left-injected
list. -/
theorem all_inl {δ : Type} :
    ∀ {l : List (δ ⊕ String)}, (∀ z ∈ l, ∃ y : δ, z = Sum.inl y) →
      ∃ l' : List δ, l = l'.map Sum.inl
  | [], _ => ⟨[], rfl⟩
  | z :: r, h => by
      obtain ⟨y, rfl⟩ := h z (by simp)
      obtain ⟨r', hr'⟩ := all_inl (l := r) (fun w hw => h w (by simp [hw]))
      exact ⟨y :: r', by rw [hr']; rfl⟩

/-- Counting on the extended domain reduces to counting on `δ`, for
any property that is false on the right summand. -/
theorem card_sum_iff {δ : Type} (n : Nat) (P : δ → Prop)
    (P' : δ ⊕ String → Prop) (hinl : ∀ v, P' (.inl v) ↔ P v)
    (hinr : ∀ s, ¬ P' (.inr s)) :
    (∃ l : List (δ ⊕ String), l.length = n ∧ l.Pairwise (· ≠ ·) ∧
        ∀ z ∈ l, P' z)
      ↔ (∃ l : List δ, l.length = n ∧ l.Pairwise (· ≠ ·) ∧ ∀ v ∈ l, P v) := by
  constructor
  · rintro ⟨l, hlen, hpw, hall⟩
    obtain ⟨l', rfl⟩ := all_inl (l := l) (fun z hz => by
      cases z with
      | inl y => exact ⟨y, rfl⟩
      | inr s => exact absurd (hall _ hz) (hinr s))
    refine ⟨l', by simpa using hlen, ?_, ?_⟩
    · rw [List.pairwise_map] at hpw
      exact hpw.imp (fun {a b} hab he => hab (by rw [he]))
    · intro v hv
      exact (hinl v).mp (hall _ (List.mem_map.mpr ⟨v, hv, rfl⟩))
  · rintro ⟨l, hlen, hpw, hall⟩
    refine ⟨l.map Sum.inl, by simpa using hlen, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact hpw.imp (fun {a b} hab he => hab (Sum.inl.inj he))
    · intro z hz
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      exact (hinl v).mpr (hall v hv)

/-- Class-expression semantics is preserved by the left injection. -/
theorem sem_inl {δ : Type} (I : OWL.Interp δ) :
    ∀ (c : OWL.Concept) (y : δ),
      (inlInterp I).sem c (Sum.inl y) ↔ I.sem c y := by
  intro c
  induction c with
  | atom a => intro y; simp only [OWL.Interp.sem]; exact inlInterp_concept I a y
  | top => intro y; simp only [OWL.Interp.sem]
  | bot => intro y; simp only [OWL.Interp.sem]
  | neg c ih => intro y; simp only [OWL.Interp.sem, ih y]
  | conj c d ihc ihd => intro y; simp only [OWL.Interp.sem, ihc y, ihd y]
  | disj c d ihc ihd => intro y; simp only [OWL.Interp.sem, ihc y, ihd y]
  | all r c ih =>
      intro y
      simp only [OWL.Interp.sem]
      constructor
      · intro h v hv
        exact (ih v).mp (h (Sum.inl v) hv)
      · intro h z hz
        cases z with
        | inl v => exact (ih v).mpr (h v hz)
        | inr s => exact absurd hz (inlInterp_role_inr I r y s)
  | ex r c ih =>
      intro y
      simp only [OWL.Interp.sem]
      constructor
      · rintro ⟨z, hz, hc⟩
        cases z with
        | inl v => exact ⟨v, hz, (ih v).mp hc⟩
        | inr s => exact absurd hz (inlInterp_role_inr I r y s)
      · rintro ⟨v, hv, hc⟩
        exact ⟨Sum.inl v, hv, (ih v).mpr hc⟩
  | atLeast n r =>
      intro y
      simp only [OWL.Interp.sem, OWL.Interp.succWitness]
      exact card_sum_iff n (fun v => I.role r y v)
        (fun z => (inlInterp I).role r (Sum.inl y) z)
        (fun v => inlInterp_role I r y v) (fun s => inlInterp_role_inr I r y s)
  | atMost n r =>
      intro y
      simp only [OWL.Interp.sem, OWL.Interp.succWitness]
      exact not_congr (card_sum_iff (n + 1) (fun v => I.role r y v)
        (fun z => (inlInterp I).role r (Sum.inl y) z)
        (fun v => inlInterp_role I r y v) (fun s => inlInterp_role_inr I r y s))
  | atLeastQ n r c ih =>
      intro y
      simp only [OWL.Interp.sem]
      exact card_sum_iff n (fun v => I.role r y v ∧ I.sem c v)
        (fun z => (inlInterp I).role r (Sum.inl y) z ∧ (inlInterp I).sem c z)
        (fun v => and_congr (inlInterp_role I r y v) (ih v))
        (fun s hs => inlInterp_role_inr I r y s hs.1)
  | atMostQ n r c ih =>
      intro y
      simp only [OWL.Interp.sem]
      exact not_congr (card_sum_iff (n + 1) (fun v => I.role r y v ∧ I.sem c v)
        (fun z => (inlInterp I).role r (Sum.inl y) z ∧ (inlInterp I).sem c z)
        (fun v => and_congr (inlInterp_role I r y v) (ih v))
        (fun s hs => inlInterp_role_inr I r y s hs.1))

/-- **`liftInterpDL`** — the CL interpretation an OWL interpretation
plus a name assignment induces. Predicate identity is carried by the
right summand of the domain; see the section header. -/
def liftInterpDL {δ : Type} (I : OWL.Interp δ) (ν : OWL.Ind → δ) : CL.Interp where
  dom := δ ⊕ String
  domWit := .inr ""
  iName := fun n =>
    match dlDecode 'i' n with
    | some a => Sum.inl (ν a)
    | none => Sum.inr n
  iStr := fun _ => .inr ""
  rel := fun p args =>
    match p, args with
    | .inr n, [z] =>
        match dlDecode 'c' n with
        | some a => (inlInterp I).concept a z
        | none => False
    | .inr n, [z, w] =>
        match dlDecode 'r' n with
        | some r => (inlInterp I).role r z w
        | none => False
    | _, _ => False
  fn := fun _ _ => .inr ""
  iProp := fun _ _ _ => .inr ""

theorem liftInterpDL_iName_ind {δ : Type} (I : OWL.Interp δ)
    (ν : OWL.Ind → δ) (a : OWL.Ind) :
    (liftInterpDL I ν).iName (indName a) = Sum.inl (ν a) := by
  simp [liftInterpDL, indName, dlDecode_dlName]

theorem liftInterpDL_iName_class {δ : Type} (I : OWL.Interp δ)
    (ν : OWL.Ind → δ) (a : String) :
    (liftInterpDL I ν).iName (className a) = Sum.inr (className a) := by
  simp [liftInterpDL, className,
    dlDecode_dlName_ne (show ('c' : Char) ≠ 'i' by decide) a]

theorem liftInterpDL_iName_role {δ : Type} (I : OWL.Interp δ)
    (ν : OWL.Ind → δ) (r : OWL.Role) :
    (liftInterpDL I ν).iName (roleName r) = Sum.inr (roleName r) := by
  simp [liftInterpDL, roleName,
    dlDecode_dlName_ne (show ('r' : Char) ≠ 'i' by decide) r]

theorem dlCompat_lift {δ : Type} (I : OWL.Interp δ) (ν : OWL.Ind → δ) :
    DLCompat (liftInterpDL I ν) (inlInterp I) := by
  constructor
  · intro a z
    rw [liftInterpDL_iName_class]
    show _ ↔ (liftInterpDL I ν).rel (Sum.inr (className a)) [z]
    simp [liftInterpDL, className, dlDecode_dlName]
  · intro r z w
    rw [liftInterpDL_iName_role]
    show _ ↔ (liftInterpDL I ν).rel (Sum.inr (roleName r)) [z, w]
    simp [liftInterpDL, roleName, dlDecode_dlName]

theorem respectsRBox_inl {δ : Type} (I : OWL.Interp δ) (R : OWL.RoleAxioms)
    (h : OWL.RespectsRBox I R) : OWL.RespectsRBox (inlInterp I) R := by
  refine ⟨fun p hp z w hzw => ?_, fun r hr z w u hzw hwu => ?_⟩
  · cases z with
    | inr s => exact absurd hzw (by cases w <;> exact id)
    | inl y =>
        cases w with
        | inr s => exact absurd hzw (inlInterp_role_inr I p.1 y s)
        | inl v => exact h.1 p hp y v hzw
  · cases z with
    | inr s => exact absurd hzw (by cases w <;> exact id)
    | inl y =>
        cases w with
        | inr s => exact absurd hzw (inlInterp_role_inr I r y s)
        | inl v =>
            cases u with
            | inr s => exact absurd hwu (inlInterp_role_inr I r v s)
            | inl t => exact h.2 r hr y v t hzw hwu

theorem satAll_inl {δ : Type} (I : OWL.Interp δ) (ν : OWL.Ind → δ)
    (A : List OWL.Assertion) (h : OWL.SatAll I ν A) :
    OWL.SatAll (inlInterp I) (fun a => Sum.inl (ν a)) A := by
  intro φ hφ
  have hs := h φ hφ
  cases φ with
  | inst a c => exact (sem_inl I c (ν a)).mpr hs
  | rel r a b => exact hs
  | diff a b => exact fun he => hs (Sum.inl.inj he)

/-- **Transfer, lift direction**: an OWL model of the role box and the
ABox yields a CL model of the translation. -/
theorem satisfiesAll_owlDlDirect_lift {δ : Type} (I : OWL.Interp δ)
    (ν : OWL.Ind → δ) (R : OWL.RoleAxioms) (A : List OWL.Assertion)
    (hR : OWL.RespectsRBox I R) (hA : OWL.SatAll I ν A) :
    CL.SatisfiesAll (liftInterpDL I ν) (owlDlDirect R A) := by
  refine (satisfiesAll_owlDlDirect_iff (dlCompat_lift I ν) R A).mpr
    ⟨respectsRBox_inl I R hR, ?_⟩
  have hnu : dlNu (liftInterpDL I ν) = fun a => Sum.inl (ν a) :=
    funext (fun a => liftInterpDL_iName_ind I ν a)
  rw [hnu]
  exact satAll_inl I ν A hA

/-- **Transfer, restriction direction**: a CL model of the translation
yields an OWL model of the role box and the ABox, over the same
domain. -/
theorem satisfiesAll_owlDlDirect_restrict (i : CL.Interp)
    (R : OWL.RoleAxioms) (A : List OWL.Assertion)
    (h : CL.SatisfiesAll i (owlDlDirect R A)) :
    OWL.RespectsRBox (restrictInterpDL i) R ∧
      OWL.SatAll (restrictInterpDL i) (dlNu i) A :=
  (satisfiesAll_owlDlDirect_iff (dlCompat_restrict i) R A).mp h

/-! ## Build-time checks -/

section Checks

#guard dlName 'i' "x" == "urn:owl:dl:ix"
#guard dlName 'c' "ex:C" == "urn:owl:dl:cex%cC"
#guard dlDecode 'i' (indName "x:y") == some "x:y"
#guard dlDecode 'c' (indName "a") == none
#guard dlDecode 'i' "nope" == none
#guard indName "a" != className "a"
#guard indName "a" != roleName "a"
#guard className "a" != roleName "a"
#guard bvar 0 == "_"
#guard bvar 3 == "_vvv"
#guard bvars 2 3 == ["_vv", "_vvv", "_vvvv"]
#guard bvars 0 0 == ([] : List String)
#guard decide (bvar 5 != indName "x")
#guard (distinctBlock (bvars 0 3)).length == 3
#guard (distinctBlock (bvars 0 4)).length == 6
#guard (roleAxiomSentences ⟨[("r", "s")], ["t"]⟩).length == 2

end Checks

end L4Factoidal.Unified
