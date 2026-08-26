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
