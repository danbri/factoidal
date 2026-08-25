/-
L4Factoidal.OWL.QueryRewriteJoins — layer 6 of the port of
`OWL.QueryRewrite`: join normalisation, and the semantic claim it rests
on.

## What the rewrite does and why

`rewrite_query` runs `normalise_joins` before the class-expression
rewriter. The F* source gives the reason: the SPARQL parser splits a
basic graph pattern at every period, so a single user-level pattern

    ?x a [ owl:intersectionOf (:A :B) ] .

parses to a tree of one- and two-triple `GP_BGP` leaves under `GP_Join`.
The class-expression marker and its `rdf:first`/`rdf:rest` chain land in
different leaves, and the rewriter, which works one BGP at a time, finds
nothing. `normalise_joins` folds adjacent BGP leaves back into one.

## The claim the F* source makes in a comment

The F* header says the flattening "preserves SPARQL semantics (GP_Join
of two BGPs = BGP-concat)". That is a statement about §18.5 evaluation,
written as a comment next to a function that runs on the shipping OWL
query path. This layer states it and proves the part of it that is a
list identity.

`evalBgp_append` is that part, and it is exact — not up to reordering,
not up to `SMapEq`:

    evalBgp (b1 ++ b2) g = (evalBgp b1 g).flatMap (evalBgpFrom g b2)

`evalBgpFrom` seeds the second half with each row of the first, which is
why the identity holds on the nose. `evalBgpFrom_extends` says the seed
survives: a row produced from `mu0` agrees with `mu0` on every variable
`mu0` binds, so coalescing never overwrites a binding the left BGP made.

## What is NOT proved here, and why it is stated rather than assumed

The full claim needs one more step:

    Occurs mu (evalBgp (b1 ++ b2) g)
      ↔ Occurs mu (join (evalBgp b1 g) (evalBgp b2 g))

`evalBgp_append` reduces the left side to a seeded evaluation of `b2`;
the right side evaluates `b2` from the empty mapping and filters by
`Binding.compatible` afterwards. Bridging the two needs a lemma
comparing seeded and unseeded `tpMatch` on the same graph triple, and
`tryBindTerm` threads the mapping through subject, predicate and object
in sequence, so a triple pattern with a repeated variable does not
decompose into independent per-position facts. Doing it properly is its
own piece of work, tracked as
<https://github.com/danbri/factoidal/issues/568>, not left implicit
here.

Nothing in this file assumes it. Every theorem below is proved.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.JoinRefinement
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.OWL.QueryRewriteJoins

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## 1. Coalescing two normalised patterns

Transcribed arm for arm from the F* `coalesce_join`. The three
BGP-shaped arms are the ones that do work; everything else keeps the
`GP_Join` node. -/

def coalesceJoin (na nb : QueryPattern) : QueryPattern :=
  match na, nb with
  | .bgp ba, .bgp bb => .bgp (ba ++ bb)
  | .bgp ba, .join (.bgp bb) rest => .join (.bgp (ba ++ bb)) rest
  | .join leftSpine (.bgp ba), .bgp bb => .join leftSpine (.bgp (ba ++ bb))
  | _, _ => .join na nb

/-! ## 2. Normalising a whole pattern

Structural recursion; only the `join` arm coalesces. Sub-selects are
deliberately not descended into, matching the F* source. -/

def normaliseJoins : QueryPattern → QueryPattern
  | .bgp b => .bgp b
  | .join a b => coalesceJoin (normaliseJoins a) (normaliseJoins b)
  | .leftJoin a b e => .leftJoin (normaliseJoins a) (normaliseJoins b) e
  | .filter e a => .filter e (normaliseJoins a)
  | .union a b => .union (normaliseJoins a) (normaliseJoins b)
  | .minus a b => .minus (normaliseJoins a) (normaliseJoins b)
  | .graph gt a => .graph gt (normaliseJoins a)
  | .lateral a b => .lateral (normaliseJoins a) (normaliseJoins b)
  | .bind e v a => .bind e v (normaliseJoins a)
  | .values vs rs => .values vs rs
  | .service i s a => .service i s (normaliseJoins a)
  | .serviceVar v s a => .serviceVar v s (normaliseJoins a)
  | .subSelect q => .subSelect q
  | .propertyPath s pp o => .propertyPath s pp o
  | .empty => .empty

/-! ## 3. Structural facts about the two functions -/

/-- The arm that does the work. -/
theorem coalesceJoin_bgp_bgp (ba bb : Bgp) :
    coalesceJoin (.bgp ba) (.bgp bb) = .bgp (ba ++ bb) := rfl

/-- A BGP is a fixed point. -/
theorem normaliseJoins_bgp (b : Bgp) : normaliseJoins (.bgp b) = .bgp b := rfl

/-- Two BGP leaves under a join become one BGP. This is the shape the
class-expression rewriter needs, and the reason the pass exists. -/
theorem normaliseJoins_join_of_bgps (ba bb : Bgp) :
    normaliseJoins (.join (.bgp ba) (.bgp bb)) = .bgp (ba ++ bb) := rfl

/-- UNION is preserved, so normalisation cannot merge across a union
branch. -/
theorem normaliseJoins_union (a b : QueryPattern) :
    normaliseJoins (.union a b) = .union (normaliseJoins a) (normaliseJoins b) := rfl

/-- A sub-select body is left alone, matching the F* source. -/
theorem normaliseJoins_subSelect (q : Query) :
    normaliseJoins (.subSelect q) = .subSelect q := rfl

/-! ## 4. The semantic identity

`evalBgpFrom` seeds the rest of the BGP with each row produced so far,
so appending two BGPs is exactly running the second from every row of
the first. -/

theorem evalBgpFrom_append (g : Graph) (b1 b2 : Bgp) (mu : Binding) :
    evalBgpFrom g (b1 ++ b2) mu
      = (evalBgpFrom g b1 mu).flatMap (evalBgpFrom g b2) := by
  induction b1 generalizing mu with
  | nil => simp [evalBgpFrom]
  | cons tp rest ih =>
      simp only [List.cons_append, evalBgpFrom, List.flatMap_assoc]
      congr 1
      funext mu'
      exact ih mu'

/-- BGP concatenation, at the evaluator. The identity is exact: same
list, same order, same multiplicities. -/
theorem evalBgp_append (g : Graph) (b1 b2 : Bgp) :
    evalBgp (b1 ++ b2) g = (evalBgp b1 g).flatMap (evalBgpFrom g b2) := by
  simp [evalBgp, evalBgpFrom_append]

/-! ## 5. The seed survives

Coalescing feeds the left BGP's rows into the right BGP as seeds. These
theorems say a seeded run never contradicts or drops what the seed
already bound, so the left BGP's answers are not silently rewritten by
the right one. -/

/-- `tryBindTerm` either fails or returns a mapping that agrees with the
input wherever the input was already defined. -/
theorem tryBindTerm_extends : ∀ (pt : PatternTerm) (t : Term) (mu mu' : Binding),
    tryBindTerm pt t mu = some mu' →
    ∀ v tv, mu.lookup v = some tv → mu'.lookup v = some tv := by
  intro pt
  induction pt with
  | iri i =>
      intro t mu mu' h v tv hv
      cases t <;> simp_all [tryBindTerm]
  | bnode b =>
      intro t mu mu' h v tv hv
      cases t <;> simp_all [tryBindTerm]
  | literal l =>
      intro t mu mu' h v tv hv
      cases t <;> simp_all [tryBindTerm]
  | var w =>
      intro t mu mu' h v tv hv
      unfold tryBindTerm at h
      cases hw : Binding.lookup w mu with
      | some existing =>
          rw [hw] at h; dsimp only at h
          by_cases he : existing.eqb t = true
          · rw [if_pos he] at h
            cases h; exact hv
          · rw [if_neg he] at h
            exact absurd h (by simp)
      | none =>
          rw [hw] at h; dsimp only at h
          simp only [Option.some.injEq] at h
          subst h
          by_cases hvw : v = w
          · subst hvw; rw [hw] at hv; exact absurd hv (by simp)
          · unfold Binding.bind Binding.lookup
            rw [if_neg (fun hh => hvw hh.symm)]
            exact hv
  | tripleTerm ps pp po ihs ihp iho =>
      intro t mu mu' h v tv hv
      unfold tryBindTerm at h
      split at h
      all_goals (try exact absurd h (by simp))
      rename_i _ s p o
      cases hs : tryBindTerm ps s.toTerm mu with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some mu1 =>
          rw [hs] at h; dsimp only at h
          cases hp : tryBindTerm pp (.iri p) mu1 with
          | none => rw [hp] at h; exact absurd h (by simp)
          | some mu2 =>
              rw [hp] at h; dsimp only at h
              exact iho o mu2 mu' h v tv
                (ihp (.iri p) mu1 mu2 hp v tv (ihs s.toTerm mu mu1 hs v tv hv))

theorem tryBindSubject_extends (ps : PatternSubject) (s : Subject)
    (mu mu' : Binding) (h : tryBindSubject ps s mu = some mu') :
    ∀ v tv, Binding.lookup v mu = some tv → Binding.lookup v mu' = some tv := by
  intro v tv hv
  cases ps with
  | iri i => cases s <;> simp_all [tryBindSubject]
  | bnode b => cases s <;> simp_all [tryBindSubject]
  | tripleTerm _ _ _ => exact absurd h (by simp [tryBindSubject])
  | var w =>
      unfold tryBindSubject at h; dsimp only at h
      cases hw : Binding.lookup w mu with
      | some existing =>
          rw [hw] at h; dsimp only at h
          by_cases he : existing.eqb s.toTerm = true
          · rw [if_pos he] at h; cases h; exact hv
          · rw [if_neg he] at h; exact absurd h (by simp)
      | none =>
          rw [hw] at h; dsimp only at h
          simp only [Option.some.injEq] at h
          subst h
          by_cases hvw : v = w
          · subst hvw; rw [hw] at hv; exact absurd hv (by simp)
          · unfold Binding.bind Binding.lookup
            rw [if_neg (fun hh => hvw hh.symm)]
            exact hv

theorem tpMatch_extends (tp : TriplePattern) (t : Triple) (mu mu' : Binding)
    (h : tpMatch tp t mu = some mu') :
    ∀ v tv, Binding.lookup v mu = some tv → Binding.lookup v mu' = some tv := by
  intro v tv hv
  unfold tpMatch at h
  cases hs : tryBindSubject tp.s t.s mu with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some mu1 =>
      rw [hs] at h; dsimp only at h
      cases hp : tryBindTerm tp.p (.iri t.p) mu1 with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some mu2 =>
          rw [hp] at h; dsimp only at h
          exact tryBindTerm_extends tp.o t.o mu2 mu' h v tv
            (tryBindTerm_extends tp.p (.iri t.p) mu1 mu2 hp v tv
              (tryBindSubject_extends tp.s t.s mu mu1 hs v tv hv))

/-- The seed survives a whole BGP. This is what makes coalescing safe
for the left BGP's answers: whatever the left half bound, every row the
right half produces still binds the same way. -/
theorem evalBgpFrom_extends (g : Graph) : ∀ (b : Bgp) (mu0 mu : Binding),
    mu ∈ evalBgpFrom g b mu0 →
    ∀ v tv, Binding.lookup v mu0 = some tv → Binding.lookup v mu = some tv
  | [], mu0, mu => by
      intro h v tv hv
      simp only [evalBgpFrom, List.mem_singleton] at h
      subst h; exact hv
  | tp :: rest, mu0, mu => by
      intro h v tv hv
      simp only [evalBgpFrom, List.mem_flatMap] at h
      obtain ⟨mu1, hmu1, hrest⟩ := h
      simp only [evalTP, List.mem_filterMap] at hmu1
      obtain ⟨t, _, hmatch⟩ := hmu1
      exact evalBgpFrom_extends g rest mu1 mu hrest v tv
        (tpMatch_extends tp t mu0 mu1 hmatch v tv hv)

/-! ## Build-time checks -/

private def bV : VarName := "v"
private def iriP : WfIri := ⟨"http://example.org/p", by decide⟩
private def iriQ : WfIri := ⟨"http://example.org/q", by decide⟩

private def bgpP : Bgp := [{ s := .var bV, p := .iri iriP, o := .var "o1" }]
private def bgpQ : Bgp := [{ s := .var bV, p := .iri iriQ, o := .var "o2" }]

private def bgpSize (p : QueryPattern) : Nat :=
  match p with | .bgp b => b.length | _ => 0

private def isJoin (p : QueryPattern) : Bool :=
  match p with | .join _ _ => true | _ => false

/-! Two BGP leaves under a join become one BGP carrying both triples. -/
#guard bgpSize (normaliseJoins (.join (.bgp bgpP) (.bgp bgpQ))) == 2
#guard isJoin (normaliseJoins (.join (.bgp bgpP) (.bgp bgpQ))) == false

/-! A three-leaf join spine collapses all the way down. -/
#guard bgpSize (normaliseJoins (.join (.join (.bgp bgpP) (.bgp bgpQ)) (.bgp bgpP))) == 3
#guard bgpSize (normaliseJoins (.join (.bgp bgpP) (.join (.bgp bgpQ) (.bgp bgpP)))) == 3

/-! A UNION branch blocks the merge, so normalisation cannot pull
triples across a union. -/
#guard isJoin (normaliseJoins (.join (.bgp bgpP) (.union (.bgp bgpQ) .empty))) == true

/-! The empty group pattern is not a BGP, so it does not absorb. -/
#guard isJoin (normaliseJoins (.join (.bgp bgpP) .empty)) == true

/-! ## Axiom audit -/

#print axioms evalBgpFrom_append
#print axioms evalBgp_append
#print axioms tpMatch_extends
#print axioms evalBgpFrom_extends

end L4Factoidal.OWL.QueryRewriteJoins
