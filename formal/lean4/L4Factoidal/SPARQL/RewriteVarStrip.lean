/-
L4Factoidal.SPARQL.RewriteVarStrip — the OWL-rewrite internal-variable
strip, and the machine-checked reason it must stay at the top level.

Ports `SPARQL11.Algebra.strip_rewrite_internal_vars` (and its two
helpers) together with the composition layer of `OWL.QueryEval`, whose
banner says it holds no RDF or SPARQL semantic logic of its own and is
forward-reference wiring only.

## Why this is a module rather than three definitions

`OWL.QueryRewrite` introduces internal variables — `_sv_`, `_av_`,
`_mc_`, `_mxc_`, `_mxqc1_`, `_exc_`, `_co_` — to carry anchors and
surrogates. Issue <https://github.com/danbri/factoidal/issues/236>
records that they LEAKED into `SELECT *` result rows. The fix strips
them, and CLAUDE.md states the constraint the fix has to respect:

> It must stay at the top level — inner `wrap_distinct_over_ggp`
> Select_All sub-selects deliberately re-expose the anchor var so the
> enclosing pattern can JOIN on it (simple5), so stripping inside them
> decorrelates the join.

`strip_inside_join_admits_spurious_row` below is that constraint as a
theorem. Two solution sequences that share an internal variable with
DIFFERENT values are incompatible, so their join is empty. Strip first
and the shared variable is gone, the two rows become compatible, and
the join produces a row that the unstripped join does not. So moving
the strip inward does not merely lose a column — it changes which rows
come back.

## What is NOT here

`rewriteQuery` itself. `OWL.QueryRewrite` is 1,799 lines and is not
ported, so the three evaluator wrappers below take the rewrite as a
PARAMETER. That makes the composition and the strip placement checkable
without the rewriter, and it is the same idiom the port uses for F\*
`assume val`s. It also means `OWL.QueryEval` stays on the not-covered
list: the Lean side cannot run an OWL-rewritten query, and no alias was
added.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## The internal-variable test

The seven prefixes `OWL.QueryRewrite` generates. A user variable
cannot collide with them by accident in a conforming query: SPARQL
1.1 §19.8 lets a variable name start with an underscore, so this is a
CONVENTION the rewriter and this filter share, not a guarantee the
grammar gives. The F\* source carries the same list. -/
def rewriteInternalPrefixes : List String :=
  ["_sv_", "_av_", "_mc_", "_mxc_", "_mxqc1_", "_exc_", "_co_"]

def isRewriteInternalVar (v : VarName) : Bool :=
  rewriteInternalPrefixes.any (fun p => strStartsWith v p)

/-- Drop the internal bindings from one solution mapping. -/
def stripRewriteInternalVarsMu (mu : Binding) : Binding :=
  mu.filter (fun vt => !isRewriteInternalVar vt.1)

/-- Drop them from every row of a solution sequence. The FINAL
projection is the only place this is applied. -/
def stripRewriteInternalVars (omega : SolutionSeq) : SolutionSeq :=
  omega.map stripRewriteInternalVarsMu

/-! ## What the strip does -/

/-- Nothing internal survives. -/
theorem strip_removes_internal (mu : Binding) :
    ∀ vt ∈ stripRewriteInternalVarsMu mu, isRewriteInternalVar vt.1 = false := by
  intro vt h
  simp only [stripRewriteInternalVarsMu, List.mem_filter] at h
  simpa using h.2

/-- Everything else is untouched, in order. -/
theorem strip_keeps_external {mu : Binding} {vt : VarName × Term}
    (hm : vt ∈ mu) (hi : isRewriteInternalVar vt.1 = false) :
    vt ∈ stripRewriteInternalVarsMu mu := by
  simp only [stripRewriteInternalVarsMu, List.mem_filter]
  exact ⟨hm, by simp [hi]⟩

theorem strip_idempotent (mu : Binding) :
    stripRewriteInternalVarsMu (stripRewriteInternalVarsMu mu)
      = stripRewriteInternalVarsMu mu := by
  simp only [stripRewriteInternalVarsMu, List.filter_filter, Bool.and_self]

theorem strip_seq_length (omega : SolutionSeq) :
    (stripRewriteInternalVars omega).length = omega.length := by
  simp [stripRewriteInternalVars]

/-! ## Why it must stay at the top level

The witness. Two rows sharing `_sv_1` with different values do not
join. Strip the shared variable away and they do. -/

private def vX : VarName := "x"
private def vSv : VarName := "_sv_1"
private def iriA : WfIri := ⟨"http://example.org/a", by decide⟩
private def iriK1 : WfIri := ⟨"http://example.org/k1", by decide⟩
private def iriK2 : WfIri := ⟨"http://example.org/k2", by decide⟩

private def omegaL : SolutionSeq := [[(vX, .iri iriA), (vSv, .iri iriK1)]]
private def omegaR : SolutionSeq := [[(vSv, .iri iriK2)]]

/-- `_sv_1` is recognised as internal, and `?x` is not. Without this
the witness would say nothing about the strip. -/
theorem witness_vars_classified :
    isRewriteInternalVar vSv = true ∧ isRewriteInternalVar vX = false := by
  constructor <;> rfl

/-- **The constraint, as a theorem.** The two sequences do not join,
because they disagree on the internal variable. After stripping, they
do join, and the result carries a row the unstripped join has not. So
stripping before a join changes which rows come back, which is why the
strip belongs to the final projection and not to an inner sub-select. -/
theorem strip_inside_join_admits_spurious_row :
    join omegaL omegaR = [] ∧
    join (stripRewriteInternalVars omegaL) (stripRewriteInternalVars omegaR)
      = [[(vX, Term.iri iriA)]] := by
  constructor <;> rfl

/-! ## The composition layer of `OWL.QueryEval`

The rewrite is a parameter — see the header. Each wrapper is the F\*
source's line for line, and the SELECT one is the only place the strip
appears. -/

variable {Q S : Type}

/-- SELECT with the rewrite applied first, and the strip applied to the
FINAL projection only. -/
def evalSelectQueryOwl (rewriteQuery : Q → Q) (evalSelect : Q → S)
    (toSeq : S → SolutionSeq) (q : Q) : SolutionSeq :=
  stripRewriteInternalVars (toSeq (evalSelect (rewriteQuery q)))

/-- ASK with the rewrite applied first. No strip: the answer is a
Boolean, so no column can leak. -/
def evalAskQueryOwl (rewriteQuery : Q → Q) (evalAsk : Q → Bool) (q : Q) : Bool :=
  evalAsk (rewriteQuery q)

/-- CONSTRUCT with the rewrite applied first. No strip: the template
names user variables only, so an internal binding cannot reach a
constructed triple. -/
def evalConstructQueryOwl (rewriteQuery : Q → Q) (evalConstruct : Q → List Triple)
    (q : Q) : List Triple :=
  evalConstruct (rewriteQuery q)

/-- A rewrite that changes nothing leaves the SELECT wrapper as the
strip alone. This is what makes the wrapper safe to apply to every
query, which the F\* banner asserts and does not prove. -/
theorem evalSelectQueryOwl_id (evalSelect : Q → S) (toSeq : S → SolutionSeq) (q : Q) :
    evalSelectQueryOwl id evalSelect toSeq q
      = stripRewriteInternalVars (toSeq (evalSelect q)) := rfl

/-- And on a result with no internal bindings, the SELECT wrapper with
an identity rewrite is the identity. -/
theorem evalSelectQueryOwl_id_clean (evalSelect : Q → S) (toSeq : S → SolutionSeq)
    (q : Q) (h : ∀ mu ∈ toSeq (evalSelect q), ∀ vt ∈ mu,
                 isRewriteInternalVar vt.1 = false) :
    evalSelectQueryOwl id evalSelect toSeq q = toSeq (evalSelect q) := by
  simp only [evalSelectQueryOwl, id_eq, stripRewriteInternalVars]
  rw [List.map_congr_left (g := fun mu => mu)]
  · exact List.map_id _
  · intro mu hmu
    exact List.filter_eq_self.mpr (fun vt hvt => by simp [h mu hmu vt hvt])

/-! ## Build-time checks -/

#guard isRewriteInternalVar "_sv_1" == true
#guard isRewriteInternalVar "_mxqc1_3" == true
#guard isRewriteInternalVar "_co_0" == true
#guard isRewriteInternalVar "x" == false
#guard isRewriteInternalVar "_user" == false
#guard (stripRewriteInternalVarsMu [(vX, Term.iri iriA), (vSv, Term.iri iriK1)]).length == 1

/-! ## Axiom audit -/

#print axioms strip_removes_internal
#print axioms strip_idempotent
#print axioms strip_inside_join_admits_spurious_row
#print axioms evalSelectQueryOwl_id_clean

end L4Factoidal.SPARQL
