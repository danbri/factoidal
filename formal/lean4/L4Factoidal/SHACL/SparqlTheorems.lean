/-
L4Factoidal.SHACL.SparqlTheorems — the SHACL-SPARQL engine against its
specification.

`ShaclTheorems.lean` proves `conformance_iff`: the SHACL Core engine
reports no result for a focus node exactly when `Spec.Conforms` holds.
This file is the same relation for SHACL Part 2.

WHAT IS COVERED. Each of the three SHACL-SPARQL judgments is proved
equivalent to its specification, pointwise:

  * §5.1  `sh:sparql`             — `sparqlViolationsForFocus_eq_nil_iff`
  * §6.2.1 ASK validator          — `customAskViolation_eq_nil_iff`
  * §6.2.2 SELECT validator       — `customSelectViolations_eq_nil_iff`
  * §6    one component, either kind, over the value nodes —
          `evalCustomComponent_eq_nil_iff`

and at graph level `validateWithSparql_conforms_iff` decomposes the
report's `sh:conforms` into SHACL Core conformance (`Spec.GraphConforms`,
through the existing `validate_conforms_iff`) and the emptiness of the
two SHACL-SPARQL passes.

WHAT IS NOT COVERED, precisely:

  1. `Spec.Conforms` itself is NOT extended with the new components,
     and cannot be: `conformance_iff` is an `iff` against
     `collectShapeViolations`, which by design never evaluates a
     `.sparql` or `.custom` constraint. See the design note in
     `Sparql.lean`'s `Spec` section.
  2. The quantifier push from "the shape-level pass produced no
     result" down to `Spec.SparqlShapeConforms` /
     `Spec.CustomOccurrenceConforms` is not proved. It is a routine
     `SparqlOutcome.concat` / `List.flatMap` decomposition over the
     focus-node and constraint lists; stating it as unproved is more
     use than an unfinished proof.
  3. The §5.3.2 FAILURE channel is specified only negatively: a query
     SHACL rejects satisfies every predicate above vacuously, because
     failure is a different outcome from non-conformance. That a
     rejected query yields NO results is `withPreboundQuery_error`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SHACL.Sparql
import L4Factoidal.SHACL.ShaclTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL

namespace L4Factoidal.SHACL

/-! ## §5.3 a substituted value behaves as the binding would

The property that makes AST substitution a faithful implementation of
pre-binding in EXPRESSION positions: the expression the substitution
puts in place of `$v` evaluates to exactly what `Expr.var v` would
evaluate to under the pre-binding row — including SPARQL §17.1 numeric
promotion, which `Expr.lit` alone does not perform. -/

theorem termToExpr_evalIn_eq_literalPromote (env : EvalEnv) (mu : Binding) (l : WfLiteral) :
    (termToExpr? (.literal l)).map (Expr.evalIn env mu) = some (literalPromote l) := by
  simp only [termToExpr?, literalPromote]
  by_cases h1 : (l.val.datatype == RDF.xsdInteger) = true
  · rw [if_pos h1, if_pos h1]
    cases hp : parseIntString l.val.lexicalForm <;> simp [Expr.evalIn, hp]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (l.val.datatype == RDF.xsdDecimal) = true
    · rw [if_pos h2, if_pos h2]; simp [Expr.evalIn]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 :
          (l.val.datatype == RDF.xsdDouble || l.val.datatype == SPARQL.xsdFloat) = true
      · rw [if_pos h3, if_pos h3]; simp [Expr.evalIn]
      · rw [if_neg h3, if_neg h3]
        by_cases h4 : (l.val.datatype == RDF.xsdBoolean) = true
        · rw [if_pos h4, if_pos h4]; simp [Expr.evalIn]
        · rw [if_neg h4, if_neg h4]; simp [Expr.evalIn]

/-- The same statement in the form the substitution uses it: replacing
`Expr.var v` by `termToExpr? t` preserves the value `Expr.var v` has
under a mapping that binds `v` to `t`. -/
theorem substVarExpr_var_evalIn (env : EvalEnv) (mu : Binding) (v : VarName) (l : WfLiteral) :
    Expr.evalIn env mu (substVarExpr v (.literal l) (.var v)) =
      Expr.evalIn env [(v, .literal l)] (.var v) := by
  have h := termToExpr_evalIn_eq_literalPromote env mu l
  have hr : Expr.evalIn env [(v, Term.literal l)] (Expr.var v) = literalPromote l := by
    simp [Expr.evalIn, Binding.lookup]
  rw [hr]
  simp only [substVarExpr, beq_self_eq_true, if_true]
  cases he : termToExpr? (Term.literal l) with
  | none => rw [he] at h; simp at h
  | some e => rw [he] at h; simpa using h

/-! ## The failure channel produces no results -/

/-- §5.3.2: a query SHACL rejects yields a failure and no validation
result — never a partial, silently-different answer. -/
theorem withPreboundQuery_error (queryText : String) (path : Option Path)
    (binds : List (VarName × Term)) (what : String) (k : Query → SparqlOutcome)
    (e : String) (h : preboundQuery queryText path binds = .error e) :
    (withPreboundQuery queryText path binds what k).results = [] ∧
      (withPreboundQuery queryText path binds what k).failure = some (what ++ " " ++ e) := by
  simp [withPreboundQuery, h]

/-! ## §5.1 `sh:sparql` -/

/-- The engine reports no result for a `sh:sparql` constraint at a
focus node exactly when the specification says the focus node
satisfies it. -/
theorem sparqlViolationsForFocus_eq_nil_iff (data shapesRaw : Graph) (focus : Term)
    (s : Shape) (cref : ShapeRef) (queryText : String) (cmsg : Option WfLiteral)
    (csev : Severity) :
    (sparqlViolationsForFocus data shapesRaw focus s cref queryText cmsg csev).results = []
      ↔ Spec.SparqlSatisfies data shapesRaw focus s queryText := by
  unfold sparqlViolationsForFocus withPreboundQuery Spec.SparqlSatisfies
  cases h : preboundQuery queryText s.path (sparqlPrebindings focus s) with
  | error e => simp
  | ok q => simp [List.map_eq_nil_iff]

/-! ## §6.2.1 ASK validators -/

theorem customAskViolation_eq_nil_iff (data : Graph) (focus v : Term) (s : Shape)
    (cc : Constraint) (queryText : String) (params : List (VarName × Term)) :
    (customAskViolation data focus v s cc queryText params).results = []
      ↔ Spec.AskValidatorSatisfies data focus v s queryText params := by
  unfold customAskViolation withPreboundQuery Spec.AskValidatorSatisfies
  cases h : preboundQuery queryText s.path (customPrebindings focus (some v) params) with
  | error e => simp
  | ok q =>
    simp only [reduceIte, Except.ok.injEq, forall_eq']
    cases hask : evalAsk emptyEnv { default := data, named := [] } q with
    | false => simp [SparqlOutcome.empty]
    | true => simp [SparqlOutcome.empty]

/-! ## §6.2.2 SELECT validators -/

theorem customSelectViolations_eq_nil_iff (data : Graph) (focus : Term) (s : Shape)
    (cc : Constraint) (queryText : String) (params : List (VarName × Term))
    (msgTemplate : Option String) :
    (customSelectViolations data focus s cc queryText params msgTemplate).results = []
      ↔ Spec.SelectValidatorSatisfies data focus s queryText params := by
  unfold customSelectViolations withPreboundQuery Spec.SelectValidatorSatisfies
  cases h : preboundQuery queryText s.path (customPrebindings focus none params) with
  | error e => simp
  | ok q => simp [List.map_eq_nil_iff]

/-! ## §6 one constraint component -/

theorem SparqlOutcome.concat_results_eq_nil_iff (os : List SparqlOutcome) :
    (SparqlOutcome.concat os).results = [] ↔ ∀ o ∈ os, o.results = [] := by
  induction os with
  | nil => simp [SparqlOutcome.concat, SparqlOutcome.empty]
  | cons o rest ih =>
    simp [SparqlOutcome.concat, SparqlOutcome.append, ih]

/-- Either validator kind, over the occurrence's value nodes. -/
theorem evalCustomComponent_eq_nil_iff (data : Graph) (focus : Term) (s : Shape)
    (values : List Term) (cc : Constraint) :
    (evalCustomComponent data focus s values cc).results = []
      ↔ Spec.CustomSatisfies data focus s values cc := by
  unfold evalCustomComponent Spec.CustomSatisfies
  match cc with
  | .custom comp isAsk queryText params msgTemplate =>
    cases isAsk with
    | true =>
      simp only [reduceIte, SparqlOutcome.concat_results_eq_nil_iff, List.mem_map]
      constructor
      · intro h v hv
        exact (customAskViolation_eq_nil_iff data focus v s _ queryText params).1
          (h _ ⟨v, hv, rfl⟩)
      · rintro h _ ⟨v, hv, rfl⟩
        exact (customAskViolation_eq_nil_iff data focus v s _ queryText params).2 (h v hv)
    | false =>
      simpa using
        customSelectViolations_eq_nil_iff data focus s
          (.custom comp false queryText params msgTemplate) queryText params msgTemplate
  | .cls _ | .datatype _ | .nodeKind _ | .minCount _ | .maxCount _
  | .minInclusive _ | .maxInclusive _ | .minExclusive _ | .maxExclusive _
  | .minLength _ | .maxLength _ | .pattern _ _ | .languageIn _ | .uniqueLang _
  | .equals _ | .disjoint _ | .lessThan _ | .lessThanOrEquals _
  | .notOf _ | .andOf _ | .orOf _ | .xoneOf _ | .nodeOf _
  | .qualifiedMinCount _ _ _ | .qualifiedMaxCount _ _ _
  | .closed _ | .hasValue _ | .inSet _ | .sparql _ _ _ _ =>
    simp [SparqlOutcome.empty]

/-! ## §3.1 the report -/

/-- The report's `sh:conforms` decomposes into SHACL Core conformance
and the two SHACL-SPARQL passes. Item 2 of the module header's
"not covered" list is exactly the step from the two pass-emptiness
conjuncts to `Spec.GraphConformsWithSparql`'s own quantifiers. -/
theorem validateWithSparql_conforms_iff (data shapesRaw : Graph) (sg : ShapesGraph) :
    (validateWithSparql data shapesRaw sg).conforms = true ↔
      Spec.GraphConforms data sg ∧
      (∀ s ∈ sg.shapes.filter (fun s => !s.targets.isEmpty),
         (sparqlViolationsForShape data shapesRaw (distinctSubjects data) s).results = []) ∧
      (∀ s ∈ sg.shapes.filter (fun s => !s.targets.isEmpty),
         (customViolationsForShape data (distinctSubjects data) sg.shapes s
            (validateFuel sg.shapes)).results = []) := by
  have hcore : (validate data sg).results = [] ↔ Spec.GraphConforms data sg := by
    have := validate_conforms_iff data sg
    simpa [validate, List.isEmpty_iff] using this
  simp only [validateWithSparql, SparqlOutcome.append, List.isEmpty_iff,
    List.append_eq_nil_iff, SparqlOutcome.concat_results_eq_nil_iff, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, hcore, and_assoc]

/-- A conforming SHACL-SPARQL report is a certificate of SHACL Core
conformance. -/
theorem validateWithSparql_sound_core (data shapesRaw : Graph) (sg : ShapesGraph)
    (h : (validateWithSparql data shapesRaw sg).conforms = true) :
    Spec.GraphConforms data sg :=
  ((validateWithSparql_conforms_iff data shapesRaw sg).mp h).1

/-! ## Axiom audit -/

#print axioms withPreboundQuery_error
#print axioms sparqlViolationsForFocus_eq_nil_iff
#print axioms customAskViolation_eq_nil_iff
#print axioms customSelectViolations_eq_nil_iff
#print axioms SparqlOutcome.concat_results_eq_nil_iff
#print axioms evalCustomComponent_eq_nil_iff
#print axioms validateWithSparql_conforms_iff
#print axioms validateWithSparql_sound_core

end L4Factoidal.SHACL
