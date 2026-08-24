/-
L4Factoidal.OWL.QueryEval — port of `OWL.QueryEval`.

The F* module is the wiring that composes `OWL.QueryRewrite.
rewrite_query` with the three top-level SPARQL evaluators. Its banner
says why it is a module of its own: `OWL.QueryRewrite` opens
`SPARQL11.Algebra` for the query AST, so `SPARQL11.Algebra` cannot open
`OWL.QueryRewrite` back without a module cycle. The Lean tree has the
same shape and needs the same split.

`SPARQL/RewriteVarStrip.lean` already carried the three wrappers with
the rewrite as a PARAMETER, because the rewrite did not exist yet. This
module is where the parameter is finally filled in: layer 7's
`rewriteQueryPattern` lifted from a pattern to a whole query.

## Where the strip goes, and why only there

`evalSelectQueryOwl` strips the rewrite's internal variables from the
FINAL projection and nowhere else. The F* source records the reason:
inner `Select_All` sub-selects deliberately re-expose the anchor
variable so the enclosing pattern can join on it, so stripping inside
them decorrelates the join. ASK returns a Boolean, so no column can
leak; CONSTRUCT names user variables only, so an internal binding
cannot reach a constructed triple. Neither wrapper strips.

## Safe to apply unconditionally

The F* banner says the rewriter "is a no-op for queries that contain no
flat-CE shape … so it is safe to apply unconditionally".
`rewriteQuery_noMarker_bgp` states the BGP case of that: a basic graph
pattern whose marker search finds nothing comes back unchanged, and the
whole query record is rebuilt from its own fields.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.OWL.QueryMaterialise
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.OWL.QueryEval

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.OWL.QueryRewriteNested
open L4Factoidal.OWL.QueryMaterialise (augmentForQuery)

/-! ## 1. The rewrite, at the query level

The F* source writes `{ q with q_pattern = … }`. `Query` is an
inductive rather than a structure here, so the record update is spelled
out through the accessors — every other field is carried across
unchanged, which is what the F* record update means. -/

def rewriteQuery (q : Query) : Query :=
  .mk q.form q.dataset (rewriteQueryPattern q.pattern) q.groupBy q.having
      q.modifier q.postValues q.base

theorem rewriteQuery_pattern (q : Query) :
    (rewriteQuery q).pattern = rewriteQueryPattern q.pattern := rfl

/-- Every field except the pattern survives the rewrite. -/
theorem rewriteQuery_preserves (q : Query) :
    (rewriteQuery q).form = q.form
    ∧ (rewriteQuery q).dataset = q.dataset
    ∧ (rewriteQuery q).groupBy = q.groupBy
    ∧ (rewriteQuery q).having = q.having
    ∧ (rewriteQuery q).modifier = q.modifier
    ∧ (rewriteQuery q).postValues = q.postValues
    ∧ (rewriteQuery q).base = q.base :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. The three evaluators

Each one fills the rewrite parameter of the matching wrapper in
`SPARQL/RewriteVarStrip.lean`. -/

/-- SELECT with the OWL rewrite, and the internal-variable strip on the
final projection. The dataset is augmented first
(`QueryMaterialise.augmentForQuery`): each
maximum-qualified-cardinality-one shape in the query gets a canonical
restriction node whose members are exactly the individuals
`Mat.isMember` proves — the sound replacement for the F\* closure's
over-typed canonical node. -/
def evalSelectOwl (env : EvalEnv) (ds : Dataset) (q : Query) : SolutionSeq :=
  SPARQL.evalSelectQueryOwl rewriteQuery
    (evalSelect env (augmentForQuery ds q)) Prod.snd q

/-- The projected variable list of the rewritten query. Reported
alongside the rows, as `evalSelect` does. -/
def evalSelectOwlVars (env : EvalEnv) (ds : Dataset) (q : Query) : List VarName :=
  (evalSelect env (augmentForQuery ds q) (rewriteQuery q)).fst

def evalAskOwl (env : EvalEnv) (ds : Dataset) (q : Query) : Bool :=
  SPARQL.evalAskQueryOwl rewriteQuery (evalAsk env (augmentForQuery ds q)) q

def evalConstructOwl (env : EvalEnv) (ds : Dataset) (q : Query) : Graph :=
  SPARQL.evalConstructQueryOwl rewriteQuery
    (evalConstruct env (augmentForQuery ds q)) q

/-! ## 3. Facts

The three wrappers differ in exactly one way, and these theorems pin
it: SELECT strips, the other two do not. -/

theorem evalSelectOwl_is_strip (env : EvalEnv) (ds : Dataset) (q : Query) :
    evalSelectOwl env ds q
      = stripRewriteInternalVars
          (evalSelect env (augmentForQuery ds q) (rewriteQuery q)).snd := rfl

theorem evalAskOwl_no_strip (env : EvalEnv) (ds : Dataset) (q : Query) :
    evalAskOwl env ds q
      = evalAsk env (augmentForQuery ds q) (rewriteQuery q) := rfl

theorem evalConstructOwl_no_strip (env : EvalEnv) (ds : Dataset) (q : Query) :
    evalConstructOwl env ds q
      = evalConstruct env (augmentForQuery ds q) (rewriteQuery q) := rfl

/-- A query whose pattern is one marker-free BGP is rewritten to
itself. This is the BGP case of the F* banner's claim that the rewriter
is a no-op on queries with no class-expression shape, which is what
makes applying it unconditionally safe. -/
theorem rewriteQuery_noMarker_bgp (form : QueryForm) (b : Bgp)
    (h : findMarkers b = []) :
    rewriteQuery (mkQuery form (.bgp b)) = mkQuery form (.bgp b) := by
  simp only [rewriteQuery, mkQuery, Query.form, Query.dataset, Query.pattern,
             Query.groupBy, Query.having, Query.modifier, Query.postValues,
             Query.base, rewriteQueryPattern,
             QueryRewriteJoins.normaliseJoins, rewritePatternNested,
             rewriteBgpNested_noMarker b h]

/-! ## Build-time checks -/

private def cP : WfIri := ⟨"http://example.org/p", by decide⟩

private def plainBgp : Bgp :=
  [ { s := .var "x", p := .iri cP, o := .var "y" } ]

private def plainQuery : Query := mkQuery (.select .all) (.bgp plainBgp)

/-! The rewrite is the identity on a marker-free query. -/
#guard (match (rewriteQuery plainQuery).pattern with
        | .bgp b => b.length | _ => 0) == 1
#guard (match (rewriteQuery plainQuery).pattern, plainQuery.pattern with
        | .bgp b1, .bgp b2 => b1 == b2
        | _, _ => false) == true

/-! A join of two marker-free BGPs is coalesced into one BGP by the
normalisation pass, then left alone by the rewriter. -/
private def joinQuery : Query :=
  mkQuery (.select .all) (.join (.bgp plainBgp) (.bgp plainBgp))

#guard (match (rewriteQuery joinQuery).pattern with
        | .bgp b => b.length | _ => 0) == 2

/-! ## Axiom audit -/

#print axioms rewriteQuery_preserves
#print axioms evalSelectOwl_is_strip
#print axioms evalAskOwl_no_strip
#print axioms rewriteQuery_noMarker_bgp

end L4Factoidal.OWL.QueryEval
