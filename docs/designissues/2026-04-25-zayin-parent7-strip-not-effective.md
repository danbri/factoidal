# Zayin — parent7 strip-synthetic-bnodes patch is a no-op (2026-04-25)

## TL;DR

Tav2's commit `4162767` added `strip_synthetic_bnode_vars` to filter
`?_bnode_*` synthetic variables out of `Select_All` projections, predicting
parent7 would flip 311 → 1. **It did not flip.** parent7 still FAILs with
exactly 311 actual rows after the fresh 14:29Z 2026-04-25 build.

The strip function IS being called. But the leaking column is **not**
`?_bnode_*` — it is `?parent` itself. The strip can't help: the user's
visible variable carries the spurious bindings.

Tav2's diagnosis was wrong. The 311 rows are not duplicates that differ
only in synthetic-variable bindings. They are 102 distinct values of
`?parent` cross-multiplied by the rewritten WHERE-clause bnode (≈ 3
matches each ⇒ 311 rows ≈ 102 × 3.05). Stripping the synthetic column
removes the inner column but the outer 102 distinct `?parent` values
remain — and `SELECT *` doesn't carry an implicit DISTINCT, so the row
count is unaffected.

## Direct evidence

Run `./bin/darwin-arm64/w3c_runner -v entailment` (fresh binary,
14:29Z 2026-04-25) and inspect `parent7` (manifest title:
"parent query with (hasChild max 1 Female) restriction"). Captured
in `/tmp/zayin-entail-stderr.log`:

```
EXPECTED (1 rows):
  ?parent=<http://example.org/test#Dudley>
ACTUAL (311 rows):
  ?parent=<http://www.w3.org/2000/01/rdf-schema#domain>
  ?parent=<http://www.w3.org/2000/01/rdf-schema#range>
  ?parent=<http://www.w3.org/2002/07/owl#sameAs>
  ?parent=<http://www.w3.org/2002/07/owl#minCardinality>
  ?parent=<http://www.w3.org/2002/07/owl#minQualifiedCardinality>
  ?parent=<http://www.w3.org/2002/07/owl#onClass>
  ...
  ?parent=_:__rl_maxqc1_<http://example.org/test#hasChild>__on__<http://example.org/test#Female>
  ?parent=_:__rl_exactqc1_<http://example.org/test#hasChild>__on__<http://example.org/test#Female>
  ?parent=_:__rl_minqc1_<http://example.org/test#hasChild>__on__<http://example.org/test#Female>
  ?parent=<http://example.org/test#Dudley>            <-- the legitimate row
```

Stats:

- `grep '?parent=' stderr | wc -l` → 312 (1 expected + 311 actual)
- `grep '?parent=' stderr | sort -u | wc -l` → 102 distinct values
- `grep '_bnode_' stderr | wc -l` → 0 (strip IS working — no synthetic
  columns in the printed output)
- 311 / 102 ≈ 3.05 (each `?parent` matches ~3 inner-bnode candidates)

## Hypothesis tree resolution

| # | Hypothesis | Result |
|---|---|---|
| 1 | `is_synthetic_bnode_var` doesn't match prefix | REJECTED. Both the runner pre-rewrite (`w3c_runner.ml:758`) and the F\* `rewrite_query_bnode_*` (`SPARQL11.Algebra.fst:3501,3506`) emit `"_bnode_" ^ b`, matching Tav2's `string_starts_with v "_bnode_"`. |
| 2 | Strip called after multiplicity baked in | PARTIALLY TRUE BUT NOT CAUSAL. `SELECT *` has no implicit DISTINCT in this query. Strip merely removes the inner column; the outer `?parent` rows are kept verbatim. Stripping after WHERE-eval is fine if ?parent rows are themselves singletons; here they are not. |
| 3 | Entailment path bypasses `eval_select_query` | REJECTED. `OWL_QueryEval.eval_select_query_owl` (`OWL.QueryEval.fst:35`) calls `eval_select_query` directly; the runner dispatches via that wrapper at `w3c_runner.ml:1009`. The strip IS reached. |
| 4 | `Select_All` ADT mismatch | REJECTED. Diagnostic confirms the synthetic columns ARE removed (zero `_bnode_*` lines in printed output). |

**Confirmed root cause:** Misdiagnosis. The 311 rows are not column-multiplied
duplicates collapsible by stripping a hidden column. They are 102 distinct
`?parent` IRIs/bnodes that each really do match the rewritten WHERE
pattern in the closure graph.

## Why ?parent has 102 distinct bindings

The query asks for `?parent rdf:type [a owl:Restriction; owl:onProperty :hasChild;
owl:maxQualifiedCardinality "1"^^xsd:nonNegativeInteger; owl:onClass :Female]`.
After the rewriter the inner `[]` bnode is `?_bnode_X` and we look for any
`?parent` typed as a node that itself satisfies the four inner constraints.

The OWL-RL closure (`owl_rl_closure_with_reflexivity` →
`owl_rule_cls_maxqc1`/`exactqc1`/`minc_qual1`) materialises canonical
"_:__rl_maxqc1_P__on__C" bnodes and then issues memberships
`(x rdf:type _:__rl_maxqc1_P__on__C)` for every non-meta edge `(x p y)`
where `x` has a P-successor typed C. Tav's earlier `is_schema_metapredicate`
gate (commit `ad8d6f7`) suppressed many spurious firings, but the rule still
fires on edges whose **subject** is a vocabulary IRI like `rdfs:domain` /
`xsd:byte` / `_:_anon4` / `_:__rl_*` whenever those subjects appear in any
non-meta-predicate edge in the closure.

Examples of leaked `?parent` values and the likely offending edge:

- `?parent=rdfs:domain` — `(rdfs:domain rdf:type rdf:Property)` axiom +
  some non-meta edge with `rdfs:domain` as subject (likely from
  `prp-spo1` propagation or one of the OWL-RL property-chain rules).
- `?parent=xsd:byte` — datatype-membership axioms emit edges where
  `xsd:byte` is a subject of a non-meta predicate.
- `?parent=_:__rl_maxqc1_<:hasChild>__on__<:Female>` — the rule
  recursively fires on the bnodes it itself emits (cls-maxqc1 fixpoint
  iteration sees its own canonicals as data).
- `?parent=_:_anon4` — anonymous subjects from
  `equivalentClass [...]` / `intersectionOf` etc. in `parent.ttl`.

The structural fix is to also gate `cls-maxqc1`/`-exactqc1`/`-minc_qual1`/
`-svf2-qualified` on the **subject** of the iterated edge being a candidate
*individual* (not a vocabulary IRI, not a class, not one of the canonical
restriction bnodes the rule itself emits). Or, less invasively, exclude
RDFS-axiomatic predicates whose subjects are property/datatype IRIs that
should not become individuals under OWL-RL semantics.

## Recommended fix

This is **structural**, not a one-liner. Tav2's strip patch should be
**reverted** or kept as defensive hygiene with the understanding that it
does not address parent7. Options for the real fix (in F\*, per rule #10):

1. **Subject-side guard on the maxqc1/exactqc1/minc-qual1/svf2 rules.**
   In `owl_rule_cls_maxqc1` (`RDF.Graph.Executable.fst:2487`), in addition
   to `is_schema_metapredicate edge.p`, also skip when:
   - `edge.s = S_IRI i` and `i` is in `is_schema_metapredicate` (vocab IRI
     used as a subject), OR
   - `edge.s = S_BNode b` and `b` starts with `__rl_` (canonical bnode
     emitted by the rule itself — break the self-feedback loop).

2. **Stratify the closure.** Run the cls-* qualified-cardinality rules
   only after a fixed point of the schema-vocabulary axioms, and never
   re-run them on the canonicals they emit. The current implementation
   re-iterates them in `owl_rl_closure` which feeds the canonicals back
   in.

3. **Fix at the closure level not the projection level.** The projection
   layer (Tav2's strip) is the wrong place — `SELECT *` is faithful to
   what's in the solution sequence. The leak is in the closure graph.

Estimated cost: ~30-line change in `owl_rule_cls_maxqc1` + sibling rules.
F\* should verify cleanly because the change is a stricter precondition
on existing fold accumulators. No new `assume val`, no patch.

## Confidence

**HIGH (~95%).** The empirical evidence is unambiguous: zero
`?_bnode_*` columns appear in the actual output (the strip IS working),
and the leaking column is `?parent` carrying 102 distinct vocabulary
IRIs, anonymous bnodes, and `__rl_*` canonicals. No amount of projection-
layer filtering can fix this; it must be addressed in the closure rules.
The remaining 5% uncertainty is whether one of the OWL-Direct dispatch
codepaths I haven't traced contributes (the runner handles `OWL-Direct` =
`OWL-RL` per `entailment_closure` so unlikely).

## What to tell the user

> Tav2's strip patch is a verified no-op for parent7. The strip IS being
> called and IS removing the synthetic column (zero `_bnode_*` lines in
> output), but the leaking column is `?parent` itself with 102 distinct
> bindings. Real fix lives in `RDF.Graph.Executable.fst:2487` and
> siblings (`cls-exactqc1`, `cls-minc-qual1`, `cls-svf2-qualified`):
> add a subject-side guard rejecting vocabulary IRIs and self-emitted
> `__rl_*` canonicals. Tav2's projection-layer patch should be considered
> defensive but irrelevant to this test; consider reverting or keeping
> with a corrected commit message.

## References

- `formal/fstar/SPARQL11.Algebra.fst:3542-3549` — strip helpers (Tav2)
- `formal/fstar/SPARQL11.Algebra.fst:3668,3705` — strip call sites
- `formal/fstar/SPARQL11.Algebra.fst:3499-3530` — `rewrite_query_bnode_*`
  and `rewrite_query_bnodes_pattern` (prefix `_bnode_`)
- `formal/fstar/ocaml-output/w3c_runner.ml:751-784` — runner-side
  pre-rewrite (also `_bnode_` prefix; entailment regimes)
- `formal/fstar/ocaml-output/w3c_runner.ml:1009` — dispatch via
  `OWL_QueryEval.eval_select_query_owl`
- `formal/fstar/OWL.QueryEval.fst:35-37` — wrapper that calls
  `rewrite_query` then `eval_select_query`
- `formal/fstar/RDF.Graph.Executable.fst:2487-2537` — `cls-maxqc1` rule
- `formal/fstar/RDF.Graph.Executable.fst:2043-2068` —
  `is_schema_metapredicate` (predicate-side gate; subject-side gate
  missing)
- `docs/designissues/2026-04-25-tav-parent7-overcount-diagnosis.md` —
  earlier (954 → 311) diagnosis; the 311 residual is the unsolved tail
  this doc explains.
- `docs/designissues/2026-04-25-tav2-parent7-finish.md` — Tav2's
  superseded diagnosis (claimed 311 was synthetic-column inflation).
