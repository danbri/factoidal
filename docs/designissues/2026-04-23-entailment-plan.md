# Entailment Suite — 2026-04-23 scoping + phased plan

**Status:** 51 pass / 19 fail / 70 total (baseline from
`docs/test-results/latest.csv`, row `sparql,entailment`).
**Previous scoping:** `docs/designissues/2026-04-19-tableau-owl-plan.md`
(23 failures then; 4 tests have since been unlocked).
**Scope of this document:** read-only — no `.fst` edits. Classify the
current 19 failures, confirm the machinery already present, rank the
next actions, and hand subagents bite-sized briefs.

## 1. Delta since 2026-04-19

Tests that moved PASS since the prior scoping:

| Test | Likely unlock mechanism |
|---|---|
| `paper-sparqldl-Q1` | Group E (owl:Thing / owl:Nothing universal axioms) shipped |
| `parent3` | `cls-svf1` (someValuesFrom owl:Thing → class-membership) wired |
| `parent9` | Same as parent3 + owl:Nothing-subclass-of-everything |
| `sparqldl-12` | owl:Thing range / owl:inverseOf chain wired |

Baseline inferred machinery in `RDF.Graph.Executable.fst`:
- `rdfs_closure_with_reflexivity` (line ~1002, RDFS rules 5/7/9/11)
- `owl_rl_closure_with_reflexivity` (line ~1648) — OWL-RL Datalog subset
  including `prp-inv*`, `eq-{ref,sym,trans,rep-s,rep-o,rep-p}`, `prp-ifp`
- `entailment_closure` dispatch (line ~1675): `OWL-RL` / `OWL-Direct` /
  `RDFS` / `RDF` / `D`
- `Tableau.fst` — stage (b) class-expression satisfiability for
  `someValuesFrom`, `allValuesFrom`, `hasValue`, `intersectionOf`,
  `unionOf`, partial `complementOf`. Cardinality AST is present
  (`CE_MinCard` … `CE_ExactQualCard`) but `is_member` does **not**
  yet decide them. `Tableau.tableau_materialise` is called from the
  runner on the `OWL-Direct` branch. No fresh-term skolemisation
  (stage (e)).

Runner dispatch (`w3c_runner.ml` ~line 405): `OWL-RDF-Based → OWL-RL`,
`OWL-Direct → OWL-Direct (OWL-RL + tableau materialise)`, then RDFS,
RDF, D.

## 2. Current 19 failures — per-test table

Each row gives the regime declared in `manifest.ttl`, the observed
failure shape, the assigned bucket, confidence, and an effort tag.

| Test | Regime (manifest) | Failure mode | Bucket | Conf | Effort |
|---|---|---|---|---|---|
| paper-sparqldl-Q2 | `OWL-Direct` | missing 1 row (`John`, `"Johnnie"`) | **A-CE-query** (anon `intersectionOf` in query WHERE) | high | M |
| paper-sparqldl-Q3 | `OWL-Direct` | missing 2 rows | **OWL-DL** (complementOf + skolem bnode generation) | high | XL (skip) |
| parent4 | `OWL-Direct` | missing 3 rows (`Alice`, `Bob`, `Dudley`) | **C-card-min** (`minCardinality 1`, unqualified) | high | S |
| parent5 | `OWL-Direct` | missing 1 row (`Dudley`) | **B-restr-qualified** (`someValuesFrom :Female`) | high | S |
| parent6 | `OWL-Direct` | missing 1 row (`Dudley`) | **C-card-min-qual** (`minQualifiedCardinality 1 onClass :Female`) | high | S |
| parent7 | `OWL-Direct` | missing 1 row (`Dudley`) | **OWL-DL** (`maxQualifiedCardinality 1` — needs tableau) | high | XL (skip) |
| parent8 | `OWL-Direct` | missing 1 row (`Dudley`) | **OWL-DL** (`qualifiedCardinality 1` = min∧max) | high | XL (skip) |
| parent10 | `OWL-Direct` | **over-generates** (7 got / 4 expected) | **wiring-regression** (anon restriction bnode or owl:Thing leaking into subClassOf results) | med | S |
| simple1 | `OWL-Direct` | 0/2 — anon `intersectionOf(A,B)` query | **A-CE-query** | high | M (unlocks 5-7) |
| simple2 | `OWL-Direct` | 0/1 — nested `intersection + Restriction someValuesFrom` | **A-CE-query** nested | high | M |
| simple3 | `OWL-Direct` | 0/1 — `someValuesFrom [intersectionOf(A,B)]` | **A-CE-query** nested | high | M |
| simple4 | `OWL-Direct` | 0/4 — anon `unionOf(B,C)` query | **A-CE-query** (union) | high | S |
| simple5 | `OWL-Direct` | 0/2 — `someValuesFrom [unionOf(A,B)]` | **A-CE-query** nested | high | M |
| simple6 | `OWL-Direct` | 0/3 — `allValuesFrom [unionOf(A,B,C)]` | **A-CE-query** nested | med | M |
| simple7 | `OWL-Direct` | 0/2 — `intersectionOf(A, unionOf(B,C))` | **A-CE-query** nested | high | M |
| simple8 | `OWL-Direct` | 0/1 — chained `someValuesFrom [someValuesFrom :B]` + functional prop | **A-CE-query** nested + chain | med | M |
| sparqldl-11 | `OWL-Direct,OWL-RDF-Based` | missing `:Parent` (got 1/2) | **B-wiring** (`owl:inverseOf` + `rdfs:domain` chain, or owl:Thing) | med | XS |
| rif01 | `RIF` | missing 1 row | **RIF-unsupported** | high | — (reclassify) |
| rif02 | `RIF` | missing 1 row | **RIF-unsupported** | high | — (reclassify) |

### Bucket distribution (19 failures)

| Bucket | Count | Disposition |
|---|---:|---|
| A-CE-query (anonymous class expressions in SPARQL WHERE) | 9 | actionable — biggest lift |
| B-restr-qualified / B-wiring (existing machinery needs a poke) | 2 | actionable — quick |
| C-card-min (+qualified) (tractable via Datalog `cls-minc1`/`cls-svf` + `onClass`) | 3 | actionable — medium |
| OWL-DL (tableau max-cardinality, negation, skolem) | 3 | **out-of-scope v1** |
| wiring-regression (parent10 over-generation) | 1 | must triage — regression since 04-19 |
| RIF-unsupported | 2 | reclassify to SKIP |

So the real actionable pool is **~13 failures**; **3 are true OWL-DL
tableau**, **2 are RIF (not-OWL)**, and **1 is a regression to diagnose
before anything else**.

## 3. Dependency graph

```
[parent10 regression]  ── must be understood first; may require a
                          small filter in the query-rewriting path so
                          that Group A doesn't compound the issue.

[B-wiring (sparqldl-11)]   ── standalone. No deps. XS.

[C-card-min (parent4)]     ── extend cls-* family with cls-minc1.
       └── blocks parent6 (C-min-qual) which reuses the counting skeleton.

[B-restr-qualified (parent5)] ── reuses `cls-svf2` (someValuesFrom
                                  qualified). Landing this + C-min also
                                  lights up parent6.

[A-CE-query simple (simple1, simple4)] ── query-preprocessor pass:
       rewrite `?x a [ owl:intersectionOf ( :A :B ) ]` →
       `?x a :A . ?x a :B .`  (same for unionOf → UNION, someValuesFrom
       → property path).  Pure AST transformation; no closure change.
       └── blocks all nested cases (simple2/3/5/6/7/8, paper-Q2).

[A-CE-query nested (simple2/3/5/6/7/8, paper-Q2)] ── once the simple
       rewrite exists, the rewrite must be recursive (fuel-bounded).
       Unlocks the remaining 7 simple* + paper-Q2.
```

## 4. Phased plan

Each phase is an independent commit.

### Phase 0 — triage parent10 regression  (XS, 1 subagent)

parent10 now returns 7 rows where 4 are expected. The previous
2026-04-19 scoping reports parent10 as **failing for the opposite
reason** (missing rows). Something wired up since April 19 is
over-generating `?C rdfs:subClassOf <anon-restriction-bnode>` triples.
Diagnose first; may be owl:Thing now being returned as a subclass, or
may be that the anon-restriction-bnode is matched twice.

**Pass-count gain:** +1 (parent10).

### Phase 1 — B-wiring: sparqldl-11 missing `:Parent`  (XS)

Manifest expects `{owl:Thing, :Parent}`; we return one of them. Expect
one of: (a) the `:child rdfs:domain :Parent` triple is not reached via
`owl:inverseOf` (currently `:parent owl:inverseOf :child`, and the
schema asserts `:child rdfs:domain :Parent`). Our `prp-inv*` + domain
axioms should produce `:parent rdfs:domain :Parent` if a domain-flip
rule fires. Either the flip isn't firing or the query isn't reading the
closed graph. Probably a 10-line fix in the OWL-RL rule set **once
diagnosed**.

**Pass-count gain:** +1 (sparqldl-11).

### Phase 2 — C-card / B-restr-qualified: parent4/5/6  (S, 1 subagent)

Implement three OWL-RL-ish Datalog rules that together materialise:

- `cls-minc1`: `_:r a owl:Restriction ; owl:onProperty P ;
  owl:minCardinality 1` and `x P _` ⇒ `x a _:r`. Unlocks parent4.
- `cls-svf2`-qualified: `_:r owl:onProperty P ; owl:someValuesFrom C`
  and `x P y`, `y a C` ⇒ `x a _:r`. Unlocks parent5.
- `cls-minc-q1`: `_:r owl:minQualifiedCardinality 1 ; owl:onClass C ;
  owl:onProperty P` and `x P y`, `y a C` ⇒ `x a _:r`. Unlocks parent6.

All three are pure forward rules keyed on an `owl:Restriction` bnode in
the **data/schema**, not the query. They fit into
`owl_rl_closure_step` alongside the existing `cls-svf1`.

**Pass-count gain:** +3 (parent4, parent5, parent6).

### Phase 3 — A-CE-query flat: simple1, simple4, paper-Q2  (M, 1 subagent)

Implement a **query-pre-rewrite** pass that walks the SPARQL algebra
tree, finds triple patterns of the form `?x rdf:type _:c` where `_:c`
(a bnode **in the query**) has `owl:intersectionOf (T1 T2 ...)` or
`owl:unionOf (T1 T2 ...)`, and rewrites them to a conjunction or UNION
respectively. This is a pure AST transformation over `SPARQL11.Algebra`,
no closure change. Recommend a new module
`formal/fstar/OWL.QueryRewrite.fst` so it doesn't bloat
`SPARQL11.Algebra.fst`.

Top-level only (not recursive). Unlocks the flat cases.

**Pass-count gain:** +3 (simple1, simple4, paper-Q2).

### Phase 4 — A-CE-query nested + someValuesFrom/allValuesFrom  (M, 1 subagent)

Extend Phase 3 to be recursive/fuel-bounded and to handle
`someValuesFrom C` → rewrite to a property-path-like
`?x P ?fresh . ?fresh a C .` (with `C` itself recursively rewritten),
and `allValuesFrom C` via a FILTER NOT EXISTS idiom. `hasValue v` →
trivial `?x P v`. Test against simple2, simple3, simple5, simple6,
simple7, simple8.

Simple6 (`allValuesFrom`) is the trickiest; mark it low confidence. If
the FILTER NOT EXISTS shape doesn't line up with the expected result,
defer it without blocking the other five.

**Pass-count gain:** +5 (simple2, 3, 5, 7, 8) nominally; +6 if simple6
works.

### Phase 5 — reclassify rif01, rif02 as SKIP / UNSUPPORTED  (XS)

Teach `w3c_runner.ml` to recognise `ent:RIF` as an unsupported regime
and emit SKIP rather than running the query. Document the decision in
the test-results CSV column `unsupported` instead of `fail`. This is
I/O glue and belongs in the runner + patch layer.

**Pass-count gain:** 0 (still counted as non-fail); cleans the signal.

### Out-of-scope v1

- **paper-sparqldl-Q3**: requires skolem bnode generation **and**
  `owl:complementOf` classical negation. Stage (d)+(e) of the tableau
  plan.
- **parent7 / parent8**: `maxCardinality` / `exactCardinality` with
  qualifications. Requires either UNA + counting-refutation (unsound
  per OWL) or true tableau branching on equality. Stage (c)+(d).

These three tests remain FAIL until the tableau module grows
cardinality + negation reasoning. Do not pretend they are close.

### Projected trajectory

| After phase | pass | fail | unsupp |
|---:|---:|---:|---:|
| baseline | 51 | 19 | 0 |
| +Phase 0 | 52 | 18 | 0 |
| +Phase 1 | 53 | 17 | 0 |
| +Phase 2 | 56 | 14 | 0 |
| +Phase 3 | 59 | 11 | 0 |
| +Phase 4 (optimistic) | 64 | 6 | 0 |
| +Phase 5 | 64 | 4 | 2 |

Residual 4 FAILs at the end: paper-sparqldl-Q3, parent7, parent8,
possibly simple6. All are genuine OWL-DL-tableau territory.

## 5. Subagent briefs

Each is ≤5 lines, paste-ready for a coordinator to hand to a subagent.

### Brief — Phase 0 (parent10 triage)
```
Investigate entailment/parent10 failure (expected 4 rows, got 7). Compare
current inferred graph for third_party/testing/w3c/sparql/sparql11/entailment/parent.ttl
under OWL-Direct regime vs the manifest's expected 3-row result
(parent10.srx). Grep owl_rl_closure_step in RDF.Graph.Executable.fst for
recently-added cls-* rules; also check tableau_materialise in Tableau.fst.
One commit, ≤50 LOC fix. No query changes.
```

### Brief — Phase 1 (sparqldl-11 missing :Parent)
```
entailment/sparqldl-11 expects {owl:Thing, :Parent}, we return 1 row.
Data: third_party/testing/w3c/sparql/sparql11/entailment/parent.ttl (has :parent
owl:inverseOf :child, :child rdfs:domain :Parent). Query:
"select ?C where {:parent rdfs:range ?C}". We need inverseOf-to-domain/
range propagation. Add the Datalog rule (:P owl:inverseOf :Q) ∧
(:Q rdfs:domain :C) ⇒ (:P rdfs:range :C) (and symmetric) into
owl_rl_closure_step in RDF.Graph.Executable.fst. One commit.
```

### Brief — Phase 2 (card-min, restr-qualified)
```
Add three forward rules to owl_rl_closure_step in
formal/fstar/RDF.Graph.Executable.fst:
  cls-minc1: (_:r owl:minCardinality 1 ; owl:onProperty P) ∧ (x P _)
             ⇒ (x a _:r)
  cls-svf2-qual: (_:r owl:onProperty P ; owl:someValuesFrom C) ∧
             (x P y) ∧ (y a C) ⇒ (x a _:r)
  cls-minc-qual1: (_:r owl:minQualifiedCardinality 1 ; owl:onProperty P ;
             owl:onClass C) ∧ (x P y) ∧ (y a C) ⇒ (x a _:r)
Mirror structure of the existing cls-svf1 rule. Unlocks parent4, parent5,
parent6. One commit.
```

### Brief — Phase 3 (CE-query flat rewrite)
```
New module formal/fstar/OWL.QueryRewrite.fst implementing rewrite of
algebra-tree triple patterns `?x rdf:type _:c` (_:c a query bnode) when
_:c has owl:intersectionOf or owl:unionOf bindings in the WHERE. Rewrite
to BGP conjunction or Union respectively. Top-level (non-recursive) in
this commit. Hook into the algebra evaluator in SPARQL11.Algebra.fst via
a new pre-eval pass (do not touch SPARQL11.Algebra.fst algebra types —
other agent active there). Target tests: simple1, simple4, paper-Q2.
```

### Brief — Phase 4 (CE-query nested + restrictions)
```
Extend OWL.QueryRewrite.fst to rewrite recursively (fuel-bounded) and
to handle owl:someValuesFrom (→ property-path style expansion with a
fresh variable), owl:allValuesFrom (→ FILTER NOT EXISTS idiom), and
owl:hasValue (→ direct triple). Target tests: simple2, simple3, simple5,
simple7, simple8. simple6 (allValuesFrom) is low-confidence — if the
FILTER idiom doesn't match expected results, defer and document.
```

### Brief — Phase 5 (RIF reclassify)
```
In formal/fstar/ocaml-output/w3c_runner.ml, when the sd:entailmentRegime
is ent:RIF, emit SKIP (unsupported) rather than running the query. The
semantic logic is zero — just a regime dispatch. Add a patch under
minimal_regrettable_glue_code_each_with_an_open_issue/ (new issue number)
since w3c_runner.ml is regenerated. Also update docs/claude-rules/
current-state.md.
```

## 6. References

- 2026-04-19 tableau scoping: `docs/designissues/2026-04-19-tableau-owl-plan.md`
- RDFS/OWL-RL source: `formal/fstar/RDF.Graph.Executable.fst`
  (`rdfs_closure_with_reflexivity` ~1002, `owl_rl_closure_step` ~1509,
  `entailment_closure` ~1675)
- Tableau: `formal/fstar/Tableau.fst`
  (`owl_tableau_entails` 634, `tableau_materialise` 686-end)
- Runner dispatch: `formal/fstar/ocaml-output/w3c_runner.ml` 355-410,
  630-680
- Manifest: `third_party/testing/w3c/sparql/sparql11/entailment/manifest.ttl`
- Latest scores: `docs/test-results/latest.csv` row `sparql,entailment`
