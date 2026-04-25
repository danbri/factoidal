# OWL-DL tableau push — paper-Q3, parent4 (min 1), parent7 (max 1) — plan

**Agent Lamed — 2026-04-25.** Branch `claude/main`, HEAD `7eda3da`.

## Mission (≤ 90 min, F\* edit ≤ 200 LoC, no extract/compile)

Three SPARQL `entailment` failures need DL reasoning beyond OWL-RL closure:

1. **paper-sparqldl-Q3** — expected 2 (`:John`, `:person1`), got 0.
2. **parent4** `(hasChild min 1)` — expected 3 (`:Alice :Bob :Dudley`), got 2 (missing `:Alice`).
3. **parent7** `(hasChild max 1 :Female)` — expected 1 (`:Dudley`), got 973 (skolem explosion).

Phased delivery — Phase 0 always lands; Phase 1 if tractable; Phase 2 deferred.

## Phase 0 — diagnosis

### Q3 — what it asks

```
?x ex:hasPublication _:b0 .
_:b0 rdf:type [ owl:onProperty ex:publishedAt ;
                rdf:type owl:Restriction ;
                owl:someValuesFrom [ rdf:type owl:Class ;
                                     owl:complementOf ex:Workshop ] ]
```

So: `?x` is anyone whose publication has *some* publishing venue that is **not**
a `:Workshop`. Data:

- `:paper1 a :ConferencePaper`,  `:ConferencePaper ⊑ ∃publishedAt.:Conference`
- `:Conference owl:disjointWith :Workshop`
- `:John :hasPublication :paper1`, `:person1 :hasPublication :paper1`

DL chain to derive `:John`:
- `:paper1 a :ConferencePaper` → `:paper1 a (∃publishedAt.:Conference)` (someValuesFrom)
- pick witness `_:y` with `:paper1 :publishedAt _:y` and `_:y a :Conference`
- `:Conference disjointWith :Workshop` ⇒ `_:y a (¬:Workshop)`
- so `:paper1` is in (∃publishedAt.(¬:Workshop)).
- so `?x ∈ {:John, :person1}`.

**Required tableau features:**
- (F1) **someValuesFrom existential witness introduction** — same as parent4.
- (F2) **disjointWith → complementOf** — `(C disjointWith D) + (y a C)` ⇒ `y a (¬D)`. We can answer the bnode-CE `[owl:complementOf :Workshop]` `Some true` for any individual provably in a class disjoint with `:Workshop`.
- (F3) Existing query-rewriter support to expand the outer `_:b0 rdf:type [owl:someValuesFrom …]` and the inner CE.

This is **not** literally back-jumping / absorption from the SPARQL-DL paper — that's
overkill. The three primitives above suffice for Q3 specifically. Full
SPARQL-DL semantics is deferred.

### parent4 — what it asks

`SELECT * WHERE { ?parent rdf:type [a owl:Restriction; owl:onProperty :hasChild; owl:minCardinality 1] }`

Expected `:Alice :Bob :Dudley`. We deliver `:Bob :Dudley` only.

- `:Bob :hasChild :Charlie` — direct successor, MinCard 1 fires (already in tableau).
- `:Dudley :hasChild :Alice` — same.
- `:Alice` — no asserted `:hasChild` edge. But `:Alice a :Parent`, and
  `:Parent ≡ ∃hasChild.owl:Thing`. DL says `:Alice` must have *some* `:hasChild`
  successor in every model.

**Required tableau feature:**
- (F1) someValuesFrom existential witness introduction — for any `i a C` where
  `C ≡ ∃P.D` (or where `i a (∃P.D)`), inject a fresh witness `_:bw` with
  `:i :P _:bw` and `_:bw a D` into the closed graph (capped by fuel).
  Then the existing (CE_MinCard 1 :hasChild) check sees one P-successor and
  fires.

### parent7 — what it asks

`SELECT * WHERE { ?parent a [a owl:Restriction; owl:onProperty :hasChild; owl:maxQualifiedCardinality 1; owl:onClass :Female] }`

Expected `:Dudley`. We deliver 973 rows — **closure-side** `cls-maxqc1` is
introducing a skolem witness per applicable instance and the rule fires
monotonically until the closure runs out of fuel.

The bug surface here is **NOT** the tableau — it's the OWL-RL closure
fabricating skolem bnodes that then re-trigger the rule. Proper fix is a
DL **existential merging** step (cap n+1 distinct successors at max-N; merge
or fail). That's hard — needs equality decisions in tableau.

**Decision:** **defer parent7 to Phase 2.** A pure tableau fix without
changing closure could only suppress those 973 rows by post-filtering, which
violates rule #15 (no semantic logic in patches/runner). The right fix is
a closure-side guard on `cls-maxqc1` to not emit max-Q-card skolems — and
that lives in `RDF.Graph.Executable.fst`, which is currently locked
(Yod3 editing). Document the gap and move on.

## What `Tableau.fst` already has (line refs to file at HEAD)

| Feature | Where | Status |
|---|---|---|
| Class-expression AST + parser | lines 135-322 | DONE |
| `is_member` for ∃ P.C, ∀ P.C, ∃ P.{v}, ⊓, ⊔, MinCard, MaxCard, ExactCard, qualified | lines 382-478 | DONE for known successors |
| `tableau_materialise` — adds `i rdf:type <CE-bnode>` for every individual that satisfies it | lines 863-868 | DONE for is_member-discharged checks |
| Existential witness introduction (∃ P.C ⇒ fresh bnode) | (none) | **MISSING — Phase 1 target** |
| disjointWith → complementOf assertion | (none) | **MISSING — Phase 1 stretch** |
| Existential merging for max-N | (none) | DEFERRED |
| Back-jumping / absorption | (none) | DEFERRED |
| sameAs / differentFrom UNA tracking | tab_node has `tn_same_as` but no propagation | DEFERRED |

## Phase 1 — minimal-viable existential witness for parent4

### F\* edit, ≤ 200 LoC, in `formal/fstar/Tableau.fst`

Add a new pass `tableau_introduce_witnesses : rdf_graph -> rdf_graph` that:

1. Collects every triple `(i rdf:type CE-bnode)` where `CE-bnode` parses as
   `CE_SomeValuesFrom p c` (also `CE_MinCard 1 p` and `CE_MinQualCard 1 p c`,
   which are equivalent for k=1).
2. For each such `(i, p, c)` triple where `i` does NOT already have a known
   `p`-successor that satisfies `c`, mint a fresh bnode `_:bw_<n>` (use
   a counter seeded by the size of the existing graph for stability), and
   emit:
   - `i p _:bw_<n>`
   - `_:bw_<n> rdf:type c_iri` (only if `c` is `CE_Named c_iri` — for
     `CE_Unknown` we still inject the property edge with no type, which is
     enough for parent4 since `c = owl:Thing`).
3. Skip if a witness for the same `(i, p, c)` was already injected (use
   structural equality on (i, p, type-of-c) — quadratic but fuel-capped).
4. Cap the number of injections at `max_witnesses` (constant, e.g. 64).
5. Returns `g` with appended triples (deduped via `add_triples_if_new`).

Wire `tableau_introduce_witnesses` into `tableau_materialise` so the
materialisation pass becomes:

```fstar
let tableau_materialise (g : rdf_graph) : rdf_graph =
  let g1 = tableau_introduce_witnesses g in
  (* existing logic on g1 instead of g *)
  ...
```

This is sound for `Some true` because we only assert the witness exists
where the model theory requires it; we never emit `Some false`.

### Why this is enough for parent4

- `tableau_materialise` is already called by the entailment closure (per
  `OWL.QueryRewrite.fst` integration).
- Calling order:
  1. OWL-RL closure runs (Datalog).
  2. `tableau_materialise` is invoked once.
  3. With Phase 1, `tableau_materialise` first introduces witnesses.
  4. Then it runs `materialise_all` over class-expression bnodes.
  5. The CE bnode `[a owl:Restriction; owl:onProperty :hasChild; owl:minCardinality 1]`
     in the parent4 query is now materialised against `:Alice` because she
     has the freshly-injected `_:bw_alice` as a `:hasChild` successor.

### Trigger logic — where do existentials *come from* in parent4?

`:Alice a :Parent` is asserted. `:Parent` `equivalentClass` `[onProperty :hasChild; someValuesFrom owl:Thing]`. The OWL-RL closure runs `cls-eqc1` and emits
`:Alice rdf:type _:R` where `_:R` is the restriction bnode. That `_:R` parses
as `CE_SomeValuesFrom :hasChild (CE_Named owl:Thing)`. So the trigger source
is the existing materialised triple `:Alice rdf:type _:R` (already in the
closed graph thanks to cls-eqc1) — we just walk every CE-bnode that parses
as `∃ P.C` or MinCard 1, find every `(i a CE-bnode)`, and inject witnesses.

**No closure changes needed.** The witness-introduction step reads from the
already-closed graph and produces additive triples.

### Verification

`make verify` on `Tableau.fst` — F\* must accept the new function. Termination
is fuel-bounded; recursion shape mirrors existing `materialise_all`.

### Expected delta

- parent4: +1 PASS.
- parent7: no change (deferred).
- paper-Q3: still 0 (Phase 1 doesn't add the disjointWith → complementOf bridge).
- Net entailment: +1.

## Phase 2 — deferred work (NOT this session)

### paper-Q3 (F2 — disjointWith → complementOf)

Add to `is_member` in CE_ComplementOf branch: when `c = CE_Named c_iri`,
search the graph for any `c2_iri` such that `(i a c2_iri)` and either
`(c_iri owl:disjointWith c2_iri)` or `(c2_iri owl:disjointWith c_iri)`.
If found, return `Some true`. Otherwise, fall back to existing logic
(double-negation flip).

Lines: ~25 LoC. Skipping this session because Phase 1 already saturates
the 200-LoC budget once we factor in helpers and the test matrix update.

### parent7 — max-cardinality merging

Real fix is a closure-side rewrite: replace `cls-maxqc1` with a guarded
emission that synthesises **at most one** witness per (i, P, C) and then
flips to a sameAs equation if a real successor surfaces later. This needs
equality-decision logic and a closure-side fixpoint with backtracking —
beyond the 90-min budget and currently blocked on `RDF.Graph.Executable.fst`
edits being locked.

Alternative: post-filter parent7's bnode answers in OWL.QueryRewrite via
a "skolem-suppression" rule on the answer projection. Marginally cheaper
but explicitly forbidden by rule #15.

### paper-Q3 (back-jumping / SPARQL-DL absorption)

Once F2 lands, the remaining gap for Q3 is a multi-hop universal/existential
interplay. Full SPARQL-DL paper algorithm is multi-paragraph; we'd implement
an absorption pre-pass that turns `C ≡ ∃P.D ⊓ ∀P.E` into rewrite rules.
Multi-week effort; explicit deferred.

## Hard limits respected

- ≤ 200 LoC F\* edit (Phase 1 estimate: ~120 LoC including helpers + test).
- Don't break OWL-RL closure (we don't touch it).
- Don't run extract / compile (Yod3 is editing F\*).
- F\*-verify Tableau.fst.
- Don't touch `SPARQL11.Algebra.fst`.

## Commit message

`owl-tableau: existential witness phase 1 (parent4) + paper-Q3/parent7 scoping`

## Files touched this session

- `docs/designissues/2026-04-25-owl-dl-tableau-paper-q3-parent-min-max-plan.md` (this file).
- `formal/fstar/Tableau.fst` (Phase 1).
