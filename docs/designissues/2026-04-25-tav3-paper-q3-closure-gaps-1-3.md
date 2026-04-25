# 2026-04-25 — Agent Tav3: paper-Q3 closure-side gaps 1 + 3

## Mission

Close gaps 1 and 3 from Shin's diagnosis (`docs/designissues/2026-04-25-shin-paper-q3-followup.md`) on the closure side. Both edits live in `formal/fstar/RDF.Graph.Executable.fst`.

## Inputs digested

* Shin's diagnosis: paper-Q3 demands a 4-step entailment chain. Mem's bridge in `Tableau.fst:475-494` covers step 2 (named-class disjointness witness) iff a witness already exists. The witness does not exist in the data — it has to be synthesised.
* Nun2 commit `ea7f286` (rewriter side, gap 2) lives on `claude/100-phase2.5-backend-wiring`. It rewrites `(complementOf C)` BGP into:
  ```
  { ?x rdf:type ?_co_<k> . ?_co_<k> owl:disjointWith C }
  UNION
  { ?x rdf:type ?_co_<k> . C owl:disjointWith ?_co_<k> }
  ```
  (i.e. either direction of `disjointWith` matches.)
* Mem's bridge (`Tableau.fst:368-403`) checks `find_objects g (S_IRI c_iri) owl_disjointWith` AND `find_subjects g owl_disjointWith (T_IRI c_iri)`, so it already accepts either direction at the F* call site. No change needed there.

## Data shape (verified against `paper-sparqldl-data.ttl`)

```
:Conference owl:disjointWith :Workshop                             # only forward
:ConferencePaper rdfs:subClassOf [a owl:Restriction ;
                                  owl:onProperty :publishedAt ;
                                  owl:someValuesFrom :Conference]
:John  :hasPublication :paper1                                      # ?x = :John
:person1 :hasPublication :paper1                                    # ?x = :person1
:paper1 a :ConferencePaper
```

## Gap 1 plan — existential witness synthesis

We need: `:paper1 :publishedAt _:w` AND `_:w a :Conference`.

Trigger pattern after RDFS/OWL closure has fired:
* `(restr_subj rdf:type owl:Restriction)` — `restr_subj` is the bnode `_:r`
* `(restr_subj owl:onProperty P)` — P is `:publishedAt`, an IRI
* `(restr_subj owl:someValuesFrom C)` — C is `:Conference`, an IRI
* `(restr_subj rdfs:subClassOf? <somewhere>)` is irrelevant — what matters is finding individuals who *belong* to that restriction's superclass chain.
* For each `(C' rdfs:subClassOf restr_subj)` (closure already runs both directions: `cls-eqc1/2` plus `rdfs11`), find every `(x rdf:type C')` and synthesise.

Note: `rdfs_rule_subClassOf` in `RDF.Graph.Executable.fst:1055` only fires when the `rdf:type` object is `T_IRI` (line 1059), so it won't materialise `(:paper1 rdf:type _:r)` automatically. That's fine — we synthesise from the `rdfs:subClassOf` chain directly, not from a materialised type triple.

**Algorithm:**

```
For each triple (r owl:someValuesFrom C) where r ∈ subject:
  If (r owl:onProperty P) with P ∈ wf_iri AND C ∈ wf_iri:
    For each subject_iri in subClassOf-chain ancestors-of(r):
      For each x with (x rdf:type subject_iri):
        Let w = canonical_svf2_witness_bnode(P, C, x)  // deterministic
        Emit:
          (x P (T_BNode w))
          ((S_BNode w) rdf:type (T_IRI C))
```

The "subClassOf-chain ancestors of r" set: `find_subjects g rdfs_subClassOf (subject_to_term r)` — every `C'` such that `C' rdfs:subClassOf r`.

`find_subjects` returns `list subject`; we constrain to `S_IRI _` so the type-membership lookup `find_subjects g rdf_type (T_IRI subject_iri)` makes sense. (Restriction-bnode-typed individuals are ALSO emitted candidates, but the only path to producing such an `x rdf:type _:r` triple is through OWL-side rules; for paper-Q3 we only need the IRI subClass case, so handling the bnode-CE case is out of scope.)

**Bnode pollution naming convention.** The existing `_:__rl_*` skolems already prefix all canonical bnodes. I'll use:

```
_:__rl_svf2w__on__<P>__filler__<C>__from__<x>
```

where `<x>` is the IRI of the originating individual. This makes the synthesised witness DETERMINISTIC (same input → same bnode id; idempotent, fixpoint converges in one extra closure iteration). Each `(P,C,x)` triple gets its own witness; we do NOT collapse across individuals (would be unsound — different individuals could have different witnesses). The `__rl_` prefix marks these as closure-synthesised and matches the existing convention — search for `__rl_` in the codebase confirms no other code parses the name back, so this is purely informational.

**Soundness sketch.** The OWL-Direct semantics of `(x rdf:type [P some C])` requires that there exists `w` with `(x P w) ∧ (w rdf:type C)`. Synthesising a fresh existential witness `_:w` is the standard skolemisation of that existential. Under OWL 2 RL (Datalog), this rule is normally avoided because RL deliberately omits existential introduction; we add it here as a SOUND extension because:

1. The skolem is deterministic in `(P, C, x)` so re-running closure converges.
2. We never collapse two distinct individuals' witnesses (no spurious sameAs).
3. The synthesised triple cannot make any previously-true closure conclusion false (monotonic).
4. The skolem name uses bnode syntax, not IRI — so no IRI-vocabulary pollution.

**Risk: bnode pollution into other queries.** A query `SELECT ?w WHERE { ?p :publishedAt ?w }` will pick up the synthesised witnesses. This matches OWL-Direct semantics (the witness IS provably a `:publishedAt` value). For closed-world / non-OWL queries, the closure pipeline is gated externally, so this is the correct behaviour for the entailment regime.

**Loop budget.** ≤ 60 LoC for the rule body + the witness-bnode helper.

## Gap 3 plan — disjointWith propagation

Three SOUND closure additions:

1. **Symmetry of `owl:disjointWith`.** The OWL spec says disjointWith is symmetric. For each `(C owl:disjointWith D)` emit `(D owl:disjointWith C)`.
2. **`complementOf` ⇒ `disjointWith` (both directions).** For each `(C owl:complementOf D)` emit `(C owl:disjointWith D)` AND `(D owl:disjointWith C)`. complementOf implies disjointWith (a class and its complement share no instances by definition).
3. **(Skipped intentionally)** Do NOT emit `(C owl:complementOf D)` from `(C owl:disjointWith D)` — disjointWith is the WEAKER relation (no overlap) while complementOf is the STRONGER relation (D is exactly the complement, so their union is owl:Thing). Emitting it would be unsound (parent4-style regression).

Mem's `Tableau.fst` bridge is symmetric in its own helper search (`any_disjoint_witness_in` on `find_objects` forward + `any_disjoint_witness_sym` on `find_subjects` reverse), so by step (1) above we make Mem's bridge fire for either direction equally. Nun2's rewriter emits BOTH `?d owl:disjointWith C` AND `C owl:disjointWith ?d` UNION branches, so step (1) makes the closure-materialised forms also work either way.

**Loop budget.** ≤ 30 LoC.

## Pipeline wiring

Both rules go into `owl_rl_closure_step` (line 2949).

* `owl_rule_disjoint_with_propagation` — early, before the restriction-membership rules. Rationale: disjointness is schema-level; firing it before svf2-existential-witness lets the witness's downstream `(w a C)` be picked up by Mem's bridge in the SAME closure iteration. Order: place it after `owl_rule_inverse_of` (line 2957) where the symmetric / equivalence-style rules live.
* `owl_rule_svf2_existential_witness` — between `owl_rule_minc1_bridge` (g13) and `owl_rule_cls_svf2_qualified` (g14). Order rationale: minc1-bridge emits the `owl:minCardinality "1"` triples on Restrictions; svf2-existential-witness emits the witness edges; cls-svf2-qualified runs after so the FORWARD direction (`(x P w) ∧ (w a C) → (x rdf:type [SVF P C])`) closes the loop on the synthesised witness.

## Acceptance plan

1. F* `make verify` clean (touched module: `RDF.Graph.Executable.fst`).
2. After Yod4 unblocks the build (patch 65 fix) + Nun2's branch merges back to main + sweep:
   * paper-sparqldl-Q3: 0 → 2 rows (`:John`, `:person1`).
   * No regression in simple1..simple8, sparqldl-*, parent4, parent7.
3. Bnode pollution guard. The synthesised `_:__rl_svf2w_*` bnodes will appear as objects in `?w` projections of certain rare query shapes (e.g. `SELECT ?w WHERE { ?p :publishedAt ?w }`). For paper-Q3 the projection variable is `?x` (bound by `:hasPublication`), not the witness, so no leakage. simple1-8 / sparqldl-* / parent* don't issue `?w :publishedAt` projections that would expose the synthesised witnesses. If any test regresses due to extra rows, the fix is to extend the existing skolem-stripping pattern (does not exist yet — would be added if needed; no test requires it today).

## Branch hygiene

* Stay on `claude/main`. Do NOT push commits to Nun2's branch (Kaph2's branch / `claude/100-phase2.5-backend-wiring`).
* Do NOT run `./build-ocaml.sh extract` — Yod4 is fixing the build-blocker; we coordinate by NOT extracting.
* `make verify` only on `RDF.Graph.Executable.fst`.

## Status log

* 2026-04-25 start: scratch doc written. Reading targets located:
  - `owl_rl_closure_step` line 2949
  - `owl_rule_cls_svf2_qualified` line 2132 (forward direction, our model)
  - `owl_rule_minc1_bridge` line 2102 (template for inserting before svf2)
  - `owl_disjointWith_iri` line 2019, `owl_complementOf_iri` line 2015
  - `owl_someValuesFrom_iri` line 1960, `owl_onProperty_iri` line 1956
  - Mem's bridge: `Tableau.fst:368-403`
* Next: write F* code in one edit, verify, commit.
