# OWL-DL tableau — paper-Q3 complementOf-via-disjointWith bridge

**Agent Mem — 2026-04-25.** Branch `claude/main`, parent HEAD `554e134`.
Lamed's Phase 2 piece. Lamed's commit: `92a9ee1`. Plan doc:
`docs/designissues/2026-04-25-owl-dl-tableau-paper-q3-parent-min-max-plan.md`.

## Mission

Land the ~25-line, sound, local fix to `Tableau.fst` `is_member`
`CE_ComplementOf` case so that paper-sparqldl-Q3 picks up its missing 2-row
expected answer once Phase 1 (existential witness, Lamed) is in place.

## What Q3 needs (from Lamed's plan + the SRX file)

```
?x ex:hasPublication _:b0 .
_:b0 rdf:type [ owl:onProperty ex:publishedAt ;
                rdf:type owl:Restriction ;
                owl:someValuesFrom [ rdf:type owl:Class ;
                                     owl:complementOf ex:Workshop ] ]
```

Data:
- `:paper1 a :ConferencePaper`,
  `:ConferencePaper rdfs:subClassOf [onProperty :publishedAt; someValuesFrom :Conference]`
- `:Conference owl:disjointWith :Workshop`
- `:John :hasPublication :paper1`, `:person1 :hasPublication :paper1`

Expected: `?x ∈ {:John, :person1}`.

DL chain (after Lamed Phase 1):
- existential witness intro adds `:paper1 :publishedAt _:bw` and `_:bw a :Conference`.
- now we need `_:bw a (¬:Workshop)`. **This is the bridge.**
- That fills `someValuesFrom (¬:Workshop)` for `:paper1`, hence Q3 binds `:John`/`:person1`.

## Bridge rule (sound, monotonic, ≤ 25 LoC)

In `is_member` `CE_ComplementOf c` branch, *before* the existing
double-negation flip, when `c = CE_Named c_iri`:

> Search the closed graph for any class `d_iri` declared disjoint with `c_iri`
> (either direction — `owl:disjointWith` is symmetric per OWL 2 semantics)
> such that `has_type g i d_iri`. If found, return `Some true`.

One direction only — never `Some false`. Sound because:
> `(C disjointWith D) ∧ (i a C)` is a model-theoretic guarantee that `i ∉ D`,
> i.e. `i a (¬D)`.

If no disjoint witness is found, fall through to existing flip logic
(`is_member g i c (n - 1)` then `Some (not b)`).

## Implementation outline

In `Tableau.fst`:

1. Add OWL vocab constant `owl_disjointWith` near the other owl_* defs.
2. Add a helper `has_disjoint_witness : g -> i -> c_iri -> bool` that:
   - Collects all triples `(c_iri owl:disjointWith ?d)` *and*
     `(?d owl:disjointWith c_iri)` (both forward + reverse, symmetric).
   - For each such `d_iri`, checks `has_type g i d_iri`.
   - Returns true on first hit.
3. Edit `CE_ComplementOf c` branch in `is_member` to:
   ```
   | CE_ComplementOf c ->
     (match c with
      | CE_Named c_iri when has_disjoint_witness g i c_iri -> Some true
      | _ ->
        (match is_member g i c (n - 1) with
         | Some b -> Some (not b)
         | None   -> None))
   ```

Estimated: 5 lines vocab, 12-15 lines helper, 3-4 lines edit ≈ 22-25 LoC.

## Verification

Run `make verify` (or direct fstar) on `Tableau.fst`. No `--lax`. Termination
is fuel-free in the helper (single linear scan over `g`). The mutually
recursive measure `decreases %[fuel; 0]` is preserved because the helper is
non-recursive and the `CE_Named c_iri when ...` guard does not recurse —
the existing fall-through still passes `n - 1`.

## Hard limits respected

- ≤ 50 LoC F\* edit (target ~25).
- No edits to `RDF.Graph.Executable.fst`, `OWL.QueryRewrite.fst`,
  `SPARQL11.Algebra.fst`.
- No extract / compile (Yod3 has the F\* lock on Parquet.Footer.fst).
- No 3030 endpoint impact.

## Expected outcome

Per Lamed: paper-sparqldl-Q3 → +1 PASS once Yod3 finishes (i.e. once the
extracted/compiled w3c_runner is rebuilt with both Phase 1 witness intro and
this Phase 2 bridge in place). Without Phase 1 witness intro, `_:bw` doesn't
exist in the graph, so the bridge alone is insufficient — but the bridge
itself is independently sound and is a building block several other tests
need.

## Commit

`tableau: complementOf via disjointWith bridge (paper-Q3)`

## Files touched

- `docs/designissues/2026-04-25-owl-q3-complementof-bridge-plan.md` (this file).
- `formal/fstar/Tableau.fst` (Phase 2 bridge).
