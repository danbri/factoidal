# Roaring bitmap — F\* sources

Work in progress. This is **Phase A** of the plan in
[`../../../design_issues/roaring_fstar_plan.md`](../../../design_issues/roaring_fstar_plan.md):
just the spec layer + array container + unit tests.

## Files

- `Spec.fst` — abstract `Set u32` denotation and helpers. The "what
  a Roaring bitmap means" layer; no runtime data structure here.
- `Container.Array.fst` — the array container (sorted `u16[]`,
  cardinality ≤ 4096, distinct values). Insert / remove / contains
  / cardinality with correctness lemmas tying them to the Spec
  denotation.
- `Test.fst` — `assert_norm` smoke tests + lemma-shaped property
  tests. Verifying this module IS running the test suite.

## Verifying

These files are not yet wired into the main `formal/fstar/`
Makefile. To verify standalone (assumes the project's standard
F\* opam env):

```
eval $(opam env --switch=fstar)
cd formal/roaring/src
make verify
```

(Makefile lives next to this README; it just shells out to
`fstar.exe` per file.)

## Dependencies

Pure F\* stdlib — `FStar.List.Tot`, `FStar.Math.Lemmas`, `FStar.Mul`.
No `assume val`s in Phase A; first one (`popcount_u64`) lands in
Phase B's bitmap container.

## What this is not

- Not extracted to OCaml yet. (Phase I.)
- Not the bitmap or run container. (Phases B, C.)
- Not set algebra. (Phase F.)
- Not the portable wire format. (Phase H.)
- Not wired into `RDF.CottasStore.PresenceBitmap` or any SPARQL
  evaluator. (Phase J — separate design conversation.)

See the plan doc for the rest.
