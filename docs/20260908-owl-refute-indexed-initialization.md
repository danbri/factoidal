# OWL refuter indexed initialization

Date: 2026-09-08

## Change

`Refute.unsatNamedClasses` remains the list-store specification. The new
`unsatNamedClassesIndexed` implementation evaluates the same definition over
`Store.ofIndex (Index.ofGraph g)`. The theorem
`unsatNamedClassesIndexed_eq` uses `Store.ofIndex_eq (Index.Wf.ofGraph g)` to
prove identical list results and order. The `@[csimp]` theorem
`unsatNamedClasses_eq_indexed` selects the indexed implementation for compiled
calls to the public specification.

`initState` now constructs one indexed store and reuses it for the state,
anonymous datatype ranges, and initial `rdf:type` expression parsing. The
per-expression theorem `parseNnfWith_indexed_eq` proves equality to the prior
`Store.ofGraph` reader. There is no new semantic cap or output reordering.

## Measurement

The input was `third_party/qudt/QUDT-all-in-one-OWL.ttl`. The measured RL
closure has 638,420 triples. The earlier list-store
`unsatNamedClasses` phase took 60.312 seconds. A native executable compiled
after this change measured:

```text
phase=public-unsat-named ms=1369
phase=direct-indexed-unsat-named ms=1367
equal=true count=0
```

This confirms that `@[csimp]` changed the compiled public call. The phase is
44 times faster on this input and meets the under-10-second target.

The same phase on the schema.org closure took 99 ms in the direct indexed
initialization measurement. Other measured schema.org initialization phases
were closure 832 ms, index 72 ms, type scan 1 ms, type-expression parsing
under 1 ms, and label insertion 1.460 seconds.

QUDT initialization now proceeds past this phase, but initial label insertion
remains a separate bottleneck: it did not finish within approximately 90
seconds in the phase harness. A public schema.org consistency run in this
isolated pre-search-optimization tree was stopped after 111.91 seconds. These
stopped runs are not performance passes and are not used for the speedup
claim above.

## Checks and limits

The focused refuter build, OWL DL type-inconsistency catalog, and full Lake
build were run after removing the temporary measurement executable. Axiom
reports were checked for `unsatNamedClassesIndexed_eq`,
`unsatNamedClasses_eq_indexed`, and `parseNnfWith_indexed_eq`.

The Lean tail-recursion scanner reports `finiteRegexLanguage` from the prior
datatype patch as an input-length candidate because its classifier scans the
full signature, including the return type `Option (List (List Nat))`. The
function actually recurses over `Re` tree depth. Its production caller parses
pattern text only after a 256-codepoint limit. This is a scanner false
positive; no allow-list entry was added. Regex tree-depth recursion remains
an explicit limit of that helper.

No `sorry`, user `axiom`, `native_decide`, `unsafe`, `@[implemented_by]`, new
`partial`, or trust option was added. This substitution does not add a
graph-refuter soundness bridge; that existing gap remains tracked by issue
586.
