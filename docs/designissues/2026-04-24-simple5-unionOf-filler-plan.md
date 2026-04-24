# simple5: unionOf filler in someValuesFrom — rewriter plan

**Date:** 2026-04-24 · **Agent:** M · **Target:** SPARQL entailment test `simple5`.

The SPARQL query `simple5.rq` asks for `?x` such that `?x` is an instance of
`∃:p.(:A ⊔ :B)`. Data: `:a :p :b` (`:b a :B`) and `:c :p :d` (`:d a :A, :B`).
Expected: `{:a, :c}`.

Plan: extend `formal/fstar/OWL.QueryRewrite.fst` so that when the rewriter
sees `someValuesFrom` whose filler is a `unionOf(C1, …, Cn)` CE, it emits

```
{ ?x :p ?g . ?g a C1 } UNION … UNION { ?x :p ?g . ?g a Cn }
```

instead of the existing "filler must be a named class" shortcut. `?g` is a
fresh per-CE variable (reuse the module's gensym helper). Keep the existing
bookkeeping-triple stripping for the filler bnode and its rdf:first/rdf:rest
chain — it already handles the nested bnode. The closure in
`RDF.Graph.Executable.fst` is **not** touched; OWL 2 disjunction lives in the
rewriter per the disjunction-in-rewriter doctrine (#feedback). F* verify with
`make verify`; do not extract/compile (main thread is doing that).
