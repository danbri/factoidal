# bin/rif-runner — vendored W3C RIF Core test runner

Stand-alone CLI that drives the 4 vendored RIF Core test cases under
`third_party/testing/rif/tc/` end-to-end: RIF-XML rule parsing,
`<Import>` companion-graph resolution, forward-chaining saturation,
and the real SPARQL 1.1 evaluator (not a triple-membership shim).

```
rif_runner [-v|--verbose]
```

No arguments needed: the four cases (mf:name from
`third_party/testing/w3c/sparql/sparql11/entailment/manifest.ttl`,
IRIs `:rif01 :rif03 :rif04 :rif06`) are a hardcoded lookup table —
see the module comment in `rif_runner.ml` for why a general manifest
walker is not worth building for exactly four fixtures.

## Pipeline

1. `Parser_RIFXML.parse_rif_program_with_imports` — RIF-XML rules +
   `<Import>` URL list. The internal-subset `<!DOCTYPE ... [ <!ENTITY
   ...> ]>` prolog every vendored `.rif`/`.rdf` fixture opens with is
   stripped and its entities inlined first (`expand_doctype_entities`)
   since `Parser.XML.fst` has no DTD support — pure textual
   preprocessing, same category as `bin/owl-runner`'s
   `catalog_entities` expansion.
2. Merge the manifest `qt:data` `.ttl` with every resolved `<Import>`
   companion graph. `Modeling_Brain_Anatomy`'s import declares
   `<profile>http://www.w3.org/ns/entailment/OWL-Direct</profile>`;
   its rule body needs `rdf:type MaterialAnatomicalEntity` on
   individuals the ontology only asserts via `rdf:type Gyrus` +
   `rdfs:subClassOf`, so that companion graph is closed under
   `RDF_Graph_Executable.owl_rl_closure_with_reflexivity` +
   `Tableau.tableau_materialise` before merging
   (`apply_import_closure`). `RDF_Combination_Blank_Node`'s import
   declares plain `.../entailment/RDF` and is merged as-is.
3. `RIF_Core_Eval.fixpoint` — fuel-bounded forward-chaining
   saturation (fuel 100; `Prims.nat` is `Z.t` in this codegen, so the
   fuel argument must be `Z.of_int 100`, not a bare OCaml `int`).
4. The `.rq` query runs through `SPARQL11_Parser` +
   `OWL_QueryEval.{eval_select_query_owl,eval_ask_query_owl}` +
   `SPARQL11_Algebra` — the same parser/evaluator every other W3C
   runner in this repo uses — compared against the expected `.srx`
   via `Parser_SRX`. Blank nodes in the query pattern (rif06's
   `[] a ex:named`) are rewritten to existential variables via
   `SPARQL11_Algebra.rewrite_query_bnodes_pattern`, mirroring
   `bin/w3c-runner/w3c_runner.ml`'s entailment-regime dispatch.

Deliberately NOT used: `RIF.Core.Tests.run_rif_ask_triple` /
`run_rif_select_rows` / `run_rif_entailment_check`. Those are
simplified ground-triple-membership shims (see
`formal/fstar/RIF.Core.Tests.fst` section 3/4) that never run a real
SELECT projection or ASK boolean evaluation — using them would mean
this runner isn't actually testing the SPARQL query, just checking a
raw triple is present.

## Score

4 pass, 0 fail (out of 4), measured 2026-07-04. See
`docs/claude-rules/scope.md`'s RIF paragraph for the supported-subset
statement (frame/BGP-shaped rule bodies + single `<Import>` — not
general RIF-BLD/RIF-PRD).

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches. This
runner is a consumer of the F\*-extracted RIF engine + SPARQL
evaluator, so it lives under `bin/<consumer>/` per the migration
epic [#200](https://github.com/danbri/factoidal/issues/200) Section D.

## Build

Compiled in an isolated `mktemp` scratch dir (copy the required
extracted `.ml` modules in, compile there, copy the resulting binary
out) — the same isolation `formal/fstar/build-ocaml-serializer.sh`
uses, so this doesn't poison `formal/fstar/ocaml-output/`'s `.cmi`/
`.cmx` artifacts for whatever `build-ocaml.sh` invocation is
in flight. Module list mirrors `bin/owl-runner`'s
`COMMON_MODULES` (`build-ocaml.sh`'s `compile` step).

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/owl-runner/README.md`, `bin/w3c-runner/README.md`
- `formal/fstar/RIF.Core.Eval.fst`, `RIF.Core.Translation.fst`,
  `RIF.Core.Syntax.fst`, `Parser.RIFXML.fst`
