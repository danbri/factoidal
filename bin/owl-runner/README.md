# bin/owl-runner — W3C OWL 2 test runner

Stand-alone CLI that drives the W3C OWL 2 PositiveEntailmentTest /
ConsistencyTest / InconsistencyTest catalog against the
F\*-extracted `RDF.Graph.Executable.owl_rl_closure` and
`Tableau.tableau_materialise`.

```
owl_runner [--verbose] [profile-RL.rdf]
```

Default catalog: `third_party/testing/owl/profile-RL.rdf`.

## Rule #15 sniff

This runner contains a `test:importedOntology` fold (loads the
support ontology's triples into the premise graph before closure
runs) and an existential-bnode-match relaxation
(anonymous-subject conclusions match any term). Both are W3C
OWL test-corpus conventions, not RDF/SPARQL semantics. Per
CLAUDE.md iron rule #15 ("no semantic logic in test runners"),
the harness is on the boundary — defensible for the test corpus
but a candidate for moving inside the verified library if the
behaviour is needed elsewhere.

The §6.1.4 RDF/XML-correctness inline doc on `Parser.RDFXML.fst`
is the result of investigating this runner; see #227.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This runner is a consumer of the F\*-extracted closure + Tableau,
so it lives under `bin/<consumer>/` per the migration epic
[#200](https://github.com/danbri/factoidal/issues/200) Section D.

## Build

`formal/fstar/build-ocaml.sh compile` — source path
`../../../bin/owl-runner/owl_runner.ml`.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/rdfc10-runner/README.md`
- OWL design docs: `docs/designissues/2026-04-19-tableau-owl-plan.md`,
  `docs/designissues/2026-05-07-tableau-audit.md`,
  `docs/designissues/2026-05-07-owl2-rl-next-steps.md`
