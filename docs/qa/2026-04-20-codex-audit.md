# 2026-04-20 Codex Audit

Scope: read-only audit of whether Factoidal has a real, useful working surface. Scratch fixtures were created under `tmp/`.

## What Worked

- Native CLI exists and runs from `bin/darwin-arm64/factoidal`.
  - `--version` returned `factoidal 0.1.0 (F*-extracted SPARQL/RDF)`.
  - `--help` documents RDF parsing, SPARQL query, named graphs, entailment, and COTTAS input.
- Basic RDF/SPARQL behavior works on scratch data.
  - Turtle count returned `4 triples`.
  - SELECT with PREFIX returned Alice and Bob.
  - `COUNT(*)` returned typed integer `"4"^^xsd:integer`.
  - N-Quads `GRAPH ?g` query returned two named graph rows.
- `npm/factoidal` smoke tests pass.
  - `npm test` passed 8 checks.
  - `node npm/factoidal/test/smoke-wasm.js` passed 3 checks on this Node, with a package type warning.
- W3C runner is real and reads the checked-out W3C suites.
  - `--list` shows 34 SPARQL suites and 6 RDF suites.
  - SPARQL slices: `bind` 10/10, `property-path` 33/33, `subquery` 12 pass / 2 unsupported, `functions` 74 pass / 1 fail.
  - RDF slices: `rdf-mt` 39/39, `rdf-n-triples` 70/70.
  - JS runner slice: `node docs/fstar-extracted/w3c-runner.js bind` passed 10/10.
- F* verification works when run through the `fstar` opam switch.
  - In a copied tree under `tmp/fstar-audit`, `opam exec --switch=fstar -- make -B verify` verified `RDF.Graph.Executable`, `SPARQL11.Algebra`, and `Tableau`.
  - Warnings observed: recursive binding not used and an unpopped `#push-options` depth warning in `SPARQL11.Algebra.fst`.
- HTTP endpoint works after allowing localhost bind.
  - `factoidal-http --port 3139 --dataset tmp/audit-people.ttl --read-only` loaded 4 triples.
  - A GET `/query` request returned SPARQL Results JSON for Alice and Bob.
- Example script `examples/tiny_namedgraphs.sh` works if `bin/darwin-arm64` is on `PATH`.

## Friction / Risks

- The repo was already dirty before this audit, with generated JS/WASM/formal artifacts modified or untracked. I did not revert or touch those files.
- Plain shell environment cannot see `fstar.exe` or `ocamlfind`; commands need `opam exec --switch=fstar -- ...` or `eval $(opam env --switch=fstar)`.
- `docs/test-results/index.html` is stale relative to current README/local runner results. It says generated `2026-04-17`, SPARQL `275 pass / 144 fail`, while local targeted suites and README indicate much newer progress.
- `npm run build` in `docs/` fails before `npm ci` because `eleventy` is not installed locally.
- `w3c_runner --all` was stopped after more than a minute with no captured output. Targeted suites are usable; full-suite UX needs progress/log guidance or an expected runtime note.
- There remains a significant unverified boundary: many `assume val` entries for regex/hash/parser glue, Parquet/COTTAS/HDT/HDTQ stores, and forward references, plus four `admit ()` proof lemmas in `SPARQL11.Algebra.fst`.
- The npm wasm smoke test passes but emits Node's `MODULE_TYPELESS_PACKAGE_JSON` warning for `test/smoke-wasm.js`.
- Example scripts assume `factoidal` is on `PATH`; a fresh checkout user needs to know to prepend `bin/<platform>`.

## Bottom Line

Something real is built here. The native CLI, npm wrapper, browser/Node JS artifact, wasm smoke path, conformance runner, F* verification path, and HTTP endpoint all execute useful RDF/SPARQL work locally. The main caveat is not existence but maturity: generated artifacts and published test-result docs are out of sync, the full-suite runner is awkward to use interactively, and the verified boundary is still smaller than the product framing implies.
