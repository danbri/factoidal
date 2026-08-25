# @factoidal/lean

The Lean 4 engine of [Factoidal](https://github.com/danbri/factoidal)
as a single WebAssembly module for browser, Node (>= 20) and Deno:
RDF parsing (N-Triples, N-Quads, Turtle, TriG, RDF/XML — RDF 1.1 and
1.2 modes), SPARQL 1.1/1.2 query and update, RDFS / ρdf / RDFS-Plus /
OWL 2 RL closures, and RDFC-1.0 canonicalization, compiled from the
`L4Factoidal` formal source (`formal/lean4/`), which builds with no
`sorry` and pins its W3C suite behaviour at compile time.

This package carries only the engine artifacts:

    l4factoidal.js    ES-module loader (loadL4)
    l4factoidal.mjs   Emscripten glue
    l4factoidal.wasm  the module
    version.json      build provenance + claims

Most users want it through `@factoidal/core`, whose `factoidal/l4`
(low-level) and `factoidal/l4-core` (typed API) subpaths resolve this
package automatically when it is installed next to core:

    npm install @factoidal/core @factoidal/lean
    const factoidal = require('@factoidal/core/l4-core');
    const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples' });
    const rows = await factoidal.query(ds, 'SELECT * WHERE { ?s ?p ?o }');

Direct use without core:

    const { loadL4 } = require('@factoidal/lean');
    const l4 = await loadL4();
    l4.call('queryDataset', [nquadsText, 'ASK { ?s ?p ?o }']);

The op names and JSON envelopes match `@factoidal/core`'s npm-entry
ABI; `l4.call('ops', [])` lists them. `version.json` records the Lean
toolchain, Emscripten version, source git SHA, wasm SHA-256, and the
conformance claims measured at that SHA.

License: Apache-2.0. The wasm links Lean's runtime (Apache-2.0),
mimalloc (MIT), and vendored HACL* C (Apache-2.0 — see
`third_party/hacl/PROVENANCE.md` in the repository).
