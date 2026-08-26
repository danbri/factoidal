# @factoidal/lean — superseded, never published

**Superseded by issue [#618](https://github.com/danbri/factoidal/issues/618).**
The Lean 4 engine artifacts described below now ship *inside*
`@factoidal/core` (`npm/factoidal/l4-assets/`), so a plain
`npm install @factoidal/core` gets both engines with no companion
package to add. `factoidal/l4` and `factoidal/l4-core` resolve the
in-package copy first automatically — no call site changes.

This package was never published to npm, so nothing outside this repo
depends on it. It is kept in place (not deleted) only as a manual
override path — installing it next to a newer `@factoidal/core` still
works, because `factoidal/l4`'s resolver falls back to
`@factoidal/lean` when `l4-assets/` is absent — and as the historical
record of the packaging design this repo tried first (see
`docs/designissues/2026-08-22-npm-l4-module-packaging.md`, which
records both the original "companion package" reasoning and why it
changed). It will not be kept in sync with the Lean build going
forward; `npm/factoidal/l4-assets/` is the maintained copy.

---

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
