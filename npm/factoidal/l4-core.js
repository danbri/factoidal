// factoidal — Node entry point for the **Lean 4** engine.
//
// The same typed public API shape as index.js / wasm.js (parse /
// query / update / serialize / canonicalize / dataFactory / Dataset /
// the closure and checker family), served by the Lean 4 extraction
// compiled to WebAssembly (L4Factoidal — formal/lean4/) instead of
// the F* extraction. Asset resolution is l4.js's three-step ladder:
// @factoidal/lean, $FACTOIDAL_L4_ASSETS, then the repository checkout.
//
//   const factoidal = require('@factoidal/core/l4-core');
//   const ds = await factoidal.parse('<a> <b> "c" .', { format: 'ntriples' });
//
// Surface: the subset capabilities() reports. Operations the Lean
// engine does not implement (SHACL, ShEx, HDT, COTTAS, VC crypto,
// entailment-regime query modes, tableauMaterialise /
// tableauDlInconsistent, RML/CSVW/JSON-LD/RIF) reject with a clear
// engine-capability error rather than silently falling back to the F*
// engine — the point of this entry is that everything it answers came
// through the Lean extraction. See ./select.js (factoidal/select) for
// an explicit, observable lean/fstar/lean1st/fstar1st/slowcompareboth
// switch built on top of this and ./index.js (issue #618); this module
// itself never falls back. owlIsConsistent / owlEntails ARE served
// (the three-valued OWL DL verdict, formal/lean4 issue 586) when the
// resolved wasm carries the ops — an older bundle answers "unknown op",
// which surfaces as the entryResult error, so probe the `ops`
// reflection before relying on them. The export list mirrors wasm.js
// so callers can swap engines by import path alone.

'use strict';

const { buildApi } = require('./lib/api.js');
const rdfjs = require('./rdfjs.js');
const l4 = require('./l4.js');
const pkg = require('./package.json');

const NOT_SUPPORTED =
  'factoidal/l4-core: this operation is not implemented by the Lean 4 ' +
  'engine (see capabilities()); use the F* engine entry points for it. ' +
  'If the Lean assets are missing, npm install @factoidal/lean or set ' +
  'FACTOIDAL_L4_ASSETS.';

// The entry-ABI method names lib/api.js dispatches on, mapped onto the
// Lean wasm module's single dispatch export. Methods absent from this
// list are deliberately absent from the entry object: api.js
// typeof-guards each one and capabilities() reports the truth.
//
// The resolved wasm's full dispatch surface has 21 ops
// (`bin/linux-x86_64/l4factoidal ops`); this list wires 12 of them.
// Two families are deliberately withheld, for different reasons:
//
//   - CL/IKL (`clParse`, `clToDataset`, `queryWithIklService`): held
//     back by OWNER DECISION, 2026-08-26
//     (https://github.com/danbri/factoidal/issues/618) — "I don't want
//     npm code for direction b at this stage, unless for the shape of
//     ikl which is the subset we get mapping rdf into ikl. But ikl
//     doesn't have shapes or named profiles. Take it out of npm for
//     now." IKL has no notion of shapes or named profiles, so an
//     x-ikl-<suffix> entailment-regime family (see lib/api.js's
//     ENTAIL_VALUES / the x-ikl guard in query()) invents a taxonomy
//     the spec does not have. These three ops are NOT removed from the
//     compiled wasm (no rebuild happened for this) — they are simply
//     never dispatched to from this JS surface. Do not add them here
//     without a fresh owner sign-off; see the regression test in
//     test/select.test.js that pins them absent.
//   - dataset handles (`datasetOpen`/`datasetQuery`/`datasetUpdate`/
//     `datasetSerialize`/`datasetClose`): ordinary RDF dataset handles,
//     not part of the CL/IKL decision above. Held back only because
//     lib/api.js has no typed wrapper shape for a stateful handle yet
//     (every existing typed op is request/response) — a scope
//     judgement, not an owner ruling. Wiring these in is a reasonable
//     follow-up.
const OPS = [
  'parseToDatasetJson',
  'queryDataset',
  'updateDataset',
  'serializeNQuads',
  'serializeTurtle',
  'canonicalizeToNQuads',
  'owlClosure',
  'owlIsConsistent',
  'owlEntails',
  'rhoDfClosure',
  'rhoDfFragmentCheck',
  'rdfsPlusClosure',
];

async function loadLeanEntry() {
  const eng = await l4.loadL4();
  if (typeof eng.call !== 'function') {
    throw new Error(
      'factoidal/l4-core: the resolved Lean wasm module predates the ' +
      'dispatch ABI (no call export); update @factoidal/lean or ' +
      'FACTOIDAL_L4_ASSETS to a build with l4_call'
    );
  }
  const entry = { abiVersion: '1' };
  for (const op of OPS) {
    // lib/api.js's entryResult() takes the envelope as a JSON STRING
    // (entry_jsoo.ml's wire shape). The Lean loader's call() parses the
    // envelope and throws on {"ok":false}; re-encode both outcomes so
    // this entry object is wire-compatible with the F* one.
    entry[op] = (...args) => {
      try {
        return JSON.stringify(eng.call(op, args.map(String)));
      } catch (err) {
        return JSON.stringify({
          ok: false,
          error: String((err && err.message) || err),
        });
      }
    };
  }
  return entry;
}

const api = buildApi({
  engineName: 'l4',
  loadEntry: loadLeanEntry,
  runCli: async () => ({ exitCode: 1, stdout: '', stderr: NOT_SUPPORTED }),
});

module.exports = {
  parse: api.parse,
  query: api.query,
  update: api.update,
  serialize: api.serialize,
  canonicalize: api.canonicalize,
  graphs: api.graphs,
  canonicalHash: api.canonicalHash,
  owlClosure: api.owlClosure,
  coreRdfsClosure: api.coreRdfsClosure,
  coreRdfsCheck: api.coreRdfsCheck,
  rhoDfClosure: api.rhoDfClosure,
  rhoDfFragmentCheck: api.rhoDfFragmentCheck,
  rdfsPlusClosure: api.rdfsPlusClosure,
  // Served by the Lean engine's dispatch ABI when the resolved wasm
  // carries the ops (see the header note).
  owlIsConsistent: api.owlIsConsistent,
  owlEntails: api.owlEntails,
  // Not implemented by this engine — kept on the surface so a caller
  // swapping engines gets the pinned capability error, not
  // `undefined is not a function`.
  shaclValidate: api.shaclValidate,
  shexValidate: api.shexValidate,
  capabilities: api.capabilities,
  Dataset: rdfjs.Dataset,
  dataFactory: rdfjs.dataFactory,
  engine: 'lean4-wasm',
  available: l4.available,
  version: pkg.version,
};
