// hacl-init.js — one-time async initialiser for the HACL* WebAssembly
// crypto backend used by the VC Data Integrity (eddsa-rdfc-2022) ABI
// (vcVerify / vcSign / vcSha256Hex etc. on `factoidalNpmEntry`).
//
// Why an explicit init step: js_of_ocaml `external` primitives are
// SYNCHRONOUS, but WebAssembly instantiation is ASYNCHRONOUS. So the
// consumer initialises the HACL* wasm modules ONCE (await), which stashes
// the ready HACL* API object on `globalThis.__factoidalHacl`; after that
// the synchronous `caml_hacl_*` stubs in the bundle (hacl_stubs.js) read
// that global and call HACL* synchronously — no await on the hot path.
//
// Crypto sourcing policy: skills/crypto-policy/SKILL.md. The crypto itself
// is HACL*'s OWN official WebAssembly build (third_party/hacl-wasm/, the
// `hacl-wasm` npm artifacts, F*/Low*-verified, KaRaMeL->wasm). This file
// contains NO cryptographic logic — it only loads the verified modules and
// drives HACL*'s own vendored `api.js` bindings.
//
// Usage (Node):
//   const { initHacl } = require('@danbri/foafos/hacl-init.js');
//   await initHacl();
//   require('./factoidal-npm-entry.js');           // sets globalThis.factoidalNpmEntry
//   const r = JSON.parse(globalThis.factoidalNpmEntry.vcEd25519Verify(pk, msg, sig));
//
// Usage (browser): serve the `hacl-wasm/` directory next to the page and
//   call `await initHacl({ apiUrl: '/path/to/hacl-wasm/api.js' })`. HACL*'s
//   api.js fetches its own .wasm/.json relative to that URL.

'use strict';

// Transitive closure of Ed25519 + SHA-2, in load order. Matches the module
// subset vendored under third_party/hacl-wasm/ (see PROVENANCE.md).
var HACL_MODULES = [
  'WasmSupport', 'FStar', 'LowStar_Endianness',
  'Hacl_Hash_Base', 'Hacl_Hash_SHA2',
  'Hacl_IntTypes_Intrinsics', 'Hacl_Bignum_Base', 'Hacl_Bignum',
  'Hacl_Bignum25519_51', 'Hacl_Curve25519_51',
  'Hacl_Ed25519_PrecompTable', 'Hacl_Ed25519'
];

var _initPromise = null;

// Load HACL*'s own api.js bindings. In Node we `require` the vendored copy
// (which reads its .wasm/.json off disk relative to itself). Callers may
// override with opts.apiPath (Node) or opts.HaclWasm (a pre-required module).
function _loadHaclWasm(opts) {
  if (opts && opts.HaclWasm) return opts.HaclWasm;
  var path = require('path');
  var candidates = [];
  if (opts && opts.apiPath) candidates.push(opts.apiPath);
  // Packaged layout: hacl-wasm/ sits next to this file.
  candidates.push(path.resolve(__dirname, './hacl-wasm/api.js'));
  // In-repo layout: run directly out of the source tree.
  candidates.push(path.resolve(__dirname, '../../third_party/hacl-wasm/api.js'));
  var lastErr = null;
  for (var i = 0; i < candidates.length; i++) {
    try { return require(candidates[i]); }
    catch (e) { lastErr = e; }
  }
  throw new Error(
    'hacl-init: could not locate HACL* wasm bindings (api.js). Tried: ' +
    candidates.join(', ') + '. Last error: ' + (lastErr && lastErr.message));
}

/**
 * Initialise the HACL* WebAssembly crypto backend exactly once.
 * Idempotent: repeated calls return the same promise.
 *
 * @param {object} [opts]
 * @param {string} [opts.apiPath]  Node: path to a HACL* api.js to require.
 * @param {object} [opts.HaclWasm] Pre-required HACL* module (skips lookup).
 * @param {string[]} [opts.modules] Override the wasm module list.
 * @returns {Promise<object>} the ready HACL* API object.
 */
function initHacl(opts) {
  if (_initPromise) return _initPromise;
  opts = opts || {};
  _initPromise = (async function () {
    var HaclWasm = _loadHaclWasm(opts);
    var modules = opts.modules || HACL_MODULES;
    var Hacl = await HaclWasm.getInitializedHaclModule(modules);
    globalThis.__factoidalHacl = Hacl;
    return Hacl;
  })();
  return _initPromise;
}

/** True once initHacl() has completed and the backend is live. */
function haclReady() {
  return !!(typeof globalThis !== 'undefined' && globalThis.__factoidalHacl);
}

module.exports = { initHacl: initHacl, haclReady: haclReady, HACL_MODULES: HACL_MODULES };
