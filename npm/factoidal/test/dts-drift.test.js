// Cheap drift gate: every function/const a .d.ts DECLARES must actually
// exist on the module it types, and (the direction that bit us) every
// runtime export of the .js should be typed in its .d.ts. This is a
// regex-level structural check — not a real tsc typecheck — but it is
// enough to have caught the fn.d.ts/fn.js divergence (openCottas/
// toCottas exported from fn.js but undeclared in fn.d.ts) this test
// pins closed.

'use strict';

const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');

// Names that are declared in a .d.ts but are NOT runtime value exports
// (types/interfaces/classes-as-types), so they legitimately have no
// module.exports entry. Kept explicit so a genuinely-missing function
// can't hide behind a blanket allowlist.
const TYPE_ONLY = new Set([
  // index.d.ts type-level declarations
  'NamedNode', 'BlankNode', 'Literal', 'Variable', 'DefaultGraph', 'Quad',
  'Quad_Subject', 'Quad_Predicate', 'Quad_Object', 'Quad_Graph', 'Term',
  'DataFactory', 'DataFormat', 'EntailRegime', 'Bindings', 'DataInput',
  'ParseOptions', 'QueryOptions', 'SerializeOptions', 'ShaclValidateResult',
  'CsvwOptions', 'JsonLdOptions', 'JsonLdFromRdfOptions', 'XPathResult',
  'MathValue', 'XFormsBind', 'XFormsNodeValidity', 'SchematronFinding',
  'ToanExpr', 'MatrixCell', 'MatrixResult', 'SrjTerm', 'SparqlResultsJson',
  'OutputFormat',
  // fn.d.ts type-level declarations
  'FnDataset', 'Builder', 'ValidateResult', 'Cell', 'Derived', 'CottasStore',
]);

// Parse `export function NAME` / `export const NAME` / `export class NAME`
// / `export interface NAME` / `export type NAME` from a .d.ts.
function declaredValueNames(dtsPath) {
  const src = fs.readFileSync(dtsPath, 'utf8');
  const names = new Set();
  const re = /^export\s+(?:declare\s+)?(?:async\s+)?(function|const|class)\s+([A-Za-z_$][\w$]*)/gm;
  let m;
  while ((m = re.exec(src)) !== null) {
    if (!TYPE_ONLY.has(m[2])) names.add(m[2]);
  }
  return names;
}

function runtimeNames(mod) {
  return new Set(Object.keys(mod).filter((k) => k !== 'default'));
}

test('fn.d.ts declares nothing fn.js does not implement', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'fn.d.ts'));
  const runtime = runtimeNames(require('../fn.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  assert.deepEqual(missing, [],
    `fn.d.ts declares names absent from fn.js: ${missing.join(', ')}`);
});

test('fn.js implements nothing that fn.d.ts leaves untyped', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'fn.d.ts'));
  const runtime = runtimeNames(require('../fn.js'));
  // FnDataset is exported as a value (class) but declared as a type in
  // fn.d.ts; treat it as typed.
  const untyped = [...runtime].filter((n) => !declared.has(n) && !TYPE_ONLY.has(n));
  assert.deepEqual(untyped, [],
    `fn.js exports names undeclared in fn.d.ts: ${untyped.join(', ')}`);
});

test('l4-core.d.ts declares nothing l4-core.js does not implement', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'l4-core.d.ts'));
  const runtime = runtimeNames(require('../l4-core.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  assert.deepEqual(missing, [],
    `l4-core.d.ts declares names absent from l4-core.js: ${missing.join(', ')}`);
});

test('l4-core.js implements nothing that l4-core.d.ts leaves untyped', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'l4-core.d.ts'));
  const runtime = runtimeNames(require('../l4-core.js'));
  // Dataset is exported as a value (class) by l4-core.js but typed via
  // the `export { Dataset, ... }` re-export from './index' in
  // l4-core.d.ts, which declaredValueNames's regex cannot see (same
  // situation as fn.d.ts's FnDataset); treat it as typed here without
  // widening TYPE_ONLY for the index.d.ts checks.
  const untyped = [...runtime].filter(
    (n) => !declared.has(n) && !TYPE_ONLY.has(n) && n !== 'Dataset');
  assert.deepEqual(untyped, [],
    `l4-core.js exports names undeclared in l4-core.d.ts: ${untyped.join(', ')}`);
});

test('index.d.ts declares nothing index.js does not implement', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'index.d.ts'));
  const runtime = runtimeNames(require('../index.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  assert.deepEqual(missing, [],
    `index.d.ts declares names absent from index.js: ${missing.join(', ')}`);
});

test('index.js implements nothing that index.d.ts leaves untyped', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'index.d.ts'));
  const runtime = runtimeNames(require('../index.js'));
  const untyped = [...runtime].filter((n) => !declared.has(n) && !TYPE_ONLY.has(n));
  assert.deepEqual(untyped, [],
    `index.js exports names undeclared in index.d.ts: ${untyped.join(', ')}`);
});

test('select.d.ts declares nothing select.js does not implement', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'select.d.ts'));
  const runtime = runtimeNames(require('../select.js'));
  const missing = [...declared].filter((n) => !runtime.has(n));
  assert.deepEqual(missing, [],
    `select.d.ts declares names absent from select.js: ${missing.join(', ')}`);
});

test('select.js implements nothing that select.d.ts leaves untyped', () => {
  const declared = declaredValueNames(path.join(__dirname, '..', 'select.d.ts'));
  const runtime = runtimeNames(require('../select.js'));
  const untyped = [...runtime].filter((n) => !declared.has(n) && !TYPE_ONLY.has(n));
  assert.deepEqual(untyped, [],
    `select.js exports names undeclared in select.d.ts: ${untyped.join(', ')}`);
});

test('the VC crypto surface is typed on both index.d.ts and fn.d.ts', () => {
  const vc = [
    'vcSha256Hex', 'vcEd25519SecretToPublic', 'vcEd25519Sign',
    'vcEd25519Verify', 'vcEddsaCreateFromCanonical', 'vcEddsaVerifyFromCanonical',
  ];
  const indexDecl = declaredValueNames(path.join(__dirname, '..', 'index.d.ts'));
  const fnDecl = declaredValueNames(path.join(__dirname, '..', 'fn.d.ts'));
  for (const name of vc) {
    assert.ok(indexDecl.has(name), `index.d.ts declares ${name}`);
    assert.ok(fnDecl.has(name), `fn.d.ts declares ${name}`);
  }
});
