// Tests for the graphflow spike. Run with:  node --test bin/graphflow/test/
//
// These live outside npm/factoidal/test/ on purpose: graphflow is a consumer
// tool (Iron Rule 11), not part of the published package, so it must not ride
// along in the package's test glob or its `files` list.

const test = require('node:test');
const assert = require('node:assert');
const { execFileSync } = require('node:child_process');
const { readFileSync } = require('node:fs');
const path = require('node:path');

const ROOT = path.resolve(__dirname, '../../..');
const RUN = path.join(ROOT, 'bin/graphflow/run.mjs');
const CHECK = path.join(ROOT, 'bin/graphflow/check.mjs');
const CERT = path.join(ROOT, 'tmp/graphflow.cert.json');

const node = (args, opts) =>
  execFileSync(process.execPath, args, { encoding: 'utf8', cwd: ROOT, ...opts });

test('the network runs and its certificate checks out', { timeout: 300000 }, () => {
  node([RUN], { stdio: ['ignore', 'pipe', 'ignore'] });
  const out = node([CHECK, CERT]);
  assert.match(out, /^ACCEPTED:/m);
  assert.match(out, /signature\s+ed25519 .* verified with node:crypto/);
});

test('the certificate covers every process, with chained hashes', () => {
  const cert = JSON.parse(readFileSync(CERT, 'utf8'));
  assert.equal(cert.format, 'graphflow-cert/0.1');
  assert.deepEqual(cert.transforms.map((t) => t.process).sort(),
    ['canon', 'closure', 'data', 'shapes', 'sign', 'validate']);
  const by = Object.fromEntries(cert.transforms.map((t) => [t.process, t]));
  // The fan-out: both consumers of closure.out consumed the same value.
  assert.equal(by.closure.outputs.out.sha256, by.validate.inputs.ds.sha256);
  assert.equal(by.closure.outputs.out.sha256, by.canon.inputs.ds.sha256);
  // The fan-in: validate took its shapes from the other parse.
  assert.equal(by.shapes.outputs.out.sha256, by.validate.inputs.shapes.sha256);
});

test('the closure is load-bearing: validation sees a target only after it', () => {
  const cert = JSON.parse(readFileSync(CERT, 'utf8'));
  const validate = cert.transforms.find((t) => t.process === 'validate');
  // fido has no ex:name, and is only an ex:Mammal (the shape's target class)
  // because core-RDFS closure derived it from ex:Dog rdfs:subClassOf ex:Mammal.
  // Without the closure process there would be no target and no violation.
  assert.equal(validate.outputs.conforms.value, false);
});

test('every guard bites', { timeout: 300000 }, () => {
  const out = node([path.join(ROOT, 'bin/graphflow/sabotage.mjs')]);
  assert.match(out, /sabotage: \d+ guard\(s\) bit, 0 did not/);
  assert.doesNotMatch(out, /WENT UNNOTICED/);
});

test('the checker never reaches for the engine', () => {
  // Strip comments before searching. The first version of this test searched
  // the raw source and failed on check.mjs's own header comment, which says
  // "No @factoidal/core import" — a guard that reads prose flags the sentence
  // documenting its own success. (Same shape as an audit counting the comment
  // that warns about the thing it audits.) Read code, not commentary.
  const code = readFileSync(CHECK, 'utf8')
    .replace(/\/\*[\s\S]*?\*\//g, ' ')
    .split('\n').map((l) => l.replace(/(^|[^:])\/\/.*$/, '$1')).join('\n');
  for (const forbidden of ['@factoidal/core', 'factoidal.js', 'fn.js', 'child_process', 'node:http']) {
    assert.ok(!code.includes(forbidden), `check.mjs must not reference ${forbidden}`);
  }
  // And positively: its only imports are node builtins.
  const imports = [...code.matchAll(/from\s+['"]([^'"]+)['"]/g)].map((m) => m[1]);
  assert.ok(imports.length > 0, 'expected to find import statements');
  for (const spec of imports) {
    assert.ok(spec.startsWith('node:'), `check.mjs imports ${spec}; only node: builtins are allowed`);
  }
});
