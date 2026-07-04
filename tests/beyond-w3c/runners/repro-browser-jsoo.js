// Reproduce the browser invocation path in Node.
// Mirrors npm/factoidal/browser.js's runFactoidalCli() (formerly
// duplicated inline in factoidal-sparql-client.js before that
// component was rewired to call the npm package directly).
const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..', '..', '..');
const dataPath = path.join(ROOT, 'docs/fstar-extracted/samples/people.ttl');
const queryPath = path.join(ROOT, 'tests/beyond-w3c/fixtures/queries/bind-upper.rq');

const dataContent = fs.readFileSync(dataPath, 'utf8');
const queryText = fs.readFileSync(queryPath, 'utf8');

globalThis.jsoo_fs_tmp = [{ name: '/tmp/data.ttl', content: dataContent }];
globalThis.process = globalThis.process || {};
globalThis.process.argv = ['node', 'factoidal',
  '-d', '/tmp/data.ttl', '-e', queryText, '-o', 'json'];

const buf = [];
const origLog = console.log, origErr = console.error;
console.log   = (...a) => buf.push(a.join(' '));
console.error = (...a) => buf.push(a.join(' '));

let exitCode = 0;
const origExit = globalThis.process.exit;
globalThis.process.exit = (n) => { exitCode = n | 0; throw new Error('__exit__'); };

const src = fs.readFileSync(path.join(ROOT, 'docs/fstar-extracted/factoidal.js'), 'utf8');
try {
  (new Function(src))();
} catch (e) {
  if (!e || e.message !== '__exit__') {
    buf.push('\n[harness] ' + (e && e.stack || e));
    exitCode = 1;
  }
} finally {
  globalThis.process.exit = origExit;
}

console.log = origLog; console.error = origErr;
process.stdout.write(buf.join('\n'));
process.stdout.write('\n');
process.exit(exitCode);
