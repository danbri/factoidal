// factoidal — Node driver for the js_of_ocaml CLI bundle.
//
// The engine bundle (factoidal.js) is a single-shot CLI: argv in,
// stdout out. runCli() drives one invocation in-process:
//   1. input documents are registered in js_of_ocaml's fake filesystem
//      (globalThis.jsoo_fs_tmp, drained at engine startup — `/static/`
//      is always the MlFakeDevice mount, in Node and browsers alike);
//   2. globalThis.process.argv carries the flags;
//   3. stdout/stderr are captured on BOTH channels the bundle may use:
//      console.log/.error (the fstar_utf8_output_stubs.js path in
//      current bundles) and require('fs').writeSync on fds 1/2 (the
//      classic js_of_ocaml path), the latter via a proxied require;
//   4. process.exit is replaced by a sentinel throw.
//
// This file also resolves WHICH bundle to load: an explicit override,
// then the package-local copy (what npm ships), then the repo build
// output (developer tree). The resolution is exported so tests can pin
// the freshest artifact.

'use strict';

const fs = require('node:fs');
const path = require('node:path');

const PKG_ROOT = path.resolve(__dirname, '..');

/** Candidate bundle paths, in resolution order. */
function bundleCandidates() {
  const c = [];
  if (process.env.FACTOIDAL_JS_BUNDLE) c.push(process.env.FACTOIDAL_JS_BUNDLE);
  c.push(path.join(PKG_ROOT, 'factoidal.js'));
  // Developer tree fallback: repo build output.
  c.push(path.resolve(PKG_ROOT, '..', '..', 'docs', 'fstar-extracted', 'factoidal.js'));
  return c;
}

// A bundle is usable for the typed API when its CLI knows --dump-nq
// (the argv strings survive into the generated JavaScript, so a
// substring check is a reliable capability sniff). Prefer the first
// candidate that qualifies; fall back to the first that merely exists
// so queryRaw() keeps working against very old bundles.
function resolveBundlePath() {
  let firstExisting = null;
  for (const p of bundleCandidates()) {
    if (!p || !fs.existsSync(p)) continue;
    if (firstExisting === null) firstExisting = p;
    try {
      if (fs.readFileSync(p, 'utf8').includes('--dump-nq')) return p;
    } catch (_) { /* unreadable candidate — keep looking */ }
  }
  if (firstExisting) return firstExisting;
  throw new Error(
    'factoidal.js engine bundle not found. Run ' +
    "'formal/fstar/build-ocaml.sh js && formal/fstar/build-ocaml.sh npm' " +
    'in the repo, or set FACTOIDAL_JS_BUNDLE.'
  );
}

let _src = null;
let _srcPath = null;

function loadSource() {
  const p = resolveBundlePath();
  if (_src !== null && _srcPath === p) return _src;
  _src = fs.readFileSync(p, 'utf8');
  _srcPath = p;
  return _src;
}

/**
 * Run one CLI invocation of the js_of_ocaml engine bundle.
 *
 * @param {string[]} args   CLI arguments (after argv[0]/argv[1]).
 * @param {Array<{name: string, content: string}>} files
 *        Documents for the fake filesystem. Names must start
 *        with '/static/'.
 * @returns {{stdout: string, stderr: string, exitCode: number}}
 */
function runCli(args, files) {
  const orig = {
    argv: globalThis.process ? globalThis.process.argv : undefined,
    exit: globalThis.process ? globalThis.process.exit : undefined,
    jsooFs: globalThis.jsoo_fs_tmp,
    consoleLog: console.log,
    consoleError: console.error,
  };

  const stdoutChunks = [];
  const stderrChunks = [];
  function asUtf8(data) {
    if (typeof data === 'string') return data;
    if (data && typeof data.toString === 'function') {
      try { return Buffer.from(data).toString('utf8'); }
      catch (_) { return String(data); }
    }
    return String(data);
  }

  // js_of_ocaml's Node runtime opens fds 1/2 via require('fs') and
  // writes with fs.writeSync — bypassing console.log and
  // process.stdout. Proxy the fs module we hand the bundle.
  const patchedFs = new Proxy(fs, {
    get(target, prop, receiver) {
      if (prop === 'writeSync') {
        return function proxyWriteSync(fd, chunk, ...rest) {
          if (fd === 1) { stdoutChunks.push(asUtf8(chunk)); return asUtf8(chunk).length; }
          if (fd === 2) { stderrChunks.push(asUtf8(chunk)); return asUtf8(chunk).length; }
          return target.writeSync(fd, chunk, ...rest);
        };
      }
      return Reflect.get(target, prop, receiver);
    },
  });
  function wrappedRequire(name) {
    if (name === 'fs' || name === 'node:fs') return patchedFs;
    return require(name);
  }

  globalThis.process = globalThis.process || {};
  globalThis.process.argv = ['node', 'factoidal', ...args];
  globalThis.jsoo_fs_tmp = (files || []).map((f) => ({
    name: f.name,
    content: f.content,
  }));

  // Current bundles emit stdout/stderr line-wise via console.log /
  // console.error (fstar_utf8_output_stubs.js); console adds the
  // trailing newline, so re-append it when capturing.
  console.log = (...a) => { stdoutChunks.push(a.map(asUtf8).join(' ') + '\n'); };
  console.error = (...a) => { stderrChunks.push(a.map(asUtf8).join(' ') + '\n'); };

  let exitCode = 0;
  const EXIT_SENTINEL = new Error('__factoidal_exit__');
  globalThis.process.exit = (n) => { exitCode = n | 0; throw EXIT_SENTINEL; };

  function restore() {
    if (globalThis.process) {
      globalThis.process.argv = orig.argv;
      globalThis.process.exit = orig.exit;
    }
    globalThis.jsoo_fs_tmp = orig.jsooFs;
    console.log = orig.consoleLog;
    console.error = orig.consoleError;
  }

  try {
    const src = loadSource();
    (new Function('require', src))(wrappedRequire);
  } catch (e) {
    if (e !== EXIT_SENTINEL) {
      restore();
      throw e;
    }
  } finally {
    restore();
  }

  return {
    stdout: stdoutChunks.join(''),
    stderr: stderrChunks.join(''),
    exitCode,
  };
}

module.exports = { runCli, resolveBundlePath };
