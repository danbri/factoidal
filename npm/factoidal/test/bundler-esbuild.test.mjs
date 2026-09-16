// Proves the bundler route of issue #682 end to end: esbuild --bundle
// over test/fixtures/bundler-app.mjs (which imports ONLY
// '@factoidal/core/api' and '@factoidal/core/factoidal-npm-entry.js',
// both statically importable, no fetch, no eval) produces output that
// runs standalone under Node with `platform: 'browser'` — the same
// constraint a real bundler-built web page runs under. The browser
// CSP page itself (no `unsafe-eval`) is proved separately by
// tests/web-demos/bundler_csp_smoke.sh, which bundles this same
// fixture and drives it through headless Chromium.
//
// Skips (does not fail) only when esbuild cannot be resolved --
// `npm install` in npm/factoidal (esbuild is a devDependency) makes
// it resolvable; every other failure here is a real regression.
//
// esbuild `external` list (issue #682): factoidal-npm-entry.js is
// js_of_ocaml output, whose runtime has four literal
// `require(moduleName)` call sites for Node built-ins: 'node:fs' and
// 'node:tty' unconditionally inside class methods (file I/O,
// `isatty()` — code paths this fixture's parse/SELECT flow never
// calls), and 'util' and 'fzstd' behind `typeof require ===
// "function"` guards (a TextDecoder fallback and zstd decompression
// for COTTAS bytes). esbuild constant-folds `typeof require` to
// `"undefined"` when bundling to `format: 'esm'` for `platform:
// 'browser'` (no `require` global exists in that output, so the
// guard is provably false) and dead-code-eliminates the guarded
// branches — 'util' and 'fzstd' are never even seen. The two
// UNGUARDED requires are still syntactically present in the bundle
// graph (their containing methods are never CALLED by this fixture,
// but esbuild does not do that depth of interprocedural analysis) and
// must be marked `external` (esbuild then leaves the `require(...)`
// call as-is instead of trying to bundle a module for it): 'node:fs',
// 'node:tty'. Safe at runtime: with no `require` global, `typeof
// require === "function"` used elsewhere is false, and the two
// external `require(...)` calls only execute inside methods this
// fixture's parse/SELECT path never reaches. This list is derived
// empirically below (esbuild's own "Could not resolve" errors from an
// externals-free build), not hardcoded, so a js_of_ocaml runtime
// change that adds, removes, or unguards one is caught by this test
// rather than by a silent stale allowlist.

import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import { execFileSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const PKG_ROOT = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const FIXTURE = path.join(PKG_ROOT, 'test', 'fixtures', 'bundler-app.mjs');

// ESM test file: no CJS `require` in scope by default -- needed to
// load esbuild's own (CommonJS) package.
const require = createRequire(import.meta.url);

let esbuild = null;
let esbuildSkipReason = null;
try {
  esbuild = require('esbuild');
} catch (e) {
  esbuildSkipReason = `esbuild not resolvable in npm/factoidal (devDependency; ` +
    `run 'npm install' in npm/factoidal): ${e.message}`;
}

// esbuild resolves bare imports by walking up from the importing
// file's directory looking for node_modules/<name> at each ancestor
// (standard Node algorithm) -- a self-referencing symlink at
// npm/factoidal/node_modules/@factoidal/core, pointing at the package
// root itself, makes '@factoidal/core/...' resolve exactly as it
// would for a real consumer that ran `npm install @factoidal/core`,
// with no esbuild `alias` option needed.
function ensureSelfSymlink() {
  const nmDir = path.join(PKG_ROOT, 'node_modules');
  const scopeDir = path.join(nmDir, '@factoidal');
  const linkPath = path.join(scopeDir, 'core');
  fs.mkdirSync(scopeDir, { recursive: true });
  const already = fs.existsSync(linkPath) &&
    fs.lstatSync(linkPath).isSymbolicLink() &&
    fs.realpathSync(linkPath) === fs.realpathSync(PKG_ROOT);
  if (already) return;
  fs.rmSync(linkPath, { recursive: true, force: true });
  fs.symlinkSync(PKG_ROOT, linkPath, 'dir');
}

// Parse esbuild's "Could not resolve \"X\"" build-error text into the
// bare specifier X, deduplicated.
function unresolvedSpecifiers(esbuildError) {
  const specs = new Set();
  for (const err of (esbuildError && esbuildError.errors) || []) {
    const m = /Could not resolve "([^"]+)"/.exec(err.text || '');
    if (m) specs.add(m[1]);
  }
  return [...specs];
}

test('esbuild --bundle over the CSP fixture runs under Node (platform: browser, format: esm)',
  async (t) => {
    if (esbuildSkipReason) { t.skip(esbuildSkipReason); return; }

    ensureSelfSymlink();

    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'factoidal-bundler-test-'));
    const outfile = path.join(outDir, 'bundle.mjs');

    const baseOptions = {
      entryPoints: [FIXTURE],
      outfile,
      bundle: true,
      platform: 'browser',
      format: 'esm',
      write: true,
      logLevel: 'silent',
    };

    const t0 = Date.now();
    let externalList = [];
    try {
      await esbuild.build(baseOptions);
    } catch (firstError) {
      externalList = unresolvedSpecifiers(firstError);
      assert.ok(externalList.length > 0,
        'esbuild build failed and reported no "Could not resolve" ' +
        `specifiers to mark external -- real failure:\n${firstError && firstError.message}`);
      await esbuild.build({ ...baseOptions, external: externalList });
    }
    const bundleMs = Date.now() - t0;
    console.log(`  esbuild bundle: ${bundleMs}ms, external=[${externalList.join(', ')}]`);

    // The empirically-derived external list must be exactly the two
    // UNGUARDED js_of_ocaml Node-builtin requires documented in this
    // file's header ('util'/'fzstd' are guarded by `typeof require`
    // and esbuild dead-code-eliminates them for this platform/format
    // combination before ever trying to resolve them) -- not a subset
    // (a missing one means the build above would have failed) and not
    // a superset (a stray extra name means something in the fixture
    // itself started requiring a Node builtin, which this test should
    // catch rather than silently externalize).
    assert.deepEqual(
      [...externalList].sort(),
      ['node:fs', 'node:tty'],
      'external list drifted from the documented js_of_ocaml runtime probes');

    assert.ok(fs.existsSync(outfile), 'esbuild wrote the bundle output');
    const bundleSource = fs.readFileSync(outfile, 'utf8');

    // js_of_ocaml's runtime bootstraps a filesystem-device table at
    // module load, unconditionally (not gated by anything this
    // fixture's parse/SELECT path controls): it branches on
    // `process.versions.node` to decide between a real-fs device
    // (needs the externalized `require("node:fs")`, which throws
    // under `format: 'esm'` output if actually called -- ESM has no
    // dynamic require) and an in-memory one. In a real browser that
    // branch is never taken (no `process` global at all), which is
    // what this bundle is built for (`platform: 'browser'`); running
    // the SAME output directly under Node, `process` is real, so the
    // real-fs branch runs and hits the externalized require. Deleting
    // `globalThis.process` before executing reproduces the browser
    // condition this platform target assumes, without touching the
    // bundle file esbuild wrote (only the copy fed to this child
    // process) -- exactly what the actual browser CSP page in
    // tests/web-demos/bundler_csp_smoke.sh gets for free simply by
    // being a browser.
    const runSource = 'delete globalThis.process;\n' + bundleSource;

    let stdout;
    try {
      stdout = execFileSync(process.execPath, ['--input-type=module'], {
        input: runSource,
        encoding: 'utf8',
        timeout: 30000,
      });
    } catch (runError) {
      assert.fail(
        'running the bundled output under Node failed ' +
        `(exit ${runError.status}):\nstdout: ${runError.stdout}\nstderr: ${runError.stderr}`);
    }

    const m = /ROW_COUNT:(\d+)/.exec(stdout);
    assert.ok(m, `bundle output did not print ROW_COUNT:N -- got:\n${stdout}`);
    assert.equal(Number(m[1]), 3, 'SELECT ?p WHERE { ?p a foaf:Person } returns 3 rows');

    fs.rmSync(outDir, { recursive: true, force: true });
  });
