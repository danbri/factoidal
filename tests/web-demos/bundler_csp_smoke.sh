#!/usr/bin/env bash
# tests/web-demos/bundler_csp_smoke.sh
#
# Proves the CSP-safe route of issue #682 against a REAL browser under
# a strict Content-Security-Policy: bundles
# npm/factoidal/test/fixtures/bundler-app.mjs with esbuild (same
# fixture and same external-modules handling as
# npm/factoidal/test/bundler-esbuild.test.mjs -- see that file's
# header for why 'node:fs'/'node:tty' are marked external and why
# that's inert in a real browser), serves the output from a page whose
# every HTTP response carries
#   Content-Security-Policy: script-src 'self'
# (no `unsafe-eval`, no `unsafe-inline`), and drives headless Chromium
# (Playwright) over it. The fixture writes its SELECT row count into
# `document.title`; this script asserts it reads "3" and that no
# `pageerror` or console error fired -- a `new Function(src)` eval
# blocked by this CSP throws exactly the kind of pageerror this script
# would catch, so a regression back to the old browser.js-only
# fetch+eval route (or any other CSP-incompatible code reachable from
# the bundler entry point) fails this script, not just a Node-side
# unit test.
#
# Same Playwright-resolution pattern as tests/web-demos/hub_browser_all.sh
# and tests/web-demos/browser_persistence_smoke.sh.
#
# Usage:
#   tests/web-demos/bundler_csp_smoke.sh
#   BUNDLER_CSP_SMOKE_PORT=8935 tests/web-demos/bundler_csp_smoke.sh
#
# Requirements: node >= 20, esbuild resolvable from npm/factoidal
# (devDependency -- `npm install` there if missing), the `playwright`
# package with Chromium provisioned (do NOT run `playwright install`;
# see hub_browser_all.sh's header for the resolution order this one
# mirrors).
#
# Exit code: 0 pass; 1 fail (a real regression -- see the printed
# reason); 2 a required tool/artifact is missing (also printed, with
# which one).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

PKG_DIR="$REPO_ROOT/npm/factoidal"

command -v node >/dev/null 2>&1 || { echo "Missing node" >&2; exit 2; }

if ! node -e "require.resolve('esbuild', {paths:['$PKG_DIR']})" >/dev/null 2>&1; then
  echo "Missing esbuild in $PKG_DIR/node_modules -- run 'npm install' in $PKG_DIR first (it is a devDependency, package.json + package-lock.json are committed)." >&2
  exit 2
fi

PLAYWRIGHT_PKG_DIR="${PLAYWRIGHT_PKG:-/opt/node22/lib/node_modules/playwright}"
if [ -d "$PLAYWRIGHT_PKG_DIR" ]; then
  # Directory imports aren't valid ESM specifiers -- point at the
  # package's own ESM entry (package.json "exports"."."."import").
  PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_PKG_DIR/index.mjs"
else
  if ! node -e "require.resolve('playwright')" >/dev/null 2>&1; then
    echo "Missing playwright (looked in \$PLAYWRIGHT_PKG_DIR=$PLAYWRIGHT_PKG_DIR and node's module path)." >&2
    exit 2
  fi
  PLAYWRIGHT_IMPORT_SPEC="playwright"
fi

for f in \
  "$PKG_DIR/api.js" "$PKG_DIR/api.mjs" \
  "$PKG_DIR/factoidal-npm-entry.js" \
  "$PKG_DIR/test/fixtures/bundler-app.mjs"
do
  [ -f "$f" ] || { echo "Missing $f" >&2; exit 2; }
done

WORKDIR="$(mktemp -d)"
HTTP_PID=""
cleanup() {
  [ -n "$HTTP_PID" ] && kill "$HTTP_PID" >/dev/null 2>&1 || true
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

PORT="${BUNDLER_CSP_SMOKE_PORT:-8935}"
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"

cat >"$SERVE_ROOT/index.html" <<'HTML_EOF'
<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <title>loading</title>
</head>
<body>
  <script type="module" src="./app.js"></script>
</body>
</html>
HTML_EOF

DRIVER_PATH="$WORKDIR/driver.mjs"
cat >"$DRIVER_PATH" <<'DRIVER_EOF'
// Node driver for tests/web-demos/bundler_csp_smoke.sh (written to a
// temp file by the shell script -- not meant to be run standalone).
// Configuration comes from environment variables the shell script
// sets, so nothing here depends on shell string interpolation.
import { createRequire } from 'node:module';
import { readFileSync, mkdirSync, rmSync, existsSync, lstatSync, realpathSync, symlinkSync } from 'node:fs';
import { createServer } from 'node:http';
import path from 'node:path';

const PKG_DIR = process.env.PKG_DIR;
const SERVE_ROOT = process.env.SERVE_ROOT;
const PORT = Number(process.env.BUNDLER_CSP_SMOKE_PORT_RESOLVED);

const require = createRequire(path.join(PKG_DIR, 'package.json'));
const esbuild = require('esbuild');

// esbuild resolves the fixture's '@factoidal/core/...' imports by
// walking up from the fixture file's directory looking for
// node_modules/@factoidal/core -- a self-referencing symlink to the
// package root (same trick npm/factoidal/test/bundler-esbuild.test.mjs
// uses) makes that resolve exactly as it would for a real consumer
// that ran `npm install @factoidal/core`, with no esbuild `alias`.
function ensureSelfSymlink() {
  const scopeDir = path.join(PKG_DIR, 'node_modules', '@factoidal');
  const linkPath = path.join(scopeDir, 'core');
  mkdirSync(scopeDir, { recursive: true });
  const already = existsSync(linkPath) &&
    lstatSync(linkPath).isSymbolicLink() &&
    realpathSync(linkPath) === realpathSync(PKG_DIR);
  if (already) return;
  rmSync(linkPath, { recursive: true, force: true });
  symlinkSync(PKG_DIR, linkPath, 'dir');
}
ensureSelfSymlink();

// --- 1. bundle the fixture (same approach as
//        npm/factoidal/test/bundler-esbuild.test.mjs; see that file's
//        header for why these specific Node built-ins need `external`
//        and why that's inert in a real browser) ---------------------

const FIXTURE = path.join(PKG_DIR, 'test', 'fixtures', 'bundler-app.mjs');
const OUTFILE = path.join(SERVE_ROOT, 'app.js');

function unresolvedSpecifiers(esbuildError) {
  const specs = new Set();
  for (const err of (esbuildError && esbuildError.errors) || []) {
    const m = /Could not resolve "([^"]+)"/.exec(err.text || '');
    if (m) specs.add(m[1]);
  }
  return [...specs];
}

const baseOptions = {
  entryPoints: [FIXTURE],
  outfile: OUTFILE,
  bundle: true,
  platform: 'browser',
  format: 'esm',
  write: true,
  logLevel: 'silent',
};

let externalList = [];
const t0 = Date.now();
try {
  await esbuild.build(baseOptions);
} catch (firstError) {
  externalList = unresolvedSpecifiers(firstError);
  if (externalList.length === 0) {
    console.error('esbuild build failed with no "Could not resolve" specifiers to mark external:');
    console.error(firstError && firstError.message);
    process.exit(1);
  }
  await esbuild.build({ ...baseOptions, external: externalList });
}
console.log(`bundler_csp_smoke: esbuild bundle ${Date.now() - t0}ms, external=[${externalList.join(', ')}]`);

// --- 2. serve SERVE_ROOT with a strict CSP on every response --------

const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript' };

const server = createServer((req, res) => {
  const urlPath = (req.url === '/' ? '/index.html' : req.url).split('?')[0];
  const filePath = path.join(SERVE_ROOT, decodeURIComponent(urlPath));
  if (!filePath.startsWith(SERVE_ROOT)) {
    res.writeHead(403).end();
    return;
  }
  let body;
  try {
    body = readFileSync(filePath);
  } catch (_e) {
    res.writeHead(404, { 'Content-Security-Policy': "script-src 'self'" }).end('not found');
    return;
  }
  const ext = path.extname(filePath);
  res.writeHead(200, {
    'Content-Type': (MIME[ext] || 'application/octet-stream') + '; charset=utf-8',
    // The whole point of this harness: no 'unsafe-eval', no
    // 'unsafe-inline' -- a fetch()+new Function(src) eval anywhere on
    // the page's script path is refused by exactly this header.
    'Content-Security-Policy': "script-src 'self'",
  });
  res.end(body);
});

await new Promise((resolve, reject) => {
  server.on('error', reject);
  server.listen(PORT, '127.0.0.1', resolve);
});
console.log(`bundler_csp_smoke: serving ${SERVE_ROOT} on http://127.0.0.1:${PORT}/ with CSP script-src 'self'`);

// --- 3. drive headless Chromium --------------------------------------

let chromium;
try {
  ({ chromium } = await import(process.env.PLAYWRIGHT_IMPORT_SPEC));
} catch (e) {
  console.error('bundler_csp_smoke: could not import Playwright:', e.message);
  server.close();
  process.exit(2);
}

let browser;
try {
  browser = await chromium.launch({ args: ['--disable-gpu', '--no-sandbox'] });
} catch (e) {
  console.error('bundler_csp_smoke: Chromium failed to launch (environment issue, not a code regression):', e.message);
  server.close();
  process.exit(2);
}

const page = await browser.newPage();
const pageErrors = [];
const consoleErrors = [];
page.on('pageerror', (err) => pageErrors.push(err.message));
page.on('console', (msg) => { if (msg.type() === 'error') consoleErrors.push(msg.text()); });

let failReason = null;
try {
  const resp = await page.goto(`http://127.0.0.1:${PORT}/index.html`, {
    waitUntil: 'networkidle',
    timeout: 20000,
  });
  const csp = resp && resp.headers()['content-security-policy'];
  if (csp !== "script-src 'self'") {
    failReason = `served page's Content-Security-Policy header was ${JSON.stringify(csp)}, expected "script-src 'self'"`;
  }

  if (!failReason) {
    const settle = await page.waitForFunction(
      () => document.title !== 'loading',
      { timeout: 15000 }
    ).then(() => true).catch(() => false);
    if (!settle) {
      failReason = `document.title never left "loading" within 15000ms (current: ${await page.title()})`;
    }
  }

  if (!failReason) {
    const title = await page.title();
    if (title !== '3') {
      failReason = `document.title was ${JSON.stringify(title)}, expected "3" (the fixture's three-row SELECT)`;
    }
  }
} catch (e) {
  failReason = `page.goto/evaluate failed: ${e.message}`;
}

if (!failReason && pageErrors.length > 0) {
  failReason = `pageerror: ${pageErrors[0]}`;
}
if (!failReason && consoleErrors.length > 0) {
  failReason = `console.error: ${consoleErrors[0]}`;
}

await page.close({ runBeforeUnload: false }).catch(() => {});
await browser.close().catch(() => {});
server.close();

if (failReason) {
  console.log(`FAIL bundler_csp_smoke: ${failReason}`);
  if (pageErrors.length > 0) console.log(`  all pageerrors: ${JSON.stringify(pageErrors)}`);
  if (consoleErrors.length > 0) console.log(`  all console errors: ${JSON.stringify(consoleErrors)}`);
  process.exit(1);
}

console.log('PASS bundler_csp_smoke: document.title === "3" under Content-Security-Policy: script-src \'self\', no pageerror, no console error');
process.exit(0);
DRIVER_EOF

DRIVER_RC=0
PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_IMPORT_SPEC" \
PKG_DIR="$PKG_DIR" \
SERVE_ROOT="$SERVE_ROOT" \
BUNDLER_CSP_SMOKE_PORT_RESOLVED="$PORT" \
  timeout 120 node "$DRIVER_PATH" || DRIVER_RC=$?

exit "$DRIVER_RC"
