#!/usr/bin/env bash
# tests/web-demos/browser_persistence_smoke.sh
#
# Headless-Chromium proof for issue #282's browser-persistence
# prototype (docs/designissues/2026-07-06-browser-persistence.md):
# drives npm/factoidal/browser.js's deltaLogOpen/deltaLogAppend/
# deltaLogMerge (IndexedDB-backed) through a REAL page navigation
# (page.reload(), not an in-page state reset) to prove the durable-
# UPDATE claim -- "parse data, apply an update, persist the delta
# entries, reload the page, read the log back, merge-on-read
# reproduces the updated dataset" -- against real browser storage, not
# a mock. Also drives a torn-write simulation: directly corrupt the
# most recently written IndexedDB record and confirm parse_delta_batch's
# checksum framing causes it to be skipped (the clean prefix survives,
# the corrupt entry never appears, never a partial/garbage decode).
#
# Same Playwright-resolution pattern as tests/web-demos/hub_posts_smoke.sh
# (this script does not need Eleventy -- there is no site build here,
# just a static test fixture served over python3 -m http.server).
#
# Usage:
#   tests/web-demos/browser_persistence_smoke.sh
#
# Requirements: node >= 20, the `playwright` package with Chromium
# installed, and docs/fstar-extracted/factoidal-npm-entry.js (or
# npm/factoidal/factoidal-npm-entry.js) built with the deltaBatchToHex/
# deltaMergeApplyBrowser exports (formal/fstar/build-ocaml.sh's js step,
# after bin/npm-entry/entry_jsoo.ml gained those exports).
#
# Exit code: 0 iff every check below passes; non-zero otherwise.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

WORKDIR="$(mktemp -d)"
HTTP_PID=""
cleanup() {
  [ -n "$HTTP_PID" ] && kill "$HTTP_PID" >/dev/null 2>&1 || true
  rm -rf "$WORKDIR"
}
trap cleanup EXIT

PLAYWRIGHT_PKG_DIR="${PLAYWRIGHT_PKG:-/opt/node22/lib/node_modules/playwright}"
if [ -d "$PLAYWRIGHT_PKG_DIR" ]; then
  PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_PKG_DIR/index.mjs"
else
  if ! node -e "require.resolve('playwright')" >/dev/null 2>&1; then
    echo "Missing playwright (looked in \$PLAYWRIGHT_PKG_DIR=$PLAYWRIGHT_PKG_DIR and node's module path)." >&2
    exit 2
  fi
  PLAYWRIGHT_IMPORT_SPEC="playwright"
fi

ENTRY_CANDIDATES=(
  "docs/npm/foafos/factoidal-npm-entry.js"
  "docs/fstar-extracted/factoidal-npm-entry.js"
  "npm/factoidal/factoidal-npm-entry.js"
)
FOUND_ENTRY=""
for c in "${ENTRY_CANDIDATES[@]}"; do
  if [ -f "$c" ]; then FOUND_ENTRY="$c"; break; fi
done
if [ -z "$FOUND_ENTRY" ]; then
  echo "Missing factoidal-npm-entry.js in any of: ${ENTRY_CANDIDATES[*]}" >&2
  echo "Run formal/fstar/build-ocaml.sh's js step (then npm) first." >&2
  exit 2
fi
echo "Using npm-entry bundle: $FOUND_ENTRY"

SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
cp npm/factoidal/browser.js "$SERVE_ROOT/browser.js"
cp "$FOUND_ENTRY" "$SERVE_ROOT/factoidal-npm-entry.js"
cp tests/web-demos/browser-persistence-test.html "$SERVE_ROOT/index.html"

PORT="${BROWSER_PERSISTENCE_SMOKE_PORT:-8933}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/index.html" 2>/dev/null && break
  sleep 0.2
done

timeout 120 node --input-type=module -e "
import { chromium } from '$PLAYWRIGHT_IMPORT_SPEC';

const PORT = $PORT;
const url = 'http://127.0.0.1:' + PORT + '/index.html';
const DB_NAME = 'browser-persistence-smoke-db';

let failures = 0;
function check(label, cond) {
  if (cond) { console.log('  PASS  ' + label); }
  else { console.log('  FAIL  ' + label); failures++; }
}

const browser = await chromium.launch();
const page = await browser.newPage();
const consoleMsgs = [];
page.on('console', (msg) => consoleMsgs.push('[console:' + msg.type() + '] ' + msg.text()));
page.on('pageerror', (err) => consoleMsgs.push('[pageerror] ' + err.message));

console.log('--- loading fixture: ' + url + ' ---');
await page.goto(url, { waitUntil: 'networkidle' });
await page.waitForFunction(() => window.__factoidalBrowserPersistenceReady === true, { timeout: 15000 });

// Start from a clean database every run (idempotent -- deltaLogDestroy
// on a nonexistent db is a no-op).
await page.evaluate(async (dbName) => {
  const F = window.__factoidalBrowserPersistence;
  await F.deltaLogDestroy({ dbName }).catch(() => {});
}, DB_NAME);

console.log('--- phase 1: open + append 3 batches (INSERT DATA, DELETE+INSERT, CREATE+INSERT-into-new-graph) ---');
const appendResults = await page.evaluate(async (dbName) => {
  const F = window.__factoidalBrowserPersistence;
  const handle = await F.deltaLogOpen(dbName);
  const r0 = await F.deltaLogAppend(handle,
    'INSERT DATA { <urn:x:a> <urn:x:p> <urn:x:v1> . <urn:x:b> <urn:x:p> <urn:x:v2> . }');
  const r1 = await F.deltaLogAppend(handle,
    'DELETE DATA { <urn:x:b> <urn:x:p> <urn:x:v2> . } ; INSERT DATA { <urn:x:c> <urn:x:p> <urn:x:v3> . }');
  const r2 = await F.deltaLogAppend(handle,
    'CREATE GRAPH <urn:x:g1> ; INSERT DATA { GRAPH <urn:x:g1> { <urn:x:d> <urn:x:p> <urn:x:v4> } }');
  return [r0, r1, r2];
}, DB_NAME);

check('batch 0 seq === 0', appendResults[0].seq === 0);
check('batch 0 opCount === 2 (two ADDs)', appendResults[0].opCount === 2);
check('batch 1 seq === 1', appendResults[1].seq === 1);
check('batch 1 opCount === 2 (one REMOVE + one ADD)', appendResults[1].opCount === 2);
check('batch 2 seq === 2', appendResults[2].seq === 2);
check('batch 2 opCount === 2 (CREATE + ADD-into-new-graph)', appendResults[2].opCount === 2);

console.log('--- phase 2: merge BEFORE reload ---');
const mergedBefore = await page.evaluate(async (dbName) => {
  const F = window.__factoidalBrowserPersistence;
  return await F.deltaLogMerge({ dbName }, '');
}, DB_NAME);
console.log('  merged (before reload):\n' + mergedBefore.split('\n').map((l) => '    ' + l).join('\n'));

check('contains <urn:x:a> <urn:x:p> <urn:x:v1>', /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/.test(mergedBefore));
check('contains <urn:x:c> <urn:x:p> <urn:x:v3>', /<urn:x:c>\s+<urn:x:p>\s+<urn:x:v3>/.test(mergedBefore));
check('does NOT contain <urn:x:b> (tombstoned by DELETE DATA)', !/<urn:x:b>/.test(mergedBefore));
check('contains <urn:x:d> <urn:x:p> <urn:x:v4> in urn:x:g1', /<urn:x:d>\s+<urn:x:p>\s+<urn:x:v4>\s+<urn:x:g1>/.test(mergedBefore));

console.log('--- phase 3: REAL page.reload() (the persistence claim) ---');
await page.reload({ waitUntil: 'networkidle' });
await page.waitForFunction(() => window.__factoidalBrowserPersistenceReady === true, { timeout: 15000 });

const mergedAfter = await page.evaluate(async (dbName) => {
  const F = window.__factoidalBrowserPersistence;
  return await F.deltaLogMerge({ dbName }, '');
}, DB_NAME);

check('merge AFTER reload is byte-identical to BEFORE reload (survived real navigation)',
  mergedAfter === mergedBefore);
check('(after reload) still contains <urn:x:a> ... <urn:x:v1>', /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/.test(mergedAfter));
check('(after reload) still contains <urn:x:d> ... <urn:x:v4> in urn:x:g1', /<urn:x:d>\s+<urn:x:p>\s+<urn:x:v4>\s+<urn:x:g1>/.test(mergedAfter));

console.log('--- phase 4: torn-write simulation (corrupt the last record, batch 2) ---');
const corrupted = await page.evaluate(async (dbName) => {
  const F = window.__factoidalBrowserPersistence;
  return await F._deltaLogCorruptLastForTest({ dbName });
}, DB_NAME);
check('corrupt-for-test found a record to truncate', corrupted === true);

const mergedAfterCorrupt = await page.evaluate(async (dbName) => {
  const F = window.__factoidalBrowserPersistence;
  return await F.deltaLogMerge({ dbName }, '');
}, DB_NAME);
console.log('  merged (after corrupting batch 2):\n' + mergedAfterCorrupt.split('\n').map((l) => '    ' + l).join('\n'));

check('clean prefix survives: still contains <urn:x:a> ... <urn:x:v1>',
  /<urn:x:a>\s+<urn:x:p>\s+<urn:x:v1>/.test(mergedAfterCorrupt));
check('clean prefix survives: still contains <urn:x:c> ... <urn:x:v3>',
  /<urn:x:c>\s+<urn:x:p>\s+<urn:x:v3>/.test(mergedAfterCorrupt));
check('corrupt batch never partially applied: <urn:x:g1> graph is entirely absent',
  !/<urn:x:g1>/.test(mergedAfterCorrupt));
check('corrupt batch never partially applied: <urn:x:d> is entirely absent',
  !/<urn:x:d>/.test(mergedAfterCorrupt));
check('output changed relative to the pre-corruption merge (corruption had an effect)',
  mergedAfterCorrupt !== mergedAfter);

if (failures > 0) {
  console.log('console log:\n' + consoleMsgs.join('\n'));
}

await page.evaluate(async (dbName) => {
  const F = window.__factoidalBrowserPersistence;
  await F.deltaLogDestroy({ dbName }).catch(() => {});
}, DB_NAME);

await browser.close();

console.log('===');
if (failures === 0) {
  console.log('browser persistence smoke: ALL PASS');
  process.exit(0);
} else {
  console.log('browser persistence smoke: ' + failures + ' FAILURE(S)');
  process.exit(1);
}
"
