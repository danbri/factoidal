#!/usr/bin/env bash
# tests/web-demos/hub_post32_value_check.sh
#
# Headless-Chromium VALUE checks for docs/web/hub/32-this-answer-is-a-
# theorem.md (the certified rho-df closure post). Sibling to
# hub_browser_all.sh (every post, pageerror/rejected-cell detection
# only) and hub_post21_geo_check.sh (post 21's map structure) -- this
# script asserts what those cannot: the VALUES the post's cells
# compute in a real browser.
#
# Why value-level: post 32 shipped with two browser-only breakages the
# node suite (tests/hub/post32_test.mjs) could not see, because the
# node harness binds `fn` to the node npm package while the page binds
# it to docs/_includes/hub.njk's wrapper over docs/npm/factoidal/
# browser.js. Bug 1 (2026-08-07, owner-reported): fn.rhoDfFragmentCheck
# had no browser wrapper at all -- cell REJECTED, which
# hub_browser_all.sh would have caught had it been run before
# publishing. Bug 2 (2026-08-08, owner-reported): the browser wrappers
# passed raw Turtle to an ABI that parses N-Quads, so the closure
# SILENTLY succeeded over the empty graph -- every cell resolved, no
# rejection anywhere, and the page's theorem-backed ASK printed
# `false` where the prose promises `true`. Only a value assertion
# catches that class.
#
# Checks (strict page web/hub/32-this-answer-is-a-theorem/ only):
#   1. Zero pageerror events; zero rejected (.observable-cell-error)
#      cells.
#   2. Step 1: some cell output contains `"fragment": true` (the
#      fragment check really parsed the org graph -- an empty-graph
#      vacuous true is indistinguishable here, which is exactly why
#      check 3 exists).
#   3. Step 3: some cell output is exactly `true` (the ASK over the
#      certified closure -- the page's headline theorem answer; under
#      bug 2 this printed `false`).
#   4. The F-1 escape cell prints fragmentBefore true AND
#      fragmentAfter false (the counterexample really runs: closure
#      derived the bnode-object triple that leaves the fragment).
#   5. The perf cell's derivedTriples exceeds 1000 (the 60-class
#      chain's subclass closure is ~1891 triples; under bug 2 the
#      six-rule leg returned 0 lines and the owlClosure leg silently
#      closed the empty graph).
#
# Usage:
#   tests/web-demos/hub_post32_value_check.sh
#   HUB_POST32_VALUE_CHECK_PORT=8942 tests/web-demos/hub_post32_value_check.sh
#
# Requirements: same as hub_browser_all.sh -- node >= 20, Playwright
# with Chromium provisioned (vendored path or module path).
#
# Exit code: 0 iff every check passes; non-zero otherwise. Wall-clock
# capped by the driver's own per-step timeouts (anti-pattern #17).

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

for f in third_party/eleventy/npm-cache third_party/observable/dist/runtime.esm.js docs/npm/factoidal/browser.js docs/npm/factoidal/factoidal-npm-entry.js; do
  [ -e "$f" ] || { echo "Missing $f -- run the vendoring steps first." >&2; exit 2; }
done

echo "== Installing vendored Eleventy offline (third_party/eleventy/install.sh) =="
third_party/eleventy/install.sh docs

echo "== Building docs/ site (npx @11ty/eleventy --output=_site) =="
BUILD_LOG="$WORKDIR/build.log"
BUILD_RC=0
( cd docs && rm -rf _site && npx @11ty/eleventy --output=_site ) >"$BUILD_LOG" 2>&1 || BUILD_RC=$?
tail -n 10 "$BUILD_LOG"

SITE_DIR="$REPO_ROOT/docs/_site"
if [ "$BUILD_RC" -ne 0 ]; then
  if grep -q "2026-07-05-csvw-program-plan.md" "$BUILD_LOG"; then
    echo "NOTE: full docs/ build failed on the known CSVW Nunjucks-comment defect; falling back to an isolated copy." >&2
    ISO="$WORKDIR/docs-iso"
    mkdir -p "$ISO"
    rsync -a --exclude=node_modules --exclude=_site docs/ "$ISO/"
    ln -s "$REPO_ROOT/third_party" "$WORKDIR/third_party"
    sed -i -E 's/\{#([A-Za-z_]+)\}/[FRAGMENT \1]/g' \
      "$ISO/designissues/2026-07-05-csvw-program-plan.md"
    ( cd "$ISO" && rm -rf _site && "$REPO_ROOT/docs/node_modules/.bin/eleventy" --input=. --output=_site ) >>"$BUILD_LOG" 2>&1
    SITE_DIR="$ISO/_site"
  else
    echo "FAIL: docs/ build failed for a reason other than the known CSVW defect -- see log above." >&2
    exit 1
  fi
fi

PAGE="$SITE_DIR/web/hub/32-this-answer-is-a-theorem/index.html"
[ -f "$PAGE" ] || { echo "FAIL: $PAGE was not produced." >&2; exit 1; }

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_POST32_VALUE_CHECK_PORT:-8942}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/32-this-answer-is-a-theorem/" 2>/dev/null && break
  sleep 0.2
done

DRIVER_PATH="$WORKDIR/driver.mjs"
cat >"$DRIVER_PATH" <<'DRIVER_EOF'
const { chromium } = await import(process.env.PLAYWRIGHT_IMPORT_SPEC);
const PORT = process.env.HUB_POST32_PORT_RESOLVED;
const BASE = `http://127.0.0.1:${PORT}/factoidal`;

let failures = 0;
function check(label, ok) {
  console.log((ok ? 'PASS' : 'FAIL') + ' -- ' + label);
  if (!ok) failures++;
}

const browser = await chromium.launch({ args: ['--disable-gpu', '--no-sandbox'] });
const page = await browser.newPage();
const pageErrors = [];
page.on('pageerror', (err) => pageErrors.push(err.message));

await page.goto(`${BASE}/web/hub/32-this-answer-is-a-theorem/`, { waitUntil: 'networkidle', timeout: 30000 });

// The perf cell runs TWO closures over a 60-class chain through the js
// bundle -- give the cells a generous settle window before asserting.
await page.waitForFunction(() => {
  const cells = [...document.querySelectorAll('.observable-cell')];
  return cells.length > 0 && cells.every((c) => c.textContent && c.textContent.trim().length > 0);
}, { timeout: 120000 });

const cellTexts = await page.$$eval('.observable-cell', (els) => els.map((e) => e.textContent.trim()));
const rejected = await page.$$eval('.observable-cell', (els) =>
  els.filter((e) => e.classList.contains('observable-cell-error')).map((e) => e.textContent.slice(0, 200))
);

check('zero pageerror events', pageErrors.length === 0);
if (pageErrors.length) console.log('  pageerrors: ' + pageErrors.join(' | '));
check('zero rejected (.observable-cell-error) cells', rejected.length === 0);
if (rejected.length) console.log('  rejected: ' + rejected.join(' | '));

// pretty() renders plain objects as key/value TABLES, so the values
// are asserted row-wise, not as JSON text.
const tableRows = await page.$$eval('.observable-cell table tr', (trs) =>
  trs.map((tr) => [...tr.querySelectorAll('th,td')].map((c) => c.textContent.trim()))
);
const rowValue = (key) => {
  const row = tableRows.find((r) => r[0] === key);
  return row ? row[1] : undefined;
};

check('step 1: the fragment-check cell renders a `fragment -> true` row',
  rowValue('fragment') === 'true');

check('step 3: a cell output is exactly `true` (the theorem-backed ASK answer)',
  cellTexts.some((t) => t === 'true'));

check('F-1 escape cell: fragmentBefore true, fragmentAfter false',
  rowValue('fragmentBefore') === 'true' && rowValue('fragmentAfter') === 'false');

const derived = Number(rowValue('derivedTriples') ?? -1);
check(`perf cell: derivedTriples > 1000 (got ${derived})`,
  derived > 1000);

await browser.close();
console.log(failures === 0
  ? 'post32 value check: ALL PASS'
  : `post32 value check: ${failures} FAILURES`);
process.exit(failures === 0 ? 0 : 1);
DRIVER_EOF

DRIVER_RC=0
PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_IMPORT_SPEC" \
HUB_POST32_PORT_RESOLVED="$PORT" \
  node "$DRIVER_PATH" || DRIVER_RC=$?

echo "HUB_POST32_VALUE_CHECK_RC=$DRIVER_RC"
exit "$DRIVER_RC"
