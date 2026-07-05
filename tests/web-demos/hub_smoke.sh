#!/usr/bin/env bash
# tests/web-demos/hub_smoke.sh
#
# Smoke test for the documentation-hub scaffold
# (docs/_includes/hub.njk + docs/web/hub/index.md): builds the site
# offline with the vendored Eleventy (third_party/eleventy/), serves
# the built _site under its real /factoidal/ pathPrefix, and drives
# headless Chromium (Playwright) to confirm:
#
#   1. The page loads the vendored Observable runtime + inspector +
#      stdlib + Plot + d3 bundles (third_party/observable/) and the
#      npm package mirror (docs/npm/foafos/) all same-origin, no CDN.
#   2. The ` ```observable-js ` fenced-block convention actually
#      mounts a live cell (docs/_includes/hub.njk's mountCell()).
#   3. That cell calls Factoidal.query() (the npm module, driving the
#      real F*-extracted engine compiled to JS) and the Inspector
#      renders the computed value.
#
# A pass here is evidence the whole chain the hub scaffold depends on
# works end to end: vendored-Eleventy build -> vendored-Observable
# runtime -> fenced-block convention -> npm-packaged engine.
#
# Usage:
#   tests/web-demos/hub_smoke.sh
#
# Requirements: node >= 20, the `playwright` package with Chromium
# installed (already provisioned in this environment; see
# tests/web-demos/README.md's "Why not just Playwright..." note for
# why this is the one demo test that DOES drive a real headless
# browser -- the hub scaffold's whole point is the in-page Observable
# runtime, which has no meaningful non-browser equivalent to test
# against, unlike the engine-parity tests in this directory).
#
# Exit code: 0 iff the site builds and the live cell renders the
# expected computed value; non-zero otherwise.

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
  # Directory imports aren't valid ESM specifiers -- point at the
  # package's own ESM entry (package.json "exports"."."."import").
  PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_PKG_DIR/index.mjs"
else
  # Fall back to whatever node's own module resolution can find.
  if ! node -e "require.resolve('playwright')" >/dev/null 2>&1; then
    echo "Missing playwright (looked in \$PLAYWRIGHT_PKG_DIR=$PLAYWRIGHT_PKG_DIR and node's module path)." >&2
    exit 2
  fi
  PLAYWRIGHT_IMPORT_SPEC="playwright"
fi

for f in third_party/eleventy/npm-cache third_party/observable/dist/runtime.esm.js docs/npm/foafos/browser.js; do
  [ -e "$f" ] || { echo "Missing $f -- run the vendoring steps first (see third_party/eleventy/README.md, third_party/observable/README.md)." >&2; exit 2; }
done

echo "== Installing vendored Eleventy offline (third_party/eleventy/install.sh) =="
third_party/eleventy/install.sh docs

echo "== Building docs/ site (npx @11ty/eleventy --output=_site) =="
BUILD_LOG="$WORKDIR/build.log"
BUILD_RC=0
( cd docs && rm -rf _site && npx @11ty/eleventy --output=_site ) >"$BUILD_LOG" 2>&1 || BUILD_RC=$?
tail -n 20 "$BUILD_LOG"

SITE_DIR="$REPO_ROOT/docs/_site"
if [ "$BUILD_RC" -ne 0 ]; then
  if grep -q "2026-07-05-csvw-program-plan.md" "$BUILD_LOG"; then
    # Known, pre-existing, out-of-territory defect (as of 2026-07-05):
    # that design doc's prose contains `{#fragment}` examples that
    # Nunjucks's markdown template engine parses as an unterminated
    # `{# comment #}` tag, failing the WHOLE site build (Eleventy has
    # no per-template isolation). Not introduced by, or fixable from,
    # this hub scaffold -- it's the CSVW work's file. Fall back to an
    # isolated copy of docs/ with only that one file's `{#...}`
    # examples defused, so this test still verifies the hub scaffold
    # rather than failing on an unrelated doc typo. Remove this
    # fallback once the CSVW doc is fixed upstream.
    echo "NOTE: full docs/ build failed on the known CSVW Nunjucks-comment defect (see build log above); falling back to an isolated copy to still verify the hub scaffold." >&2
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

[ -f "$SITE_DIR/web/hub/index.html" ] || { echo "FAIL: $SITE_DIR/web/hub/index.html was not produced." >&2; exit 1; }
[ -f "$SITE_DIR/vendor/observable/runtime.esm.js" ] || { echo "FAIL: vendored Observable runtime did not land in _site (passthrough copy misconfigured?)." >&2; exit 1; }

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_SMOKE_PORT:-8931}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

# Wait for the server to come up (cap at 10s, per anti-pattern #17 --
# never let an ad-hoc wait hang unbounded).
for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/" 2>/dev/null && break
  sleep 0.2
done

timeout 60 node --input-type=module -e "
import { chromium } from '$PLAYWRIGHT_IMPORT_SPEC';

const browser = await chromium.launch();
const page = await browser.newPage();
const consoleMsgs = [];
page.on('console', (msg) => consoleMsgs.push('[console:' + msg.type() + '] ' + msg.text()));
page.on('pageerror', (err) => consoleMsgs.push('[pageerror] ' + err.message));

await page.goto('http://127.0.0.1:$PORT/factoidal/web/hub/', { waitUntil: 'networkidle' });

let failures = 0;
function check(label, cond) {
  if (cond) { console.log('  PASS  ' + label); }
  else { console.log('  FAIL  ' + label); failures++; }
}

try {
  await page.waitForSelector('.observable-cell', { timeout: 8000 });
} catch (e) {
  console.log('No .observable-cell mounted. Console log:\n' + consoleMsgs.join('\n'));
  await browser.close();
  process.exit(1);
}
check('observable-cell div mounted (fenced-block convention wired up)', true);

try {
  await page.waitForFunction(() => {
    const el = document.querySelector('.observable-cell');
    return el && el.textContent && el.textContent.trim().length > 0;
  }, { timeout: 15000 });
} catch (e) {
  console.log('Cell never produced output. Console log:\n' + consoleMsgs.join('\n'));
  await browser.close();
  process.exit(1);
}

const cellText = await page.\$eval('.observable-cell', (el) => el.textContent.trim());
const cellClass = await page.\$eval('.observable-cell', (el) => el.className);
console.log('  cell output: ' + cellText);

check('cell did not error', !cellClass.includes('observable-cell-error'));
check('cell computed the expected value via Factoidal.query()',
  cellText.includes('hub scaffold smoke test: 1 binding(s), o = 42'));

await browser.close();

console.log('===');
if (failures === 0) {
  console.log('hub smoke: ALL PASS');
  process.exit(0);
} else {
  console.log('hub smoke: ' + failures + ' FAILURE(S)');
  process.exit(1);
}
"
