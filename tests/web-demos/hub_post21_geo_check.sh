#!/usr/bin/env bash
# tests/web-demos/hub_post21_geo_check.sh
#
# Headless-Chromium checks for task #105 (GeoSPARQL map fix + fullscreen
# + live-mode hub twin): builds the site offline with the vendored
# Eleventy, serves it under /factoidal/, and drives Playwright over
# BOTH docs/web/hub/21-geosparql-geometry-and-topology.md (the strict
# page) and its auto-generated docs/web/hub-live/21-.../ twin
# (docs/web/hub-live.11ty.js). Sibling to hub_browser_all.sh (every
# post, shallow pageerror/rejected-cell check only) and
# hub_posts_smoke.sh (posts 01-18, viewport/interaction checks) -- this
# script is the one place post 21's map gets asserted on structurally:
# the vendored vector basemap actually rendered, the fullscreen
# control exists, and -- the check those two broader harnesses cannot
# do -- that the STRICT page never attempts a single non-localhost
# network request, proving the CSP-driven "no tile host" design
# decision documented in the post's own prose actually holds at
# runtime, not just in the CSP string.
#
# Checks:
#   STRICT page (web/hub/21-.../):
#     1. Zero pageerror / console.error events.
#     2. No cell ends in the Inspector's REJECTED (observable-cell-error)
#        state.
#     3. At least 20 SVG <path> elements inside .hub-leaflet-map (the
#        33-borough choropleth + the Thames line render as real vector
#        paths, not a blank background) -- "borough count > 20" per
#        task #105.
#     4. The custom fullscreen control (.leaflet-control-hub-fullscreen)
#        is present in the DOM.
#     5. NO request during the whole page lifecycle (via Playwright
#        request interception, not just a post-hoc network log) targets
#        a host other than the local test server -- the CSP's
#        `img-src`/`connect-src 'self'` claim, verified at the network
#        layer, not just read off the meta tag.
#
#   LIVE page (web/hub-live/21-.../):
#     6. Page loads with zero pageerror events (console.error is not
#        gated here -- a live-mode tile/endpoint request MAY fail in a
#        network-less CI sandbox, and that failure is expected/allowed,
#        not a regression; pageerror still gates because an uncaught
#        JS exception is never expected regardless of network).
#     7. The live-mode banner (.hub-live-banner) is present and its
#        text contains "Live mode".
#     8. `window.__hubLiveTileLayer` exists (the map cell's own
#        data-hub-mode="live" branch created a real L.tileLayer
#        instance) -- proven WITHOUT asserting any tile was actually
#        fetched (CI has no network guarantee; requests to
#        tile.openstreetmap.org are intercepted and answered locally
#        below so this script never depends on or waits for real
#        network I/O).
#
# Usage:
#   tests/web-demos/hub_post21_geo_check.sh
#   HUB_POST21_GEO_CHECK_PORT=8941 tests/web-demos/hub_post21_geo_check.sh
#
# Requirements: same as hub_browser_all.sh / hub_posts_smoke.sh -- node
# >= 20, the vendored Playwright package with Chromium already
# provisioned.
#
# Exit code: 0 iff every check above passes; non-zero otherwise.
# Wall-clock capped at 10 minutes (anti-pattern #17).

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

for f in third_party/eleventy/npm-cache third_party/observable/dist/runtime.esm.js docs/npm/factoidal/browser.js docs/web/hub/assets/geo/london-boroughs.geojson; do
  [ -e "$f" ] || { echo "Missing $f -- run the vendoring steps first." >&2; exit 2; }
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
    # Same known, pre-existing, out-of-territory defect hub_smoke.sh /
    # hub_posts_smoke.sh already work around -- see their headers.
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

STRICT_PAGE="$SITE_DIR/web/hub/21-geosparql-geometry-and-topology/index.html"
LIVE_PAGE="$SITE_DIR/web/hub-live/21-geosparql-geometry-and-topology/index.html"
[ -f "$STRICT_PAGE" ] || { echo "FAIL: $STRICT_PAGE was not produced." >&2; exit 1; }
[ -f "$LIVE_PAGE" ] || { echo "FAIL: $LIVE_PAGE was not produced -- web/hub-live.11ty.js's pagination over collections.hubPosts did not include post 21." >&2; exit 1; }

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_POST21_GEO_CHECK_PORT:-8941}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/21-geosparql-geometry-and-topology/" 2>/dev/null && break
  sleep 0.2
done

DRIVER_PATH="$WORKDIR/driver.mjs"
cat >"$DRIVER_PATH" <<'DRIVER_EOF'
const { chromium } = await import(process.env.PLAYWRIGHT_IMPORT_SPEC);
const PORT = process.env.HUB_POST21_PORT_RESOLVED;
const BASE = `http://127.0.0.1:${PORT}/factoidal`;

let failures = 0;
function check(label, ok) {
  console.log((ok ? 'PASS' : 'FAIL') + ' -- ' + label);
  if (!ok) failures++;
}

const browser = await chromium.launch({ args: ['--disable-gpu', '--no-sandbox'] });

async function waitForCellsSettled(page) {
  await page.waitForFunction(() => {
    const cells = [...document.querySelectorAll('.observable-cell')];
    return cells.length === 0 || cells.every((c) => c.textContent && c.textContent.trim().length > 0);
  }, { timeout: 25000 });
}

// --- STRICT page ------------------------------------------------------
{
  const page = await browser.newPage();
  const pageErrors = [];
  const consoleErrors = [];
  const externalRequests = [];
  page.on('pageerror', (err) => pageErrors.push(err.message));
  page.on('console', (msg) => { if (msg.type() === 'error') consoleErrors.push(msg.text()); });
  // Request interception (not a post-hoc network log): every request
  // this page's lifecycle makes is inspected BEFORE it leaves the
  // browser process. Anything not aimed at our own local test server
  // is recorded as a CSP-policy violation and aborted -- so this check
  // can never pass by accident just because the sandbox has no network
  // route to the outside world anyway.
  await page.route('**/*', (route) => {
    const url = new URL(route.request().url());
    if (url.hostname !== '127.0.0.1') {
      externalRequests.push(route.request().url());
      return route.abort();
    }
    return route.continue();
  });

  await page.goto(`${BASE}/web/hub/21-geosparql-geometry-and-topology/`, { waitUntil: 'networkidle', timeout: 30000 });
  await waitForCellsSettled(page);

  const rejectedCells = await page.$$eval('.observable-cell', (els) =>
    els.filter((e) => e.classList.contains('observable-cell-error')).map((e) => e.textContent.slice(0, 200))
  );
  const pathCount = await page.$$eval('.hub-leaflet-map svg path', (els) => els.length);
  const fullscreenControlPresent = (await page.$('.leaflet-control-hub-fullscreen')) !== null;

  check('strict: zero pageerror events', pageErrors.length === 0);
  if (pageErrors.length) console.log('  pageerrors: ' + pageErrors.join(' | '));
  check('strict: zero console.error events', consoleErrors.length === 0);
  if (consoleErrors.length) console.log('  console.error: ' + consoleErrors.join(' | '));
  check('strict: zero rejected (.observable-cell-error) cells', rejectedCells.length === 0);
  if (rejectedCells.length) console.log('  rejected: ' + rejectedCells.join(' | '));
  check(`strict: base-layer SVG path count > 20 (got ${pathCount})`, pathCount > 20);
  check('strict: fullscreen control (.leaflet-control-hub-fullscreen) present', fullscreenControlPresent);
  check(`strict: zero non-localhost requests attempted (got ${externalRequests.length})`, externalRequests.length === 0);
  if (externalRequests.length) console.log('  external requests: ' + externalRequests.join(' | '));

  await page.close();
}

// --- LIVE page ----------------------------------------------------------
{
  const page = await browser.newPage();
  const pageErrors = [];
  page.on('pageerror', (err) => pageErrors.push(err.message));
  // Live mode MAY attempt a real OSM tile / remote-endpoint request --
  // that's the whole point of the mode. This script has no network
  // guarantee (and shouldn't burn CI time waiting for one), so any
  // request to a non-local host is given an immediate, harmless 204
  // response rather than left to hang or hit the real internet. This
  // is NOT the same assertion as the strict page's check above (which
  // records and FAILS on such a request) -- see the task's own
  // instruction: "do NOT assert tiles fetched -- CI has no network
  // guarantee."
  await page.route('**/*', (route) => {
    const url = new URL(route.request().url());
    if (url.hostname !== '127.0.0.1') return route.fulfill({ status: 204, body: '' });
    return route.continue();
  });

  await page.goto(`${BASE}/web/hub-live/21-geosparql-geometry-and-topology/`, { waitUntil: 'networkidle', timeout: 30000 });
  await waitForCellsSettled(page);

  const bannerText = await page.$eval('.hub-live-banner', (el) => el.textContent).catch(() => null);
  const bodyMode = await page.evaluate(() => document.body.getAttribute('data-hub-mode'));
  const hasTileLayer = await page.evaluate(() => !!window.__hubLiveTileLayer);

  check('live: zero pageerror events', pageErrors.length === 0);
  if (pageErrors.length) console.log('  pageerrors: ' + pageErrors.join(' | '));
  check('live: page loads (title/body reachable)', bodyMode !== null);
  check('live: data-hub-mode="live" on <body>', bodyMode === 'live');
  check('live: banner (.hub-live-banner) present', bannerText !== null);
  check('live: banner text contains "Live mode"', !!(bannerText && bannerText.includes('Live mode')));
  check('live: window.__hubLiveTileLayer created (tile layer OBJECT, not a fetched tile)', hasTileLayer);

  await page.close();
}

await browser.close();

console.log('===');
console.log(`hub_post21_geo_check: ${failures === 0 ? 'ALL PASS' : failures + ' FAILURE(S)'}`);
process.exit(failures === 0 ? 0 : 1);
DRIVER_EOF

DRIVER_RC=0
PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_IMPORT_SPEC" \
HUB_POST21_PORT_RESOLVED="$PORT" \
  timeout 120 node "$DRIVER_PATH" || DRIVER_RC=$?

exit "$DRIVER_RC"
