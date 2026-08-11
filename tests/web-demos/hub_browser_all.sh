#!/usr/bin/env bash
# tests/web-demos/hub_browser_all.sh
#
# Headless-Chromium regression harness for EVERY documentation-hub post
# (docs/web/hub/NN-*.md, currently 30 of them): builds the site offline
# with the vendored Eleventy (third_party/eleventy/), serves the built
# _site under its real /factoidal/ pathPrefix, and drives headless
# Chromium (Playwright) over every post page in ONE browser instance
# (a fresh page per post) to catch browser-only cell regressions --
# the class of bug that is invisible to every node-side test because
# it only happens inside a real DOM/layout/GC environment. Two real
# examples that motivated this harness (task #84, tracks issue #245):
# post 21's Leaflet map threw "Cannot read properties of undefined
# (reading 'min')" from an async fitBounds call, and post 24's HDT
# reader turned out to make the tab unresponsive (fixed in F* by task
# #102's O(1) decoded-byte representation in HDT.Container; the
# allowlist entry it carried is gone) -- neither shows up under
# `node --test`.
#
# Sibling to tests/web-demos/hub_smoke.sh (the scaffold's own smoke
# cell) and tests/web-demos/hub_posts_smoke.sh (posts 01-18, mounted
# cells + mobile-viewport overflow check). This script is broader but
# shallower: EVERY post, but only pageerror/REJECTED-cell detection --
# no viewport/interaction checks (those stay hub_posts_smoke.sh's job).
#
# SCOPE DECISION: the hub INDEX (docs/web/hub/index.md) is skipped --
# it already has a dedicated smoke test (hub_smoke.sh) asserting its
# one scaffold cell computes the expected value; this script only
# walks the 30 numbered posts under _site/web/hub/NN-*/.
#
# Post enumeration is NOT hardcoded: it's read from the built
# `_site/web/hub/*/index.html` directory listing, so a new post lands
# in this harness automatically the next time it runs.
#
# --- Intentional-error / known-bug allowlist -------------------------
# A hub page may deliberately end a cell in a failed/rejected state (a
# demo of the engine correctly REJECTING something), or may carry a
# real, already-diagnosed bug that needs engine work out of this
# script's scope. Both cases go through the same per-post ALLOWLIST
# object inside the Node driver below (search for "ALLOWLIST"), each
# entry with an explicit human-readable reason -- never a blanket
# suppression. A survey of all 30 posts (grepping for `throw`,
# "intentional", "deliberately", "on purpose", "checksum" etc. across
# docs/web/hub/*.md) found several cells that talk about rejection in
# PROSE (post 18's IndexedDB torn-write/checksum demo, post 21's WKT
# parser, post 28's MathML-to-Presentation converter) but every one of
# them wraps its throwing code in the cell's own try/catch and returns
# a normal (non-rejected) value describing the failure -- so as of this
# writing there are NO posts with a live intentionally-REJECTED
# Observable cell, and the allowlist below is EMPTY. (Its one
# historical entry -- post 24, whose fn.queryHdt() calls took 5.7-20.5s
# each through the js bundle and got the tab killed -- was fixed in F*
# by HDT.Container's O(1) decoded-byte representation, task #102.) If
# a future post adds a real intentionally-rejected cell, add an
# `allowedCellIndices` entry for it there, with its own reason comment.
#
# Usage:
#   tests/web-demos/hub_browser_all.sh
#   HUB_BROWSER_ALL_PORT=8940 tests/web-demos/hub_browser_all.sh
#
# Requirements: same as hub_smoke.sh -- node >= 20, the vendored
# Playwright package with Chromium already provisioned (do NOT run
# `playwright install`; see that script's header for the resolution
# order this one mirrors).
#
# Exit code: 0 iff every post PASSes (or is explicitly ALLOWLISTED);
# non-zero otherwise. Total wall-clock is capped at 15 minutes
# (anti-pattern #17) via the `timeout` wrapped around the browser
# phase below.

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
  if ! node -e "require.resolve('playwright')" >/dev/null 2>&1; then
    echo "Missing playwright (looked in \$PLAYWRIGHT_PKG_DIR=$PLAYWRIGHT_PKG_DIR and node's module path)." >&2
    exit 2
  fi
  PLAYWRIGHT_IMPORT_SPEC="playwright"
fi

for f in third_party/eleventy/npm-cache third_party/observable/dist/runtime.esm.js docs/npm/factoidal/browser.js; do
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
    # Same known, pre-existing, out-of-territory defect hub_smoke.sh
    # and hub_posts_smoke.sh already work around: a CSVW design doc's
    # `{#fragment}` prose breaks Eleventy's whole-site build. Fall back
    # to an isolated copy of docs/ with only that file's fragments
    # defused.
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

[ -d "$SITE_DIR/web/hub" ] || { echo "FAIL: $SITE_DIR/web/hub was not produced." >&2; exit 1; }
[ -f "$SITE_DIR/web/hub/index.html" ] || { echo "FAIL: $SITE_DIR/web/hub/index.html was not produced." >&2; exit 1; }

# Enumerate posts from what actually got built rather than a hardcoded
# list -- every NN-slug directory directly under web/hub/ is a post.
# The hub index itself is index.html, a FILE at this level, not a
# directory (excluded automatically by -type d). web/hub/README.md
# (the cell-authoring contract, not a post) also builds to a directory
# here -- excluded explicitly by the ^[0-9]+- name filter, since it
# has no series_order and isn't one of the "~30 posts" this harness
# means to cover.
mapfile -t POSTS < <(find "$SITE_DIR/web/hub" -mindepth 1 -maxdepth 1 -type d -printf '%f\n' | grep -E '^[0-9]+-' | sort)
if [ "${#POSTS[@]}" -eq 0 ]; then
  echo "FAIL: no post directories found under $SITE_DIR/web/hub" >&2
  exit 1
fi
echo "== Found ${#POSTS[@]} post(s) under web/hub/ =="

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_BROWSER_ALL_PORT:-8933}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/" 2>/dev/null && break
  sleep 0.2
done

POSTS_JSON_PATH="$WORKDIR/posts.json"
{
  printf '['
  first=1
  for p in "${POSTS[@]}"; do
    [ "$first" -eq 1 ] || printf ','
    first=0
    printf '"%s"' "$p"
  done
  printf ']'
} >"$POSTS_JSON_PATH"

DRIVER_PATH="$WORKDIR/driver.mjs"
cat >"$DRIVER_PATH" <<'DRIVER_EOF'
// Node driver for tests/web-demos/hub_browser_all.sh. Written to a
// temp file by the shell script (not meant to be run standalone) --
// configuration comes from environment variables + the POSTS_JSON
// file the shell script also wrote, so nothing here depends on shell
// string interpolation.
import { readFileSync } from 'node:fs';

const { chromium } = await import(process.env.PLAYWRIGHT_IMPORT_SPEC);

const PORT = process.env.HUB_BROWSER_ALL_PORT_RESOLVED;
const POSTS = JSON.parse(readFileSync(process.env.POSTS_JSON_PATH, 'utf8'));

// Playwright's own {timeout} option on waitForFunction/goto/evaluate
// is NOT reliable once a page's JS main thread is fully blocked by a
// long synchronous computation: confirmed empirically against post 24
// (see ALLOWLIST below) -- a declared 30000ms waitForFunction timeout
// didn't actually reject until ~44s of real wall-clock time, by which
// point headless Chromium had already begun tearing the unresponsive
// tab down underneath us (the 'close'/'disconnected' events fired in
// the same instant the call finally threw). ownRace() enforces OUR OWN
// deadline via a plain setTimeout racing the real promise, so control
// always comes back on schedule regardless of what the page is doing.
// The raced-away promise is still given a .then/.catch (never left as
// an unhandled rejection that could crash the driver later); Playwright
// itself aborts it once we close the page a few lines down.
function ownRace(promise, ms) {
  return new Promise((resolve) => {
    let done = false;
    const timer = setTimeout(() => {
      if (!done) { done = true; resolve({ timedOut: true }); }
    }, ms);
    Promise.resolve(promise).then((value) => {
      if (!done) { done = true; clearTimeout(timer); resolve({ timedOut: false, ok: true, value }); }
    }).catch((e) => {
      if (!done) { done = true; clearTimeout(timer); resolve({ timedOut: false, ok: false, error: (e && e.message) || String(e) }); }
    });
  });
}

const NAV_TIMEOUT_MS = Number(process.env.HUB_BROWSER_ALL_NAV_TIMEOUT_MS || 30000);
// Chosen well under the ~44s-to-79s window where an unresponsive tab
// was observed to get killed by headless Chromium on its own (see
// post 24 below) -- 25s bounds our OWN wait comfortably inside that
// margin, close to (but safely short of) the "~30s" this task asked
// for, so we always regain control and cleanly close the page before
// anything at the browser-process level goes wrong.
const CELL_SETTLE_TIMEOUT_MS = Number(process.env.HUB_BROWSER_ALL_CELL_TIMEOUT_MS || 25000);

// --- Intentional-error / KNOWN-BUG allowlist -------------------------
// Keyed by post slug (the _site/web/hub/<slug>/ directory name). Every
// entry MUST carry a human-readable `reason` -- no blanket suppression.
//   allowTimeout        -- true if the cell-settle wait is expected to
//                           time out (a real, already-diagnosed bug,
//                           not fixed in this test-infra-only task)
//   allowedCellIndices  -- Set of `data-hub-cell` index strings whose
//                           REJECTED state is an intentional demo of
//                           the engine correctly rejecting something
//   pageerrorAllow      -- RegExp[]; a `pageerror` matching one of
//                           these is not treated as a failure
//
// A page with an allowlist entry still fails on any pageerror that
// does NOT match pageerrorAllow, and on any rejected cell whose index
// is NOT in allowedCellIndices -- the allowlist narrows exactly the
// known condition, nothing broader.
const ALLOWLIST = {};

function allowlistFor(slug) {
  const entry = ALLOWLIST[slug];
  return {
    reason: entry ? entry.reason : null,
    allowTimeout: !!(entry && entry.allowTimeout),
    allowedCellIndices: (entry && entry.allowedCellIndices) || new Set(),
    pageerrorAllow: (entry && entry.pageerrorAllow) || [],
  };
}

const browser = await chromium.launch({ args: ['--disable-gpu', '--no-sandbox'] });

let pass = 0;
let fail = 0;

for (const slug of POSTS) {
  const allow = allowlistFor(slug);
  const url = `http://127.0.0.1:${PORT}/factoidal/web/hub/${slug}/`;

  if (!browser.isConnected()) {
    console.log(`FAIL ${slug}: browser process disconnected during an earlier post's run (see output above)`);
    fail++;
    continue;
  }

  const page = await browser.newPage();
  const pageErrors = [];
  const consoleErrors = [];
  page.on('pageerror', (err) => pageErrors.push(err.message));
  page.on('console', (msg) => { if (msg.type() === 'error') consoleErrors.push(msg.text()); });

  const nav = await ownRace(
    page.goto(url, { waitUntil: 'networkidle', timeout: NAV_TIMEOUT_MS }),
    NAV_TIMEOUT_MS + 5000
  );
  if (nav.timedOut || !nav.ok) {
    const msg = nav.timedOut
      ? `navigation did not complete within ${NAV_TIMEOUT_MS + 5000}ms`
      : `navigation failed: ${nav.error}`;
    console.log(`FAIL ${slug}: ${msg}`);
    fail++;
    await ownRace(page.close({ runBeforeUnload: false }), 5000);
    continue;
  }

  // Single unified settle-check -- deliberately NOT split into a
  // separate "get cell count first, then decide whether to wait"
  // step. An earlier version of this driver did split it that way and
  // had a real false-PASS bug: page 24's main thread can become fully
  // blocked (see ALLOWLIST above) fast enough that even the very
  // first, supposedly-cheap `$$eval('.observable-cell', els =>
  // els.length)` call gets queued behind the block and times out on
  // OUR OWN cap -- and a naive "timed out => assume 0 cells => skip
  // the wait entirely" treats that as a trivial pass, exactly the
  // false negative this harness exists to prevent. Once the render
  // thread is blocked, ANY eval (count, settle-check, or otherwise)
  // is equally likely to stall, so there is no "cheap" way to peek
  // first -- the fix is to not need to. The predicate below handles
  // "zero cells" (task step 3's "a page with zero cells passes
  // trivially") and "cells exist, wait for them" in the exact same
  // expression -- `cells.length === 0` is true immediately for a
  // genuinely cell-less page (e.g. post 22), so there is no separate
  // fast path to race against the block.
  const settle = await ownRace(
    page.waitForFunction(() => {
      const cells = [...document.querySelectorAll('.observable-cell')];
      // Settled = nonempty text OR rendered DOM children: a cell whose
      // value is pure graphics (post 28's sigmoidPlotDisplay resolves
      // to an SVG polyline) has empty textContent forever, and reading
      // that as "still computing" is a false alarm (2026-08-08).
      return cells.length === 0 || cells.every((c) =>
        (c.textContent && c.textContent.trim().length > 0) || c.childElementCount > 0);
    }, { timeout: CELL_SETTLE_TIMEOUT_MS + 15000 }),
    CELL_SETTLE_TIMEOUT_MS
  );
  const settleTimedOut = settle.timedOut || !settle.ok;

  // Read final cell state (own-capped -- the page may still be
  // computing if settleTimedOut is true, in which case this may also
  // time out and we fall back to "no cell info available").
  const cellRead = await ownRace(
    page.$$eval('.observable-cell', (els) =>
      els.map((el) => ({
        idx: el.getAttribute('data-hub-cell'),
        // Prefer the vendored Observable Inspector's own rejection
        // marker: third_party/observable/dist/inspector.esm.js's
        // Inspector.rejected() adds "observablehq--error" to the SAME
        // container node hub.njk's createOutput() passes to
        // `new Inspector(container)`. hub.njk's own wrapper also adds
        // "observable-cell-error" to that identical node (belt and
        // suspenders, same element either way) -- see hub.njk's
        // createOutput() around the "inspector.rejected = ..." line.
        errored: el.classList.contains('observablehq--error') || el.classList.contains('observable-cell-error'),
        text: (el.textContent || '').trim().slice(0, 300),
      }))
    ),
    5000
  );
  const cells = (!cellRead.timedOut && cellRead.ok) ? cellRead.value : [];

  const rejected = cells.filter((c) => c.errored && !allow.allowedCellIndices.has(c.idx));
  const badPageErrors = pageErrors.filter((m) => !allow.pageerrorAllow.some((re) => re.test(m)));

  let failReason = null;
  if (badPageErrors.length > 0) {
    failReason = `pageerror: ${badPageErrors[0]}`;
  } else if (rejected.length > 0) {
    failReason = `cell[${rejected[0].idx}] rejected: ${rejected[0].text.slice(0, 160)}`;
  } else if (settleTimedOut && !allow.allowTimeout) {
    if (cellRead.timedOut || !cellRead.ok) {
      failReason = `cells did not settle within ${CELL_SETTLE_TIMEOUT_MS}ms (page unresponsive -- could not read final cell state either)`;
    } else {
      const stillEmpty = cells.filter((c) => c.text.length === 0).length;
      failReason = `cells did not settle within ${CELL_SETTLE_TIMEOUT_MS}ms (${stillEmpty}/${cells.length} still empty)`;
    }
  }

  if (failReason) {
    console.log(`FAIL ${slug}: ${failReason}`);
    if (consoleErrors.length > 0) {
      console.log(`  console.error (${consoleErrors.length} total): ${consoleErrors[0].slice(0, 200)}`);
    }
    fail++;
  } else {
    let note = '';
    if (settleTimedOut && allow.allowTimeout) {
      note = ` (ALLOWLISTED, KNOWN-BUG: ${allow.reason.slice(0, 120)}...)`;
    }
    console.log(`PASS ${slug}${note}`);
    pass++;
  }

  await ownRace(page.close({ runBeforeUnload: false }), 8000);
}

await ownRace(browser.close(), 10000);

const total = pass + fail;
console.log('===');
console.log(`hub-browser: ${pass} pass, ${fail} fail (out of ${total} posts)`);
process.exit(fail === 0 ? 0 : 1);
DRIVER_EOF

DRIVER_RC=0
PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_IMPORT_SPEC" \
HUB_BROWSER_ALL_PORT_RESOLVED="$PORT" \
POSTS_JSON_PATH="$POSTS_JSON_PATH" \
  timeout 900 node "$DRIVER_PATH" || DRIVER_RC=$?

exit "$DRIVER_RC"
