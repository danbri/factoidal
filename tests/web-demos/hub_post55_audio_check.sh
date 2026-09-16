#!/usr/bin/env bash
# tests/web-demos/hub_post55_audio_check.sh
#
# Headless-Chromium check for hub post 55's audio cell
# (docs/web/hub/55-valis-a-drum-machine-in-rdf.md, danbri/factoidal#687):
# builds the site offline with the vendored Eleventy, serves it under
# /factoidal/, and drives headless Chromium -- launched with
# --autoplay-policy=no-user-gesture-required, since a synthetic click()
# from Playwright does not carry the "sticky user activation" a real
# tap does, and Web Audio's autoplay gate would otherwise leave the
# AudioContext "suspended" forever -- to the post, waits for every cell
# to settle, clicks Play, and asserts within 5 s that
# window.__valisAudio (set by the audio cell right after
# Audio.loadCircuit() resolves) reports an AudioContext in state
# "running" with a positive compiled-node count, and that no pageerror
# happened anywhere in the page's lifecycle. Clicks Stop afterward.
#
# Modeled on tests/web-demos/hub_post21_geo_check.sh (build+serve
# scaffold, ownRace-free here since this check's own waits are already
# short and bounded) and hub_browser_all.sh (the settle-wait predicate).
#
# Usage:
#   tests/web-demos/hub_post55_audio_check.sh
#   HUB_POST55_AUDIO_CHECK_PORT=8956 tests/web-demos/hub_post55_audio_check.sh
#
# Requirements: node >= 20, the vendored Playwright package with
# Chromium already provisioned (do NOT run `playwright install`).
#
# Exit code: 0 pass, 1 fail (a check did not hold), 2 environment
# missing (playwright, a vendored prerequisite, or the built page
# itself -- the message on stderr says which).
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
    echo "ENV MISSING: playwright (looked in \$PLAYWRIGHT_PKG_DIR=$PLAYWRIGHT_PKG_DIR and node's module path)." >&2
    exit 2
  fi
  PLAYWRIGHT_IMPORT_SPEC="playwright"
fi

for f in third_party/eleventy/npm-cache third_party/observable/dist/runtime.esm.js docs/npm/factoidal/browser.js third_party/valis/vocabs/valis.ttl docs/web/hub/assets/valis-daw/audio.mjs; do
  [ -e "$f" ] || { echo "ENV MISSING: $f -- run the vendoring steps first (third_party/valis/PROVENANCE.md, docs/web/hub/assets/valis-daw/README.md)." >&2; exit 2; }
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
    # Same known, pre-existing, out-of-territory defect hub_browser_all.sh
    # and hub_post21_geo_check.sh already work around -- see their headers.
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

PAGE="$SITE_DIR/web/hub/55-valis-a-drum-machine-in-rdf/index.html"
[ -f "$PAGE" ] || { echo "ENV MISSING: $PAGE was not produced by the build." >&2; exit 2; }

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_POST55_AUDIO_CHECK_PORT:-8956}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/55-valis-a-drum-machine-in-rdf/" 2>/dev/null && break
  sleep 0.2
done

DRIVER_PATH="$WORKDIR/driver.mjs"
cat >"$DRIVER_PATH" <<'DRIVER_EOF'
// Node driver for tests/web-demos/hub_post55_audio_check.sh. Written to
// a temp file by the shell script (not meant to be run standalone).
const { chromium } = await import(process.env.PLAYWRIGHT_IMPORT_SPEC);
const PORT = process.env.HUB_POST55_PORT_RESOLVED;
const URL_ = `http://127.0.0.1:${PORT}/factoidal/web/hub/55-valis-a-drum-machine-in-rdf/`;

let failures = 0;
function check(label, ok) {
  console.log((ok ? 'PASS' : 'FAIL') + ' -- ' + label);
  if (!ok) failures++;
}

// --autoplay-policy=no-user-gesture-required: headless Chromium's
// default autoplay gate treats a Playwright-synthesized click() as NOT
// carrying real user activation, so AudioContext.resume() would
// otherwise leave the context "suspended" forever even after Play is
// clicked. This flag is the browser-launch-time opt-out for exactly
// that gate, scoped to this one Chromium instance.
const browser = await chromium.launch({
  args: ['--disable-gpu', '--no-sandbox', '--autoplay-policy=no-user-gesture-required'],
});

const page = await browser.newPage();
const pageErrors = [];
const consoleErrors = [];
page.on('pageerror', (err) => pageErrors.push(err.message));
page.on('console', (msg) => { if (msg.type() === 'error') consoleErrors.push(msg.text()); });

await page.goto(URL_, { waitUntil: 'networkidle', timeout: 30000 });

// Wait for every cell to settle (same predicate as hub_browser_all.sh),
// so the audio cell has rendered its Play/Stop controls before we look
// for them.
await page.waitForFunction(() => {
  const cells = [...document.querySelectorAll('.observable-cell')];
  return cells.length === 0 || cells.every((c) =>
    (c.textContent && c.textContent.trim().length > 0) || c.childElementCount > 0);
}, { timeout: 30000 });

const playButton = await page.$('.valis-play');
check('Play button (.valis-play) is present after cells settle', playButton !== null);

if (playButton) {
  await playButton.click();

  // Poll window.__valisAudio for up to 5 s (the task's own budget),
  // rather than a single point-in-time read right after the click --
  // loadCircuit() and the AudioWorklet module fetch are asynchronous.
  const deadline = Date.now() + 5000;
  let audioState = null;
  while (Date.now() < deadline) {
    audioState = await page.evaluate(() => window.__valisAudio || null);
    if (audioState && audioState.state === 'running' && audioState.nodeCount > 0) break;
    await new Promise((r) => setTimeout(r, 150));
  }

  console.log('window.__valisAudio at end of poll: ' + JSON.stringify(audioState));
  check('window.__valisAudio.state === "running" within 5s', !!audioState && audioState.state === 'running');
  check(`window.__valisAudio.nodeCount > 0 within 5s (got ${audioState && audioState.nodeCount})`,
    !!audioState && audioState.nodeCount > 0);

  const stopButton = await page.$('.valis-stop');
  check('Stop button (.valis-stop) is present after Play', stopButton !== null);
  if (stopButton) await stopButton.click();
}

check('zero pageerror events over the whole page lifecycle', pageErrors.length === 0);
if (pageErrors.length) console.log('  pageerrors: ' + pageErrors.join(' | '));
// console.error is logged but does not gate pass/fail here, same
// convention as hub_browser_all.sh's driver: audio.mjs's unlock()
// creates a silent data:audio/wav <audio> element as a belt-and-
// suspenders iOS ringer-switch workaround (ported unchanged from the
// original DAW), which this page's CSP (no media-src, so it falls
// back to default-src 'self') refuses -- harmlessly, since the real
// AudioContext.resume() this check asserts on does not depend on it.
if (consoleErrors.length) console.log('  console.error (informational, not gated): ' + consoleErrors.join(' | '));

await page.close();
await browser.close();

console.log('===');
console.log(`hub_post55_audio_check: ${failures === 0 ? 'ALL PASS' : failures + ' FAILURE(S)'}`);
process.exit(failures === 0 ? 0 : 1);
DRIVER_EOF

DRIVER_RC=0
PLAYWRIGHT_IMPORT_SPEC="$PLAYWRIGHT_IMPORT_SPEC" \
HUB_POST55_PORT_RESOLVED="$PORT" \
  timeout 120 node "$DRIVER_PATH" || DRIVER_RC=$?

exit "$DRIVER_RC"
