#!/usr/bin/env bash
# tests/web-demos/hub_posts_smoke.sh
#
# Smoke test for the five published documentation-hub posts
# (docs/web/hub/01-*.md through 05-*.md): builds the site offline
# with the vendored Eleventy (third_party/eleventy/), serves the built
# _site under its real /factoidal/ pathPrefix, and drives headless
# Chromium (Playwright) over each post page to confirm:
#
#   1. Every ```observable-js cell on the page (docs/_includes/hub.njk's
#      mountCell() convention) mounts and computes without ending up in
#      the .observable-cell-error state.
#   2. At least one cell on each page renders a nonempty value (proof
#      the `fn` typed-adapter binding — hub.njk's CELL_BINDINGS — is
#      actually wired to the real F*-extracted engine, not just that
#      the runtime loaded).
#   3. At a 390px mobile viewport, the page never scrolls horizontally
#      (document.documentElement.scrollWidth <= viewport width) — same
#      check tests/web-demos/*.sh already apply to other demo pages.
#
# Sibling to tests/web-demos/hub_smoke.sh, which covers the hub
# scaffold's own smoke cell on docs/web/hub/index.md; this script
# covers the content posts wave B (and later waves) added on top of
# that scaffold.
#
# Usage:
#   tests/web-demos/hub_posts_smoke.sh
#
# Requirements: node >= 20, the `playwright` package with Chromium
# installed (see tests/web-demos/hub_smoke.sh's own header for the
# resolution order this script mirrors).
#
# Exit code: 0 iff the site builds and every post page's live cells
# compute without error; non-zero otherwise.

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
    # Same known, pre-existing, out-of-territory defect hub_smoke.sh
    # already works around: a CSVW design doc's `{#fragment}` prose
    # breaks Eleventy's whole-site build. Fall back to an isolated
    # copy of docs/ with only that file's fragments defused.
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

POSTS=(
  "web/hub/01-triples-rdf-from-first-principles/"
  "web/hub/02-asking-questions-sparql/"
  "web/hub/03-schemas-that-infer-rdfs-owl/"
  "web/hub/04-concept-schemes-skos/"
  "web/hub/05-shapes-that-validate-shacl/"
  "web/hub/06-shapes-the-other-dialect-shex/"
  "web/hub/07-json-ld-rdf-as-json/"
  "web/hub/08-canonical-graphs-rdfc10/"
  "web/hub/09-mapping-tables-to-triples-rml/"
  "web/hub/10-rules-rif-core/"
  "web/hub/11-one-graph-five-syntaxes/"
  "web/hub/12-the-api-tour/"
  "web/hub/13-verifiable-credentials-and-csvw/"
  "web/hub/14-the-rdfjs-api/"
  "web/hub/15-how-fast-the-performance-story/"
  "web/hub/16-the-verified-in-fstar-story/"
  "web/hub/17-mutating-and-serving-data/"
  "web/hub/18-the-durable-log-live/"
)
for p in "${POSTS[@]}"; do
  [ -f "$SITE_DIR/$p/index.html" ] || { echo "FAIL: $SITE_DIR/$p/index.html was not produced." >&2; exit 1; }
done

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_POSTS_SMOKE_PORT:-8932}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/" 2>/dev/null && break
  sleep 0.2
done

POSTS_JSON="["
for p in "${POSTS[@]}"; do POSTS_JSON="$POSTS_JSON\"$p\","; done
POSTS_JSON="${POSTS_JSON%,}]"

# Per-post minimum live-cell count. Every post defaults to 2 (the
# original blanket check); posts 15 and 16 are deliberately single-cell
# by design (post 15: one in-browser timing illustration, explicitly
# not a benchmark; post 16: the "live element" is mostly the reader
# opening RDF.Term.fsti, with one pretty()-table cell rendering the
# extraction pipeline -- see docs/designissues/2026-07-05-docs-hub-plan.md
# and this post's own brief for why a second cell would not add
# anything real).
MIN_CELLS_JSON='{
  "web/hub/15-how-fast-the-performance-story/": 1,
  "web/hub/16-the-verified-in-fstar-story/": 1
}'

timeout 120 node --input-type=module -e "
import { chromium } from '$PLAYWRIGHT_IMPORT_SPEC';

const PORT = $PORT;
const POSTS = $POSTS_JSON;
const MIN_CELLS = $MIN_CELLS_JSON;

const browser = await chromium.launch();
let totalFailures = 0;

for (const post of POSTS) {
  const url = 'http://127.0.0.1:' + PORT + '/factoidal/' + post;
  console.log('--- ' + url + ' ---');
  const page = await browser.newPage();
  const consoleMsgs = [];
  page.on('console', (msg) => consoleMsgs.push('[console:' + msg.type() + '] ' + msg.text()));
  page.on('pageerror', (err) => consoleMsgs.push('[pageerror] ' + err.message));

  let failures = 0;
  function check(label, cond) {
    if (cond) { console.log('  PASS  ' + label); }
    else { console.log('  FAIL  ' + label); failures++; }
  }

  await page.setViewportSize({ width: 1024, height: 800 });
  await page.goto(url, { waitUntil: 'networkidle' });

  let cellCount = 0;
  try {
    await page.waitForSelector('.observable-cell', { timeout: 10000 });
    cellCount = await page.\$\$eval('.observable-cell', (els) => els.length);
  } catch (e) {
    console.log('  No .observable-cell mounted. Console log:\n' + consoleMsgs.join('\n'));
    failures++;
    totalFailures += failures;
    await page.close();
    continue;
  }
  const minCells = MIN_CELLS[post] || 2;
  check('at least ' + minCells + ' live cell(s) mounted (found ' + cellCount + ')', cellCount >= minCells);

  // Give every cell's async body time to settle.
  try {
    await page.waitForFunction(() => {
      const cells = [...document.querySelectorAll('.observable-cell')];
      return cells.every((c) => c.textContent && c.textContent.trim().length > 0);
    }, { timeout: 20000 });
  } catch (e) {
    console.log('  Not every cell produced output within the timeout. Console log:\n' + consoleMsgs.join('\n'));
  }

  const cellInfo = await page.\$\$eval('.observable-cell', (els) =>
    els.map((el) => ({ text: el.textContent.trim(), errored: el.classList.contains('observable-cell-error') }))
  );

  let nonEmptyCount = 0;
  cellInfo.forEach((c, i) => {
    check('cell ' + i + ' did not error', !c.errored);
    if (c.errored) console.log('    error text: ' + c.text);
    if (c.text.length > 0) nonEmptyCount++;
  });
  check('at least one cell produced a nonempty value', nonEmptyCount >= 1);

  // Interaction pass (one page is enough): edit cell 0's source via the
  // Edit toggle, replace it with a trivially different deterministic
  // expression, tap Run, and confirm the output actually changed and
  // no .observable-cell-error appeared. DOM order per hub.njk's
  // mountCell() is: <pre>, textarea.observable-cell-editor,
  // div.observable-cell-toolbar, div.observable-cell -- walk siblings
  // from the container rather than relying on index-based selectors.
  if (post === POSTS[0]) {
    console.log('  -- interaction: edit + run cell 0 --');
    const cellSel = '.observable-cell[data-hub-cell=\"0\"]';
    await page.waitForSelector(cellSel);

    const beforeText = await page.\$eval(cellSel, (el) => el.textContent.trim());
    check('cell 0 has a nonempty output before editing (was: ' + beforeText + ')', beforeText.length > 0);

    const editorState = await page.evaluate((sel) => {
      const container = document.querySelector(sel);
      const toolbar = container.previousElementSibling;
      const editBtn = toolbar.querySelector('.observable-cell-edit-btn');
      editBtn.click();
      const editor = toolbar.previousElementSibling;
      return { notHidden: !editor.hidden, computedDisplay: getComputedStyle(editor).display };
    }, cellSel);
    check('Edit toggle reveals the textarea editor (hidden attr cleared)', editorState.notHidden);
    // Regression guard: an author `.observable-cell-editor { display:
    // block }` rule can silently outrank the UA `[hidden]` rule at
    // equal specificity, leaving the textarea visible even while
    // `.hidden` reads true -- assert the *rendered* state too.
    check(
      'Edit toggle actually renders the textarea (computed display: ' + editorState.computedDisplay + ')',
      editorState.computedDisplay !== 'none'
    );

    await page.evaluate((sel) => {
      const container = document.querySelector(sel);
      const toolbar = container.previousElementSibling;
      const editor = toolbar.previousElementSibling;
      editor.value = 'return 6 * 7;';
      editor.dispatchEvent(new Event('input', { bubbles: true }));
    }, cellSel);

    await page.evaluate((sel) => {
      const container = document.querySelector(sel);
      const toolbar = container.previousElementSibling;
      const runBtn = toolbar.querySelector('.observable-cell-run-btn');
      runBtn.click();
    }, cellSel);

    // The Inspector renders named variables as 'hubCell0 = <value>',
    // same format the pre-edit assertion above already observed.
    try {
      await page.waitForFunction((sel) => {
        const el = document.querySelector(sel);
        return el && /(^|\s)42$/.test(el.textContent.trim());
      }, cellSel, { timeout: 5000 });
    } catch (e) {
      // fall through -- the check() below reports the actual text.
    }

    const afterText = await page.\$eval(cellSel, (el) => el.textContent.trim());
    const afterErrored = await page.\$eval(cellSel, (el) => el.classList.contains('observable-cell-error'));
    check('edited cell (return 6 * 7;) re-ran via Run and now outputs 42 (was: ' + afterText + ')', /(^|\s)42$/.test(afterText));
    check('edited cell has no .observable-cell-error after Run', !afterErrored);
  }

  if (failures > 0) {
    console.log('  console log:\n' + consoleMsgs.join('\n'));
  }

  // 390px mobile viewport: no page-level horizontal scroll. Run after
  // the interaction pass on post 0 too, so this also exercises the
  // toolbar/editor chrome left in its post-edit state (editor visible)
  // for that page -- not just the pristine pre/toolbar layout.
  await page.setViewportSize({ width: 390, height: 844 });
  await page.waitForTimeout(200);
  const overflow = await page.evaluate(() => ({
    scrollWidth: document.documentElement.scrollWidth,
    clientWidth: document.documentElement.clientWidth,
  }));
  check(
    '390px viewport: no horizontal overflow (scrollWidth ' + overflow.scrollWidth +
    ' <= clientWidth ' + overflow.clientWidth + ')',
    overflow.scrollWidth <= overflow.clientWidth
  );

  totalFailures += failures;
  await page.close();
}

await browser.close();

console.log('===');
if (totalFailures === 0) {
  console.log('hub posts smoke: ALL PASS');
  process.exit(0);
} else {
  console.log('hub posts smoke: ' + totalFailures + ' FAILURE(S)');
  process.exit(1);
}
"
