#!/usr/bin/env bash
# tests/web-demos/hub_links_check.sh
#
# Link-integrity check for the documentation hub (docs/web/hub/*.md +
# the site homepage): builds the site offline with the vendored
# Eleventy (third_party/eleventy/), serves the built _site under its
# real /factoidal/ pathPrefix, and drives headless Chromium
# (Playwright) over the hub index, README, all five published posts,
# and the homepage to collect every <a href> on each page.
#
# Every same-site link (relative, `/factoidal/...`, or bare `/...`) is
# resolved against the built _site filesystem using the same
# pretty-URL convention tests/local/check_pages_links.sh uses (a
# trailing `/` resolves to `index.html`). Any that don't resolve are
# reported and fail the script.
#
# github.com links are collected too but checked only when --external
# is passed (curl through whatever network access is available) --
# CI environments often lack outbound github.com egress, so this half
# of the check is advisory-only and never affects the exit code.
#
# Background: an owner report (2026-07-06) found a few hub -> github
# 404s -- wrong branch in blob URLs (this repo's main line is
# claude/main, not main) and repo-relative markdown links
# (../../../tests/hub/postNN_test.mjs style) that Eleventy passed
# through as site-relative paths escaping the site root, 404ing on
# Pages. This script is the reusable regression guard for both classes
# of breakage.
#
# Usage:
#   tests/web-demos/hub_links_check.sh              # same-site links only, exits nonzero on breakage
#   tests/web-demos/hub_links_check.sh --external    # also curl-check github.com links (advisory, report only)
#
# Requirements: node >= 20, the `playwright` package with Chromium
# installed (see tests/web-demos/hub_smoke.sh's header for the
# resolution order this script mirrors).
#
# Exit code: 0 iff the site builds and every same-site link on the
# checked pages resolves; non-zero otherwise. github.com link status
# (only probed with --external) never affects the exit code.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$REPO_ROOT"

CHECK_EXTERNAL=0
for arg in "$@"; do
  case "$arg" in
    --external) CHECK_EXTERNAL=1 ;;
    *) echo "Unknown argument: $arg (only --external is supported)" >&2; exit 2 ;;
  esac
done

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

for f in third_party/eleventy/npm-cache docs/web/hub/index.md; do
  [ -e "$f" ] || { echo "Missing $f -- run the vendoring steps first (see third_party/eleventy/README.md)." >&2; exit 2; }
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
    # Same known, pre-existing, out-of-territory defect hub_posts_smoke.sh
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

PAGES=(
  "web/hub/"
  "web/hub/README/"
  "web/hub/01-triples-rdf-from-first-principles/"
  "web/hub/02-asking-questions-sparql/"
  "web/hub/03-schemas-that-infer-rdfs-owl/"
  "web/hub/04-concept-schemes-skos/"
  "web/hub/05-shapes-that-validate-shacl/"
  ""
)
for p in "web/hub/" "web/hub/01-triples-rdf-from-first-principles/" "web/hub/02-asking-questions-sparql/" \
         "web/hub/03-schemas-that-infer-rdfs-owl/" "web/hub/04-concept-schemes-skos/" \
         "web/hub/05-shapes-that-validate-shacl/"; do
  [ -f "$SITE_DIR/$p/index.html" ] || { echo "FAIL: $SITE_DIR/$p/index.html was not produced." >&2; exit 1; }
done

echo "== Serving $SITE_DIR under /factoidal/ and driving headless Chromium to collect links =="
SERVE_ROOT="$WORKDIR/serve-root"
mkdir -p "$SERVE_ROOT"
ln -s "$SITE_DIR" "$SERVE_ROOT/factoidal"

PORT="${HUB_LINKS_CHECK_PORT:-8934}"
( cd "$SERVE_ROOT" && exec python3 -m http.server "$PORT" --bind 127.0.0.1 ) >"$WORKDIR/http-server.log" 2>&1 &
HTTP_PID=$!

for _ in $(seq 1 50); do
  curl -sS -o /dev/null "http://127.0.0.1:$PORT/factoidal/web/hub/" 2>/dev/null && break
  sleep 0.2
done

PAGES_JSON="["
for p in "${PAGES[@]}"; do PAGES_JSON="$PAGES_JSON\"$p\","; done
PAGES_JSON="${PAGES_JSON%,}]"

RESULT_JSON="$WORKDIR/result.json"

timeout 90 node --input-type=module -e "
import { chromium } from '$PLAYWRIGHT_IMPORT_SPEC';
import fs from 'node:fs';

const PORT = $PORT;
const PAGES = $PAGES_JSON;

const browser = await chromium.launch();
const page = await browser.newPage();

const linksByPage = {};
for (const p of PAGES) {
  const url = 'http://127.0.0.1:' + PORT + '/factoidal/' + p;
  await page.goto(url, { waitUntil: 'networkidle' });
  const hrefs = await page.\$\$eval('a[href]', els => els.map(e => e.getAttribute('href')));
  linksByPage[p || '(homepage)'] = hrefs;
}

await browser.close();
fs.writeFileSync('$RESULT_JSON', JSON.stringify(linksByPage));
"

echo "== Resolving same-site links against $SITE_DIR (pretty-URL convention) =="

SAMESITE_RC=0
python3 - "$RESULT_JSON" "$SITE_DIR" "$WORKDIR/github_links.txt" <<'PYEOF' || SAMESITE_RC=$?
import json, os, sys

result_path, site_root, github_out = sys.argv[1], sys.argv[2], sys.argv[3]
data = json.load(open(result_path))
site_root = os.path.abspath(site_root)
path_prefix = "/factoidal/"

page_dir_map = {
    "web/hub/": "web/hub",
    "web/hub/README/": "web/hub/README",
    "web/hub/01-triples-rdf-from-first-principles/": "web/hub/01-triples-rdf-from-first-principles",
    "web/hub/02-asking-questions-sparql/": "web/hub/02-asking-questions-sparql",
    "web/hub/03-schemas-that-infer-rdfs-owl/": "web/hub/03-schemas-that-infer-rdfs-owl",
    "web/hub/04-concept-schemes-skos/": "web/hub/04-concept-schemes-skos",
    "web/hub/05-shapes-that-validate-shacl/": "web/hub/05-shapes-that-validate-shacl",
    "(homepage)": "",
}
skip_schemes = ("mailto:", "data:", "ftp:", "javascript:")

total = 0
broken = []
github_links = set()
seen = set()

for page, hrefs in data.items():
    page_dir = os.path.join(site_root, page_dir_map.get(page, ""))
    for href in hrefs:
        if not href or href.startswith(skip_schemes):
            continue
        if href.startswith("https://github.com") or href.startswith("http://github.com"):
            github_links.add(href)
            continue
        if href.startswith("http://") or href.startswith("https://"):
            continue  # other external links: out of scope for this checker
        key = (page, href)
        if key in seen:
            continue
        seen.add(key)
        if href.startswith(path_prefix):
            target = os.path.join(site_root, href[len(path_prefix):])
        elif href.startswith("/"):
            target = os.path.join(site_root, href.lstrip("/"))
        else:
            target = os.path.join(page_dir, href)
        if target.endswith("/"):
            target = os.path.join(target, "index.html")
        target = os.path.normpath(target)
        total += 1
        escapes = not (target + os.sep).startswith(site_root + os.sep) and target != site_root
        if escapes or not os.path.exists(target):
            broken.append((page, href, target, "ESCAPES_ROOT" if escapes else "MISSING"))

with open(github_out, "w") as fh:
    for link in sorted(github_links):
        fh.write(link + "\n")

print(f"Checked {total} same-site links across {len(data)} pages.")
if broken:
    print(f"{len(broken)} broken:")
    for page, href, target, reason in broken:
        print(f"  on {page}: href=\"{href}\" -> {target} [{reason}]")
    sys.exit(1)
print("All same-site links resolve. All green.")
PYEOF

if [ "$CHECK_EXTERNAL" -eq 1 ]; then
  echo ""
  echo "== --external: probing github.com links (advisory only) =="
  EXTERNAL_BROKEN=0
  while IFS= read -r url; do
    [ -z "$url" ] && continue
    CODE=$(curl -s -o /dev/null -w "%{http_code}" -L --max-time 20 "$url" || echo "ERR")
    if [ "$CODE" = "200" ]; then
      echo "  200  $url"
    else
      echo "  $CODE  $url  (advisory -- does not fail this script; may be sandbox/CI egress, not a real 404)"
      EXTERNAL_BROKEN=$((EXTERNAL_BROKEN + 1))
    fi
  done < "$WORKDIR/github_links.txt"
  echo "github.com links checked: advisory only, $EXTERNAL_BROKEN non-200 (see notes above)."
else
  echo ""
  echo "(github.com links not checked -- pass --external to probe them; advisory only, never affects exit code)"
fi

exit "$SAMESITE_RC"
