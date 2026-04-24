#!/usr/bin/env bash
# Integrity check for the Eleventy-built GitHub Pages site:
# every relative href/src reference in every .html must resolve to a
# real file under _site.
#
# Usage:
#   ./tests/local/check_pages_links.sh [path-to-_site]
#
# Default path: docs/_site. Exit 0 on all-green, 1 on any broken link.
#
# Scope: relative URLs and `/factoidal/...` pathPrefix links. HTTP(S) is
# intentionally NOT probed (rate-limiting would make CI flaky).

set -euo pipefail

SITE_ROOT="${1:-docs/_site}"
if [ ! -d "$SITE_ROOT" ]; then
  echo "site root not found: $SITE_ROOT" >&2
  echo "run 'cd docs && npx @11ty/eleventy --output=_site' first" >&2
  exit 2
fi

PATH_PREFIX="/factoidal/"
TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

python3 - "$SITE_ROOT" "$PATH_PREFIX" "$TMP" <<'PYEOF'
import os, re, sys

site_root, path_prefix, tmp = sys.argv[1], sys.argv[2], sys.argv[3]
site_root = os.path.abspath(site_root)
skip_schemes = ("http:", "https:", "mailto:", "data:", "ftp:", "//", "javascript:")
link_re = re.compile(r'(?:href|src)="([^"#?]+)', re.IGNORECASE)

total = 0
broken = []
html_count = 0

for dirpath, _dirs, files in os.walk(site_root):
    for f in files:
        if not f.endswith(".html"):
            continue
        html_count += 1
        page = os.path.join(dirpath, f)
        with open(page, "r", encoding="utf-8", errors="replace") as fh:
            content = fh.read()
        for url in link_re.findall(content):
            if not url or url.startswith(skip_schemes):
                continue
            if url.startswith(path_prefix):
                target = os.path.join(site_root, url[len(path_prefix):])
            elif url.startswith("/"):
                target = os.path.join(site_root, url.lstrip("/"))
            else:
                target = os.path.join(dirpath, url)
            if target.endswith("/"):
                target = os.path.join(target, "index.html")
            target = os.path.normpath(target)
            total += 1
            if not os.path.exists(target):
                broken.append((os.path.relpath(page, site_root), url,
                               os.path.relpath(target, site_root)))

with open(tmp, "w") as fh:
    fh.write(f"total={total}\n")
    fh.write(f"html={html_count}\n")
    fh.write(f"broken={len(broken)}\n")
    for page, url, target in broken:
        fh.write(f"B\t{page}\t{url}\t{target}\n")
PYEOF

TOTAL=$(awk -F= '/^total=/{print $2}' "$TMP")
HTML=$(awk -F= '/^html=/{print $2}' "$TMP")
BROKEN=$(awk -F= '/^broken=/{print $2}' "$TMP")

echo ""
echo "Checked $TOTAL relative links across $HTML HTML files under $SITE_ROOT."
if [ "$BROKEN" -gt 0 ]; then
  echo "$BROKEN broken:"
  grep '^B' "$TMP" | while IFS=$'\t' read -r _ page url target; do
    echo "  in $page: href=\"$url\" -> $target MISSING"
  done
  exit 1
fi
echo "All green."
