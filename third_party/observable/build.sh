#!/usr/bin/env bash
# third_party/observable/build.sh
#
# Re-vendors the Observable browser libraries from npm into
# self-contained ES module bundles under third_party/observable/dist/.
# Network access to registry.npmjs.org is required to RUN this
# script; the *output* (dist/*.esm.js) is what ships and is what the
# hub loads at runtime — no network needed to consume it.
#
# Why bundle instead of shipping the raw npm packages:
#   - @observablehq/runtime and @observablehq/inspector ship an ESM
#     `src/index.js` with only relative imports, so they're already
#     self-contained.
#   - @observablehq/stdlib, @observablehq/plot, and d3 ship ESM
#     entries that import OTHER npm packages by bare specifier
#     (`d3-array`, `isoformat`, `interval-tree-1d`, `d3`, ...). A
#     browser <script type="module"> cannot resolve a bare specifier
#     without either an import map or a bundler. We bundle so the
#     files work by relative/same-origin URL alone — no import map,
#     no CDN (the constraint that killed raw.githubusercontent
#     loading elsewhere in this repo; see npm/factoidal/browser.js).
#   - d3.esm.js is ALSO produced standalone (not just inlined into
#     plot.esm.js) so hub cells can use raw d3 (selections, scales)
#     without pulling in all of Plot. This does mean d3's code is
#     present twice on a page that loads both plot.esm.js and
#     d3.esm.js (two separate module realities, so `instanceof`
#     checks across the two copies won't unify) -- acceptable for a
#     first vendoring pass; revisit with an import-map-based shared
#     d3 instance if a hub post needs both in the same page.
#
# Usage:
#   third_party/observable/build.sh
#
# Pinned versions (see manifest.json for the full transitive tree):
#   @observablehq/runtime  6.0.0
#   @observablehq/inspector 5.0.1
#   @observablehq/stdlib   5.8.8
#   @observablehq/plot     0.6.17
#   d3                     7.9.0
#   esbuild (build-time only, not shipped) 0.28.1

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
VENDOR_DIR="$REPO_ROOT/third_party/observable"
BUILD_DIR="$(mktemp -d)"
trap 'rm -rf "$BUILD_DIR"' EXIT

echo "Building in $BUILD_DIR ..."
cd "$BUILD_DIR"
npm init -y >/dev/null

npm install --no-save \
  @observablehq/runtime@6.0.0 \
  @observablehq/inspector@5.0.1 \
  @observablehq/stdlib@5.8.8 \
  @observablehq/plot@0.6.17 \
  d3@7.9.0 \
  esbuild@0.28.1

mkdir -p out
ESBUILD=./node_modules/.bin/esbuild
COMMON=(--bundle --format=esm --platform=browser --target=es2022 --legal-comments=eof)

"$ESBUILD" node_modules/@observablehq/runtime/src/index.js   "${COMMON[@]}" --outfile=out/runtime.esm.js
"$ESBUILD" node_modules/@observablehq/inspector/src/index.js "${COMMON[@]}" --outfile=out/inspector.esm.js
"$ESBUILD" node_modules/@observablehq/stdlib/src/index.js    "${COMMON[@]}" --outfile=out/stdlib.esm.js
"$ESBUILD" node_modules/@observablehq/plot/src/index.js      "${COMMON[@]}" --outfile=out/plot.esm.js
"$ESBUILD" node_modules/d3/src/index.js                      "${COMMON[@]}" --outfile=out/d3.esm.js

echo "Verifying no bare-specifier imports remain..."
if grep -n '^import' out/*.esm.js | grep -Ev 'from "\.\/|from "\/' ; then
  echo "ERROR: bare import found above -- bundle is not self-contained." >&2
  exit 1
fi

mkdir -p "$VENDOR_DIR/dist" "$VENDOR_DIR/licenses"
cp out/*.esm.js "$VENDOR_DIR/dist/"

node -e '
const fs = require("fs");
const path = require("path");
const root = "node_modules";
function listPkgDirs(dir) {
  const out = [];
  for (const name of fs.readdirSync(dir)) {
    if (name === ".bin" || name === "esbuild" || name === "@esbuild") continue;
    const full = path.join(dir, name);
    if (name.startsWith("@")) {
      for (const sub of fs.readdirSync(full)) out.push(path.join(name, sub));
    } else {
      out.push(name);
    }
  }
  return out;
}
const vendorDir = process.argv[1];
const pkgs = listPkgDirs(root).sort();
const rows = [];
for (const p of pkgs) {
  const dir = path.join(root, p);
  const pkgJsonPath = path.join(dir, "package.json");
  if (!fs.existsSync(pkgJsonPath)) continue;
  const pj = JSON.parse(fs.readFileSync(pkgJsonPath, "utf8"));
  rows.push({ name: p, version: pj.version, license: pj.license || "UNKNOWN" });
  const files = fs.readdirSync(dir);
  const licFile = files.find(f => /^licen[cs]e/i.test(f));
  if (licFile) {
    const destDir = path.join(vendorDir, "licenses", p);
    fs.mkdirSync(destDir, { recursive: true });
    fs.copyFileSync(path.join(dir, licFile), path.join(destDir, licFile));
  }
}
fs.writeFileSync(path.join(vendorDir, "manifest.json"), JSON.stringify(rows, null, 2));
console.log(rows.length, "packages recorded in manifest.json");
' "$VENDOR_DIR"

echo "sha256 of the vendored bundles:"
sha256sum "$VENDOR_DIR"/dist/*.esm.js

echo "Done. Review the diff in $VENDOR_DIR and update the sha256 list in README.md."
