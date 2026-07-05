#!/usr/bin/env bash
# third_party/eleventy/install.sh
#
# Installs Eleventy (and its full dependency tree, 134 packages) into
# a target project directory WITHOUT touching the network, using the
# vendored npm cache at third_party/eleventy/npm-cache/.
#
# The vendored artifact is an npm cache directory (the same
# content-addressable tarball store `npm install` populates under
# ~/.npm), not a checked-in node_modules tree or loose .tgz files.
# This is the standard "npm ci --offline" recipe: point --cache at a
# directory that already holds every tarball named in
# package-lock.json (matched by integrity hash), and `npm ci --offline`
# resolves entirely from disk. See README.md for why this was chosen
# over individually-packed tarballs or a committed node_modules/.
#
# Usage:
#   third_party/eleventy/install.sh [target-dir]
#
# target-dir defaults to docs/ (the site's Eleventy project). It must
# already contain a package.json + package-lock.json whose resolved
# versions match what's in this cache (docs/package-lock.json is the
# one this cache was built from — see README.md).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
VENDOR_DIR="$REPO_ROOT/third_party/eleventy"
TARGET_DIR="${1:-$REPO_ROOT/docs}"

if [ ! -d "$VENDOR_DIR/npm-cache" ]; then
  echo "error: $VENDOR_DIR/npm-cache is missing -- nothing to install offline from." >&2
  exit 1
fi
if [ ! -f "$TARGET_DIR/package-lock.json" ]; then
  echo "error: $TARGET_DIR/package-lock.json not found." >&2
  exit 1
fi

cd "$TARGET_DIR"
echo "Installing Eleventy into $TARGET_DIR from vendored cache (offline)..."
npm ci --offline --cache="$VENDOR_DIR/npm-cache"
echo "Done. Verify with: npx @11ty/eleventy --version"
