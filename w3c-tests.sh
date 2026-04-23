#!/usr/bin/env bash
# w3c-tests.sh — run the W3C conformance suites and regenerate the
# test-results page plus machine-readable artifacts.
#
# Thin wrapper around formal/fstar/generate-report.sh so top-level use
# is one command. Produces:
#
#   docs/test-results/index.html
#   docs/test-results/latest.csv
#   docs/test-results/latest.json
#   docs/test-results/history/<iso-timestamp>.{csv,json}
#   formal/fstar/ocaml-output/sparql_results.log   (raw runner log)
#   formal/fstar/ocaml-output/rdf_results.log      (raw runner log)
#
# Usage:
#   ./w3c-tests.sh           # run the tests and regenerate
#   ./w3c-tests.sh --cached  # regenerate from the last log, no re-run

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT/formal/fstar"

if [ "${1:-}" = "--cached" ]; then
  exec ./generate-report.sh
else
  exec ./generate-report.sh --run
fi
