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
# Stay at repo root — the w3c_runner resolves test-fixture base URIs
# using Sys.getcwd() when no mf:assumedTestBase is present, so CWD
# must be the repo root to match the historical baseline. Some rdf-xml
# tests silently diverge (same triple counts, different IRI strings) if
# CWD changes between runs. Keep this invariant.
cd "$REPO_ROOT"

if [ "${1:-}" = "--cached" ]; then
  exec ./formal/fstar/generate-report.sh
else
  exec ./formal/fstar/generate-report.sh --run
fi
