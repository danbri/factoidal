#!/usr/bin/env bash
# ensure-test-env.sh — make THIS checkout (main clone, git worktree, or CI
# runner) able to run every test suite: initialise all test-data
# submodules and verify each suite's fixtures are actually present.
#
# Why this exists: `git worktree add` does NOT populate submodules, and a
# fresh container populates none. Every gap shows up later as a lying
# score — a 0/0 dashboard row, a runner reporting "0 tests", or hub tests
# failing on ENOENT that get misread as engine regressions. This session
# hit all three. Run this FIRST in any environment that will run tests;
# it is idempotent and a fast no-op when everything is present.
#
# Usage:
#   tools/ensure-test-env.sh           # init + verify, labelled table
#   tools/ensure-test-env.sh --check   # verify only (no network), rc=1 if gaps
#
# Exit codes: 0 = all suites present; 1 = something missing (output says
# what and what it breaks). NEVER trust a suite score from a checkout
# where this script exits 1.

set -u
CHECK_ONLY=0
[ "${1:-}" = "--check" ] && CHECK_ONLY=1

# Resolve the checkout root this script is invoked FROM (worktree-safe:
# use git, not the script's own location, so a worktree that ran a
# main-checkout copy still operates on itself).
ROOT="$(git rev-parse --show-toplevel 2>/dev/null)"
if [ -z "$ROOT" ]; then
  echo "ensure-test-env: not inside a git checkout" >&2
  exit 1
fi
cd "$ROOT"

# 1. Initialise every test-data submodule (idempotent; needs network
#    only on first population of a given container).
if [ "$CHECK_ONLY" -eq 0 ]; then
  SUBS=$(git config -f .gitmodules --get-regexp path 2>/dev/null \
          | awk '$2 ~ /^third_party\/testing\// {print $2}')
  if [ -n "$SUBS" ]; then
    # shellcheck disable=SC2086
    git submodule update --init --jobs 4 $SUBS \
      || echo "ensure-test-env: submodule init reported errors (offline?) — verification below shows what is usable" >&2
  fi
fi

# 2. Verify per-suite sentinel paths — one representative file/dir per
#    suite, chosen from what its runner actually opens. A suite absent
#    here means its runner/dashboard row LIES (0/0 or ENOENT), so the
#    table names the consumer that breaks.
MISSING=0
check() { # path, suite label, consumer that breaks without it
  if [ -e "$ROOT/$1" ]; then
    printf "  ok       %-22s %s\n" "$2" "$1"
  else
    printf "  MISSING  %-22s %s  -> breaks: %s\n" "$2" "$1" "$3"
    MISSING=1
  fi
}

echo "ensure-test-env: suite fixture verification ($ROOT)"
check third_party/testing/w3c/README.md              "sparql+rdf (W3C)"   "w3c_runner, the 631/0+1031/0 floors"
check third_party/testing/rdf-canon                  "rdfc10"             "rdfc10_runner"
check third_party/testing/shacl                      "shacl"              "shacl_runner, dashboard shacl rows"
check third_party/testing/shex                       "shex"               "shex_runner"
check third_party/testing/json-ld                    "jsonld"             "jsonld_runner + fromrdf_runner, hub post07"
check third_party/testing/csvw                       "csvw"               "csvw_runner, npm csvw tests, hub post13"
check third_party/testing/vc                         "vc"                 "vc_runner, hub post13"
check third_party/testing/did                        "did"                "did_runner, hub post23"
check third_party/testing/rml-modules/rml-core       "rml-core"           "rml_runner (76/76 floor), hub post09"
check third_party/testing/rml-modules/rml-io         "rml-io"             "rml_runner --all"
check third_party/testing/rml-modules/rml-cc         "rml-cc"             "rml_runner --all"
check third_party/testing/rml-modules/rml-fnml       "rml-fnml"           "future rml_runner"
check third_party/testing/rml-modules/rml-star       "rml-star"           "future rml_runner"
# Vendored-in-tree (not submodules) — regressions here mean a bad
# checkout/sparse clone rather than submodule drift, but verify anyway:
check third_party/testing/xml/xmlconf                "xml-conformance"    "xml_runner (1414/0/1171 row)"
check third_party/testing/xslt/manifest.json         "xslt"               "xslt_runner"
check third_party/testing/owl                        "owl"                "owl_runner"
check third_party/testing/hdt/rml-core-ontology.hdt  "hdt"                "hdt parity, hub post24, npm hdt tests"

if [ "$MISSING" -eq 1 ]; then
  echo "ensure-test-env: GAPS FOUND — do not trust 0/0 scores or ENOENT test failures from this checkout." >&2
  echo "ensure-test-env: rerun without --check (needs network) or copy fixtures from a populated checkout." >&2
  exit 1
fi
echo "ensure-test-env: all suites present."
