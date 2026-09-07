#!/usr/bin/env bash
# Run the local RDF 1.2 Semantics tight-case suite.
#
# A thin wrapper around the W3C runner, needed only because the suite lives
# outside the vendored corpus and the runner locates that corpus by a fixed
# candidate list. RDF12_TESTS_BASE overrides the root; everything else — the
# manifest reader, the entailment arms, the scoring — is the same code path
# the vendored rdf12/rdf-semantics suite runs through, which is the point.
#
# Fixtures + manifest: tests/local/rdf12-semantics-tight/
# Reasoning + citations: docs/designissues/2026-09-07-rdf12-sparql12-semantics-fstar.md
#
# Exit 0 only when every case passes. This suite is a gate: a fail means
# either the engine regressed on a semantic condition we decided
# deliberately, or the decision changed and the design record has to change
# with it.

set -uo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if [ -n "${W3C_RUNNER_BIN:-}" ]; then
  BIN="$W3C_RUNNER_BIN"
else
  case "$(uname -s)/$(uname -m)" in
    Darwin/arm64)  BIN="bin/darwin-arm64/w3c_runner" ;;
    Darwin/x86_64) BIN="bin/darwin-x86_64/w3c_runner" ;;
    *)             BIN="bin/linux-x86_64/w3c_runner" ;;
  esac
fi

if [ ! -x "$BIN" ]; then
  echo "rdf12-semantics-tight: no w3c_runner at $BIN" >&2
  exit 2
fi

LOG="${RDF12_TIGHT_LOG:-formal/fstar/ocaml-output/rdf12_semantics_tight.log}"
mkdir -p "$(dirname "$LOG")"

RC=0
RDF12_TESTS_BASE=tests/local "$BIN" --rdf12entail rdf12-semantics-tight \
  2>&1 | tee "$LOG" || RC=$?

SCORE="$(grep -E '^TOTAL:' "$LOG" | tail -1)"
if [ -z "$SCORE" ]; then
  echo "rdf12-semantics-tight: runner produced no TOTAL line — treating as failure" >&2
  exit 2
fi

FAILS="$(printf '%s' "$SCORE" | sed -nE 's/.* ([0-9]+) fail.*/\1/p')"
if [ "${FAILS:-1}" != "0" ]; then
  echo "rdf12-semantics-tight: $SCORE" >&2
  exit 1
fi

echo "rdf12-semantics-tight: $SCORE"
exit "$RC"
