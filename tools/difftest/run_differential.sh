#!/usr/bin/env bash
# Differential testing harness driver (issue #317, review gate 4).
#
# Fuzzes RDF parsers (N-Triples/Turtle/N-Quads/TriG/RDF-XML) and SPARQL
# evaluation against independent reference implementations (pyoxigraph /
# Oxigraph for RDFC-1.0 canonicalization + SPARQL; rdflib for SPARQL),
# writing JSON reports under .claude-runs/difftest/. See
# docs/designissues/2026-07-29-differential-testing-ledger.md for the
# triaged findings from the baseline run.
#
# Usage:
#   tools/difftest/run_differential.sh [N_RDF] [N_SPARQL]
#
# Caps each phase at 10 minutes (anti-pattern #17); run this in the
# background for larger N (anti-pattern #20).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

N_RDF="${1:-200}"
N_SPARQL="${2:-80}"
OUT_DIR="${OUT_DIR:-.claude-runs/difftest}"
mkdir -p "$OUT_DIR"

echo "== differential testing: RDF parser harness (n=$N_RDF) =="
timeout 570 python3 tools/difftest/rdf_diff.py \
  --n "$N_RDF" --seed-base "${RDF_SEED_BASE:-10000}" \
  --out "$OUT_DIR/rdf-corpus"

echo "== differential testing: SPARQL evaluation harness (n=$N_SPARQL) =="
timeout 570 python3 tools/difftest/sparql_diff.py \
  --n "$N_SPARQL" --seed-base "${SPARQL_SEED_BASE:-20000}" \
  --out "$OUT_DIR/sparql-corpus"

echo "== reports =="
echo "  $OUT_DIR/rdf-corpus/report.json"
echo "  $OUT_DIR/sparql-corpus/report.json"
echo "Triage ledger: docs/designissues/2026-07-29-differential-testing-ledger.md"
