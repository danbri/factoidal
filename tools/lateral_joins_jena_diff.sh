#!/usr/bin/env bash
# Differential test: run every LATERAL fixture through both factoidal
# and Apache Jena 5.2.0 (arq) against the same data, sort rows (no
# ORDER BY guarantees a stable order across engines), and diff. Reports
# "N of M agree with Jena 5.2.0" per rule #25 (labelled scores only).
#
# Jena is cached at ~/.cache/factoidal-bench/apache-jena-5.2.0 --
# tools/bench-competitive.sh fetches it if absent. If java is
# unavailable, this script SKIPS (does not fabricate a Jena row).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
DATA="${ROOT}/tests/local/data/lateral_sample.nq"
SPARQL_DIR="${ROOT}/tests/local/sparql"

JENA_VERSION="${JENA_VERSION:-5.2.0}"
JENA_CACHE_ROOT="${JENA_CACHE_ROOT:-${HOME}/.cache/factoidal-bench}"
JENA_HOME_DEFAULT="${JENA_CACHE_ROOT}/apache-jena-${JENA_VERSION}"
JENA_HOME="${JENA_HOME:-${JENA_HOME_DEFAULT}}"

if ! command -v java >/dev/null 2>&1; then
  echo "SKIP: java not available in this sandbox -- cannot run arq. Expected answers were hand-verified against a real Jena 5.2.0 run and are pinned in tests/local/lateral_joins.sh."
  exit 0
fi

if [[ ! -x "${JENA_HOME}/bin/arq" ]]; then
  echo "SKIP: Jena not found at ${JENA_HOME} -- run tools/bench-competitive.sh once to fetch it, or set JENA_HOME."
  exit 0
fi

if [[ ! -x "${BIN}" ]]; then
  echo "factoidal binary not found at ${BIN}" >&2
  exit 1
fi

ARQ="${JENA_HOME}/bin/arq"

# Fixtures that produce comparable answer sets (the three illegal-
# reassignment fixtures are checked for rejection in tests/local/
# lateral_joins.sh instead -- a diff there is "both engines reject",
# not a row-level comparison).
FIXTURES=(
  lateral_topn_per_key.rq
  lateral_subselect_masking.rq
  lateral_plain_bgp.rq
  lateral_vs_join_naive.rq
  lateral_empty_lhs.rq
  lateral_empty_rhs_per_row.rq
)

agree=0
total=0

for rq in "${FIXTURES[@]}"; do
  total=$((total + 1))
  # Jena's CSV writer emits CRLF line endings; factoidal emits LF.
  # Strip \r before comparing so the diff is content-only.
  factoidal_out="$("${BIN}" --data "${DATA}" --query "${SPARQL_DIR}/${rq}" -o csv 2>/dev/null | tr -d '\r' | tail -n +2 | sort)"
  jena_out="$("${ARQ}" --data "${DATA}" --query "${SPARQL_DIR}/${rq}" --results=CSV 2>/dev/null | grep -v '^Picked up' | tr -d '\r' | tail -n +2 | sort)"
  if [[ "${factoidal_out}" == "${jena_out}" ]]; then
    echo "AGREE ${rq}"
    agree=$((agree + 1))
  else
    echo "DISAGREE ${rq}"
    echo "  --- factoidal ---"
    printf '  %s\n' "${factoidal_out}"
    echo "  --- jena ${JENA_VERSION} ---"
    printf '  %s\n' "${jena_out}"
  fi
done

echo "${agree} of ${total} agree with Jena ${JENA_VERSION}"
if [[ ${agree} -ne ${total} ]]; then
  exit 1
fi
