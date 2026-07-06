#!/usr/bin/env bash
# Regression pin for docs/designissues/2026-07-05-disk-backed-db-perf-review.md
# roadmap item 3: characteristic-set row clustering (--row-order cs) +
# eager sidecar build (--build-sidecars) in tools/corpus_pipeline.py must
# not change query answers versus the unmodified producer/SPOG path (row
# order is semantically free per docs/cottas-format-v1.md §3), and the
# sidecar files must exist on disk right after import when requested.
#
# Builds two COTTAS artifacts from the same small fixture
# (tests/local/data/cottas_sample.nq, already used by
# cottas_corpus_regressions.sh): one with today's default behaviour
# (--row-order producer, no eager sidecars) and one with the new
# characteristic-set-clustered + eager-sidecar path, then diffs four
# query results (named-graph SELECT, default-graph ASK, COUNT(*), and
# GRAPH ?g GROUP BY count) across them.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-cottas-roworder-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

INPUT="${ROOT}/tests/local/data/cottas_sample.nq"
PYCOTTAS_PYTHON="${PYCOTTAS_PYTHON:-${ROOT}/_tmp.junk/pycottas-venv/bin/python}"

UNCLUSTERED_ROOT="${WORKDIR}/unclustered"
CLUSTERED_ROOT="${WORKDIR}/clustered"
UNCLUSTERED_ARTIFACT="${UNCLUSTERED_ROOT}/sample-cottas/v1/data.cottas"
CLUSTERED_ARTIFACT="${CLUSTERED_ROOT}/sample-cottas/v1/data.cottas"

FAIL=0

"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" \
  --corpus-root "${UNCLUSTERED_ROOT}" \
  --dataset-name sample-cottas \
  --chunk-name sample-cottas \
  >"${WORKDIR}/build-unclustered.log" 2>&1

"${PYCOTTAS_PYTHON}" "${ROOT}/tools/corpus_pipeline.py" materialize-nq-cottas-corpus \
  --input "${INPUT}" \
  --corpus-root "${CLUSTERED_ROOT}" \
  --dataset-name sample-cottas \
  --chunk-name sample-cottas \
  --row-order cs \
  --build-sidecars \
  >"${WORKDIR}/build-clustered.log" 2>&1

if [[ ! -f "${UNCLUSTERED_ARTIFACT}" || ! -f "${CLUSTERED_ARTIFACT}" ]]; then
  echo "FAIL cottas-roworder-artifacts"
  cat "${WORKDIR}/build-unclustered.log" "${WORKDIR}/build-clustered.log"
  exit 1
fi
echo "PASS cottas-roworder-artifacts"

# Sidecars must exist next to the clustered artifact (eager import-time
# build), and must NOT be required to exist next to the unclustered one
# (today's default stays lazy -- only asserting the clustered path here).
SIDECAR_SUFFIXES=(.s.dict .s.presence .p.dict .p.presence .o.dict .o.presence .g.dict .g.presence .p.offsets .po.presence)
missing=0
for suf in "${SIDECAR_SUFFIXES[@]}"; do
  if [[ ! -f "${CLUSTERED_ARTIFACT}${suf}" ]]; then
    echo "  missing sidecar: ${CLUSTERED_ARTIFACT}${suf}"
    missing=1
  fi
done
if [[ "${missing}" -ne 0 ]]; then
  echo "FAIL cottas-roworder-sidecars-built"
  FAIL=1
else
  echo "PASS cottas-roworder-sidecars-built"
fi

run_query() {
  # run_query ARTIFACT QUERY_TEXT OUT_FILE
  FACTOIDAL_COTTAS_BRIDGE=/definitely/missing PYCOTTAS_PYTHON=/definitely/missing \
    "${BIN}" --data-cottas "$1" -e "$2" -o csv >"$3" 2>"${3}.err"
}

check_same() {
  # check_same NAME UNCLUSTERED_OUT CLUSTERED_OUT
  if ! diff -q <(sort "$2") <(sort "$3") >/dev/null; then
    echo "FAIL cottas-roworder-$1"
    echo "  --- unclustered ---"; cat "$2"
    echo "  --- clustered ---"; cat "$3"
    FAIL=1
  else
    echo "PASS cottas-roworder-$1"
  fi
}

# (a) named-graph SELECT
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <https://example.org/name> ?o } }" \
  "${WORKDIR}/unclustered.named.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <https://example.org/name> ?o } }" \
  "${WORKDIR}/clustered.named.csv"
check_same "named-graph-select" "${WORKDIR}/unclustered.named.csv" "${WORKDIR}/clustered.named.csv"

# (b) default-graph ASK
run_query "${UNCLUSTERED_ARTIFACT}" \
  "ASK { <https://example.org/default-subject> <https://example.org/status> \"default\" }" \
  "${WORKDIR}/unclustered.ask.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "ASK { <https://example.org/default-subject> <https://example.org/status> \"default\" }" \
  "${WORKDIR}/clustered.ask.csv"
check_same "default-graph-ask" "${WORKDIR}/unclustered.ask.csv" "${WORKDIR}/clustered.ask.csv"

# (c) COUNT(*) over the default graph -- correctness proof that
# clustering didn't drop/duplicate rows in the SPARQL-visible slice.
# (Only 1 quad is in the default graph in this fixture; { ?s ?p ?o }
# with no GRAPH clause queries the default graph only, per SPARQL 1.1
# dataset semantics -- this is not a full-corpus row count.)
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }" \
  "${WORKDIR}/unclustered.count.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }" \
  "${WORKDIR}/clustered.count.csv"
check_same "count-star" "${WORKDIR}/unclustered.count.csv" "${WORKDIR}/clustered.count.csv"

# Full-corpus row-count proof (all 5 quads, default + both named
# graphs) that CS clustering is a pure permutation: raw Parquet row
# count via DuckDB on both artifacts must equal the 5-quad input.
for pair in "unclustered:${UNCLUSTERED_ARTIFACT}" "clustered:${CLUSTERED_ARTIFACT}"; do
  tag="${pair%%:*}"; artifact="${pair#*:}"
  rowcount="$("${PYCOTTAS_PYTHON}" - "${artifact}" <<'PY'
import sys
import duckdb
print(duckdb.sql(f"SELECT COUNT(*) FROM read_parquet('{sys.argv[1]}')").fetchone()[0])
PY
)"
  if [[ "${rowcount}" != "5" ]]; then
    echo "FAIL cottas-roworder-full-row-count-${tag} (expected 5, got ${rowcount})"
    FAIL=1
  else
    echo "PASS cottas-roworder-full-row-count-${tag}"
  fi
done

# (d) GRAPH ?g GROUP BY count
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g" \
  "${WORKDIR}/unclustered.gcount.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g" \
  "${WORKDIR}/clustered.gcount.csv"
check_same "graph-groupby-count" "${WORKDIR}/unclustered.gcount.csv" "${WORKDIR}/clustered.gcount.csv"

# (e)-(h) Bound-predicate exact-COUNT regression (2026-07-06,
# docs/designissues/2026-07-05-disk-backed-db-perf-review.md roadmap
# item 4): `cottas_ondisk_count_exact` used to decode ALL FOUR s/p/o/g
# columns of every row group whenever any of s/p/o was bound, even
# though `cell_match None _` always matches -- an unbound column's
# VALUE is never needed for a count-only query. The fix
# (`walk_row_groups_count_exact_global` /
# `count_selective_matches_seq` in RDF.CottasStore.fst) decodes only
# the columns whose bound is actually `Some`.
#
# IMPORTANT: these queries deliberately do NOT wrap the triple pattern
# in `GRAPH ?g { ... }` -- `SPARQL11.Store.fst`'s
# `detect_streaming_count_star` (the only caller of
# `cottas_ondisk_count_exact`) matches via `extract_single_tp_bgp`,
# which requires a BARE `GP_BGP [tp]`, not `GP_Graph gv (GP_BGP [tp])`.
# A `GRAPH ?g { ... }`-wrapped COUNT never reaches this fast path at
# all (it falls through to the generic materialise-then-count
# evaluator instead) -- confirmed by hitting an unrelated pre-existing
# bug in the CS-clustered on-disk SEARCH path (a bound-p+bound-o
# pattern under `GRAPH ?g` returned 0 instead of 1 on the clustered
# build only, traced to `filter_candidates_by_compound_po`'s
# `.po.presence` consult, NOT to this fix -- `cottas_ondisk_count_exact`
# never calls that function at all). Filed as a followup, out of scope
# for this item; these checks use bare BGPs against the fixture's
# single default-graph quad
# (`<default-subject> <status> "default">`) so they actually exercise
# the changed code path. Each is checked for cross-build agreement AND
# a literal expected count, so a regression that returns the same
# wrong number on both builds still fails.
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { ?s <https://example.org/status> ?o }" \
  "${WORKDIR}/unclustered.count-p.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { ?s <https://example.org/status> ?o }" \
  "${WORKDIR}/clustered.count-p.csv"
check_same "count-bound-p" "${WORKDIR}/unclustered.count-p.csv" "${WORKDIR}/clustered.count-p.csv"
if [[ "$(tail -n1 "${WORKDIR}/unclustered.count-p.csv" | tr -d '\r')" != "1" ]]; then
  echo "FAIL cottas-roworder-count-bound-p-value (expected 1)"
  cat "${WORKDIR}/unclustered.count-p.csv"
  FAIL=1
else
  echo "PASS cottas-roworder-count-bound-p-value"
fi

run_query "${UNCLUSTERED_ARTIFACT}" \
  'SELECT (COUNT(*) AS ?n) WHERE { ?s <https://example.org/status> "default" }' \
  "${WORKDIR}/unclustered.count-po.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  'SELECT (COUNT(*) AS ?n) WHERE { ?s <https://example.org/status> "default" }' \
  "${WORKDIR}/clustered.count-po.csv"
check_same "count-bound-p-o" "${WORKDIR}/unclustered.count-po.csv" "${WORKDIR}/clustered.count-po.csv"
if [[ "$(tail -n1 "${WORKDIR}/unclustered.count-po.csv" | tr -d '\r')" != "1" ]]; then
  echo "FAIL cottas-roworder-count-bound-p-o-value (expected 1)"
  cat "${WORKDIR}/unclustered.count-po.csv"
  FAIL=1
else
  echo "PASS cottas-roworder-count-bound-p-o-value"
fi

run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { <https://example.org/default-subject> ?p ?o }" \
  "${WORKDIR}/unclustered.count-s.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { <https://example.org/default-subject> ?p ?o }" \
  "${WORKDIR}/clustered.count-s.csv"
check_same "count-bound-s" "${WORKDIR}/unclustered.count-s.csv" "${WORKDIR}/clustered.count-s.csv"
if [[ "$(tail -n1 "${WORKDIR}/unclustered.count-s.csv" | tr -d '\r')" != "1" ]]; then
  echo "FAIL cottas-roworder-count-bound-s-value (expected 1)"
  cat "${WORKDIR}/unclustered.count-s.csv"
  FAIL=1
else
  echo "PASS cottas-roworder-count-bound-s-value"
fi

run_query "${UNCLUSTERED_ARTIFACT}" \
  'SELECT (COUNT(*) AS ?n) WHERE { ?s <https://example.org/status> "nonexistent" }' \
  "${WORKDIR}/unclustered.count-zero.csv"
run_query "${CLUSTERED_ARTIFACT}" \
  'SELECT (COUNT(*) AS ?n) WHERE { ?s <https://example.org/status> "nonexistent" }' \
  "${WORKDIR}/clustered.count-zero.csv"
check_same "count-bound-p-o-zero-match" "${WORKDIR}/unclustered.count-zero.csv" "${WORKDIR}/clustered.count-zero.csv"
if [[ "$(tail -n1 "${WORKDIR}/unclustered.count-zero.csv" | tr -d '\r')" != "0" ]]; then
  echo "FAIL cottas-roworder-count-bound-p-o-zero-value (expected 0)"
  cat "${WORKDIR}/unclustered.count-zero.csv"
  FAIL=1
else
  echo "PASS cottas-roworder-count-bound-p-o-zero-value"
fi

# (i) Second-boot-must-not-rebuild pin (2026-07-05 companion-magic fix).
# Once the ten sidecars exist (built eagerly at import above), a boot
# of the on-disk path must skip ALL rebuild paths: no
# "companion header verify FAILED", no "building all companions", no
# lamed3 offsets build, no compound-po build. Before the
# RDF.CottasStore.DictWriter.fst dict_magic fix ('COKD' -> 'COTD',
# matching RDF.CottasStore.OnDiskIndex.fst's cotd_magic_u32), the four
# .dict/.presence pairs failed header verification on every single
# boot -- ~57 s of rebuild per server start on the 888,949-quad gene
# store -- even immediately after being written by the same binary.
BOOT_LOG="${WORKDIR}/second-boot.log"
FACTOIDAL_COTTAS_BRIDGE=/definitely/missing PYCOTTAS_PYTHON=/definitely/missing \
  "${BIN}" query --data-cottas "${CLUSTERED_ARTIFACT}" \
  --explain "SELECT * WHERE { ?s ?p ?o } LIMIT 1" \
  >/dev/null 2>"${BOOT_LOG}"
REBUILD_MARKERS='companion header verify FAILED|companion header read FAILED|companion absent for col=|building all companions|offsets file absent; building|\[lamed3-trace\] building offsets|\[compound-po-trace\] columnscan'
if grep -Eq "${REBUILD_MARKERS}" "${BOOT_LOG}"; then
  echo "FAIL cottas-roworder-second-boot-no-rebuild"
  echo "  boot log rebuild lines:"
  grep -E "${REBUILD_MARKERS}" "${BOOT_LOG}" | sed 's/^/    /'
  FAIL=1
elif ! grep -q "skipping pre-warm" "${BOOT_LOG}"; then
  echo "FAIL cottas-roworder-second-boot-no-rebuild (no 'skipping pre-warm' marker; boot log follows)"
  sed 's/^/    /' "${BOOT_LOG}"
  FAIL=1
else
  echo "PASS cottas-roworder-second-boot-no-rebuild"
fi

# (j)-(p) GRAPH-wrapped compound (p,o) prune matrix (issue #297,
# 2026-07-06, docs/designissues/2026-07-05-disk-backed-db-perf-review.md
# roadmap item 4 follow-up). Root cause: `filter_candidates_by_compound_po`
# in `RDF.CottasStore.fst` resolved its predicate/object token ids via
# `ondisk_lookup_pred_id_global` / `_obj_id_global` (the Bet7 lazy-runtime
# revmap, id = FIRST-OCCURRENCE order over the physical row scan) instead
# of via the `.p.dict` / `.o.dict` companion files (id = SORTED-LEXICOGRAPHIC
# RANK, the space `.po.presence`'s writer actually used, per
# `RDF.CottasStore.DictWriter.fst`'s `ids[i] = i` invariant and
# `Cottas_compound_po_writer.build_tok_to_id`). The two id-spaces happen
# to coincide on a small producer-order (SPOG-sorted) build by
# coincidence, but diverge once CS clustering changes physical row
# order, so the reader binary-searches the WRONG pair-code and
# `compound_rg_passes_pair` wrongly prunes the one row group that DOES
# contain the (p, o) pair -- a wrong `0`/empty answer, not a slow one.
# Fix: `filter_candidates_by_compound_po` now resolves ids via the new
# `compound_po_dict_encode` helper (reads `.p.dict` / `.o.dict` directly,
# order-independent), matching the writer. The `.po.presence` bytes
# on disk were always correct -- this was a READER bug, not a writer
# bug, so no existing-store migration/rebuild is needed.
#
# Each shape below is checked for THREE-WAY agreement -- CS-clustered
# build, producer-order build, AND the in-memory engine loading the
# same fixture directly (`--data`, no COTTAS at all) -- plus a literal
# expected row count, so a regression that returns the same wrong
# answer on all three builds still fails.
csv_data_row_count() {
  # csv_data_row_count FILE -- number of CSV data rows (total lines minus
  # the header line). The runner always emits a header, even for a
  # zero-row result (verified empirically: "g,s" with no further lines).
  local file="$1"
  local total
  total="$(wc -l < "${file}" | tr -d ' ')"
  if [[ "${total}" -eq 0 ]]; then
    echo 0
  else
    echo $((total - 1))
  fi
}

three_way_check() {
  # three_way_check NAME QUERY EXPECTED_N
  local name="$1" query="$2" expected="$3"
  local out_uncl="${WORKDIR}/3way.${name}.uncl.csv"
  local out_cl="${WORKDIR}/3way.${name}.cl.csv"
  local out_mem="${WORKDIR}/3way.${name}.mem.csv"
  run_query "${UNCLUSTERED_ARTIFACT}" "${query}" "${out_uncl}"
  run_query "${CLUSTERED_ARTIFACT}" "${query}" "${out_cl}"
  FACTOIDAL_COTTAS_BRIDGE=/definitely/missing PYCOTTAS_PYTHON=/definitely/missing \
    "${BIN}" --data "${INPUT}" -e "${query}" -o csv >"${out_mem}" 2>"${out_mem}.err"

  local ok=1
  if ! diff -q <(sort "${out_uncl}") <(sort "${out_cl}") >/dev/null; then
    ok=0
  fi
  if ! diff -q <(sort "${out_uncl}") <(sort "${out_mem}") >/dev/null; then
    ok=0
  fi
  local got
  got="$(csv_data_row_count "${out_uncl}")"
  if [[ "${got}" != "${expected}" ]]; then
    ok=0
  fi

  if [[ "${ok}" -eq 1 ]]; then
    echo "PASS cottas-roworder-graph-${name}"
  else
    echo "FAIL cottas-roworder-graph-${name} (expected ${expected} rows; unclustered=${got:-?})"
    echo "  --- unclustered (producer-order COTTAS) ---"; cat "${out_uncl}"
    echo "  --- clustered (CS-clustered COTTAS) ---"; cat "${out_cl}"
    echo "  --- in-memory engine ---"; cat "${out_mem}"
    FAIL=1
  fi
}

# (j) bound-p only (2 matches: alice/name/Alice, bob/name/Bob)
three_way_check "bound-p" \
  "SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <https://example.org/name> ?o } }" \
  2

# (k) bound-o only (1 match: alice/name/Alice)
three_way_check "bound-o" \
  'SELECT ?g ?s ?p WHERE { GRAPH ?g { ?s ?p "Alice" } }' \
  1

# (l) bound-p AND bound-o -- THE FAILING SHAPE reported 2026-07-06:
# returned 0 instead of 1 on the CS-clustered build only, before the fix.
three_way_check "bound-p-and-o" \
  'SELECT ?g ?s WHERE { GRAPH ?g { ?s <https://example.org/name> "Alice" } }' \
  1

# (m) bound-p AND bound-o, IRI-typed object (not just literal) -- the
# `.o.dict` token includes angle-bracket IRIs too; exercise that path.
three_way_check "bound-p-and-o-iri-object" \
  "SELECT ?g ?s WHERE { GRAPH ?g { ?s <https://example.org/knows> <https://example.org/bob> } }" \
  1

# (n) bound-p AND bound-o, zero matches (name/"Specimen" doesn't exist)
three_way_check "bound-p-and-o-zero" \
  'SELECT ?g ?s WHERE { GRAPH ?g { ?s <https://example.org/name> "Specimen" } }' \
  0

# (o) bound-s AND bound-p (2-of-3 bound; different code path than (l))
three_way_check "bound-s-and-p" \
  "SELECT ?g ?o WHERE { GRAPH ?g { <https://example.org/alice> <https://example.org/name> ?o } }" \
  1

# (p) bound-s only (2 matches: alice/name/Alice, alice/knows/bob)
three_way_check "bound-s" \
  "SELECT ?g ?p ?o WHERE { GRAPH ?g { <https://example.org/alice> ?p ?o } }" \
  2

# (q)-(r) Issue #297 item 1: streaming-COUNT(*) fast-path widened to
# GRAPH <constant-iri> { tp } (SPARQL11.Store.fst's
# `extract_single_tp_bgp_scoped` / `detect_streaming_count_star`). This
# is a DIFFERENT code path than (j)-(p) above -- COUNT(*) dispatches to
# `cottas_ondisk_count_exact`, which never calls
# `filter_candidates_by_compound_po` at all (confirmed in the perf
# review doc), so these checks pin the NEW feature, not the (j)-(p) bug
# fix. GRAPH ?g (unbound variable) COUNT(*) is deliberately NOT
# fast-pathed (would need a sum-across-all-named-graphs evaluation
# shape, not a single dataset scope) and still takes the materialise
# path -- not tested here since its correctness was never in question.
three_way_check "count-fastpath-named-graph-people" \
  "SELECT (COUNT(*) AS ?n) WHERE { GRAPH <https://example.org/graph/people> { ?s ?p ?o } }" \
  1
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { GRAPH <https://example.org/graph/people> { ?s ?p ?o } }" \
  "${WORKDIR}/count-fastpath.csv"
if [[ "$(tail -n1 "${WORKDIR}/count-fastpath.csv" | tr -d '\r')" != "3" ]]; then
  echo "FAIL cottas-roworder-count-fastpath-named-graph-people-value (expected 3)"
  cat "${WORKDIR}/count-fastpath.csv"
  FAIL=1
else
  echo "PASS cottas-roworder-count-fastpath-named-graph-people-value"
fi
run_query "${UNCLUSTERED_ARTIFACT}" \
  "SELECT (COUNT(*) AS ?n) WHERE { GRAPH <https://example.org/graph/does-not-exist> { ?s ?p ?o } }" \
  "${WORKDIR}/count-fastpath-unknown-graph.csv"
if [[ "$(tail -n1 "${WORKDIR}/count-fastpath-unknown-graph.csv" | tr -d '\r')" != "0" ]]; then
  echo "FAIL cottas-roworder-count-fastpath-unknown-graph-value (expected 0)"
  cat "${WORKDIR}/count-fastpath-unknown-graph.csv"
  FAIL=1
else
  echo "PASS cottas-roworder-count-fastpath-unknown-graph-value"
fi

exit "${FAIL}"
