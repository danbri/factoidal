#!/bin/bash
# Q03 fix: disable Lamed3's *_via_offsets dispatchers so they always
# fall through to *_inner. The slow paths inside *_via_offsets do 3
# full DLBA column decodes per candidate row group when bound_o or
# bound_s is set — taking 30+ s on parliament for queries like
# `?o a wktLiteral`. *_inner has Tet3's bitmap prune correctly wired
# and answers in microseconds for the same shape.
#
# Diagnosis traced by --explain (commit c8e317f) — the F* planner
# correctly picks T2(est=0) first; the runtime stalls in lamed3's
# search/estimate offset path. Independent confirmation from
# reviewer 2026-04-26.
#
# Strategy: rather than do delicate surgery inside the slow loops
# (multi-line Printf format strings broke anchor-matching twice),
# replace the function call in each dispatcher with a literal None.
# The *_via_offsets functions are still defined (still extracted,
# still compile) — they just never run. Each dispatcher's
# `match X with Some -> Y | None -> Z` falls through to Z (*_inner).
#
# Compliance: rule #11 allows bug fixes to existing OCaml glue. This
# is a bug fix to Lamed3's perf shim — no new semantic logic, just
# bypass of a buggy fast path. Rolls back trivially. Becomes
# obsolete and deletable when fstar-purity-unwind.md Phase 2.6
# retires Lamed3 entirely.

set -euo pipefail

ML="ocaml-output/RDF_CottasStore.ml"

if [ ! -f "$ML" ]; then
  echo "  WARN: $ML not found; skipping q03_estimate_fix patch."
  exit 0
fi

if grep -q 'q03_estimate_fix marker' "$ML"; then
  echo "  [q03_estimate_fix] already applied; skipping."
  exit 0
fi

python3 <<'PY'
import sys

ML = "ocaml-output/RDF_CottasStore.ml"
with open(ML, "r") as f:
    src = f.read()

# Marker so re-runs don't double-apply.
MARKER = "(* q03_estimate_fix marker — disables lamed3 *_via_offsets dispatchers *)"

# Pattern 1: estimate_fast dispatcher
estimate_old = ('  let rec estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =\n'
                '    match estimate_fast_via_offsets h bound with')
estimate_new = ('  ' + MARKER + '\n'
                '  let rec estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =\n'
                '    match (None : pint option) with  (* q03_estimate_fix: bypass *_via_offsets *)')

# Pattern 2: search_fast dispatcher
search_old = ('  let rec search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)\n'
              '    : Parser_BallyhooCOTTAS.cottas_qp_row list =\n'
              '    (* lamed3: try offset-index path first. *)\n'
              '    match search_fast_via_offsets h bound with')
search_new = ('  let rec search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)\n'
              '    : Parser_BallyhooCOTTAS.cottas_qp_row list =\n'
              '    (* q03_estimate_fix: bypass lamed3 *_via_offsets — falls through to *_inner *)\n'
              '    match (None : Parser_BallyhooCOTTAS.cottas_qp_row list option) with')

# Pattern 3: search_fast_limited dispatcher
limited_old = '    match search_fast_limited_via_offsets h bound limit with\n'
limited_new = '    match (None : Parser_BallyhooCOTTAS.cottas_qp_row list option) with  (* q03_estimate_fix: bypass *)\n'

applied = []

if estimate_old in src:
    src = src.replace(estimate_old, estimate_new, 1)
    applied.append("estimate_fast")

if search_old in src:
    src = src.replace(search_old, search_new, 1)
    applied.append("search_fast")

if limited_old in src:
    src = src.replace(limited_old, limited_new, 1)
    applied.append("search_fast_limited")

if not applied:
    sys.stderr.write("  [q03_estimate_fix] WARN: no dispatchers matched; check anchor strings.\n")
    sys.exit(0)

with open(ML, "w") as f:
    f.write(src)

print("  [q03_estimate_fix] disabled lamed3 *_via_offsets dispatchers in: " + ", ".join(applied))
PY
