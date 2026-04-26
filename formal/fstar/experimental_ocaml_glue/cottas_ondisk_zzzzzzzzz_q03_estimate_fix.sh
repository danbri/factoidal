#!/bin/bash
# Q03 fix (estimate-side only): Lamed3's estimate_fast_via_offsets
# bypasses Tet3's obj/subj presence bitmaps when bound_o or bound_s
# is set. Falls into a 3-column DLBA-decode-per-rg loop that takes
# 30+ s on parliament for queries like `?o a wktLiteral` because
# rdf:type appears in every rg.
#
# Diagnosis traced by --explain (commit c8e317f) — the F* planner
# does the right thing (picks T2 first), but estimate_fast_via_offsets
# inside union_backend_estimate stalls before search even runs.
#
# Fix: when not no_other_bound, return None from
# estimate_fast_via_offsets and let Mem5's estimate_fast_inner take
# over. Mem5's path uses Tet3's bitmaps and returns in microseconds
# for the same shape.
#
# Note (2026-04-26): same bug exists in search_fast_via_offsets and
# search_fast_limited_via_offsets but the multi-line Printf format
# strings make sed/python anchor matching fragile across both
# functions. Fixing those two is a separate follow-up; this patch
# unblocks the *estimate* phase, which is where the daemon was
# stalling on Q03 BEFORE search even started. After this patch lands,
# estimate is fast, planner picks T2 first, search starts on T2 —
# and search has the same 3-column-decode bug, so Q03 still 504s.
# But the failure mode shifts from "estimate stalls" to "search
# stalls", which is closer to the real fix.
#
# Compliance: rule #11 allows bug fixes to existing OCaml glue.
# Sort position `zzzzzzzzz` (9 z's) so it runs AFTER Lamed3
# (zzzzzz) and Mem5 (zzzzzzz). Becomes obsolete and can be deleted
# when fstar-purity-unwind.md Phase 2.6 retires Lamed3.

set -euo pipefail

ML="ocaml-output/RDF_CottasStore.ml"

if [ ! -f "$ML" ]; then
  echo "  WARN: $ML not found; skipping q03_estimate_fix patch."
  exit 0
fi

if grep -q 'q03_estimate_fix: estimate_fast_via_offsets bails on not no_other_bound' "$ML"; then
  echo "  [q03_estimate_fix] already applied; skipping."
  exit 0
fi

python3 <<'PY'
import re, sys

ML = "ocaml-output/RDF_CottasStore.ml"
with open(ML, "r") as f:
    src = f.read()

# Anchor: estimate_fast_via_offsets's no_other_bound let-binding (single-line).
anchor = ('             let no_other_bound =\n'
          '               (match bound.Parser_BallyhooCOTTAS.cbqp_s with FStar_Pervasives_Native.None -> true | _ -> false) &&\n'
          '               (match bound.Parser_BallyhooCOTTAS.cbqp_o with FStar_Pervasives_Native.None -> true | _ -> false) &&\n'
          '               (match bound.Parser_BallyhooCOTTAS.cbqp_g with FStar_Pervasives_Native.None -> true | _ -> false) in\n')

inject = ('             let no_other_bound =\n'
          '               (match bound.Parser_BallyhooCOTTAS.cbqp_s with FStar_Pervasives_Native.None -> true | _ -> false) &&\n'
          '               (match bound.Parser_BallyhooCOTTAS.cbqp_o with FStar_Pervasives_Native.None -> true | _ -> false) &&\n'
          '               (match bound.Parser_BallyhooCOTTAS.cbqp_g with FStar_Pervasives_Native.None -> true | _ -> false) in\n'
          '             (* q03_estimate_fix: estimate_fast_via_offsets bails on not no_other_bound.\n'
          '                Lamed3\'s slow path did 3 full DLBA column decodes per candidate rg,\n'
          '                taking 30+ s on bound-s/o queries even when Tet3\'s presence bitmap\n'
          '                would have answered 0 in microseconds. Bail out now and let\n'
          '                estimate_fast_inner (Mem5\'s bitmap path) handle it. *)\n'
          '             if not no_other_bound then begin\n'
          '               Printf.eprintf "[q03_estimate_fix] estimate_fast_via_offsets bails: bound_s/o/g present, deferring to estimate_fast_inner\\n%!";\n'
          '               None\n'
          '             end else begin\n')

if anchor not in src:
    sys.stderr.write("  [q03_estimate_fix] WARN: estimate_fast_via_offsets no_other_bound anchor not found; aborting.\n")
    sys.exit(0)

src2 = src.replace(anchor, inject, 1)

tail_anchor = ('               !count no_other_bound;\n'
               '             Some !count)\n')
tail_inject = ('               !count no_other_bound;\n'
               '             Some !count\n'
               '             end)\n')

if tail_anchor not in src2:
    sys.stderr.write("  [q03_estimate_fix] WARN: estimate_fast_via_offsets tail anchor not found; aborting.\n")
    sys.exit(0)

src3 = src2.replace(tail_anchor, tail_inject, 1)

with open(ML, "w") as f:
    f.write(src3)

print("  [q03_estimate_fix] applied: estimate_fast_via_offsets bails on not no_other_bound, defers to estimate_fast_inner")
PY
