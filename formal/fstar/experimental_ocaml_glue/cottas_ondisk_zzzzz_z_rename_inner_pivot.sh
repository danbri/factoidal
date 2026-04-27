#!/bin/bash
# Rename pivot — issue #105.
#
# Decouples the `search_fast`/`estimate_fast`/`search_fast_limited`
# rename from Lamed3's reader half. Without this patch, Lamed3 owns
# both (a) the rename to `*_inner` and (b) the `*_via_offsets`
# dispatcher wrapping; trimming Lamed3 to writer-only removes both,
# breaking Mem5 + Tet3-redirect anchors. With this patch, the rename
# happens first as a stand-alone trivial pass-through wrapper:
#
#   let rec search_fast (h ...) ... =
#     search_fast_inner h bound
#   and search_fast_inner (h ...) ... =
#     ... [original perf-shim body] ...
#
# Lamed3 can then independently:
#   - Add `*_via_offsets` reader definitions (or not).
#   - Replace the trivial pass-through with offset-dispatch (or not).
# Mem5 and Tet3 redirects always anchor against `*_inner`; that anchor
# now exists regardless of whether Lamed3's reader half is present.
#
# Sort order: `cottas_ondisk_zzzzz_z_*` (5 z's + `_z` suffix) sorts
# AFTER `cottas_ondisk_zzzzz_ondisk_index.sh` (Vav3, 5 z's + `_o`)
# because `o` < `z` alphabetically, and BEFORE
# `cottas_ondisk_zzzzzz_lamed3_offset_idx.sh` (6 z's) because the
# 5z+`_` prefix is shorter than 6z. Verified by `ls | sort` of
# `cottas_ondisk_zzzz*` patches.
#
# Rule #11(c): trivial dispatch shim. The pass-through carries no
# decision — it's literal forwarding. The rename is structural, no
# semantics added.
#
# Anchor: matches the `let search_fast (h ...) : ... list =` header
# left by `cottas_ondisk_runtime.sh`'s perf-shim
# (`cottas_ondisk_search -> search_fast`). Same for
# `search_fast_limited` (Aleph6) and `estimate_fast`.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  ML="$OUTDIR"
else
  ML="$OUTDIR/RDF_CottasStore.ml"
fi

if [[ ! -f "$ML" ]]; then
  echo "  [rename-inner-pivot] WARN: $ML not found; skipping."
  exit 0
fi

if grep -q '__RENAME_INNER_PIVOT_APPLIED__' "$ML"; then
  echo "  [rename-inner-pivot] already applied; skipping."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys, pathlib

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# Three rename targets: search_fast, search_fast_limited, estimate_fast.
# Each has a perf-shim header left by cottas_ondisk_runtime.sh. We rename
# the header and prepend a `let rec X = X_inner h bound\n  and ` wrapper.

# ---- 1. search_fast ----
old_search_hdr = '''  let search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''
new_search_hdr = '''  (* __RENAME_INNER_PIVOT_APPLIED__ — issue #105 fix.
     `search_fast` is now a trivial pass-through to `search_fast_inner`;
     downstream patches (Mem5, Tet3 redirects, Lamed3 reader half if
     present) anchor against `_inner`. *)
  let rec search_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    search_fast_inner h bound
  and search_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''

if old_search_hdr not in content:
    sys.stderr.write("  [rename-inner-pivot] WARN: search_fast header not found; skipping search_fast rename\n")
else:
    content = content.replace(old_search_hdr, new_search_hdr, 1)

# ---- 2. search_fast_limited ----
old_lim_hdr = '''  let search_fast_limited (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''
new_lim_hdr = '''  let rec search_fast_limited (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list =
    search_fast_limited_inner h bound limit
  and search_fast_limited_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) (limit : pint)
    : Parser_BallyhooCOTTAS.cottas_qp_row list ='''

if old_lim_hdr not in content:
    sys.stderr.write("  [rename-inner-pivot] WARN: search_fast_limited header not found; skipping\n")
else:
    content = content.replace(old_lim_hdr, new_lim_hdr, 1)

# ---- 3. estimate_fast ----
old_est_hdr = '''  let estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint ='''
new_est_hdr = '''  let rec estimate_fast (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint =
    estimate_fast_inner h bound
  and estimate_fast_inner (h : cottas_ondisk_handle) (bound : Parser_BallyhooCOTTAS.cottas_bound_qp) : pint ='''

if old_est_hdr not in content:
    sys.stderr.write("  [rename-inner-pivot] WARN: estimate_fast header not found; skipping\n")
else:
    content = content.replace(old_est_hdr, new_est_hdr, 1)

path.write_text(content)
sys.stderr.write("  [rename-inner-pivot] applied: search_fast / search_fast_limited / estimate_fast renamed to *_inner with pass-through wrappers\n")
PYEOF

echo "  Rename-inner-pivot applied (issue #105)."
