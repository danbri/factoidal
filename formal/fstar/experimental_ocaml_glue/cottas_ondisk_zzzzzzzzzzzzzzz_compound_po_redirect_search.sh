#!/bin/bash
# Compound (p, o) -> F* redirect: search_fast_inner per-rg gate.
# Issue #104, follow-up to estimate-side redirect.
#
# What this patch does:
#
#   The estimate-side redirect (cottas_ondisk_zzzzzzzzzzzzzz_compound_po_redirect_estimate.sh,
#   commit eda1f9c) wires the F* compound-(p,o) bitmap into mem5's
#   estimate_fast_inner candidate-counter. That makes candidates=0/26
#   for queries like Q03 (?o a wktLiteral) — but mem5's estimate is
#   only used by the planner for ORDERING, not for skipping execution.
#   The executor's search_fast_inner then walks all rgs that pass the
#   per-column-only Tet3 gate and pays the full DLBA decode on the
#   surviving rgs (rg=22 + rg=16 in Q03's case) before finding 0
#   matches. That's the remaining 3.7s on Q03's wall clock.
#
#   This patch wires the SAME F* compound check into the search_fast_inner
#   per-rg gate, AND-composed with the existing per-column Tet3 verdict.
#   When both p and o are bound and the compound bitmap says "no pair
#   in this rg", the rg is skipped entirely — no column decode, no
#   filter-loop. Q03 should drop to <100ms.
#
#   Same helper module Compound_po_fstar_redirect (installed by the
#   estimate-side patch) is reused — no duplicate boot hook.
#
#   Shape (c) per fstar-purity-unwind.md: trivial dispatch shim that
#   calls F*-extracted code (rule #11(c)).
#
# Sort order: cottas_ondisk_zzzzzzzzzzzzzzz_* (15 z's) — runs strictly
# AFTER the estimate-side redirect at 14 z's. The estimate patch
# installs the helper module; this patch only wires it in.
#
# Rule #11(c): NO RDF/SPARQL semantic logic in this patch. The shim
# only AND-composes an existing F*-routed verdict.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  ML="$OUTDIR"
else
  ML="$OUTDIR/RDF_CottasStore.ml"
fi

if [[ ! -f "$ML" ]]; then
  echo "  [compound-po-fstar-redirect-search] WARN: $ML not found; skipping."
  exit 0
fi

if grep -q '__COMPOUND_PO_REDIRECT_SEARCH_APPLIED__' "$ML"; then
  echo "  [compound-po-fstar-redirect-search] already applied; skipping."
  exit 0
fi

# Sanity check: the estimate-side patch must have run first (it
# installs the Compound_po_fstar_redirect helper module that this
# patch's call site refers to).
if ! grep -q 'module Compound_po_fstar_redirect' "$ML"; then
  echo "  Warning: compound-po-fstar-redirect-search needs the estimate redirect's helper module;"
  echo "  experimental_ocaml_glue/cottas_ondisk_zzzzzzzzzzzzzz_compound_po_redirect_estimate.sh must run first."
  exit 0
fi

python3 - "$ML" <<'PYEOF'
import sys
import pathlib

path = pathlib.Path(sys.argv[1])
content = path.read_text()

# ----------------------------------------------------------------------
# Anchor: search_fast_inner's per-rg gate. The unique pattern is the
# 3-line "could_o = could_via path 2 ..." line followed by
# "if not (could_p && could_s && could_o) then begin / incr n_skipped /
# if !n_skipped <= 3 || !n_skipped mod 5 = 0 then".
#
# This appears in BOTH search_fast_inner AND search_fast_limited (which
# has its own gate at a different line). To anchor specifically on
# search_fast_inner we include the n_skipped log message text — that
# message says "[tet3-trace] search_fast rg=%d skipped" while
# search_fast_limited says "[tet3-trace] search_fast_limited rg=%d
# skipped". The "search_fast rg=" string (without _limited) is the
# unique discriminator.
# ----------------------------------------------------------------------

old_block = '''      let could_o = could_via path 2 bound.Parser_BallyhooCOTTAS.cbqp_o
        bound_o Cottas_ondisk_lazy.obj_rg_could_contain in
      if not (could_p && could_s && could_o) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] search_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b)\\n%!"
            rg could_p could_s could_o'''

new_block = '''      let could_o = could_via path 2 bound.Parser_BallyhooCOTTAS.cbqp_o
        bound_o Cottas_ondisk_lazy.obj_rg_could_contain in
      (* compound_po_fstar_redirect (search): AND-compose the per-column
         Tet3 verdict with the joint-(p, o) compound bitmap when both
         are bound and the .po.presence companion is present. F*'s
         rg_could_contain_pair does the actual binary search; we just
         wire the AND. Same helper as the estimate-side redirect.
         __COMPOUND_PO_REDIRECT_SEARCH_APPLIED__ *)
      let compound_ok =
        match Compound_po_fstar_redirect.could_contain_pair_via_fstar
                path rg bound.Parser_BallyhooCOTTAS.cbqp_p
                bound.Parser_BallyhooCOTTAS.cbqp_o with
        | FStar_Pervasives_Native.Some b -> b
        | FStar_Pervasives_Native.None -> true in
      if not (could_p && could_s && could_o && compound_ok) then begin
        incr n_skipped;
        if !n_skipped <= 3 || !n_skipped mod 5 = 0 then
          Printf.eprintf "[tet3-trace] search_fast rg=%d skipped (could_p=%b could_s=%b could_o=%b compound_ok=%b)\\n%!"
            rg could_p could_s could_o compound_ok'''

if old_block not in content:
    sys.stderr.write("  [compound-po-fstar-redirect-search] FATAL: search_fast_inner gate anchor not found; aborting\n")
    sys.exit(1)

content = content.replace(old_block, new_block, 1)

path.write_text(content)
sys.stderr.write("  [compound-po-fstar-redirect-search] applied: search_fast_inner per-rg gate AND-composed with F* compound (p, o) bitmap\n")
PYEOF

echo "  Compound (p, o) F* redirect (search) patch applied."
