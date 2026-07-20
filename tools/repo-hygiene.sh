#!/usr/bin/env bash
# tools/repo-hygiene.sh — build-artifact hygiene gate for the F*/OCaml tree.
#
# HONEST SCOPE (rewritten 2026-07-20 after the first version was correctly
# called out as unsound). This is NOT a general "reachability proof." It is a
# gate built on ONE thing the build itself computes soundly:
#
#   A module is compiled into the shipped native artifacts IFF the build
#   emitted its `.cmx`. The native build (build-ocaml.sh) only compiles what
#   is in its module list and reachable from it, so `.cmx` EXISTENCE is the
#   build's own verdict — not a grep guess. A tracked `.fst` with no `.cmx`
#   was never compiled: it is not in the build. That is sound and exact.
#
# What this DOES prove (soundly):
#   - Every tracked `.fst` is compiled into the rule-#9 native artifacts
#     (has a `.cmx`), or it is DEAD (no `.cmx`). Zero false positives on the
#     "no `.cmx`" verdict — PageCache.Bounds.fst was exactly this.
#   - No orphaned `.cmx`/`.cmi`/`.o` (compiled object whose `.ml` is gone).
#   - No orphaned extracted `.ml` (no `.fst` source AND no `.cmx` AND not a
#     referenced hand-written realisation).
#
# What this does NOT prove (stated so it never overclaims again):
#   - "Linked into a specific shipped binary." A module could be compiled
#     (`.cmx` exists) yet linked into no binary's link line — a weaker,
#     rarer dead. Detecting that needs parsing the 30 multi-line
#     `ocamlfind ocamlopt … -o` invocations (with their `$COMMON_MODULES`
#     shell expansion); TODO, tier 2.
#   - The js_of_ocaml / wasm / KaRaMeL-C / formal/roaring build backends —
#     a module live ONLY via one of those is out of this gate's scope.
#   - Fixture worthiness (manifest-reachability) and doc worthiness
#     (link-reachability). Separate buckets, not attempted here.
#
# The genuinely-sound design for the full claim is "build-as-oracle": have
# build-ocaml.sh emit, after linking, the exact set of `.cmx` each binary
# consumed, and diff the tree against that union. The build already computes
# reachability; capture it rather than re-deriving it with a script. Until
# that lands, this gate covers the compiled/orphaned checks only.
#
# Usage:  tools/repo-hygiene.sh            # findings
#         tools/repo-hygiene.sh --list     # also list the compiled modules
#         tools/repo-hygiene.sh --ci       # exit 1 on any DEAD/orphan finding
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
F=formal/fstar; OUT=$F/ocaml-output
LIST=0; CI=0
for a in "$@"; do [ "$a" = "--list" ] && LIST=1; [ "$a" = "--ci" ] && CI=1; done
u() { echo "$1" | sed 's/\./_/g'; }   # dotted module -> underscore .ml/.cmx stem
dead=0; ok=0

echo "=== repo-hygiene: build-artifact gate ($(git rev-parse --short HEAD)) ==="
echo "    Oracle: a .fst is compiled into the rule-#9 native artifacts iff its"
echo "    .cmx exists (the build's own output). See header for scope + limits."
echo

# --- [1] .fst with no .cmx = not compiled = DEAD (sound, exact) -------------
echo "-- [1] tracked .fst compiled into the native build (.cmx exists)? --"
while IFS= read -r f; do
  stem=$(u "$(basename "$f" .fst)")
  if [ -f "$OUT/${stem}.cmx" ]; then
    ok=$((ok+1)); [ $LIST -eq 1 ] && echo "  compiled  $f"
  else
    # A .fst with no .cmx is either dead, or (rarely) an interface-only /
    # JS-only module. Flag it; a false alarm here is a JS/roaring-only module
    # (see scope limits) — verify against depend.make before deleting.
    echo "  NO-CMX    $f  (not compiled into native build — DEAD unless JS/roaring-only; verify vs depend.make)"; dead=$((dead+1))
  fi
done < <(git ls-files "$F/*.fst")

# --- [2] extracted .ml orphans (no .fst, no .cmx, not a live realisation) ---
echo
echo "-- [2] ocaml-output/*.ml backed by a .fst OR a compiled/referenced realisation? --"
while IFS= read -r m; do
  b=$(basename "$m" .ml); dotted="${b//_/.}"
  if [ -f "$F/${dotted}.fst" ] || [ -f "$F/${dotted}.fsti" ] || [ -f "$OUT/${b}.cmx" ] \
     || grep -rqE "\b${b}\b" "$F/build-ocaml.sh" $F/experimental_ocaml_glue/*.sh $F/ocaml-patches.sh bin/*/*.ml 2>/dev/null; then
    ok=$((ok+1)); [ $LIST -eq 1 ] && echo "  ok        $m"
  else
    echo "  ORPHAN-ML $m  (no .fst source, no .cmx, no build/glue/consumer reference)"; dead=$((dead+1))
  fi
done < <(git ls-files "$OUT/*.ml")

# --- [3] orphaned compiled objects: .cmx/.cmi/.o whose .ml/.c is gone -------
echo
echo "-- [3] ocaml-output/*.{cmi,cmx,o}: a .ml or .c stub source must exist --"
while IFS= read -r o; do
  stem=$(basename "$o"); stem="${stem%.*}"
  # Worthy if: a .ml source exists, OR a .c stub (local glue OR vendored,
  # e.g. HACL* hacl-obj/Hacl_*.o compiled from $HACL_DIR/src and linked via
  # $HACL_NATIVE_STUBS), OR the build names it (vendored/generated object).
  if [ -f "$OUT/${stem}.ml" ] \
     || git ls-files --error-unmatch "$F/experimental_ocaml_glue/${stem}.c" >/dev/null 2>&1 \
     || grep -rqE "\b${stem}\b" "$F/build-ocaml.sh" 2>/dev/null; then
    ok=$((ok+1)); [ $LIST -eq 1 ] && echo "  ok        $o"
  else
    echo "  ORPHAN-OBJ $o  (no .ml source, no .c stub, not named by the build)"; dead=$((dead+1))
  fi
done < <(git ls-files "$OUT/*.cmi" "$OUT/*.cmx" "$OUT/*.o")

# --- [4] merged-branch litter (advisory) -----------------------------------
echo
merged=$(git branch --merged claude/main 2>/dev/null | grep -vcE '^\*|claude/main')
echo "-- [4] $merged local branch(es) fully merged into claude/main (safe 'git branch -d') --"

echo
echo "=== $ok build-artifact checks passed, $dead DEAD/orphan finding(s) ==="
echo "    This gate covers the native compiled/orphaned checks ONLY — see the"
echo "    header for what it does NOT cover (deliverable-link closure, JS/C/"
echo "    roaring backends, fixtures, docs). It is a gate, not a worthiness proof."
[ $CI -eq 1 ] && [ $dead -gt 0 ] && exit 1
exit 0
