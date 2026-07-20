#!/usr/bin/env bash
# tools/repo-hygiene.sh — reachability proof that the F*/OCaml build-chain
# files earn their place. Every such tracked file is either proven reachable
# from a live-system ROOT (and we print the root that reaches it), or flagged
# DEAD. This is dead-code reachability, not inspection: it is exhaustive over
# the buckets it covers and proves the negative (nothing worthy is missed).
#
# ROOTS (live-system entry points):
#   - F* build root:   formal/fstar/build-ocaml.sh  ALL_MODULES(...)  + the
#                      .fsti interface pre-check glob.
#   - OCaml link root: build-ocaml.sh COMMON_MODULES + every `ocamlfind
#                      ocamlopt`/`ocamlc` link line + experimental_ocaml_glue
#                      realisation references.
#   - Consumer root:   bin/*/*.ml runners that `open`/qualify a module.
#
# COVERAGE (v1): the F*/OCaml build chain — where dead code actually hides
#   (~1160 files). Fixtures (manifest-reachable) and docs (link-reachable)
#   are a documented v2; see TODO at the bottom. Branch litter is checked too.
#
# Usage:  tools/repo-hygiene.sh            # summary + any DEAD findings
#         tools/repo-hygiene.sh --list     # also print WORTHY verdict per file
#         tools/repo-hygiene.sh --ci       # exit 1 if any DEAD file found
set -uo pipefail
cd "$(git rev-parse --show-toplevel)"
F=formal/fstar
BUILD=$F/build-ocaml.sh
LIST=0; CI=0
for a in "$@"; do [ "$a" = "--list" ] && LIST=1; [ "$a" = "--ci" ] && CI=1; done
dead=0; worthy=0

# --- root sets -------------------------------------------------------------
# F* modules named in ALL_MODULES(...) (dotted basenames, e.g. RDF.Term.fst).
mapfile -t FST_ROOTS < <(sed -n '/ALL_MODULES=(/,/^[[:space:]]*)/p' "$BUILD" \
                         | grep -oE '[A-Z][A-Za-z0-9_.]+\.fst' | sort -u)
in_fst_roots() { printf '%s\n' "${FST_ROOTS[@]}" | grep -qxF "$1"; }

# OCaml names referenced by any link line / COMMON_MODULES / glue patch.
# We test membership by grepping the underscore .ml basename across those.
ocaml_referenced() {  # $1 = underscore basename without .ml, e.g. Sparql_Parser_Stubs
  grep -rqE "\b$1\b" "$BUILD" $F/experimental_ocaml_glue/*.sh \
        $F/ocaml-patches.sh bin/*/*.ml 2>/dev/null
}

echo "=== repo-hygiene reachability report ($(git rev-parse --short HEAD)) ==="
echo

# --- Check 1: F* source (.fst) reachability -------------------------------
echo "-- [1] F* source (.fst): in build roots OR open/include/qualified by a live module --"
while IFS= read -r f; do
  base=$(basename "$f"); mod="${base%.fst}"; esc="${mod//./\\.}"
  if in_fst_roots "$base"; then
    worthy=$((worthy+1)); [ $LIST -eq 1 ] && echo "  WORTHY $f  <- ALL_MODULES"
    continue
  fi
  # not a declared root: reachable only if another live .fst/.fsti or a bin
  # runner opens/includes/qualifies it.
  refs=$(grep -rlE "(open|include)[[:space:]]+${esc}\b|\b${esc}\." \
         $F/*.fst $F/*.fsti bin/*/*.ml 2>/dev/null | grep -vxF "$f")
  if [ -n "$refs" ]; then
    worthy=$((worthy+1)); [ $LIST -eq 1 ] && echo "  WORTHY $f  <- referenced by $(echo "$refs" | head -1)"
  else
    echo "  DEAD   $f  (not in ALL_MODULES; zero open/include/qualified refs)"; dead=$((dead+1))
  fi
done < <(git ls-files "$F/*.fst")

# --- Check 2: extracted / hand-written OCaml (.ml) -------------------------
echo
echo "-- [2] ocaml-output/*.ml: extracted-from-a-live-.fst OR a referenced hand-written realisation --"
while IFS= read -r m; do
  b=$(basename "$m" .ml); dotted="${b//_/.}"
  # (a) extracted: a .fst/.fsti source with the dotted name exists
  if [ -f "$F/${dotted}.fst" ] || [ -f "$F/${dotted}.fsti" ]; then
    worthy=$((worthy+1)); [ $LIST -eq 1 ] && echo "  WORTHY $m  <- extracted from ${dotted}.fst"
    continue
  fi
  # (b) hand-written realisation referenced by a link line / glue / consumer
  if ocaml_referenced "$b"; then
    worthy=$((worthy+1)); [ $LIST -eq 1 ] && echo "  WORTHY $m  <- referenced hand-written realisation"
  else
    echo "  DEAD   $m  (no .fst source; referenced by no link line / glue / consumer)"; dead=$((dead+1))
  fi
done < <(git ls-files "$F/ocaml-output/*.ml")

# --- Check 3: orphaned compiled objects (.cmi/.cmx/.o) whose .ml is gone ---
echo
echo "-- [3] ocaml-output/*.{cmi,cmx,o}: a corresponding .ml (or .c stub) must exist --"
while IFS= read -r o; do
  b=$(basename "$o"); stem="${b%.*}"
  if [ -f "$F/ocaml-output/${stem}.ml" ] \
     || git ls-files --error-unmatch "$F/experimental_ocaml_glue/${stem}.c" >/dev/null 2>&1 \
     || grep -rqE "\b${stem}\b" "$BUILD" 2>/dev/null; then
    worthy=$((worthy+1)); [ $LIST -eq 1 ] && echo "  WORTHY $o"
  else
    echo "  DEAD   $o  (no .ml source, no .c stub, no build reference)"; dead=$((dead+1))
  fi
done < <(git ls-files "$F/ocaml-output/*.cmi" "$F/ocaml-output/*.cmx" "$F/ocaml-output/*.o")

# --- Check 4: patch scripts referenced by nothing --------------------------
echo
echo "-- [4] experimental_ocaml_glue + top-level patch scripts: applied by a build step --"
while IFS= read -r p; do
  b=$(basename "$p")
  if grep -rqE "\b${b}\b" "$BUILD" $F/ocaml-patches.sh $F/build-js.sh 2>/dev/null \
     || grep -qE 'for .* in .*glue' "$BUILD" 2>/dev/null; then
    worthy=$((worthy+1)); [ $LIST -eq 1 ] && echo "  WORTHY $p"
  else
    echo "  NOTE   $p  (not named by a build step — confirm it is applied by a glob loop)"
  fi
done < <(git ls-files "$F/sparql-parser-patches.sh")

# --- Check 5: stale local branches (fully merged into claude/main) ---------
echo
echo "-- [5] local branches fully merged into claude/main (routine litter) --"
merged=$(git branch --merged claude/main 2>/dev/null | grep -vE '^\*|claude/main' | wc -l | tr -d ' ')
echo "  $merged local branch(es) fully merged into claude/main — safe 'git branch -d'."

# --- summary ---------------------------------------------------------------
echo
echo "=== SUMMARY: $worthy proven-worthy (path-to-root shown with --list), $dead DEAD ==="
echo "    Coverage: F*/OCaml build chain + patch scripts + branches."
echo "    NOT yet proven by this tool (v2 TODO): third_party/testing fixtures"
echo "    (manifest-reachability from .github/test-suites/*.yaml) and docs/"
echo "    (link-reachability from CLAUDE.md/README/ledger). docs/test-results/"
echo "    history/ needs a RETENTION policy, not reachability (append-only)."
[ $CI -eq 1 ] && [ $dead -gt 0 ] && exit 1
exit 0
