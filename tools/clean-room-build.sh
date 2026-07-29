#!/usr/bin/env bash
# clean-room-build.sh — cold, cache-free reproduction of every advertised
# score from a bare clone (issue #314, review gate 1).
#
# WHY THIS EXISTS
# ---------------
# Every score this project publishes is produced by a tree that has
# accumulated: F* .checked files, committed extracted .ml (iron rule #9),
# committed bin/<platform>/ binaries, and a committed incremental-extract
# manifest. None of the published numbers has ever been shown to survive
# the removal of all four. Until that is demonstrated, "the suites pass"
# carries an unstated dependency on our own build state.
#
# This script removes all four, rebuilds from F* source, and re-runs every
# suite. It is EXPENSIVE (a cold full verify+extract is hours). Run it in
# the background, logged, with a wall-clock cap (anti-pattern #19/#20).
#
# WHAT IS AND IS NOT PURGED
# -------------------------
# Purged (build outputs — must be regenerable from .fst source):
#   formal/fstar/*.fst.checked, *.fsti.checked   F* proof cache
#   formal/fstar/*.verified                      Makefile touch-markers
#   formal/fstar/ocaml-output/*.ml               extracted OCaml
#   formal/fstar/ocaml-output/*.cm[iox]          OCaml compile artifacts
#   formal/fstar/ocaml-output/.extract-state/    incremental-extract manifest
#   bin/<platform>/                              committed binaries
#   formal/fstar/c-output/                       KaRaMeL output
#
# NOT purged (inputs, not outputs):
#   *.fst / *.fsti                               the product
#   third_party/testing/**                       W3C fixtures (test INPUTS)
#   hand-written consumer .ml under bin/<consumer>/ and the
#   ocaml-patches.sh / experimental_ocaml_glue patch scripts (rule #11
#   realisations — source, not generated)
#
# Test fixtures are large git submodules. `--fixtures-from DIR` copies them
# from an existing checkout instead of re-fetching over the network. That
# does NOT weaken the clean-room claim (fixtures are inputs we do not
# generate), and the artifact records which mode was used.
#
# USAGE
#   tools/clean-room-build.sh --workdir /tmp/cleanroom [options]
#
#   --workdir DIR        where to clone (required; must not exist or be empty)
#   --source REPO        git repo/path to clone from (default: this checkout)
#   --ref REF            branch/tag/sha to check out (default: current HEAD sha)
#   --fixtures-from DIR  copy third_party/testing from DIR instead of
#                        `git submodule update --init` (offline-safe)
#   --cap-minutes N      hard wall-clock cap for the whole run (default 480)
#   --skip-suites        build only; do not run the conformance suites
#   --artifact PATH      where to write the dated result artifact
#                        (default: docs/clean-room/<UTC-date>.md in THIS checkout)
#
# EXIT CODES
#   0  cold build completed and suites ran
#   1  a purge/setup precondition failed
#   2  the cold F* verify+extract failed  (= the tree does not rebuild)
#   3  the OCaml compile failed
#   4  suite execution failed to produce a report
#   124 wall-clock cap hit
#
# A nonzero exit here is the point of the exercise, not a script bug: it
# means the published numbers depend on build state that a bare clone
# does not have.

set -uo pipefail

WORKDIR=""
SOURCE_REPO=""
REF=""
FIXTURES_FROM=""
CAP_MINUTES=480
SKIP_SUITES=0
ARTIFACT=""

THIS_CHECKOUT="$(git rev-parse --show-toplevel 2>/dev/null || true)"

die() { echo "clean-room: $*" >&2; exit 1; }

while [ $# -gt 0 ]; do
  case "$1" in
    --workdir)       WORKDIR="${2:-}"; shift 2 ;;
    --source)        SOURCE_REPO="${2:-}"; shift 2 ;;
    --ref)           REF="${2:-}"; shift 2 ;;
    --fixtures-from) FIXTURES_FROM="${2:-}"; shift 2 ;;
    --cap-minutes)   CAP_MINUTES="${2:-}"; shift 2 ;;
    --skip-suites)   SKIP_SUITES=1; shift ;;
    --artifact)      ARTIFACT="${2:-}"; shift 2 ;;
    -h|--help)       sed -n '1,70p' "$0"; exit 0 ;;
    *)               die "unknown argument: $1" ;;
  esac
done

[ -n "$WORKDIR" ] || die "--workdir is required"
[ -n "$THIS_CHECKOUT" ] || die "must be run from inside a git checkout"
[ -n "$SOURCE_REPO" ] || SOURCE_REPO="$THIS_CHECKOUT"
# A BRANCH (or tag) name, not a bare sha: the clone is shallow, and a
# --depth 1 clone can only be pointed at a named ref.
[ -n "$REF" ] || REF="$(git rev-parse --abbrev-ref HEAD)"
[ "$REF" != "HEAD" ] || die "detached HEAD — pass --ref <branch-or-tag>"
[ -n "$ARTIFACT" ] || ARTIFACT="$THIS_CHECKOUT/docs/clean-room/$(date -u +%Y-%m-%d).md"

if [ -e "$WORKDIR" ] && [ -n "$(ls -A "$WORKDIR" 2>/dev/null)" ]; then
  die "--workdir $WORKDIR exists and is not empty; refusing to reuse a dirty tree"
fi

command -v fstar.exe >/dev/null 2>&1 \
  || die "fstar.exe not on PATH — run: eval \$(opam env --switch=fstar)  (iron rule #12)"

CLONE="$WORKDIR/factoidal"
RUN_START=$(date +%s)
mkdir -p "$WORKDIR" || die "cannot create $WORKDIR"

# ---------------------------------------------------------------------------
# Toolchain provenance. Recorded before anything is built, so the artifact
# says exactly what produced the numbers.
# ---------------------------------------------------------------------------
FSTAR_VERSION="$(fstar.exe --version 2>&1 | tr '\n' ' ' | sed 's/  */ /g')"
Z3_VERSION="$(z3 --version 2>&1 | head -1)"
OCAML_VERSION="$(ocamlfind ocamlopt -version 2>/dev/null || ocamlopt -version 2>/dev/null || echo unknown)"
UNAME="$(uname -srm)"
NPROC="$(nproc 2>/dev/null || echo unknown)"

echo "clean-room: F*      $FSTAR_VERSION"
echo "clean-room: z3      $Z3_VERSION"
echo "clean-room: ocaml   $OCAML_VERSION"
echo "clean-room: host    $UNAME ($NPROC cores)"
echo "clean-room: source  $SOURCE_REPO @ $REF"
echo "clean-room: workdir $WORKDIR"
echo "clean-room: cap     ${CAP_MINUTES}m"

# ---------------------------------------------------------------------------
# 1. Bare clone of exactly the commit under test.
#
# Shallow (--depth 1) over a file:// URL, deliberately. A full local clone
# would either hardlink the source repo's object store (shared state — the
# thing this script exists to eliminate) or, with --no-local, re-pack every
# byte of history: this repository carries ~5 GB of it, largely committed
# binaries under iron rule #9, which is hours of work and gigabytes of disk
# that tell us nothing about reproducibility.
#
# A shallow clone shares no object storage with the source and materialises
# the tree purely from git, which is the property that matters here: nothing
# in the built tree can have come from the source checkout's build state.
# History depth is irrelevant to whether the corpus rebuilds from source.
# ---------------------------------------------------------------------------
echo "clean-room: [1/6] cloning (shallow, from git only)..."
case "$SOURCE_REPO" in
  /*) CLONE_URL="file://$SOURCE_REPO" ;;
  *)  CLONE_URL="$SOURCE_REPO" ;;
esac
git clone --depth 1 --no-hardlinks --branch "$REF" "$CLONE_URL" "$CLONE" 2>&1 | tail -3
[ -d "$CLONE/.git" ] || die "clone of branch '$REF' from $CLONE_URL failed"
CLONE_SHA="$(git -C "$CLONE" rev-parse HEAD)"
echo "clean-room: cloned $REF at $CLONE_SHA"

# ---------------------------------------------------------------------------
# 2. PURGE every generated artifact. This is the whole point: if any of
#    these is load-bearing for a published score, the rebuild below fails.
# ---------------------------------------------------------------------------
echo "clean-room: [2/6] purging generated artifacts..."
purge_count() { find "$@" 2>/dev/null | wc -l | tr -d ' '; }

N_CHECKED=$(purge_count "$CLONE/formal/fstar" -maxdepth 1 -name '*.checked')
N_ML=$(purge_count "$CLONE/formal/fstar/ocaml-output" -maxdepth 1 -name '*.ml')
N_BIN=$(purge_count "$CLONE/bin" -mindepth 2 -type f ! -name '*.md' ! -name '.gitkeep')

find "$CLONE/formal/fstar" -maxdepth 1 \( -name '*.checked' -o -name '*.verified' \) -delete 2>/dev/null
find "$CLONE/formal/fstar" -maxdepth 2 -name '*.checked' -delete 2>/dev/null
rm -rf "$CLONE/formal/fstar/ocaml-output/.extract-state"
rm -rf "$CLONE/formal/fstar/c-output"
# Extracted OCaml only.
#
# NOT every .ml in ocaml-output/ is generated. A handful are hand-written
# rule-#11 realisations that live there permanently and are tracked in git —
# fstar_pure_hashes.ml (vendored pure-OCaml MD5/SHA-1/SHA-2 realising the
# hash_* assume vals), fstar_hacl_crypto.ml, service_wrap_hook.ml,
# service_wrap_http.ml. Deleting those does not test reproducibility, it just
# breaks the build with a missing source file, which is exactly what the first
# run of this script did: `Error: I/O error: fstar_pure_hashes.ml: No such
# file or directory`.
#
# The distinction is derivable rather than hardcoded: a generated .ml is named
# after an F* module, so Foo_Bar.ml is generated iff Foo.Bar.fst exists. That
# stays correct as modules and glue files come and go.
python3 - "$CLONE" <<'PYEOF'
import os, sys, glob
clone = sys.argv[1]
fstdir = os.path.join(clone, 'formal/fstar')
outdir = os.path.join(fstdir, 'ocaml-output')
modules = {os.path.basename(p)[:-4].replace('.', '_')
           for p in glob.glob(os.path.join(fstdir, '*.fst'))}
removed = kept = 0
for p in glob.glob(os.path.join(outdir, '*.ml')):
    if os.path.basename(p)[:-3] in modules:
        os.remove(p); removed += 1
    else:
        kept += 1
print(f"clean-room: removed {removed} F*-generated .ml; kept {kept} hand-written (rule #11 realisations)")
PYEOF
find "$CLONE/formal/fstar/ocaml-output" -maxdepth 1 \
     \( -name '*.cmi' -o -name '*.cmx' -o -name '*.cmo' \
        -o -name '*.o' -o -name '*.a' -o -name '*.cmxa' -o -name '*.bc.js' \) \
     -delete 2>/dev/null
# Committed binaries (iron rule #9) — the thing a cold build must reproduce.
find "$CLONE/bin" -mindepth 2 -type f ! -name '*.md' ! -name '.gitkeep' -delete 2>/dev/null
# Dangling symlinks left behind in ocaml-output now that bin/ is empty.
find "$CLONE/formal/fstar/ocaml-output" -maxdepth 1 -xtype l -delete 2>/dev/null

echo "clean-room: purged ${N_CHECKED} .checked, ${N_ML} extracted .ml, ${N_BIN} binaries, and the extract manifest"

# Assert the purge actually happened — a silent no-op here would make the
# whole run a lie. Checks for GENERATED leftovers specifically, so the
# hand-written realisations deliberately kept above do not trip it.
REMAIN_CHECKED=$(purge_count "$CLONE/formal/fstar" -maxdepth 1 -name '*.checked')
REMAIN_ML=$(python3 - "$CLONE" <<'PYEOF'
import os, sys, glob
clone = sys.argv[1]
fstdir = os.path.join(clone, 'formal/fstar')
modules = {os.path.basename(p)[:-4].replace('.', '_')
           for p in glob.glob(os.path.join(fstdir, '*.fst'))}
print(sum(1 for p in glob.glob(os.path.join(fstdir, 'ocaml-output/*.ml'))
          if os.path.basename(p)[:-3] in modules))
PYEOF
)
REMAIN=$(( REMAIN_CHECKED + REMAIN_ML ))
[ "$REMAIN" -eq 0 ] || die "purge left $REMAIN generated files behind ($REMAIN_CHECKED .checked, $REMAIN_ML extracted .ml); aborting rather than reporting a warm build as cold"
[ -f "$CLONE/formal/fstar/ocaml-output/.extract-state/manifest.tsv" ] \
  && die "extract manifest survived the purge"

# ---------------------------------------------------------------------------
# 3. Test fixtures. INPUTS, not outputs — restored, not rebuilt.
# ---------------------------------------------------------------------------
echo "clean-room: [3/6] restoring test fixtures..."
FIXTURE_MODE="submodule-init"
if [ -n "$FIXTURES_FROM" ]; then
  FIXTURE_MODE="copied from $FIXTURES_FROM"
  [ -d "$FIXTURES_FROM/third_party/testing" ] || die "--fixtures-from has no third_party/testing"
  mkdir -p "$CLONE/third_party"
  cp -a "$FIXTURES_FROM/third_party/testing" "$CLONE/third_party/" || die "fixture copy failed"
fi
FIXTURE_RC=0
( cd "$CLONE" && ./tools/ensure-test-env.sh ) || FIXTURE_RC=$?
if [ "$FIXTURE_RC" -ne 0 ]; then
  die "ensure-test-env.sh exited $FIXTURE_RC — suite scores from this tree would be lies (hazard #15)"
fi

# ---------------------------------------------------------------------------
# 4. Cold F* verify + extract. --force-full is belt-and-braces: the manifest
#    is already gone, but if a future change re-commits it, this still
#    guarantees every module goes through fstar.exe.
# ---------------------------------------------------------------------------
echo "clean-room: [4/6] cold F* verify + extract (this is the multi-hour step)..."
CAP_SECONDS=$(( CAP_MINUTES * 60 ))
T0=$(date +%s)
EXTRACT_RC=0
( cd "$CLONE/formal/fstar" && timeout "${CAP_SECONDS}s" ./build-ocaml.sh extract --force-full ) \
  || EXTRACT_RC=$?
T_EXTRACT=$(( $(date +%s) - T0 ))
echo "clean-room: extract rc=$EXTRACT_RC in ${T_EXTRACT}s"
if [ "$EXTRACT_RC" -ne 0 ]; then
  [ "$EXTRACT_RC" -eq 124 ] && die "wall-clock cap of ${CAP_MINUTES}m hit during extract"
  echo "clean-room: COLD EXTRACT FAILED — the tree does not rebuild from source" >&2
  exit 2
fi

# ---------------------------------------------------------------------------
# 5. Compile.
# ---------------------------------------------------------------------------
echo "clean-room: [5/6] compiling..."
T0=$(date +%s)
COMPILE_RC=0
ELAPSED=$(( $(date +%s) - RUN_START ))
REMAIN_SECONDS=$(( CAP_SECONDS - ELAPSED ))
[ "$REMAIN_SECONDS" -gt 60 ] || die "wall-clock cap exhausted before compile"
( cd "$CLONE/formal/fstar" && timeout "${REMAIN_SECONDS}s" ./build-ocaml.sh compile ) || COMPILE_RC=$?
T_COMPILE=$(( $(date +%s) - T0 ))
echo "clean-room: compile rc=$COMPILE_RC in ${T_COMPILE}s"
[ "$COMPILE_RC" -eq 0 ] || { echo "clean-room: COMPILE FAILED" >&2; exit 3; }

# ---------------------------------------------------------------------------
# 6. Every advertised suite. generate-report.sh --run is the single entry
#    point that re-runs all conformance suites and regenerates latest.json.
# ---------------------------------------------------------------------------
T_SUITES=0
SUITES_RC=0
if [ "$SKIP_SUITES" -eq 1 ]; then
  echo "clean-room: [6/6] --skip-suites given; not running conformance suites"
else
  echo "clean-room: [6/6] running every advertised suite..."
  T0=$(date +%s)
  ELAPSED=$(( $(date +%s) - RUN_START ))
  REMAIN_SECONDS=$(( CAP_SECONDS - ELAPSED ))
  [ "$REMAIN_SECONDS" -gt 60 ] || die "wall-clock cap exhausted before suites"
  ( cd "$CLONE/formal/fstar" && timeout "${REMAIN_SECONDS}s" ./generate-report.sh --run ) || SUITES_RC=$?
  T_SUITES=$(( $(date +%s) - T0 ))
  echo "clean-room: suites rc=$SUITES_RC in ${T_SUITES}s"
fi

T_TOTAL=$(( $(date +%s) - RUN_START ))

# ---------------------------------------------------------------------------
# Artifact. Scores + toolchain versions + timings, dated, committable.
# ---------------------------------------------------------------------------
mkdir -p "$(dirname "$ARTIFACT")"
COLD_JSON="$CLONE/docs/test-results/latest.json"
{
  echo "# Clean-room reproducibility run — $(date -u +%Y-%m-%d\ %H:%M) UTC"
  echo
  echo "Issue [#314](https://github.com/danbri/factoidal/issues/314), review gate 1."
  echo "Produced by \`tools/clean-room-build.sh\`. Every generated artifact was"
  echo "deleted before this build: F* \`.checked\` files, extracted \`.ml\`,"
  echo "committed \`bin/<platform>/\` binaries, and the incremental-extract manifest."
  echo
  echo "## Provenance"
  echo
  echo "| Field | Value |"
  echo "|---|---|"
  echo "| Commit | \`$CLONE_SHA\` |"
  echo "| Source | \`$SOURCE_REPO\` |"
  echo "| F* | $FSTAR_VERSION |"
  echo "| z3 | $Z3_VERSION |"
  echo "| OCaml | $OCAML_VERSION |"
  echo "| Host | $UNAME, $NPROC cores |"
  echo "| Test fixtures | $FIXTURE_MODE |"
  echo
  echo "## Purge (what was deleted before building)"
  echo
  echo "| Artifact | Count removed |"
  echo "|---|---|"
  echo "| F* \`.checked\` files | $N_CHECKED |"
  echo "| Extracted \`.ml\` | $N_ML |"
  echo "| Committed binaries | $N_BIN |"
  echo "| Extract manifest | 1 (\`.extract-state/\`) |"
  echo
  echo "## Timings"
  echo
  echo "| Phase | Wall-clock | Exit |"
  echo "|---|---|---|"
  echo "| Cold F* verify + extract | $((T_EXTRACT/60))m $((T_EXTRACT%60))s | $EXTRACT_RC |"
  echo "| OCaml compile | $((T_COMPILE/60))m $((T_COMPILE%60))s | $COMPILE_RC |"
  echo "| All conformance suites | $((T_SUITES/60))m $((T_SUITES%60))s | $SUITES_RC |"
  echo "| **Total** | **$((T_TOTAL/60))m $((T_TOTAL%60))s** | |"
  echo
  echo "## Scores from the cold tree"
  echo
  if [ -f "$COLD_JSON" ]; then
    echo '```json'
    cat "$COLD_JSON"
    echo '```'
  else
    echo "No \`docs/test-results/latest.json\` was produced (suites rc=$SUITES_RC)."
  fi
} > "$ARTIFACT"

echo "clean-room: artifact written to $ARTIFACT"
echo "clean-room: total ${T_TOTAL}s (extract ${T_EXTRACT}s, compile ${T_COMPILE}s, suites ${T_SUITES}s)"
[ "$SUITES_RC" -eq 0 ] || exit 4
exit 0
