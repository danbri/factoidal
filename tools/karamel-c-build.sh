#!/bin/bash
# KaRaMeL C-build pilot — F* -> .krml -> .c/.h -> gcc -> end-to-end demo.
#
# Plan doc: docs/designissues/2026-05-07-c-build-and-roaring-plan.md (Track 2)
# Install notes for the krml binary itself:
#   docs/designissues/2026-05-10-krml-install-notes.md
#   (clone FStarLang/karamel master, deps in a dedicated `karamel` opam
#    switch on OCaml 4.14.1, `make minimal`, install
#    _build/default/src/Karamel.exe as /usr/local/bin/krml).
#
# Pilot modules (Group A — full C, linked, demo-tested):
#   RDF.Format, SPARQL.JSON.Escape, SPARQL.HTTP.StaticFiles,
#   SPARQL.HTTP.QueriesIndex
# Group B (SPARQL.Update.Analysis, SPARQL.Query.Analysis) emits .krml
# cleanly but krml's monomorphizer blows the stack / times out on their
# SPARQL11.Algebra dependency graph — run with --group-b to reproduce;
# status tracked in the plan doc's 2.3 table.
# Group C (RDF.Store.Columnar.DeltaLog — the durable-UPDATE delta-log
# byte format) — full C, linked, demo-tested (12/12 checks); runs by
# default alongside Group A. See §"Group C" below for the two
# KaRaMeL-compat fixes this module needed that the Group A pilot never
# hit (u32/u64-scale `nat` arithmetic).
# Group D (RDF.Store.Columnar.DeltaMerge — merge-on-read) hits the
# SAME SPARQL11.Algebra/RDF.Graph.Executable blocker as Group B (it
# opens both) — run with --group-d to reproduce; see that section.
#
# Usage:
#   eval $(opam env --switch=fstar)   # F* on PATH (iron rule #12)
#   tools/karamel-c-build.sh            # Group A + Group C, lower + gcc + demo
#   tools/karamel-c-build.sh --group-b  # also attempt the Analysis bundle (blocked)
#   tools/karamel-c-build.sh --group-d  # also attempt DeltaMerge (blocked)
#
# Environment:
#   KRML_HOME  root of a karamel checkout (include/ + krmllib/dist/...).
#              Default: /root/karamel, else inferred from `which krml`.

set -euo pipefail
cd "$(dirname "$0")/../formal/fstar"

GROUP_B=0
GROUP_D=0
for arg in "$@"; do
  [[ "$arg" == "--group-b" ]] && GROUP_B=1
  [[ "$arg" == "--group-d" ]] && GROUP_D=1
done

# --- toolchain checks -------------------------------------------------------
if ! command -v fstar.exe >/dev/null 2>&1; then
  echo "FATAL: fstar.exe not on PATH. Run: eval \$(opam env --switch=fstar)" >&2
  exit 127
fi
if ! command -v krml >/dev/null 2>&1; then
  echo "FATAL: krml not on PATH. See docs/designissues/2026-05-10-krml-install-notes.md" >&2
  exit 127
fi
KRML_HOME="${KRML_HOME:-/root/karamel}"
if [[ ! -d "$KRML_HOME/include/krml" ]]; then
  echo "FATAL: KRML_HOME=$KRML_HOME has no include/krml — point KRML_HOME at a karamel checkout." >&2
  exit 127
fi

# --- bounded wait on the extraction lock (never wait forever) ---------------
# build-ocaml.sh owns .build-running; concurrent ad-hoc fstar.exe runs are
# unsafe (shared .checked cache). Poll up to 10 min, then abort.
for i in $(seq 1 60); do
  [[ ! -f .build-running ]] && break
  [[ "$i" == 60 ]] && { echo "FATAL: .build-running still present after 10 min — a build-ocaml.sh run is active; retry later." >&2; exit 75; }
  sleep 10
done

# --- step 1: F* -> .krml (full dependency graph, single out.krml) -----------
echo "=== [1/4] fstar.exe --codegen krml (Group A allowlist) ==="
mkdir -p krml-output/groupA
fstar.exe --z3version 4.13.3 --codegen krml \
  --odir krml-output/groupA --cache_checked_modules \
  --extract 'krml:*' \
  RDF.Format.fst SPARQL.JSON.Escape.fst \
  SPARQL.HTTP.StaticFiles.fst SPARQL.HTTP.QueriesIndex.fst \
  > krml-output/_groupA.log 2>&1 || {
    echo "FATAL: F* krml extraction failed — tail of log:" >&2
    tail -20 krml-output/_groupA.log >&2
    exit 1
  }
grep -c "^Verified module" krml-output/_groupA.log | \
  xargs -I{} echo "    {} modules verified; out.krml written"

# --- step 2: krml -> .c/.h ---------------------------------------------------
# -warn-error +2 downgrades "extern without implementation" from fatal to
# warning: the open externs (FStar.String.lowercase, Parser.FastString
# byte primitives, ...) are provided by krmllib + c-output/demo stubs at
# link time. The bundle groups every support module behind the four pilot
# APIs so non-Low* code that the APIs never reach is dropped.
echo "=== [2/4] krml -> c-output/Factoidal_Pilot.{c,h} ==="
krml -skip-compilation -skip-makefiles -tmpdir c-output \
  -warn-error +2 \
  -bundle 'RDF.Format+SPARQL.JSON.Escape+SPARQL.HTTP.StaticFiles+SPARQL.HTTP.QueriesIndex=*[rename=Factoidal_Pilot]' \
  krml-output/groupA/out.krml \
  > c-output/_krml_groupA.log 2>&1 || {
    echo "FATAL: krml lowering failed — tail of log:" >&2
    tail -20 c-output/_krml_groupA.log >&2
    exit 1
  }
ls -la c-output/Factoidal_Pilot.c c-output/Factoidal_Pilot.h

# --- step 3: gcc -------------------------------------------------------------
echo "=== [3/4] gcc compile + link ==="
CFLAGS=(-I "$KRML_HOME/include" -I "$KRML_HOME/krmllib/dist/minimal" -I c-output)
gcc -c "${CFLAGS[@]}" c-output/Factoidal_Pilot.c -o c-output/Factoidal_Pilot.o
gcc -c "${CFLAGS[@]}" c-output/demo/factoidal_pilot_stubs.c -o c-output/demo/factoidal_pilot_stubs.o
gcc -c "${CFLAGS[@]}" c-output/demo/format_demo.c -o c-output/demo/format_demo.o
# krmllib pieces the pilot links against (string/char/int runtime).
for f in prims fstar_string fstar_char fstar_uint32 fstar_int32; do
  gcc -c -I "$KRML_HOME/include" -I "$KRML_HOME/krmllib/dist/minimal" \
      -I "$KRML_HOME/krmllib/dist/generic" \
      "$KRML_HOME/krmllib/dist/generic/$f.c" -o "c-output/demo/$f.o"
done
gcc c-output/demo/format_demo.o c-output/Factoidal_Pilot.o \
    c-output/demo/factoidal_pilot_stubs.o \
    c-output/demo/{prims,fstar_string,fstar_char,fstar_uint32,fstar_int32}.o \
    -o c-output/demo/format_demo
echo "    linked c-output/demo/format_demo"

# --- step 4: run the end-to-end demo ----------------------------------------
echo "=== [4/4] run demo ==="
./c-output/demo/format_demo

# --- optional: Group B (known-blocked, kept for reproduction) ----------------
if [[ "$GROUP_B" == 1 ]]; then
  echo "=== [group-b] SPARQL.{Update,Query}.Analysis (expected to fail in krml) ==="
  mkdir -p krml-output/groupB
  fstar.exe --z3version 4.13.3 --codegen krml \
    --odir krml-output/groupB --cache_checked_modules \
    --extract 'krml:*' \
    SPARQL.Update.Analysis.fst SPARQL.Query.Analysis.fst \
    > krml-output/_groupB.log 2>&1
  GB_RC=0
  timeout 1200 krml -skip-compilation -skip-makefiles -tmpdir c-output/groupB \
    -warn-error +2 \
    -bundle 'SPARQL.Update.Analysis+SPARQL.Query.Analysis=*[rename=Factoidal_Analysis]' \
    krml-output/groupB/out.krml \
    > krml-output/_groupB_krml.log 2>&1 || GB_RC=$?
  echo "    krml exit code: $GB_RC (2 = stack overflow, 124 = 20-min timeout;"
  echo "    both mean the SPARQL11.Algebra graph is too big for krml's"
  echo "    monomorphizer — see plan doc 2.3)"
fi

# --- Group C: RDF.Store.Columnar.DeltaLog (durable-UPDATE delta log) --------
#
# Pure F*, no SPARQL11.Algebra/RDF.Graph.Executable dependency (unlike
# Group B/D) — extracts and lowers cleanly. Two KaRaMeL-compat issues
# the Group A pilot never hit, both fixed with an *isolated, C-build-
# only* fix (no shared krmllib/karamel files touched, nothing else
# rebuilds):
#
#   1. krml's stock `krml/internal/compat.h` types `Prims.nat`/`int`
#      (F*'s unbounded math integers) as `int32_t`. This module's u32
#      magic numbers / length guards use literals up to 2^32, which
#      silently truncate to 0 at that width — turning `n >= 2^32`
#      guards into `n >= 0` (always true) and `write_u64_le`'s
#      `n / 2^32`-style divisions into divide-by-zero traps. Fixed by
#      `c-output/deltalog/compat-override/krml/internal/compat.h`,
#      which widens `krml_checked_int_t` to `__int128` (put ahead of
#      $KRML_HOME/include via -I precedence) plus a matching
#      `prims64.c` recompile of the `Prims_op_*` primitives at that
#      width — every object linked into the Group C demo is compiled
#      fresh against this header; the Group A pilot's own int32-width
#      objects are never touched or reused.
#   2. Even int64_t wasn't wide enough: `delta_batch_ok`'s own
#      `db_seq/db_epoch < 2^64` bound check embeds the LITERAL
#      `18446744073709551616` (2^64) — one past `ULLONG_MAX`, which no
#      standard C integer type (up to 64-bit) can represent at all, so
#      the literal mis-parses regardless of the target width. Fixed
#      IN THE .fst (re-verified, no --lax): rewrote the (semantically
#      identical) bound as `<= 18446744073709551615` (2^64 - 1), which
#      fits `unsigned long long` exactly. See the `u64_max_nat` banner
#      in RDF.Store.Columnar.DeltaLog.fst for the full writeup.
#
# krmllib string/char primitives this module calls that karamel's own
# dist/generic/{fstar_string,fstar_char}.c don't implement
# (list_of_string / string_of_list / index / u32_of_char) are realised
# in c-output/deltalog/demo/deltalog_stubs.c — same trust boundary as
# the Group A pilot's own factoidal_pilot_stubs.c, just a different
# subset of missing functions.
echo "=== [group-c] RDF.Store.Columnar.DeltaLog ==="
mkdir -p krml-output/groupC
fstar.exe --z3version 4.13.3 --codegen krml \
  --odir krml-output/groupC --cache_checked_modules \
  --extract 'krml:*' \
  RDF.Store.Columnar.DeltaLog.fst \
  > krml-output/_groupC.log 2>&1 || {
    echo "FATAL: F* krml extraction (DeltaLog) failed — tail of log:" >&2
    tail -20 krml-output/_groupC.log >&2
    exit 1
  }

DL_DIR=c-output/deltalog
DL_OV="$DL_DIR/compat-override"
mkdir -p "$DL_DIR/internal" "$DL_DIR/demo"
krml -skip-compilation -skip-makefiles -tmpdir krml-output/groupC-c \
  -warn-error +2+9 \
  -bundle 'RDF.Store.Columnar.DeltaLog=*[rename=Factoidal_DeltaLog]' \
  krml-output/groupC/out.krml \
  > krml-output/_groupC_krml.log 2>&1 || {
    echo "FATAL: krml lowering (DeltaLog) failed — tail of log:" >&2
    tail -20 krml-output/_groupC_krml.log >&2
    exit 1
  }
cp krml-output/groupC-c/Factoidal_DeltaLog.c krml-output/groupC-c/Factoidal_DeltaLog.h \
   krml-output/groupC-c/krmlinit.c krml-output/groupC-c/krmlinit.h "$DL_DIR/"
cp krml-output/groupC-c/internal/Factoidal_DeltaLog.h "$DL_DIR/internal/"

DL_CFLAGS=(-I "$DL_OV" -I "$KRML_HOME/include" -I "$KRML_HOME/krmllib/dist/minimal" -I "$DL_DIR")
gcc -c "${DL_CFLAGS[@]}" "$DL_DIR/Factoidal_DeltaLog.c" -o "$DL_DIR/Factoidal_DeltaLog.o"
gcc -c "${DL_CFLAGS[@]}" "$DL_DIR/krmlinit.c" -o "$DL_DIR/krmlinit.o"
gcc -c "${DL_CFLAGS[@]}" "$DL_OV/prims64.c" -o "$DL_DIR/prims64.o"
for f in fstar_char fstar_string fstar_uint32; do
  gcc -c "${DL_CFLAGS[@]}" -I "$KRML_HOME/krmllib/dist/generic" \
    "$KRML_HOME/krmllib/dist/generic/$f.c" -o "$DL_DIR/$f.o"
done
gcc -c "${DL_CFLAGS[@]}" "$DL_DIR/demo/deltalog_stubs.c" -o "$DL_DIR/demo/deltalog_stubs.o"
gcc -c "${DL_CFLAGS[@]}" "$DL_DIR/demo/delta_log_demo.c" -o "$DL_DIR/demo/delta_log_demo.o"
gcc "$DL_DIR/demo/delta_log_demo.o" "$DL_DIR/Factoidal_DeltaLog.o" "$DL_DIR/krmlinit.o" \
    "$DL_DIR/prims64.o" "$DL_DIR/fstar_char.o" "$DL_DIR/fstar_string.o" "$DL_DIR/fstar_uint32.o" \
    "$DL_DIR/demo/deltalog_stubs.o" -o "$DL_DIR/demo/delta_log_demo"
echo "    linked $DL_DIR/demo/delta_log_demo"
echo "=== [group-c] run demo ==="
"./$DL_DIR/demo/delta_log_demo"

# --- optional: Group D (known-blocked, kept for reproduction) ---------------
if [[ "$GROUP_D" == 1 ]]; then
  echo "=== [group-d] RDF.Store.Columnar.DeltaMerge (expected to fail in krml) ==="
  echo "    (opens RDF.Graph.Executable + SPARQL11.Algebra — the same"
  echo "    dependency graph Group B blocks on; reproduced 2026-07-06:"
  echo "    krml ran >10min at >5GB RSS with 'ulimit -s unlimited' before"
  echo "    the timeout below killed it — same root cause as Group B,"
  echo "    NOT the u32/u64-literal issues Group C hit and fixed.)"
  mkdir -p krml-output/groupD
  fstar.exe --z3version 4.13.3 --codegen krml \
    --odir krml-output/groupD --cache_checked_modules \
    --extract 'krml:*' \
    RDF.Store.Columnar.DeltaMerge.fst \
    > krml-output/_groupD.log 2>&1
  GD_RC=0
  ulimit -s unlimited
  timeout 600 krml -skip-compilation -skip-makefiles -tmpdir krml-output/groupD-c \
    -warn-error +2+9 \
    -bundle 'RDF.Store.Columnar.DeltaMerge=*[rename=Factoidal_DeltaMerge]' \
    krml-output/groupD/out.krml \
    > krml-output/_groupD_krml.log 2>&1 || GD_RC=$?
  echo "    krml exit code: $GD_RC (124 = 10-min timeout, 2 = stack overflow;"
  echo "    either means the SPARQL11.Algebra/RDF.Graph.Executable graph is"
  echo "    too big for krml's monomorphizer — see plan doc 2.3 and Group B)"
fi

echo ""
echo "Done."
