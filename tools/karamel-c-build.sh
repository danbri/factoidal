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
#
# Usage:
#   eval $(opam env --switch=fstar)   # F* on PATH (iron rule #12)
#   tools/karamel-c-build.sh          # extract + lower + gcc + run demo
#   tools/karamel-c-build.sh --group-b  # also attempt the Analysis bundle
#
# Environment:
#   KRML_HOME  root of a karamel checkout (include/ + krmllib/dist/...).
#              Default: /root/karamel, else inferred from `which krml`.

set -euo pipefail
cd "$(dirname "$0")/../formal/fstar"

GROUP_B=0
[[ "${1:-}" == "--group-b" ]] && GROUP_B=1

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

echo ""
echo "Done."
