#!/usr/bin/env bash
#
# build-wasm.sh — compile the Lean 4 library to a single WebAssembly
# module that runs in the browser, Node and Deno.
#
#   formal/lean4/Wasm/build-wasm.sh [work-dir]
#
# Outputs (committed, per the repo's commit-binaries rule):
#   docs/web/hub/assets/l4/l4factoidal.wasm   the module
#   docs/web/hub/assets/l4/l4factoidal.mjs    Emscripten's glue
#   docs/web/hub/assets/l4/l4factoidal.js     our ES-module loader
#
# The glue's basename decides the sidecar name it looks for: emcc's
# output `l4factoidal.mjs` resolves `l4factoidal.wasm` next to itself.
# Renaming one without the other breaks loading in every runtime, and
# passing `wasmBinary` does NOT override it in Emscripten 6.
#
# WHY THIS SCRIPT EXISTS AT ALL
# Lean compiles to C, but linking needs Lean's runtime AND the compiled
# core library (`Init`) as wasm32 objects, and the elan toolchain ships
# neither — only native ones. The two pieces are rebuilt here:
#
#   1. the core library's C, regenerated from the toolchain's OWN
#      sources with the toolchain's OWN native `lean` binary. This is
#      the cheap step people expect to be expensive: every import is
#      already an .olean, so elaboration is ~1s per module and the whole
#      of `Init` takes a few minutes at -P8. We do NOT build the Lean
#      compiler for wasm (the route lean4's CMake takes), because
#      nothing here needs to ELABORATE Lean inside the browser — only to
#      RUN already-compiled Lean.
#
#   2. Lean's C++ runtime (src/runtime/*.cpp at the pinned tag) plus
#      mimalloc, compiled with Emscripten. GMP-free; mimalloc is NOT
#      optional (see the config.h comment in step 2).
#
# See skills/lean4-wasm-export/SKILL.md for the routes that were
# evaluated and rejected, and for the traps (they are not obvious).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
LEAN_DIR="$REPO_ROOT/formal/lean4"
ASSETS="$REPO_ROOT/docs/web/hub/assets/l4"
WORK="${1:-${L4_WASM_WORK:-/tmp/l4wasm-build}}"
MIMALLOC_TAG="v2.2.7"   # the version lean4 v4.33.x pins

LEAN_TAG="$(tr -d ' \n' < "$LEAN_DIR/lean-toolchain" | sed 's|.*:||')"   # e.g. v4.33.1
# `lean --print-prefix` is the authoritative answer and follows elan's
# shim; deriving the directory name from the tag is NOT reliable (elan
# spells it `leanprover--lean4---v4.33.1`, tag and all, and `command -v
# lean` points at the shim in ~/.elan/bin, whose parent is not the
# toolchain). Getting this wrong silently resolves to ~/.elan and the
# build fails 40 lines later complaining about missing core sources.
TOOLCHAIN="$(cd "$LEAN_DIR" && lean --print-prefix)"

say() { printf '\n=== %s\n' "$*"; }

say "configuration"
echo "  lean tag     : $LEAN_TAG"
echo "  toolchain    : $TOOLCHAIN"
echo "  work dir     : $WORK"
echo "  assets out   : $ASSETS"
command -v emcc >/dev/null || { echo "emcc not on PATH (brew install emscripten)"; exit 1; }
command -v lean >/dev/null || { echo "lean not on PATH (export PATH=\$HOME/.elan/bin:\$PATH)"; exit 1; }
emcc --version | head -1

LEAN_SRC="$TOOLCHAIN/src/lean"
LEAN_LIB="$TOOLCHAIN/lib/lean"
[ -d "$LEAN_SRC/Init" ] || { echo "toolchain does not ship core sources at $LEAN_SRC"; exit 1; }

mkdir -p "$WORK" "$ASSETS"
CORE_C="$WORK/core-c"; CORE_OBJ="$WORK/core-obj"
RT_SRC="$WORK/lean4-src/src"; RT_OBJ="$WORK/rt-obj"
LIB_OBJ="$WORK/lib-obj"; INC="$WORK/wasm-include"
mkdir -p "$CORE_C" "$CORE_OBJ" "$RT_OBJ" "$LIB_OBJ" "$INC/lean"

# ---------------------------------------------------------------------
say "step 0 — build the Lean library natively (also emits its C)"
( cd "$LEAN_DIR" && lake build l4wasm )

# ---------------------------------------------------------------------
say "step 1 — fetch Lean's C++ runtime sources at $LEAN_TAG"
# Sparse + blobless: only src/runtime and src/include are ever downloaded
# (~4 MB), not the multi-hundred-MB full tree. src/util is needed too:
# runtime/interrupt.cpp includes "util/io.h".
if [ ! -d "$RT_SRC/runtime" ]; then
  rm -rf "$WORK/lean4-src"
  git clone --filter=blob:none --sparse --depth 1 --branch "$LEAN_TAG" \
      https://github.com/leanprover/lean4 "$WORK/lean4-src"
  ( cd "$WORK/lean4-src" && git sparse-checkout set src/runtime src/include src/util )
fi

# ---------------------------------------------------------------------
say "step 2 — wasm build configuration headers"
# CMake normally generates these.
#
# LEAN_USE_GMP is deliberately absent: the runtime falls back to its own
# bignums in runtime/mpn.cpp, which is what keeps the artifact GMP-free
# (one of the selection criteria).
#
# LEAN_MIMALLOC, by contrast, is REQUIRED, and finding that out cost a
# day. Lean's non-mimalloc allocator path is inconsistent upstream:
# `lean_alloc_small_object` returns `malloc(sizeof(size_t) + sz) + 1`
# (a pointer 8 bytes INTO the block, with the size stashed in front),
# and `lean_free_small_object` correctly backs up before freeing — but
# `lean_free_object`, which handles arrays, strings and closures, calls
# `lean_dealloc(o, ...)` -> `free_sized(o, ...)` on the UNADJUSTED
# pointer. Under mimalloc both paths agree, so the bug is invisible in
# every shipped Lean build. Without it the wasm module aborted inside
# `free_sized` on the first path that frees a string — measured
# 2026-08-22 via an -sASSERTIONS=2 build, stack
# `bgpQuery -> lean_dec_ref_cold -> lean_del_core_other -> free_sized`.
cat > "$INC/lean/config.h" <<'EOF'
#pragma once
#include <lean/version.h>
#define LEAN_MIMALLOC
#define LEAN_IS_STAGE0 0
EOF
cp "$TOOLCHAIN/include/lean/version.h" "$INC/lean/version.h"

# mimalloc, at the version lean4 pins (see src/CMakeLists.txt's
# LEAN_MI_SECURE comment). lean.h includes it as <lean/mimalloc.h>.
if [ ! -d "$WORK/mimalloc" ]; then
  git clone --depth 1 --branch "$MIMALLOC_TAG" \
      https://github.com/microsoft/mimalloc "$WORK/mimalloc"
fi
cp "$WORK/mimalloc/include/mimalloc.h" "$INC/lean/mimalloc.h"
printf '#pragma once\n#define LEAN_GITHASH "%s"\n' "$(lean --githash)" > "$INC/githash.h"

# ---------------------------------------------------------------------
say "step 3 — regenerate the core library's C with the native lean"
export LEAN_PATH="$LEAN_LIB"
gen_one() {
  local f="$1" out
  out="$CORE_C/$(echo "${f#$LEAN_SRC/}" | sed 's|/|_|g; s|\.lean$|.c|')"
  [ -s "$out" ] && return 0
  lean -R "$LEAN_SRC" -c "$out" "$f" >/dev/null 2>&1 || { echo "GEN-FAIL $f" >&2; rm -f "$out"; }
}
export -f gen_one
export CORE_C LEAN_SRC
{ echo "$LEAN_SRC/Init.lean"; find "$LEAN_SRC/Init" -name '*.lean'; } \
  | xargs -P 8 -I{} bash -c 'gen_one "$@"' _ {}
echo "  core C files: $(ls "$CORE_C"/*.c | wc -l | tr -d ' ')"

# ---------------------------------------------------------------------
# Flags shared by every compile.
#  -fwasm-exceptions : Lean's C++ runtime throws. Native wasm exception
#                      handling (Chrome 95+, Firefox 131+, Safari 18.4+,
#                      Node 18+) — the same choice lean4's own CMake makes.
#  NO -pthread       : a pthread build needs SharedArrayBuffer, which
#                      needs COOP/COEP response headers that GitHub Pages
#                      does not send. Nothing here spawns a Lean task
#                      thread (we call lean_initialize_runtime_module,
#                      not the full lean_initialize).
#  -O3 -DNDEBUG      : the flags Lake passes leanc for native builds.
#                      Match them so the wasm build is the configuration
#                      Lean actually supports. NOTE: NDEBUG changes how
#                      the allocator bug described in step 2 PRESENTS
#                      (`LEAN ASSERTION VIOLATION ... lean_ctor_num_objs`
#                      with assertions on, `memory access out of bounds`
#                      with them off) but does NOT fix it — mimalloc
#                      does. Do not mistake the quieter symptom for a
#                      cure; that misdiagnosis cost a rebuild cycle here.
CFLAGS="-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I $INC -I $RT_SRC/include
        -Wno-unused-parameter -Wno-unused-command-line-argument -Wno-parentheses-equality"

say "step 4 — compile the core library's C to wasm objects"
cc_one() {
  local f="$1" b
  b="$(basename "${1%.c}")"
  [ -s "$CORE_OBJ/$b.o" ] && return 0
  emcc $CFLAGS -c "$f" -o "$CORE_OBJ/$b.o" 2>/dev/null || { echo "CC-FAIL $b" >&2; rm -f "$CORE_OBJ/$b.o"; }
}
export -f cc_one
export CORE_OBJ CFLAGS
ls "$CORE_C"/*.c | xargs -P 8 -I{} bash -c 'cc_one "$@"' _ {}
echo "  core objects: $(ls "$CORE_OBJ"/*.o | wc -l | tr -d ' ')"

# ---------------------------------------------------------------------
say "step 5 — compile Lean's C++ runtime to wasm objects"
# libuv.cpp, uv/* and openssl.cpp are omitted: neither library is built
# for wasm32 and no exported entry point reaches Lean's IO layer. That
# leaves exactly one undefined symbol, stubbed in l4_stubs.c — see the
# comment there; the count is the evidence the ABI really is pure.
RT_SRCS="debug thread mpz utf8 object apply exception interrupt memory stackinfo
         compact init_module io hash byteslice platform alloc allocprof sharecommon
         stack_overflow process object_ref mpn mutex"
# c++20: runtime/object.cpp uses std::memory_order::relaxed and std::bit_cast.
# uv.h is needed for DECLARATIONS only (io.cpp includes it).
UVINC=""
for d in /opt/homebrew/include /usr/local/include /usr/include; do
  [ -f "$d/uv.h" ] && { UVINC="-I $d"; break; }
done
[ -n "$UVINC" ] || { echo "uv.h not found (brew install libuv) — needed for declarations only"; exit 1; }
for s in $RT_SRCS; do
  [ -s "$RT_OBJ/$s.o" ] && continue
  em++ -std=c++20 $CFLAGS -I "$RT_SRC" $UVINC -c "$RT_SRC/runtime/$s.cpp" -o "$RT_OBJ/$s.o"
done
if [ ! -s "$RT_OBJ/mimalloc_static.o" ]; then
  emcc -O3 -DNDEBUG -DMI_SECURE=0 -Wno-unused-function \
       -I "$WORK/mimalloc/include" -c "$WORK/mimalloc/src/static.c" \
       -o "$RT_OBJ/mimalloc_static.o"
fi
echo "  runtime objects: $(ls "$RT_OBJ"/*.o | wc -l | tr -d ' ') (incl. mimalloc)"

# ---------------------------------------------------------------------
say "step 6 — compile our library's C, the shim and the stub"
rm -f "$LIB_OBJ"/*.o
# Wasm/Main.c is the NATIVE CLI driver: it defines `main` and pulls in
# lean_setup_args. It must never be linked into the wasm module.
while IFS= read -r f; do
  b="$(echo "${f#$LEAN_DIR/.lake/build/ir/}" | sed 's|/|_|g; s|\.c$||')"
  [ "$b" = "Wasm_Main" ] && continue
  emcc $CFLAGS -c "$f" -o "$LIB_OBJ/$b.o"
done < <(find "$LEAN_DIR/.lake/build/ir" -name '*.c')
emcc $CFLAGS -c "$LEAN_DIR/Wasm/l4_shim.c"  -o "$LIB_OBJ/l4_shim.o"
emcc $CFLAGS -c "$LEAN_DIR/Wasm/l4_stubs.c" -o "$LIB_OBJ/l4_stubs.o"
echo "  library objects: $(ls "$LIB_OBJ"/*.o | wc -l | tr -d ' ')"

# ---------------------------------------------------------------------
say "step 7 — link"
# em++ (not emcc) for the link: the C driver does not pull in libc++,
# and Lean's runtime is C++.
# The linker's dead-code elimination is what keeps this small — most of
# Init is never reached from the exported entry points.
em++ -O3 -DNDEBUG -fwasm-exceptions \
  "$LIB_OBJ"/*.o "$CORE_OBJ"/*.o "$RT_OBJ"/*.o \
  -o "$WORK/l4factoidal.mjs" \
  -sMODULARIZE=1 -sEXPORT_ES6=1 \
  -sEXPORTED_FUNCTIONS=_l4_init,_l4_version_c,_l4_bgp_query_c,_l4_free_result,_malloc,_free \
  -sEXPORTED_RUNTIME_METHODS=ccall,cwrap,UTF8ToString \
  -sALLOW_MEMORY_GROWTH=1 \
  -sSTACK_SIZE=8MB \
  -sENVIRONMENT=web,worker,node \
  -sASSERTIONS=0

# ---------------------------------------------------------------------
say "step 8 — install artifacts"
# The glue looks for its sibling by the basename emcc chose; keep that
# name and let our loader supply the bytes explicitly anyway.
cp "$WORK/l4factoidal.mjs"  "$ASSETS/l4factoidal.mjs"
cp "$WORK/l4factoidal.wasm" "$ASSETS/l4factoidal.wasm"
ls -l "$ASSETS"
echo
echo "wasm bytes: $(wc -c < "$ASSETS/l4factoidal.wasm")"
echo "done."
