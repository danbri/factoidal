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
say "step 1b — patch the runtime's string_to_list_core for wasm32"
# Upstream defect, present at v4.33.1 AND on leanprover/lean4 master
# (checked 2026-08-25): runtime/object.cpp's string_to_list_core — the
# body of lean_string_data, i.e. String.data / String.toList —
# terminates the List Char it builds with `lean_box_uint32(0)`. On
# 64-bit targets that folds to the scalar lean_box(0), the correct
# representation of List.nil, so no shipped Lean build ever misbehaves.
# On wasm32 (sizeof(void*) == 4) lean_box_uint32 HEAP-ALLOCATES a ctor
# object (tag 0, 0 fields, 4 scalar bytes) — which is NOT a scalar.
# Lean-COMPILED consumers read that object's pointer tag (0 = List.nil)
# and work anyway, so span/take/foldl over such a list all pass — but
# lean_string_mk (String.mk / String.ofList) walks the list with
# `while (!lean_is_scalar(o))`, never meets a scalar terminator, reads
# a garbage tail out of the fake nil's scalar area and runs off across
# the heap until a word with the low bit set stops it: measured
# 2026-08-25 as a 3,267,424,256-byte std::string allocation
# (std::bad_alloc) from `_init_..._closed__48` under lean_obj_once.
# lean_box(0) is List.nil's representation on EVERY target; patch the
# one line. The guard makes this idempotent across cached work dirs;
# a fresh patch application invalidates the cached object.o.
OBJ_CPP="$RT_SRC/runtime/object.cpp"
if grep -q 'obj_res  r = lean_box_uint32(0);' "$OBJ_CPP"; then
  sed -i.bak 's|obj_res  r = lean_box_uint32(0);|obj_res  r = lean_box(0); /* wasm32 patch (build-wasm.sh step 1b): List.nil must be the scalar lean_box(0); lean_box_uint32 heap-allocates on 32-bit, and lean_string_mk then never sees a list terminator */|' \
    "$OBJ_CPP"
  rm -f "$OBJ_CPP.bak" "$RT_OBJ/object.o"
  echo "  patched string_to_list_core (object.o invalidated)"
else
  grep -q 'wasm32 patch (build-wasm.sh step 1b)' "$OBJ_CPP" \
    && echo "  already patched" \
    || { echo "  PATCH ANCHOR NOT FOUND — upstream object.cpp changed; re-audit string_to_list_core"; exit 1; }
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
# Init always; plus the Std subset the library imports (Std.Data.HashMap
# / HashSet arrived with RLClosureIndexed and the COTTAS lazy dicts —
# their initializers pull the Std/Data + Std/Classes import closure).
# Std.Time / Std.Net / Std.Internal.UV are NOT regenerated: their C
# references libuv definitions the wasm link has only declarations for.
STD_DIRS=""
for d in "$LEAN_SRC/Std/Data" "$LEAN_SRC/Std/Classes" "$LEAN_SRC/Std/Do"; do
  [ -d "$d" ] && STD_DIRS="$STD_DIRS $d"
done
{ echo "$LEAN_SRC/Init.lean"; find "$LEAN_SRC/Init" -name '*.lean'; \
  [ -n "$STD_DIRS" ] && find $STD_DIRS -name '*.lean'; true; } \
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
# uv.h is needed for DECLARATIONS only (io.cpp includes it). The
# header is STAGED into an isolated include dir rather than adding its
# system directory to the include path: on Linux the header lives in
# /usr/include, and putting -I/usr/include on an Emscripten compile
# line makes glibc headers shadow the wasm sysroot's
# (bits/wordsize.h fatal error in step 5).
UVINC=""
for d in /opt/homebrew/include /usr/local/include /usr/include; do
  if [ -f "$d/uv.h" ]; then
    mkdir -p "$WORK/uv-include"
    cp "$d/uv.h" "$WORK/uv-include/"
    [ -d "$d/uv" ] && cp -r "$d/uv" "$WORK/uv-include/"
    UVINC="-I $WORK/uv-include"
    break
  fi
done
[ -n "$UVINC" ] || { echo "uv.h not found (apt-get install libuv1-dev / brew install libuv) — needed for declarations only"; exit 1; }
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
# lean_setup_args. It must never be linked into the wasm module — and
# neither may Wasm/Cli.c (the l4factoidal CLI, its own `main`) nor ANY
# Harness executable root: every Harness_* unit
# carries its own `_lean_main` (the runners l4w3c, l4shacl, l4rif, …),
# and linking two of them is a duplicate-symbol error. The wasm module
# is the LIBRARY plus Wasm_{Abi,Exports}; executables stay native.
while IFS= read -r f; do
  rel="${f#$LEAN_DIR/.lake/build/ir/}"
  b="$(echo "$rel" | sed 's|/|_|g; s|\.c$||')"
  [ "$b" = "Wasm_Main" ] && continue
  [ "$b" = "Wasm_Cli" ] && continue
  case "$b" in Harness_*) continue;; esac
  # Lake never deletes the ir of a module that was deleted or renamed;
  # a stale .c whose .lean source is gone duplicates symbols with the
  # module that replaced it (RIF/Core.c vs RIF/Syntax.c). Compile only
  # C whose source module still exists.
  src="$LEAN_DIR/${rel%.c}.lean"
  [ -f "$src" ] || { echo "  (skipping stale ir: $rel — no $src)"; continue; }
  emcc $CFLAGS -c "$f" -o "$LIB_OBJ/$b.o"
done < <(find "$LEAN_DIR/.lake/build/ir" -name '*.c')
emcc $CFLAGS -c "$LEAN_DIR/Wasm/l4_shim.c"  -o "$LIB_OBJ/l4_shim.o"
emcc $CFLAGS -c "$LEAN_DIR/Wasm/l4_stubs.c" -o "$LIB_OBJ/l4_stubs.o"
# HACL* Ed25519 — the library's one `@[extern]` family
# (L4Factoidal/Crypto/Ed25519.lean, realised by ffi/hacl_ed25519.c over
# the vendored, unmodified third_party/hacl C). Native builds get the
# same four units from the lakefile's extern_lib; the wasm module needs
# them compiled for wasm32 here, or the link fails on the three
# l4_hacl_ed25519_* symbols. Crypto policy: HACL* on every target, never
# a different implementation (skills/crypto-policy, Lean 4 amendment).
# The shim's object is named l4_hacl_shim.o, NOT hacl_ed25519.o: on a
# case-insensitive filesystem that name collides with Hacl_Ed25519.o.
HACL_DIR="$REPO_ROOT/third_party/hacl"
for f in "$HACL_DIR/src/Hacl_Ed25519.c" "$HACL_DIR/src/Hacl_Curve25519_51.c" \
         "$HACL_DIR/src/Hacl_Hash_SHA2.c"; do
  emcc $CFLAGS -I "$HACL_DIR/include" -c "$f" -o "$LIB_OBJ/$(basename "${f%.c}").o"
done
emcc $CFLAGS -I "$HACL_DIR/include" -c "$LEAN_DIR/ffi/hacl_ed25519.c" -o "$LIB_OBJ/l4_hacl_shim.o"
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
  -sEXPORTED_FUNCTIONS=_l4_init,_l4_version_c,_l4_bgp_query_c,_l4_call_c,_l4_free_result,_malloc,_free \
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
# ---------------------------------------------------------------------
say "step 9 — companion npm package + Pages mirror + provenance"
NPMLEAN="$LEAN_DIR/../../npm/factoidal-lean"
MIRROR="$LEAN_DIR/../../docs/npm/lean"
if [ -d "$NPMLEAN" ]; then
  WASM_SHA=$(sha256sum "$ASSETS/l4factoidal.wasm" | cut -d' ' -f1)
  # Stamp the wasm's content hash into the wrapper's WASM_VERSION
  # constant (issue #584) BEFORE copying it anywhere, so the loader
  # that ships to the Pages assets dir, npm/factoidal-lean/ and
  # docs/npm/lean/ all carry the same value and the wasm fetch's `?v=`
  # query string changes exactly when the wasm bytes change -- the
  # ServiceWorker's stale-while-revalidate cache (docs/sw.js) keys by
  # pathname, so without this a fresh loader could pair with a stale
  # wasm for one page load after a deploy.
  sed -i.bak -E "s/^const WASM_VERSION = \"[0-9a-f]*\";/const WASM_VERSION = \"${WASM_SHA:0:12}\";/" "$ASSETS/l4factoidal.js"
  rm -f "$ASSETS/l4factoidal.js.bak"
  cp "$ASSETS/l4factoidal.js" "$ASSETS/l4factoidal.mjs" "$ASSETS/l4factoidal.wasm" "$NPMLEAN/"
  GIT_SHA=$(git -C "$LEAN_DIR" rev-parse HEAD 2>/dev/null || echo unknown)
  EMCC_VER=$(emcc --version | head -1)
  LEAN_TC=$(cat "$LEAN_DIR/lean-toolchain")
  PKG_VER=$(python3 -c "import json;print(json.load(open('$NPMLEAN/package.json'))['version'])")
  python3 - "$NPMLEAN/version.json" <<PYEOF
import json, sys, datetime
json.dump({
  "version": "$PKG_VER",
  "gitSha": "$GIT_SHA",
  "builtAt": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
  "leanToolchain": "$LEAN_TC",
  "emscripten": "$EMCC_VER",
  "abiVersion": "1",
  "wasmSha256": "$WASM_SHA",
  "wasmBytes": $(stat -c %s "$ASSETS/l4factoidal.wasm" 2>/dev/null || stat -f %z "$ASSETS/l4factoidal.wasm"),
  "claims": {
    "source": "formal/lean4 (L4Factoidal): no sorry, no user axioms, no native_decide; W3C behaviour pinned by build-time #guard",
    "suitesAtBuildSha": "see docs/test-results and formal/lean4/PORT_NOTES.md at gitSha"
  }
}, open(sys.argv[1], "w"), indent=2)
PYEOF
  mkdir -p "$MIRROR"
  cp "$NPMLEAN"/l4factoidal.js "$NPMLEAN"/l4factoidal.mjs "$NPMLEAN"/l4factoidal.wasm \
     "$NPMLEAN"/version.json "$NPMLEAN"/package.json "$NPMLEAN"/README.md "$NPMLEAN"/LICENSE "$MIRROR/" 2>/dev/null || true
  echo "  companion + mirror updated (wasm sha256 $WASM_SHA)"

  # The IN-PACKAGE copy. Issue #618 moved the Lean engine's assets
  # INSIDE @factoidal/core (npm/factoidal/l4-assets/), which is the
  # copy a plain `npm install @factoidal/core` actually resolves; the
  # three directories above are the superseded companion package and
  # its Pages mirror. This step was missing until 2026-08-26, so the
  # rebuild of #627 left l4-assets/ holding the PREVIOUS wasm while the
  # other three carried the new one, and the four copies -- which the
  # tarball gate and the loader's WASM_VERSION assume are byte-identical
  # -- silently disagreed. Syncing it here rather than by hand is what
  # stops that recurring.
  L4ASSETS="$LEAN_DIR/../../npm/factoidal/l4-assets"
  if [ -d "$L4ASSETS" ]; then
    cp "$ASSETS/l4factoidal.js" "$ASSETS/l4factoidal.mjs" "$ASSETS/l4factoidal.wasm" "$L4ASSETS/"
    # Its version.json carries `engine` and `note` members the companion
    # package's does not, so refresh the provenance fields in place
    # instead of overwriting the file.
    python3 - "$L4ASSETS/version.json" "$NPMLEAN/version.json" <<'PYSYNC'
import json, sys
dst_path, src_path = sys.argv[1], sys.argv[2]
src = json.load(open(src_path))
dst = json.load(open(dst_path))
for k in ("version", "gitSha", "builtAt", "leanToolchain", "emscripten",
          "abiVersion", "wasmSha256", "wasmBytes", "claims"):
    dst[k] = src[k]
# A stale-artifact note is a claim about the PREVIOUS build; a fresh
# build is exactly the event that retires it.
dst.pop("sourceDrift", None)
with open(dst_path, "w") as f:
    json.dump(dst, f, indent=2)
    f.write("\n")
PYSYNC
    echo "  in-package l4-assets updated (npm/factoidal/l4-assets)"
  else
    echo "  (npm/factoidal/l4-assets absent — in-package step skipped)"
  fi

  # Every committed copy must be byte-identical: the loader stamps ONE
  # WASM_VERSION (the wasm's own sha256 prefix) into the `?v=` query
  # string, so a copy that differs would be served under a hash that is
  # not its own.
  BADCOPY=0
  for d in "$ASSETS" "$NPMLEAN" "$MIRROR" "$LEAN_DIR/../../npm/factoidal/l4-assets"; do
    [ -f "$d/l4factoidal.wasm" ] || continue
    THIS=$(sha256sum "$d/l4factoidal.wasm" | cut -d' ' -f1)
    if [ "$THIS" != "$WASM_SHA" ]; then
      echo "  MISMATCH $d/l4factoidal.wasm has $THIS, expected $WASM_SHA"
      BADCOPY=1
    fi
  done
  [ "$BADCOPY" -eq 0 ] || { echo "committed wasm copies disagree — refusing to report success"; exit 1; }
  echo "  all committed wasm copies agree ($WASM_SHA)"
else
  echo "  (npm/factoidal-lean absent — companion step skipped)"
fi

echo "done."
