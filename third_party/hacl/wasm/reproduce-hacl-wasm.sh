#!/usr/bin/env bash
# Reproduce hacl-wasm@1.4.0's Ed25519 + SHA-2 (+ Curve25519) WebAssembly
# from HACL* source via KaRaMeL's wasm backend ("WASM*" pipeline).
#
# We NEVER hand-roll crypto. This script rebuilds HACL*'s verified wasm;
# every primitive is HACL*'s F*/Low*-verified code. See
# docs/designissues/2026-07-08-self-hosted-hacl-wasm.md and
# skills/crypto-policy/SKILL.md. Relates to #63 and #286.
#
# Two modes:
#   byte-identical  Use the EXACT pinned toolchain that produced
#                   hacl-wasm@1.4.0. Goal: bit-for-bit identical .wasm.
#   functional      Use whatever F*/KaRaMeL is on PATH. Goal: correct
#                   crypto (passes RFC vectors), NOT byte-identical.
#
# Authoritative toolchain pin (from the 1.4.0 tarball's INFO.txt):
#   F* version:      e617752a1b014a16892f7d8772d62e5c234f06c1
#   KaRaMeL version: 2cf2974007f4103dba5619e4eb9e3eaeefad533b
#   Vale version:    0.3.19
#
# This environment (2026-07-08) has KaRaMeL 11bb8e1 + F* 2025.12.15 —
# both NEWER than the pins, so `byte-identical` mode requires installing
# the pinned toolchain first; `functional` mode runs as-is but produces
# non-identical bytes (proven: WasmSupport.wasm is 1131 B here vs 1135 B
# upstream, identical through offset 394 then diverges).

set -euo pipefail

MODE="${1:-functional}"
HACL_WASM_VERSION="1.4.0"
FSTAR_PIN="e617752a1b014a16892f7d8772d62e5c234f06c1"
KRML_PIN="2cf2974007f4103dba5619e4eb9e3eaeefad533b"
VALE_PIN="0.3.19"

WORK="${WORK:-$(mktemp -d)}"
REF="${REF:-}"        # dir of reference .wasm to diff against (optional)
JOBS="${JOBS:-$(nproc)}"

say() { printf '\n=== %s ===\n' "$*"; }

case "$MODE" in
  byte-identical|functional) ;;
  *) echo "usage: $0 [byte-identical|functional]"; exit 2 ;;
esac

say "mode=$MODE  work=$WORK  jobs=$JOBS"

# ---------------------------------------------------------------------------
# 0. Toolchain
# ---------------------------------------------------------------------------
if [ "$MODE" = "byte-identical" ]; then
  cat <<EOF
byte-identical mode needs the PINNED toolchain. Install, in order:
  1. F*      @ $FSTAR_PIN   (build per FStarLang/FStar README)
  2. KaRaMeL @ $KRML_PIN    (build per FStarLang/karamel README)
  3. Vale    @ $VALE_PIN
The Project Everest docker image for this era pins all three together;
prefer it over building each from source. Then re-run with these on PATH:
  export FSTAR_EXE=/path/to/fstar.exe
  export KRML_HOME=/path/to/karamel
  export PATH="\$KRML_HOME:\$PATH"
EOF
  : "${FSTAR_EXE:?set FSTAR_EXE to the pinned fstar.exe}"
  : "${KRML_HOME:?set KRML_HOME to the pinned karamel checkout}"
else
  # functional mode: use the project's fstar switch + installed krml.
  eval "$(opam env --switch=fstar 2>/dev/null || true)"
  FSTAR_EXE="${FSTAR_EXE:-$(command -v fstar.exe)}"
  KRML_HOME="${KRML_HOME:-/root/karamel}"
  export PATH="$KRML_HOME:$PATH"
fi

command -v krml   >/dev/null || { echo "krml not on PATH"; exit 1; }
"$FSTAR_EXE" --version | head -1
echo "krml: $(krml -version 2>&1 | head -1)"

# krml copies its JS loader runtime from <krml-bindir>/../lib/krml/js.
# Our install ships it under $KRML_HOME/krmllib/js; stage it if missing.
KRML_BIN="$(command -v krml)"
KRML_LIBJS="$(dirname "$KRML_BIN")/../lib/krml/js"
if [ ! -e "$KRML_LIBJS/browser.js" ] && [ -d "$KRML_HOME/krmllib/js" ]; then
  mkdir -p "$KRML_LIBJS"
  cp -r "$KRML_HOME/krmllib/js/." "$KRML_LIBJS/" || true
fi

# ---------------------------------------------------------------------------
# 1. HACL* source (disk-safe sparse clone)
# ---------------------------------------------------------------------------
say "clone hacl-star (sparse)"
cd "$WORK"
if [ ! -d hacl-star/.git ]; then
  git clone --depth 1 --filter=blob:none --sparse \
    https://github.com/hacl-star/hacl-star.git
fi
cd hacl-star
# Everything the F* extraction + wasm target touches.
git sparse-checkout set --skip-checks \
  Makefile Makefile.common Makefile.include Makefile.local \
  code specs lib vale providers dist hints obj mk .docker .scripts \
  runtimeconfig.json Hacl.fst.config.json
echo "hacl-star HEAD: $(git rev-parse HEAD)"

# ---------------------------------------------------------------------------
# 2. F* extraction -> obj/*.krml  (the expensive, toolchain-pinned step)
# ---------------------------------------------------------------------------
# hacl-star's Makefile drives F* over the Low* sources to produce
# obj/*.krml, then invokes `krml -minimal -wasm` over them. The wasm
# target is `dist/wasm`. This step is a multi-hour verified build.
say "build dist/wasm (F* extract -> krml -wasm)"
export FSTAR_HOME="" # let hacl-star resolve via FSTAR_EXE
make -j"$JOBS" FSTAR_EXE="$FSTAR_EXE" KRML_HOME="$KRML_HOME" \
  VALE_HOME="${VALE_HOME:-}" dist/wasm/Makefile.basic

OUT="$WORK/hacl-star/dist/wasm"
say "built artifacts"
ls -la "$OUT"/*.wasm | sed -n '1,40p'
cat "$OUT/INFO.txt" 2>/dev/null || true

# ---------------------------------------------------------------------------
# 3. Diff against reference bytes (if provided)
# ---------------------------------------------------------------------------
if [ -n "$REF" ]; then
  say "diff vs reference ($REF)"
  rc=0
  for f in Hacl_Ed25519 Hacl_Hash_SHA2 Hacl_Curve25519_51 FStar WasmSupport; do
    if [ -f "$OUT/$f.wasm" ] && [ -f "$REF/$f.wasm" ]; then
      if cmp -s "$OUT/$f.wasm" "$REF/$f.wasm"; then
        echo "$f.wasm  BYTE-IDENTICAL"
      else
        echo "$f.wasm  DIFFER ($(wc -c <"$OUT/$f.wasm") vs $(wc -c <"$REF/$f.wasm") bytes)"
        rc=1
      fi
    fi
  done
  [ "$MODE" = "byte-identical" ] && exit "$rc"
fi

# ---------------------------------------------------------------------------
# 4. Functional test (RFC 8032 Ed25519 / FIPS 180-4 SHA-256)
# ---------------------------------------------------------------------------
# Node harness: load the built wasm via the generated loader/api and run
# the same vectors as the vc-crypto tests. Left as the integration hook —
# api.json in the built dist enumerates each function's `tests` vectors
# (the loader's own self-test), e.g. Hacl_Hash_SHA2 hash("abc") = ba78...
say "functional check hint"
echo "Run the loader self-tests (node $OUT/api_test.js) or wire"
echo "$OUT/*.wasm + loader.js into the vc-crypto RFC-vector harness."

say "done. artifacts in $OUT"
echo "(clean up: rm -rf $WORK)"
