#!/usr/bin/env bash
# tools/install-toolchain-cache.sh — stand up the F* toolchain from the
# repo's `toolchain-cache` orphan branch in ~2-4 minutes, instead of the
# ~25-minute opam source build. See skills/fstar-env/SKILL.md §2.
#
# What it does (all idempotent):
#   1. apt: opam + system OCaml 4.14.1 (matches CI) + libgmp/pkg-config
#   2. z3 4.13.3 from the PyPI z3-solver wheel (GitHub releases 403
#      through scoped sandbox proxies; PyPI is open)
#   3. opam switch `fstar` on the SYSTEM compiler (no compiler build)
#   4. F* binary + lib/fstar from the toolchain-cache branch chunks
#   5. background: opam install of the small runtime deps needed by
#      the compile/js steps (zarith sha digestif js_of_ocaml ...)
#
# Exit codes: 0 ok (deps may still be installing in background — see
# $DEPS_LOG); non-zero = a hard step failed, stderr says which.

set -uo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FSTAR_VERSION="${FSTAR_VERSION:-2025.12.15}"   # keep = CI build-info.json
PLAT="linux-x86_64"
DEPS_LOG="$REPO_ROOT/.claude-runs/toolchain-deps.log"

log() { echo "install-toolchain-cache: $*" >&2; }

# Already done?
if command -v fstar.exe >/dev/null 2>&1 || { command -v opam >/dev/null 2>&1 \
   && [ -x "$(opam var --switch=fstar bin 2>/dev/null)/fstar.exe" ]; }; then
  log "fstar.exe already present; nothing to do"
  exit 0
fi

# 1. apt
if ! command -v opam >/dev/null 2>&1 || ! command -v ocaml >/dev/null 2>&1; then
  log "apt: opam + ocaml + gmp + zstd (~1 min)"
  # libzstd-dev: without it the compile step disables the Parquet zstd
  # C stub and native linking fails on caml_parquet_zstd_decompress_hex
  apt-get update -qq && apt-get install -y -qq opam ocaml libgmp-dev pkg-config m4 libzstd-dev \
    || { log "APT FAILED"; exit 1; }
fi

# 2. z3 4.13.3 via wheel
if ! z3 --version 2>/dev/null | grep -q 4.13.3; then
  log "z3 4.13.3 via PyPI wheel"
  python3 -m venv /tmp/z3venv 2>/dev/null
  /tmp/z3venv/bin/pip install -q z3-solver==4.13.3.0 \
    && cp /tmp/z3venv/bin/z3 /usr/local/bin/z3-4.13.3 \
    && chmod +x /usr/local/bin/z3-4.13.3 \
    && ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3 \
    || { log "Z3 WHEEL FAILED"; exit 1; }
fi

# 3. opam switch on the system compiler (no build)
opam init -y --disable-sandboxing --bare >/dev/null 2>&1
if ! opam switch list 2>/dev/null | grep -q fstar; then
  log "opam switch (system ocaml, no compiler build)"
  opam switch create fstar --packages=ocaml-system -y >/dev/null \
    || { log "SWITCH FAILED"; exit 1; }
fi
eval "$(opam env --switch=fstar)"
SWITCH_PREFIX="$(opam var prefix)"

# 4. F* from the cache branch
if [ ! -x "$SWITCH_PREFIX/bin/fstar.exe" ]; then
  log "fetching toolchain-cache branch chunks"
  TC=/tmp/toolchain-cache.$$
  mkdir -p "$TC"
  git -C "$REPO_ROOT" fetch -q origin toolchain-cache \
    || { log "FETCH toolchain-cache FAILED"; exit 1; }
  # git archive: reads the commit without touching the main worktree
  # or its index (safe while a build is running there)
  git -C "$REPO_ROOT" archive --format=tar origin/toolchain-cache | tar -x -C "$TC" \
    || { log "ARCHIVE toolchain-cache FAILED"; exit 1; }
  cat "$TC"/fstar-"$FSTAR_VERSION"-"$PLAT".tar.gz.part* > "$TC/fstar.tar.gz" \
    || { log "cache chunks for $FSTAR_VERSION/$PLAT not found"; exit 1; }
  EXPECT=$(awk '{print $1}' "$TC/SHA256SUMS" | head -1)
  GOT=$(sha256sum "$TC/fstar.tar.gz" | awk '{print $1}')
  [ "$EXPECT" = "$GOT" ] || { log "SHA256 MISMATCH ($GOT != $EXPECT)"; exit 1; }
  log "untarring fstar.exe + lib/fstar into the switch"
  tar -C "$SWITCH_PREFIX" -xzf "$TC/fstar.tar.gz" || { log "UNTAR FAILED"; exit 1; }
  rm -rf "$TC"
fi

# 4b. .checked verification cache (gates-green snapshots only; see
#     skills/session-restore gate rule). Partial hits are still wins.
if [ ! -e "$REPO_ROOT/formal/fstar/RDF.Graph.Executable.fst.checked" ]; then
  if git -C "$REPO_ROOT" fetch -q origin checked-cache 2>/dev/null; then
    CC=/tmp/checked-cache.$$
    mkdir -p "$CC"
    git -C "$REPO_ROOT" archive --format=tar origin/checked-cache | tar -x -C "$CC" \
      && ( cd "$CC" && sha256sum -c SHA256SUMS >/dev/null 2>&1 ) \
      && tar -C "$REPO_ROOT/formal/fstar" -xzf "$CC"/checked-*.tar.gz \
      && log ".checked cache restored ($(ls "$REPO_ROOT"/formal/fstar/*.checked | wc -l) modules)" \
      || log ".checked cache restore failed (non-fatal; cold verify will rebuild)"
    rm -rf "$CC"
  fi
fi

# 5. runtime deps for compile/js steps, in background (verify-only work
#    does not need them)
mkdir -p "$(dirname "$DEPS_LOG")"
if ! ocamlfind list 2>/dev/null | grep -q zarith; then
  log "opam deps (zarith sha digestif js_of_ocaml ...) installing in background -> $DEPS_LOG"
  nohup opam install -y zarith sha digestif js_of_ocaml js_of_ocaml-compiler zarith_stubs_js ocamlfind \
    > "$DEPS_LOG" 2>&1 &
fi

# 5b. wasm builds: wasm_of_ocaml-compiler needs binaryen >= 116 for
#     wasm-merge. Ubuntu apt ships binaryen 108 (no wasm-merge) and
#     GitHub release assets are proxy-blocked; conda-forge tarballs
#     are plain HTTPS and work (2026-07-04 lesson). Idempotent.
if ! command -v wasm-merge >/dev/null 2>&1; then
  log "binaryen 121 (wasm-merge) from conda-forge -> /usr/local"
  (
    set -e
    BTMP="$(mktemp -d)"
    curl -sSL --max-time 180 -o "$BTMP/binaryen.conda" \
      "https://api.anaconda.org/download/conda-forge/binaryen/121/linux-64/binaryen-121-h5888daf_0.conda"
    command -v zstd >/dev/null 2>&1 || apt-get install -y -qq zstd
    python3 -c "import zipfile; zipfile.ZipFile('$BTMP/binaryen.conda').extract('pkg-binaryen-121-h5888daf_0.tar.zst', '$BTMP')"
    mkdir -p "$BTMP/pkg"
    tar --zstd -xf "$BTMP/pkg-binaryen-121-h5888daf_0.tar.zst" -C "$BTMP/pkg"
    cp -a "$BTMP/pkg/bin/"* /usr/local/bin/
    cp -a "$BTMP/pkg/lib/"* /usr/local/lib/ 2>/dev/null || true
    ldconfig
    rm -rf "$BTMP"
  ) >> "$DEPS_LOG" 2>&1 || log "WARNING: binaryen install failed (wasm builds unavailable; js/native unaffected)"
fi
if command -v wasm-merge >/dev/null 2>&1 && ! command -v wasm_of_ocaml >/dev/null 2>&1; then
  log "opam wasm_of_ocaml-compiler installing in background -> $DEPS_LOG"
  nohup opam install -y wasm_of_ocaml-compiler >> "$DEPS_LOG" 2>&1 &
fi

log "fstar: $("$SWITCH_PREFIX/bin/fstar.exe" --version 2>/dev/null | head -1)"
log "ready for verification now; compile-ready when $DEPS_LOG shows success"
exit 0
