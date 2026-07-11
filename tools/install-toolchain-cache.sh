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

# Retry a flaky network command up to 4x with quadratic backoff. The
# sandbox network drops connections mid-fetch, and a single failure is
# not a real error (handoff note 2026-07-10: "git fetch is flaky, retry
# w/ backoff"). Used for the two cache-branch fetches below.
retry() {
  local n=1 max=4
  while true; do
    "$@" && return 0
    [ "$n" -ge "$max" ] && return 1
    log "retry $n/$max failed ($1 ...); sleeping $((n*n*2))s"
    sleep $((n*n*2))
    n=$((n+1))
  done
}

# Already done? Require BOTH fstar.exe AND the compile-deps sentinel. A
# partial state — fstar.exe present but fstar.lib's deps missing, exactly
# the 2026-07-11 first-build failure — must fall through so step 5
# finishes the deps. Every intermediate step below is independently
# idempotent, so a fall-through when only the deps are outstanding is a
# cheap no-op, not a rebuild.
if { command -v fstar.exe >/dev/null 2>&1 || { command -v opam >/dev/null 2>&1 \
     && [ -x "$(opam var --switch=fstar bin 2>/dev/null)/fstar.exe" ]; }; } \
   && [ -f "$REPO_ROOT/.claude-runs/toolchain-deps.ok" ]; then
  log "fstar.exe + compile deps already present; nothing to do"
  exit 0
fi

# 1. apt
if ! command -v opam >/dev/null 2>&1 || ! command -v ocaml >/dev/null 2>&1; then
  log "apt: opam + ocaml + gmp + zstd (~1 min)"
  # A broken THIRD-PARTY repo (e.g. the ondrej/php PPA changing its
  # published Label, observed 2026-07-11) makes `apt-get update` exit
  # non-zero even though the main Ubuntu archives refreshed fine.
  # Chaining `update && install` then aborts the whole toolchain install
  # over a repo we do not even use. So run update TOLERANTLY, and
  # hard-gate only on the install of the packages we actually need — all
  # of which live in the main archives.
  # libzstd-dev: without it the compile step disables the Parquet zstd
  # C stub and native linking fails on caml_parquet_zstd_decompress_hex
  apt-get update -qq \
    || log "apt-get update reported errors (continuing — usually a broken third-party PPA, not our packages)"
  apt-get install -y -qq opam ocaml libgmp-dev pkg-config m4 libzstd-dev \
    || { log "APT FAILED (main-archive packages could not be installed)"; exit 1; }
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

# 3b. Pin z3 4.13.3 inside the switch bin as well. Some containers ship a
#     newer z3 higher on PATH, or a later `opam install` pulls one into
#     the switch; either silently shadows 4.13.3, and a bare `fstar.exe`
#     without `--z3version` then uses the wrong solver (Iron Rule #10;
#     session-restore never-again #2 — a 2026-07-10 container shipped z3
#     4.16.0 first on PATH). Belt-and-braces with the /usr/local/bin/z3
#     symlink from step 2.
if [ -x /usr/local/bin/z3-4.13.3 ]; then
  mkdir -p "$SWITCH_PREFIX/bin"
  ln -sf /usr/local/bin/z3-4.13.3 "$SWITCH_PREFIX/bin/z3"
fi

# 4. F* from the cache branch
if [ ! -x "$SWITCH_PREFIX/bin/fstar.exe" ]; then
  log "fetching toolchain-cache branch chunks"
  TC=/tmp/toolchain-cache.$$
  mkdir -p "$TC"
  retry git -C "$REPO_ROOT" fetch -q origin toolchain-cache \
    || { log "FETCH toolchain-cache FAILED after retries"; exit 1; }
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
  if retry git -C "$REPO_ROOT" fetch -q origin checked-cache 2>/dev/null; then
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
#    does not need them). A success sentinel (toolchain-deps.ok) lets a
#    build tell "deps ready" from "still installing / failed" instead of
#    failing cryptically at the ocamlopt link step.
mkdir -p "$(dirname "$DEPS_LOG")"
DEPS_OK="$REPO_ROOT/.claude-runs/toolchain-deps.ok"
# Guard on BOTH a build dep (zarith) AND a fstar.lib runtime dep
# (batteries): a PARTIAL prior install — zarith present but the fstar.lib
# deps missing, exactly the 2026-07-11 first-build failure — must be
# COMPLETED on re-run, not skipped by a zarith-only sentinel.
if ! { ocamlfind list 2>/dev/null | grep -q zarith \
       && ocamlfind list 2>/dev/null | grep -q batteries; }; then
  rm -f "$DEPS_OK"
  log "opam deps (zarith sha digestif js_of_ocaml + fstar.lib runtime deps + uucp) installing in background -> $DEPS_LOG"
  # F* is dropped here as a binary untar (step 4), which bypasses opam's
  # dependency resolution — so fstar.lib's own runtime requires
  # (batteries, pprint, ppx_deriving[_yojson], yojson, stdint) are never
  # pulled and the compile step fails with "Package `batteries' not found -
  # required by `fstar.lib'". uucp is needed directly by build-ocaml.sh's
  # ocamlopt link line. Retry (a flaky sandbox network drops mid-install)
  # and touch the sentinel on success.
  nohup bash -c '
    deps_ok="$1"
    for attempt in 1 2 3; do
      if opam install -y zarith sha digestif js_of_ocaml js_of_ocaml-compiler zarith_stubs_js ocamlfind \
           uucp batteries stdint pprint ppx_deriving ppx_deriving_yojson yojson; then
        touch "$deps_ok"; echo "opam deps: complete"; exit 0
      fi
      echo "opam deps attempt $attempt failed; retrying in $((attempt*10))s" >&2
      sleep $((attempt*10))
    done
    echo "opam deps FAILED after 3 attempts — first ./build-ocaml.sh will fail at link; re-run tools/install-toolchain-cache.sh" >&2
    exit 1
  ' _ "$DEPS_OK" > "$DEPS_LOG" 2>&1 &
else
  # Deps already present (e.g. a pre-existing install predating the
  # sentinel) — record it so the top "already done?" guard early-exits
  # cleanly on the next run instead of falling through every time.
  touch "$DEPS_OK"
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
