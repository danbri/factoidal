# The all-skosdex build machine: packs every fetchable skosdex vocabulary
# into one wire-version-10 generation, activates it, and syncs it to an R2
# bucket. See README.md beside this file.
#
# TWO engines are in the image, and the pack and activate steps prefer the
# first:
#
#   1. The NATIVE Lean tools `l4block-shard-pack` and
#      `l4block-shard-activate`, built from this repository in the first
#      stage below. The 37 GB source needs them: the WebAssembly module
#      cannot finish it, because Emscripten's allocator holds memory the
#      native process gives back (measurements in
#      docs/designissues/2026-09-07-wasm-packer-memory.md). The native
#      packer stays near 400 MB of peak footprint at 256 MiB batches.
#   2. `@factoidal/core` from the npm registry, which supplies the
#      `factoidal` command for the version line and as the fallback route
#      if a binary is absent.

# ---------------------------------------------------------------------------
# Stage 1: build the two native packer binaries
# ---------------------------------------------------------------------------
FROM debian:bookworm-slim AS lean

RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      git ca-certificates curl build-essential \
 && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path \
 && rm /tmp/elan-init.sh

# The ref to build. A branch name, a tag, or a full commit SHA: the fetch
# below asks the remote for the ref by name, and GitHub serves a reachable
# SHA the same way.
ARG FACTOIDAL_REF=claude/main
ARG FACTOIDAL_REPO=https://github.com/danbri/factoidal

# The repository's .git history is about 20 GB, so it is never cloned whole.
# --filter=blob:none fetches no file contents until a checkout asks for them,
# --depth 1 fetches one commit, and the sparse cone limits the checkout to
# what the Lake package reads: `formal/lean4` (the package itself, including
# its `lean-toolchain` and its `ffi/` C shims) and `third_party/hacl` (the
# vendored HACL* C the lakefile compiles into libl4hacl.a, reached as
# ../../third_party/hacl). Nothing here is a Git LFS object; the flag says so
# rather than leaving it to the absence of git-lfs in this stage.
RUN git init -q /src \
 && git -C /src remote add origin "$FACTOIDAL_REPO" \
 && git -C /src config core.sparseCheckout true \
 && git -C /src sparse-checkout set --cone formal/lean4 third_party/hacl \
 && GIT_LFS_SKIP_SMUDGE=1 git -C /src fetch --depth 1 --filter=blob:none origin "$FACTOIDAL_REF" \
 && GIT_LFS_SKIP_SMUDGE=1 git -C /src checkout --detach FETCH_HEAD \
 && git -C /src log -1 --format='factoidal ref %H %ci' \
 && du -sh /src/.git /src/formal/lean4

# The package's own lean-toolchain is the pin. Installing it as an explicit
# step keeps the version visible in the build log instead of arriving as a
# side effect of the first `lake` call.
RUN elan toolchain install "$(cat /src/formal/lean4/lean-toolchain)" \
 && elan default "$(cat /src/formal/lean4/lean-toolchain)" \
 && lean --version && lake --version

# The two target names are the `lean_exe` declarations in
# formal/lean4/lakefile.lean:
#     @[default_target] lean_exe «l4block-shard-activate» ...
#     @[default_target] lean_exe «l4block-shard-pack» ...
# Naming them builds those two and nothing else. A bare `lake build` would
# build every default target: about forty executables plus the wasm library,
# and the machine runs two of them.
#
# No `-j`: Lake 5.0.0 (the Lake shipped with Lean 4.33.1) has no such flag
# and fails the build with `unknown short option '-j'` — measured
# 2026-09-07. LEAN_NUM_THREADS is the job count, set from the builder's
# core count.
#
# No `--no-cache` / `--try-cache`: lake-manifest.json lists no packages, so
# there is no dependency cache to fetch or skip.
#
# Lake still elaborates every module in the two executables' import closure,
# which is most of L4Factoidal, and then compiles the generated C. This is
# the long step of the image build.
WORKDIR /src/formal/lean4
RUN set -e; \
    nproc; \
    LEAN_NUM_THREADS="$(nproc)" lake build l4block-shard-pack l4block-shard-activate; \
    for b in l4block-shard-pack l4block-shard-activate; do \
      test -x ".lake/build/bin/$b"; \
      { ldd ".lake/build/bin/$b" || echo "ldd: $b is not a dynamic executable"; }; \
      "./.lake/build/bin/$b" 2>&1 | head -1; \
    done

# ---------------------------------------------------------------------------
# Stage 2: the machine that runs the pipeline
# ---------------------------------------------------------------------------
FROM node:22-bookworm-slim

# libgmp10: Lean's toolchain links its own libgmp.a, so the binaries are
# expected to need nothing beyond the base image. The package is here as
# insurance against a toolchain that links GMP dynamically instead; the
# `ldd` line in stage 1 records which it was.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      git git-lfs rclone gzip gawk ca-certificates procps curl libgmp10 \
 && rm -rf /var/lib/apt/lists/* \
 && git lfs install --system

# The newest 0.7.x at image build time; 0.7.1 adds --batch-bytes and the
# script falls back to the engine default under 0.7.0. Kept for the
# `factoidal` CLI: the version line, and the pack/activate fallback route
# when a native binary is missing.
ARG FACTOIDAL_CORE_VERSION=^0.7.0
RUN npm install -g "@factoidal/core@${FACTOIDAL_CORE_VERSION}" \
 && factoidal version

COPY --from=lean /src/formal/lean4/.lake/build/bin/l4block-shard-pack \
                 /src/formal/lean4/.lake/build/bin/l4block-shard-activate \
                 /opt/factoidal/bin/
# Both binaries answer the usage line and exit 2 with no arguments. The gate
# is the `grep`, not the exit code: it fails the image build if a binary
# cannot start in THIS stage (a shared library the build stage had and this
# one does not).
RUN set -e; \
    chmod 0755 /opt/factoidal/bin/l4block-shard-pack /opt/factoidal/bin/l4block-shard-activate; \
    /opt/factoidal/bin/l4block-shard-pack 2>&1 | grep -q '^usage: l4block-shard-pack'; \
    /opt/factoidal/bin/l4block-shard-activate 2>&1 | grep -q '^usage: l4block-shard-activate'

COPY build-skosall.sh /opt/build-skosall.sh
RUN chmod 0755 /opt/build-skosall.sh

WORKDIR /data
CMD ["bash", "/opt/build-skosall.sh"]
