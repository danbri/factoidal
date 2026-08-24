# toolchain-cache (orphan branch)

Prebuilt F* toolchain pieces so fresh sandboxes skip the ~25-minute
opam source build. Not merged into main lines; fetched on demand:

    git fetch origin toolchain-cache
    git checkout origin/toolchain-cache -- .   # into a scratch dir

Contents:
- fstar-<version>-<platform>.tar.gz.partNN — split (<100MB/blob)
  gzip tarball of `bin/fstar.exe` + `lib/fstar` from the opam switch
  named in the filename. Reassemble: `cat *.partNN > f.tar.gz`,
  verify against SHA256SUMS, untar into the switch prefix.
- SHA256SUMS — of the reassembled tarball.

The consumer is tools/install-toolchain-cache.sh on the main line
(also used by the session bootstrap hook). Rebuild + re-push these
chunks when the pinned F* version in bin/ci-linux-x86_64/
build-info.json changes. See skills/fstar-env/SKILL.md.


## l4wasm-work-cache-v4.33.1.tar.gz

The Lean4-to-wasm build's expensive intermediates, keyed to
`formal/lean4/lean-toolchain` = leanprover/lean4:v4.33.1 and
Emscripten 6.0.8: regenerated core-library C (`core-c/`, Init + the
Std/Data subset), its wasm objects (`core-obj/`), the runtime objects
(`rt-obj/`, mimalloc included), the staged headers, and the sparse
lean4/mimalloc sources. Restore with:

    mkdir -p $HOME/l4wasm-work
    tar xzf l4wasm-work-cache-v4.33.1.tar.gz -C $HOME
    L4_WASM_WORK=$HOME/l4wasm-work formal/lean4/Wasm/build-wasm.sh

Emscripten itself is NOT cached (1.7 GB): `git clone
https://github.com/emscripten-core/emsdk && ./emsdk install 6.0.8 &&
./emsdk activate 6.0.8` reinstalls it from the network in minutes,
and `apt-get install libuv1-dev` supplies uv.h. Delete this tarball
when the lean-toolchain pin moves.