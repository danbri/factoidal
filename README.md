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
