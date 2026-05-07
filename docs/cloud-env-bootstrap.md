# Cloud env bootstrap — what we needed to add to a fresh image

Snapshot taken 2026-05-07 after a multi-day Claude Code cloud-env
session. Documents the deltas between a vanilla Ubuntu 24.04 image
(as supplied by the harness) and the working state needed to build,
verify, and test Factoidal.

The intent is: next time we spin up a fresh cloud env, this doc
should be the punch-list for getting from "blank slate" to "ready to
work on factoidal" in under 30 minutes.

## What the image already had (do not reinstall)

Pre-baked by the harness. No action needed:

- Ubuntu 24.04 base (linux 6.18.5).
- `build-essential`, `clang`, `clang-format`, `clang-tidy`, `lld`,
  `lldb`, `llvm`, `g++-13`, `gcc-13`, `gdb`, `valgrind`, `autoconf`,
  `automake`, `libtool`, `bison`, `flex`.
- `cmake` 3.28, `ninja-build` 1.11, `pkg-config`, `make` 4.3.
- Python 3.10, 3.11, 3.12, 3.13 with `dev`, `venv`, `pip`.
- `openjdk-21-jdk`.
- Docker (`docker-ce`, `containerd.io`, `docker-buildx-plugin`,
  `docker-compose-plugin`).
- `node`/`npm` (via `.bun`, `.cargo`, `.npm` in `~`).
- `tmux`, `vim`, `nano`, `less`, `ripgrep`, `jq`, `yq`, `lsof`,
  `strace`, `curl`, `wget`, `unzip`, `zip`, `xz-utils`, `bzip2`.
- `git` 2.43, `gnupg2`, `ssh-client`, `ca-certificates`.
- `tree`, `nettcat`, `bc`, `age`, `software-properties-common`.
- `postgresql-16`, `redis-server` 7.0, `poppler-utils`.
- `php8.4` family (cli, common, curl, dev, gd, igbinary, intl,
  mbstring, mysql, opcache, pgsql, readline, redis, sqlite3, xml,
  zip).
- A bunch of X11/audio libs for headless browser support
  (`xvfb`, `libnss3`, `fonts-liberation`, etc.).
- `/tmp/code-sign` symlink → `/opt/env-runner/environment-manager`,
  used by `gpg.ssh.program` for commit signing.

## Deltas applied during this session

These are the things we had to do on top of the harness image.

### 1. apt installs (3 small batches)

```bash
sudo apt-get install -y opam libgmp-dev pkg-config unzip curl
sudo apt-get install -y libzstd-dev
sudo apt-get install -y gh
```

`opam` brings in OCaml 4.14.1 (`ocaml-interp`, `ocaml-base`,
`libstdlib-ocaml`). `libgmp-dev` is needed for `zarith`. `libzstd-dev`
is needed for the Parquet reader's zstd decompression stub.

`gh` is the GitHub CLI; the `mcp__github__*` tools work without it
(via the MCP server) but `gh` is convenient for ad-hoc auth checks
and PR inspection. Note: this is Ubuntu's bundled `gh` 2.45.0 from
the default apt repo, not the upstream `cli/cli` apt source — that's
fine for our usage.

### 2. Z3 4.13.3 (manual binary install)

F\* needs z3 4.13.3 specifically. Ubuntu's apt-packaged z3 is too
old.

```bash
# Download Z3 4.13.3 release binary (from
# github.com/Z3Prover/z3/releases — pin to 4.13.3 exactly).
# Extract z3 binary to /usr/local/bin/z3-4.13.3.
sudo ln -s /usr/local/bin/z3-4.13.3 /usr/local/bin/z3

# Verify:
z3 --version  # → "Z3 version 4.13.3 - 64 bit"
```

Pin matters: F\* 2025.12.15 fails on z3 4.8.x or 4.12.x. **Iron rule:
no version-mismatch hacks.** See the `fstar-env` skill for the
full version-pin reasoning.

Symlink at `/usr/local/bin/z3` makes `z3 --version` work out of the
box. The versioned binary at `/usr/local/bin/z3-4.13.3` is what the
F\* `--z3version 4.13.3` flag actually invokes.

### 3. opam switch + F\* + dependencies

```bash
opam init --bare --disable-sandboxing -y
opam switch create fstar ocaml-base-compiler.4.14.1 -y
eval $(opam env --switch=fstar)

opam install fstar.2025.12.15 -y
# Brings in: angstrom, astring, bigstringaf, camlp-streams,
#           digestif, eqaf, logs, memtrace, ocplib-endian,
#           ppx_derivers, ppxlib, sha, str, unix, zarith.
```

Total `~/.opam` size: 2.2 GB.

CI uses F\* 2025.12.15. Local can carry multiple versions side by
side — we have 2025.10.06, 2025.12.15, 2026.03.24 installed — but
only 2025.12.15 is the one actually used by `make verify` and
`build-ocaml.sh`. Activate with `eval $(opam env --switch=fstar)`
before any F\* work.

### 4. (NOT installed) — js_of_ocaml + zarith_stubs_js

The `build-ocaml.sh js` and `wasm` targets need:

```bash
opam install js_of_ocaml js_of_ocaml-compiler zarith_stubs_js -y
```

We did **not** install these in this session because we didn't
exercise the JS/WASM extraction path. If the live RIF demo or web
deploy track moves, install these. (They are required per
`build-ocaml.sh`'s preamble comment.)

### 5. (NOT installed) — KaRaMeL `krml`

Per `docs/designissues/2026-05-07-c-build-and-roaring-plan.md`, the
`./build-ocaml.sh karamel` target emits `.krml` files but the final
`krml → .c → .a` step is blocked on installing the `krml` binary.

Opam's `krml` package needs `python2.7` which Ubuntu 24.04 does not
ship; the workaround is the source-build path documented in the
plan doc. We did not attempt this in this session.

### 6. gh CLI auth (one-time, interactive)

```bash
gh auth login
# Use device-code flow — visit the URL it prints in a browser
# OUTSIDE the cloud env, paste the device code, authorise.
# Resulting token: gho_*** stored in /root/.config/gh/hosts.yml.
```

After auth, `gh auth status` should show:
```
github.com
  ✓ Logged in to github.com account danbri
```

Auth survives across sessions provided `~/.config/gh/` is preserved.
If the cloud env wipes home dir between sessions, this is a
re-auth-each-session step.

### 7. Git config

The harness pre-sets:
```bash
git config --global user.name "Claude"
git config --global user.email "noreply@anthropic.com"
git config --global user.signingkey /home/claude/.ssh/commit_signing_key.pub
git config --global gpg.format ssh
git config --global gpg.ssh.program /tmp/code-sign
git config --global commit.gpgsign true
```

`commit.gpgsign true` is on, but pushes routinely succeed even when
the signing key isn't available — the harness's `/tmp/code-sign` is
a symlink to `/opt/env-runner/environment-manager` which handles the
signing transparently.

If commits fail with "gpg failed to sign the data," check that
`/tmp/code-sign` exists and the env-runner is healthy.

### 8. Submodule init

```bash
cd /home/user/factoidal
git submodule update --init --recursive
```

Initialises the W3C test-fixture submodules:

- `third_party/testing/csvw` — CSV-on-the-Web tests
- `third_party/testing/did` — DID test corpus
- `third_party/testing/rdf-canon` — RDFC-1.0 canonicalisation tests
- `third_party/testing/rml` — RML mapping tests
- `third_party/testing/shex` — ShEx tests

The W3C SPARQL+RDF tests (`third_party/testing/w3c/`) need separate
submodule init when that submodule is added — currently it's
already in tree, just needs `update`.

Without these, `w3c_runner` reports zero tests.

## What this session also accumulated (NOT bootstrap, just observations)

- **6.8 GB in `.claude/worktrees/`** across 33 stale agent worktrees.
  Each parallel agent leaves a worktree behind. Daily cleanup recommended:
  ```bash
  git worktree prune --expire 1.day.ago
  # Plus manual rm of agent-* dirs whose branches are merged.
  ```
- **Three F\* versions in `~/.opam`** (2025.10.06, 2025.12.15,
  2026.03.24). The opam install paths are independent so this is
  benign; just disk usage.

## Quick bootstrap script (untested — for documentation only)

For a fresh env, the following sequence should reach "ready to work":

```bash
#!/bin/bash
set -e

# 1. apt deltas
sudo apt-get update
sudo apt-get install -y opam libgmp-dev libzstd-dev pkg-config unzip curl gh

# 2. Z3 4.13.3
ZVER=4.13.3
ZURL="https://github.com/Z3Prover/z3/releases/download/z3-${ZVER}/z3-${ZVER}-x64-glibc-2.35.zip"
TMP=$(mktemp -d)
curl -L "$ZURL" -o "$TMP/z3.zip"
unzip -q "$TMP/z3.zip" -d "$TMP"
sudo cp "$TMP/z3-${ZVER}-x64-glibc-2.35/bin/z3" /usr/local/bin/z3-${ZVER}
sudo ln -sf /usr/local/bin/z3-${ZVER} /usr/local/bin/z3
rm -rf "$TMP"

# 3. opam + F*
opam init --bare --disable-sandboxing -y
opam switch create fstar ocaml-base-compiler.4.14.1 -y
eval $(opam env --switch=fstar)
opam install -y fstar.2025.12.15

# 4. (Optional, for JS/WASM target)
# opam install -y js_of_ocaml js_of_ocaml-compiler zarith_stubs_js

# 5. gh auth (interactive)
gh auth login

# 6. clone + submodules
git clone https://github.com/danbri/factoidal.git
cd factoidal
git submodule update --init --recursive

# 7. verify the toolchain
eval $(opam env --switch=fstar)
cd formal/fstar
fstar.exe --version            # → 2025.12.15
z3 --version                   # → 4.13.3
make verify                    # First module verifies in ~30s

echo "Bootstrap complete."
```

## What's NOT in this doc

- **CLAUDE Code harness setup** — handled by the harness itself.
- **MCP server tokens / config** — handled by the harness.
- **Hooks** (stop hook, etc.) — `.claude/skills/update-config`
  covers these; they live in `~/.claude/settings.json`.
- **Editor config / dotfiles** — out of scope.
- **IDE integrations** — out of scope.

## Cross-references

- `.claude/skills/fstar-env/SKILL.md` — toolchain repair (when this
  bootstrap has been done but something is broken).
- `.claude/skills/build-and-test/SKILL.md` — what to do once the
  toolchain is up.
- `.claude/skills/workflow-gotchas-debugging/SKILL.md` — recovery
  from session-state hazards (worktree leakage, build races).
- `docs/designissues/2026-05-07-c-build-and-roaring-plan.md` — the
  KaRaMeL `krml` install path (currently blocked on python2.7).
