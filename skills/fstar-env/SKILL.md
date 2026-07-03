---
name: fstar-env
description: Set up or repair the F* / opam / z3 toolchain for the Factoidal project. Use when the user asks to install or set up F*, when `fstar.exe` is missing from PATH, when z3 has the wrong version (must be 4.13.3), when `make verify` or `build-ocaml.sh` fails with toolchain errors, when starting on a fresh clone that hasn't been bootstrapped, or when an agent has been "burning time on partial builds" because the opam switch isn't activated.
---

# F\* / opam / z3 environment setup

The Factoidal project verifies F\* specs and extracts OCaml from them. Without
a correctly configured F\*/opam/z3 toolchain, **nothing in `formal/fstar/`
works** — verification fails, extraction fails, and the OCaml binaries can't
be rebuilt. This skill handles first-time setup, repair, and diagnosis.

The authoritative source for setup details is `CLAUDE.md` in the project root
(the "Setup" section). This skill is the operational distillation; if the two
ever drift, CLAUDE.md wins and this skill should be updated to match.

## When to use this skill

Run this skill when any of the following are true:

- `fstar.exe --version` errors with "command not found".
- `z3 --version` shows anything other than `4.13.3`.
- `make verify` in `formal/fstar/` fails with a missing-binary error.
- `./build-ocaml.sh` (any subcommand) fails before producing output.
- The user asks to "set up F\*", "install F\*", "fix the F\* env", etc.
- A fresh clone hasn't yet had the toolchain bootstrapped.

## Iron rules (these are not optional)

1. **Never use `--lax`.** The flag is banned project-wide. If verification
   fails, fix the spec or install the missing tool — do not work around the
   failure with `--lax`.
2. **Always activate the opam switch before any F\* work.** Every shell
   that invokes `fstar.exe`, `make verify`, or `build-ocaml.sh` must run
   `eval $(opam env --switch=fstar)` first. If `fstar.exe` is missing from
   PATH, stop and activate the switch rather than burning time on partial
   builds.
3. **z3 must be exactly 4.13.3.** Other versions silently produce wrong
   answers or refuse proofs that should go through. The `apt-get install z3`
   version is too old; the `opam install z3` build often fails. Use the
   pre-built binary from the Z3Prover GitHub release (see §3).

## Quick diagnostic

Before installing anything, check what's already there:

```bash
# What's installed?
opam --version 2>&1 || echo "opam: missing"
opam switch show 2>&1 | grep -q fstar && echo "fstar switch: present" || echo "fstar switch: missing"
which fstar.exe 2>&1 || echo "fstar.exe: not on PATH (switch may not be activated)"
z3 --version 2>&1 || echo "z3: missing"
```

If `fstar switch` is present but `fstar.exe` is not on PATH, **the switch
just needs activation** — see §4. Don't reinstall anything.

If `z3 --version` shows something other than 4.13.3, replace it (§3). Wrong
versions of z3 are a top-three time-sink in this project.

## §1. System prerequisites

Linux (Debian/Ubuntu):

```bash
sudo apt-get update
sudo apt-get install -y opam libgmp-dev pkg-config unzip curl
```

macOS (Homebrew):

```bash
brew install opam gmp pkg-config
```

Both need: `unzip`, `curl` for fetching the z3 binary release.

## §2. opam + F\* toolchain

**Fast path first (2-4 minutes, no compiles).** There is no upstream
apt/deb package for F\*, opam builds it from source (~25 min), and
F\*'s prebuilt GitHub release binaries are 403'd by scoped sandbox
proxies. So the repo carries its own prebuilt cache on the
`toolchain-cache` orphan branch (split <100MB chunks of
`bin/fstar.exe` + `lib/fstar`, SHA256-verified; main-line clones
never pay for it). One command:

```bash
tools/install-toolchain-cache.sh
```

apt ocaml (system 4.14.1 = CI's) + opam switch on the system compiler
+ pip-wheel z3 4.13.3 + untar F\* — verification-ready immediately;
the small opam deps for compile/js (`zarith`, `sha`, `digestif`,
`js_of_ocaml*`) install in the background
(`.claude-runs/toolchain-deps.log`). The session bootstrap hook runs
this automatically in remote sandboxes. When the pinned F\* version
changes (see `fstar_version` in `bin/ci-linux-x86_64/build-info.json`),
rebuild the chunks per the README on the `toolchain-cache` branch.

**Source-build path (fallback / new versions).** First-time only:

```bash
opam init -y                    # add --disable-sandboxing in containers
opam switch create fstar ocaml-base-compiler.4.14.1
eval $(opam env --switch=fstar)
opam install -y fstar.2025.12.15 js_of_ocaml js_of_ocaml-compiler zarith_stubs_js sha digestif
```

**Pin the F\* version to what CI extracts with** — read
`fstar_version` in `bin/ci-linux-x86_64/build-info.json` (2025.12.15
at the time of writing) and install exactly that. A newer opam F\*
verifies fine but its `--codegen OCaml` output differs, so a local
extraction churns all ~90 tracked `.ml` files against CI's and the
tree thrashes between versions per committer. Verified the hard way
2026-07-03 (opam default gave 2026.03.24 vs CI's 2025.12.15;
downgrade before extracting).

Do NOT add the `z3` opam package: it installs a current z3 (4.16+)
into the switch's bin, which then shadows the pinned 4.13.3 on PATH
whenever the switch is active. This is survivable — every repo script
passes `--z3version 4.13.3`, which makes F\* select the
`z3-4.13.3`-named binary rather than plain `z3` — but a bare
`fstar.exe` invocation without the flag will silently use the wrong
solver. §3 installs the pinned binary.

## §3. Install z3 4.13.3 (CRITICAL)

The opam-built or apt-installed z3 will not work. Install the pre-built
binary from the official Z3 release:

### Linux x86-64

```bash
cd /tmp
curl -sL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip" -o z3.zip
unzip -q z3.zip
sudo cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/local/bin/z3-4.13.3
sudo chmod +x /usr/local/bin/z3-4.13.3
sudo ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3
```

### Proxied sandboxes where GitHub release downloads 403

Tested access model in Claude Code on the web sandboxes (2026-07-03,
via `$HTTPS_PROXY/__agentproxy/status` + direct probes): **git
protocol to ANY GitHub repository works** (clone/fetch/ls-remote,
including into /tmp — not just the session-scoped repo), but
`api.github.com` and `github.com/<owner>/<repo>/releases/download/...`
return 403 JSON, so release assets and API calls fail — the `z3.zip`
above arrives as a ~175-byte error body and unzip fails. Package
registries (PyPI, npm, crates.io, proxy.golang.org) bypass the proxy
entirely. Consequences: anything published as a release asset needs a
mirror (this repo's `toolchain-cache` branch) or a registry-published
equivalent. Fallback that works because PyPI is open:

```bash
python3 -m venv /tmp/z3venv && /tmp/z3venv/bin/pip install -q z3-solver==4.13.3.0
sudo cp /tmp/z3venv/bin/z3 /usr/local/bin/z3-4.13.3
sudo chmod +x /usr/local/bin/z3-4.13.3
sudo ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3
```

(The wheel bundles the same upstream binary. Confirmed working
2026-07-03.)

### macOS arm64 (Apple Silicon)

```bash
cd /tmp
curl -sL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-osx-13.7.zip" -o z3.zip
unzip -q z3.zip
sudo cp z3-4.13.3-arm64-osx-13.7/bin/z3 /usr/local/bin/z3-4.13.3
sudo chmod +x /usr/local/bin/z3-4.13.3
sudo ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3
```

### macOS via Homebrew (fallback, may not pin version)

```bash
brew install z3
```

Verify the version after install:

```bash
z3 --version    # must show "Z3 version 4.13.3"
z3-4.13.3 --version    # also must show "Z3 version 4.13.3"
```

If either is missing or shows a different version, do not proceed —
debug the install before continuing.

## §4. Activate the switch in this shell

This is the single most common reason F\* commands fail in a session
where everything was previously working:

```bash
eval $(opam env --switch=fstar)
```

Add this to the user's shell rc file (`~/.bashrc`, `~/.zshrc`) for
persistence, or run it at the start of every Factoidal-related shell.

After activation:

```bash
which fstar.exe         # should resolve under ~/.opam/fstar/bin/
fstar.exe --version     # should print a version string
```

## §5. Verify the install end-to-end

```bash
cd /path/to/factoidal
eval $(opam env --switch=fstar)
cd formal/fstar
make verify
```

`make verify` should walk the `MODULES` list in the Makefile and emit a
per-module `.verified` marker file. Any failure here is either:

- A bug in the spec (rare during setup; common during development).
- A missing/wrong-version z3 (most likely cause during setup).
- A missing `fstar.exe` (switch not activated).

If you suspect z3 is at fault, run a single module by hand and read the
solver output:

```bash
fstar.exe RDF.Graph.Executable.fst
```

z3 errors will appear in the F\* output verbatim.

## §6. Submodules (test data)

Test corpora are git submodules under `third_party/testing/`. A clone
made without `--recurse-submodules` has empty directories there, and
the runners then report **zero tests** — worse, `./w3c-tests.sh`
(without `--cached`) will overwrite the committed result logs and
dashboard with a 0/0 run. If you ever see "0 pass, 0 fail", this is
why: init the submodules, `git checkout` the clobbered logs, rerun.

Two submodules are load-bearing for the test suites:

```bash
cd /path/to/factoidal
git submodule update --init third_party/testing/w3c \
                            third_party/testing/rdf-canon
```

- `third_party/testing/w3c` — w3c/rdf-tests (SPARQL 1.1 + RDF 1.1
  suites; pinned to a commit on the RDF 1.2
  `sparql-mixed-rdf-version-tests` branch). Feeds `w3c_runner`.
- `third_party/testing/rdf-canon` — RDFC-1.0 canonicalization tests.
  Feeds `rdfc10_runner`.

The other five (`shex`, `csvw`, `vc`, `did`, `rml`) are vendored for
future suites and not yet wired to any runner —
`git submodule update --init --recursive` pulls everything if you
prefer one command. OWL 2 test data is NOT a submodule (it's a static
vendored drop at `third_party/testing/owl/`, present in every clone),
and the UK Parliament perf corpus lives at `third_party/data/`.

## §7. Build the OCaml binaries

Once verification works:

```bash
cd formal/fstar
eval $(opam env --switch=fstar)   # always
./build-ocaml.sh                  # full extract + compile cycle
```

The script auto-detects the platform and writes binaries to
`bin/<platform>/`, with symlinks under `ocaml-output/`. Pre-built
binaries for `darwin-arm64` and `linux-x86_64` live in the repo and can
be used directly without an F\* toolchain — but only if the spec
hasn't changed since the last commit.

`build-ocaml.sh extract` re-extracts (use after editing `.fst` files
or after a fresh checkout). `build-ocaml.sh compile` compiles
without re-extracting. **Important: `compile` does not apply
`ocaml-patches.sh`** — use `extract` after pulling fresh sources.

## §8. Common failure modes

| Symptom | Likely cause | Fix |
|---|---|---|
| `fstar.exe: command not found` | Switch not activated | `eval $(opam env --switch=fstar)` |
| `Z3 version 4.8.x` etc. | Wrong z3 binary | Reinstall per §3 |
| `make verify` hangs > 5 min on one module | z3 timeout / wrong solver | Check z3 version, then look for a deep proof obligation |
| Mysterious "Syntax error" far from real issue | Reserved word (`total`, `in_mem`, …) or `*)` inside a comment | Check the line *above* the reported one; grep for parens-stars in comments |
| `./build-ocaml.sh` fails with linking error | OCaml stdlib mismatch from old switch | `opam reinstall fstar.lib zarith` |
| Extracted code calls `failwith "Not yet implemented"` | An `assume val` wasn't patched | Check `ocaml-patches.sh` ran; cross-reference glue files in `minimal_regrettable_glue_code_each_with_an_open_issue/` |

## §9. CI / Claude Code on the web

For Claude Code on the web sessions, the toolchain isn't pre-installed
in the sandbox. Two options:

1. Use the committed pre-built binaries in `bin/<platform>/` for runtime
   tests; only run `./w3c_runner` and similar, not `fstar.exe` /
   `build-ocaml.sh`.
2. Run a `SessionStart` hook (see the `session-start-hook` skill) that
   installs opam + the fstar switch + z3 4.13.3 from the binary release.

Option 1 is faster (seconds vs minutes) and adequate for any work that
doesn't change `.fst` files or extracted `.ml` files. Option 2 is needed
for end-to-end verification or extraction work.

## §10. Sanity test for "is the env working?"

A one-shot sanity check that exercises the full pipeline:

```bash
cd /path/to/factoidal
eval $(opam env --switch=fstar)
z3 --version | grep -q 4.13.3 || { echo "z3 wrong version"; exit 1; }
fstar.exe --version | head -1 || { echo "fstar broken"; exit 1; }
cd formal/fstar
make verify >/dev/null && echo "verify OK"
echo "env appears healthy"
```

If all three of the version check, `make verify`, and the final echo
succeed, the toolchain is good.

## What this skill does NOT do

- It does not run `make verify` or `build-ocaml.sh` for the user — those
  are user-driven actions, not setup steps.
- It does not modify `~/.bashrc` / `~/.zshrc` — that's a user choice.
- It does not install KaRaMeL (needed for C extraction). KaRaMeL is a
  separate setup; only relevant when extracting C/WASM, not for the
  default OCaml path.
- It does not install OCaml-side ecosystem tools (dune, etc.) beyond
  what `opam install` brought in.

## Cross-references

- `CLAUDE.md` — authoritative source for the iron rules here.
- `build-and-test` skill — what to do once the env works.
- `test-suites` skill — running the conformance suites (the committed
  binaries in `bin/<platform>/` run them with NO toolchain at all).
- `perf-benchmarking` skill — performance measurement setup.
- `formal/roaring/src/Makefile` — example of a standalone
  `make verify` target outside the main F\* tree.
