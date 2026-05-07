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

First-time only:

```bash
opam init -y
opam switch create fstar ocaml-base-compiler.4.14.1
eval $(opam env --switch=fstar)
opam install -y fstar z3 js_of_ocaml js_of_ocaml-compiler zarith_stubs_js
```

The `opam install` line installs F\* itself plus the JS extraction
toolchain. The `z3` opam package is installed too, but the build often
fails or produces the wrong version — §3 replaces the binary on PATH.

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

Factoidal vendors W3C test files as a git submodule. Without them,
`./w3c_runner` has no test data:

```bash
cd /path/to/factoidal
git submodule update --init --recursive
```

`third_party/testing/w3c/` should be populated after this.

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

- `CLAUDE.md` § "Setup" — authoritative source for these instructions.
- `docs/skills/testing.md` — what to do once the env works.
- `docs/skills/measuring.md` — performance measurement setup.
- `formal/roaring/src/Makefile` — example of a standalone
  `make verify` target outside the main F\* tree.
