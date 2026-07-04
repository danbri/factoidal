---
name: build-and-test
description: Build, extract, compile, and test the Factoidal F* project. Use when the user asks to "run the tests", "verify F*", "build the binary", "extract OCaml", "build for JS/WASM", or wants to know how to invoke the W3C test runner. Also use when troubleshooting build-ocaml.sh, ocaml-patches.sh, or test-runner output.
---

# Build, extract, and test

The `formal/fstar/build-ocaml.sh` script orchestrates F\* → OCaml extraction,
compilation to native binaries, and the JS/WASM extraction targets. The
W3C test runner exercises the resulting binaries against the real W3C
test corpora vendored as a submodule.

This skill assumes the toolchain is already set up. If `fstar.exe`,
`make verify`, or `./build-ocaml.sh` fails before producing output, run
the **fstar-env** skill first.

## TL;DR

```bash
eval $(opam env --switch=fstar)
cd formal/fstar

make verify                # F* type-check + SMT discharge
./build-ocaml.sh           # full extract + compile + test
./build-ocaml.sh extract   # extract only
./build-ocaml.sh compile   # compile only (skip extract; doesn't run patches)
./build-ocaml.sh test      # run tests only
./build-ocaml.sh js        # js_of_ocaml output
./build-ocaml.sh wasm      # wasm_of_ocaml output (experimental)
./build-ocaml.sh karamel   # F* → .krml (C-build pilot; krml binary install pending)

cd ocaml-output
./w3c_runner               # all SPARQL suites
./w3c_runner --rdf         # RDF parser suites
./w3c_runner --all         # both
./w3c_runner --list        # list suites
./w3c_runner bind          # specific suite(s)
./w3c_runner -v aggregates # verbose: full expected/actual on stderr
```

## Build steps in detail

### `make verify`

Walks the `MODULES` list in `formal/fstar/Makefile` and writes a
`<module>.verified` marker per module. Failure ⇒ a real spec error
(rare during setup, common during dev). z3 wrong version ⇒ false
errors that look like real ones; check `z3 --version` first.

The `Makefile` passes `--z3version 4.13.3` via the `FSTAR` variable.

### `./build-ocaml.sh extract`

Runs `fstar.exe --codegen OCaml` over the hardcoded module list inside
the script. **Each new F\* module must be added to that list** (search
for `for fst in ... do` around line 215).

Common pitfall: extract does not pass `--z3version 4.13.3` on older
checkouts (pre-PR `claude/build-z3version-flag`). If you see
`Unexpected Z3 version` errors, that fix is the prereq.

The .ml output files in `ocaml-output/` are tracked in git.

### `./build-ocaml.sh compile`

Compiles the extracted .ml plus the hand-written CLI/runner wrappers
into native binaries. **Does NOT run `ocaml-patches.sh`** — if a fresh
extraction needs patches, use `extract` (which includes patches) or
run `./ocaml-patches.sh` manually.

Output binaries land in `bin/<platform>/` (e.g. `bin/linux-x86_64/`).
Symlinks from `ocaml-output/` point to them. Per Iron Rule #9 the
binaries are committed; do not skip them when staging.

### `./build-ocaml.sh test`

Runs unit tests. Does not run W3C tests — use `./w3c_runner` for those.

### `./build-ocaml.sh js`

Produces `docs/fstar-extracted/factoidal.js` via js_of_ocaml. Used
for the demo page deployment (CI rebuilds and commits it). For a
source-mapped debuggable variant see the `jsoo-debug-bundle` skill.

### `./build-ocaml.sh wasm`

Experimental wasm_of_ocaml output, using the vendored zarith wasm
runtime in `ocaml-output/wasm_runtime/` plus `wasm_stub_shims.py`
post-processing. The historical SHA/MD5 crashes in the `functions`
suite are why hashes are realised by the pure-OCaml
`fstar_pure_hashes.ml` (no C primitives) — see the `ocaml-boundary`
skill. Check `tests/beyond-w3c/` parity results for current
wasm-runtime status before quoting a suite count.

### `./build-ocaml.sh karamel`

C-build pilot: runs `fstar.exe --codegen krml` on a small allowlist
of pure modules and writes `.krml` files to `krml-output/`. Currently
extracts 5/6 candidates clean; `RDF.Format.fst` fails Warning 250
(string-pattern match arms not supported by KaRaMeL). Final
`.krml → .c → .a` step blocked on krml binary install.

See `docs/designissues/2026-05-07-c-build-and-roaring-plan.md`.

## W3C test runner

The committed binary is `bin/<platform>/w3c_runner` (works on a fresh
clone with no toolchain). After a local build, a symlink also appears
at `formal/fstar/ocaml-output/w3c_runner`.

### Test data discovery

The runner searches a list of relative paths for the test fixture
submodule:

1. `third_party/testing/w3c/sparql/sparql11`
2. `../../third_party/testing/w3c/sparql/sparql11`
3. `../../../third_party/testing/w3c/sparql/sparql11`
4. `../../tests/w3c/sparql/sparql11` (legacy)
5. `../../../tests/w3c/sparql/sparql11` (legacy)
6. `tests/w3c/sparql/sparql11` (legacy)

If none are found, output shows zero tests. Always run from a
directory whose ancestor contains `third_party/testing/w3c/`. The
project root works; `formal/fstar/ocaml-output/` works.

If the binary in `bin/linux-x86_64/` was built before the
`third_party/...` paths were added, it'll only know the legacy paths
and fail on a fresh checkout. Recompile.

### Output format

```
TOTAL: 626 pass, 1 fail, 4 skip, 0 unsupported
```

Always show pass/fail/skip explicitly. Per anti-pattern #25, **never**
write "626/631" without labels — split into pass-vs-fail and
pass-vs-total framings if both ratios matter.

The most-recent recorded run's JSON is at
`docs/test-results/latest.json` and historical runs are in
`docs/test-results/history/`.

### Failure debugging

- `-v <suite>` writes the full expected vs actual row dump to stderr.
- FAIL lines on stdout always show the unmatched expected rows
  inline; -v adds the actual rows.
- For a single test: `./w3c_runner -v <suite>` then grep stderr.

### Current scores

Do not trust score tables embedded in docs — they go stale. The live
numbers are in `docs/test-results/latest.json` (and the dashboard at
https://danbri.github.io/factoidal/test-results/). Regenerate locally
with `./w3c-tests.sh --cached`. For reference: as of 2026-07-03 the
runnable W3C total was 1662 pass, 0 fail (SPARQL 631, RDF 1031).
The full testing landscape (OWL, RDFC-1.0, parity, probes) is in the
`test-suites` skill.

## W3C test data layout (submodule)

```
third_party/testing/w3c/                   git submodule (rdf-tests)
  rdf/rdf11/rdf-n-triples/                 N-Triples syntax tests
  rdf/rdf11/rdf-turtle/                    Turtle syntax+eval tests
  rdf/rdf11/rdf-n-quads/                   N-Quads syntax tests
  rdf/rdf11/rdf-trig/                      TriG syntax+eval tests
  rdf/rdf11/rdf-xml/                       RDF/XML eval tests
  rdf/rdf11/rdf-mt/                        Model theory / semantics
  sparql/sparql11/                         SPARQL 1.1 (34 suites, 631 tests)
```

Initialise via `git submodule update --init --recursive` — without it
the runner reports zero tests.

## Extraction notes (F\* → OCaml)

- `--codegen OCaml` erases proofs, ghost code, spec-only material.
- Extracted .ml files use the `FStar_*` runtime from `fstar.lib`
  (opam package).
- `Prims.int` extracts to `Z.t` (zarith). Boundary casts: `Z.of_int`,
  `Z.to_int`, `Z.lt` for compares, `Z.to_string` + `%s` for Printf.
- `assume val` declarations extract as `failwith "Not yet
  implemented"` — must be patched via `ocaml-patches.sh`.
- `noeq` types block KaRaMeL C extraction (OCaml extraction works
  fine).

## Common build / test failures

| Symptom | Cause | Fix |
|---|---|---|
| `Unexpected Z3 version: expected '4.8.5', got '4.13.3'` | Pre-fix build-ocaml.sh extract | Merge `claude/build-z3version-flag` or pass `--z3version 4.13.3` manually |
| `failwith "Not yet implemented"` at runtime | Unpatched `assume val` | Run `./build-ocaml.sh extract` or `./ocaml-patches.sh` |
| `bin/linux-x86_64/w3c_runner` shows 0 tests | Stale binary; built before submodule paths added | Rebuild: `./build-ocaml.sh` |
| Ext fails with `MLP_Const` translate error | Module has string-pattern match arms unsupported by KaRaMeL | Refactor to `if/else if`; or omit from karamel allowlist |
| Compile fails on `Prims.int` mismatch | OCaml int passed where Z.t expected | Add `Z.of_int` at the call site |
| `FATAL: another build-ocaml.sh is already running in this worktree` | Stale or concurrent invocation holds the per-worktree flock | Wait for the running build, or `pkill -f 'build-ocaml.sh'` if stuck |
| Fresh build fails with `Unbound module FooBar` | Source-without-build-wiring (workflow-gotchas-debugging §3) | Add the new module to all three lists in `build-ocaml.sh` (extract loop, `COMMON_MODULES`, `FSTAR_MODULES`) |
| Modules being re-extracted that should be cached | Concurrent fstar.exe runs from parallel agents corrupting the .checked.lax cache | Lock should prevent same-worktree races; check `ps aux \| grep fstar.exe` for cross-worktree contention |

## Single-runner lock and build-running marker

`build-ocaml.sh` opens a `flock` on `.build.lock` at entry. Concurrent
invocations in the same worktree exit immediately with exit code 75
and a `FATAL: another build-ocaml.sh is already running` message.

The lock is per-worktree — two worktrees can build concurrently and
won't block each other (their locks are at different paths). Only
same-worktree concurrency is refused, which is enough to prevent the
.cmi/.cmx/.checked-cache races we hit in 2026-05-07.

The marker file `.build-running` is written on entry and removed via
`trap` on exit (success or failure or signal). Stop hooks should
suppress "uncommitted changes" warnings while this file exists, since
the build is actively rewriting `.ml` and binary files.

Both files are gitignored (`formal/fstar/.gitignore`).

## What this skill does NOT do

- Does not set up the F\* toolchain — see the `fstar-env` skill.
- Does not modify F\* source files.
- Does not interpret W3C test failures as spec issues — that's a
  judgement call for the developer.

## Cross-references

- `fstar-env` skill — toolchain setup, z3 install, opam switch.
- `fast-verify-extract` skill — skip the full `./build-ocaml.sh` cycle
  for a single-module change: `.checked` caching, targeted
  verify/extract of just the edited module, and safe parallelism.
- `docs/designissues/2026-05-07-c-build-and-roaring-plan.md` —
  KaRaMeL pilot details, krml install paths.
- `test-suites` skill — every suite (W3C, OWL, RDFC, parity, probes)
  and the reporting discipline.
- `perf-benchmarking` skill — timing and performance measurement.
- `ocaml-boundary` skill — what may be hand-written OCaml at all.
