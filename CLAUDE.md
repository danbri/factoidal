# Factoidal — Verified RDF/SPARQL from F*

## :warning: F* Comment Syntax — DANGER :warning:

**F\* comments `(* ... *)` support NESTING.** Any `*)` inside a comment
prematurely closes it, and any `(*` opens a new nesting level. This means
constructs containing `*)` will **silently corrupt the rest of your file**
when placed inside comments.

**This WILL break:**
```fstar
(* ARQ algebra example
   construct(*)
*)
```
The `*)` inside `construct(*)` closes the comment. Everything after it becomes
code. F\* then reports a syntax error **hundreds of lines later**, making
debugging extremely difficult.

**Safe alternatives:**
- Reword to avoid parens-star: `(* COUNT-star special case *)`
- Use `//` line comments (F\* supports them): `// COUNT(*) special case`
- Escape or rephrase: `(* SELECT vars-or-star ... *)`

**Rule: Never put `*)` or `(*` inside an F\* block comment.** Grep your `.fst`
files for these sequences if you get mysterious syntax errors far from the
actual cause.

## What This Project Is

A formally verified RDF/SPARQL implementation. The **F\* specifications are the
product**. Executable code is obtained by **extraction**, not by hand-writing
Rust/JS/OCaml/anything that "mirrors" a spec.

## Iron Rules

1. **F\* is the source of truth.** All RDF/SPARQL logic lives in `.fst` files.
2. **Code is extracted, not hand-written.** Use `fstar.exe --codegen OCaml` (or
   KaRaMeL for C/WASM). Never vibe-code an implementation and claim it "mirrors"
   the spec.
3. **assume val = acknowledged gap.** Every `assume val` must have a stub in
   `minimal_regrettable_glue_code_each_with_an_open_issue/` (individual patch
   files, each with a GitHub issue number in the filename). No silent holes.
4. **Parsers belong in F\*.** RDF serialization parsers (N-Triples, Turtle,
   N-Quads, TriG, RDF/XML, CSV/TSV results) are implemented in F\* and
   extracted. All hand-written OCaml parsers have been removed. New parsers
   MUST be written in F\* first.
5. **Full SPARQL 1.1 is the target.** This includes Query, Update, Protocol,
   SERVICE (federated query), and all result formats (XML/SRX, JSON, CSV, TSV).
   Never default to 1.0 manifests when 1.1 exists.
6. **Run the real W3C test files.** Read manifests, `.rq`, `.srx`, `.ttl` from
   disk. Do not construct synthetic queries that are "inspired by" W3C tests.
7. **No cobbling.** No hand-written JS/Rust/OCaml reimplementations of what F\*
   defines. If you need new functionality, add it in F\* first, then extract.
8. **RDF semantics are not optional.** The rdf-mt (model theory) tests verify
   fundamental RDF graph semantics — literal equivalence, datatype handling,
   language tag normalization, RDFS closure rules. These are core requirements,
   not "just inference." Dismissing them is wrong.
9. **Commit compiled binaries.** The compiled `w3c_runner` and `factoidal`
   binaries live in `bin/<platform>/` (e.g., `bin/darwin-arm64/`,
   `bin/linux-x86_64/`) and MUST be committed to git. This lets anyone
   check out the repo and immediately run tests without needing an F\*/opam
   toolchain. `ocaml-output/` contains symlinks to the current platform's
   binaries. `build-ocaml.sh compile` auto-detects the platform and outputs
   to the correct directory. Do not add binaries to `.gitignore`. Do not
   skip them when staging.
10. **Patches are for stubs and workarounds, NOT logic.** Post-extraction
    patches live in `minimal_regrettable_glue_code_each_with_an_open_issue/`
    as individual files named `<issue>_<description>.sh`. Each patch MUST
    have a corresponding open GitHub issue. Patches may wire `assume val`
    stubs, fix F\* type system limitations, and do forward-reference wiring.
    They must **never** contain RDF/SPARQL semantic logic. If you find yourself
    writing "if the entailment regime is RDFS then do X" in a patch, STOP —
    that logic belongs in F\*. Every line of logic in a patch is unverified,
    won't extract to C/WASM, and must be re-implemented for every target.
    **Known violations:** blank-node-as-existential rewriting (#53).
    When an issue is resolved (F\* replaces the patch), delete the patch
    file. Resolved: RDFS closure + reflexivity axioms (#60) — now lives in
    `RDF.Graph.Executable.fst` as `rdfs_closure_with_reflexivity`.

## Agent Work Strategy

Use subagents aggressively for parallelism — launch separate agents for
independent work (F\* verification + OCaml compile + test runs). Top-level
Claude coordinates; never block the main loop waiting on one task when
other work can proceed. Use `run_in_background: true` for long-running
operations. See rules #19 / #20 / #21 for the timeout + logging discipline
that makes this safe.

## Anti-Patterns (rules #1 – #25)

The full text of each anti-pattern — with war-story justification, example
bugs, and mitigation — lives in
[`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md).
The one-line summaries below are the shortcut. When a commit message says
"per rule #17" or "anti-pattern #15", look it up there.

1. Writing OCaml parsers instead of F\* parsers.
2. Dismissing rdf-mt tests as "needing an inference engine."
3. Reporting misleading test scores (unlabelled numerators/denominators).
4. Building parallel OCaml toolkits instead of extending the F\* spec.
5. Creating symlinks or hacks for version mismatches (esp. z3) — fix the env.
6. Promoted-type blindness: handle `ER_Num`/`ER_Dec`/`ER_Dbl`/`ER_Bool`
   alongside `ER_Term(T_Literal _)` everywhere.
7. Parser/evaluator AST mismatch: grep `SPARQL11_Parser.ml` to see what
   the parser actually emits before adding evaluator logic.
8. `parse_to_scaled` before `parse_double_to_scaled` — always try the
   double-aware form first; E-notation gets mis-parsed as fractional digits
   otherwise.
9. Recursive string-function base cases kill metadata — handle the single-
   element case explicitly to preserve lang tags and datatypes.
10. OCaml `Str` regex operates on bytes, not codepoints; unmatched group
    back-refs raise `Not_found`.
11. `build-ocaml.sh compile` does NOT apply `ocaml-patches.sh`. Use
    `extract` after a fresh extraction or run the patches manually.
12. `(*` inside F\* comments silently swallows the rest of the file.
    Use `//` line comments when the text contains `(*` or `*)`.
13. Never edit extracted `.ml` files in `ocaml-output/` directly — they
    are regenerated by `./build-ocaml.sh extract`. Fix the `.fst` or add
    a patch to `ocaml-patches.sh` instead.
14. Never `|| true` to swallow shell failures — capture the exit code
    explicitly (`CMD_RC=0; cmd || CMD_RC=$?`).
15. Never sneak semantic logic into `ocaml-patches.sh` or `w3c_runner.ml`.
    RDF/SPARQL decisions belong in `.fst` files; patches are I/O glue and
    `assume val` wiring only.
16. Never truncate command output with `tail -N` / `head -N` in scripts.
    Use `tee` to save full output while streaming.
17. Never let ad-hoc parse or SPARQL runs hang indefinitely — cap at
    10 minutes (`timeout 600` or equivalent). Kill and shrink input on cap
    trips; don't rerun and hope.
18. Dump in-flight plan to `.claude-worklog.md` at checkpoints — the
    harness persists transcripts but not in-memory plan state.
19. Every long-running process gets a timestamped log under `.claude-runs/`,
    runs in background, and has a hard wall-clock cap. Record start and
    completion in `.claude-worklog.md`.
20. Never burn clock time on the known-slow Turtle path. Launch
    W3C-scale tests via subagent or `run_in_background`, not in the
    foreground of the main loop.
21. Never stall on parallel work. Push, CI, browser check in flight ≠
    reason to wait — pick the next independent item off the queue.
22. Subagent stall is a checkpoint, not a loss. Check `git status` /
    `git log` / file mtimes before relaunching — the work may already
    be on disk.
23. Scope every subagent to a single commit-sized goal. One subagent =
    one commit = one deliverable.
24. Subagent prompts ship code sketches, not "figure it out". Include
    the concrete diff, file + line, helper function signatures; cap
    scope at one function or one rule.
25. Never write cryptic score strings. "972/59" without labels is
    banned — write "972 pass, 59 fail (out of 1031)".

## Setup

### First-time clone

```bash
git clone --recurse-submodules https://github.com/danbri/factoidal.git
cd factoidal

# If already cloned without --recurse-submodules:
git submodule update --init --recursive
```

The W3C test files live in `tests/w3c/` (submodule pointing to
`github.com/w3c/rdf-tests`). Without initialising the submodule, the test
runner will have no test data.

### System prerequisites

```bash
# Debian/Ubuntu
sudo apt-get install -y opam libgmp-dev pkg-config

# macOS (Homebrew)
brew install opam gmp pkg-config
```

### F\* toolchain (opam)

```bash
# Initialize opam (first time only)
opam init -y
# Create the F* switch:
opam switch create fstar ocaml-base-compiler.4.14.1
eval $(opam env --switch=fstar)
opam install fstar z3 js_of_ocaml js_of_ocaml-compiler zarith_stubs_js

# Activate (run in every new shell)
eval $(opam env --switch=fstar)
```

### Install z3 (CRITICAL — verification cannot work without it)

**This project is about verified code. z3 is not optional.** Every session must
ensure z3 is available before doing any F\* work. Without z3, extraction and
verification will fail.

```bash
# Check if z3 is available:
z3 --version  # must show 4.13.3

# If z3 is missing, install the pre-built binary (opam build often fails):

# Linux x86-64:
cd /tmp
curl -sL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip" -o z3.zip
unzip -q z3.zip
cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/local/bin/z3-4.13.3
chmod +x /usr/local/bin/z3-4.13.3
ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3

# macOS arm64 (Apple Silicon):
cd /tmp
curl -sL "https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-osx-13.7.zip" -o z3.zip
unzip -q z3.zip
cp z3-4.13.3-arm64-osx-13.7/bin/z3 /usr/local/bin/z3-4.13.3
chmod +x /usr/local/bin/z3-4.13.3
ln -sf /usr/local/bin/z3-4.13.3 /usr/local/bin/z3

# macOS alternative (may not get exact version):
brew install z3

# Verify it works:
z3-4.13.3 --version  # must show "Z3 version 4.13.3"
```

**Do NOT use `--lax` at all.** All F\* modules must verify and extract without
`--lax`. The `--lax` flag is banned — it defeats the purpose of formal
verification. Install z3 first, then verify and extract.


### Quick verification

```bash
eval $(opam env --switch=fstar)
cd formal/fstar

# Verify F* specs
make verify

# Extract + compile + test
./build-ocaml.sh

# Run W3C tests (w3c_runner is built by build-ocaml.sh)
cd ocaml-output
./w3c_runner                    # all SPARQL suites
./w3c_runner --rdf              # RDF parser suites
./w3c_runner --all              # both
./w3c_runner --list             # list suites
./w3c_runner bind functions     # specific suites
./w3c_runner -v aggregates      # verbose: full expected/actual dump on stderr
```

**Failure output**: FAIL lines always show UNMATCHED expected rows inline.
Use `-v` for the full expected/actual row dump (goes to stderr).

### Extraction notes

- **Never use `--lax`** — all modules must verify before extraction
- `--codegen OCaml` erases proofs, ghost code, spec-only material
- Extracted `.ml` files use `FStar_*` runtime from `fstar.lib` opam package
- `assume val` declarations extract as `failwith "Not yet implemented"` — must be patched
- `noeq` types block KaRaMeL C extraction (OCaml extraction works fine)

### W3C Test Suites

```
tests/w3c/                          git submodule: github.com/w3c/rdf-tests
  rdf/rdf11/rdf-n-triples/         N-Triples syntax tests (70)
  rdf/rdf11/rdf-turtle/            Turtle syntax+eval tests (313)
  rdf/rdf11/rdf-n-quads/           N-Quads syntax tests (87)
  rdf/rdf11/rdf-trig/              TriG syntax+eval tests (356)
  rdf/rdf11/rdf-xml/               RDF/XML eval tests (166)
  rdf/rdf11/rdf-mt/                Model theory / semantics (39)
  sparql/sparql11/                 SPARQL 1.1 test suites (34 suites, 631 tests)
```

## Key Dependencies

- `fstar` — F\* compiler (opam, 2025.12.15)
- `z3` — SMT solver (required by F\*)
- `fstar.lib` — F\* OCaml runtime library (opam)
- `str` — OCaml regex library (for regex_match stub)
- `zarith` — arbitrary-precision integers (F\* extracts `Prims.int` as `Z.t`)
- `js_of_ocaml` — OCaml to JavaScript compiler (optional)
- `zarith_stubs_js` — bigint stubs for js_of_ocaml (optional)
- `libgmp-dev` — system package required by zarith (apt-get)

## GitHub CLI (`gh`) in Claude Code

The git remote uses a local proxy (`127.0.0.1`), so `gh` commands that infer
the repo from the remote will fail with "none of the git remotes configured
for this repository point to a known GitHub host." **Fix: always pass
`--repo danbri/factoidal` explicitly.**

```bash
# These work:
gh pr create --repo danbri/factoidal --base claude/main --head my-branch ...
gh pr list --repo danbri/factoidal
gh pr view 42 --repo danbri/factoidal

# This does NOT work (no --repo):
gh pr create --base claude/main ...  # ERROR: unknown host
```

## Expanded Docs

The three sections below used to live in this file; they grew too long to
load into every session's context. They're now separate:

- [`docs/claude-rules/anti-patterns.md`](docs/claude-rules/anti-patterns.md)
  — full text of the 25 numbered anti-pattern rules summarised above.
- [`docs/claude-rules/performance.md`](docs/claude-rules/performance.md)
  — Known Performance Issues, esp. the Turtle parser audit + speed plan.
- [`docs/claude-rules/current-state.md`](docs/claude-rules/current-state.md)
  — Current State (Honest Assessment): F\* inventory, `assume val` table,
  verification gaps, W3C suite scores, phased plan.

See also [`docs/claude-rules/README.md`](docs/claude-rules/README.md) for
an index and for the relationship between this file and the expanded docs.

## Repository Structure

```
factoidal/
├── formal/fstar/              THE PRODUCT
│   ├── RDF.Graph.Executable.fst   RDF graph types + operations
│   ├── SPARQL11.Algebra.fst       SPARQL 1.1 algebra + evaluator
│   ├── SPARQL11.Parser.fst        SPARQL parser (in development)
│   ├── Parser.*.fst               RDF format parsers (combinators, Turtle, etc.)
│   ├── Makefile
│   ├── build-ocaml.sh
│   ├── ocaml-patches.sh               applies patches from glue directory
│   ├── minimal_regrettable_glue_code_each_with_an_open_issue/
│   │   ├── 53_blank_node_variable_rewriting.sh
│   │   ├── 62_forward_ref_wiring.sh
│   │   ├── 63_regex_hash_uuid_stubs.sh
│   │   ├── 64_sparql_parser_escape_stubs.sh
│   │   ├── 65_base_iri_resolution.sh
│   │   ├── 66_zero_length_property_path.sh
│   │   ├── 67_rdfxml_validation.sh
│   │   ├── 68_unicode_boundary_workarounds.sh
│   │   └── 69_runner_io_glue.sh
│   └── ocaml-output/          extracted .ml + symlinks to bin/<platform>/
├── bin/                       pre-built binaries per platform
│   ├── darwin-arm64/          macOS Apple Silicon
│   │   ├── factoidal
│   │   └── w3c_runner
│   └── linux-x86_64/         Linux x86-64 (statically linked)
│       ├── factoidal
│       └── w3c_runner
├── tests/w3c/                 git submodule (W3C test files)
├── kgx/                       SPARQL CONSTRUCT queries (future)
├── docs/
│   ├── claude-rules/          expanded Claude rules (anti-patterns, perf, state)
│   ├── designissues/          architecture docs
│   └── skills/                operational knowledge
├── junk/do_not_use/           vibe-coded artifacts (DO NOT USE)
└── CLAUDE.md                  this file
```
