# tests/unit — Factoidal's own unit-test suite

This directory holds unit tests authored specifically for Factoidal. It is
distinct from `tests/w3c/`, which is a git submodule tracking the upstream
W3C RDF / SPARQL conformance test suites.

## What goes here

Tests that exercise things the W3C suites do not usefully cover:

- UTF-8 byte-level round-trip through parsers and output serialisers.
- CLI / demo-driver invariants (prefix handling, JSON formatting,
  exit codes, error surfacing).
- Documented limitations of the current implementation (e.g., `Str`
  regex byte-vs-codepoint, ASCII-only `UCASE`/`LCASE`) that are
  codified as either passing-or-deliberately-failing assertions so
  future regressions have a place to land and future fixes have a
  unit-level guardrail.
- Byte-level contracts of shared helpers (e.g., `Parser.FastString`)
  that callers rely on but that aren't part of any W3C spec.

## Layout

Each `*.ml` file is a **self-contained test binary**. It compiles against the
already-extracted F\* modules in `formal/fstar/ocaml-output/` (i.e., we do not
re-run extraction to run unit tests). It links its own `main`, runs a set of
named assertions, and prints one line per assertion plus a summary line at the
end. Exit code is `0` iff every assertion matched its expected outcome (PASS
or documented expected-FAIL).

`run-all.sh` discovers every `*.ml` next to it, builds each binary, runs it,
and reports per-file and overall pass/fail counts.

## Usage

```bash
cd tests/unit
./run-all.sh                          # run every test file
./run-all.sh utf8_roundtrip           # run a specific test (no .ml suffix)
```

Prerequisites:

- The F\* → OCaml pipeline has already been run (i.e.,
  `formal/fstar/ocaml-output/*.cmx` exist). The easiest way is
  `cd formal/fstar && ./build-ocaml.sh extract compile`, but if you
  are iterating on unit tests alone, the pre-built `.cmx` files
  committed alongside the platform binaries are sufficient.
- `opam env --switch=fstar` is active, so `ocamlfind`, `zarith`,
  `fstar.lib`, `str`, etc. are on the path.

## Relationship to other test runners

| Runner | What it tests | Where it lives |
|---|---|---|
| `tests/unit/run-all.sh` | Unit tests in this directory | here |
| `formal/fstar/ocaml-output/w3c_runner` | W3C conformance suites (SPARQL 1.1, RDF 1.1) | formal/fstar/ocaml-output/ |
| `tests/local/*.sh` | Ad-hoc regression scripts (COTTAS, SPARQL negative syntax, etc.) | tests/local/ |
| `tests/compat/` | Cross-version compatibility (RDF 1.2 drafts) | tests/compat/ |

The unit suite is **not** wired into `w3c_runner`; it is an independent
bench of invariant checks and is expected to run fast (under a second on
current hardware).

## Writing a new test file

Boilerplate:

```ocaml
(* Each file is a standalone OCaml test binary. No Alcotest, no
   OUnit — just let bindings and a small assertion helper, to keep
   the dependency footprint at exactly what the F* extraction already
   pulls in. *)

let passed = ref 0
let failed = ref 0
let expected_failures = ref 0

let check ~name ~expected_pass ok_bool =
  if ok_bool then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else if not expected_pass then begin
    incr expected_failures;
    Printf.printf "  XFAIL %s  (documented limitation)\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

let () =
  (* ...run assertions, each calling `check`... *)
  Printf.printf "summary: %d pass, %d expected-fail, %d unexpected fail\n"
    !passed !expected_failures !failed;
  if !failed > 0 then exit 1
```

Keep each file under ~150 lines. If it's getting bigger, split into
multiple files named by the behaviour they target
(e.g., `utf8_roundtrip_sparql.ml` vs `utf8_roundtrip_parse_only.ml`).

## Documenting known bugs

When an assertion deliberately fails, pass `~expected_pass:false` to
`check` and leave a short comment above the assertion pointing at the
relevant GitHub issue or anti-pattern number in `docs/claude-rules/`.
That way a reader can tell within seconds whether a failure is a new
regression or a documented limitation.

## Rule anchors

- Per CLAUDE.md rule #25: summary lines spell out "N pass, N fail"
  with full labels — no cryptic `X/Y/Z` strings.
- Per CLAUDE.md rule #16: `run-all.sh` does not truncate output; every
  assertion's line is visible, and the summary goes at the end.
- Per CLAUDE.md rule #14: `run-all.sh` captures exit codes instead of
  swallowing them with `|| true`.
