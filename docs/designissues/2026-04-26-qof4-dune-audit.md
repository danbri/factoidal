# Qof4 — dune-reference audit (2026-04-26)

## Scratch doc / watchdog pulse

User did `grep -Ri dune *` and found 4 docs that pretend dune is the build
system. **Factoidal does NOT use dune.** Build is `formal/fstar/build-ocaml.sh`,
which calls `ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix
-linkpkg -w -8-14-26 $COMMON_MODULES <entry>.ml -o $BINDIR/<exe>` directly. The
sole legitimate `dune` mention in the repo is a comment in `build-ocaml.sh:37`
about Jane Street's `zarith_stubs_js` `dune` stanza — that's referencing a
*third-party* package's build system, not ours.

## Files with false claims (to be edited by this audit)

- `docs/designissues/2026-04-26-tav5-sigbus-circuit-breaker.md:39`
  — "No `build-ocaml.sh extract`. `dune build factoidal_http.exe` only."
- `docs/designissues/2026-04-26-heth3-query-timeout.md:73`
  — "1. `dune build` (or `ocamlopt` per `build-ocaml.sh`) factoidal-http."
- `docs/designissues/2026-04-26-lamed3-predicate-offset-index.md:70`
  — "Rule #11: do **not** run `./build-ocaml.sh extract`. Patch + dune."
- `docs/designissues/debugging-perf-ecosystem.md` (8 occurrences)
  — Whole sub-section recommending `dune build *.bc` for bytecode +
    `(modes (native exe) (byte exe))` stanza that does not exist.

## Replacement strategy

- Where the intent was "compile-only, no extract": replace with
  `./build-ocaml.sh compile`.
- Where the intent was "rebuild a single target": there is no
  per-target make rule — the script always rebuilds w3c_runner,
  factoidal, factoidal-http, owl_runner, rdfc10_runner, cottas_ondisk_smoketest
  in one shot. Replace with `./build-ocaml.sh compile`.
- For the bytecode-debugging passage in `debugging-perf-ecosystem.md`:
  the script does build bytecode (`ocamlc` for `w3c_runner.byte` and
  `factoidal.byte`) but only inside the `js` step, and the resulting
  `.byte` files are intermediates en route to `js_of_ocaml`. There is no
  `factoidal_http.byte` target. Edit the doc to describe the actual
  shape (intermediate bytecode for js_of_ocaml; no `factoidal_http.byte`
  yet; adding one means an additional `ocamlfind ocamlc` invocation in
  `build-ocaml.sh compile`, NOT a dune stanza).

## Out of scope

- Adding a `dune-project`. (Separate large decision; not this audit.)
- Editing `build-ocaml.sh` or any other script.
- Editing source `.fst` / `.ml`.

This doc itself is the 5-minute pulse so the parent thread sees the
agent is alive before the file edits land.
