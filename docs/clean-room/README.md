# Clean-room reproducibility runs

Dated artifacts from `tools/clean-room-build.sh`. Each one records a cold
rebuild of the whole tree from a bare clone — no F\* `.checked` files, no
extracted `.ml`, no committed `bin/<platform>/` binaries, no
incremental-extract manifest — followed by a run of every advertised
conformance suite.

Filed against [#314](https://github.com/danbri/factoidal/issues/314),
review gate 1 of the 2026-07-29 external review
([#313](https://github.com/danbri/factoidal/issues/313)).

## Why the series exists

Every score this project publishes comes from a tree that has accumulated
build state. Iron rule #9 commits binaries deliberately; `.checked` files
and the extraction manifest accumulate as a side effect. None of that is
wrong, but it means "the suites pass" had an unstated dependency on our
own build state until someone demonstrated otherwise. These artifacts are
that demonstration, repeated.

## Reading an artifact

Each file carries four blocks:

- **Provenance** — commit, F\* / z3 / OCaml versions, host, and whether
  test fixtures were restored from submodules or copied from an existing
  checkout. Fixtures are test *inputs*; copying them does not weaken the
  claim, and the artifact says which mode was used.
- **Purge** — how many `.checked` files, extracted `.ml` and binaries were
  deleted before building. If these counts are zero, the run is not cold
  and the numbers below it mean nothing. The script asserts this rather
  than trusting it.
- **Timings** — per phase, with exit codes.
- **Scores** — the `docs/test-results/latest.json` the cold tree produced.
  Any delta against the dashboard is explained in prose beneath it.

## Running one

```bash
eval $(opam env --switch=fstar)          # iron rule #12
tools/clean-room-build.sh --workdir /some/scratch/dir
```

It is expensive. Background it, log it, and cap it (anti-patterns #19,
#20). `--skip-suites` gives just the build. `--help` lists the rest.

The weekly CI job is `.github/workflows/clean-room-build.yml`; it is
scheduled rather than per-PR, and deliberately does **not** cache F\*'s
`.checked` files.

## What the first runs found

The exercise was expected to surface drift, and did:

- Five modules — `CSVW.Json`, `CSVW.Validate`, `Math.Sigmoid`,
  `SHACL.NodeExpr`, `SHACL.Rules` — are referenced by `build-ocaml.sh`'s
  `COMMON_MODULES` compile list but their extracted `.ml` is **not
  committed**. A cold build regenerates them, so the tree self-heals; a
  `./build-ocaml.sh compile` from a fresh clone without extracting first
  does not. This is the anti-pattern #27 shape.
- `formal/fstar/ocaml-output/` mixes generated output with four
  hand-written rule-#11 realisations (`fstar_pure_hashes.ml`,
  `fstar_hacl_crypto.ml`, `service_wrap_hook.ml`, `service_wrap_http.ml`).
  Only the first is on the allowlist in
  `.github/workflows/check-ocaml-output-cleanliness.yml`, and that check's
  "generated files start with `open Prims`" heuristic also misfires on
  `RDF_Graph_Executable.ml`, which a patch script rewrites to start with
  `include` lines.
- The incremental-extract manifest is **tracked in git** despite
  `.gitignore` calling it "local build-cache state, not a committed
  artifact" — which is what made
  [#320](https://github.com/danbri/factoidal/issues/320)'s soundness gap
  repo-wide rather than dev-loop-only.
