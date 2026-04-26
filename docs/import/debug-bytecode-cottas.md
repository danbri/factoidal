# Debugging SPARQL over COTTAS with `ocamldebug`

This note documents the current low-friction path for:

- building a separate bytecode debug target
- materialising an on-disk COTTAS artifact from RDF
- inspecting artifact stats
- running the planner/explain path over that artifact
- launching `ocamldebug` against the CLI query path

The normal `build-ocaml.sh` flow is intentionally untouched.

## Quick start

Build the debug bytecode target:

```bash
cd formal/fstar
./build-ocaml-debug.sh factoidal
```

or via the helper:

```bash
tools/factoidal-debug-query.sh build-debug
```

Build the standalone fallback Factoidal RDF serializer:

```bash
tools/factoidal-debug-query.sh build-serializer
```

Create a COTTAS corpus from RDF using the current corpus-pipeline tooling:

```bash
tools/factoidal-debug-query.sh import-cottas \
  --input third_party/data/ukparliament/ukparliament-rdf-2019-07-27.trig \
  --corpus-root tmp/ukparliament-debug/CorpusCOTTAS \
  --dataset-name ukparliament-2019 \
  --chunk-name ukparliament-2019 \
  --parser factoidal
```

Parser modes:

- `--parser factoidal`: use `factoidal dump-nq` from the main binary, or the standalone fallback serializer if the main binary is unavailable
- `--parser auto`: try Factoidal first, then fall back to Python parsers
- `--parser python`: prefer `pyoxigraph`, fall back to `rdflib`
- `--parser pyoxigraph` / `--parser rdflib`: force a specific Python parser

The current default is `--parser factoidal`.

Resolve the resulting `data.cottas` path:

```bash
tools/factoidal-debug-query.sh cottas-path \
  --corpus-root tmp/ukparliament-debug/CorpusCOTTAS \
  --chunk-name ukparliament-2019
```

Inspect the artifact:

```bash
tools/factoidal-debug-query.sh cottas-info \
  tmp/ukparliament-debug/CorpusCOTTAS/ukparliament-2019/v1/data.cottas
```

## Planner / explain path

The current planner-only surface is:

```bash
./bin/darwin-arm64/factoidal \
  --data-cottas tmp/ukparliament-debug/CorpusCOTTAS/ukparliament-2019/v1/data.cottas \
  --explain-only \
  --query tools/sample-queries/ukparliament/detail/procedures_Xi2z3U8E_overview_01_modern.rq
```

Equivalent helper form:

```bash
tools/factoidal-debug-query.sh explain \
  --data-cottas tmp/ukparliament-debug/CorpusCOTTAS/ukparliament-2019/v1/data.cottas \
  --query tools/sample-queries/ukparliament/detail/procedures_Xi2z3U8E_overview_01_modern.rq
```

This path uses `factoidal_explain.ml` and reports:

- parsed algebra in a custom human-readable tree
- per-triple-pattern estimates
- dictionary hit/miss information
- join-order choices derived from the current planner

Important: this is the path that actually reasons against the on-disk
COTTAS store today.

## `ocamldebug` path

Launch the bytecode CLI with an initial breakpoint:

```bash
tools/factoidal-debug-query.sh debug \
  --data-cottas tmp/ukparliament-debug/CorpusCOTTAS/ukparliament-2019/v1/data.cottas \
  --query tools/sample-queries/ukparliament/detail/procedures_Xi2z3U8E_overview_01_modern.rq \
  --break Factoidal_cli:950
```

The helper:

- ensures `bin/<platform>/factoidal.byte` exists
- opens `~/.opam/fstar/bin/ocamldebug`
- sets the CLI arguments
- installs one initial breakpoint
- starts the program

Useful debugger commands:

```text
where
print query_text
step
backstep
reverse
```

## Current caveat: exact path coverage

For `SELECT` and `ASK` with `--data-cottas`, `factoidal.byte` now goes
through the same `SPARQL11_Store` / `GB_CottasOnDisk` execution path as
the production disk-backed backend.

That means:

- planner introspection is truly on-disk
- bytecode step-debugging of `SELECT` / `ASK` over COTTAS is now against
  the same on-disk backend family as production

Remaining caveats:

- `CONSTRUCT` still falls back to the eager in-memory query path
- enabling entailment closure also falls back to the eager path
- the HTTP daemon/request loop is still deliberately outside the default
  reversible-debug workflow

## Do we have ARQ-style SSE today?

Partly.

There is an SSE-style algebra printer in F* source:

- [`formal/fstar/SPARQL11.Parser.fst`](../../formal/fstar/SPARQL11.Parser.fst)

The relevant section starts at the comment:

- `Part 8: SSE-style Algebra Printer`

However, this printer is not currently exposed through the CLI. The
current `--explain` output is a custom readable tree from
`factoidal_explain.ml`, not ARQ-style SSE.

So the current state is:

- **yes**: algebra/planner introspection exists now
- **yes**: an SSE printer exists in F* source
- **no**: there is not yet a user-facing `--algebra-sse` / `--explain-sse`
  CLI surface

## Recommended workflow

For planner issues:

1. Create or reuse a `data.cottas`
2. Run `tools/factoidal-debug-query.sh explain ...`
3. Inspect estimates and join order

For evaluator issues:

1. Build `factoidal.byte`
2. Launch `tools/factoidal-debug-query.sh debug ...`
3. Break in `Factoidal_cli`, `SPARQL11_Parser`, or evaluator code
4. Step forward/backward with `ocamldebug`

For daemon/request-loop issues:

- use the native server and native debuggers/sampling tools
- do not make the HTTP server the default reversible-debug target
The helper prefers:

1. `FACTOIDAL_PYTHON` if set
2. `tmp/pycottas-venv/bin/python` if present
3. `python3`

This avoids depending on the native CLI shim's hard-coded `python3`
when the repo already has a better-pinned import environment.

For `--parser factoidal`, the helper and `corpus_pipeline.py` will use:

1. `FACTOIDAL_BIN` if set
2. `bin/<platform>/factoidal` in this repo
3. `bin/<platform>/factoidal-dump-nq` fallback
4. `factoidal` from `PATH`
