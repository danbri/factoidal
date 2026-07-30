# Factoidal

An RDF/SPARQL implementation specified in F\* and extracted to OCaml
(and JS/wasm/C) for execution. The F\* specifications are the product —
executable code is obtained by extraction, not by hand-writing
implementations.

**What "verified" means here — three rings.** Claims differ by layer,
and the boundary matters more than the headline:

1. **Proved core.** The RDF term/graph algebra, the SPARQL algebra and
   evaluator, the SPARQL 1.1 query/UPDATE parser, the RDF format
   parsers, and most of the ~170 F\* modules verify fully under
   Z3 4.13.3 — no `--lax`, no `--admit_smt_queries`, zero `admit()`.
   What these modules state, Z3 checked. (`SPARQL11.Parser.fst`
   formerly admitted the SMT obligations for 119 of its definitions in
   two pragma regions; those obligations are discharged as of
   2026-07-10.)
2. **Tested extracted implementation.** One carve-out: every
   `assume val` (I/O, host regex, crypto) is realised by audited
   OCaml/HACL\* glue, catalogued with an open issue each. This ring is
   *tested* like ordinary good software, not proved.
3. **Experimental extensions.** The wider semantic-platform surface —
   OWL/SHACL/ShEx/JSON-LD/RIF/RML engines, XSLT/XML/Schematron/MathML,
   the COTTAS on-disk store, browser/wasm/C targets — is F\*-first and
   suite-measured, at per-suite completeness levels the live dashboard
   reports.

Status: work in progress. The W3C SPARQL 1.1 + RDF 1.1 runnable suites
pass in full (see the dashboard). The Turtle path parses ~100k
triples/second with near-linear scaling (1M triples in ~10s, measured
2026-07-03 on the committed linux-x86_64 binary). The compliant engine
is the **in-memory** one (1M quads: ~41s end-to-end, ~1.2 GB RAM —
RAM-bound at ~1.2 KB/quad). The **on-disk** store (COTTAS —
Parquet-backed quads; ~3.1M quads behind the
[UK Parliament demo](https://danbri.github.io/factoidal/web/demos/ukparliament/))
runs its production query path through F\*-extracted token-direct entry
points (since 2026-07-06); the remaining hand-written OCaml
optimization glue has zero production callers and is pending deletion
(issue #118; row-by-row state in
`docs/designissues/fstar-ocaml-boundary-audit.md`). Standing qualifier:
parser and algebra spec verified in F\* (ring-2 caveats above); on-disk
backend still carries that glue until #118 completes.

**[Live W3C test results](https://danbri.github.io/factoidal/test-results/)**

## Quick Start

```bash
# Install prerequisites
# Debian/Ubuntu:
sudo apt-get install -y opam libgmp-dev pkg-config
# macOS (Homebrew):
brew install opam gmp pkg-config

# Set up OCaml + F* toolchain (first time only)
opam init -y
opam switch create fstar ocaml-base-compiler.4.14.1
eval $(opam env --switch=fstar)
opam install fstar z3 zarith sha digestif

# Clone with W3C test data
git clone --recurse-submodules https://github.com/danbri/factoidal.git
cd factoidal

# Already cloned without submodules? The test runners need these two
# (without them they report zero tests):
git submodule update --init third_party/testing/w3c third_party/testing/rdf-canon

# Build everything (verify F* → extract OCaml → compile)
cd formal/fstar
eval $(opam env --switch=fstar)
./build-ocaml.sh

# The factoidal CLI is now at:
./ocaml-output/factoidal --help

# e.g. usage
alias factoidal=`pwd`/formal/fstar/ocaml-output/factoidal

```

## The `factoidal` Command-Line Tool

A SPARQL query and RDF parsing tool — similar to Apache Jena's `arq` or
Rasqal's `roqet`, but backed by formally verified F\* code.

### SPARQL queries

```bash
# Query a Turtle file
factoidal --data data.ttl -e 'SELECT * WHERE { ?s ?p ?o }'

# Query with prefixes
factoidal -d data.ttl -e '
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?person ?name
  WHERE { ?person foaf:name ?name }
'

# Query from a file
factoidal --data data.ttl --query query.rq

# Multiple data files
factoidal -d file1.ttl -d file2.nt --query query.rq

# Pipe data via stdin
cat data.ttl | factoidal -d - -e 'SELECT ...'

# Named graphs
factoidal -d default.ttl -n http://example.org/g1=g1.ttl --query query.rq

# CSV output
factoidal -d data.ttl -e 'SELECT ?s ?p ?o WHERE { ?s ?p ?o }' -o csv
```

### N-Quads and named graphs

N-Quads (`.nq`) and TriG (`.trig`) files contain named graphs. Use `GRAPH`
patterns to query them:

```bash
# Query named graphs in an N-Quads file
factoidal --data data.nq -e 'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }'

# Query a specific named graph
factoidal -d data.nq -e '
  SELECT ?s ?p ?o
  WHERE { GRAPH <http://example.org/graph1> { ?s ?p ?o } }
'

# Without GRAPH, only the default graph is queried
factoidal -d data.nq -e 'SELECT * WHERE { ?s ?p ?o }'

# Count triples across all graphs
factoidal --count data.nq

# Dump all quads as N-Triples (flattened)
factoidal --dump data.nq

# TriG files work the same way
factoidal -d data.trig -e 'SELECT ?g ?s WHERE { GRAPH ?g { ?s ?p ?o } } LIMIT 10'
```

### RDF parsing and conversion

```bash
# Parse Turtle and dump as N-Triples (format conversion)
factoidal --dump data.ttl

# Count triples in a file
factoidal --count data.ttl

# Parse RDF/XML
factoidal --dump --format rdfxml data.rdf

# Parse with explicit base IRI
factoidal --dump --base http://example.org/ data.ttl
```

### Piping data from the web

Factoidal reads stdin when you pass `-d -`, so you can pipe RDF from any
HTTP client. Use `--format` to specify the format (stdin has no file
extension; the default is Turtle).

#### Unix (curl)

```bash
# Fetch Turtle from DBpedia and query it
curl -sL "http://dbpedia.org/data/Berlin.ttl" \
  | factoidal -d - -e 'PREFIX dbo: <http://dbpedia.org/ontology/>
    SELECT ?pop WHERE { ?s dbo:populationTotal ?pop }'

# Content negotiation — ask for N-Triples via Accept header
curl -sL -H "Accept: application/n-triples" \
  "http://dbpedia.org/resource/Berlin" \
  | factoidal -d - --format ntriples -e 'SELECT * WHERE { ?s ?p ?o } LIMIT 10'

# Fetch RDF/XML and count triples
curl -sL -H "Accept: application/rdf+xml" \
  "http://dbpedia.org/resource/Berlin" \
  | factoidal -d - --format rdfxml --count
```

#### Unix (wget)

```bash
wget -qO- "http://dbpedia.org/data/Berlin.ttl" \
  | factoidal -d - -e 'SELECT * WHERE { ?s ?p ?o } LIMIT 5'
```

#### Windows (PowerShell — Invoke-WebRequest)

```powershell
# PowerShell's Invoke-WebRequest (aliased as iwr/curl on Windows — not the
# same as Unix curl). Pipe RDF into factoidal via stdin.
(Invoke-WebRequest -Uri "http://dbpedia.org/data/Berlin.ttl").Content `
  | factoidal -d - -e "SELECT * WHERE { ?s ?p ?o } LIMIT 5"

# Content negotiation with Accept header
(Invoke-WebRequest -Uri "http://dbpedia.org/resource/Berlin" `
  -Headers @{"Accept"="application/n-triples"}).Content `
  | factoidal -d - --format ntriples -e "SELECT * WHERE { ?s ?p ?o } LIMIT 10"
```

> **Note for Windows users:** PowerShell aliases `curl` to `Invoke-WebRequest`,
> which is unrelated to Unix curl. If you have the real curl installed (Windows
> 10+ ships `curl.exe` in System32), use `curl.exe` explicitly to avoid the
> alias:
>
> ```powershell
> curl.exe -sL "http://dbpedia.org/data/Berlin.ttl" `
>   | factoidal -d - -e "SELECT * WHERE { ?s ?p ?o } LIMIT 5"
> ```

#### Windows (cmd.exe — curl.exe)

```cmd
curl.exe -sL "http://dbpedia.org/data/Berlin.ttl" | factoidal -d - -e "SELECT * WHERE { ?s ?p ?o } LIMIT 5"
```

### Example session

```
$ cat people.ttl
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex:   <http://example.org/> .

ex:alice foaf:name "Alice" ;
         foaf:knows ex:bob .
ex:bob   foaf:name "Bob" ;
         foaf:age 30 .

$ factoidal -d people.ttl -e 'PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?person ?name WHERE { ?person foaf:name ?name }'
+----------------------------+---------+
| ?person                    | ?name   |
+----------------------------+---------+
| <http://example.org/alice> | "Alice" |
| <http://example.org/bob>   | "Bob"   |
+----------------------------+---------+
2 result(s)

$ factoidal -d people.ttl -e 'SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }'
+-------------------------------------------------+
| ?c                                              |
+-------------------------------------------------+
| "4"^^<http://www.w3.org/2001/XMLSchema#integer> |
+-------------------------------------------------+
1 result(s)
```

### Full CLI reference

```
factoidal — formally verified SPARQL query tool

SPARQL query:
  factoidal --data FILE --query FILE.rq
  factoidal --data FILE -e 'SELECT * WHERE { ?s ?p ?o }'
  factoidal -d file1.ttl -d file2.nt --query q.rq
  cat data.ttl | factoidal -d - -e 'SELECT ...'

Named graphs (N-Quads / TriG):
  factoidal -d data.nq -e 'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }'
  factoidal -d data.trig -e 'SELECT ?g ?s WHERE { GRAPH ?g { ?s ?p ?o } }'
  factoidal -d data.nq -e 'SELECT * WHERE { ?s ?p ?o }'  (default graph only)

RDF parsing/dump:
  factoidal --dump FILE.ttl           Parse and dump as N-Triples
  factoidal --count FILE.ttl          Count triples
  factoidal --dump --format rdfxml FILE.rdf

Options:
  -d, --data FILE        Load RDF data (repeatable, "-" for stdin)
                         Format auto-detected: .ttl .nt .nq .trig .rdf .xml .owl
  -n, --named IRI=FILE   Load named graph
  -q, --query FILE       SPARQL query file
  -e SPARQL              Inline SPARQL query string
  -b, --base IRI         Base IRI for parsing
  -f, --format FMT       Input format: turtle, ntriples, nquads, trig, rdfxml
  -o, --output FMT       Output format: table (default), csv, ntriples
  --dump                 Parse RDF and dump as N-Triples
  --count                Parse RDF and count triples
  --version              Show version
  --help                 This help

Supported RDF formats:  Turtle (.ttl), N-Triples (.nt), N-Quads (.nq),
                        TriG (.trig), RDF/XML (.rdf, .xml, .owl)
Supported query forms:  SELECT, ASK, CONSTRUCT

N-Quads and TriG files preserve named graph structure. Use GRAPH patterns
in SPARQL to query specific graphs.
```

## Supported SPARQL Features

SELECT, ASK, CONSTRUCT, PREFIX, BASE, FILTER, OPTIONAL, UNION, MINUS,
BIND, VALUES, EXISTS/NOT EXISTS, DISTINCT, REDUCED, ORDER BY, LIMIT,
OFFSET, GROUP BY, HAVING, aggregates (COUNT, SUM, AVG, MIN, MAX,
GROUP_CONCAT, SAMPLE), subqueries, property paths, and 30+ built-in
functions.

## Building from Source

### Prerequisites

| Dependency | Purpose | Install (Linux) | Install (macOS) |
|-----------|---------|-----------------|-----------------|
| opam | OCaml package manager | `apt-get install opam` | `brew install opam` |
| gmp | Arbitrary-precision integers | `apt-get install libgmp-dev` | `brew install gmp` |
| pkg-config | Build tool | `apt-get install pkg-config` | `brew install pkg-config` |
| F\* (fstar) | Verified compiler | `opam install fstar` | `opam install fstar` |
| z3 | SMT solver (F\* uses it) | `opam install z3` or [binary release](https://github.com/Z3Prover/z3/releases) | `brew install z3` or [binary release](https://github.com/Z3Prover/z3/releases) |
| zarith | OCaml bigint library | `opam install zarith` | `opam install zarith` |
| sha, digestif | Hash functions (MD5/SHA) | `opam install sha digestif` | `opam install sha digestif` |
| js_of_ocaml, zarith_stubs_js | JavaScript extraction (optional) | `opam install js_of_ocaml zarith_stubs_js` | same |
| wasm_of_ocaml-compiler, binaryen | WebAssembly extraction (optional) | `apt-get install binaryen && opam install wasm_of_ocaml-compiler` | `brew install binaryen && opam install wasm_of_ocaml-compiler` |
| Rust toolchain (cargo, rustc) | Build the F\* MCP server (optional, agent-side only) | `apt-get install cargo` or `curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \| sh` | `brew install rust` or rustup |

The Rust toolchain is **optional** and agent-side: the project ships a
project-scoped MCP server config (`.mcp.json`) pointing at
`http://127.0.0.1:3700`, where the [FStarLang/fstar-mcp](https://github.com/FStarLang/fstar-mcp)
daemon runs and bridges F\*'s `--ide` protocol over MCP Streamable
HTTP. Sandboxed agent sessions install the binary and start the
daemon automatically via `tools/sandbox-bootstrap.sh` (invoked from
`.claude/hooks/session-start.sh` under Claude Code; other agent
harnesses can call the same script from their own session-start
hook). Local contributors do `cargo install --locked --git https://github.com/FStarLang/fstar-mcp.git && tools/fstar-mcp-server.sh start`
once. Without it, F\* still verifies / extracts / runs normally —
the MCP only changes the agent's diagnostic loop.

### Build steps

```bash
# Activate the F* opam switch
eval $(opam env --switch=fstar)
cd formal/fstar

# Full pipeline: verify F* → extract OCaml → compile → test
./build-ocaml.sh

# Or run individual steps:
./build-ocaml.sh extract   # F* extraction only
./build-ocaml.sh compile   # compile OCaml only (skip extraction)
./build-ocaml.sh test      # run W3C tests only
```

The build produces two binaries in `bin/<platform>/` (e.g., `bin/darwin-arm64/`
or `bin/linux-x86_64/`), with symlinks in `formal/fstar/ocaml-output/`:
- `factoidal` — the CLI query/parsing tool
- `w3c_runner` — the W3C conformance test runner

### Verify F\* specifications

```bash
cd formal/fstar
make verify                  # whole corpus; hours from cold, seconds warm
make -j$(nproc) verify       # same, parallel over the dependency DAG
make verify-smoke            # six core modules only; fast sanity check
make verify-RDF.Canonical    # one module
```

`make verify` type-checks every `.fst` in `formal/fstar/` against the SMT
solver — the target derives its module list from the directory, so it
cannot drift from the corpus.

⚠️ **Current status: 189 of 190 modules verify clean; `make verify` exits
nonzero.** The single failure is
`RDF.CottasStore.PageCache.Bounds.fst` — an orphaned proof-only module
that is referenced by nothing, is in no build list, and so was verified by
nothing until this target started covering the corpus. Its lemma
statements still say `v:list (option string)` where `page_cache` now uses
the abstract `cottas_column` type, so it no longer type-checks. Nothing
extracts or links it, so no shipped binary is affected. Tracked
separately; do not read this as the engine failing to verify, and do not
claim `make verify` is green until it is fixed. Read the claim precisely: **what these
modules state, Z3 checked.** For most modules that means totality,
termination and refinement types plus whatever local lemmas the module
declares; it is not a proof that the module implements the W3C
Recommendation it is named after. Standards behaviour is measured by the
conformance suites below, not by this command. (Until 2026-07-29 this
target checked six modules by hand while this paragraph claimed all of
them — [#319](https://github.com/danbri/factoidal/issues/319).)

The RDF graph
and SPARQL algebra modules are fully verified — zero `admit()` anywhere
in the F\* source (the 4 SPARQL proof-lemma admits an earlier README
disclosed have since been eliminated). `SPARQL11.Parser.fst` is now in
the same state: the two `#push-options "--admit_smt_queries true"`
regions that used to cover its mutually-recursive expression and
UPDATE parser blocks (119 of 233 definitions) were removed on
2026-07-10 — the whole file verifies under Z3 4.13.3 with no `--lax`
and no admitted obligations. See [CLAUDE.md](CLAUDE.md).

### Run W3C conformance tests

```bash
cd formal/fstar/ocaml-output
./w3c_runner                    # all SPARQL 1.1 suites
./w3c_runner --rdf              # all RDF 1.1 suites
./w3c_runner --all              # both
./w3c_runner --list             # list available suites
./w3c_runner bind functions     # specific suites
./w3c_runner -v aggregates      # verbose mode
```

## Project Structure

```
factoidal/
├── formal/fstar/                  THE PRODUCT
│   ├── RDF.Graph.Executable.fst   RDF graph types + operations (1052 lines)
│   ├── SPARQL11.Algebra.fst       SPARQL 1.1 algebra + evaluator (3783 lines)
│   ├── SPARQL11.Parser.fst        SPARQL parser (2942 lines)
│   ├── Parser.*.fst               RDF format parsers (13 modules, ~6k lines)
│   ├── Makefile                   verify + extract targets
│   ├── build-ocaml.sh            F* → OCaml → binary pipeline
│   ├── ocaml-patches.sh          wires assume-val stubs
│   └── ocaml-output/             extracted OCaml + symlinks to bin/
│       ├── factoidal_cli.ml       CLI tool source (I/O glue)
│       ├── w3c_runner.ml          W3C test runner (I/O glue)
│       └── *.ml                   F*-extracted OCaml modules
├── bin/                           pre-built binaries per platform
│   ├── darwin-arm64/              macOS Apple Silicon
│   └── linux-x86_64/             Linux x86-64 (statically linked)
├── third_party/testing/w3c/                    git submodule (W3C test files)
└── CLAUDE.md                     development instructions
```

## W3C Conformance Status

Live, per-suite numbers: **[test-results dashboard](https://danbri.github.io/factoidal/test-results/)**
(regenerated by CI on every push; machine-readable at
`docs/test-results/latest.json`).

SPARQL 1.1 suites: 631 pass, 0 fail; RDF 1.1 parsing + model-theory
suites: 1031 pass, 0 fail — 1662 of 1662 runnable tests. The dashboard
carries every scored suite (OWL, RDFC-1.0, SHACL, ShEx validation +
ShEx negativeSyntax, JSON-LD, RML, RIF, VC, XSLT, XML conformance,
MathML, JSON Schema, Schematron, CSVW, DID, HDT parity, and the
browser-bundle/npm JS suites — 30+ rows), each with labelled
pass/fail/skip — prefer those live numbers to anything frozen in this
file. Caveats that apply to scores (ASK boolean comparison, lenient
blank-node matching, the SPARQL-parser admitted regions above) are
catalogued in
[`docs/claude-rules/current-state.md`](docs/claude-rules/current-state.md).

## Browser / Node builds

The same F\* source is extracted once and compiled for three runtimes:

| Target | Where | Toolchain | Status |
|---|---|---|---|
| Native | `bin/<platform>/` | `ocamlfind ocamlc` | full W3C pass counts |
| JavaScript | `docs/fstar-extracted/w3c-runner.js` | js_of_ocaml | runs in any browser or Node |
| WebAssembly | `docs/fstar-extracted/w3c-runner.wasm.js` + `.wasm.assets/` | wasm_of_ocaml | needs Wasm-GC (Chrome ≥ 119, Node ≥ 22); 17/18 SPARQL suites reproduce native |

```bash
cd formal/fstar
./build-ocaml.sh           # native + JS
./build-ocaml.sh wasm      # WebAssembly (needs wasm_of_ocaml-compiler + binaryen)
```

Try the wasm build from Node:

```bash
cd docs/fstar-extracted
node w3c-runner.wasm.js bind    # 10/10 pass, identical to native
```

Both browser artifacts are rebuilt by CI on every push and served from the
[GitHub Pages site](https://danbri.github.io/factoidal/fstar-extracted/).

The Wasm build links a vendored copy of
[zarith\_stubs\_js](https://github.com/janestreet/zarith_stubs_js)'s
`runtime.wat` + `runtime_wasm.js` (bridges `ml_z_*` via JavaScript BigInt).
The `functions` SPARQL suite currently crashes under Wasm because the
MD5/SHA builtins go through `stub_sha*`/`caml_digestif_*` C stubs that don't
yet have equivalent Wasm bindings.

## Architecture

```
F* formal spec (the product)
    │
    ▼
fstar.exe --codegen OCaml (extraction, proof-erased)
    │
    ├── ocamlfind ocamlc  → bin/<platform>/{factoidal, w3c_runner}  (native)
    ├── js_of_ocaml       → docs/fstar-extracted/w3c-runner.js
    └── wasm_of_ocaml     → docs/fstar-extracted/w3c-runner.wasm.{js,assets/}
```

All RDF parsing, SPARQL parsing, and query evaluation is performed by
F\*-extracted code. The CLI tools are thin I/O wrappers — they read files,
call the extracted functions, and format the output.

## License

Apache License 2.0 — see [LICENSE](LICENSE) for details.
