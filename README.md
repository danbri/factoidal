# Factoidal

A formally verified RDF/SPARQL implementation written in F\*, with
verified code extracted to OCaml for execution. The F\* specifications
are the product — executable code is obtained by extraction, not by
hand-writing implementations.

Status: I'm surprised it works at all. I have seen rdf/xml FOAF files parse in milliseconds, but Turtle DBpedia entries will take longer than heat death of the universe. Formal does not necessarily mean fast. Work in progress.

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
make verify    # requires z3
```

This type-checks all F\* modules against the SMT solver. The RDF graph and
SPARQL algebra modules are fully verified (0 admit in RDF, 4 admit in proof
lemmas for SPARQL). The SPARQL parser uses `--admit_smt_queries true` for
~65% of its mutually recursive functions — it type-checks but SMT proofs
are not fully discharged. See [CLAUDE.md](CLAUDE.md) for details.

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
├── tests/w3c/                    git submodule (W3C test files)
└── CLAUDE.md                     development instructions
```

## W3C Conformance Status

**SPARQL 1.1**: 379 pass / 38 fail / 205 skip (UPDATE) / 9 unsupported — 91% of applicable tests

Strong areas: aggregates (46/46), functions (74/75), bind (10/10), negation
(11/12), property paths (33/33), subqueries (12/14), project-expression (7/7),
exists (6/6), grouping (6/6), CSV/TSV/JSON results (10/10).

**RDF 1.1 Parsing**: 890 pass / 141 fail across N-Triples, Turtle, N-Quads,
TriG, RDF/XML, and model theory suites (39/39 rdf-mt).

See [CLAUDE.md](CLAUDE.md) for a detailed breakdown and known gaps.

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
