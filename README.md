# Factoidal

A formally verified RDF/SPARQL implementation written in F\*, with
verified code extracted to OCaml for execution. The F\* specifications
are the product — executable code is obtained by extraction, not by
hand-writing implementations.

Status: I'm surprised it works at all. I have seen rdf/xml FOAF files parse in milliseconds, but Turtle DBpedia entries will take longer than heat death of the universe. Formal does not necessarily mean fast. Work in progress.

**[Live W3C test results](https://danbri.github.io/factoidal/test-results/)**

## Quick Start

```bash
# Install prerequisites (Debian/Ubuntu)
sudo apt-get install -y opam libgmp-dev pkg-config

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

RDF parsing/dump:
  factoidal --dump FILE.ttl           Parse and dump as N-Triples
  factoidal --count FILE.ttl          Count triples
  factoidal --dump --format rdfxml FILE.rdf

Options:
  -d, --data FILE        Load RDF data (repeatable, "-" for stdin)
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

Supported RDF formats:  Turtle, N-Triples, N-Quads, TriG, RDF/XML
Supported query forms:  SELECT, ASK, CONSTRUCT
```

## Supported SPARQL Features

SELECT, ASK, CONSTRUCT, PREFIX, BASE, FILTER, OPTIONAL, UNION, MINUS,
BIND, VALUES, EXISTS/NOT EXISTS, DISTINCT, REDUCED, ORDER BY, LIMIT,
OFFSET, GROUP BY, HAVING, aggregates (COUNT, SUM, AVG, MIN, MAX,
GROUP_CONCAT, SAMPLE), subqueries, property paths, and 30+ built-in
functions.

## Building from Source

### Prerequisites

| Dependency | Purpose | Install |
|-----------|---------|---------|
| opam | OCaml package manager | `apt-get install opam` |
| libgmp-dev | Arbitrary-precision integers | `apt-get install libgmp-dev` |
| F\* (fstar) | Verified compiler | `opam install fstar` |
| z3 | SMT solver (F\* uses it) | `opam install z3` or [binary release](https://github.com/Z3Prover/z3/releases) |
| zarith | OCaml bigint library | `opam install zarith` |
| sha, digestif | Hash functions (MD5/SHA) | `opam install sha digestif` |

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

The build produces two binaries in `formal/fstar/ocaml-output/`:
- `factoidal` — the CLI query/parsing tool
- `w3c_runner` — the W3C conformance test runner

### Verify F\* specifications

```bash
cd formal/fstar
make verify    # requires z3
```

This type-checks all F\* modules against the SMT solver. No `admit()` or
`--lax` is used — all proofs are machine-checked.

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
│   ├── RDF.Graph.Executable.fst   RDF graph types + operations (638 lines)
│   ├── SPARQL11.Algebra.fst       SPARQL 1.1 algebra + evaluator (3658 lines)
│   ├── SPARQL11.Parser.fst        SPARQL parser
│   ├── Parser.Combinators.fst     Parser combinator foundation
│   ├── Parser.NTriples.fst        N-Triples parser
│   ├── Parser.Turtle.fst          Turtle parser
│   ├── Parser.NQuads.fst          N-Quads parser
│   ├── Parser.TriG.fst            TriG parser
│   ├── Parser.XML.fst             Non-validating XML parser
│   ├── Parser.RDFXML.fst          RDF/XML parser
│   ├── Parser.SRX.fst             SPARQL Results XML parser
│   ├── Parser.CSVResults.fst      CSV/TSV results parser
│   ├── Makefile                   verify + extract targets
│   ├── build-ocaml.sh            F* → OCaml → binary pipeline
│   ├── ocaml-patches.sh          wires assume-val stubs
│   └── ocaml-output/             extracted OCaml + CLI tools
│       ├── factoidal_cli.ml       CLI tool source (I/O glue)
│       ├── w3c_runner.ml          W3C test runner (I/O glue)
│       └── *.ml                   F*-extracted OCaml modules
├── tests/w3c/                    git submodule (W3C test files)
└── CLAUDE.md                     development instructions
```

## W3C Conformance Status

**SPARQL 1.1**: 303 pass / 105 fail / 205 skip (UPDATE) / 18 unsupported — 74% of applicable tests

Strong areas: aggregates (38/44), functions (71/75), bind (9/10), negation
(11/12), property paths (31/33), subqueries (9/12), project-expression (7/7).

**RDF 1.1 Parsing**: 644 pass / 387 fail across N-Triples, Turtle, N-Quads,
TriG, RDF/XML, and model theory suites.

See [CLAUDE.md](CLAUDE.md) for a detailed breakdown and known gaps.

## Architecture

```
F* formal spec (the product)
    │
    ▼
fstar.exe --codegen OCaml (extraction, proof-erased)
    │
    ▼
OCaml binaries (factoidal CLI + W3C test runner)
    │
    ├── factoidal: SPARQL queries + RDF parsing from the command line
    └── w3c_runner: W3C conformance test suite runner
```

All RDF parsing, SPARQL parsing, and query evaluation is performed by
F\*-extracted code. The CLI tools are thin I/O wrappers — they read files,
call the extracted functions, and format the output.

## License

Apache License 2.0 — see [LICENSE](LICENSE) for details.
