# Generated Source Artifacts

All files in this directory are **machine-generated** from the F* formal specifications
via automated extraction pipelines. Do not edit manually — regenerate from source.

## Contents

```
gensrc/
├── ocaml/
│   ├── RDF_Graph_Executable.ml   # F* → OCaml (fstar.exe --codegen OCaml)
│   └── SPARQL11_Algebra.ml       # F* → OCaml (patched for assume val stubs)
├── js/
│   ├── factoidal-fstar.js        # OCaml → JS (js_of_ocaml) — demo bundle
│   └── w3c-tests.js              # OCaml → JS (js_of_ocaml) — test runner
└── c/
    ├── RDF_Graph_Executable.c    # F* → C (KaRaMeL extraction)
    └── RDF_Graph_Executable.h    # C header
```

## Regeneration

```bash
cd formal/fstar
eval $(opam env --switch=fstar)
./build-ocaml.sh          # OCaml + JS extraction
make extract-c            # C extraction via KaRaMeL
```

## Source → Generated Correspondence

| F* Source | Generated |
|-----------|-----------|
| `formal/fstar/RDF.Graph.Executable.fst` | `ocaml/RDF_Graph_Executable.ml`, `c/RDF_Graph_Executable.c` |
| `formal/fstar/SPARQL11.Algebra.fst` | `ocaml/SPARQL11_Algebra.ml` |
| Both modules | `js/factoidal-fstar.js`, `js/w3c-tests.js` |

## Test Status

**Programmatic algebra tests: 50/50 passing** (hand-constructed, not W3C-driven).

**W3C SPARQL tests (real .rq files): 87/124 passing** (70%) — uses F*-extracted parser
(`SPARQL.Parser.fst`) + F*-extracted evaluator (`SPARQL11.Algebra.fst`) against actual
W3C test suite files. See `formal/fstar/ocaml-output/w3c_sparql_tests.ml` for the harness.

Note: The programmatic tests exercise the evaluator directly without parsing. The W3C tests
are the honest measure — they parse real `.rq` query files through the full F*-extracted pipeline.
