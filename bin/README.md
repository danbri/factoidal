# Pre-built Binaries

Platform-specific pre-built binaries so you can run factoidal without
an F*/opam toolchain.

```
bin/
├── darwin-arm64/       macOS Apple Silicon (M1/M2/M3/M4)
│   ├── factoidal       SPARQL query + RDF parsing CLI
│   └── w3c_runner      W3C conformance test runner
└── linux-x86_64/       Linux x86-64 (statically linked)
    ├── factoidal
    └── w3c_runner
```

## Usage

```bash
# macOS
bin/darwin-arm64/factoidal --help
bin/darwin-arm64/w3c_runner --all

# Linux
bin/linux-x86_64/factoidal --help
bin/linux-x86_64/w3c_runner --all
```

## Rebuilding

```bash
cd formal/fstar
eval $(opam env --switch=fstar)
./build-ocaml.sh compile
```

The build script auto-detects the platform and outputs to the correct
`bin/<platform>/` directory.
