# bin/factoidal-dump-nq — canonical N-Quads serializer

Stand-alone CLI that reads RDF input and emits canonical N-Quads on
stdout.

```
factoidal-dump-nq <input>
```

Used as the F\*-extracted RDFC-1.0 canonicalisation reference output
in CI; also as a smoketest for the F\*-extracted N-Quads serialiser
on real W3C input files.

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches.
This binary is a consumer of the F\*-extracted RDF / Canonical /
parser modules, so it lives under `bin/<consumer>/` per the
migration epic [#200](https://github.com/danbri/factoidal/issues/200)
Section D.

The built binary still lands at `bin/<platform>/factoidal-dump-nq`
(and `factoidal-dump-nq.byte` for bytecode) — same path as before;
only the source moved.

## Build

```
cd formal/fstar
./build-ocaml-serializer.sh
```

`build-ocaml-serializer.sh` cd's into `formal/fstar/ocaml-output/`
and references this source via `../../../bin/factoidal-dump-nq/
factoidal_dump_nq.ml` (three levels up).

## .gitignore

ocamlopt build artifacts (`.cmi`, `.cmx`, `.cmo`, `.o`) are
gitignored.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/cottas-ondisk-smoketest/README.md`
