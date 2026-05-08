# bin/parquet-probe

Diagnostic CLI that prints the parquet metadata header (magic,
metadata length, row groups, columns, page offsets) of a given
file. Useful for poking at COTTAS / HDT artefacts without
spinning up a SPARQL endpoint.

Built from `parquet_probe.ml` against the F\*-extracted
`Parquet.Footer` module.

## Why this lives in `bin/<consumer>/`

Per CLAUDE.md rule #11: consumer tools (CLIs, smoke tests,
runners) are not part of the verified library and belong in
`bin/<consumer>/`, not in `formal/fstar/ocaml-output/`.

Relocated 2026-05-08 (#200 PR5 — allowlist retirement track).
Was previously grandfathered in the
`check-ocaml-output-cleanliness.yml` allowlist; the relocation
shrinks the allowlist by one entry.

## Build

`./build-ocaml.sh compile` builds the binary at
`bin/<platform>/parquet_probe`.

## Run

```
./bin/linux-x86_64/parquet_probe path/to/file.parquet
```

Outputs key=value lines: `magic=PAR1`, `num_rows=...`,
`row_groups=...`, `row_group0_col0_data_page_offset=...`, etc.
Exits non-zero if the file isn't recognisable as Parquet.
