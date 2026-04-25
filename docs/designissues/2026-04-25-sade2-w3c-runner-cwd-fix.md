# Sade2 — w3c_runner cwd-sensitivity fix (2026-04-25)

## Bug

`relpath_under` (line 2333 of `formal/fstar/ocaml-output/w3c_runner.ml`) and
its caller `make_turtle_base_tc` (line 2348) absolutise relative paths via
`Filename.concat (Sys.getcwd ()) p`. `Filename.concat` does **not** normalise
`..` segments. When the runner is invoked from `formal/fstar/ocaml-output/`,
the manifest path arrives as `../../../third_party/.../rdf-xml/manifest.ttl`,
so `md` ends up shaped like

    /Users/.../formal/fstar/ocaml-output/../../../third_party/.../rdf-xml

while `tc.query_file` (parsed out of an `mf:action` IRI through
`iri_to_local_path`) is absolutised differently and ends up shaped like

    /Users/.../third_party/.../rdf-xml/rdf-ns-prefix-confusion/test0004.rdf

The literal-prefix subtraction therefore fails, `relpath_under` falls back to
`Filename.basename filepath`, the subdirectory (`rdf-ns-prefix-confusion/`)
is dropped from the test base IRI, every parsed subject/object IRI lacks
that subdirectory segment, and `triple_sets_match` reports
`Triples mismatch: expected N, got N` for 19 rdf-xml tests.

Same binary, two cwds, two scores:

    repo root                          → rdf-xml pass:166 fail:0
    formal/fstar/ocaml-output          → rdf-xml pass:147 fail:19

Vav's diagnosis (`docs/designissues/2026-04-25-vav-rdfxml-regression-diagnosis.md`)
called this out and recommended Option (i): normalise the `..` segments in
`relpath_under` before the prefix-subtract.

## Fix (Option A)

Insert a small pure-OCaml path normaliser `normalise_path` directly above
`relpath_under` and apply it to `md` and `fp` after the cwd-prepend. Pure
string manipulation — no `Unix` module dependency, no `realpath` system call,
works cross-platform, idempotent on already-normalised paths, leaves absolute
prefix `/` intact, drops `.` segments, collapses `..` against the previous
non-`..` segment (and leaves leading `..` segments alone for genuinely
relative-up paths).

Apply the same normalisation in `make_turtle_base_tc`'s `None`-branch fallback
and in `make_turtle_base` for symmetry, so `file://` base IRIs from any cwd
are also stable.

## Acceptance

    cd formal/fstar/ocaml-output
    ./w3c_runner --rdf rdf-xml | tail -2
    # expect rdf-xml pass:166 fail:0

    cd /Users/danbri/working/factoidal
    ./bin/darwin-arm64/w3c_runner --rdf rdf-xml | tail -2
    # expect rdf-xml pass:166 fail:0
