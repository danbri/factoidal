# JSON-LD program Phase 2: the toRdf manifest runner

Scaffolding note for `bin/jsonld-runner/jsonld_runner.ml`, following
Phase 1 (`Parser.JSONLD.fst`, expanded-form-only) per the phasing in
[`2026-07-04-jsonld-program-lessons.md`](2026-07-04-jsonld-program-lessons.md).
This is a scaffold-only change: source + wiring text, not a build.
The build-ocaml.sh diff below has not been applied or compiled in
this pass; apply and verify it in a follow-up commit under the
fast-verify-extract loop.

## How the runner works

`bin/jsonld-runner/jsonld_runner.ml` is I/O glue only (CLAUDE.md rule
#10 / anti-pattern #15) — it contains no JSON-LD or RDF semantics.
Everything that decides *meaning* lives in F*:

- `Parser.JSON.parse_json` parses the manifest itself. The toRdf
  manifest (`third_party/testing/json-ld/tests/toRdf-manifest.jsonld`)
  is a JSON-LD document; per Iron Rule #7 ("parsers belong in F*") it
  is walked using the extracted `Parser_JSON` accessors
  (`json_get_field` / `json_get_string` / `json_get_array`), not any
  OCaml JSON library.
- `Parser.JSONLD.parse_jsonld` deserializes each test's `input`
  `.jsonld` file into an `option rdf_dataset` (`None` on parse
  failure).
- `RDF.Canonical.canonicalize_to_nquads` canonicalizes both the
  parsed input's dataset and the parsed `expect` `.nq` fixture
  (loaded via `Parser.NQuads.parse_nquads`, which is lenient and
  always returns a dataset). The two canonical N-Quads strings are
  compared with plain OCaml string equality — this makes the compare
  independent of blank-node label choices on either side (the
  isomorphism the task asked for), reusing the exact machinery
  `tests/local/jsonld_regressions.sh` already relies on (there via
  the `factoidal --canonicalize` CLI; here via the extracted module
  directly, since the runner links `RDF_Canonical.ml` itself).

Per-test dispatch, driven by the manifest's `@type` array:

- **`jld:PositiveEvaluationTest`**: PASS iff `parse_jsonld` returns
  `Some ds` and `canonicalize_to_nquads ds` equals
  `canonicalize_to_nquads (parse_nquads expect_content)`.
- **`jld:NegativeEvaluationTest`**: PASS iff `parse_jsonld` returns
  `None` (the manifest's `expectErrorCode` is read but not currently
  compared — Phase 1 has no error-code-granular reporting; message-
  only for now).
- **`jld:PositiveSyntaxTest`**: PASS iff `parse_jsonld` returns
  `Some _` (no `expect` file exists for this test type, so there is
  nothing to compare against — only "does it parse without an
  error").

Two scope cuts, applied before dispatch:

1. **`option.specVersion == "json-ld-1.0"` -> SKIP.** This program
   targets JSON-LD 1.1 only; 11 of the 467 toRdf entries carry this
   tag.
2. **Input contains the literal substring `"@context"` -> FAIL, not
   SKIP.** `Parser.JSONLD` (Phase 1) has no context-processing at
   all — its module banner is explicit that `@context` members are
   dropped, uninterpreted. Skipping these tests would flatter the
   score (anti-pattern #3/#25); scoring them FAIL makes the real
   burn-down visible and gives Phase 3 (`JSONLD.Context` /
   `JSONLD.Expand`) a concrete, shrinking number to work against.
   This check runs uniformly across all three test types: for
   `NegativeEvaluationTest` it also covers the case where the
   "invalidity" is itself a context-processing error Phase 1 cannot
   detect (letting those run naturally would risk a false PASS if
   `parse_jsonld`'s silent-drop-@context behavior happened to still
   return `None` for an unrelated reason, or a false negative
   reading if it happened to succeed — forcing FAIL sidesteps both).

Output format mirrors `w3c_runner`'s: `  PASS: <name>` /
`  FAIL: <name> — <reason>` / `  skip: <name> — <reason>` per test
(stdout), a `[n/total] <id> <status>` progress line per test
(stderr, so it doesn't pollute the parseable stdout log), a
per-category `Suite Results:` block (`toRdf-Positive` /
`toRdf-Negative` / `toRdf-PositiveSyntax`, each with
`pass:P fail:F skip:S`), and a final:

```
jsonld-toRdf: N pass, M fail, K skip (out of T)
```

line. That exact shape (`<label>: N pass, M fail ... (out of T)`)
matches the regex `generate-report.sh`'s `extract_owl_scores`-style
generic per-catalog parser already expects
(`formal/fstar/generate-report.sh` lines ~184-210); wiring a
`jsonld-toRdf` row into the dashboard is a follow-up that extends
that script the same way the OWL profile scores were added, not a
new mechanism.

## build-ocaml.sh wiring (not yet applied)

Three edits, all modeled directly on the existing `w3c_runner` /
`rdfc10_runner` blocks. `Parser_JSON.ml`, `Parser_JSONLD.ml`,
`Parser_NQuads.ml`, and `RDF_Canonical.ml` are already members of
`$COMMON_MODULES` (build-ocaml.sh line ~397-441), so no module-list
change is needed there — only a new compile target.

**1. New `NATIVE_TARGETS` / `NATIVE_SOURCES` entries** (in the arrays
around build-ocaml.sh line ~505-520):

```bash
  NATIVE_TARGETS=(
    "$BINDIR/w3c_runner"
    "$BINDIR/factoidal"
    "$BINDIR/factoidal-http"
    "$BINDIR/owl_runner"
    "$BINDIR/rdfc10_runner"
    "$BINDIR/jsonld_runner"
    "$BINDIR/cottas_ondisk_smoketest"
  )
  NATIVE_SOURCES=(
    $COMMON_MODULES
    ../../../bin/w3c-runner/w3c_runner.ml
    ../../../bin/factoidal-http/factoidal_http.ml
    ../../../bin/factoidal-serve/factoidal_serve.ml
    ../../../bin/factoidal-explain/factoidal_explain.ml
    ../../../bin/factoidal-cli/factoidal_cli.ml
    ../../../bin/factoidal-http/factoidal_http_main.ml
    ../../../bin/owl-runner/owl_runner.ml
    ../../../bin/rdfc10-runner/rdfc10_runner.ml
    ../../../bin/jsonld-runner/jsonld_runner.ml
    ../../../bin/cottas-ondisk-smoketest/cottas_ondisk_smoketest.ml
    ../experimental_ocaml_glue/parquet_zstd_stubs.c
  )
```

**2. New ocamlopt block**, placed after the `rdfc10_runner` block
(after line ~642, before the `factoidal_http_client` block) so the
new runner sits alongside its closest sibling (both are standalone
single-manifest runners, unlike `w3c_runner`'s multi-suite CLI).
Per the 2026-07-04 http_client-block lesson recorded here (every
sibling block — `owl_runner`, `rdfc10_runner`, `factoidal_http_client`
— places `$PARQUET_NATIVE_STUBS` immediately after `$COMMON_MODULES`,
before the target's own `.ml`; skipping it is what caused an earlier
missing-symbol link failure), the new block follows the same order:

```bash
    # jsonld_runner — JSON-LD 1.1 toRdf manifest runner (Phase 2 of
    # the JSON-LD program). Reads
    # third_party/testing/json-ld/tests/toRdf-manifest.jsonld via the
    # F*-extracted Parser_JSON, calls Parser_JSONLD.parse_jsonld
    # (expanded-form only), and compares against expected .nq fixtures
    # via RDF_Canonical.canonicalize_to_nquads. See
    # docs/designissues/2026-07-05-jsonld-phase2-runner.md.
    JSONLD_RUNNER_RC=0
    run_with_heartbeat "ocamlopt jsonld_runner" "_ocamlopt_jsonld_runner.log" -- \
      ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
      $STATIC_FLAGS \
      $COMMON_MODULES \
      $PARQUET_NATIVE_STUBS \
      ../../../bin/jsonld-runner/jsonld_runner.ml \
      -o "$BINDIR/jsonld_runner" || JSONLD_RUNNER_RC=$?
    cat _ocamlopt_jsonld_runner.log
    if [[ "$JSONLD_RUNNER_RC" -ne 0 ]]; then
      echo "  ERROR: jsonld_runner build failed (ocamlopt rc=$JSONLD_RUNNER_RC)" >&2
      echo "  See full log above. Build aborted." >&2
      exit "$JSONLD_RUNNER_RC"
    fi
    if [[ ! -x "$BINDIR/jsonld_runner" ]]; then
      echo "  ERROR: jsonld_runner ocamlopt returned 0 but $BINDIR/jsonld_runner is missing or not executable" >&2
      exit 1
    fi
    echo "  Built: bin/${PLATFORM}/jsonld_runner ($(wc -c < "$BINDIR/jsonld_runner") bytes)"
```

**3. Symlink** (next to the existing convenience symlinks, line
~710-714):

```bash
  ln -sf "../../../bin/${PLATFORM}/jsonld_runner" jsonld_runner
```

No change to Step 3 ("Run native OCaml tests") is proposed here —
wiring `jsonld_runner` into the default `./build-ocaml.sh test` run
and into `generate-report.sh`'s dashboard extraction is separate
follow-up work once the baseline below is confirmed against a real
build.

## Expected baseline (state honestly)

Computed by walking the manifest's 467 `sequence` entries directly
(345 `PositiveEvaluationTest`, 106 `NegativeEvaluationTest`, 16
`PositiveSyntaxTest`) and checking each referenced `input` file for
the literal substring `@context`, without invoking any OCaml or F*
tooling (consistent with the hard constraint on this pass — no
compiler was run to produce these counts):

| category | total | skip (1.0) | FAIL (@context) | exercised |
|---|---|---|---|---|
| PositiveEvaluationTest | 345 | 5 | 303 | 37 |
| NegativeEvaluationTest | 106 | 6 | 86 | 14 |
| PositiveSyntaxTest | 16 | 0 | 0 | 16 |
| **total** | **467** | **11** | **389** | **67** |

That matches the lessons doc's own estimate: expanded-form-only,
~37 of the 345 positive inputs lack `@context` entirely and are the
only positive tests Phase 1 has a chance of passing outright. Of the
67 "exercised" tests (the ones that reach `parse_jsonld` and get a
real dispatch instead of a forced FAIL or SKIP), whether they PASS or
FAIL depends on Phase 1 correctness details this pass did not
execute against a compiled binary — that is the number the first
real `./build-ocaml.sh extract && jsonld_runner` run needs to report,
not something to guess here. Expect most of the 16
`PositiveSyntaxTest` entries to pass (they were chosen by the W3C
suite specifically to be context-free literal-encoding edge cases —
`literal_ascii_boundaries`, `literal_with_UTF8_boundaries`, control
characters — which is exactly Phase 1's designed surface); the 37
context-free positive tests and 14 context-free negative tests are
less certain without a run.

## Parser_JSONLD entry-point signature (assumption — verify before compiling)

Read directly from `formal/fstar/Parser.JSONLD.fst` (not assumed from
memory):

```fstar
val parse_jsonld (input:string) : option rdf_dataset
```

which the existing extraction (`formal/fstar/ocaml-output/Parser_JSONLD.ml`,
already checked in) confirms as:

```ocaml
let parse_jsonld (input : Prims.string) :
  RDF_Graph_Executable.rdf_dataset FStar_Pervasives_Native.option = ...
```

This matches the exact call already used in
`bin/factoidal-cli/factoidal_cli.ml` (`Parser_JSONLD.parse_jsonld
content` matched against `FStar_Pervasives_Native.Some ds` /
`FStar_Pervasives_Native.None`), which the new runner's `run_test`
also relies on — no new assumption beyond what that existing call
site already depends on. Likewise confirmed directly from the
checked-in extractions (not assumed):

- `Parser_JSON.parse_json (input:string) : option json_val`
- `Parser_JSON.json_get_field / json_get_string / json_get_array : string -> json_val -> option _`
- `Parser_NQuads.parse_nquads (input:string) : rdf_dataset` (non-option, lenient)
- `RDF_Canonical.canonicalize_to_nquads (ds:rdf_dataset) : string`

All four were read from the actual `.fst` source and the already-
extracted `.ml` in `ocaml-output/` (read-only reference, not edited)
rather than assumed — the orchestrator does not need to re-verify
these before compiling, only the build-ocaml.sh wiring diff above,
which has not been applied or run.
