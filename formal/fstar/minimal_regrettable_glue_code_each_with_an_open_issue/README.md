# Minimal Regrettable Glue Code (Each With an Open Issue)

Every file in this directory is a patch that modifies F\*-extracted OCaml code
at build time. Each patch exists because the F\* source cannot yet express
what the patch does. **Every patch has a corresponding open GitHub issue
tracking when it can be eliminated.**

## Patch Inventory

| File | Issue | Category | Target |
|------|-------|----------|--------|
| `57_service_client_bind.sh` | [#57](https://github.com/danbri/factoidal/issues/57) | assume-val stubs | SPARQL11_Algebra.ml |
| `62_forward_ref_wiring.sh` | [#62](https://github.com/danbri/factoidal/issues/62) | Forward-ref wiring | SPARQL11_Algebra.ml |
| `63_regex_hash_uuid_stubs.sh` | [#63](https://github.com/danbri/factoidal/issues/63) | assume-val stubs | SPARQL11_Algebra.ml |
| `64_sparql_parser_escape_stubs.sh` | [#64](https://github.com/danbri/factoidal/issues/64) | assume-val stubs | SPARQL11_Parser.ml |
| `65_base_iri_resolution.sh` | [#65](https://github.com/danbri/factoidal/issues/65) | F\* API gap workaround | SPARQL11_Algebra.ml, SPARQL11_Parser.ml |
| `66_zero_length_property_path.sh` | [#66](https://github.com/danbri/factoidal/issues/66) | SPARQL semantics fix | SPARQL11_Algebra.ml |
| `67_rdfxml_validation.sh` | [#67](https://github.com/danbri/factoidal/issues/67) | F\* semantic gap | Parser_RDFXML.ml |
| `68_unicode_boundary_workarounds.sh` | [#68](https://github.com/danbri/factoidal/issues/68) | F\* type workaround | Parser_NTriples.ml, Parser_Turtle.ml |
| `53_blank_node_variable_rewriting.sh` | [#53](https://github.com/danbri/factoidal/issues/53) | **KNOWN VIOLATION** | w3c_runner.ml |
| `69_runner_io_glue.sh` | [#69](https://github.com/danbri/factoidal/issues/69) | I/O glue | w3c_runner.ml |
| `89_fast_string_primitives.sh` | [#89](https://github.com/danbri/factoidal/issues/89) | assume-val stubs (perf) | Parser_FastString.ml |
| ~~`103_parquet_ascii_string_fast_path.sh`~~ | (was: parquet ASCII fast-path) | RETIRED 2026-05-14 — Parquet.Footer.fst migrated to Parser.FastString primitives in Phases A/B/C; patch deleted in Phase D. | Parquet_Footer.ml (formerly) |
| `202_now_ms.sh` | [#202](https://github.com/danbri/factoidal/issues/202) | assume-val stubs (I/O clock) | SPARQL_Eval_TimeBudget.ml |

> **Note on the `103_` filename**: the patch was named to track a GitHub issue, but the
> actual issue #103 on GitHub ("CONSTRUCT over --data-cottas still falls back to eager
> in-memory path") is unrelated to the Parquet ASCII fast-path. The same drift exists for
> the (already-retired) `95_stack_safe_list_ops.sh` ↔ GitHub `#95` (which is about WASM
> demo perf). Future patches should either confirm the GitHub issue mapping before naming,
> or use a local-only number that doesn't collide with the GitHub issue space.

## Categories

- **assume-val stubs**: Replace `failwith "Not yet implemented"` with OCaml implementations of F\* `assume val` declarations. Acceptable long-term for platform-specific code (crypto, I/O).
- **Forward-ref wiring**: Work around F\* extraction's inability to handle mutual recursion across module boundaries. Should be eliminated by restructuring F\* code.
- **F\* API gap workaround**: Provide functionality that F\* could express but doesn't yet (e.g., threading base IRI through function signatures).
- **F\* type workaround**: Work around F\* type system limitations (e.g., char precondition `< 0xD7FF` vs Unicode's `< 0xD800`).
- **KNOWN VIOLATION**: RDF/SPARQL semantic logic that MUST be in F\* but isn't yet. These are bugs, not features. Each is tracked with high priority.
- **I/O glue**: Small adjustments to the test runner. Should be direct edits to w3c_runner.ml, not patches.

## How It Works

Each `.sh` file:
1. Takes `OUTDIR` as `$1` (the directory containing extracted `.ml` files)
2. Checks if the target file exists
3. Checks if the patch is already applied (idempotency via grep markers)
4. Applies the patch only if not already present

The master script `apply_patches.sh` in the parent directory iterates through
all files in this directory in sorted order.

## Rules

1. **Every patch MUST have a GitHub issue.** No exceptions.
2. **The issue number is in the filename.** `<issue>_<description>.sh`
3. **Every patch MUST be idempotent.** Check before applying.
4. **No RDF/SPARQL semantic logic.** If your patch implements query evaluation,
   graph comparison, entailment reasoning, or any other semantic operation — STOP.
   That belongs in `.fst` files.
5. **When an issue is resolved** (F\* code replaces the patch), delete the file.
