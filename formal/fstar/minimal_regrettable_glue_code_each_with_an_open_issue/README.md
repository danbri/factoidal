# Minimal Regrettable Glue Code (Each With an Open Issue)

Every file in this directory is a patch that modifies F\*-extracted OCaml code
at build time. Each patch exists because the F\* source cannot yet express
what the patch does. **Every patch has a corresponding open GitHub issue
tracking when it can be eliminated.**

## Patch Inventory

| File | Issue | Category | Target |
|------|-------|----------|--------|
| `57_service_client_bind.sh` | [#57](https://github.com/danbri/factoidal/issues/57) | assume-val stubs | SPARQL11_Algebra.ml |
| `62_forward_ref_wiring.sh` | [#62](https://github.com/danbri/factoidal/issues/62) | Forward-ref wiring | SPARQL11_Algebra.ml (further retired 2026-08-10, G4-subselect-fold: `eval_subselect_fwd` is now a concrete F\* definition too -- `eval_select_query` joined the `eval_pattern_store`/`substitute_existentials`/`eval_exists` clique via the `query_size` extension of `pattern_size`/`expr_size` (GP_SubSelect sizes as `1 + query_size q`; `lemma_lateral_substitute_preserves_size` covers the LATERAL call site), no longer wired here; scope now 1 symbol -- `eval_property_path_fwd`. Previous retirement 2026-08-09, g4-exists-cycle-pilot: `eval_exists_fwd`.) |
| `63_regex_hash_uuid_stubs.sh` | [#63](https://github.com/danbri/factoidal/issues/63) | assume-val stubs | SPARQL11_Algebra.ml |
| `67_rdfxml_validation.sh` | [#67](https://github.com/danbri/factoidal/issues/67) | F\* semantic gap | Parser_RDFXML.ml |
| `89_fast_string_primitives.sh` | [#89](https://github.com/danbri/factoidal/issues/89) | assume-val stub | Parser_FastString_CharBoundary.ml (cut down 2026-08-10, FastString re-founding Step 2/3: was 6 primitives + a codepoints-of-string override against Parser_FastString.ml, now just the 1 surviving assume val, `unsafe_char_of_d7ff`, moved to its own module -- see docs/designissues/2026-08-10-faststring-refounding-plan.md. The 6 primitives are real F\* definitions now; their fast-OCaml realisation is `experimental_ocaml_glue/parser_faststring_ops_runtime.sh`, a rule-11(b) perf patch, not an assume-val stub, hence not listed in this table) |
| `103_parquet_ascii_string_fast_path.sh` | [#103](https://github.com/danbri/factoidal/issues/103) | OCaml runtime override (perf) | Parquet_Footer.ml |
| `181_shacl_validate_stub.sh` | [#181](https://github.com/danbri/factoidal/issues/181) | assume-val stubs | SHACL_Validation.ml |
| `202_now_ms.sh` | [#202](https://github.com/danbri/factoidal/issues/202) | assume-val stubs (I/O clock) | SPARQL_Eval_TimeBudget.ml |
| `296_z3_check_sat.sh` | [#296](https://github.com/danbri/factoidal/issues/296) | assume-val stub (ASSUME-HOST) | Tableau_CountingOracle.ml |

Retired patches (F\* now covers them; kept in git history only): #53
blank-node rewriting, #64 parser escape stubs, #65 base-IRI resolution,
#66 zero-length property paths, #68 unicode boundary workarounds, #69
runner I/O glue.

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

The master script `ocaml-patches.sh` in the parent directory applies this
directory (in issue-number order) and then `experimental_ocaml_glue/`. It is
run by `build-ocaml.sh extract` — NOT by `compile` (anti-pattern #11).

## Rules

1. **Every patch MUST have a GitHub issue.** No exceptions.
2. **The issue number is in the filename.** `<issue>_<description>.sh`
3. **Every patch MUST be idempotent.** Check before applying.
4. **No RDF/SPARQL semantic logic.** If your patch implements query evaluation,
   graph comparison, entailment reasoning, or any other semantic operation — STOP.
   That belongs in `.fst` files.
5. **When an issue is resolved** (F\* code replaces the patch), delete the file.
