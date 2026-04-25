# RDFC-1.0 Map test JSON output (Agent Qof2, P2)

**Date**: 2026-04-25
**Branch**: claude/main
**Goal**: Implement Map output in `rdfc10_runner.ml` so the 22 STUB
RDFC10MapTest entries become PASS where canonicalisation produces the
correct bnode mapping.

## Format

Sample expected file (`test053-rdfc10map.json`):

```
{
  "e3": "c14n0",
  "e6": "c14n1",
  ...
  "e4": "c14n6"
}
```

- Outer braces on their own lines (`{\n` and `}\n`).
- Each entry `  "<orig>": "<canon>",` — 2-space indent, no trailing comma
  on the last entry.
- Keys/values are bnode labels WITHOUT the `_:` prefix (parser strips it).
- Order: sorted by canonical value (`c14n0`, `c14n1`, ..., `c14nN`),
  i.e. issuance order from `assign_full_in_order`.

## Implementation

The F\* function `RDF.Canonical.build_canonical_mapping : rdf_dataset ->
list (bnode_id * string)` already exists and returns
`(original-label, canonical-label)` in issuance order. No F\* edit needed.

### OCaml runner changes (`rdfc10_runner.ml`)

1. Add `mapping_to_json : (string * string) list -> string` that:
   - sorts the pairs by canonical value (extract integer from `c14nN`)
   - renders the JSON with the exact byte format above
2. Add `run_map_test` mirroring `run_eval_test` but emitting the JSON
   mapping instead of the canonical N-Quads, then byte-compares against
   the expected `*-rdfc10map.json` file.
3. Wire `TK_Map` → `run_map_test` in `run_test`.

### Sorting

The OCaml extraction's `is_issued` field preserves insertion order
(append via `@`), so it should already be in c14n0..c14nN order. We
sort defensively anyway by extracting the integer suffix.

## Hard limits

- 0 LoC F\* edit (helper already exists).
- ≤ 100 LoC OCaml runner edit.
- No `--lax`, no semantic logic in the runner (just JSON formatting).

## Expected outcome

Up to +22 Map tests PASS. Tests where the underlying canonicalisation
fails (poison-clique / n-step automorphism cases like test074) will
still STUB or FAIL — but most simpler Map tests should pass since
HFDQ + 3-step neighbour refinement covers them.
