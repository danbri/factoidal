# Worklog: F* Spec Alignment

**Baseline tag:** `spec-alignment-v0` (commit 7223568)
**Date:** 2026-03-06

## Audit Summary

Full formal audit of F* spec (`rdfcore11.fstar.txt`, `sparql11.fstar.txt`) vs Rust implementation (`sparql.rs`, `rdf.rs`). Six semantic bugs found where Rust contradicts F*.

## Semantic Bugs to Fix

| # | Area | F* spec | Rust bug | Status |
|---|------|---------|----------|--------|
| 3 | FILTER inside OPTIONAL | LeftJoin filter is join condition; failed filter preserves left row unextended | Filter is post-filter; failed filter discards row | FIXED |
| 4 | BIND overwrites | `apply_bind` returns None if var already bound (rdfcore11:404-405) | `HashMap::insert` overwrites unconditionally (sparql.rs:2435) | FIXED |
| 7 | BEV for IRIs/BNodes | Returns `false` (rdfcore11:376-377) | Returns `true` (sparql.rs:2255) | FIXED |
| 8 | BEV for typed literals | Returns `false` (rdfcore11:378) | Returns `true` if lexical non-empty (sparql.rs:2252) | FIXED |
| 13 | Arithmetic on plain literals | Type error (sparql11:490-493) | Coerces to f64 (sparql.rs:2100-2101) | FIXED |

**Not fixing now (architectural):** Bug #5 (f64 vs int) — requires NumericValue enum, large refactor. Tracked for Layer 1.

## Fix Log

### 2026-03-06: Spec alignment fixes

All four fixes applied, all 177 tests pass. W3C SPARQL score: 159 → 161 (+2).

**Fix #3 — FILTER inside OPTIONAL (sparql.rs:2372-2413)**
Rewrote `WhereClause::Optional` handler to partition inner clauses into patterns and filters.
Patterns evaluated first; if patterns match but filters fail, original binding preserved (LeftJoin semantics).

**Fix #4 — BIND no-overwrite guard (sparql.rs:2467)**
Added `if !binding.contains_key(var_name)` guard before `insert`. BIND now skips already-bound variables per F* spec.

**Fix #7 — BEV for IRIs/BNodes (sparql.rs:2257)**
Changed `TermValue::Iri(_) | TermValue::BNode(_) => true` to `=> false`. Non-literals are type errors in boolean context.

**Fix #8 — BEV for typed literals (sparql.rs:2249-2255)**
Only `xsd:string` and `rdf:langString` use non-empty check. All other typed literals → `false`.

**Fix #13 — Arithmetic type strictness (sparql.rs:2098-2105)**
Removed `PlainLiteral` coercion arms. Arithmetic now returns `None` for non-numeric operands.

### 2026-03-06: Arithmetic in expressions (parser fix)

`parse_filter_expr` could not handle arithmetic operators (`+`, `-`, `*`, `/`).
Expressions like `datatype(?l + ?r)` inside FILTER failed with `"Expected ')', got '+'"`.

**Fix:** Split `parse_filter_expr` into `parse_filter_expr` (handles arithmetic) and
`parse_filter_expr_primary` (handles atoms/functions). The outer function checks for
arithmetic operators after parsing a primary expression.

**Impact:** type-promotion suite 0/30 → 30/30 (100%). Total: 161 → 191 (+30).

### Remaining divergences (not bugs, or deferred)

| # | Area | Decision |
|---|------|----------|
| 5 | f64 vs int | Deferred to Layer 1 (needs NumericValue enum) |
| 1.4 | graph_bnodes dedup | Rust dedup is reasonable; F* spec may be wrong |
| 1.6 | graph_remove error | Rust error return is an extension, not a contradiction |
| 6 | Lang tag case | Rust is more correct (BCP 47); update F* spec |
| 10-12 | Functions on non-variables | Parser limitation; track for later |

