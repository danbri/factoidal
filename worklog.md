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

### 2026-03-06: Three-valued FILTER logic

`eval_filter` returned `bool`, but SPARQL uses three-valued logic (true/false/error).
`!error` was becoming `true` instead of staying `error`. This caused `FILTER(! ?w)` to
pass for unbound variables and unknown-datatype literals.

**Fix:** Changed `eval_filter` return type from `bool` to `Option<bool>`.
- `None` = type error (row excluded from results)
- `Not(inner)`: `None.map(|v| !v)` = `None` (error propagates)
- `And`: false ∧ error = false, true ∧ error = error
- `Or`: true ∨ error = true, false ∨ error = error
- All call sites use `.unwrap_or(false)` — errors exclude the row

**Impact:** boolean-effective-value 6/7 → 7/7 (100%). Total: 191 → 192 (+1).

### 2026-03-06: Blank node identity + tokenizer `<` fix

**Bug A — Blank node identity not preserved across triples.**
Both Turtle and N-Triples parsers called `BNode::from_str(label)` per occurrence,
which generated fresh IDs for non-numeric labels (fell through to `BNode::auto()`).
`_:a` in one triple got a different ID than `_:a` in another triple.

**Fix:** Added `HashMap<String, BNode>` to both parsers (`bnode_labels` field in
TurtleParser, local map in ntriples::parse). Labels map to their first-assigned ID.

**Bug B — Tokenizer `<` always parsed as IRI start.**
`FILTER(?price < 15)` was tokenized as `<` + ` 15) ...` = one malformed IRI token.

**Fix:** `<` is only treated as IRI start if followed by a letter, `/`, `_`, `#`, `:`,
or `>` (for `<>`). Otherwise emitted as operator token.

**Impact:**
- distinct: 7/11 → 11/11 (100%)
- optional: 1/7 → 4/7 (+3)
- optional-filter: 1/6 → 5/6 (+4)
- expr-ops: 9/17 → 10/17 (+1)
- Total: 192 → 204 (+12). Running total from baseline: 159 → 204 (+45, 36.5% → 46.8%).

### 2026-03-06: MINUS, plain literal matching, Unicode prefix, REGEX type-check

**MINUS anti-join** — Implemented `WhereClause::Minus` per F* spec (§18.5): retain μ1
only if no μ2 in RHS is compatible with overlapping domains. +2 negation tests.

**Plain literal matching** — Untyped literal patterns now only match `xsd:string`
literals (not custom-typed). Per RDF 1.1, `"x"` ≠ `"x"^^:someType`. Fixes quotes-3.
basic suite now **27/27 (100%)**.

**Unicode prefix names** — Turtle `@prefix` directive now reads chars (not bytes),
fixing CJK prefix names like `@prefix 食: <...>`.

**REGEX type-check** — REGEX returns type error for IRI/BNode arguments. +1 regex test.

**F* spec updates** — Added langMatches spec (BCP 47 matching), fn_regex_typed
(type constraint), resolve_query_iri (BASE resolution), unescape_sparql_string,
literal matching semantics documentation.

**Impact:**
- basic: 26→27/27 (100%) — literal matching fix
- negation: 2→4/11 — MINUS support
- regex: still 20/21 — type-check fix
- Total: 222 → 228 (+6). Running total: 159 → 228 (+69, 36.5% → 52.3%).

### 2026-03-06: BASE IRI resolution + Turtle relative IRIs

**SPARQL BASE resolution** — Relative IRIs like `<x>`, `<#x>` in query body now resolve
against declared BASE. PREFIX namespace IRIs (e.g., `PREFIX : <>`) also resolve against BASE.

**Turtle base IRI in test harness** — SPARQL test data files now parsed with `parse_with_base`
using the file's absolute path as base IRI. Fixes relative IRIs like `<abc>`, `<>` in test data.

**Impact:**
- basic: 22→26/27 (96.3%) — 4 base-prefix tests fixed
- expr-builtin: 10→13/24 — langMatches data files now parse
- triple-match: 2→3/4 — fred@edu relative IRI
- Total: 214 → 222 (+8). Running total: 159 → 222 (+63, 36.5% → 50.9%).

### 2026-03-06: sameTerm, langMatches, regex flags, triple-quoted strings

**sameTerm()** — Added `Filter::FnSameTerm` variant. RDF term identity comparison
(stricter than `=`; same lexical + same datatype = same term).

**langMatches()** — Added `Filter::FnLangMatches` variant. BCP 47 basic matching:
`langMatches(lang(?x), "*")` checks non-empty lang tag; `langMatches(lang(?x), "en")`
does case-insensitive prefix match.

**Regex q/x flags** — `q` flag escapes metacharacters (literal match). `x` flag strips
unescaped whitespace and `#`-comments from pattern.

**SPARQL string unescape** — Regex patterns now have `\\` → `\`, `\n` → newline, etc.
applied before compilation. Previously `"example\\.com"` retained double backslash.

**Triple-quoted strings** — Tokenizer now handles `"""..."""` and `'''...'''`.
Normalized to regular double-quoted strings for downstream processing.

**Impact:**
- regex: 14/21 → 20/21 (95.2%)
- basic: 20/27 → 22/27 (+2)
- expr-builtin: 9/24 → 10/24 (+1)
- 1.1/functions: 32/74 → 33/74 (+1)
- Total: 204 → 214 (+10). Running total: 159 → 214 (+55, 36.5% → 49.1%).

### Remaining divergences (not bugs, or deferred)

| # | Area | Decision |
|---|------|----------|
| 5 | f64 vs int | Deferred to Layer 1 (needs NumericValue enum) |
| 1.4 | graph_bnodes dedup | Rust dedup is reasonable; F* spec may be wrong |
| 1.6 | graph_remove error | Rust error return is an extension, not a contradiction |
| 6 | Lang tag case | Rust is more correct (BCP 47); update F* spec |
| 10-12 | Functions on non-variables | Parser limitation; track for later |

