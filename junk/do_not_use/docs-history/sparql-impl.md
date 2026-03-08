> **STATUS: HISTORICAL INTEREST ONLY** — Line numbers and structure described here refer to an earlier version of `sparql.rs` (1893 lines; now ~2922 lines). Many features listed as "not implemented" have since been added. Retained for reference only.

# SPARQL Engine Implementation Guide

Internal developer reference for `rdf-wasm/src/sparql.rs` (1893 lines).

## 1. Architecture Overview

The file is organized into five major sections:

| Section | Lines | Description |
|---------|-------|-------------|
| **Types & Data Structures** | 1-180 | `TermValue`, `PatternElement`, `TriplePattern`, `Filter`, `FilterExpr`, `CompOp`, `WhereClause`, `ParsedQuery` |
| **Parser** | 182-838 | `Parser` struct with `parse_query()`, `parse_where_body()`, `parse_pattern_element()`, `parse_filter()` family |
| **Tokenizer** | 840-940 | `tokenize()` — hand-written char-by-char lexer |
| **Evaluator** | 942-1452 | `resolve_element()`, `match_element()`, `match_triple()`, `eval_filter*()`, `evaluate_clauses()`, plus `TypedFilterValue` and `typed_compare()` |
| **Public API** | 1454-1564 | `QueryResult` struct, `execute()` function |
| **Tests** | 1566-1893 | 14 unit tests covering core functionality |

Note: The tokenizer appears *after* the parser in the source, but is called first at runtime (line 194). The parser consumes tokens produced by `tokenize()`.

## 2. Data Structures

### TermValue (lines 25-90)

Runtime representation of a bound RDF term. Richer than a plain string so filters can inspect term kind.

```
TermValue::Iri(String)
TermValue::BNode(String)
TermValue::Literal { lexical, datatype, lang }
```

Key methods:
- `from_rdf_term()` / `from_subject()` — convert from core `rdf.rs` types
- `display()` — serialize back to SPARQL result format (`<iri>`, `"lex"@lang`, `"lex"^^<dt>`)
- `as_str_value()` — extract the string content regardless of kind
- `sort_key()` — `(u8, &str)` tuple for ORDER BY (BNode=0 < IRI=1 < Literal=2, then lexicographic)

### PatternElement (lines 96-102)

Parsed but not yet resolved pattern position (subject, predicate, or object in a triple pattern):

- `Variable(String)` — `?x` or `$x`
- `Iri(String)` — `<http://...>` or `a` (expanded to `rdf:type`)
- `PrefixedName(prefix, local)` — `foaf:name` (resolved later via `resolve_element()`)
- `Literal(lexical, lang, datatype)` — `"hello"@en`, `42`, `true`

### TriplePattern (lines 104-109)

Three `PatternElement`s: `s`, `p`, `o`. The fundamental unit of a BGP.

### Filter (lines 111-126)

Boolean-valued filter expressions:

- `Comparison(FilterExpr, CompOp, FilterExpr)` — `?x = 5`, `?age > 18`
- `And` / `Or` / `Not` — logical connectives
- `BooleanEffectiveValue(FilterExpr)` — bare expression evaluated as truthy/falsy
- `FnBound(var)` — `BOUND(?x)`
- `FnIsLiteral` / `FnIsIri` / `FnIsBlank` — type-testing functions
- `FnRegex(expr, pattern, flags)` — `REGEX(?x, "pat", "i")`
- `FnContains` / `FnStrStarts` / `FnStrEnds` — string functions

### FilterExpr (lines 128-138)

Value-producing expressions inside filters:

- `Variable(String)` — `?x`
- `StringLit(String)` — `"hello"`
- `NumericLit(f64)` — `42`, `3.14`
- `IriLit(String)` — `<http://...>`
- `FnStr` / `FnLang` / `FnDatatype` — accessor functions wrapping an inner `FilterExpr`
- `Arithmetic(left, op, right)` — `?x + 1`, `?a * ?b`

### CompOp (lines 140-148)

Six comparison operators: `Eq`, `Ne`, `Lt`, `Gt`, `Le`, `Ge`.

### WhereClause (lines 162-169)

The clause types that can appear inside a WHERE body:

- `Pattern(TriplePattern)` — a BGP triple pattern
- `Filter(Filter)` — a FILTER constraint
- `Optional(Vec<WhereClause>)` — an `OPTIONAL { ... }` block
- `Union(Vec<WhereClause>)` — legacy: right side of UNION appended inline
- `UnionGroup(Vec<Vec<WhereClause>>)` — `{ } UNION { } UNION { }` with multiple branches

### ParsedQuery (lines 171-180)

Top-level parse result:

- `prefixes: HashMap<String, String>` — PREFIX declarations
- `variables: Vec<String>` — SELECT variables (empty = `SELECT *`)
- `distinct: bool`
- `where_clauses: Vec<WhereClause>`
- `order_by: Vec<OrderClause>`
- `limit: Option<usize>`
- `offset: Option<usize>`

### TypedFilterValue (lines 1057-1083)

Typed wrapper used during filter evaluation to enable type-aware comparisons (numeric vs string vs IRI, etc.):

- `Iri(String)`, `BNode(String)`, `PlainLiteral(String)`, `LangLiteral(String, String)`
- `NumericLiteral(f64, String)` — value + datatype IRI
- `TypedLiteral(String, String)` — lexical + datatype for non-numeric, non-string types
- `BooleanLiteral(bool)`

Conversion: `term_to_typed()` (line 1095) converts `TermValue` to `TypedFilterValue` using the XSD datatype constants at lines 1085-1089.

### QueryResult (lines 1460-1463)

Public result struct (serializable via serde):

- `variables: Vec<String>` — column names
- `rows: Vec<Vec<Option<String>>>` — each row is a vector of optional display strings

## 3. Tokenizer

### `tokenize()` (lines 844-940)

Hand-written character-level tokenizer. Converts a SPARQL query string into `Vec<String>`.

**Processing order** (each iteration of the main `while i < len` loop):

1. **Whitespace** (line 852) — skip
2. **Comments** (line 857) — `#` through end of line, skip
3. **Two-char operators** (line 864) — `!=`, `<=`, `>=`, `^^`, `||`, `&&` recognized as single tokens
4. **Single-char tokens** (line 873) — `{ } ( ) . , * = ! ; [ ]` and `<` / `>`
   - Special case: `<` starts an IRI scan (lines 875-887) — reads through to `>` and emits the entire `<iri>` as one token
5. **String literals** (line 893) — `"` starts a quoted string, handles `\` escapes. After the closing `"`, immediately checks for `@lang` tag and emits it as a separate token
6. **Words** (line 920) — everything else: variables (`?x`), keywords (`SELECT`), prefixed names (`foaf:name`), numbers. Stops at whitespace, braces, parens, commas, semicolons, quotes. Period (`.`) stops only if followed by whitespace/`}`/EOF (so decimal numbers like `3.14` pass through intact)

**Known tokenizer limitations:**
- Single-quoted strings (`'...'`) are not handled by the string literal branch (only `"` is checked at line 893). They fall through to the word branch.
- Triple-quoted strings (`"""..."""`) are not handled; the tokenizer sees the first `"` and scans to the next `"`, splitting the content incorrectly.
- No Unicode escape processing (`\uXXXX`) in the tokenizer itself.
- The `>` character as a comparison operator can conflict with IRI parsing if preceded by `<` (mitigated by the IRI scan taking priority).

## 4. Parser

### Parser struct (lines 186-220)

Wraps a `Vec<String>` of tokens with a position cursor. Core methods:

- `peek()` — look at current token without consuming
- `next()` — consume and return current token
- `expect(s)` — consume and assert token matches (case-insensitive)

### `parse_query()` (lines 222-362)

Entry point. Parses a complete SELECT query in this order:

1. **PREFIX / BASE loop** (lines 228-258) — zero or more PREFIX and BASE declarations. BASE registers as the empty-string prefix for relative IRI resolution.
2. **SELECT** (line 261) — required keyword
3. **DISTINCT** (lines 263-266) — optional modifier
4. **Variable list** (lines 268-283) — either `*` or a list of `?var` tokens
5. **WHERE { ... }** (lines 285-293) — `WHERE` keyword is optional (per SPARQL spec), `{` is required. Delegates body to `parse_where_body()`.
6. **ORDER BY** (lines 296-329) — optional. Accepts `ASC(?var)`, `DESC(?var)`, or bare `?var` (defaults to ASC).
7. **LIMIT** (lines 332-340) — optional integer
8. **OFFSET** (lines 343-351) — optional integer

Returns `ParsedQuery`.

### `parse_where_body()` (lines 364-491)

Parses the content between `{` and `}`. Loops until it sees `}`, dispatching on the current token:

- **FILTER** (lines 372-391) — consumes keyword, handles both `FILTER(expr)` and `FILTER expr` forms, calls `parse_filter()`, skips optional trailing `.`
- **OPTIONAL** (lines 392-401) — consumes keyword, expects `{`, recurses into `parse_where_body()`, expects `}`
- **UNION** (lines 402-412) — handles the case where `UNION` appears after a preceding clause. Parses `{ body }` and emits `WhereClause::Union`
- **Sub-group `{`** (lines 413-441) — an inner `{ ... }` block. After parsing, peeks for `UNION`:
  - If UNION follows: collects all `{ } UNION { }` branches into `WhereClause::UnionGroup`
  - Otherwise: inlines the sub-group's clauses into the current level
- **Triple pattern** (lines 442-487) — parses three `PatternElement`s (subject, predicate, object). Then handles:
  - `,` (comma) — object list shorthand: same subject+predicate, new object
  - `;` (semicolon) — property list shorthand: same subject, new predicate+object. Nested `,` within `;` is also handled.
  - Optional trailing `.`

### `parse_pattern_element()` (lines 493-596)

Parses a single subject/predicate/object position. Dispatches by first character:

| Token starts with | Result |
|---|---|
| `?` or `$` | `Variable` |
| `a` (exactly) | IRI for `rdf:type` |
| `<...>` | `Iri` (angle brackets stripped) |
| `"` or `'` | `Literal` with optional `@lang` or `^^datatype` lookahead. Handles triple-quoted strings (lines 510-520) and prefixed datatypes like `xsd:integer` (line 529) |
| `true` / `false` | Boolean literal with `xsd:boolean` datatype |
| digit / `+` / `-` | Numeric literal; datatype inferred as `xsd:integer`, `xsd:decimal`, or `xsd:double` based on presence of `.` or `e`/`E` |
| contains `:` | `PrefixedName(prefix, local)` |
| `[]` or `[` | Anonymous blank node treated as a fresh variable (`__bnode_N`). Property lists inside `[...]` are skipped (lines 581-591) |

### `parse_filter()` / `parse_filter_or()` / `parse_filter_and()` (lines 598-619)

Standard precedence-climbing parser for boolean filter expressions:

- `parse_filter()` delegates to `parse_filter_or()`
- `parse_filter_or()` — left-associative `||` chain, calls `parse_filter_and()`
- `parse_filter_and()` — left-associative `&&` chain, calls `parse_filter_primary()`

### `parse_filter_primary()` (lines 622-768)

Parses a single filter atom. Tries in order:

1. **`!`** (line 626) — logical NOT, recurses
2. **`(`** (line 632) — parenthesized sub-filter
3. **Named functions** (lines 640-714):
   - `BOUND(?var)` — variable argument
   - `ISLITERAL(expr)`, `ISIRI(expr)` / `ISURI(expr)`, `ISBLANK(expr)` — expr argument
   - `REGEX(expr, "pattern" [, "flags"])` — string pattern + optional flags
   - `CONTAINS(a, b)`, `STRSTARTS(a, b)`, `STRENDS(a, b)` — two expr arguments
4. **Comparison or arithmetic** (lines 716-768):
   - Parses left-side `FilterExpr` via `parse_filter_expr()`
   - If next token is a comparison operator (`=`, `!=`, `<`, `>`, `<=`, `>=`): parses right-side and returns `Filter::Comparison`
   - If next token is arithmetic (`+`, `-`, `*`, `/`): parses right operand, then checks for a trailing comparison operator. If found, wraps the arithmetic in the left side of the comparison. If not, returns `BooleanEffectiveValue` of the arithmetic expression
   - If no operator follows: returns `BooleanEffectiveValue(expr)`

### `parse_filter_expr()` (lines 770-837)

Parses a value-producing expression (not boolean-valued). Handles:

- `STR(expr)`, `LANG(expr)`, `DATATYPE(expr)` — function calls (lines 775-795)
- Variables (`?x`, `$x`) — line 798
- String literals (`"..."`, `'...'`) — line 800, with `^^datatype` and `@lang` consumed but datatype information currently discarded (returns `StringLit`)
- IRI literals (`<...>`) — line 817
- Boolean keywords (`true`, `false`) — line 821, returned as `StringLit`
- Numeric values — line 823, parsed as `f64` into `NumericLit`
- Prefixed names — line 829, returned as `StringLit` (not resolved to full IRI)

**Important limitation:** `parse_filter_expr()` does not handle arithmetic. Arithmetic is only parsed in `parse_filter_primary()` when it appears between a left expression and a comparison operator. This means nested arithmetic like `STR(?x + 1)` will fail.

## 5. Evaluator

### `resolve_element()` (lines 946-973)

Expands `PrefixedName` to full IRI using the prefix map. Also resolves prefixed datatypes on `Literal` elements (e.g., `xsd:integer` to the full XSD IRI).

### `match_element()` (lines 975-1016)

Matches a single `PatternElement` against a `TermValue`:

- `Variable` — always matches, returns `Some(Some((name, value)))` to bind
- `Iri` — matches only `TermValue::Iri` with same string, returns `Some(None)` on success
- `Literal` — matches only `TermValue::Literal`; checks lexical, then optionally lang and datatype
- `PrefixedName` — returns `None` (should be resolved before reaching here)

Return type is `Option<Option<(String, TermValue)>>`:
- `None` — no match
- `Some(None)` — matched a constant (no new binding)
- `Some(Some(...))` — matched a variable, producing a new binding

### `match_triple()` (lines 1018-1054)

Matches a `TriplePattern` against a concrete `Triple` given existing bindings.

1. Resolves all three pattern elements via `resolve_element()`
2. Converts the triple's s/p/o to `TermValue`
3. For each position: if the pattern element is a variable already in `existing` bindings, checks consistency (line 1037-1042). Otherwise calls `match_element()`.
4. Returns `Some(new_bindings)` on success (merged with existing), `None` on failure.

### `term_to_typed()` (lines 1095-1117)

Converts `TermValue` to `TypedFilterValue` for type-aware comparison. Decision tree:

- `Iri` / `BNode` pass through
- `Literal` with `lang` -> `LangLiteral`
- `Literal` with `xsd:boolean` datatype -> `BooleanLiteral`
- `Literal` with numeric datatype (`xsd:integer`, `xsd:decimal`, `xsd:double`, `xsd:float`) -> `NumericLiteral` (parsed to `f64`)
- `Literal` with `xsd:string` -> `PlainLiteral`
- Everything else -> `TypedLiteral`

### `eval_filter_expr_typed()` (lines 1119-1186)

Evaluates a `FilterExpr` against a binding to produce a `TypedFilterValue`:

- `Variable` — looks up in binding, converts via `term_to_typed()`
- `StringLit` -> `PlainLiteral`
- `NumericLit` -> `NumericLiteral` with `xsd:integer`
- `IriLit` -> `Iri`
- `FnStr` — recursively evaluates inner, returns `PlainLiteral` of `as_string()`
- `FnLang` — only works if inner is a `Variable` bound to a `Literal`; returns the lang tag or empty string
- `FnDatatype` — only works if inner is a `Variable` bound to a `Literal`; returns datatype as `Iri`
- `Arithmetic` — evaluates both sides, coerces to `f64`, applies operator. Division by zero returns `None`. Result datatype follows promotion: double > decimal > integer.

### `typed_compare()` (lines 1190-1269)

Core SPARQL value comparison. Takes two `TypedFilterValue`s and a `CompOp`, returns `Option<bool>`:

- **Numeric vs Numeric** — f64 comparison with epsilon for equality
- **Boolean vs Boolean** — only `Eq`/`Ne` supported
- **PlainLiteral vs PlainLiteral** — string comparison, all operators
- **LangLiteral vs LangLiteral** — only `Eq`/`Ne`, both lexical and lowercase lang must match
- **IRI vs IRI** — string comparison, all operators
- **BNode vs BNode** — only `Eq`/`Ne`
- **TypedLiteral vs TypedLiteral** — if same datatype, lexical comparison; different datatypes return `None` (type error)
- **Cross-type** — returns `None` (incomparable)

Returning `None` means "type error", which `eval_filter()` treats as `false` (line 1281).

### `eval_filter()` (lines 1275-1391)

Evaluates a `Filter` against a binding, returning `bool`:

- `Comparison` — evaluates both sides as typed, calls `typed_compare()`, defaults to `false` on type error or missing values
- `And` / `Or` / `Not` — standard boolean logic (short-circuiting via Rust's `&&` and `||`)
- `BooleanEffectiveValue` — implements SPARQL's EBV rules (lines 1288-1324):
  - For variables: checks term type — boolean `"true"`/`"1"` is true, numeric non-zero is true, non-empty string is true, IRI/BNode is true, unbound is false
  - For other expressions: evaluates to string, treats empty/`"0"`/`"false"` as false
- `FnBound` — `binding.contains_key(var)`
- `FnIsLiteral` / `FnIsIri` / `FnIsBlank` — pattern match on `TermValue` variant. Only works for variable arguments (non-variable always returns false).
- `FnRegex` — uses `regex::RegexBuilder`, supports `i` (case-insensitive), `s` (dot-matches-newline), `m` (multi-line) flags. Invalid regex pattern silently returns false.
- `FnContains` / `FnStrStarts` / `FnStrEnds` — evaluate both args to strings, apply Rust string methods

### `evaluate_clauses()` (lines 1393-1452)

The core evaluation loop. Takes a slice of `WhereClause`s, a graph, initial bindings, and prefixes. Processes clauses sequentially, updating the result set:

- **Pattern** (lines 1403-1413) — for each existing binding, scans *all* triples in the graph and attempts `match_triple()`. This is a nested loop join: O(bindings * triples) per pattern. Successful matches produce new bindings; failed matches are discarded.
- **Filter** (lines 1415-1417) — `results.retain(|b| eval_filter(filter, b))` — removes non-matching bindings in place.
- **Optional** (lines 1418-1430) — for each binding, recursively evaluates the inner clauses. If inner evaluation produces results, they replace the original binding (left outer join). If inner evaluation is empty, the original binding is kept unchanged.
- **Union (legacy)** (lines 1431-1436) — evaluates right branch from scratch (empty binding) and appends results to current set.
- **UnionGroup** (lines 1437-1447) — evaluates each branch starting from the current result set, then unions all branch results together.

## 6. Public API

### `execute()` (lines 1466-1564)

The sole public entry point. Flow:

1. **Parse** — `Parser::new(query_str)` tokenizes, then `parser.parse_query()` produces a `ParsedQuery`
2. **Evaluate** — `evaluate_clauses()` with initial binding of one empty `HashMap`
3. **Determine output variables** — if `SELECT *`, collects all variable names seen across all bindings and sorts alphabetically (lines 1474-1488)
4. **ORDER BY** — stable sort using `TermValue::sort_key()` with `Ordering::reverse()` for DESC (lines 1491-1512). Unbound variables sort after bound ones.
5. **DISTINCT** — linear scan deduplication: builds display rows and checks against a `seen` list (lines 1515-1529). O(n^2) due to `Vec::contains`.
6. **OFFSET** — slice from offset onward (lines 1532-1538)
7. **LIMIT** — truncate (lines 1541-1543)
8. **Format** — converts bindings to `Vec<Vec<Option<String>>>` using `TermValue::display()` (lines 1546-1553)

Returns `Result<QueryResult, String>`.

## 7. Known Limitations & Extension Points

### Not Implemented

| Feature | SPARQL spec | Where to add |
|---------|-------------|--------------|
| **GRAPH** keyword | Named graph patterns | `WhereClause` enum + `parse_where_body()` + `evaluate_clauses()`. Would need graph-aware dataset model. |
| **BIND** | `BIND(expr AS ?var)` | `WhereClause::Bind` + `parse_where_body()` (check for `BIND` keyword) + `evaluate_clauses()` (add binding to each row) |
| **VALUES** | `VALUES (?x) { (1) (2) }` | `WhereClause::Values` + parser + evaluator (inject bindings) |
| **Aggregates** | `COUNT`, `SUM`, `AVG`, `MIN`, `MAX`, `GROUP_CONCAT`, `SAMPLE` | Need `GROUP BY` + `HAVING` support in `ParsedQuery`, aggregate expression type in `FilterExpr`, post-evaluation grouping step in `execute()` |
| **GROUP BY / HAVING** | Grouping modifier | `ParsedQuery` fields + parsing after `}` + grouping step between evaluation and ORDER BY |
| **Property paths** | `*`, `+`, `?`, `|`, `/`, `^` on predicates | `PatternElement::PropertyPath` variant + recursive/iterative expansion in evaluator |
| **Sub-SELECT** | `SELECT ... { SELECT ... { } }` | Detect `SELECT` token in `parse_where_body()`, recursively parse inner query, evaluate as sub-query |
| **SELECT expressions** | `SELECT (?x + 1 AS ?y)` | Extend variable parsing in `parse_query()` to accept `(expr AS ?var)`, apply after evaluation |
| **CONSTRUCT / ASK / DESCRIBE** | Query forms | Detect query form before `parse_query()`, different output handling |
| **Casting functions** | `xsd:integer(...)`, `xsd:string(...)` | `FilterExpr::Cast(target_type, inner)` + type conversion logic |
| **REDUCED** | Like DISTINCT but implementation-defined | Flag in `ParsedQuery` + optional dedup in `execute()` |
| **Unary minus** | `-?x` in expressions | Handle in `parse_filter_expr()` when first char is `-` followed by a non-digit |
| **IN / NOT IN** | `?x IN (1, 2, 3)` | `Filter::In(expr, Vec<FilterExpr>)` + parser + evaluator |
| **List patterns** | `( :a :b :c )` in triple patterns | Expand to `rdf:first`/`rdf:rest` chain in parser |
| **EXISTS / NOT EXISTS** | Existence sub-patterns | Already partially present via `Filter::Not` + the W3C test results show 3/6 EXISTS passing. Would need `Filter::Exists(Vec<WhereClause>)` for full support |
| **MINUS** | Set difference | `WhereClause::Minus` + evaluator subtracting matching rows |
| **String functions** | `STRLEN`, `SUBSTR`, `UCASE`, `LCASE`, `ENCODE_FOR_URI`, `CONCAT`, `REPLACE`, `STRAFTER`, `STRBEFORE` | Add to `Filter` enum (boolean-valued) or `FilterExpr` (value-producing) as appropriate |
| **Numeric functions** | `ABS`, `ROUND`, `CEIL`, `FLOOR`, `RAND` | `FilterExpr` variants |
| **Date/time functions** | `NOW`, `YEAR`, `MONTH`, `DAY`, etc. | `FilterExpr` variants + chrono parsing |
| **Hash functions** | `MD5`, `SHA1`, `SHA256`, `SHA384`, `SHA512` | `FilterExpr` variants |
| **IRI functions** | `IRI()`, `URI()`, `BNODE()`, `STRDT()`, `STRLANG()` | `FilterExpr` variants |
| **IF / COALESCE** | Conditional expressions | `FilterExpr::If(cond, then, else)` |

### Architectural Limitations

- **No indexing** — BGP evaluation scans all triples for every pattern (line 1406). For large graphs, consider a triple index (SPO, POS, OSP) in `RdfGraph`.
- **O(n^2) DISTINCT** — uses `Vec::contains` (line 1522). Switch to `HashSet` for large result sets.
- **Tokenizer handles `"` but not `'`** — single-quoted strings fall through to the word branch.
- **No expression arithmetic in `parse_filter_expr()`** — arithmetic is only parsed in `parse_filter_primary()` between a left expr and a comparison. Nested arithmetic (e.g., `STR(?x + 1)`) will fail.
- **Prefixed names in filter expressions** are returned as `StringLit` (line 831) rather than resolved to IRIs. Comparing `foaf:Person` in a FILTER won't work unless the full IRI is used.
- **`FnLang` and `FnDatatype`** only work when the inner expression is a `Variable` (lines 1130, 1141). Nested expressions like `LANG(STR(?x))` will return empty/None.

## 8. Common Patterns for Adding Features

### Adding a New FILTER Function

Example: adding `STRLEN(?x)` as a value-producing function.

**Step 1: Add to `FilterExpr` enum** (line 128):
```rust
enum FilterExpr {
    // ... existing variants ...
    FnStrLen(Box<FilterExpr>),
}
```

**Step 2: Parse it in `parse_filter_expr()`** (around line 774, in the `match upper.as_str()` block):
```rust
"STRLEN" => {
    self.next()?;
    self.expect("(")?;
    let inner = self.parse_filter_expr()?;
    self.expect(")")?;
    Ok(FilterExpr::FnStrLen(Box::new(inner)))
}
```

**Step 3: Evaluate it in `eval_filter_expr_typed()`** (around line 1119):
```rust
FilterExpr::FnStrLen(inner) => {
    let v = eval_filter_expr_typed(inner, binding)?;
    let len = v.as_string().len() as f64;
    Some(TypedFilterValue::NumericLiteral(len, XSD_INTEGER.to_string()))
}
```

If the function is boolean-valued (like `SAMETERM`), add it to the `Filter` enum instead, parse it in `parse_filter_primary()`, and evaluate it in `eval_filter()`.

### Adding a New Boolean FILTER Function

Example: adding `SAMETERM(?x, ?y)`.

**Step 1: Add to `Filter` enum** (line 111):
```rust
enum Filter {
    // ... existing variants ...
    FnSameTerm(FilterExpr, FilterExpr),
}
```

**Step 2: Parse in `parse_filter_primary()`** (around line 640, in the `match upper.as_str()` block):
```rust
"SAMETERM" => {
    self.next()?;
    self.expect("(")?;
    let a = self.parse_filter_expr()?;
    self.expect(",")?;
    let b = self.parse_filter_expr()?;
    self.expect(")")?;
    return Ok(Filter::FnSameTerm(a, b));
}
```

**Step 3: Evaluate in `eval_filter()`** (around line 1275):
```rust
Filter::FnSameTerm(a, b) => {
    // SAMETERM requires exact match (same term type + same value)
    match (eval_filter_expr_typed(a, binding), eval_filter_expr_typed(b, binding)) {
        (Some(av), Some(bv)) => /* compare type + value */,
        _ => false,
    }
}
```

### Adding a New WHERE Clause Type

Example: adding `BIND(expr AS ?var)`.

**Step 1: Add to `WhereClause` enum** (line 162):
```rust
enum WhereClause {
    // ... existing variants ...
    Bind(FilterExpr, String), // expression, variable name
}
```

**Step 2: Parse in `parse_where_body()`** (around line 371, add a new `else if` branch):
```rust
} else if upper == "BIND" {
    self.next()?; // BIND
    self.expect("(")?;
    let expr = self.parse_filter_expr()?;
    self.expect("AS")?;
    let var = self.next()?;
    if !var.starts_with('?') {
        return Err(format!("BIND AS expects variable, got '{var}'"));
    }
    self.expect(")")?;
    if self.peek() == Some(".") { self.next()?; }
    clauses.push(WhereClause::Bind(expr, var[1..].to_string()));
```

**Step 3: Evaluate in `evaluate_clauses()`** (around line 1401, add a new match arm):
```rust
WhereClause::Bind(expr, var_name) => {
    for binding in &mut results {
        if let Some(val) = eval_filter_expr_typed(expr, binding) {
            let term_val = /* convert TypedFilterValue back to TermValue */;
            binding.insert(var_name.clone(), term_val);
        }
    }
}
```

### Adding a New FilterExpr Variant

When adding a new `FilterExpr` variant, you must update three places:

1. **`FilterExpr` enum** (line 128) — add the variant
2. **`parse_filter_expr()`** (line 770) — add parsing logic
3. **`eval_filter_expr_typed()`** (line 1119) — add evaluation logic

If the new variant can appear as a standalone boolean test (not just inside a comparison), also consider whether `BooleanEffectiveValue` handles it correctly in `eval_filter()` (line 1288).

### Test Patterns

Unit tests live in the `mod tests` block (line 1566). The standard pattern:

1. Build a graph with `test_graph()` (4 triples) or construct a custom one
2. Call `execute(&g, "SPARQL query string")`
3. Assert on `r.rows.len()`, `r.variables.len()`, or specific cell values via `r.rows[i][j].as_ref().unwrap()`

The W3C conformance tests live separately in `rdf-wasm/tests/w3c_sparql.rs` and use the manifest-driven harness described in `docs/skills/testing.md`.
