# 2026-04-25 — xsd:float / xsd:decimal cast canonical lexical form

## Failing tests (cast suite, after Wave 2 = 1590/1600)

```
FAIL: xsd:float cast    — expected 31, got 31 (16 rows differ)
FAIL: xsd:decimal cast  — expected 31, got 31 (2 rows differ — n09, n10)
```

## Diagnosis

Two distinct issues:

### A. xsd:float cast emits non-canonical lex forms (eval_xsd_cast in SPARQL11.Algebra.fst)

For `target_type = "float"` (line ~2119) we currently emit:
- `ER_Bool true` → `"1.0E0"`  ✓ matches expected b01
- `ER_Bool false` → `"0.0E0"` ✗ expected `"0E0"` (b02, b03)
- `ER_Num n` → `string_of_int n ^ ".0E0"` ✗ expected `"1.0"`, `"-1.0"`, but `0`→`"0"` (n01, n02, n03)
- `ER_Dbl s` (xsd:double or xsd:float input with E-notation, e.g. `"0E1"`, `"1E0"`) → preserves lex ✗ expected `"0.0"`, `"1.0"` (n07, n08, n09, n10)
- string `"0.0"` → preserves ✗ expected `"0E0"` (s05)
- string `"-10.2E3"` → preserves ✗ expected `"-1.02E4"` (s03)
- string `"+33.3300"` → preserves (after strip_leading_plus → `"33.3300"`) ✗ expected `"3.333E1"` (s04)
- string `"0E1"` → preserves ✗ expected `"0E0"` (s07)
- string `"1.5"` → preserves ✗ expected `"1.5E0"` (s08)

Pattern is the canonical xsd:float form ARQ-style:
- when value is an integer that comes via integer-form input → preserve integer lex
- when value is integer-valued from numeric input (ER_Num 1) → `"1.0"`
- when value is integer 0 from ER_Num 0 → `"0"`
- when input has E-notation → re-canonicalize to mantissa-in-[1,10)·10^exp, OR plain `"X.0"` for integer values
- bool false → `"0E0"`, bool true → `"1.0E0"`

### B. xsd:float source value preserves lex form across `?v` projection (cast-decimal n09, n10)

`?v` is bound directly in WHERE and propagates through SELECT projection unchanged. For
input data `:n09 :p "0E1"^^xsd:float`, the SRX expects `?v="0.0"^^xsd:float`. Our store
preserves `"0E1"`. Comparison fails because `numeric_literal_equal` in
`w3c_runner.ml` only handles xsd:double / xsd:decimal / xsd:integer — not xsd:float.

## Plan

### Step 1 (this commit): xsd:float canonical form in cast (F* fix)

Targeted edits in `eval_xsd_cast`, `target_type = "float"` branch (~line 2119):

- `ER_Bool false` → `"0E0"` (not `"0.0E0"`)
- `ER_Num 0` → `"0"`
- `ER_Num n` (n≠0) → `string_of_int n ^ ".0"`
- `ER_Dbl s` and string E-notation: detect integer-valued (`x.xEy` where x·10^y is integer) → emit `"<int>.0"` or `"0.0"` directly; otherwise normalize mantissa
- `ER_Term T_Literal` of plain string with `.` or `E` → re-canonicalize via parse_double_to_scaled → emit ARQ-style scientific or `"<int>.0"`

This is enough to flip cast-float from FAIL to PASS for at least the bool/integer/double-input
rows (b02, b03, n01, n02, n03, n07, n08, n09, n10). String-input rows
(s03, s04, s05, s07, s08) need a more complex scientific normalizer.

### Step 2 (this commit, decimal):

cast-decimal output is correct; failure is in `?v` (projection of xsd:float store value).
The unmatched rows (n09, n10) have decimal values `"0.0"` and `"1.0"` which match
expected — but the `?v` differs (`"0E1"` vs `"0.0"`).

Pure-F* fix routes:
- (a) canonicalize xsd:float on Turtle parse — invasive, may break other tests
- (b) canonicalize xsd:float on E_Var lookup before binding — doesn't help because projection uses raw `mu`
- (c) extend `numeric_literal_equal` in w3c_runner.ml to include xsd:float — runner I/O glue (legitimate per rule #15: result-comparison harness, not RDF semantics)

Per "Pure F* edit" directive: take route (a) but only for clearly-double-form xsd:float
literals (those with `E` or pure integer/decimal lex). Defer if it breaks other tests.

### Expected impact

- cast-float: from FAIL (16 unmatched) to PASS for at least bool/integer/double-input rows
- cast-decimal: from FAIL (2 unmatched) to PASS via float canonicalization on store-load

If only one of the two flips, accept partial fix and document remaining gap.

## Implementation notes

- `parse_double_to_scaled` returns `(int_value, scale)`: e.g. `"0E1"` → `(0, 0)` (scaled by 10^scale gives 0), `"1E0"` → `(1, 0)`, `"-10.2E3"` → `(-10200, 0)` (or scaled differently).
- Java-style `Float.toString` rule: scientific if abs(x) ≥ 10^7 or < 10^-3, else decimal.
- This patch focuses on integer-valued cases only; full ARQ-style scientific
  normalization is a follow-up.
