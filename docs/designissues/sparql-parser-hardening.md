# SPARQL Parser Hardening — Subagent Brief

## Context

SPARQL11.Parser.fst has a working parser (Part 1-8, ~2800 lines) that passes
322/408 W3C tests. A previous attempt to add improvements created a broken
second parser block (Part 9) that was removed in PR #49. Three specific
improvements from that block need to be re-implemented cleanly.

## Task: Add 3 improvements to the existing parser

### 1. EOF validation in `parse_sparql`

**Current code** (line ~2593):
```fstar
let parse_sparql (input : string) : parse_result query =
  let tokens = tokenize input in
  parse_select_query [] 10000 tokens
```

**Problem:** `parse_select_query` returns `ParseOk q remaining_tokens` but
`parse_sparql` ignores `remaining_tokens`. So `SELECT ?x { ?x ?p ?o } GARBAGE`
parses successfully — the `GARBAGE` is silently dropped.

**Fix:** Check that remaining tokens are empty or only `Tok_EOF`:
```fstar
let rec tokens_only_eof (ts : token_stream) : bool =
  match ts with
  | [] -> true
  | Tok_EOF :: rest -> tokens_only_eof rest
  | _ -> false

let parse_sparql (input : string) : parse_result query =
  let tokens = tokenize input in
  match parse_select_query [] 10000 tokens with
  | ParseOk q rest ->
    if tokens_only_eof rest then ParseOk q rest
    else ParseErr "unexpected tokens after query"
  | ParseErr msg -> ParseErr msg
```

**Constraint:** `tokens_only_eof` needs `(decreases ts)` or `(decreases
(List.Tot.length ts))` for termination. The structural decreases on `ts`
should work since `rest` is a tail of `ts`.

### 2. VALUES row count validation

**Current code:** `parse_values` (search for `GP_Values`) accepts any number
of terms per row, even if it doesn't match the variable count.

**Problem:** `VALUES (?x ?y) { (1) (1 2) }` should fail (first row has 1
term, needs 2), but the parser accepts it.

**Fix:** After parsing values data, check each row length matches the
variable list length. Add validation in the `parse_values` body after
the values data is parsed:
```fstar
let vars_len = List.Tot.length vars in
let check_row (row : list (option rdf_term)) : bool =
  List.Tot.length row = vars_len in
if List.Tot.for_all check_row rows then
  ParseOk (GP_Values vars rows) rest
else
  ParseErr "VALUES row has wrong number of terms"
```

### 3. SELECT * + GROUP BY rejection

**Current code:** `parse_select_query` accepts `SELECT * ... GROUP BY ?x`
even though SPARQL 1.1 spec forbids it.

**Problem:** "When GROUP BY is used, only variables that appear in aggregate
expressions, the GROUP BY clause, or are mentioned in HAVING may be projected.
SELECT * with GROUP BY is always an error."

**Fix:** In `parse_select_query` (or `parse_solution_modifier`), after
parsing GROUP BY, check if the select clause is `Select_All`:
```fstar
if Select_All? sc && Some? group_by then
  ParseErr "SELECT * not allowed with GROUP BY"
else ...
```

## Constraints

1. **Modify only existing functions.** Do NOT add a new "Part 9" or parallel
   implementation. Edit `parse_sparql`, `parse_values`, and the select/modifier
   handling in place.

2. **Every change must verify.** Run `fstar.exe --codegen OCaml SPARQL11.Parser.fst`
   after each change. If it fails, fix it before proceeding.

3. **No duplicate function names.** F* does not allow two top-level definitions
   with the same name, even if one is `let rec` and one is `let`. Check with
   `grep -c "^let function_name" SPARQL11.Parser.fst` before adding.

4. **F* comment safety.** Never put `*)` or `(*` inside `(* ... *)` comments.
   Use `//` line comments when writing SPARQL-related text that might contain
   these sequences.

5. **No assume val.** These three changes are pure logic — no need for
   `assume val` or ocaml-patches.sh stubs.

6. **Run full build.** After all changes:
   ```bash
   cd formal/fstar
   ./build-ocaml.sh
   ```
   This must succeed (all 12 modules extract, compile, tests run).

7. **Track test impact.** Report before/after for:
   - syntax-query suite (currently 76/94)
   - The 3 specific improvements should catch more negative syntax tests

## Where to find things

- Parser entry point: `SPARQL11.Parser.fst` line ~2593 (`parse_sparql`)
- Select query parser: search `parse_select_query`
- VALUES parser: search `GP_Values`
- Solution modifier parser: search `parse_solution_modifier`
- Token types: search `type token =` (top of file)
- Parse result type: search `type parse_result`

## Sample working F* pattern (existing code style)

```fstar
// From the existing parser — shows correct pattern for recursive descent
and parse_prologue (pm : prefix_map) (fuel : nat) (ts : token_stream)
  : Tot (parse_result (prefix_map & option wf_iri)) (decreases fuel) =
  if fuel = 0 then ParseOk (pm, None) ts
  else begin match parse_peek ts with
    | Tok_PREFIX ->
      let ts' = parse_advance ts in
      (match parse_peek ts' with
       | Tok_PNAME pn ->
         let (prefix, _) = split_pname pn in
         let ts'' = parse_advance ts' in
         (match parse_peek ts'' with
          | Tok_IRI iri ->
            if is_iri iri then
              parse_prologue ((prefix, iri) :: pm) (fuel-1) (parse_advance ts'')
            else ParseErr "invalid prefix IRI"
          | _ -> ParseErr "expected IRI after PREFIX name")
       | _ -> ParseErr "expected prefix name after PREFIX")
    | _ -> ParseOk (pm, None) ts
  end
```

Key patterns:
- `parse_result` wraps `ParseOk value remaining_tokens` or `ParseErr msg`
- `fuel : nat` with `(decreases fuel)` for termination
- `parse_peek ts` to look at current token
- `parse_advance ts` to consume one token
- Pattern match on token constructors
