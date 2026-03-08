# Scoping Document: Verified SPARQL 1.1 Query Parser in F*

## 1. Current State Analysis

### 1.1 The F* Algebra (SPARQL11.Algebra.fst, ~3000 lines)

The existing F* specification defines types at the **abstract algebra level**, not at the concrete syntax level. The key types are:

**Pattern-level types:**
- `pattern_term` (PT_Var, PT_IRI, PT_BNode, PT_Literal)
- `pattern_subject` (PS_Var, PS_IRI, PS_BNode)
- `triple_pattern` (record: tp_s, tp_p, tp_o)
- `bgp = list triple_pattern`

**Expression types (noeq type expr, ~40 constructors):**
- Covers all SPARQL 1.1 built-in functions: STR, LANG, DATATYPE, BOUND, IF, COALESCE, IN/NOT IN, string functions, numeric functions, hash functions, date/time functions, EXISTS/NOT EXISTS, aggregates, function calls.
- Numeric literals split into E_NumericLit (int), E_DecimalLit (string), E_DoubleLit (string).

**Property paths (and property_path, 8 constructors):**
- PP_IRI, PP_Inverse, PP_Sequence, PP_Alternative, PP_ZeroOrMore, PP_OneOrMore, PP_ZeroOrOne, PP_NegatedSet.

**Graph patterns (and group_graph_pattern, 12 constructors):**
- GP_BGP, GP_Join, GP_LeftJoin, GP_Filter, GP_Union, GP_Graph, GP_Minus, GP_Bind, GP_Values, GP_Service, GP_SubSelect, GP_PropertyPath, GP_Empty.

**Query structure:**
- `query` record: q_base, q_prefixes, q_form, q_dataset, q_pattern, q_group_by, q_having, q_modifier, q_values.
- `query_form`: QF_Select, QF_Construct, QF_Ask, QF_Describe.
- `solution_modifier`: order_by, distinct, reduced, offset, limit.
- `select_clause`: Select_Vars (list select_item) | Select_All.
- `dataset_clause`: DC_Default | DC_Named.

**Critical observation**: These types already represent a **nearly complete abstract syntax tree** for SPARQL 1.1 queries. They are not purely algebraic (e.g., `query` has prologue fields like `q_base` and `q_prefixes` which are syntactic, not algebraic). The types conflate CST and algebra in places, but they cover the semantic content of the grammar well.

### 1.2 The OCaml Parser (sparql_parser.ml, ~1500 lines)

The hand-written OCaml parser is a recursive-descent parser that produces the F*-extracted types directly. Coverage:

**Fully covered:**
- Prologue (PREFIX, BASE)
- SELECT queries (DISTINCT, REDUCED, projections, aliases)
- ASK queries
- CONSTRUCT queries (template + WHERE)
- WHERE clause with GroupGraphPattern
- All graph pattern forms: BGP, OPTIONAL, UNION, MINUS, FILTER, BIND, VALUES, GRAPH, SERVICE, sub-SELECT
- Full expression language: all 40+ built-in functions, aggregates, operator precedence
- Property paths (alternative, sequence, inverse, *, +, ?, negated property sets)
- Solution modifiers: GROUP BY, HAVING, ORDER BY, LIMIT, OFFSET
- Inline data (VALUES with single and multiple variables)

**Notable gaps:**
- DESCRIBE queries: not implemented
- Dataset clauses (FROM/FROM NAMED): skipped
- Collections syntax `(a b c)` in triple patterns: not implemented
- SPARQL Update: entirely absent (out of scope per CLAUDE.md)

### 1.3 The SPARQL 1.1 Grammar (173 productions)

| Category | Productions | Count |
|----------|------------|-------|
| Query structure | [1]-[2], [7]-[12] | 8 |
| Update (out of scope) | [3], [29]-[51] | 24 |
| Prologue | [4]-[6] | 3 |
| Dataset | [13]-[16] | 4 |
| Solution modifiers | [17]-[28] | 12 |
| Graph patterns | [53]-[68] | 16 |
| Triples/properties | [52], [69]-[109] | 42 |
| Expressions | [110]-[128] | 19 |
| Literals/terminals | [129]-[173] | 45 |

Excluding 24 Update productions: **149 query-relevant productions**.

## 2. F* Syntax Types Needed

### 2.1 CST vs AST Strategy

**Recommendation: Two-layer approach with a thin CST.**

The existing `query` type is already close to a CST. Main differences between concrete syntax and current types:

1. **Prefix expansion**: Concrete syntax has `PrefixedName`; the algebra has only `wf_iri`.
2. **Syntactic sugar**: Blank node property lists, collections, predicate-object shorthand.
3. **Triple grouping**: Concrete syntax has `;` and `,` separators; algebra has flat `list triple_pattern`.
4. **GroupGraphPatternSub**: Grammar interleaves TriplesBlock with GraphPatternNotTriples.

**Proposed types:**

```fstar
type cst_iri_ref =
  | CIRI_Full    : string -> cst_iri_ref
  | CIRI_Prefixed : string -> string -> cst_iri_ref

noeq type cst_triples_same_subject =
  | CTS_VarOrTerm : cst_var_or_term -> cst_property_list -> cst_triples_same_subject
  | CTS_TriplesNode : cst_triples_node -> cst_property_list -> cst_triples_same_subject

noeq type cst_triples_node =
  | CTN_Collection : list cst_graph_node -> cst_triples_node
  | CTN_BlankNodePropList : cst_property_list -> cst_triples_node
```

### 2.2 Types Reusable from Algebra

- `expr` (all 40+ constructors)
- `property_path`
- `aggregate_fn`, `comp_op`, `arith_op`
- `select_clause`, `select_item`
- `solution_modifier`, `order_condition`
- `group_condition`, `having_condition`
- `query_form`, `dataset_clause`

### 2.3 Types Needing a CST Layer

- IRI references (pre-expansion)
- Triple patterns (pre-flattening)
- GroupGraphPatternSub (pre-algebra translation)
- ConstructTemplate

## 3. Parser Architecture

### 3.1 Recommended Approach: Hand-Written Recursive Descent in F*

The SPARQL grammar is LL(1). Advantages:
- Direct correspondence between grammar productions and F* functions
- Termination proofs via decreasing input position
- Can produce CST types directly

```fstar
type parse_input = { text : string; pos : nat }

type parse_result (a:Type) =
  | Parse_OK : value:a -> remaining:parse_input -> parse_result a
  | Parse_Err : message:string -> position:nat -> parse_result a

val parse_sparql_query : input:string -> Tot (parse_result cst_query)
val elaborate : cst_query -> option query
```

### 3.2 Lexer

```fstar
type token =
  | Tok_Keyword : sparql_keyword -> token
  | Tok_IRI : string -> token
  | Tok_PName : string -> string -> token
  | Tok_Var : string -> token
  | Tok_String : string -> token
  | Tok_Integer : string -> token
  | Tok_Decimal : string -> token
  | Tok_Double : string -> token
  | Tok_LangTag : string -> token
  | Tok_BNode : string -> token
  | Tok_Symbol : sparql_symbol -> token
  | Tok_EOF : token

val tokenize : string -> Tot (list token)
```

## 4. Verification Strategy

### Properties to Prove (in priority order)

1. **Totality**: Every parser function terminates. Via F*'s `Tot` effect.
2. **Soundness**: Output is well-formed (prefixed names resolved, etc.).
3. **Elaboration correctness**: Produced `query` satisfies algebra invariants.
4. **Roundtrip** (deferred): parse(print(q)) ~ q.

### What NOT to Prove Initially

- **Completeness** against grammar (very high effort, validate empirically via W3C tests)
- **Full RFC 3987 IRI validation** (defer, use current simple `is_iri`)

## 5. Phasing

| Phase | Scope | Duration |
|-------|-------|----------|
| 1 | Lexer + Core CST (SELECT, BGP, simple expressions) | 2-3 weeks |
| 2 | Full graph patterns (OPTIONAL, UNION, MINUS, etc.) | 2-3 weeks |
| 3 | Full expression language (50+ built-in functions) | 2-3 weeks |
| 4 | Property paths | 1-2 weeks |
| 5 | Remaining query forms + modifiers | 1-2 weeks |
| 6 | Hardening + W3C validation | 2-3 weeks |
| **Total** | | **10-16 weeks** |

## 6. Effort Estimate

| Component | F* Lines (est.) | Difficulty |
|-----------|----------------|-----------|
| Token type + lexer | 300-400 | Low |
| CST types | 200-300 | None |
| Parser (all productions) | 1500-2500 | Medium-High |
| Elaboration (CST -> algebra) | 400-600 | Medium |
| Testing + hardening | -- | Low |
| **Total** | **2400-3800** | |

The verified F* version will be 2-3x larger than the unverified OCaml parser (~1500 lines), consistent with typical verified/unverified code ratios.

## 7. Key Risks

1. **Termination of mutual recursion**: Expression -> EXISTS -> GraphPattern -> SubSelect -> Expression. Mitigate with input position as decreasing metric.
2. **Unicode handling**: PN_CHARS_BASE requires Unicode range checks. Tedious but straightforward.
3. **Z3 verification time**: Keep functions small, use separate module.
4. **Interaction with `noeq` types**: Works fine for pattern matching, need explicit equality functions.

## 8. Summary Recommendation

1. Start with the lexer (most self-contained, immediate value)
2. Use existing algebra types as AST; thin CST layer only where needed
3. Verify totality first, soundness second
4. Validate empirically with W3C tests
5. Separate module: `SPARQL11.Parser.fst` (or Lexer + Parser split)

The 10-16 week estimate assumes focused effort. Phased approach delivers value incrementally: after Phase 1, basic SELECT queries parse with verified termination.
