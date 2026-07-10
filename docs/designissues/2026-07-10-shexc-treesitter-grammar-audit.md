# ShExC grammar-coverage audit: tree-sitter-shexc vs Parser.ShExC

Date: 2026-07-10.
Inputs: `third_party/tree-sitter-shexc/src/grammar.json` (92 named
productions, vendored at upstream commit `27fcb96e` — see
`third_party/tree-sitter-shexc/PROVENANCE.md`) and
`formal/fstar/Parser.ShExC.fst` (the F\*-implemented ShExC parser,
Stage 9 of the ShEx program) targeting `formal/fstar/ShEx.Schema.fst`'s
`shex_schema` AST. Spec references are to the ShExC grammar in
[ShEx 2.1 § Shape Expressions Compact Syntax](https://shex.io/shex-semantics/#shexc)
by production anchor (`#prod-<name>`).

Purpose: a scoping artifact for the three-way differential probe
(`tests/shexc-treesitter/run.sh`). The table walks every named
production in the tree-sitter grammar and records how Parser.ShExC
handles the same construct, flagging (a) constructs tree-sitter parses
that we cannot parse or represent, and (b) constructs we accept that
its grammar has no production for.

Verdict summary (details in the table and the two flag sections):

- 3 grammar features tree-sitter has that Parser.ShExC rejects
  (RESTRICTS, `&`-spelled EXTENDS with full inline-shape targets,
  `,` as a triple-expression separator) — all outside the shexTest
  schemas/ corpus, all absent from `ShEx.Schema.fst`'s AST except
  EXTENDS-by-ref.
- 2 lexical families where tree-sitter is stricter (regex escape
  whitelist; value-set entries limited to `_iri`, excluding `a` and
  blank nodes) — both were Parser.ShExC permissiveness bugs surfaced
  by the negativeSyntax suite and fixed in this landing.
- 2 families where tree-sitter is more permissive than the suite
  demands (duplicate facets; `"str"^^dt` as a numeric-facet value;
  numeric facets on unknown datatypes) plus 1 it cannot express
  (undeclared-prefix rejection, a context-sensitive check no
  context-free grammar performs) — these are exactly the fixtures
  tree-sitter wrongly accepts in the three-way table.

## Production-by-production table

Column 2 names the Parser.ShExC function (all in
`formal/fstar/Parser.ShExC.fst`) or tokenizer branch that renders the
production; column 3 records AST target + divergences.

| tree-sitter production | our handling | notes |
|---|---|---|
| `shex_doc` | `parse_statements` / `parse_shexc_schema` | Same shape: directive*, then statements. Spec `#prod-shexDoc`. |
| `_directive` | `parse_directives` | PREFIX / BASE / IMPORT, case-insensitive, interleavable between statements in both. |
| `base_decl` | `parse_directives` `TK_KW "BASE"` branch | Both SPARQL-style (no trailing dot). Resolved into `turtle_state.base_iri`. |
| `prefix_decl` | `parse_directives` `TK_KW "PREFIX"` branch | Ours requires `ST_PName ns ""` (a PNAME_NS) then IRIREF — same as `pname_ns` + `irireference`. |
| `import_decl` | `parse_directives` `TK_KW "IMPORT"` branch | Ours stores the target verbatim (`raw_shexc_term`), matching ShExJ `imports`; tree-sitter just parses. |
| `_not_start_action_or_start_actions`, `_not_start_action`, `_statement` | `parse_statement` | Same statement family (START / shapeExprDecl / startActs / directive). |
| `start` | `parse_statement` `TK_KW "START" :: TK_EQ` branch | `sch_start`. Spec `#prod-start`. |
| `start_actions` | `parse_statement` `TK_SEMACT` branch | `sch_start_acts`. |
| `shape_expr_decl` | `parse_statement` label branches | ABSTRACT supported (`sd_is_abstract`); label = IRI/PNAME/bnode; EXTERNAL supported (`SE_ShapeExternal`). **`restricts` field: not supported by us — see flag R1.** |
| `_shape_external` | `TK_KW "EXTERNAL"` | `SE_ShapeExternal`. |
| `restriction` | **not supported** | Flag R1 below. |
| `_shape_expr` | `parse_shape_expression` | Entry into the OR/AND/NOT/atom chain. |
| `shape_or` / `inline_shape_or` | `parse_shape_or` / `parse_shape_or_rest` | Tree-sitter builds binary left-assoc nodes; we flatten one bare chain to N-ary `SE_ShapeOr` (ShExJ shape). Same language. |
| `shape_and` / `inline_shape_and` | `parse_shape_and` / `parse_shape_and_rest` | Same, N-ary `SE_ShapeAnd`; parenthesized sub-chains stay nested in both. |
| `shape_not` / `inline_shape_not` | `parse_shape_not` | `SE_ShapeNot`. |
| `shape_atom` / `inline_shape_atom` | `parse_shape_atom` | Both support nodeConstraint⋈shapeOrRef juxtaposition (implicit AND), parens, `.` wildcard. Tree-sitter splits lit/non-lit constraints in the grammar itself (only non-lit may juxtapose); we enforce the same restriction in `parse_optional_shape_or_ref_suffix` gated by `nc_is_non_literal` (added by the negativeSyntax landing — previously any constraint could take a ref suffix, wrongly accepting `1datatypeRef1` etc.). |
| `_shape_or_ref` / `_inline_shape_or_ref` | `parse_optional_shape_or_ref_suffix`, `parse_shape_atom` ref branches | shapeDefinition or `@`-ref. |
| `inline_shape_expression` | `parse_inline_shape_expression` | Alias of the same chain in both (tree-sitter's inline variants differ only in where annotations/semActs attach). |
| `shape_ref` | tokenizer `@`-fusing + `TK_AT_TERM`/`TK_AT` branches | `SE_Ref`. Both accept `@<iri>`, `@pfx:l`, `@_:b`, and whitespace after `@`. |
| `_non_lit_node_constraint` | `parse_node_constraint_only` (nodeKind/string-facet paths) | nodeKind IRI/BNODE/NONLITERAL + string facets. Tree-sitter attaches annotations/semActs inside the constraint node; ours attach at the tripleConstraint level — an AST-placement difference with no language difference for the corpus. |
| `_lit_node_constraint` | `parse_node_constraint_only` (LITERAL/datatype/valueSet/numeric-facet paths) | LITERAL + xsFacets, datatype + xsFacets, valueSet + xsFacets, bare numericFacet+. Facet-flavor separation (string facets ↛ literal-only constraints, numeric facets ↛ non-lit constraints) enforced by us post-parse in `nc_facets_wellformed`; tree-sitter encodes it structurally. |
| `node_kind` | `TK_KW "IRI"/"BNODE"/"NONLITERAL"` | `ShexNK_*`. Tree-sitter's node_kind excludes LITERAL (it lives in `_lit_node_constraint`), same split we enforce. |
| `_x_facet`, `string_facet`, `string_length_kw` | `parse_facets` LENGTH/MINLENGTH/MAXLENGTH/PATTERN/regex branches | Both require INTEGER values for length facets. Duplicate-facet rejection: ours rejects a repeated facet (per `#prod-xsFacet` note and the negativeSyntax suite, e.g. `1iriLength2`); **tree-sitter's `repeat($.string_facet)` accepts duplicates — probe divergence D1.** |
| `numeric_facet`, `numeric_range_kw`, `numeric_length_kw` | `parse_facets` MIN/MAX-INCLUSIVE/EXCLUSIVE, TOTALDIGITS/FRACTIONDIGITS branches | Ours requires a numeric literal after a range keyword and an integer after a length keyword (spec `#prod-numericFacet`); ours also rejects numeric facets on non-numeric datatypes (`1unknowndatatypeMaxInclusive`). |
| `_raw_numeric` | `TK_NUMBER` only | **Tree-sitter additionally accepts `string '^^' iri` as a numeric-facet value** (e.g. `MININCLUSIVE "V"^^<roman>`), which the spec's `#prod-numericFacet` (numericLiteral only) and the negativeSyntax suite (`1decimalMininclusiveroman-numeral` and 3 siblings) both reject — probe divergence D2. |
| `value_set` | `parse_value_set` | `[ valueSetValue* ]` → `nc_values`. |
| `_value_set_value`, `_exclusions` | `parse_value_set_value`, `parse_exclusions`, `dot_exclusion_kind` | IRI/literal/language ranges + the `. exclusion+` wildcard form, kind-disambiguated the same way. Tree-sitter restricts entry heads to `_iri`/`literal`/`langtag`; ours now rejects blank nodes and the bare `a` keyword in value sets (previously accepted — negativeSyntax `1val1bnode`, `1valA`). |
| `iri_stem_range`, `iri_exclusion` | `parse_value_set_value` TERM/TILDE branches, `parse_exclusion` | `VSV_IriStem(Range)`. |
| `literal_stem_range`, `literal_exclusion` | STRING/TILDE branches | `VSV_LiteralStem(Range)`. |
| `language_stem_range`, `language_exclusion` | LANGTAG/TILDE branches (incl. `@~` empty-stem form) | `VSV_LanguageStem(Range)`. |
| `shape_definition` / `inline_shape_definition` | `parse_shape_definition` / `parse_shape_modifiers` | Modifiers (EXTRA/CLOSED/EXTENDS)*, `{ tripleExpr? }`, then annotations + semActs. Same structure. |
| `_shape_definition_modifier`, `_closed_kw` | `parse_shape_modifiers` | CLOSED → `sh_closed`; repeated EXTRA lists concatenate in both. |
| `extension` | `TK_KW "EXTENDS" :: TK_AT_TERM/TK_AT TK_TERM` | **Divergence: tree-sitter accepts `&` as an EXTENDS synonym and a full `_inline_shape_expr` target; ours only `EXTENDS @<ref>`** — flag R2. `sh_extends` holds label strings only, matching ShExJ's `extends: [shapeExprRef]`. |
| `extra_property_set` | `parse_predicate_list1` | EXTRA predicate+ → `sh_extra`. |
| `triple_expression`, `_one_of_triple_expr` | `parse_one_of_triple_expr` | `|`-separated groups → `TE_OneOf` (only when ≥2 members, matching ShExJ). |
| `one_of` | `parse_one_of_rest` | Same. |
| `group_triple_expr` | `parse_group_triple_expr` / `parse_group_rest` | `;`-separated with optional trailing separator. **Tree-sitter also accepts `,` as a separator; the spec's `#prod-groupTripleExpr` and our parser accept only `;`** — flag R3/D3. |
| `_unary_triple_expr` | `parse_unary_triple_expr` | `$label` prefix, tripleConstraint, bracketed, `&`-include. |
| `bracketed_triple_expr` | `parse_unary_body` LPAREN branch | Cardinality/annotations/semActs land on the inner group's own slots (ShExJ shape); tree-sitter keeps them as siblings. Same language. |
| `triple_constraint` | `parse_triple_constraint` | senseFlag `^`, predicate, value expr, cardinality, annotations, semActs → `shex_triple_constraint`. Bare `.` value omits `tc_value_expr` (ShExJ quirk) — tree-sitter always materializes `inline_shape_expression`; AST difference only. |
| `cardinality`, `repeat_range` | `parse_optional_cardinality`, `sc_try_repeat_range` | `*`/`+`/`?`/`{m}`/`{m,n}`/`{m,}`/`{m,*}`. Both tokenize the brace form lexically (ours in `sc_try_repeat_range`, theirs as a `token(...)` regex). |
| `include` | `TK_AMP` branches in `parse_unary_triple_expr` | `TE_Ref`. Ours also accepts `& @<ref>` (corpus fixture form); tree-sitter's `include` takes a bare label but its `extension` rule separately claims `& <inline-shape>` at modifier position. |
| `annotation` | `parse_annotations` | `// pred (iri\|literal)` → `shex_annotation`. |
| `semantic_actions`, `code_decl` | `parse_semacts`, tokenizer `%`-branch (`sc_scan_code_body`) | `%iri{...%}` and the no-code `%iri%` form; `\%`/`\\`/UCHAR escapes decoded. Tree-sitter's `code` token regex admits the same escape family. |
| `shape_expr_label`, `triple_expr_label` | `resolve_shexc_term` on `TK_TERM` | IRI or blank node; literals rejected in both (`1val1vcrefSTRING_LITERAL1`). |
| `predicate` | `TK_TERM` + tokenizer `a`-shorthand | `a` → rdf:type allowed at predicate position ONLY in both (tree-sitter: `predicate` is the only rule referencing `kw_a`; ours: value-set/label positions reject `ST_Iri rdf:type` produced by the bare-`a` token — fixed in this landing). |
| `datatype`, `_iri`, `irireference` | `sc_scan_iriref_term` (reusing `scan_iri_ref_span`) | IRIREF charset per spec (`#term-IRIREF`): control chars, space, `<>"{}|^\`\\` excluded; UCHAR allowed — both enforce (tree-sitter by regex, ours via `contains_forbidden_iri_char` + UCHAR validation in the Turtle scanner). |
| `prefixed_name`, `pname_ns`, `pname_ln` | `parse_prefixed_name` (Parser.Turtle) | PN_CHARS/PN_LOCAL rules incl. `%XX` and `\`-escapes, dot-position rules. Ours additionally requires the prefix to be *declared* (`resolve_prefixed_name` → None ⇒ reject), which a context-free grammar cannot — tree-sitter accepts `prefix-none`/`prefix-missing` (probe divergence D4). |
| `blank_node` | `parse_bnode` (Parser.NTriples) | BLANK_NODE_LABEL per spec. |
| `literal`, `rdf_literal`, `lang_string` | `parse_object_value`, `parse_value_set_value` | String + optional langtag/`^^`datatype. Tree-sitter glues string+langtag into one token to disambiguate value-set `"x"@en` vs literal-then-language-stem; our tokenizer emits `TK_STRING`+`TK_LANGTAG` and the value-set parser prefers the lang-literal reading — same resolution. |
| `numeric_literal`, `integer`, `decimal`, `double` | `parse_numeric_literal` (Parser.Turtle; double-aware first, anti-pattern #8) | INTEGER/DECIMAL/DOUBLE with xsd datatype assignment. |
| `boolean_literal` | `TK_KW "TRUE"/"FALSE"` | **Case divergence: ours tokenizes keywords case-insensitively, so `TRUE`/`True` parse as booleans; tree-sitter (and the spec, `#prod-booleanLiteral`) admit lowercase `true`/`false` only.** No corpus fixture exercises it in a value position; noted as latent looseness (accepted-without-production flag A1). |
| `string`, `string_literal1/2`, `string_literal_long1/2` | `parse_turtle_string` (Parser.Turtle) | All four quote forms + ECHAR/UCHAR. Tree-sitter's single-line string regexes exclude raw control chars only for `\n`/`\r`; it still mis-rejects 4 corpus fixtures with exotic control/boundary bytes (see three-way table) — probe limitation, not ours. |
| `langtag` | tokenizer `@`+word scan (`sc_scan_langtag_end`) | Ours scans a letters/digits/hyphen superset of the spec's `@[a-zA-Z]+(-[a-zA-Z0-9]+)*` and lowercases (corpus convention); the negativeSyntax suite carries no bad-langtag fixture, so the superset is currently unobserved — flag A2. |
| `repeat_range` | `sc_try_repeat_range` | See cardinality row. |
| `regexp` | tokenizer `/`-branch (`sc_scan_regex_body`) + flags scan | `/.../ [smix]*`. Escape whitelist (`\` before `nrt\|.?*+(){}$-[]^/` or UCHAR) enforced by tree-sitter's regex; ours now enforces the same whitelist (previously passed any `\c` through verbatim — negativeSyntax `1literalPattern_with_ECHAR_escape_*`). Flags: tree-sitter pins `[smix]`; ours scans a word and stores verbatim (flag A3). |
| `code` | `sc_scan_code_body` | `{...%}` bodies with `\%`/`\\`/UCHAR. |
| `comment` | `sc_skip_ws_comments` / `sc_skip_block_comment` | `#`-line and `/* */` block comments in both. |

## Flags: tree-sitter constructs we cannot parse or represent

- **R1 — `restriction` (`RESTRICTS`/`-` shapeOrRef, on `shape_expr_decl`).**
  ShEx 2.1-extension syntax. Parser.ShExC rejects it
  (parse-and-reject-loudly), and `ShEx.Schema.fst` has no `restricts`
  slot (ShExJ 2.0 has none either). Zero occurrences in the vendored
  shexTest corpus. If the corpus ever grows RESTRICTS fixtures, this
  needs an AST extension first.
- **R2 — `extension` generality: `&` spelling and full inline-shape
  targets (`EXTENDS IRI {...}`).** We parse `EXTENDS @<ref>` only
  (list of refs, matching ShExJ `extends`); a non-ref EXTENDS target
  is unrepresentable in `sh_extends : list string`. The corpus's
  extends fixtures are all ref-shaped. Rejected loudly today.
- **R3 — `,` as a triple-expression separator** (`group_triple_expr`).
  The spec's `#prod-groupTripleExpr` uses `;` only; tree-sitter's `,`
  alternative follows shex.js's jison grammar, which tolerates commas.
  We reject `,`. No corpus fixture uses it (a negativeSyntax fixture
  rejecting it would make tree-sitter wrongly accept — none exists).
- **R4 — shapeOrRef-then-constraint juxtaposition** (`shape_atom`'s
  third alternative: `_shape_or_ref optional(_non_lit_node_constraint)`,
  spec `#prod-shapeAtom`): `@<S1> MINLENGTH 3` — the ref/definition
  first, the non-lit constraint second. We parse the reversed order
  (constraint then ref, via `parse_optional_shape_or_ref_suffix`) but
  reject this one: `parse_shape_atom`'s `TK_AT_TERM` branch returns the
  ref with no constraint-suffix attempt. Representable in the AST (the
  same implicit `SE_ShapeAnd` pair, reversed); zero corpus fixtures
  exercise it (the 433/433 differential is unaffected). Candidate
  future fix with a regression fixture first.

## Flags: things we accept that tree-sitter's grammar has no production for

- **A1 — case-insensitive `TRUE`/`FALSE` boolean literals** (spec and
  tree-sitter: lowercase only). Latent; no fixture either way.
- **A2 — langtag superset**: digits/hyphens permitted in the first
  subtag and leading-hyphen shapes are not rejected at tokenize time.
  Latent; no fixture.
- **A3 — regex flags**: we accept any word-shaped flags run
  (stored verbatim); tree-sitter pins `[smix]*`. Latent; corpus flags
  are within `[smix]`.

These three are recorded as candidate future tightenings; none is
exercised by any shexTest fixture today, so tightening them now would
be spec-conformance work without a test to pin it (the suite's
regression-pinning discipline in `skills/test-suites/SKILL.md` wants
the failing test first).

## Probe divergences (tree-sitter wrongly accepts / rejects)

Anchored by the three-way run (`tests/shexc-treesitter/run.sh`,
results in the landing's results log):

- **D1 — duplicate facets accepted** (`repeat($.string_facet)` /
  `repeat($._x_facet)`): wrongly accepts `1iriLength2`,
  `1literalLength2`.
- **D2 — `string^^iri` as numeric-facet value** (`_raw_numeric`):
  wrongly accepts the 4 `*Mininclusiveroman-numeral` fixtures. Its
  grammar deliberately over-approximates here (facet-value typing is
  semantic in shex.js); the spec grammar's `numericFacet` admits
  `numericLiteral` only, so these are candidate upstream grammar
  issues.
- **D2b — numeric facet on unknown datatype**: `1unknowndatatypeMaxInclusive`
  (`<dt1> MAXINCLUSIVE 5`) is context-sensitive (is `dt1` numeric?);
  tree-sitter accepts, the suite expects reject. Same
  over-approximation family as D2.
- **D4 — undeclared prefixes accepted** (`prefix-none`,
  `prefix-missing`): prefix declaration tracking is context-sensitive;
  a pure CFG probe cannot reject these. Expected limitation, not an
  upstream bug.
- **D5 — 4 positive fixtures wrongly rejected**
  (`1literalPattern_with_all_controls`,
  `1literalPattern_with_ascii_boundaries`,
  `1val1STRING_LITERAL1_with_all_controls`,
  `1val1STRING_LITERAL1_with_ascii_boundaries`): raw control bytes
  inside single-line string literals. The spec's STRING_LITERAL1/2
  exclude only the quote, backslash, `\n`, `\r`; tree-sitter's
  tokenizer appears to choke on other raw control bytes. Candidate
  upstream issue.
