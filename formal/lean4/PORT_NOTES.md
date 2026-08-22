# L4Factoidal — F\* → Lean 4 port notes

Scope so far: the RDF term/graph data model, the SPARQL algebra core
(solution mappings, triple patterns, BGP evaluation, §18.5 operators)
and proved invariants (goal steps 1–3, 2026-08-22); then the XML layer
— the generic XML 1.0 parser and with it the well-formedness decision,
namespace processing, and a serialiser with round-trip fixtures
(2026-08-22, see "The XML stage" below).
Everything builds with `lake build` on the pinned toolchain
(`lean-toolchain`: Lean 4.33.1); the `#guard` tests in
`L4Factoidal/Tests.lean` run at build time, so a green build is also
a green test run.

## Module correspondence

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/RDF/Core.lean` | `RDF.Term.fsti`, `RDF.Triple.fsti` | terms, literals (incl. RDF 1.2 direction + triple terms), the three literal-equality relations, reflexivity/identity theorems |
| `L4Factoidal/RDF/XmlCanon.lean` | `RDF.Term.fsti` `xmlc_*` family | rdf:XMLLiteral exclusive-c14n value equality (WebOnt-miscellaneous-202 fix) |
| `L4Factoidal/RDF/Graph.lean` | `RDF.Graph.fsti` (+ `RDF.Dataset.Merge` renaming) | graphs as lists with set-semantics ops, datasets, blank-node renaming, membership theorems |
| `L4Factoidal/SPARQL/Algebra.lean` | `SPARQL11.Algebra.fst` Parts 1–2, §7.2–7.3/§18.5, and the `eval_pattern_store` arms of §18.6 | bindings, patterns (incl. SPARQL 1.2 triple-term patterns), `tpMatch`, `evalBgp`, join/leftJoin/union/minus/filter, and the FULL `GraphPattern` constructor set — GRAPH, LATERAL, BIND, VALUES, SERVICE/SERVICE ?var, a post-processed sub-pattern (the sub-SELECT shape), property paths, the empty pattern. `GraphPattern.evalIn ds active` is the dataset-aware evaluator; `GraphPattern.eval g` is its no-named-graphs case, kept so every earlier theorem still applies |
| `L4Factoidal/SPARQL/Invariants.lean` | (new; replaces the F\* SMT-`Lemma` style) | empty-pattern laws, merge/lookup characterisation, filter/minus safety, BGP monotonicity — all kernel-checked, no solver |
| `L4Factoidal/SPARQL/PropertyPath.lean` | `SPARQL11.Algebra.fst` Part 4 (`property_path`) + Part 13 (`eval_property_path`) | §9.1 path syntax and §18.4/§9.3 evaluation to (subject, object) pairs; the two closure forms iterate to a fixed point under a node-count fuel bound, with an early stop when a round adds nothing |
| `L4Factoidal/SPARQL/Query.lean` | `SPARQL11.Algebra.fst` Parts 5, 6, 10, 11, 12 | the concrete `QueryPattern` AST (one constructor per F\* `group_graph_pattern` case), `Query`/`QueryForm`/`SelectClause`/`SelectItem`/`OrderCondition`/`SolutionModifier`/`GroupCondition`/`DatasetClause`, `QueryPattern.lower` into the algebra, §15.1 `sparqlOrder`, §18.4 DISTINCT/REDUCED/slice/project/sort, §18.5.1 grouping + the seven aggregates + HAVING, and `evalSelect`/`evalAsk`/`evalConstruct` |
| `L4Factoidal/SPARQL/QueryTheorems.lean` | (new; replaces the F\* SMT-`Lemma` style) | §18.3 row equality is an equivalence; DISTINCT is a sublist of its input, idempotent, and loses no row up to equivalence; LIMIT bounds the length; projection preserves the row count; ORDER BY is a permutation; single-graph evaluation is the default-graph case of dataset evaluation; LATERAL's inner-join shape |
| `L4Factoidal/SPARQL/QueryTests.lean` | (new; ports cases from `tests/unit/lateral_unit.ml`, `tests/unit/lateral_service_unit.ml`, `tests/local/sparql/lateral_topn_per_key.rq`) | 134 `#guard`s over GRAPH iri/var, BIND, VALUES with UNDEF, LATERAL (incl. sub-SELECT projection masking and top-N per key), SERVICE and SERVICE SILENT, projection with expressions, DISTINCT/REDUCED, ORDER BY, LIMIT/OFFSET, the aggregates, HAVING, ASK, CONSTRUCT with template blank nodes, and the property-path forms. NOT a conformance score — no parser, no manifest reader |
| `L4Factoidal/RDFS/Vocabulary.lean` | `RDF.Vocabulary.fsti` (5 of its constants) | `rdf:type`, `rdfs:subClassOf`, `rdfs:subPropertyOf`, `rdfs:domain`, `rdfs:range` as `WfIri` with `rfl` witnesses — the whole vocabulary the rdfs-core fragment names |
| `L4Factoidal/RDFS/RdfsCore.lean` | `RDF.Entailment.RDFS.RhoDFClosure.fst` (banner + rule set) | SPECIFICATION: the six RDF 1.1 Semantics §9.2 rows (rdfs2/3/5/7/9/11) as an inductive relation `Derives g t`, plus `Derives.mono` and `Derives.cut` |
| `L4Factoidal/RDFS/Closure.lean` | `RhoDFClosure.fst` lines 98-130 + `RDFS.Closure.fsti` lines 242-355 | IMPLEMENTATION: the six `rdfs_rule_*` bodies, `stepConclusions`/`step` (= `rho_df_closure_step`), the fuel/length-test loop `closure` (= `rho_df_closure`), `closureIter` (= `rho_df_closure_iter`), and `closureFix` with a stated fuel bound |
| `L4Factoidal/RDFS/ClosureTheorems.lean` | `RhoDFClosure.fst` theorems 1-3 | T1 extensivity, T2 soundness against `Derives`, T3 monotonicity, T4 completeness at a saturated graph, the fuel dichotomy, and the `Triple.eqb` transitivity chain the last two need |
| `L4Factoidal/RDFS/ClosureTests.lean` | (new) | 31 `#guard`s over five fixtures, each checking a derived AND a non-derived triple, plus the axiom audit lines |
| `L4Factoidal/SPARQL/Expr.lean` | `SPARQL11.Algebra.fst` Part 3 + §17: `expr`, `comp_op`, `arith_op`, `aggregate_fn`, `eval_result`, `ebv_checked`, `bool_and/or/not_checked`, `er_to_term`/`er_to_string`/`er_string_info`/`er_direction`/`er_string_preserve`, the scaled-decimal numeric model (`parse_to_scaled`, `parse_double_to_scaled`, `format_scaled_value`, `format_as_double`, `add_scaled`, `numeric_compare`, `value_compare`, `format_numeric_result`, `eval_arith_int`), the `fn_*` accessor family, `fn_langMatches_spec`, and the `eval_expr_with_base` / `eval_coalesce_with_base` / `eval_in_with_base` / `eval_concat_with_base` clique | the §17 expression language: AST, effective boolean value, promoted numeric types, the §17.3 error tables, §17.4 builtins, and `Expr.toCond` — the §18.5 bridge that finally gives `GraphPattern.filter` a real filter |
| `L4Factoidal/SPARQL/ExprTheorems.lean` | (new; replaces the F\* SMT-`Lemma` style) | §17.2.2 EBV rows, §17.4.1.1 BOUND, the §17.3 truth tables at both the `Option Bool` and evaluator level, the scaled-decimal order (reflexivity, exchange/antisymmetry, cross-multiplied characterisation, transitivity), `=` reflexivity on IRI/literal/Boolean/numeric values and its non-reflexivity on blank nodes, and the §18.5 FILTER collapse |
| `L4Factoidal/SPARQL/ExprTests.lean` | (new) | 152 `#guard` checks over the §17 semantics plus the FILTER/LeftJoin bridge on the `Tests.lean` fixture. NOT a conformance score: no parser, no manifest reader — iron rule #6 is met only when a Lean runner reads the W3C files |
| `L4Factoidal/RDF/Isomorphism.lean` | `RDF.GraphIsomorphism.fst` (comparison role only — ALGORITHM DIFFERS, see below) | RDF 1.1 Concepts §3.6 specification (`Graph.Isomorphic`, `Dataset.Isomorphic`) + the executable decision procedure: ground pre-filter, blank-node signature pruning, bounded backtracking bijection search returning the WITNESS mapping, three-way `IsoOutcome` |
| `L4Factoidal/RDF/IsomorphismTheorems.lean` | (new) | reflexivity (graphs; datasets under distinct graph names) and SOUNDNESS for both, plus the checker-correctness sub-lemmas `Graph.setEq_of_setEqB`, `bijectiveCert_inj`, `bijectiveCert_onto` |
| `L4Factoidal/RDF/IsomorphismTests.lean` | (new) | 73 `#guard`s: relabelling, chain vs fork, ground-set comparison, order/duplicate insensitivity, the two-blank-node cycle vs two self-loops, RDF 1.2 nested blank nodes, dataset-wide blank-node scoping, named-graph matching by IRI, the budget refusal |
| `L4Factoidal/XML/Document.lean` | `Parser.XML.fst` (AST + character classes) | XML 1.0 5th ed. `[2] Char`, `[3] S`, `[4] NameStartChar`, `[4a] NameChar`, `[5] Name`; the parse tree (`Attribute`, `Node`); the prolog model (`XmlDecl` `[23]`, `Doctype` `[28]`, `Document` `[1]`); the Namespaces §3 name model (`QNameSplit`, `ExpandedName`); the convenience accessors |
| `L4Factoidal/XML/Parser.lean` | `Parser.XML.fst` (the parser) | `parseXML : String → Except XmlError Document`. In XML the parser IS the well-formedness decision; the module header lists all twenty constraints it enforces and every scope cut it inherits |
| `L4Factoidal/XML/Namespaces.lean` | `XML.Namespaces.fst` | `[7] QName` splitting, prefix-scope resolution down the tree, the default namespace, the reserved `xml`/`xmlns` prefixes and their two reserved namespace names, 1.0-vs-1.1 undeclaring, §6.3 uniqueness after expansion, undeclared-prefix rejection |
| `L4Factoidal/XML/Wellformedness.lean` | `XML.Wellformedness.fst` | `[4] NCName` (= `[5] Name` minus `:`) and the RDF/XML §7.2.4–§7.2.12 forbidden-name and conflicting-attribute checks. Despite the F\* module's name this is NOT generic XML well-formedness — see below |
| `L4Factoidal/XML/Theorems.lean` | (new) | a structural well-formedness checker over the parse tree, a serialiser, the proved tag-matching theorem, and the two general claims stated as named `Prop`s |
| `L4Factoidal/XML/Tests.lean` | (new) | 118 `#guard`s: hub post 25's two live documents, every constraint in `Parser.lean`'s header, the namespace layer, reflexivity and round-trip fixtures |
| `L4Factoidal/XML/ConfProbe.lean` | `bin/xml-runner/xml_runner.ml` (the driver only) | the `xmlconf-probe` executable: reads W3C conformance file paths from stdin, prints a well-formed/malformed verdict per file |
| `L4Factoidal/JSON/Value.lean` | `Parser.JSON.fst` `json_val` + accessors | `Json` (`null`/`bool`/`string`/`number`/`array`/`object`), hand-written `DecidableEq` (nested-inductive — `deriving` does not apply, see file header), `field?`/`getString?`/`getBool?`/`getArray?`/`getStringArray?` |
| `L4Factoidal/JSON/Parser.lean` | `Parser.JSON.fst` (the parser half) | `parseJson : String → Except JsonError Json`, total via fuel (mirrors the F\* fuel discipline); indexes a `List Char`, not raw bytes — see file header on why (Lean `Char` = full Unicode scalar value; sidesteps `Parser.FastString`'s byte-slicing machinery and this toolchain's `String.Pos` API) |
| `L4Factoidal/JSON/Serialize.lean` | `SPARQL.JSON.Escape.fst` (`json_escape`) + the writer shape of `Parser.JSONLD.fst`'s `jcanon_serialize` (NOT its JCS canonicalisation/field-sorting) | `Json.toString` (compact) and `Json.toStringPretty` (new; no F\* counterpart) |
| `L4Factoidal/JSON/Tests.lean` | (new) | 61 `#guard`s: RFC 8259 §13 example, every escape form, surrogate-pair decode, number-lexeme preservation, rejection cases, key-order/duplicate preservation, parse∘serialize round-trips |
| `L4Factoidal/JSON/Theorems.lean` | (new) | escape-table round-trip (exhaustive, `decide`); general literal round-trip; the STRING case general induction (`stringSegments_plain` — any length/content with no character needing escaping); a kernel-reduction finding (see file header); `RoundTripGoal` stated with the exact proof gap named (no `sorry`) |

## Translation decisions

- **Refinements → subtypes.** `wf_iri = s:iri{is_iri s}` becomes
  `WfIri := {s : String // isIri s}`; the F\* `assert_norm` witnesses
  for constants become `rfl` proofs the kernel evaluates.
- **`literal_term_eq` collapses into `DecidableEq`.** The F\* strict
  term equality is field-by-field; in Lean that IS propositional
  equality (`Literal.termEq_iff_eq` proves the F\*
  `lemma_literal_term_eq_identity` counterpart). The COARSER engine
  equality (`Literal.eqb`: case-folded language tags, XMLLiteral
  c14n) stays a separate Bool relation, exactly as the F\* source
  warns it must.
- **Spec/engine decoupling.** The port keeps the SPECIFICATION
  evaluator: list scans, left-to-right BGP extension, nested-loop
  join. The F\* engine's index seam (`graph_store`/`RDF.Indexed`),
  selectivity planner (`choose_best_tp`), keyed hash join, fuel
  bounds, and tail-recursion (`*_tr`) rewrites are performance
  machinery over this same semantics and are deliberately not ported.
- **Filter conditions are `Binding → Bool`** in `Algebra.lean`. The
  expression stage (`Expr.lean`) supplies the real thing through
  `Expr.toCond : Expr → Binding → Bool` and the wrappers
  `GraphPattern.filterExpr` / `GraphPattern.leftJoinExpr`, so
  `Algebra.lean` never had to change. §18.5's "effective boolean value
  of true" is where a type error and `false` become
  indistinguishable — the collapse is in `toCond`, not in `ebv`.
- **`assume val` → PARAMETER.** What the F\* evaluator reaches for
  through the host (`fx_current_datetime`, `extension_function_call`)
  becomes a field of `EvalEnv`: `now`, `ext`, and `existsHook` for the
  §18.6 pattern layer. With `emptyEnv` each is absent and the operator
  is a type error — which for §17.6 extension functions is exactly the
  spec's own answer, not a shortcut.
- **`literalWf` is paid once.** Every literal an operator builds needs
  its well-formedness proof, so `Expr.lean` funnels construction
  through `mkTypedLiteral` / `mkLangLiteral` / `mkDirLangLiteral`
  (each discharging `literalWf` by kernel computation). The F\* source
  builds bare records and lets Z3 discharge the refinement at every
  site.
- **No `/` on `Int`.** The port uses an explicit truncate-toward-zero
  `intDivT`, because the rounding direction of Lean's `/` on `Int` is
  the one place where it could silently disagree with F\*'s
  `op_Division` and its OCaml extraction.
- **Fuel instead of well-founded recursion for `countDigits`.** The F\*
  `count_digits` recurses on `n / 10`; the Lean port carries an
  explicit fuel argument so the function stays STRUCTURAL and `#guard`
  can evaluate it during elaboration.
- **Deviations from the F\* semantics, stated plainly:**
  - `IRI()`/`URI()` does not resolve a relative reference against the
    query BASE (the F\* `resolve_iri`); RFC 3986 reference resolution
    is not ported, so a non-absolute lexical form is an error.
  - TIMEZONE, TZ, REGEX, REPLACE, the five hash builtins, aggregates,
    and EXISTS-without-a-hook return `EvalResult.error` — the
    constructor-level type error, never `sorry`. Each is listed with
    its reason in the `Expr.lean` module banner.
  - Argument LISTS (COALESCE, IN, CONCAT, function calls) are
    evaluated eagerly rather than short-circuited. The evaluator is
    pure and total, so this is observationally identical; it is noted
    because it is a visible difference from the F\* recursion shape.
- **No SMT scaffolding.** `SMTPat` hints, Z3 fuel pragmas, and
  helper lemmas whose only job was guiding the solver have no Lean
  counterpart — proofs are explicit tactic scripts. Axiom audit
  (`#print axioms`, in the build log): only `propext`,
  `Classical.choice`, `Quot.sound` — Lean's standard foundations; no
  `sorry`, no user axioms, no `native_decide`.

- **Graph isomorphism: a DIFFERENT ALGORITHM, deliberately.** This is
  the one place so far where the Lean port does not reproduce the F\*
  method, so it is recorded loudly rather than buried.
  `RDF.GraphIsomorphism.fst` reduces isomorphism to
  CANONICALISATION — it runs both sides through the verified RDFC-1.0
  canonicaliser (`RDF.Canonical`; SHA-256 + Hash-N-Degree-Quads) and
  byte-compares the canonical N-Quads, which is rdflib's reduction.
  `L4Factoidal/RDF/Isomorphism.lean` instead searches for the
  blank-node bijection directly, with ground pre-filtering and
  signature pruning. Two reasons: (1) RDFC-1.0 needs SHA-256, a much
  larger port than the comparison primitive the W3C harness is waiting
  on; (2) a canonical-hash comparison yields a Bool with no witness,
  whereas a search that RETURNS the mapping makes soundness a direct
  check — which is what `Graph.isomorphic?_sound` proves. Ported
  faithfully from the F\* module: the three-way outcome
  (`Iso_Equal`/`Iso_NotEqual`/`Iso_BudgetExceeded` → `IsoOutcome`), so
  a work-budget trip is reported and never a silent pass; and the
  language-tag case folding (`normalize_literal` there, already inside
  `Literal.eqb` here). NOT ported: `solutions_isomorphic`, the
  Jena-style SELECT-result reification, which needs the SPARQL
  solution type and belongs with the SPARQL side.
- **Search bound.** Termination is structural (recursion on the list
  of `g1`'s blank nodes), so no fuel parameter is needed for totality;
  the breadth bound is signature pruning plus `isoBnodeBudget = 16`,
  above which the procedure refuses and reports `budgetExceeded`. The
  identity mapping is tried first, so a parser evaluation test whose
  labels already agree costs one set comparison.
- **What is proved and what is not.** Proved: reflexivity, and
  SOUNDNESS (`isomorphic? = true` → `Graph.Isomorphic`) for graphs and
  datasets — the search is untrusted, since `isomorphismMap?` re-checks
  whatever it returns and only the check is used in the proof. NOT
  proved: completeness (false as stated, because of the budget and
  because signature keys write `rdf:XMLLiteral` literals lexically),
  and symmetry of the PROCEDURE (exercised on fixtures in both
  directions; a proof would need completeness first). Dataset
  reflexivity carries a `Dataset.namesNoDup` hypothesis, because
  `lookupNamed` returns the first graph under a name and the Lean type
  does not enforce RDF 1.1 §4's uniqueness of graph names.
## The XML stage (2026-08-22)

### Bytes versus codepoints — the one structural difference

`Parser.XML.fst` indexes raw UTF-8 BYTES through `Parser.FastString`.
A large part of it exists only to cope with that: `fs_cp_at` rebuilds a
codepoint from bytes, `is_utf8_continuation_byte` keeps a byte-stepping
validator from re-probing a continuation byte, `is_valid_decoded_char`
uses the `(0xFFFD, adv = 1)` sentinel to tell "a real U+FFFD" from
"these bytes are not valid UTF-8 here", and `codepoint_to_string` is a
hand-written UTF-8 encoder for resolved character references.

**None of that has a Lean counterpart.** Lean's `String`/`Char` are
codepoint types and a `Char` is a valid Unicode scalar value by
construction (`Char.isValidChar` excludes the surrogate block), so the
invalid-UTF-8 rejection those functions perform is discharged by the
TYPE rather than by a check, and a resolved character reference is one
`Char.ofNat`. Every rule stated over codepoints is ported in full.

Two consequences worth naming:

- `XmlError.position` is a CHARACTER offset into the line-ending-
  normalised document, where the F\* reports a byte offset.
- The three W3C cases the F\* comments name as its invalid-UTF-8
  targets — `xmltest/not-wf/sa/168`, `169`, `170`, which smuggle
  surrogates and a 4-byte UCS-4 form in as well-shaped UTF-8 — are
  rejected by `xmlconf-probe` at the decode step, before the parser
  runs. Same verdict, established one layer earlier.

### `XML.Wellformedness.fst` does not hold XML well-formedness

Worth stating plainly because the module name misleads. In XML there is
no separate validator pass: a document is well-formed exactly when the
parser accepts its character string. So the generic well-formedness
constraints live in `Parser.XML.fst` itself, and the Lean port keeps
them in `XML/Parser.lean`, whose header enumerates all twenty. What
`XML.Wellformedness.fst` actually holds is `[4] NCName` (a Namespaces
production) plus the RDF/XML §7.2 name and attribute rules (an RDF/XML
concern, one layer above XML). Both are ported to
`XML/Wellformedness.lean`; the RDF/XML half has no consumer inside
`L4Factoidal.XML` and is there for completeness of the port.

### Fuel

Where the F\* writes `decreases fuel`, the Lean is structurally
recursive on a `Nat` — the same bound, checked by the same argument.
The one exception is `expandEntityValue`, which keeps the F\*'s own
lexicographic `%[depth; budget]` measure as `termination_by
(depth, budget)`: diving into a nested entity drops `depth`, scanning
forward drops `budget`. No `partial`, no `sorry`, anywhere.

### Measured against the W3C XML Conformance Test Suite

`lake exe xmlconf-probe` reads file paths on stdin and prints a verdict
per file (iron rule #6: real W3C files from disk, not fixtures).
`xmlconf-fstar-crosscheck.mjs` runs the F\*-extracted parser
(`npm/factoidal`'s `xmlWellformed`) over the same list, so the two
ports can be compared file by file rather than only by totals.

Measured 2026-08-22 on the two `xmltest` standalone collections:

| collection | Lean port | F\*-extracted parser |
|---|---|---|
| `xmltest/not-wf/sa` (186 files) | 126 rejected, 60 accepted | 123 rejected, 63 accepted |
| `xmltest/valid/sa` (120 files) | 113 accepted, 7 rejected | 110 accepted, 10 rejected |

**These are raw agreement counts, NOT a conformance score.** A `not-wf`
case this parser rejects for a different reason than the one under test
is a right verdict for the wrong reason, and the profile is XML 1.0,
non-validating, non-namespace. Both columns are subject to that caveat
equally, which is what makes the comparison between them the useful
number.

File by file, across all 306 documents the two parsers disagree on
exactly six:

- `not-wf/sa/168`, `169`, `170` — the Lean probe rejects, the
  cross-check harness reports the F\* accepting. This is an artefact of
  the HARNESS, not of the F\*: Node's `readFileSync(p, "utf8")`
  replaces the bad bytes with U+FFFD before the parser sees them.
  `Parser.XML.fst`'s own comments name these three as documents it
  rejects, so the two ports agree on the intended verdict.
- `valid/sa/023`, `085`, `086` — a genuine divergence, and the Lean
  port is right. Content that is exactly one reference to an entity
  with EMPTY replacement text (`<!ENTITY e "">` with `<doc>&e;</doc>`)
  makes the F\* `parse_xml_text` fail with "empty text node"; the
  failure is indistinguishable from "no text here",
  `parse_children` discards it, and the document is then rejected for
  want of an end tag. All three are marked VALID by the W3C suite.
  `XML/Parser.lean`'s `parseChildren` separates the two outcomes and
  accepts them, recording no `[14] CharData` node for an expansion that
  yields no characters. Pinned by `#guard` in `XML/Tests.lean`.

The remaining wrongly-accepted `not-wf` cases are shared with the F\*
and are its documented scope cut: `parse_int_subset` skips
`<!ELEMENT>`, `<!ATTLIST>`, `<!NOTATION>` and parameter-entity
declarations STRUCTURALLY (`skip_decl_to_gt`) instead of parsing their
grammar, so a malformed internal-subset declaration is stepped over
rather than rejected. Implementing the internal subset's grammar is the
obvious next rung for either tree.

### Proof status

Proved, no `sorry` and no user `axiom`:

- `Node.serialize_element_tags_match` — **WFC: Element Type Match holds
  by construction.** A `Node.element` carries ONE tag and the serialiser
  writes it into both the `[40] STag` and the `[42] ETag`, so a
  mismatched pair is unrepresentable. This is the tag-matching
  component of checker reflexivity, and it is why the checker has no
  tag-matching clause left to state.
- `Node.wellFormedList_eq_all`, `Node.wellFormed_children`,
  `Node.wellFormed_of_mem_children` — the descent into children a
  general reflexivity proof needs.
- `Node.serializeList_cons` / `_nil` — serialisation is compositional.

Stated as named `Prop` definitions, checked on fixtures by `#guard`,
NOT proved in general: `ReflexiveOnParserOutput` and
`RoundTripsOnParse`. A `def … : Prop` assumes nothing and grants no
theorem; proving either means reasoning about `parseXML`'s fuel-bounded
scans over an arbitrary input string, which is a larger piece of work
than this stage. The `#guard`s are evidence and are labelled as such.

Round-trip is `parse ∘ serialise = id` on DOCUMENTS, not
`serialise ∘ parse = id` on strings. The latter is false and should be:
`<a></a>` serialises as `<a/>`. The infoset is what the parser is a
function into.

## Assumption report — `assume val`s in the F\* originals

Requested by the port brief: unverified assumptions encountered in
the source modules.

- `RDF.GraphIsomorphism.fst`: **zero** `assume val`s (200 lines,
  measured 2026-08-22 with `grep -c "assume val"`). The comparison
  semantics are fully defined in F\* and extracted; `w3c_runner.ml` is
  I/O glue that only calls them. Its dependency `RDF.Canonical` is a
  separate module and was not audited here.
- `Parser.XML`, `XML.Wellformedness`, `XML.Namespaces`: **zero**
  `assume val`s in all three, confirmed by `grep -c "assume val"` on
  each file (2,070 + 204 + 242 lines). The XML stack is pure F\* end to
  end — no host call-out, no I/O seam, no vendored primitive — so the
  port had nothing to dissolve by parameterisation and nothing to
  declare here. The only thing the F\* reaches outside itself for is
  `Parser.FastString`'s byte-indexed string primitives, which are
  ordinary defined functions, not assumptions.
- `RDF.Term`, `RDF.Triple`, `RDF.Graph`: **zero** `assume val`s. The
  core data model is fully defined; nothing was assumed away, and the
  port confirms it (every ported definition is total and executable).
- `Parser.JSON.fst`, `SPARQL.JSON.Escape.fst`: **zero** `assume val`s
  (confirmed by grep; the one hit for the string `"assume val"` in
  `SPARQL.JSON.Escape.fst` is a COMMENT referencing
  `Parser.FastString.fst`'s byte-primitive `assume val`s, not a
  declaration in either ported module). Both modules are fully defined
  and total in F\*, and the Lean port is fully defined and total too —
  no realisation gap on either side.

## A kernel-reduction finding from the JSON port (2026-08-22)

`Parser.lean`'s five mutually recursive functions
(`parseValue`/`parseObject`/`parseMembers`/`parseArray`/`parseItems`)
are `Tot`al by construction — every recursive call strictly decreases
the shared `fuel : Nat` — but Lean's equation compiler evidently
compiles this particular 5-way mutual group via WELL-FOUNDED recursion
rather than the bare structural recursion a single `fuel`-matching
function gets on its own (`stringSegments`, not part of this mutual
group, decides/`rfl`s fine in isolation). Consequence: `by decide` and
`by rfl` get "stuck" on ANY proposition mentioning `parseValue` or
anything that calls it (including `parseJson` itself) — NOT a
correctness problem (the compiled/`#eval`'d function is fine; `Tests.
lean`'s 61 `#guard`s exercise it directly), but a PROOF-TACTIC one:
kernel whnf reduction cannot unfold well-founded recursion the way it
unfolds structural recursion. Workaround, used throughout
`Theorems.lean`: `unfold parseValue parseObject ...` (equation-lemma
rewriting, which works regardless of how the recursion compiles) peels
exactly the layers a CONCRETE input needs, then `decide` closes the
remainder once no mutual-group call remains in the goal. A fully
general (∀-quantified) proof through this group needs the same
technique under an explicit induction rather than one-shot `unfold` —
see `Theorems.lean`'s `RoundTripGoal` section for exactly where this
matters (item 3, the array/object case).
- `SPARQL11.Algebra.fst`: **10** `assume val`s, all host-boundary
  call-outs (rule #11 of the F\* tree's own policy), none of them in
  the fragment this stage ports:
  - `string_uppercase_unicode` / `string_lowercase_unicode` —
    Unicode case mapping (host library). Lean note: `String.toLower`
    is used for language-tag folding; BCP47 tags are ASCII, so this
    is exact where the F\* tree needed the host for full Unicode.
  - `hash_md5` / `hash_sha1` / `hash_sha256` / `hash_sha384` /
    `hash_sha512` — SPARQL §17.4.4 hash builtins (vendored crypto).
  - `fx_current_datetime` — `NOW()` (clock I/O).
  - `extension_function_call` — SPARQL §17.6 extension-function host
    registry (issue #463).
  - `eval_property_path_fwd` — a forward reference into the
    property-path evaluator (an F\* module-structure artifact, not a
    semantic hole; the evaluator is defined later in the same file).
  - `service_endpoint_lookup` — SERVICE endpoint resolver (issue
    #57; the federated-query host seam).

  A Lean continuation porting the expression language will need
  positions for the first three groups (pure Lean implementations are
  feasible for all of them: Unicode tables, vendored hash cores, and
  a clock parameter instead of an ambient call).

- `RDF.Entailment.RDFS.RhoDFClosure.fst`, `RDFS.Closure.fsti` and
  `RDF.Vocabulary.fsti`: **zero** `assume val`s, zero `admit`, zero
  `--lax` — checked by grep over all three files at port time
  (2026-08-22). The rdfs-core closure is pure F\* throughout, so the Lean
  port inherits no assumption from it. What it DOES inherit are the
  F\* module's CARRIED HYPOTHESES, and those are the interesting part
  of the correspondence — see the next section.

## What the rdfs-core port proves, and what it does not

The F\* module states five theorems; three of them carry hypotheses it
does not discharge (`rho_df_chain_canonical`, `rho_df_chain_wf`, and
the two `no_repeats_p` premises of `lemma_len_eq_saturated`). The Lean
port re-proves the executable content natively and needs fewer
hypotheses, but its soundness statement is WEAKER in kind:

| | F\* | Lean |
|---|---|---|
| T1 extensivity | `is_subgraph g (rho_df_closure g fuel)` under `rho_df_chain_canonical` | `closure_extensive`, no hypothesis |
| T2 soundness | MODEL-THEORETIC: `rho_df_entails g (rho_df_closure g fuel)` under `rho_df_chain_wf` | PROOF-THEORETIC: `closure_sound`, every computed triple has a §9.2 derivation. No interpretations are ported, so this is NOT the F\* theorem |
| T3 closedness/monotonicity | `rho_df_closure_closed` at a fuel witness, under two `no_repeats_p` | `closure_mono_of_saturated`, derived from T2 + `Derives.mono` + T4 |
| T4 completeness | (the payoff `rho_df_closure_decides`, via `rho_df_saturation_iff`) | `complete_of_saturated` / `closure_complete_of_saturated`: all six rule cases proved |
| fixpoint test | length test, exactness assumed (`no_repeats_p`) | `addAll_eq_of_length_eq`: equal length PROVES the round was the identity |

Named remaining obligation (one, and it is stated in the code, not
hidden): that `closureFuelBound` is always enough — i.e. that the
closure of an `n`-triple graph holds at most `n * (n + 1) * n` triples,
so the length test must fire before the fuel runs out. What IS proved
is the dichotomy `closure_saturated_or_underfueled`: either the result
is saturated, or it grew by at least one triple per unit of fuel. T4
takes saturation as a hypothesis; the `#guard`s in `ClosureTests.lean`
check `step c == c` on every fixture, so nothing in the tests relies on
an unproved bound either.

Two other translation notes for this module:

- **Intra-step chaining is dropped, deliberately.** The F\* step threads
  its accumulator through the six rows, so a triple emitted by rdfs7
  can drive rdfs9 in the same round. The Lean step reads every premise
  from the round's input. Per round this emits less; at the fixpoint
  it emits the same set (the chained conclusion arrives one round
  later), and the loop runs to saturation. The gain is that `step` is a
  plain function of its input, which is what makes soundness and
  saturation one induction each. Documented at the head of
  `Closure.lean`.
- **Two membership relations, on purpose.** T1 and T2 use LIST
  membership (`t ∈ g`); T4 uses `Graph.mem` (the engine's `Triple.eqb`
  membership). It has to: `Graph.add` skips an insert when an
  eqb-equal triple is already present, so after adding `t` the graph
  may hold an `rdf:XMLLiteral` variant of `t` rather than `t` itself.
  This is a property of the ported `Graph.add`, not of the proof.

## Lemmas this port had to prove locally, that belong in `RDF/Core.lean`

`ClosureTheorems.lean` section 6 proves facts about the engine
equality that no ported module had needed yet. They are stated in the
`L4Factoidal.RDFS` namespace to avoid editing `RDF/Core.lean` in this
landing; they should MOVE to `Core.lean` (and `Graph.lean`) next time
those files are touched:

- `Subject.eqb_eq` — on subjects, engine equality IS equality.
- `langTagOptionEq_trans`, `Literal.eqb_trans`, `Term.eqb_trans`,
  `Triple.eqb_trans` — transitivity of the coarse comparison chain.
  `Core.lean` has the reflexivity lemmas (`Term.eqb_refl`,
  `Triple.eqb_refl`) but no transitivity, and transitivity is what any
  proof that chains two eqb-matches needs.
- `Triple.eqb_parts` / `Triple.eqb_of_parts` — the componentwise
  decomposition/introduction pair.
- `Term.eqb_iri`, `Term.eqb_eq_of_toSubject` — eqb collapses to
  equality in exactly the positions the entailment rules match on.
- For `Graph.lean`: `graphMem_of_mem` (list membership implies
  `Graph.mem`), `exists_of_graphMem` / `graphMem_of_exists` (the
  witness characterisation of `Graph.mem`),
  `graphMem_of_graphMem_eqb` (`Graph.mem` respects `Triple.eqb`),
  `mem_add_of_mem_list`, `mem_add_cases`, `length_le_add`,
  `add_eq_of_length_eq`. `Graph.lean` currently has only
  `mem_append`, `mem_add_of_mem`, `mem_add_self` — all three in the
  Bool relation, none in the list relation, and no length lemma.
  No change was made to `Core.lean` or `Graph.lean` in this landing.
### Assumptions met by the expression-language stage (`Expr.lean`)

The §17 fragment ported here meets four of those ten `assume val`s.
None of them became a Lean `axiom`, an `opaque`, or a `partial def`:

| F\* `assume val` | Where it bites in §17 | What `Expr.lean` does instead |
|---|---|---|
| `string_uppercase_unicode` / `string_lowercase_unicode` (issue #250) | UCASE / LCASE (§17.4.3.4/5) and the case-insensitive language-tag folding in langMatches and CONCAT | Uses Lean's own `String.toUpper` / `String.toLower`. **Stated precisely:** these are ASCII case mappings, so they are EXACT for BCP 47 language tags (ASCII by construction) but INCOMPLETE for UCASE/LCASE on non-ASCII text — the same gap issue #250 tracks on the F\* side, with the same shape (`"Müller"` upper-cases to `"MüLLER"`). A full Unicode case-mapping table is a separate pure-Lean port. |
| `hash_md5` / `hash_sha1` / `hash_sha256` / `hash_sha384` / `hash_sha512` (§17.4.3.16) | MD5, SHA1, SHA256, SHA384, SHA512 | NOT implemented and NOT assumed: the five constructors return the constructor-level type error. A pure Lean implementation, provable against a spec, is the intended answer; a stub that returns a plausible-looking string would be worse than an error. |
| `fx_current_datetime` (§17.4.5.1, issue #287) | NOW() | Became the input `EvalEnv.now : Option String`. The clock read moves to the executable edge; the semantics is a total function of its arguments. With no timestamp supplied, NOW() is a type error. |
| `extension_function_call` (§17.6, issue #463) | any IRI-named function no native family claims | Became the input `EvalEnv.ext : String → List EvalResult → Option EvalResult`. The default (`none` for every IRI) makes an unregistered IRI a type error, which is what §17.6 requires. |

The remaining F\* `assume val` in this region belongs to a feature the
stage does not port: `regex_match` / `regex_replace` (REGEX, REPLACE).

### Assumptions met by the query stage (`Query.lean`, `PropertyPath.lean`)

The wider graph-pattern set and the §18.2.4 pipeline touch three more
of the F\* `assume val`s. All three dissolve; none became a Lean
`axiom`, an `opaque`, or a `partial def`:

| F\* `assume val` | Where it bites | What this stage does instead |
|---|---|---|
| `service_endpoint_lookup` (Federated Query §2, issue #57) | the `GP_Service` / `GP_ServiceVar` arms of `eval_pattern_store` | Became the input `EvalEnv.services : List (Iri × Graph)`, read through `EvalEnv.resolveService`. `QueryPattern.lower` resolves a fixed endpoint at lowering time and hands the algebra an `Option Graph`, so `GraphPattern.service` carries a RESOLVED graph and no host call. An endpoint absent from the list is an unreachable endpoint: SILENT then yields one empty solution mapping and non-SILENT yields none — the same two answers the F\* arm gives. |
| `extension_function_call` (§17.6, issue #463) | GROUP BY / HAVING / ORDER BY / SELECT expressions, which the pipeline evaluates | Already an input (`EvalEnv.ext`) from the expression stage; the query stage threads the same `EvalEnv` through every post-pattern phase, so no new assumption appears. |
| `eval_property_path_fwd` (§18.4) | the `GP_PropertyPath` arm | An F\* FILE-ORDERING artifact, not a semantic gap: the concrete `eval_property_path` sits about 300 lines BELOW its use site in `SPARQL11.Algebra.fst`, so that file forward-declares it. Lean has no such constraint — `SPARQL.evalPath` is the definition, in `PropertyPath.lean`, and the algebra calls it directly. |

Two F\* proof obligations also disappear rather than being ported,
because the Lean encoding makes them typing facts:

* `lemma_lateral_substitute_preserves_size` — needed in F\* because
  `lateral_substitute` returns a pattern that is no subterm of the
  `GP_Lateral` node being evaluated. Here substitution is FUSED into
  lowering (`QueryPattern.lowerWith env mu`), so the recursive call
  goes to a genuine subterm and the composition of an outer
  substitution with a per-row one is just `Binding.merge` (outer
  wins).
* the `%[query_size q; 3]` lexicographic measure across the
  `eval_pattern_store` / `eval_select_query` / `eval_exists` /
  `substitute_existentials` clique — needed in F\* because a
  sub-SELECT re-enters query evaluation. Here `QueryPattern` and
  `Query` are ONE mutual inductive, so a sub-SELECT's pattern is a
  subterm, and the inner query's post-pattern pipeline (`selectPost`)
  does not recurse into patterns at all.

## Findings from the expression-language stage

Two behaviours the port made visible. Both are recorded as `#guard`s in
`ExprTests.lean` so they cannot drift silently, and neither is asserted
to be correct:

1. **Only a VARIABLE lookup promotes a literal.** `literalPromote`
   runs on the `E_Var` arm; `E_Literal` returns the term as written.
   So `"1"^^xsd:integer = "01"^^xsd:integer` written literally in an
   expression compares LEXICALLY and answers `false`, while the same
   comparison through two bound variables answers `true`. Faithful to
   the F\* source; SPARQL 1.1 §17.1's operand mapping would say `true`
   in both cases.
2. **STRDT's result is not promoted either.** `STRDT(STR(?a),
   xsd:integer) > 18` is a type error and drops the row, because
   `value_compare` sees `ER_Term (T_Literal _)` against `ER_Num` and
   has no arm for that pair. Same root cause as (1), same fidelity to
   the F\* source, same divergence from §17.1.

Both would be fixed by promoting at the point of COMPARISON rather
than at variable lookup — a change to `value_compare`, worth making in
the F\* tree first (iron rule #1) rather than only in Lean.

## Next stages (in rough order of value)

1. ~~The expression language (`expr`, EBV, §17 operators) and with it
   real `Filter`/`LeftJoin` conditions.~~ **Landed** —
   `SPARQL/Expr.lean`, `ExprTheorems.lean`, `ExprTests.lean`. What it
   still lacks: a pure regex matcher (REGEX/REPLACE), pure hash
   functions (§17.4.3.16), xsd:dateTime TIMEZONE/TZ, aggregate
   evaluation over a group, xsd type-cast constructor functions, and
   RFC 3986 BASE resolution for `IRI()`.
0. JSON-LD, SPARQL Results JSON, and JSON Schema ports now unblocked
   by `L4Factoidal/JSON/` (`Parser.JSONLD.fst`/`Parser.JSONResults.fst`
   are the F\* sources; both consume `json_val`/`Json` via the same
   `field?`/`json_get_*` shape this port kept API-compatible with).
   Closing `Theorems.lean`'s `RoundTripGoal` gap (three named items:
   escaped-content strings, general number lexemes, array/object
   induction through the mutual-recursion group) is worth doing before
   or alongside the JSON-LD port, since JSON-LD's own round-trip
   proofs will need the same techniques one level up.
1. The expression language (`expr`, EBV, §17 operators) and with it
   real `Filter`/`LeftJoin` conditions.
2. N-Triples/N-Quads parsing + serialisation (round-trip theorems —
   the F\* tree's G4/M1 program has proofs worth re-proving natively).
3. A W3C-suite harness: build a small Lean executable that reads the
   same manifests `bin/w3c-runner` does, so the Lean engine's scores
   are measured by the same files (the F\* tree's iron rule #6).
4. Wider `GraphPattern`: GRAPH, VALUES, BIND, sub-SELECT, property
   paths, and the SPARQL 1.2-track LATERAL.
5. ~~RDFS closure + soundness~~ — LANDED for the six-row rdfs-core
   fragment (`L4Factoidal/RDFS/`, 2026-08-22). The continuations it
   opens, in order:
   a. the term-universe counting bound that discharges
      `closureFuelBound` (the one named obligation above);
   b. the rdfs-core MODEL THEORY (interpretations, `rho_df_conditions`,
      `satisfies`), which turns T2 from proof-theoretic into the
      model-theoretic statement the F\* tree proves, and gives the
      "decides entailment" payoff;
   c. the twelve-row RDFS closure, whose extra rows need the axiomatic
      triples the fragment omits;
   d. moving the eqb lemmas of section 6 into `RDF/Core.lean`.
   Tableau work (#448-adjacent) after that, where Lean's structural
   induction is expected to shine.

## Crypto/SHA2 landing (2026-08-22)

`L4Factoidal/Crypto/SHA2.lean` + `SHA2Theorems.lean` + `SHA2Tests.lean`
— a pure Lean 4 implementation of FIPS 180-4 SHA-256/384/512, under
the crypto-policy skill's "Lean 4 tree amendment" (owner-approved
2026-08-22: a pure Lean hash over PUBLIC data is permitted, carrying
FIPS/RFC test vectors as build-time `#guard`s; signatures/MACs/
key-agreement stay HACL*-FFI-only, never hand-written Lean).

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/Crypto/SHA2.lean` | `RDF.Canonical.fst` `hash_sha256`/`hash_sha384` `assume val`s | full message schedule, compression, §5.1.1/§5.1.2 padding, `sha256`/`sha384`/`sha512` (`ByteArray → ByteArray`) + `sha256Hex`/`sha384Hex`/`sha512Hex` (`String → String`, UTF-8-in/lowercase-hex-out — the exact shape the F\* `assume val`s need) |
| `L4Factoidal/Crypto/SHA2.lean` (`HashAlgorithm`/`hashBytes`/`hashHex`) | (new; hash-agility layer, owner directive 2026-08-22 — "sooner or later [SHA-256] will fall and we want to be ready") | every future consumer (RDFC-1.0, VC Data Integrity, SPARQL §17.4.4) is required to take a `HashAlgorithm` parameter and call the dispatcher, never `sha256`/`sha256Hex` directly; `HashAlgorithm` deliberately leaves room for a `sha3_256`/`shake256` constructor (FIPS 202, not ported — different Keccak-based construction) |
| `L4Factoidal/Crypto/SHA2Theorems.lean` | (new) | `pushN_size` (padding-fill byte count), `pad256_size`/`pad512_size` (padded length is a multiple of 64/128 — the fact that makes the outer block loop's Nat-fuel exact rather than approximate), `sha256_size`/`sha384_size`/`sha512_size` (32/48/64-byte digest length) — all six proved (`propext`, `Quot.sound` only; no `sorry`, no extra axioms), none needed to be left unproved |
| `L4Factoidal/Crypto/SHA2Tests.lean` | (new) | 22 `#guard`s: FIPS 180-4's three official example messages ("abc", the 56-byte and 112-byte two-block examples, 1,000,000×'a') for all three algorithms, plus a non-ASCII UTF-8 case and the hash-agility dispatcher, against digests generated (not hand-typed) from macOS `shasum -a 256/384/512` output — see the file's own provenance note for why (two hand-typed digest transcription errors were caught and replaced in-session before landing) |

**This REPLACES `RDF.Canonical.fst`'s `hash_sha256`/`hash_sha384`
`assume val`s with pure, verified-total code** for the Lean tree (the
F\* tree's own `assume val`s are untouched by this landing — that is
a separate F\*-side realisation step, tracked by crypto-policy/#63).
**MD5 and SHA-1 remain unported** — out of scope for this landing
(SPARQL §17.4.4 also names `MD5`/`SHA1`; both are legacy/broken
algorithms with no RDFC-1.0 or VC Data Integrity call site, so porting
them was not prioritised here).

Structural discipline: no `partial def` anywhere. The outer block
loop is Nat-fuel-by-exact-block-count (`pad256_size`/`pad512_size`
prove the fuel is exact); the two per-block fixed-length loops
(message schedule extension, round function) use core Lean's
`for _ in [a:b] do` over a compile-time-constant range; `pushN`
(padding) is explicit Nat-structural recursion; the digest
serialisation is a straight-line, statically-fixed-count push chain
(not a loop) — see `SHA2.lean`'s module header for why that specific
design choice is what makes the length theorems tractable by `simp`
alone, without reasoning about the hash's actual arithmetic.
## Addendum (2026-08-22): N-Triples / N-Quads syntax port

Scope of this stage: RDF 1.1 N-Triples and N-Quads parsing + wire
serialisation, plus the RDF 1.2 object-position triple-term and
directional-literal extensions (W3C Working Draft, mirroring the F* tree's
`Mode_11`/`Mode_12` split). Adds `L4Factoidal/Syntax/{Lexing,NTriples,
NQuads,SyntaxTheorems}.lean` (defs/theorems) and `SyntaxTests.lean`
(46 `#guard` checks). `lake build` remains green with these five modules
wired into `L4Factoidal.lean`.

### Module correspondence

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/Syntax/Lexing.lean` | `Parser.NTriples.fst` character-level helpers (`hex_val_opt`, `valid_codepoint`/`safe_char_of_int`, `parse_iri_raw`/`parse_iri_body_acc`, `parse_string_literal`/`parse_string_body`, `parse_lang_tag`, `parse_lang_dir_12`, `parse_bnode`, `pws`/`skip_comment`/`skip_eol`) | codepoint-level (`List Char`) instead of the F* source's byte-level (`Parser.FastString`) primitives — see Assumption report below. Structural recursion throughout; no fuel needed (Lean's nested cons-pattern recursion decreases automatically where the F* source needed `decreases fuel`). |
| `L4Factoidal/Syntax/NTriples.lean` | `Parser.NTriples.fst` triple-level grammar (`parse_subject`/`parse_object`/`parse_object_12_f`/`parse_triple`/`parse_triple_12`/`parse_ntriples_strict`/`parse_ntriples_strict_12`) + the N-Triples half of `RDF.NQuads.Serialize.fst` (`nq_term_to_string`, `nq_subject_to_string`, `nq_line_for_triple_default_graph`) | `Mode` (`rdf11`/`rdf12`) is the Lean counterpart of `rdf_syntax_mode`. Only the STRICT parse entry points are ported (see "Deliberately not ported" below). `readObject12`'s triple-term nesting uses an explicit `fuel : Nat` — the one place this port keeps the F* source's fuel style, because the recursive call is reached after parsing a subject/predicate in between (not a direct cons-pattern suffix), so plain structural recursion on the char list is unavailable there. |
| `L4Factoidal/Syntax/NQuads.lean` | `Parser.NQuads.fst` (`parse_graph_label`/`parse_opt_graph_label`/`parse_nquad`/`parse_nquad_12`/`parse_nquads_strict`/`parse_nquads_strict_12`/`dataset_add_quad`) + the N-Quads half of `RDF.NQuads.Serialize.fst` (`nq_line_for_triple`) | Reuses `Syntax.NTriples`'s subject/predicate/object readers verbatim, matching the F* source's own module structure (`Parser.NQuads.fst` `open`s `Parser.NTriples`). `addQuad` is a direct-append version of `dataset_add_quad`; the F* source's `graph_add_unchecked` + `dataset_finalise` prepend-then-reverse split is a performance pragmatic over the identical set semantics, not ported (see below). |
| `L4Factoidal/Syntax/SyntaxTheorems.lean` | (new; no direct F* counterpart — the F* tree's G4/M1 round-trip program is SMT-`Lemma`-based) | ECHAR/UCHAR decode round-trip facts on concrete escape-table entries (`rfl`-proved); the general graph round-trip theorem's BASE CASE (`graph_roundtrip_nil`, proved); the general theorem's FULL statement + induction skeleton (commented out, not `sorry` — see the file's module header for the two blocking gaps). |
| `L4Factoidal/Syntax/SyntaxTests.lean` | (new; hand-written fixtures in the style of `third_party/testing/w3c/rdf/rdf11/rdf-n-triples/` — that submodule is absent in this worktree, see below) | 46 `#guard`s: positive/negative RDF 1.1 N-Triples, RDF 1.2 fixtures (directional literals, triple terms, nested triple terms, legacy `<< >>` rejection), serialise-then-parse round trips on every positive fixture graph, N-Quads with two named graphs + a blank-node graph label + a rejected literal graph label. |

### Deliberately NOT ported (spec/pragmatics split, matching the existing
`RDF.Graph`/`SPARQL.Algebra` convention in this tree)

- The F* source's FAST-PATH / SLOW-PATH split (`scan_iri_end` vs.
  `parse_iri_body_acc`, `scan_string_fast` vs. `parse_string_body`) — a
  byte-buffer performance optimisation; this port has one code path per
  reader.
- The LENIENT document parsers (`parse_ntriples`/`parse_ntriples_12`/
  `parse_nquads`/`parse_nquads_12` — skip a malformed line and keep
  going) and the streaming/count/validate-only variants (`fold_ntriples`,
  `fold_nquads`, `count_ntriples`, `count_nquads_quads`, every
  `validate_*` function, `parse_nquads_flat`). All are CLI/import-
  pipeline/performance pragmatics over the identical grammar the STRICT
  entry points this port ships already specify; this matches the
  existing `L4Factoidal` convention of porting the SPECIFICATION
  evaluator, not the OCaml extraction's performance seam.
- RDF 1.2's inline-whitespace relaxation between a closing quote and a
  following `@lang`/`^^datatype` (F* `parse_literal_12`'s `pws`-then-peek
  logic, exercised by the W3C c14n suite's `extra_whitespace-03`/`-04`
  tests). Not exercised by anything in `SyntaxTests.lean`; flagged as a
  known gap rather than silently dropped.
- The F* source's CANONICAL N-Triples/N-Quads serialiser
  (`nq_canon_term`/`canonical_nt_document`/`canonical_nq_document` —
  uppercase `\u00XX` for every C0/DEL byte, lowercased language tags,
  U+FFFE/U+FFFF escaping) — a distinct rendering contract for the
  RDFC-1.0 c14n test suite, not the general wire serialiser
  `Graph.toNTriples`/`Dataset.toNQuads` port.

### Assumption report — F\* primitives this port replaces or cannot carry over

- `Parser.FastString`'s byte-indexed primitives (`fs_byte_length`,
  `fs_byte_index`, `fs_byte_at`, `fs_byte_sub`, `fs_cp_at`,
  `fs_utf8_of_codepoint`, `unsafe_char_of_d7ff`) — all `assume val`
  realisations in the F* tree (rule #11(b), pure host-string-library
  call-outs; the F* source's own comments cite issue #70 and #325 for
  why the byte/codepoint split exists and a bug it once caused). This
  port needs NONE of them: Lean's `List Char` is already
  codepoint-indexed (produced by `String.toList`, which decodes UTF-8),
  so every byte-vs-codepoint distinction the F* source's comments walk
  through (the `#325` double-encoding bug, the ASCII-fast-path vs.
  codepoint-slow-path split in `is_bnode_char_cp`) collapses to a single
  codepoint-level definition with no host primitive at all. This is a
  case where the Lean port is STRUCTURALLY simpler than the F* source,
  not merely a different implementation of the same primitive.
- `RDF.Term.fsti`'s `is_iri` (ported as `RDF.Core.isIri`, already noted
  zero-`assume val` in the original port) is reused unchanged by this
  stage's `mkIri`. Its coarseness (non-empty + contains `:`, not the
  full IRIREF-forbidden-codepoint grammar) is the SAME gap the F* source
  has — see `SyntaxTheorems.lean`'s GAP #1 note. Not a regression this
  port introduced; recorded here because it is the reason the general
  round-trip theorem could not be closed in this session.
- No new `assume val`-equivalent (`axiom`/`opaque`/`partial`) was
  introduced anywhere in `Syntax.*`. Every reader is a total Lean
  function (`#print axioms` on the proved theorems in
  `SyntaxTheorems.lean` shows only `propext`/`Classical.choice`/
  `Quot.sound` — Lean's standard foundations, the same baseline
  `L4Factoidal.Tests`'s own audit lines already carry).

### Deviation from the port brief's literal signature order

The brief specified `parseNTriples (mode := .rdf11) (s : String)` /
`parseNQuads (mode := .rdf11) (s : String)` (default parameter FIRST).
Lean 4 does not skip a leading `optParam` in a bare positional call —
`parseNTriples "text"` with `mode` first is a TYPE ERROR (confirmed by a
scratch test: `f "hello"` against `f (mode : M := .a) (s : String)`
rejects `"hello"` against the `Mode`-typed first slot rather than
skipping to `s`). This port therefore declares the STRING parameter
first and `mode` second, trailing, with the default:
`parseNTriples (s : String) (mode : Mode := .rdf11)`. Same reordering
for `Graph.toNTriples`/`Dataset.toNQuads` (`g`/`ds` first, `mode`
second). Every call site in `SyntaxTests.lean`/`SyntaxTheorems.lean`
uses this order; `parseNTriples s` (RDF 1.1 default) and
`parseNTriples s .rdf12` both work as intended.

### Core/Graph change that would help (not made — brief scopes this port
to new files only)

`RDF.Graph.lean`'s `NamedGraph` derives `Repr` only, not `DecidableEq`
(`Dataset` likewise). This port's tests need to compare `List NamedGraph`
for the N-Quads round-trip check and cannot add `deriving DecidableEq`
without editing `RDF.Graph.lean`, so `SyntaxTests.lean` carries a local
`namedGraphsEq`/`namedGraphEq` helper instead (pointwise `name`/`graph`
comparison, `List Triple`'s own derived `DecidableEq` doing the real
work). Adding `deriving DecidableEq` to `NamedGraph` and `Dataset` in
`RDF.Graph.lean` would let that helper be replaced by ordinary `==`,
matching the `instBEqOfDecidableEq` convention this project's own
pitfall list (`skills/factoidal-lean-basics`) already recommends for
every other structure in the tree.

---

## RDFC-1.0 canonicalization (`RDF/Canonical*.lean`, Harness/CanonProbe)

Ported: `formal/fstar/RDF.Canonical.fst` (2273 lines) → three Lean
modules plus one harness executable. Spec of record:
RDF Dataset Canonicalization 1.0 (W3C Recommendation 2024),
https://www.w3.org/TR/rdf-canon/ .

### Module correspondence

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/RDF/Canonical.lean` | `RDF.Canonical.fst` Sections 1–8 | canonical N-Quads form (§3), Hash First Degree Quads (§4.5), Hash Related Blank Node (§4.6), Hash N-Degree Quads with the permutation loop (§4.7), the `c14n`/`b` identifier issuers (§4.8), and the two-pass §4.4 driver; `canonicalize`, `Dataset.canonicalNQuads`, `Dataset.canonicalHash`, `canonicalizeExceedsBudget` |
| `L4Factoidal/RDF/CanonicalTheorems.lean` | (new; the F\* module's Section 5b label-shape lemmas, plus more) | 37 theorems: output sortedness, decimal-rendering round trip and injectivity, the issuer invariant + step lemma + injectivity preservation, and the §4.5 relabelling-invariance chain up to `hashFirstDegreeQuads_rename` |
| `L4Factoidal/RDF/CanonicalTests.lean` | (new) | 62 `#guard`s incl. both RDFC-1.0 §4.2 worked examples verbatim |
| `Harness/CanonProbe.lean` (`lake exe l4rdfc-probe`) | `rdfc10_runner.ml` | walks the vendored W3C corpus off disk |

### Assumption report

The F\* module has exactly TWO `assume val`s: `hash_sha256` and
`hash_sha384`. Both are **replaced** here by the pure Lean SHA-2 of
`L4Factoidal/Crypto/SHA2.lean`, reached only through the
`HashAlgorithm` parameter (`Crypto.hashHex`) — no function in
`Canonical.lean` names `sha256`/`sha384` directly, per the hash-agility
rule in `skills/crypto-policy`. That closes the F\* module's whole
trust surface: in the F\* tree those two are realised by hand-written
OCaml (`fstar_pure_hashes.ml`), a rule-#11 gap tracked as issue #63.

Nothing else in `RDF.Canonical.fst` was assumed, and nothing else is
assumed here. No `sorry`, no user `axiom`, no `native_decide`, no
`partial`. `#print axioms` on every headline theorem and entry point
shows exactly `[propext, Classical.choice, Quot.sound]`.

### Measured against the real corpus

`lake exe l4rdfc-probe` over
`third_party/testing/rdf-canon/tests/rdfc10/` (run 2026-08-22):

- rdfc10 eval (SHA-256): **63 pass, 0 fail (out of 63)**
- sha384 eval: **1 pass, 0 fail (out of 1)** — the suite marks exactly
  one entry `rdfc:hashAlgorithm "SHA384"` (test075)
- rdfc10 map eval (issued identifier maps): **21 pass, 0 fail (out of 21)**
- negative eval (the §4.4 excessive-calls abort): **1 pass, 0 fail (out of 1)**
- total **86 pass, 0 fail (out of 86)**, the same score the F\* tree
  reports on the same corpus

Sabotage-checked, per the skill's discipline: replacing §4.5's `_:z`
placeholder with `_:y` drops the eval score to 35 pass, 28 fail (out of
63); forcing SHA-256 where the manifest asks for SHA-384 fails test075;
deleting the §3 sort from `canonicalLinesOf` makes
`canonicalLines_sorted` fail to compile. None of the three is a test
that passes by measuring nothing.

### Deliberate differences from the F\* source

1. **Termination without mutual recursion.** F\* bounds Hash N-Degree
   Quads with a lexicographic `decreases %[fuel; phase; list]` across a
   six-function mutual block. Here `hndqRun` is structurally recursive
   on its fuel and passes a "recurse one level down" closure
   (`HndqRec`) to the bucket/permutation walkers, each structurally
   recursive on its own list — so Lean accepts all six with no
   `termination_by` at all. Cost: one fuel unit per HNDQ level instead
   of F\*'s two. Fuel is seeded at `bnodes + 1` in both and is a
   totality device neither reaches on real input, so the Lean bound is
   strictly more generous.
2. **Permutation cap mirrored, and reported.** `permutationCap = 6`:
   each §4.7 bucket is truncated to its first six related blank nodes
   before permuting (720 permutations). This is the F\* source's
   `take_n 6`. It is a RESULT VARIANT for any dataset with a symmetric
   collision bucket wider than six — no such dataset exists in the W3C
   corpus, so the corpus score is unaffected, but the general claim is
   "the spec's answer for buckets up to width 6", not "the spec's
   answer".
3. **Work budget mirrored.** `hndqBudget` counts Hash-N-Degree-Quads
   calls; `canonicalizeExceedsBudget` is the §4.4 "excessive calls"
   abort, which is how the suite's negative test passes.
4. **Insertion sort, not merge sort.** F\* uses a position-split merge
   sort because its inputs reach 100k+ lines. Every rdf-canon fixture
   is under 50 lines, so this port uses a stable insertion sort with
   the same total preorder and the same first-wins tie-breaking — short
   enough that `sortedB_sortBy` proves it actually sorts.
5. **F\* dead code not ported.** `compute_all_nbr1`/`nbr2`/`nbr3`,
   `bn_full_key`, `sort_full_keys`, `assign_full_in_order` — an earlier
   phase's bounded approximation of HNDQ, unreachable from
   `build_canonical_mapping_alg_budgeted` in the F\* tree (grep-checked
   before omitting).
6. **F\* performance machinery not ported**, per this tree's
   spec/engine split: byte-level `fs_byte_at` scanning, the
   `bn_lookup_tree` balanced BST used for relabelling, and the
   accumulator/`rev` rewrites of every list build.

### What is PROVED and what is only STATED

Proved (kernel-checked, standard axioms only):

- `canonicalLines_sorted` — the emitted canonical N-Quads lines are in
  code point order (RDFC-1.0 §3), for every dataset and algorithm.
- `mkLabel_inj`, via `digitsToNat_natToDigits` → `natToDigits_inj` —
  the §4.8 label shape is injective in the counter.
- `issueFresh_label_fresh` — the issuer step lemma: the next label
  differs from every label already issued.
- `issueFresh_injective` / `issueIdentifier_injective` — both issuing
  operations preserve `IssuerLabelsInjective`, from either empty
  issuer.
- The §4.5 relabelling chain: `rewriteSubjectForHfdq_rename`,
  `rewriteTermForHfdq_rename`, `rewriteTripleForHfdq_rename`,
  `quadMentionsBnode_rename`, `renderForHfdq_rename`,
  `hfdqRenders_rename`, `hashFirstDegreeQuads_rename` — Hash First
  Degree Quads cannot see the input blank-node labels.
  Non-vacuity: `prefixLabels_injective` exhibits a label-CHANGING
  function meeting the hypotheses.

Stated only, as `Prop`-valued definitions so that nothing claims a
proof it does not have:

- `RelabellingInvariance` — `Graph.Isomorphic g1 g2 →` equal canonical
  N-Quads. The core theorem of RDFC-1.0.
- `RenamingInvariance` — its syntactic form under an injective
  relabelling.

The remaining obligations are enumerated at those definitions: the
§4.4 grouping needs sorting-is-a-permutation (the sort lemmas here
prove sortedness only), §4.7 needs an induction on `hndqRun`'s fuel,
§4.4 step 5.3's first-explored-wins tie-break needs an automorphism
argument, and the §4.5 lemmas carry an `isBnodeGraphLabel gi = false`
hypothesis.

### Change to `RDF/Graph.lean` that would remove a hypothesis (not made)

`NamedGraph.name` is an `Iri` (a `String`), so a blank-node graph label
is carried as the `"_:label"` sentinel that
`Syntax.NQuads.graphLabelToIri` writes — the same representation the F\*
source uses. The relabelling lemmas above therefore exclude blank-node
graph names, because proving them needs
`("_:" ++ x).startsWith "_:"`-style facts about `String` append, which
the byte-backed `String` of Lean 4.33 does not give up cheaply. Giving
`NamedGraph.name` a sum type (`Iri | BNodeId`) would drop the
hypothesis from four theorems and delete
`isBnodeGraphLabel`/`bnodeOfGraphLabel` from this module entirely. That
is an edit to `RDF/Graph.lean`, owned elsewhere.
## OWL tableau clash calculus (`OWL/Tableau*.lean`, 2026-08-22)

Folded in from the duplicate track
[#468](https://github.com/danbri/factoidal/issues/468) (a remote
session opened a parallel `formal/lean/` package unaware of this one;
that directory is deleted and its content lives here under the
`L4Factoidal.OWL` namespace).

- F* correspondence: NOT a port of `Tableau.Refute.fst`'s 4,682-line
  search engine. It is the declarative counterpart: the model theory
  (OWL 2 Direct Semantics Table 5, unqualified-cardinality fragment)
  plus a clash calculus whose constructors match the engine's first
  clash rules (complement, owl:Nothing, C3/C4 count clash,
  differentFrom max-cardinality refutation, disjunction branching).
  The engine file carries these soundness arguments as comments;
  `TableauTheorems.lean` machine-checks them
  (`refuted_sound : Refuted A → no model of A`).
- Assumption report: no `axiom`, no `sorry`, no `partial`;
  `derives_sound` axiom-free; `refuted_sound` /
  `refuted_not_consistent` use `propext` + `Quot.sound`.
- Individual and role names are raw `String`, not `RDF.Core`'s
  wf-IRI subtype — reconnecting them is part of the next rung, with
  the ∃-witness rule, the role box, qualified cardinality, and the
  `Type`-valued certificate checker (ladder on
  [#466](https://github.com/danbri/factoidal/issues/466)).
## Stage: Turtle 1.1 + TriG 1.1 + RFC 3986 reference resolution (2026-08-22)

Ladder rung: the gating item for a manifest-driven Lean W3C harness
(https://github.com/danbri/factoidal/issues/466, and
`docs/designissues/2026-08-22-lean4-w3c-harness.md` — the manifests are
Turtle, so nothing manifest-driven can run before a Turtle parser
exists). Branch `lean4/syntax-turtle`.

### Module correspondence (append)

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/Syntax/IriResolve.lean` | `RDF.IRI.fst` (`parse_iri`, `remove_dot_segments_step`/`remove_dot_segments`, `merge_paths`, `transform_references`, `recompose`, `resolve_iri_v2`), which `Parser.Turtle.resolve_iri` and `SPARQL11.IRI.Resolve.resolve_iri` both delegate to | RFC 3986 §3 decomposition, §5.2.2/§5.2.3/§5.2.4/§5.3, §5.2 top level. All 24 normal + 20 abnormal RFC 3986 §5.4 examples as build-time `#guard`s (the F\* source parks the same battery behind `if false` to spare Z3, so this port CHECKS strictly more than the original) |
| `L4Factoidal/Syntax/Turtle.lean` | `Parser.Turtle.fst` + `Parser.TurtleScanner.fst` | Turtle 1.1 productions [1]–[17], [128s]/[133s]/[135s]–[141s], [161s]–[172s]; `parseTurtle (text) (base := none) (mode := .rdf11)` |
| `L4Factoidal/Syntax/TriG.lean` | `Parser.TriG.fst` | TriG 1.1 productions [1g]–[7g] on top of Turtle; `parseTriG (text) (base := none) (mode := .rdf11) : Except ParseError Dataset` |
| `L4Factoidal/Syntax/TurtleTests.lean` | (new) | 127 `#guard`s, one section per grammar production, plus prefix/base interplay, relative-IRI resolution, collection nesting, negative cases, and Turtle→N-Triples→N-Triples round-trips through the landed `Graph.toNTriples` |
| `L4Factoidal/Syntax/TurtleTheorems.lean` | (new) | 22 proved theorems + 21 `#guard`s: RFC 3986 §5.2.2 base-independence and the `resolve base abs = abs` identity, §5.2.4 no-dot-segment invariant, collection chain shape, `maxUnderscoreRun` monotonicity |
| `Harness/TurtleProbe.lean` (`lean_exe l4turtle-probe`) | (new; the role `bin/w3c-runner/w3c_runner.ml` plays for the F\* tree) | walks the real W3C directories, reading each suite's base IRI out of its own `manifest.ttl` with this parser |

### Measured against the real W3C files

`lake build && ./.lake/build/bin/l4turtle-probe third_party/testing/w3c/rdf/rdf11`

| Suite | parse-positive | reject-negative | eval-iso |
|---|---|---|---|
| rdf-turtle | 222 of 223 | 94 of 94 | 111 of 111 |
| rdf-trig | 242 of 242 | 115 of 115 | 107 of 108 |

`manifest.ttl` parses in both suites (2338 triples / 313 `mf:action`
entries; 2637 / 356), which is the rung's actual deliverable. These are
PROBE numbers from a directory walk, not conformance scores: the probe
uses the `-bad-` naming convention plus `.ttl`/`.nt` sibling pairs, and
does not yet read test TYPES from the manifest. A conformance claim
waits for the `l4w3c` runner.

The two failures, both named rather than rounded away:

- `test-38.ttl` — a UTF-16 surrogate PAIR written as two `\u` escapes.
  Rejected: `\uD801` is not a Unicode scalar value, and RDF 1.1
  Turtle's UCHAR denotes a code point, not a UTF-16 code unit. The F\*
  source rejects it too (`valid_codepoint`). The file is NOT one of the
  manifest's 313 entries — the probe reports how many walked files the
  manifest does not list (4 for rdf-turtle, 1 for rdf-trig).
- `labeled_blank_node_graph.trig` — a blank-node GRAPH NAME. See the
  Core/Graph note below.

### Translation decisions (append)

- **Fuel is kept exactly where the F\* source needs it** — the
  whitespace/comment skipper, the name-token scanner, the string
  bodies, the numeric collector, `remove_dot_segments_step`, and the
  mutually-recursive term block. Every budget is derived from the
  remaining input length, so it cannot bind before the input is
  consumed. Everything else recurses structurally, with no fuel: the
  F\* byte scanners in `RDF.IRI.fst` (`find_colon`,
  `find_authority_end_iri`, `find_path_end_iri`, `find_hash_iri`,
  `find_slash_iri`, `find_last_slash_iri`, `scheme_tail_ok`) all
  collapse into `List.span` / `List.dropWhile` / `List.all`.
- **One name-character table, four consumers.** Turtle's [163s]
  PN_CHARS_BASE / [164s] PN_CHARS_U / [166s] PN_CHARS are DERIVED from
  the tables `Syntax.Lexing` already carries for BLANK_NODE_LABEL
  (`isBnodeStartChar` = PN_CHARS_U plus digits, `isBnodeChar` =
  PN_CHARS plus `.`), rather than re-tabulated. IRIREF, STRING,
  LANGTAG, BLANK_NODE_LABEL, UCHAR and ECHAR reading are
  `Syntax.Lexing`'s landed readers, reused unchanged.
- **The F\* `resolve_iri_hint` colon short-circuit is NOT reproduced.**
  `Parser.Turtle.resolve_iri_hint st rel has_colon` returns `rel`
  unchanged whenever the RAW IRIREF text contains a colon ANYWHERE.
  That is right for a genuine scheme but wrong for a relative reference
  with a colon in a later path segment (`<a/b:c>`), which RFC 3986 §4.2
  makes relative. This port always routes through
  `Syntax.IriResolve.resolveIri`, which is a no-op on an absolute
  reference (proved: `resolveIri_base_irrelevant`,
  `resolveIri_eq_self`) and correct on `<a/b:c>`.
- **Grammar-exact PN_PREFIX and prefixed-name start.** The F\*
  `validate_pname_ns_from` tests every position against one ASCII class
  and so also accepts a leading digit; `Parser.TurtleScanner`'s
  `is_ascii_name_start` rejects a NON-ASCII PN_CHARS_BASE opening
  character outright, so a non-ASCII prefix cannot be a prefixed name
  there. This port follows [167s]/[139s] instead: the first character
  must be PN_CHARS_BASE, ASCII or not. Both suites stay green under the
  stricter reading.
- **Blank-node label scoping.** The F\* source mints `_anon0`,
  `_anon1`, … and passes user labels through unchanged, so a document
  writing `_:_anon0` COLLIDES with a generated label. This port keeps
  user labels UNCHANGED (needed: a TriG blank-node graph name `_:G` has
  to stay comparable with the `_:G` of an N-Quads fixture, because
  `RDF.Dataset` keys named graphs by label string) and instead prefixes
  every GENERATED label with `anon` plus one more consecutive `_` than
  occurs anywhere in the document text (`freshBnodePrefix`). A
  BLANK_NODE_LABEL is a substring of the text, so it cannot contain a
  longer underscore run — the two namespaces are disjoint by
  construction.
- **TriG error recovery not ported.** `Parser.TriG.parse_graph_body`
  skips the offending line, sets `has_error`, and lets the strict entry
  point turn that into `None` later. This port fails at the first error
  and returns its message and position. Same accept/reject verdict,
  better diagnostic; the recovery machinery is a CLI affordance, like
  the lenient Turtle entry points already recorded as out of scope.

### RDF 1.2 (`Mode_12`) coverage — stated exactly

COVERED: object-position triple terms `<<( s p o )>>` (port of
`parse_turtle_triple_term`); the reifier `~ (iri | BlankNode)?` and the
annotation block `{| predicateObjectList |}` after an object, both
emitting `rdf:reifies` triples (port of `parse_annotations`); and
directional language tags `@lang--ltr` / `@lang--rtl` via
`Syntax.Lexing.readLangDir12`.

NOT COVERED (open gaps, not silent drops): the reified-triple form
`<< s p o (~ r)? >>` in subject/object position (F\*
`parse_reified_triple` / `parse_rt_subject` / `parse_rt_object`), and
the `VERSION` / `@version` directive (F\* `parse_version_directive`).
Neither is exercised by the RDF 1.1 suites this stage is measured
against.

### Assumption report — F\* primitives this stage replaces

- `Parser.FastString`'s byte-indexed primitives (`fs_byte_length`,
  `fs_byte_index`, `fs_byte_at`, `fs_byte_sub`, `fs_cp_at`) are
  `assume val` realisations in the F\* tree and are used throughout
  `Parser.Turtle.fst`, `Parser.TurtleScanner.fst`, `Parser.TriG.fst`,
  and `RDF.IRI.fst`. This stage needs NONE of them. The native Lean
  operations that replaced them, by F\* primitive:
  `fs_byte_length` → `List.length` on `String.toList`;
  `fs_byte_index` / `fs_byte_at` → ordinary cons-pattern matching;
  `fs_byte_sub` → `List.span` / `List.take` / `String.ofList`;
  `fs_cp_at` → nothing at all, because `String.toList` already decoded
  the UTF-8 and a Lean `Char` already IS a Unicode scalar value. Each
  F\* function that carried an ASCII-byte fast path beside a codepoint
  slow path (`validate_pname_ns_from`, `validate_pn_local_from`,
  `parse_long_string_body`, `scan_name_body_end`) becomes ONE
  definition here.
- ZERO semantic `assume val`s were carried over, and no Lean equivalent
  (`axiom`, `sorry`, `opaque`, `@[extern]`, `partial`, `native_decide`)
  appears in any file of this stage. `#print axioms` on all nine
  audited theorems in `TurtleTheorems.lean` and on `parseTurtle` /
  `parseTriG` / `resolveIri` reports exactly `propext`,
  `Classical.choice`, `Quot.sound`.
- `unescape_pn_local`'s raw-byte-fragment workaround (F\* issue #325 —
  a non-ASCII local name carrying a PN_LOCAL_ESC resolved to mojibake
  because the escape path re-encoded each element as UTF-8) has no
  counterpart here: the port works on codepoints throughout, and
  `TurtleTests.lean` checks the exact case the F\* bug hit.

### Core/Graph change that would help (not made — this stage adds files only)

`RDF.Graph.NamedGraph` keys a named graph by an `Iri` STRING, and
`RDF.Isomorphism.Dataset.namesMatchB` therefore matches named graphs by
STRING equality. A blank-node graph name consequently cannot take part
in the blank-node bijection: `labeled_blank_node_graph.trig` writes
`_:g` where its `.nq` fixture writes `_:b1`, and the two datasets are
isomorphic in the RDF 1.1 Concepts §4/§3.6 sense but are reported
unequal. (`alternating_bnode_graphs.trig` passes only because both
sides happen to use the label `G`.) The fix is in the DATASET MODEL,
not in either parser: `NamedGraph.name` wants to be a `Subject` (or an
`Iri` plus `BNodeId` sum), and `Dataset.checkMapping` wants to apply
the candidate blank-node mapping to graph names before comparing them.
That is one test today; it will be every `graph-*` entry of the
rdf-canon suite later. The same file also still lacks
`deriving DecidableEq` on `NamedGraph`/`Dataset`, as the previous stage
recorded.
## Addendum (2026-08-22): SPARQL Query Results formats (SRX/SRJ/CSV/TSV)

Scope: SPARQL 1.1 Query Results XML, JSON, CSV, and TSV Formats —
parsing AND serialising all four, a prerequisite for the Lean W3C
harness (`docs/designissues/2026-08-22-lean4-w3c-harness.md` names
`.srx`/`.srj`/`.csv`/`.tsv` expected-result files as gating items).
Adds `L4Factoidal/SPARQL/{Results,ResultsXml,ResultsJson,
ResultsCsvTsv,ResultsTests,ResultsTheorems}.lean` (1,577 lines: 77
definitions, 4 theorems in `ResultsTheorems.lean` plus the reflexivity/
transitivity-style facts folded into the format modules, 56 `#guard`
checks in `ResultsTests.lean`). `lake build` remains green with all
six modules wired into `L4Factoidal.lean`.

### Module correspondence

| Lean 4 | Ports (F*) | Notes |
|---|---|---|
| `L4Factoidal/SPARQL/Results.lean` | (new; the shared model the four F* modules below each reinvent a slice of) | `QueryResult` (`bindings`/`boolean` — CONSTRUCT/DESCRIBE graphs are out of scope, see the file's own header), `ResultsError`, and the shared `mkResultUri`/`mkResultBnode`/`mkResultLiteral`/`mkResultDirLiteral`/`mkResultTriple`/`parseResultDirection` constructors ported from `Parser.JSONResults.fst`'s `mk_literal`/`mk_dir_literal` (which `Parser.SRX.fst`/`Parser.CSVResults.fst` each redefine near-verbatim) |
| `L4Factoidal/SPARQL/ResultsXml.lean` | `Parser.SRX.fst` (parsing) + `SPARQL.Protocol.fst` Part 10 (`xml_term`/`serialise_response_xml`/`serialise_response_boolean_xml`, serialising) | Built on `L4Factoidal.XML` (`Document`/`Parser`) — walks the already-parsed infoset, does not re-implement XML parsing. Deviation: the root element must (namespace-flexibly) be `<sparql>` — the F* source never checks this |
| `L4Factoidal/SPARQL/ResultsJson.lean` | `Parser.JSONResults.fst` (parsing) + `SPARQL.Protocol.fst` Part 9 (`json_term`/`serialise_response_json`/`serialise_response_boolean_json`, serialising) | Built on `L4Factoidal.JSON` (`Value`/`Parser`/`Serialize`) — binding values are `Json` trees rendered via the already-verified compact writer; the document wrapper is hand-composed exactly as `serialise_response_json` composes it (load-bearing for the N-row shape theorem, see `ResultsTheorems.lean`). Deviations: `parse_srj_results`/`parse_srj_boolean` unified into one `parseSrj` dispatching on `"boolean"` presence; `"head"` is now REQUIRED (§2.1's grammar has it non-optional; the F* source silently defaults to `vars = []` when absent) |
| `L4Factoidal/SPARQL/ResultsCsvTsv.lean` | `Parser.CSVResults.fst` (parsing) + `SPARQL.Protocol.fst` Part 11 (`csv_plain_term`/`serialise_response_csv`, `tsv_term`/`serialise_response_tsv`, serialising) | TSV's IRI/blank-node/literal/triple-term cell syntax is IS (approximately) N-Triples syntax, so this port REUSES `Syntax.Lexing`'s `readIriRef`/`readBlankNodeLabel` and `Syntax.NTriples`'s `readLiteral`/`mkIri`/`Term.toNTriples` rather than hand-rolling a second caret/at-sign scanner the way `parse_tsv_quoted_literal` does — a genuine simplification, not just a different implementation of the same primitive (same shape of win as the N-Triples/N-Quads stage's byte-vs-codepoint collapse). Bare numeric TSV field sniffing (`isIntegerStr`/`isDecimalStr`/`isDoubleStr`) is a direct port, since bare numerals are not N-Triples syntax. Also carries `Term.eqbCsvLenient`, the Lean counterpart of `bin/w3c-runner/w3c_runner.ml`'s `term_equal_csv_lenient` — the lossy-comparison rule the W3C harness will need for every CSV-backed test |
| `L4Factoidal/SPARQL/ResultsTests.lean` | (new; fixtures copied verbatim from `third_party/testing/w3c/sparql/`) | 56 `#guard`s: round-trips (bindings incl. unbound variables, language-tagged/directional/typed literals, blank nodes, RDF 1.2 triple terms, booleans, empty results) for SRX/SRJ/TSV; forward-only fixture parsing for CSV (round-trip only claimed for CSV-native `xsd:string` content — CSV is lossy by spec); real W3C fixtures (`pp08.srx`, `projexp04.srx`, `langstring-datatype.srj`, `plain-string-same.srj`, `csvtsv01.csv`, `csvtsv01.tsv`); negative cases per format (wrong root element, malformed XML, bad `<boolean>` text; missing `head`, bad JSON syntax, non-object root; empty CSV input; malformed TSV IRIREF; CSV/TSV `.boolean` serialisation, which the format defines no encoding for) |
| `L4Factoidal/SPARQL/ResultsTheorems.lean` | `SPARQL.Protocol.RoundTrip.fst`'s `lemma_srj_n_rows` (native re-proof) | `toSrj_bindings_shape`: the N-row SRJ shape theorem, proved by `rfl` — see below for why this port needs no accumulator-bridging proof the F* lemma exists to supply. `rowsJoined_nil`/`_singleton`/`_cons_cons`/`_cons`: the N = 0/1/≥2 decomposition. `SrjRoundTripGoal`: the general round-trip goal, stated as a `def : Prop` (not a `theorem` — see the file for the named, JSON-layer-inherited gap) |

### Assumption report — F* sources ported

`Parser.SRX.fst`, `Parser.JSONResults.fst`, `Parser.CSVResults.fst`,
`SPARQL.Protocol.fst`: **zero** `assume val`s in all four (confirmed
2026-08-22 by `grep -c "assume val"` on each file). Nothing was
assumed away on the F* side, so the port declares no
`axiom`/`opaque`/`partial` on the Lean side either — confirmed by
`#print axioms` on every theorem in `ResultsTheorems.lean`: exactly
`propext`/`Classical.choice`/`Quot.sound`, this tree's standard
baseline.

### Why the N-row shape theorem needed no accumulator bridge

`SPARQL.Protocol.fst`'s `serialise_response_json` computes its row
list via `json_rows_body_acc` (a TAIL-RECURSIVE accumulator) plus
`List.Tot.rev`, a deliberate rewrite (`tav5`, 2026-04-26) of the
original direct recursion — the direct form overflowed the macOS
pthread 544 KB default stack on a real 3M-row dataset. `lemma_srj_n_rows`
exists entirely to prove that rewrite still computes the SAME string
as the original direct spec (`json_rows_joined`). This Lean port is
the tree's own SPECIFICATION evaluator (list scans, no tail-call/
stack-depth engineering, per `PORT_NOTES.md`'s translation-decisions
section above and every prior addendum), so `ResultsJson.lean`'s
`toSrj` is written directly against `rowsJoined` with no accumulator
detour — there is nothing to bridge, and the theorem is `rfl`. This is
not a shortcut around the F* proof; it is what NOT carrying the
performance rewrite into the spec tree buys back. A future Lean
PERFORMANCE variant of this serialiser (if one is ever built for a
large-graph demo) would need the accumulator rewrite and would then
need this same bridging lemma, proved the same way the F* tree proved
it.

### A finding: `Parser.CSVResults.fst`'s TSV reader/writer asymmetry for RDF 1.2 triple terms

`SPARQL.Protocol.fst`'s `tsv_term` SERIALISES an RDF 1.2 triple-term
binding as `<<( s <p> o )>>`, but `Parser.CSVResults.fst`'s
`parse_tsv_value` has NO case for a `<<(`-prefixed field at all — only
`<...>` (IRI), `"..."` (literal), `_:...` (blank node), and bare
numerals. The F* TSV format is therefore write-only for triple terms:
a value written by the F* tree's own serialiser cannot be read back by
its own parser. `ResultsCsvTsv.lean`'s `parseTsvValue` reproduces this
gap faithfully (documented at its call site and pinned by a `#guard`
in `ResultsTests.lean` showing the field is REJECTED, not
mis-parsed — the leading `<<` is not a legal IRIREF start, so
`readIriRef` fails loudly) rather than silently adding parsing support
the F* source lacks. Worth fixing in the F* tree first (iron rule #1)
before either port grows a `<<( )>>` TSV reader.
## The SPARQL query stage (2026-08-22)

### The layering choice

`SPARQL/Expr.lean` imports `SPARQL/Algebra.lean`, because a §17
expression can contain a graph pattern (EXISTS). So `Algebra.lean`
cannot import `Expr.lean`, and the wider constructor set had to land
on one side or the other. Two options were on the table: keep the
algebra abstract and put the `Expr`-carrying AST one file up, or move
`GraphPattern` out of `Algebra.lean` entirely.

**The first was taken.** `Algebra.lean` keeps a reviewable
§18.5/§18.6 semantics in which every expression-shaped detail is an
opaque argument:

| constructor | abstract argument | concrete form supplied by `Query.lean` |
|---|---|---|
| `filter` / `leftJoin` | `Binding → Bool` | EBV of an `Expr` |
| `bind` | `Binding → Option Term` | `Expr` evaluated, then `toTerm?` |
| `lateral` | `Binding → GraphPattern` | the row-substituted right operand |
| `service` | `Option Graph` | the endpoint resolved through `EvalEnv.services` |
| `modified` | `SolutionSeq → SolutionSeq` | a sub-SELECT's §18.2.4 pipeline |

`QueryPattern` in `Query.lean` mirrors every F\* `group_graph_pattern`
constructor one-for-one, so it is the AST a future parser targets, and
`QueryPattern.lower : EvalEnv → QueryPattern → GraphPattern` is the
single compilation step between the two layers. A consequence worth
naming: every theorem in `Invariants.lean` and `QueryTheorems.lean`
about the algebra stays free of expression machinery.

### What this stage does NOT port

* **DESCRIBE.** `QueryForm.describe` exists in the AST for shape, and
  evaluates to nothing — exactly as the F\* `QF_Describe` arm does.
  The description a DESCRIBE returns is left to implementations by
  §16.4, and this port makes no choice for it.
* **The OWL-rewriter bookkeeping** the F\* `eval_select_query` carries:
  `rewrite_query_bnodes_pattern` (WHERE-clause blank nodes becoming
  fresh variables — a parser-level concern),
  `strip_synthetic_bnode_vars`, and `strip_rewrite_internal_vars`.
  Those hide variables `OWL.QueryRewrite` invents; there is no OWL
  rewriter on the Lean side to invent them.
* **A sub-SELECT's dataset clauses.** The SPARQL 1.1 grammar's
  `SubSelect ::= SelectClause WhereClause SolutionModifier
  ValuesClause` has no `DatasetClause`, so the field is carried for
  shape and does not re-scope the active graph inside a sub-SELECT.
* **Fresh-node builtins under a query** (BNODE/UUID/STRUUID/RAND). The
  F\* pipeline threads a per-row / per-item freshness context
  (`fx_ctx_put`) for them; those builtins are not implemented on the
  Lean side (see the §17 assumption table), so the context has nothing
  to feed and is not ported.
* **Every performance layer**, as elsewhere in this port: no planner,
  no index seam, no hash join, no tail-recursive accumulator rewrites.
  `groupSolutions` appends, `distinctSolutions` scans. The F\* source's
  own comments mark those rewrites as stack-safety and cost fixes over
  exactly this semantics.

### Deviations recorded

* **`COUNT(DISTINCT *)`.** The F\* source builds a string key per row
  and deduplicates the keys; this port calls `distinctSolutions`,
  which is the §18.3 row equality DISTINCT itself uses. The two agree
  wherever the string key and the row equality agree, and the row
  equality is the one the spec actually defines.
* **`REDUCED` is the identity.** §18.4 permits removing some, all, or
  none of the duplicates; keeping all is conformant, and is what the
  F\* source specifies.
* **ORDER BY is a stable insertion sort**, not `List.sortWith`. The
  point is the proof: `sortSolutions_perm` is four lines against a
  sort written here, and would otherwise depend on a library sort's
  specification. §15.1 says nothing about ties, so stability is a free
  choice; it is the least surprising one.
* **`SELECT *` header order.** BGP matching CONSES each new binding
  onto the front of the row (`Binding.bind`, as `sm_bind` does), so
  `collectVarsInOrder` reports the object variable before the subject
  variable for `?s :p ?o`. Pinned in `QueryTests.lean` so the order is
  a decision on record rather than an accident.
