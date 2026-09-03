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
| `L4Factoidal/RDF/Graph.lean` | `RDF.Graph.fsti` (+ `RDF.Dataset.Merge` renaming) | graphs as lists with set-semantics ops, datasets (`NamedGraph.name : Subject` — an IRI OR a blank node, RDF 1.1 Concepts §4; DIVERGES from the F\* `named_graph.ng_name : iri`, see below), graph- and dataset-wide blank-node renaming, membership theorems |
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
| `L4Factoidal/RDF/IsomorphismTheorems.lean` | (new) | reflexivity (graphs; datasets under distinct graph names) and SOUNDNESS for both, plus the checker-correctness sub-lemmas `Graph.setEq_of_setEqB`, `bijectiveCert_inj`, `bijectiveCert_onto`, `uniq_of_nodup_name` |
| `L4Factoidal/RDF/IsomorphismTests.lean` | (new) | 85 `#guard`s: relabelling, chain vs fork, ground-set comparison, order/duplicate insensitivity, the two-blank-node cycle vs two self-loops, RDF 1.2 nested blank nodes, dataset-wide blank-node scoping, named-graph matching (IRI names ground, blank-node names matched up to the same bijection), the budget refusal |
| `L4Factoidal/XML/Document.lean` | `Parser.XML.fst` (AST + character classes) | XML 1.0 5th ed. `[2] Char`, `[3] S`, `[4] NameStartChar`, `[4a] NameChar`, `[5] Name`; the parse tree (`Attribute`, `Node`); the prolog model (`XmlDecl` `[23]`, `Doctype` `[28]`, `Document` `[1]`); the Namespaces §3 name model (`QNameSplit`, `ExpandedName`); the convenience accessors |
| `L4Factoidal/XML/Parser.lean` | `Parser.XML.fst` (the parser) | `parseXML : String → Except XmlError Document`. In XML the parser IS the well-formedness decision; the module header lists all twenty constraints it enforces and every scope cut it inherits |
| `L4Factoidal/XML/Namespaces.lean` | `XML.Namespaces.fst` | `[7] QName` splitting, prefix-scope resolution down the tree, the default namespace, the reserved `xml`/`xmlns` prefixes and their two reserved namespace names, 1.0-vs-1.1 undeclaring, §6.3 uniqueness after expansion, undeclared-prefix rejection |
| `L4Factoidal/XML/Wellformedness.lean` | `XML.Wellformedness.fst` | `[4] NCName` (= `[5] Name` minus `:`) and the RDF/XML §7.2.4–§7.2.12 forbidden-name and conflicting-attribute checks. Despite the F\* module's name this is NOT generic XML well-formedness — see below |
| `L4Factoidal/XML/Theorems.lean` | (new) | a structural well-formedness checker over the parse tree, a serialiser, the proved tag-matching theorem, and the two general claims stated as named `Prop`s |
| `L4Factoidal/XML/Tests.lean` | (new) | 118 `#guard`s: hub post 25's two live documents, every constraint in `Parser.lean`'s header, the namespace layer, reflexivity and round-trip fixtures |
| `L4Factoidal/XML/ConfProbe.lean` | `bin/xml-runner/xml_runner.ml` (the driver only) | the `xmlconf-probe` executable: reads W3C conformance file paths from stdin, prints a well-formed/malformed verdict per file |
| `L4Factoidal/Syntax/RdfXml.lean` | `Parser.RDFXML.fst` + the RDF/XML half of `XML.Wellformedness.fst` | RDF 1.1 XML Syntax §7.2: `parseRdfXml : String → Option String → Except ParseError Graph`. Node/property element dispatch, all four `rdf:parseType` forms, `rdf:li`↦`rdf:_n`, `[7.2.23]` `rdf:ID` uniqueness, §7.3 reification, XML Base + `xml:lang` scoping. Namespace-CORRECT where the F\* is not — see below |
| `L4Factoidal/Syntax/RdfXmlTests.lean` | (new) | 89 `#guard`s: at least one per §7.2 production cited in the file, plus the negative cases the W3C `rdf-xml` suite carries (`rdf:li` as a node element, non-NCName `rdf:ID`, duplicate `rdf:ID`, property attribute + `parseType`, `xml:base` fragment, withdrawn `rdf:aboutEach`/`bagID`) |
| `L4Factoidal/Syntax/RdfXmlTheorems.lean` | (new) | 37 theorems: the `rdf:_n` counter is strictly increasing and never reuses an ordinal; `xml:lang` inherits when absent and clears on `""`; base resolution reduces DEFINITIONALLY to `Syntax.resolveIri`; generated and `rdf:nodeID` blank-node labels cannot collide; the XML-scoped vs document-scoped split of `restoreScope` |
| `Harness/RdfXmlProbe.lean` | `bin/w3c-runner` (the driver role only) | the `l4rdfxml-probe` executable: walks `third_party/testing/w3c/rdf/rdf11/rdf-xml` by directory layout (no manifest, so no dependency on the Turtle parser), scores parse/reject/isomorphism with denominators |
| `L4Factoidal/JSON/Value.lean` | `Parser.JSON.fst` `json_val` + accessors | `Json` (`null`/`bool`/`string`/`number`/`array`/`object`), hand-written `DecidableEq` (nested-inductive — `deriving` does not apply, see file header), `field?`/`getString?`/`getBool?`/`getArray?`/`getStringArray?` |
| `L4Factoidal/JSON/Parser.lean` | `Parser.JSON.fst` (the parser half) | `parseJson : String → Except JsonError Json`, total via fuel (mirrors the F\* fuel discipline); indexes a `List Char`, not raw bytes — see file header on why (Lean `Char` = full Unicode scalar value; sidesteps `Parser.FastString`'s byte-slicing machinery and this toolchain's `String.Pos` API) |
| `L4Factoidal/JSON/Serialize.lean` | `SPARQL.JSON.Escape.fst` (`json_escape`) + the writer shape of `Parser.JSONLD.fst`'s `jcanon_serialize` (NOT its JCS canonicalisation/field-sorting) | `Json.toString` (compact) and `Json.toStringPretty` (new; no F\* counterpart) |
| `L4Factoidal/JSON/Tests.lean` | (new) | 61 `#guard`s: RFC 8259 §13 example, every escape form, surrogate-pair decode, number-lexeme preservation, rejection cases, key-order/duplicate preservation, parse∘serialize round-trips |
| `L4Factoidal/JSONLD/Loader.lean` | `JSONLD.Loader.fst` | the document-loader ABSTRACTION. The F\* module's whole content is one `assume val jsonld_load_document : string -> option string`; here it is `abbrev Loader := String → Option String`, a PARAMETER threaded through context processing. Plus `tableLoader` / `prefixLoader` / `cacheTableOfIndex` (the vendored `third_party/jsonld-context-cache/` index reader) for a probe to build one |
| `L4Factoidal/JSONLD/Context.lean` | `JSONLD.Context.fst` | JSON-LD 1.1 API §4.1 Context Processing, §4.2 Create Term Definition, §5.2.2 IRI Expansion; `ContainerKind`, `TermDef`, `ActiveContext`; `@protected` / `@propagate` / `@version` / `@import`; remote-context fuel + cycle guard; property- and type-scoped context application. Failures are `Except JsonLdError`, and `JsonLdError.code` is the exact string a W3C manifest's `expectErrorCode` uses |
| `L4Factoidal/JSONLD/Expand.lean` | `JSONLD.Expand.fst` | §5.1 Expansion + §5.2 Value Expansion: node objects, value objects, `@list`/`@set`, every `@container` mapping (`@index`, `@language`, `@id`, `@type`, `@graph`, `@graph`+`@id`, `@graph`+`@index`, property-valued `@index`), `@reverse` (term and inline block), `@nest`, `@included`, `@json`, the free-floating drop, duplicate-key merging, lexicographic member ordering. Frame expansion is NOT ported — see below |
| `L4Factoidal/JSONLD/ToRdf.lean` | `Parser.JSONLD.fst` (the toRdf half) | §8.2 Deserialize JSON-LD to RDF, §8.3 Object to RDF Conversion, §8.4 List to RDF Conversion, §8.6 Data Round Tripping (`numberCanonicalize`) and the `rdfDirection` option, plus RFC 8785 JCS (`jcsDocument`) including the pure exact-integer shortest-round-trip binary64 formatter for `@json` numbers with more than 15 significant digits |
| `L4Factoidal/JSONLD/Tests.lean` | (new) | 86 `#guard`s from the JSON-LD 1.1 spec's own examples: IRI expansion, compact IRIs, `@base`/`@vocab`, context processing, every §4.2 error condition, expansion shapes, list/language/type maps, `@reverse`, `@nest`, toRdf triples, §8.6 number decisions, RFC 8785 formatting, `rdfDirection` |
| `L4Factoidal/JSONLD/Theorems.lean` | (new) | keyword identity and keyword-alias expansion under §5.2.2; absolute-IRI identity; the §4.2 protected-term rules; `findTerm_removeTerm` (what makes the `defined[term] = false` strip effective); the three pop-chain theorems that reconcile this port's explicit stack with the F\* `ac_previous` field; blank-node issuer injectivity (reusing `RDF.Canonical.mkLabel_inj`); and the banned-empty-context-fallback rule stated as a theorem |
| `Harness/JsonLdProbe.lean` | `bin/jsonld-runner/jsonld_runner.ml` | the `l4jsonld-probe` executable: reads the real W3C `toRdf-manifest.jsonld`, runs every entry, compares datasets, prints labelled counts |
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
  selectivity planner (`choose_best_tp`), fuel bounds, and
  tail-recursion (`*_tr`) rewrites are performance machinery over
  this same semantics and are not ported. The keyed hash join IS
  ported (2026-08-25): `hashJoin` / `evalBgpIdx` in `Algebra.lean`
  bucket by the canonicalised key `Term.joinKey` (the
  `join_canon_term` counterpart, `RDF/Core.lean`), and
  `SPARQL/IndexedEvalRefinement.lean` proves each LIST-equal to its
  spec twin (`hashJoin_eq_join`, `evalBgpIdx_eq_evalBgp`);
  `GraphPattern.evalIn` runs the indexed pair through those
  equalities, and the spec pair remains the statement of record.
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
  does not enforce RDF 1.1 §4's uniqueness of graph names. That
  hypothesis is STILL needed after the `Subject` change below — the
  reason is duplicate names, not their type.

## Decision: a graph name is an IRI or a blank node (2026-08-22)

`RDF 1.1 Concepts` §4 says a named graph's name "may be an IRI or a
blank node". The F\* tree's `named_graph.ng_name` is a bare `iri`, so
`RDF.NQuads` there packs a blank-node name into that string as
`"_:label"` (see
`docs/designissues/2026-04-25-nquads-bnode-graph-fix.md`). This port
first copied that shape and then dropped it: **`NamedGraph.name` is a
`Subject`** — the sum `iri WfIri | bnode BNodeId`, which is exactly the
two cases §4 allows. This is a deliberate DIVERGENCE from the F\*
source, and it is the first one in the data model.

What forced it: the W3C harness (`lake exe l4w3c`) failed the two
`rdf-trig` `TestTrigEval` entries `anonymous_blank_node_graph` and
`labeled_blank_node_graph`. `Dataset.namesMatchB` compared graph names
by raw STRING equality before any bijection search ran, so a dataset
whose graph is named `_:g` was never isomorphic to one named `_:b1` —
though under §4 plus §3.6 they are. A string sentinel cannot be
compared up to a blank-node bijection; a sum type can.

What the type change bought, beyond the two tests:

- `Dataset.renameBnodes` renames graph NAMES (RDF 1.1 §3.4 scopes
  labels to the document, and §4 puts names in that scope), so
  dataset-wide renaming is now complete.
- `Dataset.bnodes` counts a blank node that occurs ONLY as a graph
  name, so the bijection search ranges over it.
- `Dataset.namesMatchB` takes the candidate mapping; a separate
  mapping-free `Dataset.namesPrune` (IRI names correspond, blank-node
  name COUNTS agree — both invariant under renaming) does the
  pre-filter that string equality used to do.
- `RDF/Canonical.lean`'s `QQuad` carries `Option Subject`; every
  `"_:"`-sentinel test (`isBnodeGraphLabel`, `bnodeOfGraphLabel`) is
  gone, and the graph slot reuses `canonSubject`/`relabelSubject`.
- The §4.5 relabelling lemmas in `RDF/CanonicalTheorems.lean` LOST
  their `isBnodeGraphLabel gi = false` hypotheses:
  `hashFirstDegreeQuads_rename` and its three sub-lemmas now hold for
  every dataset. The old exclusion was never mathematical — it was the
  string sentinel, whose `startsWith`/append reasoning Lean's
  byte-backed `String` does not give up cheaply.
- `NamedGraph` and `Dataset` derive `DecidableEq` (`Subject` has it),
  so `Syntax/SyntaxTests.lean`'s local `namedGraphsEq` workaround is
  deleted.
- SPARQL: `GRAPH <iri>` and `FROM NAMED` use the new
  `Dataset.lookupNamedIri`; `GRAPH ?g` binds `?g` to `name.toTerm`, so
  it can bind a blank node — which is what §13.3 describes.

Measured after the change: `lake exe l4w3c` over the four rdf11 syntax
manifests plus rdf-canon prints `rdf-trig: 356 pass, 0 fail, 0 skip, 0
unsupported (out of 356)` and `TOTAL: 912 pass, 0 fail, 0 skip, 0
unsupported (out of 912)`; `l4rdfc-probe` 86 of 86; `l4turtle-probe`
eval-iso 111 of 111 (Turtle) and 108 of 108 (TriG).
`Dataset.isomorphic?_sound` and `Dataset.isomorphic?_refl` stayed
proved on `[propext, Classical.choice, Quot.sound]`.
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

- `JSONLD.Loader.fst`: **one** `assume val`, and it is the only one in
  the whole JSON-LD stack (`JSONLD.Context.fst`, `JSONLD.Expand.fst`,
  and `Parser.JSONLD.fst` have zero between them, confirmed by grep).
  It is `assume val jsonld_load_document : string -> option string`,
  the remote-context fetch. In F\* it is AMBIENT: `context_process`
  calls it directly, and each consumer binary installs a realisation
  into a mutable ref cell at start-up
  (`minimal_regrettable_glue_code_each_with_an_open_issue/275_jsonld_document_loader.sh`).
  **DISSOLVED BY PARAMETERISATION** here: `abbrev Loader := String →
  Option String`, passed explicitly to `contextProcess` and to every
  entry point above it. There is no global state, no `opaque`, no
  `@[extern]`, and no ambient effect — context processing is a total
  function of its inputs, the loader among them. Real I/O lives in
  `Harness/JsonLdProbe.lean`, which builds a `Loader` value after
  reading files in `IO`. The `jsonld-context-cache` skill's rule that
  an empty-context fallback is BANNED is not merely obeyed but proved:
  `Theorems.lean`'s `fetchRemoteContext_none` and
  `contextProcess_string_none_loader` show that a loader resolving
  nothing yields `loading remote context failed`, never an empty active
  context.

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

## Next stages

The authoritative ladder is https://github.com/danbri/factoidal/issues/466 (every landing and open rung, with its branch). Queued as of 2026-08-22: `NamedGraph.name : Subject` (blank-node graph names — the two remaining rdf-trig fails), RDF/XML, JSON-LD, the SPARQL string parser, OWL 2 RL (all in flight), then SPARQL Update, SHACL Core, the regex engine, xsd:dateTime, the model-theoretic halves of the RDFS/OWL theorems, and closing the stated-but-unproved round-trip goals.
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

## Stage: RDF/XML (`Syntax/RdfXml*.lean`, `Harness/RdfXmlProbe.lean`, 2026-08-22)

Ports `formal/fstar/Parser.RDFXML.fst` (1402 lines) together with the
RDF/XML-specific half of `formal/fstar/XML.Wellformedness.fst`. Built on
the landed XML infoset parser (`XML/Parser.lean`), the namespace layer
(`XML/Namespaces.lean`) and the RFC 3986 resolver
(`Syntax/IriResolve.lean`); the `rdf:XMLLiteral` value comparison reuses
`RDF/XmlCanon.lean` through `Literal.eqb`, exactly as the F\* reuses
`RDF.Term.fsti`'s `xmlc_*` family.

### Measured against the real W3C files

`lake exe l4rdfxml-probe` over
`third_party/testing/w3c/rdf/rdf11/rdf-xml` (28 test directories,
173 `.rdf` files):

| Check | Result |
|---|---|
| parse-positive (non-`error*.rdf` must parse) | 132 pass, 0 fail (out of 132) |
| reject-negative (`error*.rdf` must be rejected) | 41 pass, 0 fail (out of 41) |
| eval-isomorphic (graph vs sibling `.nt`, RDF 1.1 Concepts §3.6) | 130 pass, 2 fail (out of 132) |

The two isomorphism failures are `rdfms-xml-literal-namespaces/test001`
and `test002`, which upstream WITHDREW from `manifest.ttl` (both entries
are commented out there). They are withdrawn because their expectation
contradicts the graded `xml-canon` tests: `xml-literal-namespaces`
expects Exclusive XML Canonicalization proper — each element of the
`rdf:parseType="Literal"` content carrying only the declarations IT
visibly utilizes — while `xml-canon/test001`, which IS graded, expects
every ambient declaration on the apex element. No single serialiser
satisfies both. This port satisfies the graded one, which is the same
choice `Parser.RDFXML.fst` makes (its issue-#446 comment records the
same tension). The F\* tree scores 166 pass, 0 fail on the manifest-graded
subset; this probe is directory-driven and therefore also walks the
withdrawn files.

`lake build` is green with zero `sorry` / user `axiom` /
`native_decide` / `partial`; the axiom audit prints
`[propext, Classical.choice, Quot.sound]` or less for every theorem.
Sabotage-checked: changing `St.resetLi` to reset the `rdf:li` counter to
2 instead of 1 fails three named `#guard`s in `RdfXmlTests.lean`.

### Assumption report

`Parser.RDFXML.fst` is **PURE** — confirmed by reading the whole module.
It contains no `assume val`, no effectful call-out, and no `--admit` or
`--lax` pragma; the one `#push-options "--z3rlimit 60"` is an SMT budget,
not an escape hatch. Every definition is `Tot`, with an explicit `fuel`
argument wherever F\* could not see termination. This port therefore
needs no purity workaround: the F\* `fuel : nat` becomes structural
recursion on a Lean `Nat`, and the `has_error : bool` flag becomes an
`Option ParseError` that names the violated rule.

`XML.Wellformedness.fst` is likewise pure, and was already ported as
`XML/Wellformedness.lean`.

### Where this port is namespace-correct and the F\* source is not

`Parser.RDFXML.fst` looks attributes up by their LITERAL spelling —
`find_attr "rdf:about"`, `find_attr "xml:lang"` — against a
`namespaces` map that `initial_state` SEEDS with five bindings
(`rdf`, `rdfs`, `xml`, `xmlns`, `xsd`). Two consequences follow that
"Namespaces in XML" forbids: a document that never declares `rdf:` still
has its `rdf:about` honoured, and a document that binds `foo:` to the
RDF namespace has its `foo:about` ignored.

This port resolves every element and attribute name through
`XML.resolveElementName` / `XML.resolveAttributeName` against the real
in-scope bindings, starting from `XML.initialScope` (which binds only
`xml`, as §3 requires). The `rdf-ns-prefix-confusion` directory — 11
files that bind the RDF namespace to unusual prefixes and bind unusual
namespaces to `rdf:` — passes on that basis rather than by accident.

### Deliberate differences from the F\* source

1. **Blank-node label spaces are disjoint.** The F\* mints
   `rdfxml_b<N>` and uses an `rdf:nodeID` value verbatim, so a document
   containing `rdf:nodeID="rdfxml_b0"` can name a node the parser also
   mints. This port writes generated labels `b<N>` and `rdf:nodeID`
   labels `n<value>`, which differ in their first character —
   `genLabel_ne_nodeIdLabel` proves the collision is impossible. Labels
   are document-local and graph identity is up to renaming (RDF 1.1
   Concepts §3.4), so the change costs nothing observable.
2. **`nodeElement` RETURNS its subject.** The F\* re-derives it at each
   call site with `determine_subject_readonly`, and its own comment
   records the counter-desynchronisation bug that produced (orphan
   `rdf:first` targets for anonymous collection members, hit by the OWL
   class-expression fixtures). Returning it removes the class of bug.
3. **RDF 1.2 is NOT ported.** `rdf:version="1.2"` gating, `its:dir` base
   direction, `rdf:parseType="Triple"` triple terms, and the
   `rdf:annotation` / `rdf:annotationNodeID` reifiers all live in the
   F\* source and are all skipped here: they belong to a separate W3C
   draft and a separate suite (`rdf12/rdf-xml`), which this stage does
   not claim.
4. **The F\*'s datatyped-with-element-children leniency is NOT
   ported.** `Parser.RDFXML.fst` treats a property element carrying both
   `rdf:datatype` and element children as an opaque XML literal, for OWL
   fixtures outside the RDF/XML suite. §7.2 has no such production, so
   this port rejects it.
5. **Errors say which rule was violated.** `parse_rdfxml_strict` returns
   `None`; `parseRdfXml` returns the first `ParseError`, with the §7.2
   production number in its message.

### What `XML/` should gain (not made — `XML/` is read-only for this stage)

`XML/Wellformedness.lean` states the RDF/XML attribute constraints over
LITERAL attribute spellings, inherited from the F\* module it ports:
`hasAttr "rdf:parseType" attrs`, `validateRdfIdAttr` matching
`a.name == "rdf:ID"`. Those predicates are wrong for any document that
does not use the customary prefixes, which is exactly what
`rdf-ns-prefix-confusion` tests. This stage therefore could NOT reuse
`checkConflictingAttrsNode` / `checkConflictingAttrsProperty` /
`validateRdfIdAttr` and states namespace-correct equivalents locally in
`RdfXml.lean` (`checkCommonAttrs`, `checkNodeAttrs`,
`checkPropertyAttrs`, `checkIdNCNames`).

What `XML/Wellformedness.lean` should gain, so the duplication can go
away:

  * variants of the three conflict checks and of `validateRdfIdAttr`
    taking a resolved view of the attributes — either
    `List (XML.ExpandedName × String)`, or `(NsScope, List Attribute)` —
    so the rule is stated over expanded names rather than spellings;
  * `hasAttrNs (scope) (ns localName) (attrs) : Bool` and
    `findAttrNs : … → Option String` alongside the existing `hasAttr` /
    `findAttr`, since every RDF/XML lookup wants the namespace-aware
    form (this port has private `findNsAttr` / `hasRdfAttr` copies);
  * the existing spelling-based functions kept only if some caller
    genuinely needs a non-namespace view; nothing in this port does.

Two smaller items, both worked around locally:

  * `XML/Namespaces.lean` has no "render the in-scope declarations"
    function, which `[7.2.17] parseTypeLiteralPropertyElt` needs.
    `RdfXml.renderNsDecls` / `dedupScope` do it here. If a second
    consumer appears (XSLT serialisation, XML canonicalization proper),
    that belongs in `XML/`.
  * `XML/` has no XML serialiser at all — `XML/Theorems.lean` has one
    for its round-trip theorem, but it is not exported for reuse and it
    does not implement c14n's open+close and escaping rules.
    `RdfXml.serializeNode` is a local, c14n-shaped one. An
    `XML/Canonical.lean` implementing Exclusive XML Canonicalization
    properly would let §7.2.17 stop approximating — and would let the
    two withdrawn `rdfms-xml-literal-namespaces` tests be revisited
    deliberately rather than by default.

## Stage: JSON-LD 1.1 context processing, expansion, and toRdf (2026-08-22)

Six files under `L4Factoidal/JSONLD/` plus `Harness/JsonLdProbe.lean`
(lake target `l4jsonld-probe`). Sources: `JSONLD.Context.fst` (1985
lines), `JSONLD.Expand.fst` (2355), `Parser.JSONLD.fst` (1459, toRdf
half), `JSONLD.Loader.fst` (67).

### Measured

`lake exe l4jsonld-probe` against the real W3C
`third_party/testing/json-ld/tests/toRdf-manifest.jsonld`:

**467 pass, 0 fail, 0 skip (out of 467)** — 345 of 345
PositiveEvaluationTest, 16 of 16 PositiveSyntaxTest, 106 of 106
NegativeEvaluationTest.

Because a perfect score is exactly the shape a broken measurement
takes, three checks back it up, all reported by the probe itself:

1. **It measured something.** Across the 345 positive tests the engine
   produced 1499 quads against 1492 expected (the difference is
   duplicate triples, which RDF set semantics collapses). Only 11
   positive tests compare an empty dataset to an empty dataset, and
   those are the suite's own free-floating-node fixtures.
2. **Sabotage testing.** Deleting the `@vocab` concatenation in
   `expandFallback` took the score to 345 pass, 122 fail. Deleting the
   `rdf:rest` triple in §8.4's list conversion took it to 442 pass, 25
   fail. Both restored, both re-measured green.
3. **The negative tests fail for the RIGHT reason.** 100 of the 106
   produce exactly the error code the manifest's `expectErrorCode`
   names. The six that differ are listed by the probe; each is a
   genuine failure at a different (earlier or stricter) rule, not a
   pass by accident. The F\* source cannot make this check at all — it
   returns a bare `option`.

### The F\* side-by-side

Measured 2026-08-22 at integration time, same manifest, same machine:
`bin/darwin-arm64/jsonld_runner third_party/testing/json-ld/tests/toRdf-manifest.jsonld`
prints `jsonld-toRdf: 467 pass, 0 fail, 0 skip (out of 467)`. The two
trees agree on every test. (The porting agent had reported the F\*
number as a stale 2026-07-05 lower bound of 399 because it did not
find the committed `darwin-arm64` binary; the binary was there — a
lesson for reports: `ls bin/<platform>/` before claiming a runner is
absent.) The Lean side adds one check the F\* runner cannot make: the
negative tests' error codes, 103 of 106 matching the manifest's
`expectErrorCode`.

### Translation decisions

- **The active context's pop chain.** F\* `active_context` carries
  `ac_previous : option active_context`, a self-referential record
  field. Lean structures are not recursive, so this port splits it:
  `ActiveContext = { cur : ContextCore, prev : List ContextCore }`. The
  F\* source performs exactly three operations on that field, and
  `pop` / `setPrev` / `clearPrev` reproduce them; `Theorems.lean`
  proves all three agree with the F\* semantics.
- **Errors are values with codes.** F\* returns `option` everywhere, so
  every failure is indistinguishable. Here every failure is
  `Except JsonLdError`, with 45 constructors covering the JSON-LD 1.1
  API §5 error conditions, and `JsonLdError.code` returning the exact
  manifest string. The control flow is unchanged: each F\* `None` site
  maps one-to-one onto an `.error` site.
- **Fuel.** The F\* context-processing group uses a lexicographic
  `%[fuel; ctx]` metric so an inline context never spends remote-fetch
  depth. This port carries the two budgets as separate arguments
  (`fuel` for termination, `rfuel` for remote depth) with
  `termination_by fuel`, which is the same discipline with a simpler
  proof obligation.
- **Codepoints, not bytes.** As in every earlier stage, `fs_byte_length`
  / `jbyte_at` / `fs_byte_sub` become code-point operations on
  `String.toList`. Every character the algorithms test for is ASCII
  (`:` `/` `@` `_` `#` `.`), and splitting UTF-8 at an ASCII position
  gives the same substring either way.
- **Blank-node labels come from `RDF.Canonical.mkLabel`.** Rather than
  a parallel `"_jld_anon" ++ toString n`, the issuer reuses the label
  function RDFC-1.0 canonicalization already has, so `mkLabel_inj`
  gives issuer injectivity for free (`freshBnode_injective`).
- **The shortest-round-trip binary64 formatter is pure.** RFC 8785
  §3.2.2.3 needs, for a JSON-literal number with more than 15
  significant digits, the shortest decimal of the NEAREST double. The
  F\* source implements Steele & White by exact rational arithmetic on
  unbounded `int`/`nat`; this port does the same on Lean `Nat`/`Int`.
  No float type, no host call-out, no `@[extern]`.

### Scoped out, and said so

- **Frame expansion.** `ContextCore.frameExpansion` exists so the record
  matches the F\* `active_context`, but the JSON-LD Framing relaxations
  the F\* source gates on it (the five framing keywords passing through
  expansion, Value Pattern `{}`/`[]`/array shapes surviving
  value-object validation, array-shaped `@id`) are NOT ported. Framing
  is a separate specification with a separate suite; this stage targets
  §5.1/§5.2/§8 and the toRdf manifest. `JSONLD.Compact`,
  `JSONLD.Flatten`, `JSONLD.Frame`, and `JSONLD.FromRdf` are likewise
  not ported.
- **Generalized RDF**, matching the F\* source: a blank-node PREDICATE
  is dropped rather than emitted, because this codebase's N-Quads
  grammar cannot express one either way.

### Two comparison routes in the probe, both reported

`Dataset.isomorphic?` is the primary comparison, per the brief. Where it
cannot decide, the probe falls back to RDFC-1.0 canonical N-Quads
equality (`Dataset.canonicalNQuads`), the same comparison
`jsonld_runner.ml` uses. Both routes are sound dataset-equality tests,
and the probe prints how many passes needed the second one rather than
hiding it.

That count is itself a measurement of the `NamedGraph.name : Subject`
change this branch merged from `claude/main`. Against the older
IRI-string graph names, **31 of the 467 passes** needed the canonical
route, because the bounded isomorphism search matched named graphs by
NAME STRING and so could not put a blank-node graph name into the
blank-node bijection at all. After the merge that drops to **6** — and
those six are the other limitation, the hard 16-blank-node search
budget, not the graph-name one. So the dataset-model change the
Turtle/TriG stage asked for is worth 25 of this suite's comparisons on
its own, and JSON-LD `@graph` ids that are blank nodes now map straight
across with no `"_:<label>"` sentinel anywhere in `ToRdf.lean`.

### One leniency, counted

`Syntax.parseNQuads` is STRICT: any malformed line aborts the whole
parse. The F\* `Parser.NQuads.parse_nquads` skips a malformed line and
continues, and the suite depends on that — `0118-out.nq`'s blank-node-
PREDICATE lines are unparseable under either grammar, and this engine
likewise never emits them. So the probe parses expected files LINE BY
LINE and drops what does not parse, reproducing the F\* runner's
behaviour. **10 lines are dropped across the whole suite**, and the
probe prints that total so the leniency is visible rather than silent.

### Assumptions

Zero `sorry`, zero user `axiom`, zero `native_decide`, zero `partial`
across all six files. `#print axioms` on the ten audited theorems
reports exactly `propext`, `Classical.choice`, `Quot.sound` (and
`pop_setPrev` depends on none at all). The one F\* `assume val` in the
stack is dissolved into the `Loader` parameter — see the assumption
report above.

The authoritative ladder is https://github.com/danbri/factoidal/issues/466 (every landing and open rung, with its branch). Landed 2026-08-22: `NamedGraph.name : Subject` (blank-node graph names — the two remaining rdf-trig fails are now green; see the decision section above). Queued as of 2026-08-22: RDF/XML, JSON-LD, the SPARQL string parser, OWL 2 RL (all in flight), then SPARQL Update, SHACL Core, the regex engine, xsd:dateTime, the model-theoretic halves of the RDFS/OWL theorems, and closing the stated-but-unproved round-trip goals.
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

## The SPARQL query-syntax stage (2026-08-22)

The last rung before the W3C `sparql11` query suites can run through
a Lean harness: the tokenizer and grammar that turn query TEXT into
the `SPARQL/Query.lean` AST, plus the reviewer-facing SSE printer.

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/SPARQL/Tokenizer.lean` | `SPARQL11.Parser.fst` Parts 2-3 (`is_*` character classes, `process_iri_escapes`, `decode_string_escape`, `scan_iri`/`scan_string`/`scan_pname_or_keyword`/`scan_number`/`scan_bnode_label`/`scan_var_name`/`scan_langtag`, `keyword_of_upper`, `next_token`, `tokenize`, `tokenize_12`) | the §19.8 TERMINAL layer: `Token` (one constructor per F\* `token` case, update keywords included), `PosToken` carrying a character offset, `tokenize` / `tokenize12` / `tokenizeAt`. The `sparql12` lexer flag becomes `SparqlVersion` |
| `L4Factoidal/SPARQL/Parser.lean` | `SPARQL11.Parser.fst` Parts 4-7 (the combinators and the whole recursive descent) + Part 8 (`sse_*`) | the §19.8 PRODUCTION layer: `parseSparql : String → Option String → SparqlVersion → Except ParseError Query`, and `Query.toSse`. One mutual block, structural on `fuel`, seeded at the F\*'s own 10000 |
| `L4Factoidal/SPARQL/ParserTests.lean` | (new) | 224 `#guard`s: the terminal layer, one per grammar production family, every well-formedness rejection with the F\*'s message text, and 20 `toSse` snapshots |
| `L4Factoidal/SPARQL/ParserTheorems.lean` | (new) | `tokenize` always ends with `eof` (induction on the fuel), `expectTok` succeeds exactly on a matching head, and the two top-level contracts: an accepted query has valid blank-node scope and consumed its whole stream |
| `Harness/SparqlSyntaxProbe.lean` (`lean_exe l4sparql-probe`) | `bin/w3c-runner` (the driver's job only) | runs the parser over the real `third_party/testing/w3c/sparql/sparql11/*.rq`, classifying by each suite's `manifest.ttl` read with the Lean Turtle parser |

### Measured, 2026-08-22

`lake exe l4sparql-probe third_party/testing/w3c/sparql/sparql11`:

```
syntax-query   63 positive pass, 0 fail (out of 63)
               31 negative pass, 0 fail (out of 31)
syntax-fed      3 positive pass, 0 fail (out of 3)
query-eval     297 parsed of 297; 9 of 9 negative-syntax entries rejected
TOTAL          403 pass, 0 fail (out of 403 manifest-listed query files)
```

Not scored, and reported as such by the probe rather than hidden: 12
`.rq` files present on disk that no manifest names (`property-path/`'s
`{n,m}` path quantifiers, dropped before SPARQL 1.1 became a
Recommendation, plus two `entailment/rif*` leftovers), and 55 `.ru`
UPDATE requests, which a QUERY parser does not read.

This is a probe result, not a conformance claim. Iron rule #6 is met
for the SPARQL side only when a Lean runner reads the same manifests
`bin/w3c-runner` does, end to end, and compares RESULTS.

### Why the probe reads manifests

The Turtle stage's probe classifies by file NAME, because a manifest
cannot be read until a Turtle parser exists. That reasoning does not
carry over: the Turtle parser is landed, and the name convention is
WRONG for this corpus. `syntax-BINDscope6.rq`, `syntax-BINDscope7.rq`,
`syntax-BINDscope8.rq`, `syntax-SELECTscope2.rq`,
`syntax-bindings-09.rq`, `aggregates/agg08.rq`,
`aggregates/agg09.rq`, `aggregates/agg11.rq`, `aggregates/agg12.rq`,
`grouping/group06.rq`, `grouping/group07.rq` and
`construct/constructwhere05.rq` are all `mf:NegativeSyntaxTest11` and
none of them contains `bad`. The first probe run scored every one of
those CORRECT rejections as a failure. So `SparqlSyntaxProbe` parses
each `manifest.ttl` with `L4Factoidal.Syntax.Turtle` and classifies by
`rdf:type` and `mf:action` / `qt:query`, keeping the name convention
only as the fallback for a directory with no manifest.

### Assumption report

`SPARQL11.Parser.fst` contains **zero `assume val`s** — measured, not
assumed (`grep -c '^assume val' formal/fstar/SPARQL11.Parser.fst`
returns `0`; the only two matches for the string `assume val` in that
file are prose in its header comment). It is the largest F\* module
ported so far with nothing to dissolve: no clock, no host regex, no
extension registry. Everything it needs is a total function of its
input string, and the Lean port is the same.

Two F\* primitives have no Lean counterpart, for the reason the XML
stage already recorded:

* `utf8_of_codepoint` — a hand-written UTF-8 encoder. The F\* indexes
  raw BYTES through `Parser.FastString`, so a resolved `\uXXXX` escape
  has to be re-encoded. Lean's `Char` IS a Unicode scalar value, so a
  resolved escape is one `Char.ofNatAux` and the encoder disappears.
* `fs_byte_length` / `substring` / `char_at` — byte-position
  arithmetic. The port threads `(pos, List Char)` instead.

### Deviations, stated plainly

* **`ParseError.pos` is a CHARACTER offset**, where the F\* reports a
  byte offset. The F\* `token_stream` carries no positions at all;
  `PosToken` adds them so a rejection can name WHERE.
* **A `\uD800`-`\uDFFF` escape inside an IRIREF is DROPPED**, where
  the F\* emits three bytes. No Lean `Char` holds a surrogate. The F\*
  itself drops an out-of-Unicode-range escape (`utf8_of_codepoint`
  returns `""`), so this extends an existing behaviour rather than
  inventing one. Inside a STRING both reject outright.
* **SPARQL 1.1 UPDATE is not ported.** The tokenizer emits the update
  keywords (dropping them would make `INSERT` lex as a prefixed name
  and silently change which QUERIES parse), but `parse_single_update_op`
  and its clique are a separate rung. `parseSparql` is a query parser.
* **The jena-text `text:query` object grammar is not ported** — a
  vendor extension outside §19.8, whose encoding lives in
  `SPARQL.FullText.fst` with no Lean counterpart to encode into.
* **SPARQL 1.2 bare reified triples `<< s p o >>`, the `~` reifier and
  `{| … |}` annotation blocks are not ported.** All four tokens are
  lexed; `QueryPattern` has no reifier arm to build into. Triple-term
  PATTERNS `<<( s p o )>>` and the `TRIPLE`/`SUBJECT`/`PREDICATE`/
  `OBJECT`/`isTRIPLE` builtins ARE ported, because
  `PatternTerm.tripleTerm` and the matching `Expr` constructors exist.
* **`resolve_pname` does not undo `[173] PN_LOCAL_ESC` backslashes.**
  The F\* concatenates the namespace and the raw local lexeme; the
  port keeps that, because changing it would change which W3C fixtures
  resolve to which IRI.

### What the AST should gain

Three findings the port could not fix from the parser side, because
`Query.lean` / `Expr.lean` were out of scope for this rung:

1. **`Expr.existsPat` / `Expr.notExistsPat` should carry a
   `QueryPattern`, not a `GraphPattern`.** The grammar produces a
   `QueryPattern`; the AST demands the lowered ALGEBRA type, whose
   `filter`, `leftJoin`, `bind`, `serviceVar` and `modified` fields
   are FUNCTIONS. Consequences the parser absorbs today: it lowers
   with `QueryPattern.lower emptyEnv`, so (a) `Query.toSse` cannot
   print inside an EXISTS with full fidelity — `sseGraphPattern`
   writes `_` where a field is a function, and everything OUTSIDE an
   EXISTS is byte-identical to `sse_ggp`; and (b) the F\*
   `validate_bnode_scope_expr`'s walk into `E_Exists` is replaced by
   running the same check on the operand AT CONSTRUCTION TIME, which
   is equivalent (that F\* function returns `(ok, [])` for an EXISTS,
   so an EXISTS operand's labels never escape its own scope) but is
   not where a reader would look for it. The fix needs `Expr` and
   `Query` in ONE mutual block.
2. **`Query.exprHasAggregate` is NARROWER than the F\*
   `expr_has_aggregate`.** The Lean version (`Query.lean` line 657)
   handles `arith`/`compare`/`and`/`or`/`not`/`unaryMinus`/
   `unaryPlus`/`cond` and answers `false` for everything else, so
   `COUNT(CONCAT(SUM(?x)))` would not be caught as a nested
   aggregate. The parser therefore carries its own
   `exprHasAggregateFull`, which covers every constructor the way the
   F\* does. `Query.exprHasAggregate` should be widened to match, and
   the parser's copy then deleted.
3. **`Expr` has no constructor for `RAND`, `UUID`, `STRUUID` or
   `BNODE`.** The parser follows the F\* and models each as
   `Expr.functionCall` on an `fn:` IRI, which is faithful — but it
   means those four §17 builtins are indistinguishable from a
   user-supplied extension function at the AST level.

Also worth recording, though not an AST gap: `Expr` derives NOTHING
(no `DecidableEq`, no `Repr`), because `existsPat` carries a
`GraphPattern` with function fields. Every parser test therefore
compares through `Query.toSse` strings rather than by structural
equality. Fixing finding 1 would make `DecidableEq` derivable and the
tests structural.

### A Lean cost finding: `decide` does not scale over a parser

Measured here, and recorded so the next session does not pay for it
twice. `decide` discharges a goal by KERNEL evaluation, and the
tokenizer is structurally recursive through `Nat`-fuel and
`List Char`, so the kernel goes through `brecOn`:

| goal | kernel cost |
|---|---|
| `tokensOf (tokenize "SELECT") = [.select, .eof]` | 0.3 s, 0.43 GB |
| `tokensOf (tokenize "<http://a/b>") = [.iri …, .eof]` | 72 s, 10.0 GB |
| ten such theorems in one file | out of memory, `lean` killed (signal 9) |

Twelve characters cost ten gigabytes. `#guard` evaluates through the
COMPILER instead and checks the same fact at build time for no cost,
so concrete-input facts are `#guard`s and `ParserTheorems.lean` keeps
exactly one `decide` PROOF (the cheapest goal) to show the technique
exists. The general facts are structural inductions, which the kernel
checks symbolically and cheaply.

The same trap appears one level up: `split at h` on a hypothesis whose
scrutinee mentions `pSelectQuery topFuel …` weak-head-normalises ten
thousand fuel levels and exhausts memory. `parseSparql` was therefore
split into `parseSparqlWith (fuel : Nat) …` plus a wrapper, so a proof
can keep the fuel SYMBOLIC; and the proofs use `cases h : e`, which
cases on the `Except` constructor without ever evaluating `e`.
## OWL 2 RL/RDF rule-based closure (`OWL/RL*.lean`, `Harness/OwlProbe`, 2026-08-22)

The Datalog materialisation layer of OWL 2 RL, in the same
spec / implementation / theorems shape as the rdfs-core port. Namespace
`L4Factoidal.OWL.RL` — NOT the flat `L4Factoidal.OWL`, which
`OWL/Tableau.lean` already occupies (it holds its own `Derives`).

### Module correspondence (append)

| Lean 4 | Ports (F\*) | Notes |
|---|---|---|
| `L4Factoidal/OWL/Vocabulary.lean` | vocabulary blocks of `OWL.RL.Spec.fst` (lines 109-182, 623-681, 1082-1097) + the `owl_*` constants interleaved through `OWL.Closure.fsti` | 38 IRIs and the two `xsd:nonNegativeInteger` cardinality literals, each with an `rfl` well-formedness witness. The five RDF/RDFS terms shared with rdfs-core are `abbrev`-re-exported from `RDFS/Vocabulary.lean`, so the two closures agree on them by construction |
| `L4Factoidal/OWL/RLRules.lean` | `OWL.RL.Spec.fst` (the rule transcription) | SPECIFICATION: `inductive Derives` with 55 constructors covering 50 rows of the OWL 2 RL/RDF tables, `inductive Clash` with 13 no-consequent rows, the `LIST[…]` premise as `ListMember` / `ListDenotes`, the batched premises as `TypesAll` / `ChainHolds` / `SharesKeyValues`, plus `mono` and `cut`. Every constructor cites its table row id |
| `L4Factoidal/OWL/RLClosure.lean` | the extractable half of `OWL.Closure.fsti` (`owl_rule_*`, `owl_rl_closure`, `is_inconsistent`) | IMPLEMENTATION: 47 row functions, `conclusionsList`/`conclusionsFrom`/`stepConclusions`/`step`, the fuel/length-test loop `closure`, `closureFix` with a stated bound, the collection walks `listElems`/`listSeqs`/`chainTargets`, and `detectClash` over 13 clash-row decisions |
| `L4Factoidal/OWL/RLTheorems.lean` | `OWL.RL.Refinement.fst` (the licensing theorems) | T1 extensivity, T2 soundness assembled from ONE LEMMA PER ROW (47), T3 monotonicity, T4 completeness at saturation (all 55 constructor cases), the fuel dichotomy, clash soundness from one lemma per clash row (13), and the collection-walk soundness/existence lemmas |
| `L4Factoidal/OWL/RLTests.lean` | (new) | 98 `#guard`s: per-family positives AND the paired negative check, the clash rows, idempotence past saturation |
| `Harness/OwlProbe.lean` | driver role only (`bin/owl-runner/owl_runner.ml`: `triple_matches`, `load_imports_into_premise`, the four `run_*_test` judges, `OWL_DirectMapping_Filter.exclude_annotation_triples`) | the `l4owl-probe` executable: census of the six W3C OWL 2 catalogs, then every RDF/XML case parsed with `Syntax/RdfXml.lean`, closed with `OWL.RL.step` under fuel + wall-clock cap, and judged per test type (see "Measured against the real corpus" below, 2026-08-22 second entry) |

### Rows ported, and rows not ported

`OWL.Closure.fsti` holds 77 `owl_rule_*` functions. Its own ledger
(transcribed into `OWL.RL.Spec.fst`, landing 4) classifies each as
`[row]` (implements a named W3C table row), `[ext]` (a sound extension
with no table row), `[axm]` (materialises an axiomatic-triple table) or
`[mode]` (fires only under a catalog semantics mode).

**Ported — 50 rows.** Table 4 equality: eq-ref (3 conclusions), eq-sym,
eq-trans, eq-rep-s, eq-rep-p, eq-rep-o. Table 4 properties: prp-dom,
prp-rng, prp-fp, prp-ifp, prp-symp, prp-trp, prp-spo1, prp-spo2,
prp-eqp1, prp-eqp2, prp-inv1, prp-inv2, prp-key. Table 5: cls-thing,
cls-nothing1, cls-int1, cls-int2, cls-uni, cls-svf1, cls-svf2, cls-avf,
cls-hv1, cls-hv2, cls-maxc2, cls-oo. Table 6: cax-sco, cax-eqc1,
cax-eqc2. Table 8: scm-cls (4 conclusions), scm-sco, scm-eqc1 (2),
scm-eqc2, scm-spo, scm-eqp1 (2), scm-eqp2, scm-dom1, scm-dom2,
scm-rng1, scm-rng2, scm-int, scm-uni. Clash rows: eq-diff1, prp-irp,
prp-asyp, prp-pdw, prp-npa1, prp-npa2, cls-nothing2, cls-com,
cls-maxc1, cls-maxqc1, cls-maxqc2, cax-dw, cax-adc.

Six of those rows reach the F\* engine through the layer BELOW it
rather than through an `owl_rule_*` of its own:
`owl_rl_closure_step_mode` runs on top of
`owl_rdfs_closure_with_reflexivity`, so prp-dom, prp-rng, prp-spo1,
cax-sco, scm-sco and scm-spo arrive as rdfs2, rdfs3, rdfs7, rdfs9,
rdfs11 and rdfs5. This port has no layering and names them under the
OWL table ids the Recommendation gives them.

**Not ported, with the F\* module's own reason.**

* **Table 7 (dt-type1, dt-type2, dt-eq, dt-diff, dt-not-type).** These
  quantify over DATA VALUES, and a value space belongs to the DATATYPE
  MAP, not to the graph. `OWL.RL.Spec.fst` states them PARAMETRICALLY
  for exactly that reason and fixes no datatype map. This port fixes
  none either, so there is nothing to instantiate. (`dt-not-type` was
  on the port brief's clash list; this is why it is absent.)
* **Every `[ext]` engine rule** — the comprehension-witness layer
  (`svf2_existential_witness`, `minc1_bridge`, `cls_hasself1/2`,
  `cls_svf_thing_*`), the differentFrom-synthesis family
  (`pdw_to_differentFrom`, `fp_diff_to_diff`, `cax_dw_to_differentFrom`),
  the chain/transitivity bridges, and the `#236` `cls_maxqc_comp`
  anchor machinery whose narrowness CLAUDE.md records. Their
  justification lives in each F\* rule's own banner, not in the
  Recommendation; porting them would import claims this port cannot
  cite a row for.
* **Every `[mode]` rule** — there are no catalog semantics modes on the
  Lean side.
* **cls-maxqc3 / cls-maxqc4** (F\* `owl_rule_cls_maxqc34`): the two
  qualified-cardinality DERIVING rows. Their CLASH siblings cls-maxqc1
  and cls-maxqc2 ARE ported.
* **eq-diff2, eq-diff3, prp-adp, cax-adp** — the AllDifferent /
  AllDisjointProperties clash rows. Same shape as cax-adc, which is
  ported; omitted for size only.
* **scm-op, scm-dp, scm-hv, scm-svf1, scm-svf2, scm-avf1, scm-avf2** —
  Table 8 restriction-comparison rows. The F\* engine ledger lists no
  `owl_rule_*` for any of them either, so nothing is lost against the
  F\* engine's own row coverage.

One asymmetry in the other direction: **cls-svf1 is ported here but the
F\* ledger names no `owl_rule_cls_svf1`** — the F\* engine reaches that
row's effect through `cls_svf2_qualified` and the comprehension-witness
rules. This port implements the row as the Recommendation writes it.

### Proof status

* **T1 extensivity** — `closure_extensive`, no hypothesis, any fuel.
* **T2 soundness (the LICENSING theorem)** — `closure_sound`: every
  triple the closure computes has a derivation in the rule relation.
  Assembled from **47 per-row lemmas, one per row function, all
  proved**: `eqRefSFor_sound` … `scmUniFor_sound`. Per-row status is
  therefore uniform — every ported row is proved licensed, with no row
  parked. This is the statement `OWL.RL.Refinement.fst` makes and
  `docs/theorem-registry.md` §1 tracks per row.
* **T3 monotonicity** — `closure_mono_of_saturated`, derived from T2 +
  `Derives.mono` + T4 and therefore carrying T4's two hypotheses. The
  unconditional same-fuel form is not proved and is not expected to
  hold pointwise: two runs stop at different rounds.
* **T4 completeness at saturation** — `complete_of_saturated` and
  `closure_complete_of_saturated`: everything derivable is in a
  saturated closure. **All 55 constructor cases proved**, under two
  named hypotheses — saturation (which
  `closure_saturated_or_underfueled` turns into "the fuel was not
  exhausted") and `ListFuelAdequate` (see below).
* **Clash soundness** — `detectClash_sound`: every `true` verdict is a
  real `Clash`, from 13 per-row lemmas.
* **The fuel dichotomy** — `closure_saturated_or_underfueled`: either
  the closure is saturated or it grew by at least one triple per unit
  of fuel.
* **Truth preservation (model theory)** — NOT ported, and its statement
  shape is written out in `RLTheorems.lean`'s header referencing
  `OWL.Semantics.fst` / `OWL.Semantics.Soundness.fst`. T2 is
  PROOF-THEORETIC. Do not read it as the F\* model-theoretic soundness
  theorem.

`#print axioms` on `closure_extensive`, `closure_sound`,
`complete_of_saturated`, `closure_complete_of_saturated`,
`closure_mono_of_saturated`, `closure_saturated_or_underfueled`,
`detectClash_sound`, `conclusionsFrom_sound`, `clashFrom_sound`,
`listSeqs_sound`, `exists_fuel_listSeqs`, `chainTargets_complete`,
`typesAllB_complete`, `sharesKeyValuesB_complete`, `Derives.cut` and
`Derives.mono` reports
`[propext, Classical.choice, Quot.sound]` and nothing else — no
`sorryAx`, no local axiom. No `sorry`, no `native_decide`; the one
`partial` in the tree is `elementsOfAux` in the PROBE, which is not
part of the verified library.

### Two specification corrections the proofs found

1. **`Derives.cut` is FALSE if the collection-valued rows read the
   graph directly.** A closure round can DERIVE an `rdf:first` or
   `rdf:rest` triple (eq-rep-s and prp-spo1 both can), so a later
   round's collection walk may rest on structure the earlier graph
   never asserted, and there is no way to pull that walk back. The
   eight collection-valued constructors therefore carry a COLLECTION
   GRAPH `gc` and the side condition `hgc : ∀ u ∈ gc, Derives g u`.
   That occurrence of `Derives` is strictly positive, so no mutual
   inductive is needed, and `cut` then needs no extra hypothesis at
   all. Caught while proving `closure_sound`.
2. **`ListDenotes.cons` needs `node.toTerm ≠ Term.iri rdfNil`.** RDF
   Schema §5.1 gives `rdf:nil` one meaning; a graph that also hangs an
   `rdf:first` off it is malformed, and the F\* `owl_list_denotes`
   (which omits the guard) admits a reading of such a graph that the
   executable walk cannot produce. Without the guard
   `exists_fuel_listSeqs` is false. Caught while proving it.

### T4: the rdfs-core pattern transfers, with one added hypothesis

`complete_of_saturated` is the rdfs-core proof at 55 cases instead of
6, and it is CHEAPER per case than the rdfs-core one: exact
deduplication removes the list-membership / `Graph.mem` asymmetry the
rdfs-core proof has to carry, so each case is "the IHs give the
premises as exact members, fire the row's own function, saturation
carries the conclusion back" with no engine-equality reasoning at all.
Nine supporting lemmas were needed, all proved: `mem_nonEmpty_of`,
`allIris_complete`, `typesAllB_complete`, `sharesKeyValuesB_complete`,
`chainTargets_complete`, `chain_start_mem`, `typesAll_subject_mem`,
plus the two `exists_fuel_*`.

The one thing that does NOT transfer for free is the collection-walk
fuel. The nine list-valued rows read their premises through a
fuel-bounded walk. Soundness needs nothing extra (`listElems_sound`,
`listSeqs_sound` are unconditional), but completeness needs the
converse — that the walk FINDS everything — which is false at fuel 0
and true above the longest chain. `ListFuelAdequate g fuel` packages
exactly that, T4 takes it as a hypothesis, and
`exists_fuel_listElems` / `exists_fuel_listSeqs` prove such a fuel
always exists. That `listFuel g = g.length + 1` is always one is the
same term-universe counting obligation `closureFuelBound` carries, and
it is unproved. T1, T2, the fuel dichotomy and clash soundness do not
depend on it.

### Deliberate difference from the rdfs-core port: EXACT deduplication

`RDFS/Closure.lean` folds `Graph.add`, whose membership test is the
engine's coarse `Triple.eqb` (case-folded language tags,
`rdf:XMLLiteral` canonical-XML equality). This port folds `addOne`,
which tests propositional equality. Two consequences, both wanted: an
RDF graph is a SET OF TRIPLES under term identity (RDF 1.1 Concepts
§3), which is what exact dedup implements; and every theorem here is
stated in ONE membership relation (`t ∈ closure g fuel`) in both
directions, instead of the list-membership / `Graph.mem` asymmetry the
coarse test forces on the rdfs-core proofs. The cost is that two
triples differing only by language-tag case both survive a round, where
the F\* engine would keep one.

Two further deviations, both recorded in the module headers:

* **Every premise is read from the round's INPUT snapshot** (the F\*
  step threads its accumulator through the rules). Per round this emits
  less; at the fixpoint it emits the same set. Same deviation, same
  reasoning, as `RDFS/Closure.lean`.
* **cax-adc requires two distinct TERMS, not two distinct POSITIONS.**
  The F\* `two_distinct_members` fires the clash on a single
  `x rdf:type C` when C is listed twice; this port requires `ci ≠ cj`,
  which is strictly weaker and matches the row's intent.

### Assumption report — `assume val`s in the F\* originals

`grep -c "assume val"` over the six F\* OWL modules
(`OWL.Closure.fsti`, `OWL.RL.Spec.fst`, `OWL.RL.Refinement.fst`,
`OWL.Semantics.fst`, `OWL.Semantics.Soundness.fst`,
`OWL.Vocabulary.fst`) returns **0 for every one of them**. The OWL
layer is pure F\*: nothing to realise, nothing this port has to replace
or carry over. That confirms the port brief's expectation.

### Lemmas needed from other modules

None were added to `RDF/` or `RDFS/` — those are owned elsewhere and
this stage touched neither. The port reuses `RDF/Core.lean`'s
`Term.toSubject?`, `Subject.toTerm` and the derived `DecidableEq`
instances, and `RDF/Graph.lean`'s `Graph` abbreviation, and nothing
else from them. `RDF/Graph.lean`'s `Graph.mem` / `Graph.add` are
deliberately NOT used, per the exact-deduplication decision above; the
membership and insertion lemmas this port needs (`mem_of_memB`,
`memB_of_mem`, `mem_addOne_*`, `addAll_*`, `addAll_eq_of_length_eq`)
are proved locally against `addOne` in `RLTheorems.lean` §1.

If a later stage wants them shared, the natural home is an exact-set
sibling of `RDF/Graph.lean`'s `Graph.add` family — `Graph.addExact` and
its six lemmas. Not made here: this stage adds files only.

### Measured against the real corpus

`lake build l4owl-probe && ./.lake/build/bin/l4owl-probe third_party/testing/owl`

    engine self-check: cax-sco fires = true, unrelated triple absent = true
    profile-RL.rdf:                 91 test cases,   0 readable by the Lean parsers
    profile-EL.rdf:                 87 test cases,   0 readable
    profile-QL.rdf:                 65 test cases,   0 readable
    type-positive-entailment.rdf:  206 test cases,   0 readable
    type-inconsistency.rdf:        128 test cases,   0 readable
    type-consistency.rdf:          354 test cases,   0 readable
    RUNNABLE BY THE LEAN CLOSURE: 0 of 931

That was the state BEFORE `Syntax/RdfXml.lean` landed (same day). The
sentence "the Lean tree has no RDF/XML-to-triples mapping" is now
false and the probe below runs the corpus.

### Measured against the real corpus, second entry (2026-08-22, after RDF/XML)

`Harness/OwlProbe.lean` now parses every case's
`test:rdfXmlPremiseOntology` / `…ConclusionOntology` /
`…NonConclusionOntology` with `RdfXml.parseRdfXml` (base = the case
IRI, as the F\* runner does), merges `owl:imports` from the catalog's
wrapper nodes (port of `load_imports_into_premise`), runs `OWL.RL.step`
round by round under fuel 100 and a wall-clock cap read between driving
triples, and judges each (case, test type) unit the way
`bin/owl-runner/owl_runner.ml` does — that runner scores a case once per
test type, and `ProfileIdentificationTest` is tallied, never judged, in
both trees. The match rule for PositiveEntailmentTest is the F\*
runner's relaxed `triple_matches` (a conclusion blank node matches any
term; `Term.eqb` elsewhere), NOT `RDF/Isomorphism.lean`: entailment is
containment modulo blank nodes, and that rule is what the F\* scores
were produced with. Functional-syntax-only cases are `unsupported` and
stay in the denominator.

Branch `lean4/owl-corpus`. Verbatim, per-closure cap 20 000 ms:

    profile-RL.rdf PositiveEntailmentTest: 11 pass, 18 fail, 0 skip, 1 unsupported (out of 30)
    profile-RL.rdf NegativeEntailmentTest: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
    profile-RL.rdf ConsistencyTest: 75 pass, 0 fail, 0 skip, 1 unsupported (out of 76)
    profile-RL.rdf InconsistencyTest: 10 pass, 1 fail, 0 skip, 3 unsupported (out of 14)
    profile-RL.rdf: 102 pass, 19 fail, 0 skip, 5 unsupported (out of 126)
    HARNESS-DIAG-OWL profile-RL.rdf: cases=91 units=126 triples_parsed=1227 closure_rounds=428 clashes=10 cap_hits=0 parse_failures=0 wall_ms=82
    profile-EL.rdf: 95 pass, 21 fail, 1 skip, 4 unsupported (out of 121)
    HARNESS-DIAG-OWL profile-EL.rdf: cases=87 units=121 triples_parsed=1098 closure_rounds=409 clashes=4 cap_hits=0 parse_failures=0 wall_ms=70
    profile-QL.rdf: 76 pass, 11 fail, 0 skip, 0 unsupported (out of 87)
    HARNESS-DIAG-OWL profile-QL.rdf: cases=65 units=87 triples_parsed=872 closure_rounds=303 clashes=5 cap_hits=0 parse_failures=0 wall_ms=57
    type-positive-entailment.rdf PositiveEntailmentTest: 93 pass, 110 fail, 0 skip, 3 unsupported (out of 206)
    type-positive-entailment.rdf ConsistencyTest: 198 pass, 5 fail, 0 skip, 3 unsupported (out of 206)
    type-positive-entailment.rdf: 291 pass, 115 fail, 0 skip, 6 unsupported (out of 412)
    HARNESS-DIAG-OWL type-positive-entailment.rdf: cases=206 units=412 triples_parsed=28902 closure_rounds=1544 clashes=0 cap_hits=10 parse_failures=0 wall_ms=326261
    type-inconsistency.rdf InconsistencyTest: 29 pass, 84 fail, 1 skip, 14 unsupported (out of 128)
    type-inconsistency.rdf: 29 pass, 84 fail, 1 skip, 14 unsupported (out of 128)
    HARNESS-DIAG-OWL type-inconsistency.rdf: cases=128 units=128 triples_parsed=5258 closure_rounds=425 clashes=29 cap_hits=0 parse_failures=0 wall_ms=1570
    type-consistency.rdf PositiveEntailmentTest: 93 pass, 110 fail, 0 skip, 3 unsupported (out of 206)
    type-consistency.rdf NegativeEntailmentTest: 23 pass, 0 fail, 0 skip, 0 unsupported (out of 23)
    type-consistency.rdf ConsistencyTest: 337 pass, 8 fail, 0 skip, 9 unsupported (out of 354)
    type-consistency.rdf: 453 pass, 118 fail, 0 skip, 12 unsupported (out of 583)
    HARNESS-DIAG-OWL type-consistency.rdf: cases=354 units=583 triples_parsed=41248 closure_rounds=2111 clashes=0 cap_hits=12 parse_failures=1 wall_ms=396557

Six-catalog sum: 1046 pass, 368 fail, 2 skip, 41 unsupported (out of
1457 units over 931 cases); 78 605 triples parsed, 5 220 closure
rounds, 48 clashes, 22 closure cap hits, 1 parse failure. The
denominators agree with the F\* runner's per-type lines where it
publishes them (profile-RL PE 30; profile-QL 20+3+58+6 = 87;
profile-EL 29+6+72+14 = 121 with its one functional-syntax skip
outside the F\* denominator; type-inconsistency 128 with one
RDF-BASED-only skip). The type catalogs overlap each other and the
profile catalogs, so the sum is a sum of units, not of distinct tests.

**Every FAIL is named and falls into one of four causes.**

* `cap:` — 16 units (10 + 12 closures hit the 20 s cap; a capped
  closure still passes a PositiveEntailmentTest when the conclusion is
  already present). WebOnt-miscellaneous-001/002/011 (2 900–3 000
  triple premises) do not finish ONE round in 20 s: the specification
  evaluator's round is quadratic in the graph. WebOnt-description-
  logic-204/206/661/664 hit the cap after 3–4 rounds. Never a pass.
* `parser:` — 1 unit. `FS2RDF-literals-ar` (type-consistency) puts an
  `rdf:XMLLiteral` value as ELEMENT content under `rdf:datatype`; RDF/XML
  §7.2.16 allows only text there (XML content needs
  `rdf:parseType="Literal"`). `Parser.RDFXML.fst` accepts the shape by a
  non-spec extension this port chose not to copy (decision 4 of the
  RDF/XML stage above). Not an `RdfXml.lean` bug; left as a FAIL.
* `closure-gap:` on RL-profile catalogs — every one is a row this port
  scoped out, by name: the F\* `[ext]` differentFrom-synthesis family
  (`fp_diff_to_diff`: owl2-rl-rules-fp/ifp-differentFrom;
  `pdw_to_differentFrom`: New-Feature-DisjointObjectProperties-001/002,
  DisjointDataProperties-002; `cax_dw_to_differentFrom`:
  WebOnt-disjointWith-001; differentFrom symmetry: WebOnt-differentFrom-
  001); the comprehension-witness family (`svf2_existential_witness`,
  `minc1_bridge`, `cls_svf_thing_*`: bnode2somevaluesfrom,
  somevaluesfrom2bnode, WebOnt-someValuesFrom-003, New-Feature-
  ObjectQCR-002, WebOnt-I5.26-010, WebOnt-I5.5-005); `cls_hasself1/2`
  (New-Feature-SelfRestriction-001/002) and the reflexive-property
  extension (New-Feature-ReflexiveProperty-001); the chain bridge
  (chain2trans1); disjointWith → complementOf (DisjointClasses-001/003);
  annotation propagation across equivalentClass
  (`owl_rule_named_equivClass_to_sameAs_mode`, WebOnt-I4.6-005-Direct);
  the `owl_rl_closure_with_reflexivity` wrapper that types every subject
  `owl:Thing` (New-Feature-Keys-001 needs `Peter rdf:type owl:Thing`
  before prp-key fires; WebOnt-Thing-003 needs an owl:Thing instance
  for cls-nothing2); Table 7 / datatype map (dt-diff: New-Feature-Keys-
  002/006; xsd hierarchy and `rdfs:Datatype` axioms: WebOnt-I5.8-006/
  008/009/011; bottom/top property axioms: New-Feature-Bottom*Property-
  001); and the DL-only inconsistencies (WebOnt-Restriction-001/002).
* `closure-gap:` on the type catalogs — dominated by OWL DL
  entailments the F\* runner reaches only under `--regime dl` (RL
  closure + `Tableau` refuter + witness rules): 61 of the 84
  type-inconsistency fails are `WebOnt-description-logic-*`; the 110
  type-positive-entailment fails are the WebOnt-Class / cardinality /
  unionOf / oneOf / equivalentClass / FunctionalProperty families plus
  the nine `rdfbased-sem-prop-*-type` cases (built-in annotation
  properties typed `owl:AnnotationProperty` — an `[axm]` table) and the
  `rdfbased-sem-restrict-*` Table 8 rows scm-svf1/2, scm-avf1/2, scm-hv
  (listed above as not ported). The eq-diff2/eq-diff3/prp-adp rows
  "omitted for size only" cost `rdfbased-sem-ndis-alldifferent-fw`,
  `…-fw-distinctmembers`, `…-alldisjointproperties-fw`,
  WebOnt-AllDifferent-001 and WebOnt-distinctMembers-001.

Sabotage (done, then restored): with `caxScoFor` removed from
`conclusionsList`, profile-RL drops from 102 pass to 98 pass — WebOnt-
imports-011 [PE] and WebOnt-description-logic-101/103/104
[Inconsistency] flip to FAIL, and the engine self-check line prints
`cax-sco fires = false`. (The probe imports `RLClosure` rather than
`RLTheorems` so that this check can even build: with `RLTheorems`
imported, the T4 completeness proof refuses the sabotaged list — a
second, stronger gate.)

The F\* `owl_runner` numbers, with the manifest and regime each is over
(`docs/test-results/latest.json`): `owl_rl_positive_entailment` 30
pass, 0 fail (out of 30) — profile-RL.rdf, PositiveEntailmentTest line
only, RL regime; `owl2_profile_ql` 87 pass, 0 fail (out of 87) —
profile-QL.rdf, four types, RL regime; `owl2_profile_el` 119 pass, 1
fail (out of 120) — profile-EL.rdf, four types, RL regime;
`owl2_dl_inconsistency` 126 pass, 1 fail (out of 127) —
type-inconsistency.rdf, DL regime; `owl_syntax_dl_species` 319 pass,
2 fail, 2 skip (out of 323) — syntax-dl.rdf, `--species` mode (not a
closure run; not attempted here). No F\* line is published for
type-positive-entailment.rdf or type-consistency.rdf.

The 98 `#guard`s in `RLTests.lean` are NOT a conformance score and are
not offered as one: they are hand-written fixtures, and iron rule #6 is
met only when a Lean runner reads the W3C files. Each family pairs a
positive check with a negative one, per `skills/measuring-inference` —
a closure test that only asserts presence passes just as happily when
the rule never fired.

## Stage: the W3C harness runs the sparql11 query suites (2026-08-22)

`lake exe l4w3c ../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`
follows `mf:include` and scores `QueryEvaluationTest`,
`CSVResultFormatTest`, `PositiveSyntaxTest11` and
`NegativeSyntaxTest11` with the Lean parser and evaluator. Full
status, verbatim score lines, the sabotage record and the failure
table: `docs/designissues/2026-08-22-lean4-w3c-harness.md`,
"Status 2026-08-22 (later)".

### Module correspondence (append)

| F\* | Lean | Notes |
|---|---|---|
| `SPARQL11.Algebra.rewrite_query_bnodes_pattern` (+ `_term`, `_subject`, `_tp`) | `SPARQL/Query.lean` `QueryPattern.rewriteBnodes`, `Query.rewriteBnodes`, `rewriteBnodeTerm`, `rewriteBnodeSubject`, `rewriteBnodeTriple` | applied at the same site: the first stage of `evalSelect` / `evalAsk` / `evalConstruct` |
| `is_synthetic_bnode_var`, `strip_synthetic_bnode_vars` | `isSyntheticBnodeVar`, `stripSyntheticBnodeVars` | at the `SELECT *` projection, before DISTINCT, as in the F\* |
| `substitute_pattern`, `eval_exists` | `SPARQL/Exists.lean` `GraphPattern.substitute`, `evalExists`, `existsHookFor` | over the LOWERED pattern; closures re-based on μ (spec-faithful substitution into expressions, where the F\* leaves `e` verbatim) |
| `w3c_runner.ml` `select_results_equal_strict` / `results_match_with` / `term_equal_csv_lenient` / the `rs:ResultSet` decoder | `Harness/Compare.lean` | harness, not library |
| `w3c_runner.ml` `run_query_eval_test`, syntax-test arms | `Harness/Run.lean` `runQueryEvaluation`, `runSyntaxTest` | harness |
| `w3c_runner.ml` `mf:include` walk, `qt:serviceData`, `sd:entailmentRegime` | `Harness/Manifest.lean` | harness |

### Measured

`TOTAL: 309 pass, 47 fail, 0 skip, 275 unsupported (out of 631)` —
the F\* tree's bar is `631 pass, 0 fail, 0 skip, 0 unsupported (out
of 631)`. All 47 failures are evaluator findings, listed by cause in
the design doc; none was fixed in this stage. The six RDF suites
still print `TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported (out of
1078)`.

### Translation decisions (append)

- The `evalSelect` doc comment used to call the blank-node rewrite "a
  parser-level concern" and omit it. That was wrong: the F\* applies
  it inside `eval_select_query`, and without it a WHERE-clause `[]`
  or `_:a` matched only a data blank node carrying the same label.
  Ported at the same site. The rewrite does not enter embedded
  expressions (an EXISTS body keeps its blank nodes), SERVICE bodies
  or VALUES rows — the F\* arms are the same.
- EXISTS substitution works on the lowered algebra because the parser
  stores a `GraphPattern` inside `Expr.existsPat`. Filter / bind /
  left-join closures are evaluated on `μ ⊕ row` (μ first), which is
  what textual substitution of `μ(v)` for `v` amounts to. Two limits
  are stated in the module header: one active graph per hook (an
  EXISTS inside `GRAPH ?g` sees the top-level graph) and no hook for
  an EXISTS nested inside an EXISTS body (it was lowered with
  `emptyEnv`). Both cost one sparql11 test each.
- Comparison strictness: values compare with `Term.eqb` (brief rule),
  NOT the F\* runner's `numeric_literal_equal` fallback. Four tests
  differ only there (`2E-1` vs `2.0E-1` and kin) and are reported as
  failures with that cause named, rather than hidden by leniency.
- `NOW()` is the fixed `fixedNow` string; `EvalEnv.ext` stays empty;
  `qt:serviceData` graphs go into `EvalEnv.services`.

### Assumption report (append)

No new `assume`-shaped anything: the harness reads files in `IO` and
everything else is total. New `#guard`s in `Harness/HarnessTests.lean`
pin the bijection rules (same expected label → same actual label, two
expected labels may not share one actual label, ORDER BY pins by
position), the CSV leniency, the budget give-up, the `rs:ResultSet`
decoder with `rs:index`, `mf:include`, `sd:entailmentRegime` in both
shapes and `qt:serviceData`. Sabotaging `compareSelectRows` to
always-true fails the build at those guards.

### OWL tableau: the ∃-witness rule (2026-08-22, second rung)

`exWitness` added to `OWL/Tableau.lean`'s clash calculus with its
freshness side condition (`x ∉ indsOf A`), and `refuted_sound`
extended. The predicted hard part — "fresh individuals need model
extension" — dissolved: assignments are TOTAL functions `Ind → δ`, so
soundness only bends the assignment at the fresh name toward the
semantic witness that `∃r.C` guarantees, and `satisfies_agree` (new)
shows the rest of the ABox cannot see the change because satisfaction
reads the assignment only at an assertion's named individuals.
`derives_inds` (new) proves the forward rules invent no names, which
turns ABox-freshness into the `x ≠ a` the edge case needs. Checked at
build time: `∃r.⊥` and the textbook `(∃r.C) ⊓ (∀r.¬C)` refutations.
Axiom base unchanged.

### OWL tableau: the role box (2026-08-22, third rung)

`RoleAxioms` (subrole pairs + transitive roles) joins `Tableau.lean`;
`Derives` and `Refuted` take it as a parameter, and satisfaction-side
`RespectsRBox` states what a model owes it. Three new forward rules —
`subRoleE`, `transE`, and the SHIQ ∀⁺-push `allTransE` (a value
restriction on a transitive role travels across each edge of that
role) — each one line of soundness given `RespectsRBox`. The old
calculus embeds at `RoleAxioms.empty` (`respects_empty` discharges the
side condition). Checked at build time: a transitive-chain clash, a
subrole clash, and the SHIQ showpiece `∃r.(∃r.C) ⊓ ∀r.¬C` with `r`
transitive — two fresh witnesses deep, the ∀⁺-push carrying `¬C` to
the second witness. Axiom base unchanged. Elaboration note: `by
decide` membership proofs inside certificate terms postpone against
metavariable-laden goals ("Expected type must not contain
metavariables") — use explicit `.head _`/`.tail _` `Mem` chains in
examples, keeping `decide` only for freshness side conditions.

## Stage: EXISTS gets its proper shape — `QueryPattern` in the AST, active graph in conditions (2026-08-22)

Branch `lean4/sparql-exists`. Fixes the two sparql11 `exists` cases
the harness named (`Exists within graph pattern`, `Nested positive
exists`). Design record, with the option not taken and why:
`SPARQL/Exists.lean` header.

### What changed

- `Expr.existsPat` / `Expr.notExistsPat` carry a `QueryPattern` (the
  F\* `E_Exists : group_graph_pattern -> expr`), no longer a lowered
  `GraphPattern`. `Expr`, `QueryPattern`, `Query`, `SelectItem`,
  `SelectClause`, `QueryForm`, `OrderCondition`, `SolutionModifier`,
  `GroupCondition` are one mutual inductive in `Expr.lean`
  (`DatasetClause` sits just above it); the accessors, `mkQuery`,
  lowering and evaluation stay in `Query.lean`.
- `GraphPattern.filter` / `GraphPattern.leftJoin` conditions are
  `Graph → Binding → Bool`: the algebra hands the condition the ACTIVE
  graph (F\* `filter_solutions_with_graph … gs.gs_graph`,
  `left_join_with_graph`). `bind` is unchanged (F\* `fx_bind_rows` does
  no existential substitution).
- `QueryPattern.lowerWith` and the new `substituteExistentials` (port
  of the F\* `substitute_existentials`, arm for arm, no catch-all) are
  one STRUCTURAL mutual block: an EXISTS body is lowered under the row
  (`lowerWith env μ body` is `substitute(body, μ)`) and evaluated
  against the active graph and `EvalEnv.dataset`. No fuel, no hook, no
  `partial`. `EvalEnv.existsHook` is gone; `EvalEnv.dataset : Option
  Dataset` (last field, default `none`) is installed by `evalSelect` /
  `evalAsk` / `evalConstruct` from the query's dataset after FROM /
  FROM NAMED. The harness no longer builds a hook.
- `Query.toSse` prints EXISTS bodies through `sseGgp` (full fidelity;
  the `_` placeholders and `sseGraphPattern` are gone). The parser's
  EXISTS arm keeps the operand as parsed.
## Stage: the §17 builtins the sparql11 harness named (2026-08-22)

What: the evaluator gaps the harness report listed — §17.5 XSD
constructor functions, the five hash builtins, TIMEZONE/TZ, the
fresh-value builtins BNODE()/UUID()/STRUUID()/RAND(), IRI() against
the query's BASE, SECONDS' lexical form, and the argument rules of
STRDT / IF / CONCAT / STRBEFORE / STRAFTER. Branch
`lean4/sparql-builtins`.

### Module correspondence (append)

| F\* | Lean | Notes |
|---|---|---|
| `E_Exists` / `E_NotExists : group_graph_pattern -> expr` | `Expr.existsPat` / `Expr.notExistsPat (p : QueryPattern)` | one mutual inductive with the query AST, `SPARQL/Expr.lean` |
| `substitute_existentials` (+ `_list`, `_opt`) | `SPARQL/Query.lean` `substituteExistentials`, `substituteExistentialsList`, `substituteExistentialsOpt` | structural, in the `lowerWith` mutual block |
| `eval_exists` | `SPARQL/Exists.lean` `evalExists`; the substitution arm is `rfl`-equal to it (`substituteExistentials_existsPat`) | `substitute_pattern` is `lowerWith env μ` |
| `filter_solutions_with_graph … g`, `left_join_with_graph … g` | `GraphPattern.filter` / `leftJoin` conditions take the active `Graph` | `SPARQL/Algebra.lean` |

### Measured

Before (claude/main 693dad6e0): `exists: 4 pass, 2 fail, 0 skip, 0
unsupported (out of 6)`; `TOTAL: 309 pass, 47 fail, 0 skip, 275
unsupported (out of 631)`.
After: `exists: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)`;
`TOTAL: 311 pass, 45 fail, 0 skip, 275 unsupported (out of 631)`. The
FAIL lists differ by exactly the two named lines removed; nothing new.
The six RDF suites: `TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported
(out of 1078)`, unchanged.

### Translation decisions (append)

- Expressions inside a substituted body are evaluated on `μ ⊕ row`
  (μ first) — the previous stage's spec-literal reading of §18.6
  `substitute`, now applied uniformly by `lowerWith` (LATERAL bodies
  included; Jena substitutes into expressions there too). The F\*
  `substitute_pattern` / `lateral_substitute` leave embedded
  expressions verbatim; the two agree on every W3C case.
- A sub-SELECT inside an EXISTS body is lowered with the
  projection-masked row (`lateralVisibleMu`), as LATERAL does; the F\*
  `substitute_pattern` leaves `GP_SubSelect` verbatim.
- `EvalEnv.dataset` is the §18.6 `D`, passed the way `services`
  already is. `emptyEnv` therefore has no dataset and an EXISTS under
  it is the expression-layer error (`E_Exists _ -> ER_Error`).
- F\* behaviours ported as they are, each questionable against §18.6
  ("EXISTS may appear wherever an expression may"): `BIND(EXISTS{…}
  AS ?v)` errors (`fx_bind_rows`, `SPARQL11.Algebra.fst:4800`), and
  EXISTS in SELECT expressions / ORDER BY / HAVING / GROUP BY errors
  (`eval_select_query` never substitutes existentials).

### Assumption report (append)

Nothing new: no `sorry`, `axiom`, `native_decide`, `partial`, `opaque`
or `@[extern]`. `#print axioms QueryPattern.lowerWith` and `evalSelect`
still show `[propext, Classical.choice, Quot.sound]`. New `#guard`s in
`QueryTests.lean` pin both fixed shapes on inline graphs (GRAPH <iri>,
GRAPH ?g, nested EXISTS, nested NOT EXISTS, EXISTS under OPTIONAL, and
the no-dataset error). Sabotage: lowering the nested body with
`emptyEnv` fails `Nested positive exists` and the nested-EXISTS guard;
restored.
| `assume val hash_md5` | `Crypto/MD5.lean` `md5`, `md5Hex` | pure Lean, RFC 1321 vectors as `#guard`s; crypto-policy tier 1 (public data) |
| `assume val hash_sha1` | `Crypto/SHA1.lean` `sha1`, `sha1Hex` | pure Lean, FIPS 180-4 vectors; reuses `pad256` |
| `assume val hash_sha256/384/512` | `Crypto.hashHex` (existing) | the hash-agile dispatcher, as the SHA2 module header requires |
| `eval_xsd_cast` | `SPARQL/Expr.lean` `evalXsdCast` + `castInteger` … `castString` | see the deviation below |
| `dt_timezone`, `dt_tz`, `strip_leading_zeros_num` | `dtTimezone`, `dtTz`, `stripLeadingZerosNum` | arm for arm |
| `fx_key_row`, `fx_key_occ`, `fx_ctx_put`, `fx_ctx_get` | `SPARQL/Algebra.lean` `fxKeyRow`, `fxKeyOcc`, `Binding.withFreshnessCtx`, `Binding.freshnessCtx` | reserved keys with a U+0001 prefix, as the F\* |
| `fx_bind_rows` | `Algebra.lean` `bindRowsFresh` (the `GraphPattern.bind` arm) | row index + bound variable as call-site tag |
| `eval_select_item` / `eval_select_items_row` row+position context | `Query.lean` `evalSelectItemsRowFrom`, `numberRows` | same two seeds |
| `fx_uuid_of_seed`, `fx_bnode_of_seed` | `fxUuidOfSeed`, `fxBnodeOfSeed` | bnode label has no `_:` prefix (Lean labels never do) |
| `q_base` / `eval_expr_with_base`'s `base` | `Query.base` (8th field) → `EvalEnv.base` | the parser records the prologue's BASE (else the document IRI it was given) |
| `w3c_runner.ml` `numeric_literal_equal` | `Harness/Compare.lean` `numericLiteralEqual`, `termEqualLenient` | harness, not library |

### Measured

`lake exe l4w3c …/sparql11/manifest-all.ttl`, before → after (same
tree, same fixtures):

- `aggregates: 42 pass, 5 fail (out of 47)` → `47 pass, 0 fail (out of 47)`
- `cast: 0 pass, 6 fail (out of 6)` → `6 pass, 0 fail (out of 6)`
- `csv-tsv-res: 5 pass, 1 fail (out of 6)` → `6 pass, 0 fail (out of 6)`
- `functions: 43 pass, 32 fail (out of 75)` → `69 pass, 6 fail (out of 75)`
- `service: 6 pass, 1 fail (out of 7)` → unchanged
- `TOTAL: 309 pass, 47 fail, 0 skip, 275 unsupported (out of 631)` →
  `TOTAL: 347 pass, 9 fail, 0 skip, 275 unsupported (out of 631)`

38 tests fixed, zero regressions (the FAIL lists were diffed by name).
The 9 remaining: 4 REPLACE and `UUID() pattern match`, `STRUUID()
pattern match`, `SERVICE test 5` need REGEX (a separate port in
flight); `Exists within graph pattern` and `Nested positive exists`
are the two EXISTS limits already recorded. The six RDF suites:
`1078 pass, 0 fail (out of 1078)` (313 + 70 + 87 + 356 + 166 + 86).

Sabotage: dropping one nibble from the SHA-256 builtin's output fails
`lake build` at `SPARQL/ExprTests.lean:436` (the `SHA256("foo")`
guard); with that one guard silenced, the harness reports `FAIL
SHA256()` and `FAIL SHA256() on Unicode data`. Restored; build green.

### Numeric lexical forms — decision per test

The harness now carries the F\* runner's one numeric leniency
(`numeric_literal_equal`: same numeric datatype, equal VALUE). It was
measured by running the four suites with the rule switched off; the
tests that pass ONLY through it, and why:

| Test | Expected file | Lean output | Why (b) tolerance |
|---|---|---|---|
| `MIN with GROUP BY` | `"2.0E-1"^^xsd:double` | `"2E-1"` | MIN returns the data term unchanged (spec); the data says `2E-1`, the expected file records a re-serialisation |
| `AVG DISTINCT with GROUP BY` | `"1050"^^xsd:double` | `"1.05E3"` | the expected form is not the XSD canonical double; the F\* prints `1.05E3` too |
| `SUM DISTINCT with GROUP BY` | `"2100"^^xsd:double` | `"2.1E3"` | same |
| `tsv03 - TSV Result Format` | `"1.0e6"` (lowercase e) | `"1.0E6"` | the data's own lexical form, lowercase in the TSV file |
| `xsd:float cast`, `xsd:double cast` | e.g. `-1.02E4`, `3.333E1`, `0E0`, `1.5E0`, `1.0` | the F\* lexical conventions (`-10.2E3`, `33.3300`, `0.0`, `1.5`, `1E0`) | one implementation's float printer; the F\* runner relies on tolerance for these rows too |
| `xsd:decimal cast` | `"0"^^xsd:decimal` for `0^^xsd:integer` | `"0.0"` | every other row matches exactly after canonicalisation (`33.33`, `0.0`, `1.0`, `13.0`) |

Every other test in those suites matches lexically. Option (a) —
porting the F\* formatting — was taken wherever the F\* evaluator
produces the expected form (SECONDS, the decimal canonicalisation,
`xsd:float` of a boolean/integer/integer-valued double, `xsd:string`
of an integer-valued number).

### Translation decisions (append)

- STRDT takes a simple / `xsd:string` literal only (§17.4.2.3); IF
  propagates a type error in its condition (§17.4.1.2); CONCAT,
  STRBEFORE, STRAFTER take STRING literals only (§17.4.3.1); the
  STRBEFORE/STRAFTER compatibility table has exactly three pairs. In
  each case the F\* evaluator is more permissive and the W3C expected
  file disagrees; the F\* runner does not see it because
  `bin/w3c-runner/w3c_runner.ml` `binding_row_matches_with` checks
  only that every EXPECTED binding is present in the actual row, so
  an actual row with an extra binding where the expected row is
  unbound still "matches". The Lean harness compares domains
  (`domainsEqual`) and so cannot hide it. Recorded in the `Expr.lean`
  banner under "DEVIATIONS FROM THE F\* SOURCE" with F\* line
  references.
- XSD casts: a cast FROM A STRING requires the lexical form to be in
  the target's lexical space (`xsd:integer("1.5")`,
  `xsd:boolean("0.0")`, `xsd:decimal("1E0")` are errors); a cast from
  a number converts the value. The F\* `eval_xsd_cast` accepts the
  string forms (`parse_to_scaled`/`parse_double_to_scaled` fallbacks),
  hidden by the same runner rule.
- RAND() is the F\* tree's fixed `0.5` — deterministic, not random;
  the banner says so.
- Fresh values: the freshness context is row index + call-site tag,
  exactly the F\* design; BIND numbers rows inside the algebra
  (`bindRowsFresh`), the SELECT projection numbers rows and items.
  No `EvalEnv` state, no counter — a query's result is a function of
  its inputs.

### Assumption report (append)

No `sorry`, `axiom`, `native_decide`, `partial`, `@[extern]` or
`opaque` added. No new theorems; the build log's axiom audit lines
still show only subsets of `[propext, Classical.choice, Quot.sound]`
(111 lines checked). The two hash modules are tier-1 pure Lean under
`skills/crypto-policy/SKILL.md` (public data, no secret) and carry
the RFC 1321 / FIPS 180-4 vectors plus block-boundary lengths (55,
56, 63, 64, 65 bytes) as `#guard`s.
## Stage: the regex engine — Brzozowski derivatives, XSD patterns, fn:matches / fn:replace (2026-08-22)

Port of the four pure F\* regex modules and the `regex_match` /
`regex_replace` block of `SPARQL11.Algebra.fst` to
`L4Factoidal/Regex/`. `grep -c "assume val"` on
`Regex.{Syntax,Derivative,Exec,XSDPattern}.fst` gives 0, 0, 0, 0 real
declarations (the two grep hits are the comments "no assume val"), so
there was nothing to realise: the whole engine is total code and
proofs, and it is ported as such. Codepoints are `Nat` as in the F\*
(never bytes; `String.toList.map Char.toNat` in, `Char.ofNatAux` out),
because the XPath layer needs two values above `0x10FFFF` as anchor
sentinels.

Public API for the SPARQL evaluator (`SPARQL/Expr.lean` is wired by its
owner; the names differ from the brief only where Lean forced it —
`matches` is a Lean keyword):

| Brief | Landed | Notes |
|---|---|---|
| `Regex.compile (pattern flags : String) : Except RegexError Regex` | `L4Factoidal.Regex.compile : String → String → Except RegexError Compiled` | flags `i s m x q`; err:FORX0001 / FORX0002 |
| `Regex.matches (r) (s) : Bool` | `L4Factoidal.Regex.isMatch : Compiled → String → Bool` | unanchored search; `^` / `$` are real anchors; `m` implemented |
| `Regex.replace (r) (s) (replacement) : Except RegexError String` | `L4Factoidal.Regex.replace : Compiled → String → String → Except RegexError String` | `$N`, `\$`, `\\`; err:FORX0003 / FORX0004 |
| `Regex.xsdPatternMatches (pattern s) : Option Bool` | `L4Factoidal.Regex.xsdPatternMatches : String → String → Option Bool` | whole-string; `none` outside the fragment |

### Module correspondence

| F\* | Lean | Notes |
|---|---|---|
| `Regex.Syntax.regex` (`R_Empty R_Eps R_Ranges R_Cat R_Alt R_Star R_And R_Not`) | `Regex/Syntax.lean` `Re` (`empty eps ranges cat alt star inter compl`) | `and` / `not` would shadow the Bool functions inside `namespace Re` |
| `size`, `in_ranges`, `complement_from`, `complement_ranges` | `Re.size`, `inRanges`, `complementFrom`, `complementRanges` | same constants (`size` still feeds `isEmpty`'s fuel) |
| `take_n`, `drop_n` | `List.take`, `List.drop` | core |
| `mem` / `cat_try` / `star_try` (one mutual well-founded recursion on `[‖w‖; size; k; tag]`) | `mem` (structural on `Re`), `catTry`, `starTry` (structural on the split index, sub-languages as function arguments), `memStar` (fuel = `‖w‖`) | same language, same split order `k = ‖w‖ .. 0`; `memStar_fuel` closes the fuel |
| `nullable` | `nullable` | |
| `r_universal`, `ranges_cmp`, `regex_cmp`, `regex_le` | `rUniversal`, `rangesCmp`, `reCmp` (`Ordering`), `reLe` | same tag numbering |
| `smart_alt`, `smart_and`, `smart_not`, `smart_cat`, `smart_star` | `smartAlt`, `smartAnd`, `smartNot`, `smartCat`, `smartStar` | |
| `Regex.Derivative.deriv`, `deriv_word`, `matches` | `Regex/Derivative.lean` `deriv`, `derivWord`, `accepts` | `matches` is a Lean keyword |
| `Regex.Exec.insert_regex`, `alt_flatten`, `and_flatten`, `has_universal`, `has_empty`, `rebuild_alt`, `rebuild_and`, `ealt`, `eand`, `nderiv` | `Regex/Exec.lean` same names in camelCase | |
| `run_word`, `matches`, `run_word_norm`, `matches_norm` | `runWord`, `accepts`, `runWordNorm`, `acceptsNorm` | |
| `any_char`, `dot_star`, `contains`, `search`, `anchored_prefix`, `find_from`, `find_match` | `anyChar`, `dotStar`, `contains`, `search`, `anchoredPrefix`, `findFrom`, `findMatch` | |
| `insert_sorted`, `collect_bounds`, `collect_range_bounds`, `class_reps`, `mem_state`, `succ_states`, `add_new`, `bfs_empty`, `is_empty`, `intersection_empty`, `subsumes` | same, camelCase | fuel `1000 * (size + 1)` as in the F\* |
| `Regex.XSDPattern.*` (constants, `single`, `dot_regex`, `hex_val`, `read_hex_n`, `char_escape`, `class_escape_ranges`, `parse_escape_atom`, `class_escape_item`, `parse_class_items`, `insert_range`, `sort_ranges`, `parse_class`, `repeat_exact`, `repeat_opt`, `read_digits_acc`, `read_uint`, `parse_brace`, `skip_lazy`, `parse_quant`, `is_atom_meta`, `parse_alt … parse_group_close`, `parse_cps`, `cps_of_string`, `parse_xsd_pattern`) | `Regex/XSDPattern.lean` same names in camelCase; `cpsOfString` lives in `Syntax.lean` | `parseClassItems` takes the input length as fuel where the F\* used `decreases (length input)` |
| `SPARQL11.Algebra.rx_flag_has`, `rx_is_ws`, `rx_strip_ws`, `rx_replace_anchors`, `rx_begin_sentinel`, `rx_end_sentinel`, `rx_nonsent`, `rx_gap_left`, `rx_gap_right`, `rx_literal_regex`, `rx_ci_extra`, `rx_ci_ranges`, `rx_fold_ci`, `rx_dotall`, `regex_match` | `Regex/XPath.lean` `flagHas`, `isWs`, `stripWs`, `replaceAnchors`, `beginSentinel`, `endSentinel`, `nonSent`, `gapLeft`, `gapRight`, `literalRegex`, `ciExtra`, `ciRanges`, `foldCi`, `dotAll`, `regexMatch` | `regexMatch` keeps the exact F\* behaviour (unparseable pattern → `false`, `m` ignored) |
| `rx_safe_char`, `rx_string_of_cps`, `rx_take` / `rx_drop` / `rx_slice`, `rx_leaf_ends_from`, `rx_leaf_ends`, `rx_list_max_opt`, `rx_longest_end` | `safeChar`, `stringOfCps` (in `Syntax.lean`), `List.take` / `List.drop` / `slice`, `leafEndsFrom`, `leafEnds`, `listMaxOpt`, `longestEnd` | |
| `rx_cre` (`RC_Leaf RC_Eps RC_Cat RC_Alt RC_Star RC_Group`), `rx_cre_size`, `rx_cre_fold_ci`, `rx_cre_dotall`, `rx_cre_repeat_exact`, `rx_cre_repeat_opt` | `CRe` (`leaf eps cat alt star group`), `CRe.size`, `CRe.foldCi`, `CRe.dotAll`, `CRe.repeatExact`, `CRe.repeatOpt` | |
| `rx_cparse_brace`, `rx_cparse_quant`, `rx_cparse_alt … rx_cparse_noncap`, `rx_parse_capturing` | `cparseBrace`, `cparseQuant`, `cparseAlt … cparseNoncap`, `parseCapturing` | groups numbered from 1, outer before nested, as in the F\* |
| `rx_cmatch`, `rx_pick_caps`, `rx_find_cap`, `rx_group_text`, `rx_expand_template`, `rx_template_has_group`, `rx_cmatch_fuel`, `rx_replace_loop`, `regex_replace`, `string_replace` | `cmatch` (outcomes as `COut` records, caps as `Cap`), `pickCaps`, `findCap`, `groupText`, `expandTemplate`, `templateHasGroup`, `cmatchFuel`, `replaceLoop`, `regexReplace` | same mechanism: the verified engine finds the leftmost-longest span, the capturing matcher only explains the span |
| — | `templateValid`, `validFlags`, `RegexError`, `Compiled`, `compile`, `isMatch`, `replace`, `xsdPatternMatches`, `markerClass`, `sigmaAllStar`, `isSentinelLeaf`, `absorbMarkers`, `wrapMultiline` | new: the API surface and the `m` flag |
| `tests/unit/regex_engine_unit.ml` (F\* unit suite) | `Regex/RegexTests.lean` §1 | every case ported as a `#guard` |

### Lemma status (every F\* `Lemma` of the four modules)

| F\* lemma | Lean theorem (`Regex/RegexTheorems.lean`) | Status |
|---|---|---|
| `nullable_correct` | `nullable_correct` | proved |
| `smart_alt_ok`, `smart_and_ok`, `smart_not_ok` | `smartAlt_ok`, `smartAnd_ok`, `smartNot_ok` | proved |
| `take_all`, `drop_all`, `drop_below` | `List.take_length`, `List.drop_length`, `List.drop_eq_nil_iff` | core lemmas, used inline |
| `cat_empty_left`, `cat_empty_right` | `catTry_empty_left`, `catTry_empty_right` | proved |
| `cat_eps_left`, `cat_eps_right_below`, `cat_eps_right` | `catTry_eps_left`, `catTry_eps_right_below`, `catTry_eps_right` | proved |
| `smart_cat_ok` | `smartCat_ok` | proved |
| `star_try_empty`, `star_empty_lang`, `star_try_eps`, `star_eps_lang` | `starTry_empty`, `memStar_empty`, `starTry_eps`, `memStar_eps` | proved (stated for every fuel) |
| `smart_star_ok` (non-star argument) | `smartStar_ok` | proved, same restriction; star idempotence stays deferred in both trees and is off the `nderiv` path |
| `ranges_cmp_eq`, `regex_cmp_eq` | `rangesCmp_eq`, `reCmp_eq` | proved |
| `take_zero`, `drop_zero`, `take_cons`, `drop_cons` | `List.take_zero`, `List.drop_zero`, `List.take_succ_cons`, `List.drop_succ_cons` | core lemmas |
| `cat_shift` + `cat_shift_gen` | `catTry_shift` (the generic form) | proved; one theorem serves `deriv` and `nderiv` |
| `star_shift` + `star_shift_gen` | `starTry_shift` | proved |
| `deriv_cat_w` + `nderiv_cat_w` | `deriv_cat_w` (generic in the derivative) | proved |
| `deriv_star_w` + `nderiv_star_w` | `deriv_star_w` | proved |
| `deriv_correct` | `deriv_correct` | proved, full AST |
| `deriv_word_correct`, `matches_correct` | `derivWord_correct`, `accepts_correct` | proved |
| `insert_regex_ok`, `alt_flatten_ok`, `rebuild_alt_ok`, `has_universal_ok`, `ealt_ok` | same names, camelCase | proved |
| `insert_regex_and_ok`, `and_flatten_ok`, `rebuild_and_ok`, `has_empty_ok`, `eand_ok` | same names, camelCase | proved |
| `nderiv_correct`, `run_word_norm_correct`, `matches_norm_correct`, `matches_norm_eq_proven` | `nderiv_correct`, `runWordNorm_correct`, `acceptsNorm_correct`, `acceptsNorm_eq_proven` | proved |
| — | `memStar_fuel`, `memStar_length`, `catTry_congr_right`, `starTry_congr_right`, `runWord_eq_derivWord`, `Exec.accepts_correct`, `search_correct`, `size_pos`, `mem_universal` | added (fuel and congruence plumbing the F\* does not need) |

Not proved, in either tree: the derivative-class-coverage lemma behind
`isEmpty` (the Owens–Reppy–Turon finiteness argument); `isEmpty` stays
sound-by-construction and guard-checked, with its fuel / closure
guarantee stated at its definition, as the F\* `is_empty` banner says.
Nothing about the capturing matcher, the XSD parser, or the XPath flag
rewrites is proved in either tree; the XPath layer's correctness
argument is the F\* one (the span is decided by the proven engine; the
capturing AST reuses the parser's leaf builders).

Axiom audit: all eleven `#print axioms` lines at the end of
`RegexTheorems.lean` show subsets of `[propext, Quot.sound]`.

### Translation decisions

- `mem` is structural. The F\* `mem` / `cat_try` / `star_try` are one
  well-founded mutual recursion; Lean gets the same language with
  `mem` structural on the regex, the enumerators structural on the
  split index with the sub-languages as function arguments, and star
  iteration on a fuel set to the word length. Cost: one extra lemma
  (`memStar_fuel`) and two congruence lemmas. Benefit: every proof
  unfolds by `simp`, and `#guard`s run the compiled code without
  well-founded-recursion unfolding (pitfall 7).
- `matches` → `accepts` / `acceptsNorm` / `isMatch`: `matches` is a
  Lean keyword.
- `fn:matches` / `fn:replace` live with the engine (`Regex/XPath.lean`),
  not in the SPARQL algebra module where the F\* keeps them (they were
  placed there when they retired two `assume val`s). `regexMatch` /
  `regexReplace` reproduce the F\* functions for side-by-side
  comparison; `compile` / `isMatch` / `replace` add the error channel
  the evaluator needs.
- The `m` flag is implemented (the F\* accepts it and treats `^` / `$`
  as string anchors, which fails W3C `sparql10/regex`
  `regex-start-end-multiline`): the input is wrapped with a sentinel
  pair around every line, non-anchor leaves may absorb sentinel runs
  (`absorbMarkers`), and the search gaps accept any codepoint.
  Guarded: `^b$` + `m` on `"a\nb\nc"` is true, without `m` false;
  `a.*c` + `sm` crosses lines; `a.c` + `m` alone does not match `"a\nc"`.
- Error channel, all in the direction of XPath F&O: unknown flag
  (FORX0001), unparseable pattern (FORX0002), pattern matching the
  empty string in `replace` (FORX0003 — the F\* copies one codepoint
  through), ill-formed template `\x` / `$x` (FORX0004 — the F\* expands
  `\c` to `c`).
- Non-ASCII case folding under `i` is not applied, as in the F\*;
  `\w` is `[A-Za-z0-9_]`, as in the F\*; `$12` reads as `$1` then `2`,
  as in the F\*.

### Guards

`RegexTests.lean`: 183 `#guard`s. §1 is the F\* unit suite
`tests/unit/regex_engine_unit.ml` case for case (engine, emptiness,
the `(a?)^25 a^25` non-blow-up, astral codepoints, the XSD parser on
the OWL / CSVW / SHACL / ShEx fixture patterns, the clean-`none`
cases). §2 pins the exact W3C inputs: `sparql11/functions`
`replace01` (all eight `data3.ttl` strings), `replace02`, `replace03`
(`(ab)|(a)` → `[1=ab][2=]cd`), `replace-case-insensitive`;
`sparql11/service/service05` (`data05.ttl` subjects); `uuid01` /
`struuid01`; and the full `sparql10/regex` manifest — `regex-query-001
..004` on `regex-data-01.ttl` and the 17 quantifier / dot / flag /
class / anchor tests on `regex-data-quantifiers.ttl`, each as a filter
over the data strings equal to the `.srx` rows. Not a conformance
score: the W3C files are not read by this stage.

Sabotage record (2026-08-22): replacing `nderiv`'s star case by
`nderiv c a` fails the build at 28 guards (`a*`, `(ab)*`, the
`(a?)^25 a^25` pair, the CSVW `^-?P.*$` forms, `[0-9]+`, `ab*c`,
`ab+c`, `ab{1,}c` …) and at `nderiv_correct` (the `rw [smartCat_ok]`
step); replacing `deriv`'s star case by `deriv c a` fails
`deriv_correct` (the star case's `rfl`) and the
`Derivative.accepts (star …) == acceptsNorm …` guard. Both restored
with `git checkout`, build green again.

### Assumption report (append)

No `sorry`, no `axiom`, no `native_decide`, no `partial`, no
`@[extern]`. The F\* side had no `assume val` here either.

### Findings against the F\* (not fixed here)

- `SPARQL11.Algebra.fst:1364–1367` (`regex_match`): the `m` flag is
  accepted but not modelled, so `^b$` with `m` on `"a\nb\nc"` is
  `false`; W3C `sparql10/regex/regex-start-end-multiline.srx` expects
  that row. `bin/darwin-arm64/w3c_runner --list` shows only the 34
  SPARQL 1.1 suites, so the F\* score on the `sparql10/regex` manifest
  is not measured by the committed runner.
- `SPARQL11.Algebra.fst:1575–1577` (`regex_replace`): `^` / `$` parse
  to eps in a replace pattern (documented there as a known limitation);
  kept as-is in `replaceRe` so `replace` agrees with the F\*.

## Stage: SPARQL 1.1 Update (branch `lean4/sparql-update`, 2026-08-22)

Files: `L4Factoidal/SPARQL/Update.lean` (AST + §3 semantics),
`SPARQL/UpdateParser.lean` (grammar [29]–[52]), `SPARQL/UpdateTests.lean`
(84 guards), `SPARQL/UpdateTheorems.lean` (nine theorems),
`Harness/Manifest.lean` (the `ut:` vocabulary), `Harness/Run.lean`
(`UpdateEvaluationTest`, `PositiveUpdateSyntaxTest11`,
`NegativeUpdateSyntaxTest11`).

### Correspondence

| F\* | Lean | Notes |
|---|---|---|
| `graph_ref` (`GR_Default GR_Named GR_All GR_Graph`) | `GraphRef` | derives `DecidableEq` (the F\* `graph_ref_eq`) |
| `update_op` (`U_Load` … `U_Modify`) | `UpdateOp` | same eleven constructors, same payloads |
| `sparql_update` | `Update` | |
| `count_named_triples`, `dataset_triple_count` (the fresh-label salt) | `Dataset.maxBnodeLabelLength`, `requestPrefix` | freshness by LENGTH, not by triple count — see "Decisions" |
| `ps_to_subject_concrete`, `pt_to_iri_concrete`, `pt_to_term_concrete`, `tp_to_triple_concrete`, `bgp_to_triples_concrete`, `collect_quads` | `groundSubject`, `groundPredicate`, `groundObject`, `groundTriple`, `collectQuads` | |
| `upsert_named_graph`, `insert_quad`, `insert_quads`, `remove_from_named_graph`, `delete_quad`, `delete_quads` | `replaceNamed`, `Dataset.insertQuad`, `Dataset.insertQuads`, `Dataset.deleteQuad`, `Dataset.deleteQuads`, `Graph.remove` | |
| `rename_quad_bnodes`, `apply_insert_data` | `Quad.renameBnodes`, `freshDataBnode`, `applyInsertData` | |
| `triple_has_bnode`, `filter_no_bnode_quads`, `apply_delete_data` | `Triple.hasBnode`, `applyDeleteData` | |
| `instantiate_tp`, `instantiate_bgp`, `instantiate_ggp_quads`, `bound_subject_of_pattern_freshen`, `bound_object_of_pattern_freshen`, `instantiate_tp_freshen`, `instantiate_bgp_freshen`, `instantiate_ggp_quads_freshen`, `fresh_bnode_for_op` | `instSubject`, `instObject`, `instTriple`, `instQuads`, `freshTemplateBnode` | ONE instantiator with a `fresh : String → BNodeId` argument: `id` for DELETE templates, `freshTemplateBnode pre opIx solIx` for INSERT templates |
| `instantiate_ggp_all`, `apply_delete_where` | `evalWhere`, `applyDeleteWhere` | |
| `using_default_iris`, `using_named_iris`, `union_named_graphs_by_iri`, `named_graphs_by_iri`, `build_where_dataset` | `whereDataset` | |
| `redirect_default_quad(s)`, `per_mapping_quads`, `per_mapping_insert_quads`, `insert_per_mapping_quads`, `apply_modify` | `redirectQuad`, `insertQuadsFor`, `applyModify` | |
| `find_named_graph_triples`, `has_named_graph`, `replace_named_graph_triples`, `empty_graph_named`, `drop_named_by_iri`, `empty_all_named`, `ensure_named_graph` | `Dataset.graphOf`, `Dataset.hasGraph`, `Dataset.setGraph`, `Dataset.dropGraph`, `Dataset.clearAllNamed`, `Dataset.ensureGraph` | |
| `read_graph_ref`, `graph_ref_exists`, `write_graph_ref` | `readRef`, `refExists`, `writeRef` | |
| `apply_create`, `apply_clear`, `apply_drop`, `apply_copy`, `apply_move`, `apply_add`, `graph_append` | `applyCreate`, `applyClear`, `applyDrop`, `applyCopy`, `applyMove`, `applyAdd` (with `Graph.union`) | return `Except UpdateError Dataset` — see "Decisions" |
| `apply_update_op`, `apply_update_ops_aux`, `apply_update_ops`, `apply_update` | `applyOp`, `applyOps`, `applyUpdateIn`, `applyUpdate` | |
| `is_implemented_op`, `update_is_implemented_only` | `Update.hasNonSilentLoad` | |
| `parse_iri_ref`, `parse_graph_ref_graph_only`, `parse_graph_ref_all`, `parse_graph_or_default`, `parse_silent` | `pIriRef`, `pGraphRef`, `pGraphRefAll`, `pGraphOrDefault`, `pSilent` | |
| `gp_has_var`, `bgp_has_any_var`, `gp_has_bnode`, `bgp_has_any_bnode`, `gp_has_nested_graph_under_graph`, `gp_has_graph_anywhere` | `patHasVar`, `bgpHasVar`, `patHasBnode`, `bgpHasBnode`, `patHasNestedGraph`, `patHasGraph` | |
| `parse_quad_block`, `parse_quad_data`, `parse_using_list`, `parse_single_update_op`, `parse_modify_after_with`, `parse_update_seq` | `pQuadBlock`, `pQuadData`, `pUsingList`, `pUpdateOp` (+ `pInsertTemplateOpt`, `pModifyRest`), `pModifyAfterWith`, `pUpdateSeq` | templates and WHERE clauses reuse `pTriplesBlock` / `pGroupGraphPattern` / `pGraphName` / `pPrologue` unchanged |
| `labeled_bnodes_in_data_op`, `bnode_labels_unique_across_data_ops` | `labeledBnodesInDataOp`, `bnodeLabelsUniqueAcrossDataOps` | §19.6 |
| `parse_sparql_update_with_base`, `parse_sparql_update_12_with_base`, `parse_sparql_update` | `parseSparqlUpdateWith`, `parseSparqlUpdate` | one entry point with a `version` argument |
| `w3c_runner.ml` `extract_data_and_graphdata` (~409–464), the `mf:result` bnode branch (~552–573) | `Harness/Manifest.lean` `dataAndGraphData`, `TestCase.updateResultData` / `updateResultGraphData` | |
| `w3c_runner.ml` the three update arms (2217–2312) | `Harness/Run.lean` `runUpdateEvaluation`, `runUpdateSyntaxTest`, `loadUpdateStore`, `dropEmptyNamed` | |

### Decisions

- **Error channel.** `applyUpdate : Dataset → Update → Except UpdateError
  Dataset`. The F\* `apply_update` is total and its Part 19e banner
  says "SILENT is advisory in our pure model — errors do not exist".
  SPARQL 1.1 Update §3.2.1–§3.2.5 and §3.1.5 say CREATE of an existing
  graph and CLEAR / DROP / COPY / MOVE / ADD naming a missing graph are
  errors unless SILENT; this port raises `graphExists` /
  `graphMissing` exactly there and `loadUnavailable` for a non-silent
  LOAD. `SILENT` makes each the identity (theorems
  `applyUpdate_clear_missing` / `_silent`, `applyUpdate_create_existing`).
  The W3C suites never exercise the non-SILENT error path, so both
  trees score the same 149; the difference is observable only on a
  request the suites do not contain.
- **Fresh blank nodes by construction.** `requestPrefix ds` is one
  character longer than the longest label in the store, so every label
  it prefixes is new. The F\* salts with the triple COUNT
  (`SPARQL11.Algebra.fst:8709`), which can repeat across requests
  (insert → delete something else → insert again lands on the same
  count and the same `_insdata_<n>_<label>`). The SCOPING is the
  F\*'s: one prefix per request for INSERT DATA (`freshDataBnode`,
  §19.6, W3C `insert-data-same-bnode`), one node per (operation,
  solution, label) for INSERT templates (`freshTemplateBnode`,
  §3.1.3.2, W3C `insert-where-same-bnode`), variable-bound nodes pass
  through (W3C `insert-05a`).
- **One template instantiator.** The F\* keeps two families
  (`instantiate_*` for DELETE, `*_freshen` for INSERT); here
  `instQuads` takes the freshening function as an argument.
- **Empty named graphs in the comparison.** `Harness/Run.lean` drops
  empty named-graph slots on both sides before
  `Dataset.isomorphicOutcome`. The F\* compares canonical N-Quads,
  which cannot represent an empty graph; the Lean isomorphism matches
  graph NAMES, so a slot left by `CLEAR GRAPH` / `CREATE GRAPH` would
  otherwise fail a test the F\* passes. Recorded in the `Run.lean`
  section banner.
- **`WITH <g> DELETE WHERE { P }`** parses as the F\* does: a `modify`
  whose DELETE template and WHERE clause are both `P`.

### Measured against the real corpus

`lake exe l4w3c ../../third_party/testing/w3c/sparql/sparql11/manifest-all.ttl`,
verbatim (update suites and total):

```
add: 8 pass, 0 fail, 0 skip, 0 unsupported (out of 8)
basic-update: 13 pass, 0 fail, 0 skip, 0 unsupported (out of 13)
clear: 4 pass, 0 fail, 0 skip, 0 unsupported (out of 4)
copy: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
delete-data: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
delete-insert: 17 pass, 0 fail, 0 skip, 0 unsupported (out of 17)
delete-where: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
delete: 19 pass, 0 fail, 0 skip, 0 unsupported (out of 19)
drop: 4 pass, 0 fail, 0 skip, 0 unsupported (out of 4)
move: 6 pass, 0 fail, 0 skip, 0 unsupported (out of 6)
syntax-update-1: 54 pass, 0 fail, 0 skip, 0 unsupported (out of 54)
syntax-update-2: 1 pass, 0 fail, 0 skip, 0 unsupported (out of 1)
update-silent: 13 pass, 0 fail, 0 skip, 0 unsupported (out of 13)
TOTAL: 505 pass, 0 fail, 0 skip, 126 unsupported (out of 631)
```

Baseline before this stage: `TOTAL: 356 pass, 0 fail, 0 skip, 275
unsupported (out of 631)`; the 149 entries that moved are exactly the
UpdateEvaluationTest (94), PositiveUpdateSyntaxTest11 (42) and
NegativeUpdateSyntaxTest11 (13) entries. No LOAD skip: the suites
contain no non-SILENT LOAD (the two `update-silent` LOAD tests are
SILENT and run). The F\* runner's line for the same 631 is 631 pass,
0 fail. The six RDF suites stay at 1078 pass, 0 fail, 0 skip, 0
unsupported (out of 1078).

### Guards and theorems

`UpdateTests.lean`: 84 `#guard`s — INSERT DATA (set semantics, GRAPH
blocks, same-label-one-node, request-fresh label), DELETE DATA (absent
triple and absent graph are no-ops), DELETE WHERE (default, `GRAPH ?g`,
`GRAPH <g>`), DELETE/INSERT (predicate rename, delete-before-insert,
unbound-variable and literal-subject templates dropped, WITH on INSERT
and DELETE, USING, USING NAMED, `GRAPH ?g` templates, fresh per
solution, fresh per operation, variable-bound node preserved, WHERE
blank node as variable), LOAD (SILENT identity, non-silent error,
`hasNonSilentLoad`), CLEAR / CREATE / DROP / COPY / MOVE / ADD with
their SILENT and error cases, the `;` sequence rules, prologue between
operations, BASE, and the twelve `syntax-update-bad-NN.ru` texts
verbatim plus §19.6.

`UpdateTheorems.lean`: `applyUpdate_nil`, `applyUpdate_insertData_empty`,
`applyUpdate_deleteData_empty`, `applyUpdate_insert_then_delete`
(round trip, exact list equality), `applyUpdate_clearAll`,
`applyUpdate_dropAll`, `applyUpdate_clear_missing`,
`applyUpdate_clear_missing_silent`, `applyUpdate_create_existing`,
`applyOps_cons`, with the helper lemmas `Graph.remove_of_not_mem` and
`Graph.remove_add_of_not_mem`. Every `#print axioms` line reads a
subset of `[propext, Classical.choice, Quot.sound]`.

Sabotage record (2026-08-22): see the design-doc Status entry of the
same date for the delete/insert-order swap.
## Stage: entailment regimes — simple, D, RDF, RDFS — on the real suites (2026-08-22)

Branch `lean4/entailment`. What landed: the full RDF 1.1 Semantics rule
set as a derivation relation and an executable closure
(`RDFS/FullClosure.lean`, `RDFS/FullClosureTheorems.lean`), the
datatype map and D-value model (`RDF/Datatypes.lean`), simple
entailment and the four regimes with D-inconsistency
(`RDF/Entailment.lean`, `RDF/EntailmentTheorems.lean`,
`RDF/EntailmentTests.lean`), and the harness arms for rdf-mt's
`PositiveEntailmentTest` / `NegativeEntailmentTest` and for the
sparql11 `entailment` suite's RDFS / RDF / D regimes
(`Harness/Manifest.lean`, `Harness/Run.lean`).

### Measured score lines, verbatim

`lake exe l4w3c` from the repository root, binary built at this stage:

```
rdf-mt: 39 pass, 0 fail, 0 skip, 0 unsupported (out of 39)
entailment: 40 pass, 0 fail, 0 skip, 30 unsupported (out of 70)
TOTAL: 396 pass, 0 fail, 0 skip, 235 unsupported (out of 631)   (sparql11/manifest-all.ttl)
TOTAL: 1078 pass, 0 fail, 0 skip, 0 unsupported (out of 1078)   (the six RDF suites)
```

F\* runner, same manifests (`docs/test-results/latest.json`): rdf-mt
38 pass, 0 fail, 1 unsupported (out of 39) — the unsupported one is
`rdfs-entailment-test001` (rdf:XMLLiteral well-formedness, which
`RDF.Entailment.RDFS.DatatypeClash.fst` declares out of scope; here the
XML parser decides it); sparql11 entailment 70 pass, 0 fail (out of
70), the F\* tree having the OWL-RL / OWL-Direct / RIF regimes this
port does not. The 30 `unsupported` here are exactly those entries:
18 `OWL-Direct` only (paper-sparqldl-Q2/Q3, parent3–10, simple1–8),
8 `OWL-Direct/OWL-RDF-Based` (lang, plainLit, paper-sparqldl-Q1/Q4,
sparqldl-10–13), 4 `RIF`. Each is named with its regime in the run
log; none is passed, none leaves the denominator. The sparql11
TOTAL moved from 356 to 396 pass by exactly those 40 entailment
entries; the query-type suites are unchanged.

### Module correspondence (append)

| F\* | Lean | Notes |
|---|---|---|
| `RDFS.Closure.fsti` rows rdfs1, rdfs4a, rdfs4b, rdfs8, rdfs13 (+ `rdfs_rule_container_membership`, `rdf_property_axiom_closure` = rdfD2), `rdfs_reflexivity_axioms` (the rdfs6 / rdfs10 approximation) | `RDFS/FullClosure.lean` `DerivesFull`, `rdfD2For`, `rdfs4aFor`, `rdfs4bFor`, `rdfs6For`, `rdfs8For`, `rdfs10For`, `rdfs12For`, `rdfs13For`, `fullClosure`, `rdfClosure` | rdfs6 / rdfs10 / rdfs12 are RULES here, not a post-hoc class/property harvest; rdfs1 is an axiom table over D |
| `RDF.Vocabulary.Axioms.fst` `rdf_axiomatic_triples`, `rdfs_axiom_*` (finite, `rdf:_1..rdf:_5`) | `rdfAxiomaticTriples`, `rdfsAxiomaticTriplesFixed`, `rdfsContainerAxioms`, `datatypeAxioms` | the `rdf:_n` slice is `rdf:_1` plus every `rdf:_n` the premise and conclusion mention (`containerMembershipIn`), not a fixed 1..5 |
| `RDF.Entailment.Simple.fst` `simple_entails`, `entails_with leq bnd` | `RDF/Entailment.lean` `SimpleEntails` (spec), `searchInstance` + `instanceCert` + `entailsWith` | witness-then-certificate, as `Isomorphism.lean`; `simpleEntails_sound` proved |
| `RDF.Entailment.Regime.fst` `dt_value_leq`, `bnd_rdf`, `entails_rdf`, `entails_rdfs` | `RDF/Datatypes.lean` `literalValueEq`, `literalIllFormed`; `Regime.literalEq`, `Regime.bindable`, `regimeEntails` | no xsd:float / xsd:double / rdf:JSON value model here (the rdf12 fixtures are not in scope of this stage) |
| `RDF.Entailment.RDFS.DatatypeClash.fst` `rdfs_d_inconsistent` | `hasIllFormedLiteral`, `hasRangeClash`, `Regime.inconsistent` | rule (b) walks `rdfs:subClassOf` from the range class and requires the literal's own datatype recognised; the F\* fires on any datatype mismatch |
| `bin/w3c-runner/w3c_runner.ml` `apply_entailment_regime`, `simple_entails_regime`, the `PositiveEntailmentTest` / `NegativeEntailmentTest` arms, the `run_query_eval_test` regime branch | `Harness/Run.lean` `runEntailmentTest`, `pickRegime`, `closeDataset`, `recognizedDatatypesOf` | regime list read as RDFS > RDF > D; OWL / RIF names refused by name |

### Theorems

`RDFS/FullClosureTheorems.lean`: `Derives.toFull` (every rdfs-core
derivation is a full-RDFS derivation — the theorem relating the two
rule sets), `DerivesFull.mono`, `DerivesFull.cut`, `rdfD2For_sound`,
`rdfs4aFor_sound`, `rdfs4bFor_sound`, `rdfs6For_sound`,
`rdfs8For_sound`, `rdfs10For_sound`, `rdfs12For_sound`,
`rdfs13For_sound`, `fullStepConclusions_sound`, `fullStep_sound`,
`fullClosureLoop_sound`, `fullClosureLoop_extensive`,
`fullClosure_extensive` (T1), `fullClosure_sound` (T2),
`rdfClosure_extensive`, `rdfClosure_sound`,
`fullClosure_saturated_or_underfueled`.
`RDF/EntailmentTheorems.lean`: `termMatch_strict_eq`,
`tripleMatch_strict_eq`, `instanceCert_strict_sound`,
`simpleEntails_sound`, `SimpleEntails.refl`.
Axiom audit (`#print axioms` in `EntailmentTests.lean`): propext,
Classical.choice, Quot.sound only.

**T4 completeness at saturation: CLOSED (2026-08-22, branch
`lean4/rdfs-complete`).** The entry below previously named it the open
obligation of this stage. It is now proved for the FULL rule set — all
sixteen `DerivesFull` constructors, the eight rows this stage added
(rdfD2, rdfs4a, rdfs4b, rdfs6, rdfs8, rdfs10, rdfs12, rdfs13) plus the
`axiomatic` constructor that carries rdfs1-as-axioms and the §8.2 /
§9.3 axiomatic triples. Theorems, in
`RDFS/FullClosureTheorems.lean`:

| Theorem | Statement |
|---|---|
| `fullComplete_of_saturated` | `fullStep c = c` and `∀ u ∈ ax, Graph.mem u c` and `∀ u ∈ g, Graph.mem u c` imply `DerivesFull ax g t → Graph.mem t c = true` |
| `fullClosure_complete_of_saturated` | `fullStep (fullClosure D cmps g) = fullClosure D cmps g` implies `DerivesFull (axiomaticTriples D cmps) g t → Graph.mem t (fullClosure D cmps g) = true` |
| `fullClosure_mono_of_saturated` | `g ⊆ g'` and `g'`'s closure saturated imply `t ∈ fullClosure D cmps g → Graph.mem t (fullClosure D cmps g') = true` |
| `graphMem_fullClosure_of_mem_closure` | the two closures compared: `t ∈ closure g fuel → Graph.mem t (fullClosure D cmps g) = true` under the same saturation hypothesis |

Support lemmas landed with them: `mem_fullStepConclusions_core` and
one `mem_fullStepConclusions_<row>` per new row (a row's conclusion
reaches the round's conclusion list), `graphMem_fullClosureLoop_of_graphMem`,
`graphMem_fullClosure_of_mem`, `graphMem_fullClosure_of_mem_axioms`.

Hypotheses, named rather than assumed:

- **saturation** (`fullStep c = c`) — the same hypothesis T4 of
  `ClosureTheorems.lean` carries; `fullClosure_saturated_or_underfueled`
  turns it into "the fuel was not exhausted".
- **`hax`** — NEW relative to the rdfs-core T4, and forced by the
  `axiomatic` constructor: a graph closed under the RULES still misses
  a derivation that quotes an axiom unless it was SEEDED with the
  axiom set. `fullClosure` seeds it, which is how
  `fullClosure_complete_of_saturated` discharges the hypothesis.
- **no list-fuel hypothesis** — unlike the OWL-RL collection rows,
  every one of the eight rows is single-premise and premise-local
  (one triple in, at most one conclusion out), so there is no bounded
  walk to fuel.

Axiom audit for the four theorems (`#print axioms` in `Tests.lean`):
propext, Classical.choice, Quot.sound only.

Still not proved: that `fullClosureFuelBound` is always enough — the
term-universe counting obligation `Closure.closureFuelBound` already
carries and this module inherits. T4 is stated against saturation, not
against a fuel constant, so nothing above depends on it. Also not
proved: any model-theoretic statement (D-interpretations are not
ported, so the regime comparisons `literalValueEq` carry guards, not
theorems).

### Translation decisions

- rdfD1 is not a row: it mints a blank node per literal. Its
  observable effects are covered by the instance search (a conclusion
  blank node may map to a literal, §5.2) and by rule (a) of
  D-inconsistency. Documented in the `FullClosure.lean` header.
- Generalised-RDF conclusions (literal subjects from rdfs3 / rdfs4b)
  are dropped, as the F\* rows drop them; the one place they carry
  meaning — a literal forced into a datatype class — is rule (b).
- The `rdf:_n` family is instantiated per entailment check from both
  graphs, with an argument in the header for why that is complete.
- Under `simple`, literal comparison is strict term identity
  (Concepts §3.3); under D / RDF / RDFS it is D-value equality, whose
  base is `Literal.eqb` (language tags case-folded) plus numeric value
  equality for recognised numeric datatypes. `xsd:int ⊂ xsd:integer ⊂
  xsd:decimal` is the only non-disjointness modelled.
- A test whose `mf:recognizedDatatypes` names a datatype outside
  `modelledDatatypes` is `unsupported`, naming it. None in rdf-mt does.
- The minimal D (`xsd:string`, `rdf:langString`) is added to every
  map; the sparql11 entailment suite names none, so it runs with the
  minimal map.

### Sabotage record (2026-08-22)

- rdfs9 removed from `Closure.stepConclusions`: rdf-mt STAYS at 39
  pass — no rdf-mt entry exercises rdfs9 (subClassOf on an instance);
  the sparql11 entailment suite drops to 37 pass, 3 fail (rdfs04,
  rdfs05, rdfs09 named), and `lake build` fails in
  `ClosureTheorems.lean` at `stepConclusions_sound` (line 378) and the
  rdfs9 case of the completeness proof. A guard for rdfs9 was added to
  `EntailmentTests.lean` so the library build also catches it.
- rdfs7 removed: rdf-mt drops to 37 pass, 2 fail
  (`rdfms-seq-representation-test003`,
  `rdfs-subPropertyOf-semantics-test001`). Restored; green again.

### Assumption report (append)

No `sorry`, no `axiom`, no `native_decide`, no `partial`, no
`@[extern]`. The F\* side: LOAD is the `U_Load _ _ _ -> ds` no-op
(`SPARQL11.Algebra.fst:8693`); this port makes the non-silent case an
explicit `UpdateError` instead of a silent success.

### Findings against the F\* (not fixed here)

- `SPARQL11.Algebra.fst:8438–8441` (Part 19e banner) with
  `apply_create` (8566), `apply_clear` (8575), `apply_drop` (8594),
  `apply_copy` (8611), `apply_move` (8627), `apply_add` (8655): the
  `silent` flag is bound and discarded (`let _ = silent in`), so
  `CREATE GRAPH <g>` on an existing graph and `CLEAR` / `DROP` /
  `COPY` / `MOVE` / `ADD` on a missing graph succeed without SILENT.
  SPARQL 1.1 Update §3.2.1–§3.2.5 and §3.1.5 make those errors. Not
  visible in the W3C suites (no non-SILENT error case).
- `SPARQL11.Algebra.fst:8707–8710` (`apply_update_ops`): the INSERT
  DATA label salt is `string_of_int (dataset_triple_count ds)`. Two
  requests run on stores with the same triple count produce the same
  `_insdata_<n>_<label>`, so `INSERT DATA { _:b … }` re-run after a
  delete that restores the count silently re-uses the earlier node
  instead of creating a fresh one.
- `SPARQL11.Algebra.fst:8693` (`apply_update_op`, `U_Load`): a
  non-silent LOAD is a silent no-op inside the algebra; only the
  runner's `update_is_implemented_only` pre-check (`w3c_runner.ml:2250`)
  keeps it from scoring. A caller of `apply_update` that skips the
  pre-check gets a success for a request §3.1.4 says must fail.
`@[extern]`. The F\* originals carry no `assume val` in these modules.

### Findings against the F\* (not fixed here)

- `RDF.Entailment.RDFS.DatatypeClash.fst:109-120`
  (`exists_range_literal_mismatch`): a clash is asserted whenever the
  literal's datatype differs from the range datatype, so
  `ex:p rdfs:range xsd:decimal . ex:s ex:p "25"^^xsd:integer .` with
  both recognised would be reported D-inconsistent, although 25 is in
  the value space of `xsd:decimal` (XSD 1.1 §3.4.13: integer is a
  subset of decimal). The same function also fires when the literal's
  own datatype is unrecognised (`"x"^^ex:dt` under a recognised range),
  where RDF 1.1 Semantics §7 gives the literal an unknown denotation.
  No rdf-mt fixture exercises either shape; `EntailmentTests.lean`
  guards the Lean behaviour.
- `RDFS.Closure.fsti` runs rdfs6 / rdfs10 as the class/property
  harvest `rdfs_reflexivity_axioms` (two extra closure passes) rather
  than as rows inside the step; with the §9.3 axioms seeded, the rows
  alone reach the same triples (`A subClassOf B` ⊢ `B subClassOf B`
  through `rdfs:subClassOf rdfs:range rdfs:Class` + rdfs3 + rdfs10),
  which is what `paper-sparqldl-Q1-rdfs`, `rdfs05`, `rdfs11` and
  `sparqldl-02` need. The F\* banner records that seeding its axiom
  table regressed an OWL consistency test (#236 interaction); this
  port has no OWL-RL closure on the RDFS path, so the seed is safe
  here and that interaction remains the F\* tree's.

## Stage: SPARQL 1.1 Protocol, Graph Store HTTP Protocol, Service Description (2026-08-22)

Branch `lean4/protocol`. The three protocol-shaped sparql11 test
types run in the Lean harness. No HTTP server in either tree: each
test is request/response decoding over the Markdown in the entry's
`rdfs:comment`, so the port is of the PURE F\* modules plus the
runner clauses that drive them.

### Module correspondence

| F\* | Lean | Notes |
|---|---|---|
| `SPARQL.Protocol.fst` Part 2 (`is_hex_digit`, `hex_value`, `ascii_lower_string`, `trim_ws`) | `SPARQL/Protocol.lean` `isHexDigit`, `hexValue`, `asciiLower`, `trimWs` | |
| Part 3 `url_decode_chars` / `url_decode` / `form_decode` | `pctUnits` + `utf8Assemble` + `percentDecodeChars`, `urlDecode`, `formDecode` | escapes decode to BYTES, then UTF-8 (see findings); `+` → space only under `formDecode` |
| — | `percentEncode`, `isUnreserved`, `hexDigitUpper`, `percentEncodeByte` | new: the inverse, for the round-trip theorem |
| Part 4 `split_once_on`, `split_all_on` | `splitOnce`, `splitAll` | `splitAll` is `String.splitOn` (same `""` → `[""]` behaviour) |
| Part 5 `parse_kv_pair`, `parse_query_string`, `collect_values`, `first_value` | same names, camelCase | |
| Part 7 `path_is_update`, `split_path_qs`, `content_type_base`, `extract_charset_param`, `charset_is_utf8_or_absent`, `chars_contains_word`, `str_contains_word_ci`, `update_has_dataset_clause`, `kvs_have_using_param`, `build_from_kvs`, `decode_request` | `pathIsUpdate`, `splitPathQs`, `contentTypeBase`, `extractCharsetParam`, `charsetIsUtf8OrAbsent`, `containsWord`, `containsWordCi`, `updateHasDatasetClause`, `kvsHaveUsingParam`, `buildFromKvs`, `decodeRequest` (+ `effectiveQs`) | `containsWord` diverges, see below |
| Part 14 `proto_request`, `proto_status_class`, `proto_strip_indent` …, `extract_request`, `extract_status_class`, `proto_header` | `ProtoRequest`, `StatusClass`, `stripIndent` …, `extractRequest`, `extractStatusClass`, `header` | |
| `w3c_runner.ml` `_gsp_extract_response_status` (OCaml) | `extractResponseStatus` | the numeric status the Graph Store manifest carries |
| `SPARQL.GraphStore.fst` (`graph_store`, `gs_target`, `gsp_get/head/put/post/delete`, `status_*`) | `SPARQL/GraphStore.lean` `GraphStore`, `Target`, `get/head/put/post/delete`, `status*` | keys are plain strings, as in the F\* |
| `w3c_runner.ml` `_gsp_target_of_request` (OCaml) | `decodeTarget` | §4.1 identification in the library; a non-IRI `graph=` is 400 (new) |
| — | `Method`, `handle` | new: the state machine as one total function; PATCH → 405 |
| `SPARQL.ServiceDescription.fst` (`sd_*`, `build_sd`, `has_endpoint_triple`, `has_service_type`, `has_supported_language`, `conforms_to_schema`, `returns_rdf`) | `SPARQL/ServiceDescription.lean`, same names camelCase | `datasetIriOf` / `defaultGraphIriOf` keep the F\* fallback to the endpoint |
| `run_protocol_test`, `run_gsp_test`, `run_service_description_test`, `_gsp_canonical_key`, `_gsp_should_seed`, `_gsp_is_mismatched_payload_test`, `_gsp_status_matches` | `Harness/ProtocolRun.lean` `protocolVerdict` / `runProtocolTest`, `gspStep` / `runGspTest`, `serviceDescriptionVerdict`, `gspCanonicalKey`, `gspShouldSeed`, `gspIsMismatchedPayload`, `gspStatusMatches` | the cross-test store is an `IO.Ref` per manifest (`Harness.Main`), reset at `PUT - Initial state` |

Not ported: Accept-header negotiation (F\* Part 6) and the response
serialisers (Parts 8–12) — the tests assert on status class, and the
Lean tree already has the results serialisers.

### Translation decisions

- `%XX` escapes decode to bytes and byte runs are read as UTF-8
  (`%C3%A9` → `é`), with a one-codepoint-per-byte fallback for runs
  that are not UTF-8, so decoding stays total. The F\* maps each
  escape to the codepoint of its value (finding below). No W3C
  protocol request carries a non-ASCII escape, so the score is the
  same either way; the guards pin the 2-, 3- and 4-byte cases.
- `pctUnits` / `utf8Assemble` are well-founded on list length
  (nested matches on the tail blocked structural recursion), so
  proofs unfold them with `conv => lhs; unfold …` and `#guard`s run
  the compiled code (pitfall 7 applies: no `decide` over them).
- `containsWord` keeps scanning after a prefix match that is not
  whitespace-bounded; the F\* returns `false` there (finding below).
  Guarded: `INSERT { <withdraw> … } USING <g> WHERE {}` is `true`.
- `decodeTarget` lives in the library as GSP §4.1; the
  `$GRAPHSTORE$` / `$HOST$` / `$NEWPATH$` placeholder collapse, the
  entry-name seeding and the `mismatched payload` name dispatch stay
  in the harness as manifest-shape glue, exactly where the F\* runner
  keeps them. Seeding is counted: `HARNESS-DIAG … gsp_seeded=N`
  (the F\* runner's `gsp_seed`; both trees report 1 on this suite —
  `DELETE - existing graph` names `person/2.ttl`, which no earlier
  entry PUT).
- The F\* runner evaluates the decoded query (or applies the update)
  over an empty dataset and drops the result, mapping every
  evaluation outcome to PASS when 2xx is expected; the verdict depends
  on the decoder and the parser only. This port does the same
  evaluation and carries its one-line summary into the FAIL text of an
  accepted-but-4xx-expected entry — the only place it can show. Only
  the first request block of an entry is decoded in either tree (the
  `update_dataset_*` UPDATE-then-ASK sequences are not replayed).
- Update-shaped requests go through `parseSparqlUpdate` /
  `applyUpdateIn` (the SPARQL 1.1 Update stage above, merged from
  `claude/main` into this branch before it closed). Before that merge
  they scored `unsupported` (26 pass, 8 unsupported on protocol); the
  merge took the suite to 34 of 34.

### Guards and theorems

`ProtocolTests.lean`: 134 `#guard`s — percent-decoding (ASCII,
`+`, malformed `%`, 2/3/4-byte UTF-8, Latin-1 fallback, encode
round-trips), the parameter bag, Content-Type / charset, USING/WITH
detection, every W3C protocol request shape (12 positive, 14
negative) against `decodeRequest` with the rule named, the
`rdfs:comment` scrapers on three manifest shapes, the Graph Store
state machine (PUT 201/204, POST 201/200 with merge, DELETE 204/404,
GET/HEAD, default graph, PATCH 405), §4.1 target decoding (incl. two
malformed `graph=` → 400), and the three Service Description checks.

`ProtocolTheorems.lean` (axioms: propext, Classical.choice,
Quot.sound): `percentDecode_percentEncode_ascii` /
`urlDecode_percentEncode_ascii` (decoding inverts encoding on every
ASCII string — the RFC 3986 reserved and unreserved sets and `%`),
`decodeRequest_get_no_query` (a GET with no `query=` parameter is
a 400-class verdict, Protocol §2.1.1 + §2.2.2), and
`decodeTarget_malformed_graph` (GSP §4.1: a `graph=` that is not an
IRI is 400).

### Measured (`lake exe l4w3c`, verbatim)

```
protocol: 34 pass, 0 fail, 0 skip, 0 unsupported (out of 34)
http-rdf-update: 19 pass, 0 fail, 0 skip, 0 unsupported (out of 19)
service-description: 3 pass, 0 fail, 0 skip, 0 unsupported (out of 3)
TOTAL: 601 pass, 0 fail, 0 skip, 30 unsupported (out of 631)
```

The 30 unsupported are the OWL-Direct / OWL-RDF-Based / RIF
entailment-regime evaluation tests (the RDFS / RDF / D ones run since
the entailment stage, merged from `claude/main` as well). The F\*
runner (`docs/test-results/latest.json`) has protocol 34 pass,
0 fail (out of 34); http-rdf-update 19 pass, 0 fail (out of 19),
`gsp_seed` 1; service-description 3 pass, 0 fail (out of 3). The
query types stay at 356 pass, 0 fail; the Update types at the Update
stage's numbers; the six RDF suites at 1078 pass, 0 fail (out of
1078).

Sabotage record (2026-08-22):
1. `+` → space removed from `pctUnits`: `lake build` fails at
   `ProtocolTests.lean:31` (`formDecode "a+b"`) and `:56` (the
   parameter bag). With those two guards disabled, NO W3C protocol
   test flips — the manifest writes every space as `%20` and its
   only `+` characters are in response media types. The guards are
   the only detector for this rule.
2. `charsetIsUtf8OrAbsent` forced to `true` (three guards disabled):
   `bad_query_non_utf8` and `bad_update_non_utf8` flip to FAIL
   ("Expected 4xx but decode_request accepted (POST /sparql/; …)").
   Before the Update merge the second landed in `unsupported` instead
   — a decoder regression on an update-shaped entry was invisible
   until the Update parser existed. Restored; the numbers above are
   from the restored build.

### Assumption report (append)

No `sorry`, no `axiom`, no `native_decide`, no `partial`, no
`@[extern]`. The F\* modules had no `assume val`.

### Findings against the F\* (not fixed here)

- `formal/fstar/SPARQL.Protocol.fst:146–167` (`url_decode_chars`):
  each `%XX` becomes the codepoint XX, so a percent-encoded
  multi-byte UTF-8 sequence decodes to one character per byte
  (`%C3%A9` → `Ã©`, not `é`). Invisible to the W3C suite (all-ASCII
  requests); visible to any non-ASCII IRI or literal in a GET query
  string.
- `formal/fstar/SPARQL.Protocol.fst:509–533` (`chars_contains_word`):
  on a prefix match that is not whitespace-bounded the function
  returns `false` instead of continuing the scan, so an update text
  such as `INSERT { <withdraw> … } USING <g> WHERE {}` is not seen to
  carry a `USING` clause and the §2.2.4 conflict with
  `using-graph-uri` is not raised. Also invisible to the W3C suite.
- `CLAUDE.md` quotes "SPARQL Protocol reaching 53 pass, 0 fail";
  `docs/test-results/latest.json` now has 34 + 19 + 3 = 56 pass,
  0 fail across the three suites.
## Stage: SHACL Core on the W3C data-shapes suite (branch `lean4/shacl`, 2026-08-22)

The SHACL Core validator (W3C Recommendation, 20 July 2017) is ported
from `formal/fstar/SHACL.Validation.fst`, with the spec/engine split the
owner asked for: `Spec.Conforms` is §3.4 conformance as a relation,
`validate` is the engine, and `ShaclTheorems.lean` proves the two agree
for every Core component. The real W3C manifests are read with the Lean
Turtle parser by a standalone probe (`lake exe l4shacl`, which does not
touch `Harness/Run.lean` / `Harness/Manifest.lean`).

### Module correspondence (append)

| F\* | Lean 4 | Notes |
|---|---|---|
| `SHACL.Validation.fst` §1, §11b (IRI constants) | `SHACL/Vocabulary.lean` | `assert_norm (is_iri …)` → `⟨"…", rfl⟩`; SHACL-SPARQL predicates kept only as `sparqlFeaturePredicates` for the `unsupported` report |
| §2–§7 (`severity`, `node_kind`, `path`, `target`, `constraint_component`, `shape`) | `SHACL/Shapes.lean` (`Severity`, `NodeKind`, `Path`, `Target`, `Constraint`, `Shape`, `ShapesGraph`) | Core 1.1 constructors only; the SHACL 1.2 / SHACL-AF / SHACL-SPARQL constructors (`CC_DatatypeIn`, `CC_SingleLine`, `CC_MemberShape`, `CC_Sparql`, `CC_Custom`, `T_Sparql`, `values_query`, `target_where`, `constraint_meta`) are not ported |
| §11a `rdf_list_terms`, §11c `parse_path`, §11f `build_targets` / `build_constraints` / `build_shape` / `parse_shape_from_graph_pure` | `rdfListTerms`, `decodePath`, `decodeTargets`, `decodeConstraints`, `decodeShape`, `decodeShapesGraph` | same fuel idiom (graph length bounds every data-driven walk); list-before-sh:*Path reading kept for path-strange-001/002 |
| §11c `path_invert`, `eval_path_fuel` / `eval_seq_fuel` / `eval_alt_fuel` / `eval_plus_fuel` | `Path.invert`, `evalPathFuel` group, `evalPath` | structural recursion on the fuel; `dedupTerms` after every hop |
| §11d `shacl_class_closure` / `is_shacl_instance` | `superClasses` (fixpoint over `addNew`), `isShaclInstance` | the F\* materialises the closure of the whole graph with the RDFS rules; the Lean walks rdfs:subClassOf from the node's rdf:type values — same §1.4 relation, proved both ways |
| §11e `eval_target` | `evalTarget`, `shapeFocusNodes` | `T_Sparql`, `T_DataShape` not ported |
| `XSD.Datatypes.fst` `literal_ill_formed`, `numeric_cmp_le/lt`, `dt_parse_ms` | `literalIllFormed`, `numericCmpLe/Lt`, `dtParseMs`, `literalToScaled` | `Scaled` / `parseToScaled` / `parseDoubleToScaled` reused from `SPARQL/Expr.lean` |
| §11g `term_lt` / `term_le` | `termLt`, `termLe` | |
| §11h–§11i `collect_shape_violations` / `eval_one_constraint` / `eval_aggregate_constraints` | `collectShapeViolations` / `evalOneConstraint` / `evalAggregate` / `qualifyingCount`, with `simpleValueCheck` and `evalAggregateNonRec` factored out | the non-recursive components are plain functions so each has its own theorem |
| §11j `validate` | `validate` | fuel `4·|shapes| + 50` as the F\* |
| §13 `validation_report_to_graph`, `result_to_triples`, `path_to_rdf` | `SHACL/Report.lean` (`reportToGraph`, `resultToTriples`, `pathToRdf`) | same predicate set, same single blank-node counter |
| `bin/shacl-runner/shacl_runner.ml` | `Harness/ShaclProbe.lean` (exe `l4shacl`) | manifest walk through repeated `mf:include`, `expected_report_graph` closure, the sh:resultMessage carve-out, RDFC-1.0 canonical N-Quads comparison (`RDF/Canonical.lean`), `--conforms-only` |
| `assume val eval_sparql_target_select` (the one SHACL `assume val`) | — | a forward reference for the unimplemented SPARQL-target form; no counterpart needed |

### Measured (verbatim, 2026-08-22)

```
shacl-core core/complex: 2 pass, 0 fail, 0 skip, 0 unsupported (out of 2)
shacl-core core/misc: 5 pass, 0 fail, 0 skip, 0 unsupported (out of 5)
shacl-core core/node: 32 pass, 0 fail, 0 skip, 0 unsupported (out of 32)
shacl-core core/path: 13 pass, 0 fail, 0 skip, 0 unsupported (out of 13)
shacl-core core/property: 38 pass, 0 fail, 0 skip, 0 unsupported (out of 38)
shacl-core core/targets: 7 pass, 0 fail, 0 skip, 0 unsupported (out of 7)
shacl-core core/validation-reports: 1 pass, 0 fail, 0 skip, 0 unsupported (out of 1)
shacl-core TOTAL: 98 pass, 0 fail, 0 skip, 0 unsupported (out of 98)
shacl-sparql sparql/component: 0 pass, 0 fail, 0 skip, 3 unsupported (out of 3)
shacl-sparql sparql/node: 0 pass, 0 fail, 0 skip, 4 unsupported (out of 4)
shacl-sparql sparql/property: 0 pass, 0 fail, 0 skip, 1 unsupported (out of 1)
shacl-sparql sparql/pre-binding: 0 pass, 0 fail, 0 skip, 14 unsupported (out of 14)
shacl-sparql TOTAL: 0 pass, 0 fail, 0 skip, 22 unsupported (out of 22)
```

F\* side, same denominators (`skills/test-suites/SKILL.md`, baseline
2026-07-05): shacl-core 98 pass, 0 fail (out of 98); shacl-sparql 22
pass, 0 fail (out of 22). The Lean tree matches on core and names the
whole SPARQL suite unsupported. Full-report comparison (default), not
conforms-only.

### Sabotage record

`sh:maxCount` disabled (`| .maxCount _ => []` in `evalAggregateNonRec`):
shacl-core drops to 88 pass, 10 fail (out of 98) — maxCount-001,
maxCount-002, targetClass-001, targetNode-001, targetSubjectsOf-001,
targetSubjectsOf-002, and-002, path-inverse-001, personexample,
shacl-shacl (the last reports 59 results against an expected conforming
report). Restored; 98 pass, 0 fail again; `ShaclTests.lean` pins
maxCount at the unit level too.

### Theorems (`ShaclTheorems.lean`; axiom audit propext, Classical.choice, Quot.sound)

- `validate_empty_conforms`, `validate_no_targets_conforms` (§3.1, §2.1).
- `minCount_zero_no_result` (§4.2.1).
- `notOf_flips` (§4.6.1): a node shape whose only component is `sh:not r`
  has no result iff the referenced shape has one.
- `isShaclInstance_iff` (§1.4): the closure walk is sound
  (`superClassesFuel_sound`) and complete
  (`superClasses_complete` — a non-closed run with fuel `|g| + 1` would
  hold more distinct classes than rdfs:subClassOf objects plus one,
  `Nodup.length_le_of_subset`).
- `simpleValueCheck_iff`: sh:class, sh:datatype, sh:nodeKind, sh:in,
  sh:pattern, sh:minLength, sh:maxLength, sh:languageIn, the four
  sh:min/maxInclusive/Exclusive — each decides its `Spec.ValueSatisfies`
  clause.
- `evalAggregateNonRec_eq_nil_iff`: sh:minCount, sh:maxCount,
  sh:hasValue, sh:uniqueLang, sh:closed, sh:equals, sh:disjoint,
  sh:lessThan, sh:lessThanOrEquals — each decides its
  `Spec.FocusSatisfies` clause.
- `collectShapeViolations_eq_nil_iff` (§3.4) and `validate_conforms_iff`
  / `validate_sound` (§3.1): the engine reports no result iff
  `Spec.Conforms` / `Spec.GraphConforms`, by induction on the fuel
  through the mutual group.

Where the specification names the engine: `Spec.ValueConforms` for
sh:xone counts matching shapes with the engine's filter, and
`Spec.AggConforms` for sh:qualifiedMin/MaxCount uses `qualifyingCount`;
path evaluation (`evalPath`) is the path semantics on both sides. Those
three are the named open obligations for a fully independent spec.

### Translation decisions

- Deactivated shapes are dropped at decode time (as the F\*); a
  deactivated shape is unreachable by reference and by target alike.
- `sh:uniqueLang` / `sh:closed` / `sh:deactivated` / qualified-disjoint
  flags are matched LEXICALLY against `"true"` (uniqueLang-002-shapes.ttl
  documents the suite's intent).
- The implicit class target (§2.1.3.1) requires `rdf:type sh:NodeShape`
  together with `rdfs:Class` / `owl:Class`, as the F\*.
- `Spec.Conforms 0` is `True`: the engine's fuel exhaustion is
  sound-by-omission and the specification says so at the same budget.
- `sh:minCount` / `sh:maxCount` / the other non-recursive aggregates run
  at the shape's fuel level, not one below (the F\* evaluates them inside
  the fuel-decrementing group); observable only at fuel 1, which
  `validate` never uses.

### Assumption report (append)

None: no `axiom`, `sorry`, `native_decide`, `partial`, `opaque` or
`@[extern]` in `L4Factoidal/SHACL/`. The probe uses one `partial def`
(the manifest walk) outside the library. The F\* module carries one
`assume val` (`eval_sparql_target_select`, SPARQL targets), not
reachable from Core.

### Findings against the F\* (not fixed here)

- `formal/fstar/SHACL.Validation.fst:2464-2465` (`CC_MinLength` /
  `CC_MaxLength`): `String.length` on the extracted OCaml string is a
  BYTE count, while §4.4.1 counts characters ("the length of the string
  representation"); a value such as `"ü"` has length 2 there. No suite
  fixture exercises a non-ASCII length. The Lean counts codepoints.
- `formal/fstar/XSD.Datatypes.fst:178-195` (`dt_parse_ms`): the date
  separators are never checked — `"2002x10x10x12x00x00"^^xsd:dateTime`
  parses as a valid dateTime. Ported unchanged so the two trees agree on
  the suite; `ShaclTests.lean` does not pin the lenient reading.

## Stage: differential harness + property-based probe (branch `lean4/differential`, 2026-08-22)

Owner's ask, verbatim: "look into ways of creating more unit tests
that truly exercise an implementation". Two mechanisms from
`docs/designissues/2026-08-22-lean4-w3c-harness.md` § "Tests that truly
exercise an implementation", built and measured (the numbers, the
findings with attribution and the sabotage record are in that
document's closing section).

### Module correspondence

| F\* / OCaml | Lean | Notes |
|---|---|---|
| — (no generator in the F\* tree) | `L4Factoidal/Testing/Gen.lean` | splitmix64 over `Nat` (`Rng`), `Gen` state monad, vocabulary, graph / BGP / query generators, SPARQL-text and algebra-AST renderings, `genCase seed` |
| `SPARQL/Invariants.lean` theorems, `QueryTheorems.lean` | `L4Factoidal/Testing/Props.lean` | 18 executable invariants `Case → Option String`; the theorems' statements checked on the EXECUTED code, plus laws no theorem covers (join commutativity, results-format round trips, RDFC relabelling, isomorphism) |
| `bin/w3c-runner/w3c_runner.ml` `run_query_eval_test` (one engine vs a file) | `Harness/Differential.lean` (`l4diff`) | TWO engines vs each other: `bin/<platform>/factoidal` via `IO.Process` (`-o json` / `-o ntriples`, `perl alarm` cap) against `parseSparql` + `evalSelect`/`evalAsk`/`evalConstruct`; compared with `Harness/Compare.lean` unchanged |
| — | `Harness/PropProbe.lean` (`l4prop`) | N seeded cases, per-invariant `pass, fail (out of N)`, repro on every failure, exit 1 |
| — | `L4Factoidal/Testing/GenTests.lean` | `#guard`s: splitmix64 reference output, determinism, pinned renderings of two seeds, the invariants on three seeds |

### Translation decisions

- The generator is a `structure Gen` state monad rather than a
  function abbreviation, so `do` notation resolves without fighting
  the function-space instances; `natLt`, `pick`, `listOf`, `bool` are
  the whole combinator set.
- The vocabulary is bounded and dense on purpose (three subjects,
  three predicates, two blank nodes, thirteen literals over four
  datatypes and three language tags) so joins join and OPTIONALs
  sometimes bind — the property probe prints how many BGP rows it
  evaluated (`measurement:` line) so a vacuous run is visible.
- Generated `LIMIT` is only emitted together with an `ORDER BY` over
  ALL three variables: a LIMIT over an unordered or partially ordered
  sequence is implementation-defined and would report spec-permitted
  differences as disagreements.
- The differential harness keeps the W3C comparator as it is
  (multiset under bijection; ORDER BY pins positions only for rows
  with blank nodes). An ordered comparison that fails but passes
  unordered is reported as `tie-order`, its own bucket, never as
  agreement. None occurred in the measured runs.
- CSV/TSV round trips are stated for results with ≥ 1 variable (the
  zero-column header is spec-ambiguous — recorded in the design doc).
- `evalConstruct` now applies `ORDER BY` before `LIMIT` (§18.2.4); the
  differential harness found the unordered slice, in BOTH trees.

### Guards and theorems

No new theorem. `GenTests.lean` adds 13 `#guard`s; `QueryTests.lean`
adds one (`CONSTRUCT … ORDER BY DESC(?label) LIMIT 1`). The library
build stays at zero `sorry` / `axiom` / `native_decide` / `partial`.

### Sabotage record (2026-08-22)

- `insertOrdered` dropping tied rows: caught by `l4prop`
  (`orderby_perm` 497 pass, 3 fail, out of 500), by `l4diff` (one more
  sparql11 disagreement) and by the full build (`sortSolutions_perm`,
  a `QueryTests` guard).
- `tryBindTerm` ignoring an existing binding of a repeated variable:
  caught by `l4diff` only (generated: 403 agree, 97 disagree, out of
  500); `l4prop` 0 failures (the laws are relative); the full library
  build PASSED — no guard or theorem covered it. Two guards added to
  `Tests.lean` so it does now.

### Assumption report (append)

No `sorry`, no `axiom`, no `native_decide`, no `partial`, no
`@[extern]` in `L4Factoidal/`. The harness executables do file and
process I/O (`IO.Process.output`) — harness code, outside the library.

### Findings against the F\* (not fixed here)

See the design document's closing section for the eleven itemised
findings. In one line each: `eval_construct_query` slices before
ordering; `ASK { ?x <q> ?x }` is true when `SELECT` returns no row;
the `functions` / `cast` expression errors that §17 says must leave a
variable unbound are bound (13 W3C tests), hidden by
`w3c_runner.ml`'s row matcher ignoring extra actual bindings;
`SERVICE SILENT` to an unreachable endpoint yields no solution
instead of one empty solution; `GRAPH ?g { ?x ?p ?g }` ignores the
inner `?g`; `UUID()` repeats within a query; a CONSTRUCT template
list emits `_:tpl_0__:bnode_13` in N-Triples output; the CLI has no
query BASE.

## Stage: Verifiable Credentials Data Integrity, `eddsa-rdfc-2022`, did:key (branch `lean4/vc`, 2026-08-22)

Proof creation and verification for the Data Integrity EdDSA
cryptosuite (W3C vc-di-eddsa §3.3), on top of the landed RDFC-1.0
(`RDF/Canonical.lean`) and JSON-LD toRdf (`JSONLD/`), with the Ed25519
primitive bound to HACL\* — the Lean tree's first and only `@[extern]`
family, exactly as `docs/designissues/2026-08-22-lean4-external-dependencies.md`
§3 step 6 predicted.

### Module correspondence

| F\* | Lean | Notes |
|---|---|---|
| `VC.Multibase.fst` (`hex_digit_val`, `hex_to_bytes`, `bytes_to_hex`, `bytes_to_nat`, `nat_to_bytes_be`, `base58btc_encode/decode`, `multibase_encode_base58btc`, `multibase_decode`, `hex_to_multibase_z`, `multibase_z_to_hex`, `ed25519_multicodec_prefix`, `ed25519_pubkey_to_multikey`) | `VC/Multibase.lean` (`hexDigitVal?`, `bytesOfHex?`, `hexOfBytes`, `bytesToNat`, `natToBytesBE`, `base58Encode`/`base58Decode?`, `multibaseEncodeBase58btc`, `multibaseDecode?`, `hexToMultibaseZ?`, `multibaseZToHex?`, `ed25519PubPrefix`, `ed25519PublicKeyToMultikey`) | bytes are `List UInt8`; nat codecs are most-significant-first with an accumulator so the round trip is a structural induction (below). New: `ed25519PrivPrefix` (`80 26`, the `z3u2…` secret-key Multikey of the spec vectors), `multikeyToEd25519PublicKey?` / `…SecretKey?`. NOT ported: the lenient base64(-url) decoder — it serves `VC.Credential`'s `relatedResource` digests, and that module is not in this stage. |
| `DID.Key.fst` (`parse_did_key`, `did_key_document`, the nine pinned IRIs) | `VC/DidKey.lean` (`parseDidKey`, `didKeyDocument`, same IRIs) | prefix stripping over `List Char`. New: the inverse `didKeyOfPublicKey` / `verificationMethodOfPublicKey` (the F\* tree re-implements it in JavaScript in `bin/vc-api-shim/server.mjs`) and `publicKeyOfVerificationMethod?`. `keyAgreement` omitted as in the F\*. |
| `VC.DataIntegrity.fst` (`transform_dataset`, `hash_data_hex`, `eddsa_rdfc_2022_create_from_canonical`, `…verify_from_canonical`, `eddsa_rdfc_2022_create`, `…verify`, `di_proof`, `serialize_proof`, `make_eddsa_proof`) | `VC/DataIntegrity.lean` (`transformDataset`, `hashData`/`hashDataHex`, `createFromCanonical`, `verifyFromCanonical`, `createProofValue`, `verifyProofValue`, `DiProof`, `serializeProof`, `makeEddsaProof`) | the four crypto `assume val`s become: SHA-256 = pure `Crypto/SHA2.lean` behind `HashAlgorithm` (hash agility); Ed25519 = `SignFn` / `VerifyFn` PARAMETERS. New, document level (what `bin/vc-api-shim/server.mjs` does in JavaScript): `proofOptionsOf`, `unsecuredOf`, `canonicalizeJsonLd`, `verifyOneProof`, `verifyDocument` (typed `VerifyError` refusals), `secureDocument`. |
| `bin/vc-api-shim/server.mjs` `proofContextFor`; `third_party/contexts/PROVENANCE.md` | `VC/Context.lean` (`proofContextFor`, `vendoredContextFiles`, `vcLoader`) | data + the proof-options context rule; the loader is a parameter. NOT a port of `VC.Context.fst` (see "Not ported"). |
| `experimental_ocaml_glue/hacl_stubs.c` + `fstar_hacl_crypto.ml` (hex-string FFI to HACL\*) | `ffi/hacl_ed25519.c` + `Crypto/Ed25519.lean` (`secretToPublic`, `sign`, `verify` over `ByteArray`) | compiled and archived by Lake (`lakefile.lean`, `extern_lib libl4hacl`) from the unmodified `third_party/hacl/` sources. |
| `bin/did-runner/did_runner.ml`, `bin/vc-runner/vc_runner.ml --crypto` | `Harness/VcProbe.lean` (`lake exe l4vc-probe`) | same fixtures, same checks, plus RFC 8032 and the W3C spec vectors. |

### `lakefile.toml` → `lakefile.lean`

Lake's TOML format has no `extern_lib` target (Lake 4.33:
`Lake/Load/Toml.lean` decodes `lean_lib`, `lean_exe`, `input_file`,
`input_dir` only), so the configuration became the Lean DSL — the
`lake translate-config lean` output of the former TOML, comments carried
over, plus four `target … : FilePath` C compilations (`buildO`, `-O2
-fPIC -I third_party/hacl/include -I <lean include>`, the flags
`build-ocaml.sh` uses for the same units) and the `extern_lib` that
archives them into `.lake/build/lib/libl4hacl.a`. Lake links an
`extern_lib` into every executable of the package, so nothing else
changed for the probes. Integrators merging other `lean4/*` branches:
a TOML edit on their side is a modify/delete conflict here — re-apply
it to the DSL file by hand (the shapes correspond one to one).

### Measured (`lake exe l4vc-probe`, verbatim)

```
ed25519-rfc8032: 22 pass, 0 fail (out of 22)
did:key: 8 pass, 0 fail (out of 8)
vc-dataintegrity-eddsa-rdfc-2022: 8 pass, 0 fail (out of 8)
vc-di-eddsa-spec-vectors: 20 pass, 0 fail (out of 20)
TOTAL: 58 pass, 0 fail (out of 58)
```

Beside the F\* tree (`docs/test-results/latest.json`): `did_key` 8
pass, 0 fail (out of 8) — the same three `tests/did` vectors and five
rejection cases; `bin/vc-runner --crypto` prints
`vc-dataintegrity-eddsa-rdfc-2022: 8 pass, 0 fail (out of 8)` on the
same inputs (its eight checks are replayed one for one, N-Quads and keys
identical). The two remaining sections have no F\* counterpart to put
beside them: the RFC 8032 vectors are the binding's own measurement
(an `@[extern]` cannot be `#guard`ed), and the F\* tree's
`vc_di_eddsa` score (31 pass, 0 fail) is the live-endpoint mocha suite
through the Node VC-API shim, not an offline run of the specification's
vectors. Section 4 is the strongest line: the spec's unsigned
credential and proof options go through the Lean JSON-LD processor
(vendored contexts) and RDFC-1.0 and reproduce the spec's canonical
N-Quads byte for byte, its two SHA-256 digests, the Ed25519 signature
`4d8e53…` and the proofValue `z2YwC8…`; `secureDocument` then produces
that proof and `verifyDocument` accepts it and refuses a tampered
proofValue, a changed claim, the wrong purpose, a non-did:key
verification method, and the unsecured credential.

`lake build`: 272 jobs, green; 77 new `#guard`s in `VC/Tests.lean`
(base58 Bitcoin Core vectors, the three did:key vectors and five
rejections, the DID document, the spec vectors' pure parts, the
pipeline with a stub verifier, the proof-options context rule, the
document-level field surgery).

### Theorems (`VC/Theorems.lean`, 34; axioms: propext, Classical.choice, Quot.sound)

- `base58Decode?_base58Encode : base58Decode? (base58Encode bs) = some bs`
  — the lemma `VC.Multibase.fst`'s banner declines ("a full base58
  bijection proof … is a disproportionate proof burden"). It is ~150
  lines: digits→nat→digits and bytes→nat→bytes by strong induction
  (`digitsToNat58_natToDigits58`, `natToBytesBE_bytesToNatAcc` in
  accumulator form), the leading-zero run via `takeWhile_append_dropWhile`,
  the two alphabet facts (`base58Digit?_base58Char`, `base58Char_ne_one`)
  by `decide` over the 58-entry list literal.
- `multibaseDecode?_encode`, `multikeyToEd25519PublicKey?_of_key`,
  `parseDidKey_didKeyOfPublicKey` (a 32-byte key survives `did:key:`).
- `hashData_congr`, `createProofValue_of_canonical_eq`,
  `verifyProofValue_of_canonical_eq`: the hash input, the proof value and
  the verdict are functions of the RDFC-1.0 canonical forms only.
- `verifyFromCanonical_not_multibase`, `verifyDocument_noProof`: refusals
  that hold for every primitive and loader.
- `verifyFromCanonical_createFromCanonical`: create-then-verify succeeds
  under the single hypothesis `verifyF pk m (signF sk m) = true` — the
  signature scheme's correctness, stated as a premise, never assumed
  globally.

### Translation decisions

- **Primitives are parameters.** `createFromCanonical`/`verifyFromCanonical`
  and everything above them take `SignFn`/`VerifyFn`. Consequences: the
  library is a total function of its inputs; the `#guard`s exercise the
  pipeline with a stub verifier that accepts exactly the spec vector's
  (pk, hashData, signature); no compile-time evaluation ever touches the
  extern (it could not — `#guard` runs the interpreter, which has no
  native symbol for an `@[extern]` opaque).
- **Bytes, not hex, at the FFI.** The F\* boundary is lowercase hex
  strings; the Lean binding takes `ByteArray`s and the C shim only checks
  lengths. Hex lives in `Multibase` for the vectors and the
  `hash_data_hex` parity function.
- **Refusals are typed.** `verifyDocument : … → Except VerifyError Unit`;
  every non-success has a constructor and a `describe`. A length-refused
  key is an EMPTY result from the primitive and `none` from
  `createFromCanonical` (the F\* `""` convention), never a proof value.
- **Proof sets verify member by member; proof chains are refused**
  (`proofChainUnsupported`). The F\* shim implements chains in JavaScript;
  porting that is document-level work for a later stage.
- **`created` is optional** and not validated beyond presence (as in the
  F\*); `proofPurpose` must equal the caller's expected purpose (default
  `assertionMethod`).
- **The securing document's `@context` is extended** by
  `proofContextFor` exactly as the shim extends it, so re-verification
  rebuilds the same proof-options context; for a VCDM 2.0 document that
  is the identity.

### Sabotage record (2026-08-22)

1. `hashData` concatenation order swapped (document hash first):
   `lake build` fails at `VC/Tests.lean:177` (`hashDataHex … ==
   specCfgHash ++ specDocHash`). Restored, green.
2. `base58Encode` stops emitting the leading `'1'` per zero byte:
   `VC/Tests.lean:59` and `:66` (the two Bitcoin Core vectors with
   leading zeros) fail AND `VC/Theorems.lean:248`
   (`base58Decode?_base58Encode`) no longer proves. Restored, green.
3. The C shim's `l4_hacl_ed25519_verify` made to return 1
   unconditionally (the build stays green — no `#guard` can see an
   extern): `l4vc-probe` reports `ed25519-rfc8032: 13 pass, 9 fail (out
   of 22)`, `vc-dataintegrity-eddsa-rdfc-2022: 5 pass, 3 fail (out of
   8)`, `vc-di-eddsa-spec-vectors: 17 pass, 3 fail (out of 20)` — every
   negative check (flipped signature bytes, wrong key, tampered
   proofValue, changed claim, corrupted canonical form). Restored:
   58 pass, 0 fail. This is why the probe carries negative checks in
   every section.
4. Measured live rather than by code sabotage, as the probe's own
   checks: flipping byte 0 or byte 63 of each RFC 8032 signature makes
   `verify` false; swapping two INPUT quads leaves the RDFC-1.0
   canonical form unchanged (so the proof still verifies), while
   swapping two lines of the canonical form changes the SHA-256 digest
   and the spec signature no longer verifies over it.

### Assumption report (append) — THE ONE EXTERN

The F\* `VC.DataIntegrity.fst` has four `assume val`s:
`hash_sha256_hex` (dissolved: pure Lean SHA-256, FIPS 180-4 vectors as
`#guard`s, `Crypto/SHA2.lean`) and `ed25519_secret_to_public` /
`ed25519_sign` / `ed25519_verify`. The latter three are
`Crypto/Ed25519.lean`'s `@[extern "l4_hacl_ed25519_*"] opaque`
declarations — the FIRST member of the Lean tree's permitted crypto
`extern` family under the crypto-policy skill's Lean 4 amendment
(signatures via HACL\* FFI only; never a hand-written
implementation). The SECOND member, added 2026-09-02, is
`Crypto/SHA2Native.lean`'s `@[extern "l4_hacl_sha256"] opaque
sha256Hacl`, permitted by item 1 of the same amendment ("binding
HACL\*'s `Hacl_Hash_SHA2.c` via Lean FFI as well, for speed, is
encouraged"); `hash_sha256_hex` stays dissolved because the PURE Lean
`sha256` remains the specification and remains what every `#guard`
and every theorem evaluates. Trust statement, in full,
in that module's header; in short: Lean knows their types and nothing
about their values; no theorem depends on them (`#print axioms` on
every theorem of the library is unchanged: propext, Classical.choice,
Quot.sound); what is trusted is HACL\*'s F\*/Low\*-verified Ed25519
(vendored unmodified, Apache-2.0, cryspen/hacl-packages
`05c3d8fb321ed65e3db3a6a8b853019e86fb40a2`), the 60-line
length-checking shim, and Lean's FFI calling convention; what is
measured is RFC 8032 §7.1 through the binding at run time. `VC.Multibase.fst`,
`DID.Key.fst`: zero `assume val`s, confirmed by grep. No `sorry`, no
`axiom`, no `native_decide`, no `partial` in `L4Factoidal/`
(`Harness/VcProbe.lean`'s `findRepoRoot` is `partial`, in the harness,
outside the library, like the other probes' directory walks).

### Not ported (and said so)

- `VC.Credential.fst` + `VC.Context.fst` — the VCDM 2.0 STRUCTURAL
  validator and its purpose-built term-resolution walker (the F\*
  `vc_stage1` suite, 117 pass, 0 fail (out of 117) over
  `third_party/testing/vc/tests/input/*-ok|-fail.json`). A separate
  stage; the Lean tree's full JSON-LD processor would replace the
  walker rather than port it.
- Proof chains (`previousProof`), the live-endpoint suites
  (`vc_di_eddsa` 31, `vc20_api` 59 — mocha over HTTP through the Node
  shim), `keyAgreement` derivation (curve arithmetic; crypto policy).
- The wasm artifact: `Wasm/build-wasm.sh` now compiles the same four C
  units for wasm32 (each compile-checked under emcc 2026-08-22; the
  shim's object is named `l4_hacl_shim.o` because `hacl_ed25519.o`
  collides with `Hacl_Ed25519.o` on a case-insensitive filesystem — a
  trap found while checking), but the full module was not rebuilt in
  this stage.

### Findings against the F\* (not fixed here)

- `formal/fstar/VC.DataIntegrity.fst:21-23` ("NATIVE-ONLY … This module
  is deliberately excluded from the js_of_ocaml/wasm bundle") and
  `formal/fstar/build-ocaml.sh:1182-1184` (same claim) are stale since
  #286: the `js` step compiles `VC_DataIntegrity.ml` and links
  `hacl_stubs.js` (`build-ocaml.sh:2309`, `:2343`, `:2441`), and
  `skills/node-crypto-haclstar-vc-wasm-build` documents VC verify
  working off-native. An obsolescence-sweep item.
- `formal/fstar/VC.Multibase.fst:20-25`: the banner's reason for not
  stating `decode (encode bs) == Some bs` ("disproportionate proof
  burden") no longer holds as an estimate — the Lean proof is ~150
  lines with no library beyond core; the F\* statement would be of the
  same size.
- `bin/vc-runner/vc_runner.ml:381-383`: the `--crypto` roundtrip's
  proof-options dataset uses `http://www.w3.org/ns/data-integrity#cryptosuite`
  and `…#proofPurpose`, which are not the Data Integrity vocabulary
  (`https://w3id.org/security#cryptosuite`, typed
  `sec:cryptosuiteString`; `…#proofPurpose` with an IRI object). Harmless
  for a self-contained roundtrip — the Lean probe replays the same
  strings for parity — but it is not a spec-shaped input; the W3C
  vectors in section 4 are.
## Stage: indexed OWL 2 RL closure — no cap hits on the W3C OWL corpus (branch `lean4/owl-indexed`, 2026-08-22)

What landed: `L4Factoidal/OWL/RLClosureIndexed.lean` — the OWL 2 RL/RDF
closure over an indexed triple store, with a PROVED list equality to the
specification engine `RLClosure.closure`; `Harness/OwlProbe.lean` scores
with it, scopes imported-document blank nodes per import, and carries a
`--profile` mode (per-row timing of the list engine, indexed cross-check,
`--indexed-only` rounds). The spec (`RLRules.lean`) and the theorem file
(`RLTheorems.lean`) are untouched. The F\* counterpart of this step is
`RDFS.Closure.SemiNaive.fst`.

### Measured first: where the time was (list engine, `--profile`)

Per-row wall time of one `RLClosure.step` round, IO.Ref-forced (see the
measuring-inference skill, rule 9, for why the first instrument read 0 ms
on every row):

```
WebOnt-description-logic-204  premise 1074 triples
  round 1: rows total emitted=5235 ms=586     dedup addAll new=1750 ms=109    cls-int1: emitted=0 ms=577
  round 5: rows total emitted=30361 ms=6640   dedup addAll new=0 ms=648       cls-int1: emitted=328 ms=6443
WebOnt-miscellaneous-001      premise 2912 triples
  round 1: rows total emitted=12282 ms=20724  dedup addAll new=3534 ms=491    cls-int1: emitted=0 ms=20634
  round 2: rows total emitted=62272 ms=104840 dedup addAll new=4108 ms=2810   cls-int1: emitted=6323 ms=104322
```

One row — cls-int1 — is 95–99.6 % of every round: per `owl:intersectionOf`
triple it walks EVERY subject occurrence of the graph and runs a `memB`
list scan per class (O(#intersections × |g| × |list| × |g|)). The exact
dedup (`addAll`, a scan per conclusion) is second and grows with |g|;
every other row is under 50 ms. The 20 s budget was spent inside round 1
of the ~3 000-triple cases, as the task brief said.

### The indexed engine and its cost model

`Index`: `Array Triple` (insertion order), `Std.HashSet Triple` (exact
membership), five `Std.HashMap` buckets — S, P, O, (S,P), (P,O) — each
holding the REVERSED filter of the array. Lookup = `getD` + reverse:
O(1) + O(result). Insert = one `push`, one set insert, five `getD` +
`insert` with a cons: O(1). `memB`: O(1). A round is O(|g| + emitted)
instead of O(|g| × scans); the round count is unchanged (same stopping
rule). Evaluation is NAIVE with indexed joins, not semi-naive: each round
still drives every row from every triple of the input snapshot, which is
what makes the bridge a per-round equality. Measured on
WebOnt-miscellaneous-001 after the blank-node fix below: 8 rounds,
12 280 triples, 1 107 ms cumulative (round 1: 30 ms; list engine round 1:
20 724 ms).

### What is proved (`RLClosureIndexed.lean`, axioms: propext, Classical.choice, Quot.sound)

The rows are written once over a `Store` record of lookups. `Store.ofGraph g`
packs the list scans, and every row over it is the `RLClosure` row by
`rfl` (47 `xxxForS_ofGraph` lemmas, 13 clash rows; the five recursive
walkers by induction). `Index.Wf i g` — the array is `g`, the set decides
`memB g`, every bucket lookup EQUALS the list filter as a list — is
preserved by `push`, `insert` (= `addOne`), `insertAll` (= `addAll`), and
gives `Store.ofIndex_eq : Store.ofIndex i = Store.ofGraph g`. Hence:

- `Index.Wf.step` — one indexed round pictures one `RLClosure.step`;
- `Index.Wf.closure` — the loop takes the same branch at every fuel;
- `indexedClosure_eq : indexedClosure g fuel = closure g fuel` — LIST
  equality (order included), every graph, every fuel;
- `mem_indexedClosure_iff` — the set-membership form the task asked for;
- `detectClashI_closureI` — the indexed clash verdict is `inconsistent`.

So T1/T2/T4 and `detectClash_sound` of `RLTheorems.lean` hold of the
indexed engine by rewriting, with nothing re-proved. The proofs reason
about `Std.HashMap.getD_insert` / `Std.HashSet.contains_insert` only.
`RLTests.lean` evaluates `indexedClosure == closure` on every fixture so
the compiled hash path is exercised too.

Sabotage (2026-08-22): `Index.push` changed to skip `rdf:type` triples in
the (P,O) bucket. `lake build` fails at `Index.Wf.push` (line 912, type
mismatch: `BucketWf (i.byPO.insert …)` expected `BucketWf (i.push t).byPO`).
Restored; green.

### Measured score lines, verbatim — before and after, same 20 s cap

Baseline, list engine (`l4owl-probe --cap-ms 20000`, run from the repo
root, commit 9dd44d59a engine):

```
profile-RL.rdf: 102 pass, 19 fail, 0 skip, 5 unsupported (out of 126)
HARNESS-DIAG-OWL profile-RL.rdf: cases=91 units=126 triples_parsed=1227 closure_rounds=428 clashes=10 cap_hits=0 parse_failures=0 wall_ms=81
profile-EL.rdf: 95 pass, 21 fail, 1 skip, 4 unsupported (out of 121)
HARNESS-DIAG-OWL profile-EL.rdf: cases=87 units=121 triples_parsed=1098 closure_rounds=409 clashes=4 cap_hits=0 parse_failures=0 wall_ms=69
profile-QL.rdf: 76 pass, 11 fail, 0 skip, 0 unsupported (out of 87)
HARNESS-DIAG-OWL profile-QL.rdf: cases=65 units=87 triples_parsed=872 closure_rounds=303 clashes=5 cap_hits=0 parse_failures=0 wall_ms=57
type-positive-entailment.rdf: 290 pass, 116 fail, 0 skip, 6 unsupported (out of 412)
HARNESS-DIAG-OWL type-positive-entailment.rdf: cases=206 units=412 triples_parsed=28902 closure_rounds=1542 clashes=0 cap_hits=10 parse_failures=0 wall_ms=327877
type-inconsistency.rdf: 29 pass, 84 fail, 1 skip, 14 unsupported (out of 128)
HARNESS-DIAG-OWL type-inconsistency.rdf: cases=128 units=128 triples_parsed=5258 closure_rounds=425 clashes=29 cap_hits=0 parse_failures=0 wall_ms=1759
type-consistency.rdf: 451 pass, 120 fail, 0 skip, 12 unsupported (out of 583)
HARNESS-DIAG-OWL type-consistency.rdf: cases=354 units=583 triples_parsed=41248 closure_rounds=2107 clashes=0 cap_hits=14 parse_failures=1 wall_ms=401706
TOTAL: 1043 pass, 371 fail, 2 skip, 41 unsupported (out of 1457)
HARNESS-DIAG-OWL TOTAL: cases=931 units=1457 triples_parsed=78605 closure_rounds=5214 clashes=48 cap_hits=24 parse_failures=1
```

After — indexed engine + per-import blank-node scoping, same command:

```
profile-RL.rdf: 102 pass, 19 fail, 0 skip, 5 unsupported (out of 126)
HARNESS-DIAG-OWL profile-RL.rdf: cases=91 units=126 triples_parsed=1227 closure_rounds=428 clashes=10 cap_hits=0 parse_failures=0 wall_ms=52
profile-EL.rdf: 95 pass, 21 fail, 1 skip, 4 unsupported (out of 121)
HARNESS-DIAG-OWL profile-EL.rdf: cases=87 units=121 triples_parsed=1098 closure_rounds=409 clashes=4 cap_hits=0 parse_failures=0 wall_ms=43
profile-QL.rdf: 76 pass, 11 fail, 0 skip, 0 unsupported (out of 87)
HARNESS-DIAG-OWL profile-QL.rdf: cases=65 units=87 triples_parsed=872 closure_rounds=303 clashes=5 cap_hits=0 parse_failures=0 wall_ms=32
type-positive-entailment.rdf: 297 pass, 109 fail, 0 skip, 6 unsupported (out of 412)
HARNESS-DIAG-OWL type-positive-entailment.rdf: cases=206 units=412 triples_parsed=28902 closure_rounds=1576 clashes=0 cap_hits=0 parse_failures=0 wall_ms=4116
type-inconsistency.rdf: 29 pass, 84 fail, 1 skip, 14 unsupported (out of 128)
HARNESS-DIAG-OWL type-inconsistency.rdf: cases=128 units=128 triples_parsed=5258 closure_rounds=425 clashes=29 cap_hits=0 parse_failures=0 wall_ms=172
type-consistency.rdf: 461 pass, 110 fail, 0 skip, 12 unsupported (out of 583)
HARNESS-DIAG-OWL type-consistency.rdf: cases=354 units=583 triples_parsed=41248 closure_rounds=2159 clashes=0 cap_hits=0 parse_failures=1 wall_ms=7024
TOTAL: 1060 pass, 354 fail, 2 skip, 41 unsupported (out of 1457)
HARNESS-DIAG-OWL TOTAL: cases=931 units=1457 triples_parsed=78605 closure_rounds=5300 clashes=48 cap_hits=0 parse_failures=1
```

FAIL lists diffed (`comm` on the `FAIL <id> [type]` lines): no new FAIL;
these 10 units moved from fail to pass — WebOnt-description-logic-201,
-204, -206, -661, -664 [ConsistencyTest], -204 [PositiveEntailmentTest],
WebOnt-miscellaneous-001, -002, -011 [ConsistencyTest], -011
[PositiveEntailmentTest]. The 24 baseline cap hits are 12 distinct units;
the two not in the list above now fail on their merits:
WebOnt-description-logic-201 and -206 [PositiveEntailmentTest],
`closure-gap: missing <…#V822576> rdf:type <…#C110>` / `<…#V21027>
rdf:type <…#C30>` — the conclusions the F\* runner reaches through its
PE-via-refutation tableau fallback, which this probe's header already
names as not ported. The one `parse_failures=1` (FS2RDF-literals-ar,
RDF/XML §7.2.16) is unchanged.

### Finding on the way: an RDF union where a merge was needed (fixed in the probe)

With the fast engine, WebOnt-miscellaneous-001/002/011 [ConsistencyTest]
first FAILED with `clash: detectClash fired on a premise asserted
consistent (67989 triples)` after 5 rounds, the closure doubling per
round (2912 → 6446 → 10554 → 15515 → 30829 → 67989). The OWL 2 RL rules
are sound for any RDF graph, so the input was wrong: `loadImports` merged
each imported RDF/XML graph by plain concatenation, and the parser labels
blank nodes `b0, b1, …` per document, so wine's restrictions and food's
restrictions shared labels — chimera restrictions. The F\* runner hit and
fixed the same defect on 2026-07-10 (`owl_runner.ml`, "Bnode renaming");
the port now applies `Graph.prefixBnodes "imp<n>_"` per import. The list
engine never got past round 1 on these cases, so the defect was invisible
until the engine was fast — the measurement that was supposed to confirm
a speed-up instead found a correctness bug in the harness.

### Module correspondence (append)

| F\* | Lean | Notes |
|---|---|---|
| `RDFS.Closure.SemiNaive.fst` (indexed/semi-naive RDFS closure), `RDF.Indexed` bucket trees | `OWL/RLClosureIndexed.lean` `Store`, `Index`, `stepI`, `closureI`, `indexedClosure`, `detectClashI` | naive rounds over hash buckets, not semi-naive deltas; the bridge is a list equality, not a saturation argument |
| `owl_runner.ml` `load_imports_into_premise` + per-import bnode renaming | `Harness/OwlProbe.lean` `loadImports` with `Graph.prefixBnodes` | same ordinal-prefix discipline |

### Assumption report (append)

No `sorry`, no `axiom`, no `native_decide`, no `partial`, no `@[extern]`
in `RLClosureIndexed.lean`. `Std.HashMap` / `Std.HashSet` from core Lean
only (still zero external dependencies). Not done: semi-naive evaluation
(each round re-derives everything; its bridge would be an equality at
saturation, a different proof) — the corpus does not need it at the 20 s
cap; cls-int1 still enumerates subject OCCURRENCES (`subjectsOf g`, one
per triple) because the row body must stay `rfl`-equal to the list row.

## Stage: SHACL-SPARQL, SHACL Part 2 (branch `lean4/shacl-sparql`, 2026-08-22)

`sh:sparql` constraints (§5.1), the SPARQL-based constraint components
(§6), pre-binding of `$this` / `$value` / `$currentShape` /
`$shapesGraph` / `$PATH` (§5.3), and the §5.3.2 restrictions that make
a query ill-formed — the suite's `sht:Failure` outcome. The port is
`L4Factoidal/SHACL/Sparql.lean` (engine + specification) and
`SHACL/SparqlTheorems.lean` (the two related).

### The pre-binding decision

SHACL §5.3 pre-binds a variable "with the [pre-bound] value" before
evaluation. This port SUBSTITUTES the value into the parsed query —
the concrete `QueryPattern` / `Expr` AST, before `QueryPattern.lower`
turns filter conditions into closures — as the F\* `subst_vars_gp`
does, and as `SPARQL/Exists.lean` substitutes into an EXISTS body. A
one-row `postValues` binding is joined on top, for the projection only.

A post-hoc join alone is not enough, and the suite says so:
`pre-binding-001`'s whole WHERE clause is
`FILTER ($this = ex:InvalidResource)`, so with a join `$this` is
unbound while the FILTER runs and the query yields nothing. `BOUND($v)`
for a pre-bound `$v` becomes `true` (`shapesGraph-001`).

Substitution and pre-binding agree exactly BECAUSE of §5.3.2 —
MINUS (the §18.5 domain-disjointness test reads the RHS variable
domain, which substitution changes), SERVICE and LATERAL (the pattern
is evaluated somewhere the substitution does not reach), VALUES on a
pre-bound variable (a second, conflicting binding source), a
sub-SELECT that does not project the variable (`SELECT *` counts as
not projecting: `pre-binding-006` fails, `-007` passes), and
assignment to a pre-bound variable. Each is a FAILURE, not a best
effort.

### A defect the port fixed, which the F\* still carries

Substituting a term literal into an EXPRESSION position loses the
SPARQL §17.1 numeric promotion the variable route applies:
`Expr.var` promotes a literal binding through `literalPromote`, while
`Expr.lit` does not, so `FILTER($value <= $maxVal)` with two
`xsd:integer` values compared them LEXICALLY — `"5" > "10"`. Found by
a new build-time guard, not by the suite (no vendored fixture compares
a pre-bound number). `termToExpr?` now yields the promoted `Expr`
constructor, and `termToExpr_evalIn_eq_literalPromote` proves the
agreement with `literalPromote`. The F\* `term_to_expr_opt` returns the
un-promoted `E_Literal` and `SPARQL11.Algebra.fst:4013` evaluates it to
`ER_Term (T_Literal l)`, so the F\* tree has the same exposure —
reported, not fixed here.

### Module correspondence (append)

| F\* | Lean 4 | Notes |
|---|---|---|
| §11b `prefix_header_for`, `declares_to_header`, `collect_declares` | `SHACL/Shapes.lean` `prefixHeaderFor`, `declaresToHeader`, `collectDeclares` | §5.2; `owl:imports` between declaration nodes walked cycle-safe (`prefixes-001`) |
| §11b `build_sparql_constraints`, `build_custom_constraints`, `is_custom_component_def`, `parse_custom_param`, `custom_params_applicable`, `choose_validator` | `decodeSparqlConstraints`, `decodeCustomConstraints`, `isCustomComponentDef`, `decodeCustomParam`, `customParamsApplicable`, `chooseValidator` | a component is recognised STRUCTURALLY (a `sh:parameter` plus a validator), not through `rdf:type sh:ConstraintComponent` — `component/validator-001` types it through a user subclass |
| `CC_Sparql` / `CC_Custom` | `Constraint.sparql` / `Constraint.custom` | `.sparql` also carries the constraint node's own `sh:severity` (the F\* re-reads it from the raw shapes graph at evaluation time) |
| §11k `subst_var_ps` / `_pt` / `_tp` / `_expr` / `_gp`, `subst_vars_gp` | `substVarSubject`, `substVarTerm`, `substVarTP`, `substVarExpr`, `substVarPattern`, `substVarsPattern` | structural mutual recursion, no fuel; `.subSelect` matched open (`.mk f d p …`) so the recursive argument stays a visible subterm |
| §11k `term_to_expr_opt` | `termToExpr?` | DIVERGES: promotes numeric / boolean literals — see the defect note above |
| §11k `prebinding_unsupported`, `si_projects_this`, `si_assigns_prebound` | `prebindingUnsupported`, `selectItemProjectsThis`, `selectItemAssignsPrebound`, `queryPrebindingUnsupported` | same five rejections, same messages |
| §11k `path_to_sparql_expr` / `_atom` / `path_list_to_sparql`, `substitute_path` | `pathToSparql`, `pathToSparqlAtom`, `pathListToSparql`, `substitutePath` | the one spec-sanctioned TEXTUAL substitution (§5.3.1 `$PATH`) |
| §11k `shacl_internal_shapes_graph_iri`, `sparql_violations_for_focus` / `_all` / `_foci` / `_shape` / `_shapes` | `shaclInternalShapesGraphIri`, `sparqlViolationsForFocus`, `sparqlViolationsForShape`, `SparqlOutcome.concat` | the `(list violation & option string)` pair becomes the `SparqlOutcome` record with `append` / `concat` |
| §11l `eval_custom_component_ask` / `_ask_values` / `_select`, `eval_one_custom_component`, `custom_violations_for_occurrence` / `_foci` / `_shape` / `_shapes` | `customAskViolation`, `customSelectViolations`, `evalCustomComponent`, `customViolationsForOccurrence`, `customViolationsForShape` | §6.2.1 per value node, §6.2.2 per focus node; the component pass walks `sh:property` (`propertyValidator-select-001`, `unsupported-sparql-006`), the `sh:sparql` pass does not — the same slice the F\* takes |
| §11l `fill_message_template`, `fill_tmpl_chars`, `split_at_close_brace`, `term_to_plain_string` | `fillMessageTemplate`, `fillTemplateChars`, `splitAtCloseBrace`, `termToPlainString` | §6.3 `{?name}` / `{$name}` |
| §13 `validate` with `report_failure` | `validateWithSparql`, `ValidationReport.failure` | `validate` stays SHACL Core and sees `.sparql` / `.custom` as inert |
| `assume val eval_sparql_target_select` | — | a module-ordering artefact in F\*; SHACL imports SPARQL here. `sh:target [ sh:select … ]` (SHACL-AF) is still the one entry of `sparqlFeaturePredicates`, reported `unsupported` |

### What the specification covers, and what it does not

`Spec.Conforms` is NOT extended with the new components, and cannot
be: `conformance_iff` is an `iff` against `collectShapeViolations`,
which by design never evaluates a `.sparql` or `.custom` constraint
(it returns `List Violation` with no room for the §5.3.2 failure
channel — the same reason the F\* dispatches these outside its Core
mutual group). A non-trivial `FocusSatisfies` clause for them would
make `conformance_iff` FALSE. So the SHACL-SPARQL specification is a
SIBLING relation: `Spec.SparqlSatisfies`, `Spec.AskValidatorSatisfies`,
`Spec.SelectValidatorSatisfies`, `Spec.CustomSatisfies`,
`Spec.CustomOccurrenceConforms`, `Spec.SparqlShapeConforms`, and the
conjunction `Spec.GraphConformsWithSparql`.

Proved (all `#print axioms` = `propext`, `Classical.choice`,
`Quot.sound`): `termToExpr_evalIn_eq_literalPromote`,
`substVarExpr_var_evalIn`, `withPreboundQuery_error`,
`sparqlViolationsForFocus_eq_nil_iff`, `customAskViolation_eq_nil_iff`,
`customSelectViolations_eq_nil_iff`,
`SparqlOutcome.concat_results_eq_nil_iff`,
`evalCustomComponent_eq_nil_iff`, `validateWithSparql_conforms_iff`,
`validateWithSparql_sound_core`.

Not proved: the quantifier push from "the shape-level pass produced no
result" down to `Spec.SparqlShapeConforms` /
`Spec.CustomOccurrenceConforms` (a routine `SparqlOutcome.concat` /
`List.flatMap` decomposition over the focus-node and constraint
lists). `validateWithSparql_conforms_iff` therefore states the two
SHACL-SPARQL conjuncts as pass emptiness, not as the `Spec` relations.

### Sabotage check (2026-08-22)

`sparqlPrebindings` renamed `"this"` to a name no query uses. The build
FAILED at four named guards — `ShaclTests.lean:312` (`.conforms`),
`:313` (`.results.length`), `:314` (`.focus`), `:318` (`.value`), all
on `prebindFilterDoc` — and `lake exe l4shacl` on the sparql manifest
dropped from 22 pass, 0 fail to **11 pass, 11 fail (out of 22)**:
`sparql/node` 0 pass, 4 fail; `sparql/property` 0 pass, 1 fail;
`sparql/pre-binding` 8 pass, 6 fail. `sparql/component` stayed at
3 pass, 0 fail, because a constraint component pre-binds through
`customPrebindings`, a different list. Restored with
`git checkout -- L4Factoidal/SHACL/Sparql.lean`; both suites green
again.

### Measured (verbatim, 2026-08-22)

```
shacl-sparql sparql/component: 3 pass, 0 fail, 0 skip, 0 unsupported (out of 3)
shacl-sparql sparql/node: 4 pass, 0 fail, 0 skip, 0 unsupported (out of 4)
shacl-sparql sparql/property: 1 pass, 0 fail, 0 skip, 0 unsupported (out of 1)
shacl-sparql sparql/pre-binding: 14 pass, 0 fail, 0 skip, 0 unsupported (out of 14)
shacl-sparql TOTAL: 22 pass, 0 fail, 0 skip, 0 unsupported (out of 22)
shacl-core TOTAL: 98 pass, 0 fail, 0 skip, 0 unsupported (out of 98)
```

The suite's own `sparql/component/manifest.ttl` includes only three of
the four fixture files in that directory — `nodeValidator-001.ttl` is
not referenced, so the shacl-sparql denominator is 22, not 23. Run
directly, `nodeValidator-001` produces the expected non-conformance.

### Assumption report (append)

No `sorry`, no `axiom`, no `native_decide`, no `partial`, no
`@[extern]` in `SHACL/Sparql.lean` or `SHACL/SparqlTheorems.lean`.
Still zero external dependencies. Not done: SPARQL-based targets
(`sh:target`, SHACL-AF); `sh:sparql` on a shape reached only through
`sh:property` (root shapes only, as the F\*); the two unproved
decompositions named above.
### OWL tableau: qualified cardinality (2026-08-22, fourth rung)

`atLeastQ` / `atMostQ` join `Concept` with their OWL 2 Direct
Semantics reading, and three clash rules follow: `minMaxClashQ`
(qualified twin of the count clash), `maxClashQ` (n+1 named
successors that are pairwise-distinct AND provably in the qualifying
class), and `minQMaxClash` — the bridge letting a qualified minimum
clash with an UNQUALIFIED maximum, since qualified successors are
still successors. The witness list is inlined into `Interp.sem`
rather than factored into a `succWitnessQ` helper, so the recursive
`I.sem c y` stays visibly structural in `c` for the termination
checker. Motivation is concrete: this is the concept form the
unsupported W3C SPARQL entailment-regime tests use (`hasChild min 1
Female`, `max 1 Female`, `exactly 1 Female`) — see the parity ledger
in docs/designissues/2026-08-22-lean-fstar-parity-ledger.md. Axiom
base unchanged.

### OWL tableau: the SHIQ ≤-rule witness merge (2026-08-22, fifth rung)

`leqMerge` closes the core SHIQ clash calculus. It is the first rule
that REWRITES the ABox (`mergeInds` renames one individual to
another) rather than extending it, and it branches over PAIRS of named
successors the way `disjSplit` branches over disjuncts. Soundness is
the pigeonhole argument, machine-checked: `n+1` distinctly-named
`r`-successors cannot all denote different elements when `≤n r` holds,
so some pair collides in every model, and the merged ABox that pair
licenses is already refuted. Supporting lemmas, all new:
`satisfies_subst` (a rename is invisible to a model that already
identifies the two names), `satAll_mergeInds`, and
`pairwise_map_ne_of_injOn` (the positive half of the pigeonhole; the
existence half comes from a classical `by_cases` on whether any pair
collides). Axiom base unchanged. The `by decide`-in-certificate trap
from rung 3 recurred here and cost a build: use explicit `Mem` chains
inside `Refuted` terms, including into a `mergeInds`-rewritten ABox
where the list is a `List.map` rather than a literal.

### GeoSPARQL: geometry model and bounding boxes (2026-08-22)

First rung of a spec family the Lean tree had never touched, chosen off
the parity ledger: `formal/fstar/RDF.Geo.*` has 4 modules and 37 W3C
tests, and is self-contained. `Geo/Types.lean` ports the geometry model
and `Geo/BBox.lean` the bounding boxes.

Coordinates are EXACT decimals (`Scaled` = mantissa + decimal scale),
not floats — the same choice the F* side made, and for the same
reason: topology predicates compare coordinates for equality, so float
rounding would make `sfEquals` depend on how the literal was parsed.
`#guard` pins `0.1 + 0.2 = 0.3` exactly.

Two Lean-specific notes. (1) `BBox.ofGeometry` recurses through
`geometryCollection`; a `foldl` over the sublist hides that recursion
from the termination checker, so `ofGeometry`/`ofGeometries` are
declared `mutual` with explicit list recursion. A doc comment may not
precede `mutual` — it attaches to the first `def` inside. (2) A
`#guard` caught a wrong arithmetic assertion in the test file itself
(0.5 × 0.2 written as 1 rather than 0.1) at build time, which is the
build-time-checking discipline paying for itself in the first hour of
a new area.

Deliberately NOT stated yet: `disjoint_bbox_no_shared_point`, the
soundness of using the box test as a pre-filter before the topology
predicates. It needs transitivity of `Scaled.le`, which needs a
rescaling-invariance lemma because pairwise `align` calls in a
three-way chain use different common scales. The obligation is written
into `BBox.lean` and NO code takes the disjoint-box shortcut until it
is discharged.

### GeoSPARQL: Scaled is a linear order; the box pre-filter is sound
(2026-08-22, same day as the model)

`Geo/Order.lean` discharges the obligation `BBox.lean` had named.
`disjoint_bbox_no_shared_point` — two non-overlapping boxes share no
point — is now proved, so the disjoint-box shortcut in front of the
topology predicates is safe to take.

The proof that mattered is `Scaled.le_trans`. It is not immediate
because `cmp` aligns ITS TWO arguments at THEIR common scale, so a
chain `a ≤ b ≤ c` involves three different alignment scales. The fix
is rescaling invariance (`le_at'_shift`): comparing at any scale that
dominates both operands gives the same verdict, after which
transitivity is integer transitivity at one shared scale.

Three core-Lean lessons, all paid for here:
1. **Inside `namespace Scaled`, bare `max` resolves to `Scaled.max`**
   and silently mis-typechecks against `Nat` scales. Write `Nat.max`.
   (`align` in Types.lean is safe only because `Scaled.max` is
   declared after it.)
2. **No mathlib means no `push_cast`, no `ring`, no `split_ifs`.**
   Use `Int.natCast_mul` + `Int.mul_assoc` by hand; probe unfamiliar
   core lemma names with a scratch file through `lake env lean`
   before writing the proof around them.
3. **`omega` refuses nonlinear atoms** like `mantissa * 10^k`.
   `generalize` the products to fresh variables first; the remaining
   if-chain reasoning is then linear and `omega` closes it.

### GeoSPARQL: the exact geometric kernel (2026-08-22)

`Geo/Topology.lean` ports the predicate kernel from
`RDF.Geo.Topology.fst`: orientation determinant, exact
point-on-segment, four-orientation segment intersection, path
crossing, ray-cast crossing parity, and point classification against
rings and holed polygons, then the Simple Features point-vs-polygon
predicates (`sfEquals`, `sfDisjoint`, `sfIntersects`, `sfWithin`,
`sfTouches`).

Everything is DIVISION-FREE by design, inherited from the F* module:
computing an actual intersection coordinate would need division and
would leave the exact-decimal world, so every test is phrased with the
orientation sign instead. The ray-cast likewise decides "crosses to
the right" from the orientation sign rather than an x-coordinate.

Simple Features conventions pinned by `#guard`: a boundary point
INTERSECTS but is not WITHIN; touching at an endpoint counts as
segment intersection; a hole returns an otherwise-interior point to
exterior. Caller-side assumption carried over verbatim: ray-casting is
meaningful only for SIMPLE rings — segment intersection needs no such
assumption.

### GeoSPARQL: WKT parsing and decimal rendering (2026-08-22)

`Geo/Wkt.lean` ports `Parser.WKT.fst`: the Simple Features WKT
grammar behind `geo:wktLiteral`, with the optional `<IRI>` CRS prefix,
all seven geometry tags, `EMPTY` forms, nested
`GEOMETRYCOLLECTION`, and case-insensitive tags. Numbers parse to
EXACT decimals, so `POINT(0.1 0.2)` compares equal to `⟨10,2⟩,⟨20,2⟩`
— the whole reason the Geo port exists.

Lean-side difference worth recording: the F* parser threads an
explicit FUEL parameter because its input is a string with an index.
This port works on `List Char`, so every production except the two
genuinely recursive ones (comma lists, collections) is structurally
decreasing and needs no fuel; the recursive pair is `partial` and
`geometry`/`geometryList` must be declared `mutual`.

Guards pin what a parser gets wrong quietly: trailing junk, a
one-coordinate point, an unknown tag, an unclosed paren and the empty
string must all FAIL rather than partially parse. `Scaled.toStringDec`
renders the exact value back (`-0.1`, `0.001`), and a parsed polygon
feeds `pointWithinPolygon` directly, so parse and topology are wired
end to end.

### GeoSPARQL: the geof: extension functions (2026-08-22)

`Geo/Functions.lean` ports `RDF.Geo.Functions.fst` and completes the
GeoSPARQL slice: `sfEquals`, `sfWithin`, `sfContains`, `sfIntersects`,
`sfDisjoint`, `sfTouches` over the point/polygon fragment.

It required ZERO change to the SPARQL evaluator. GeoSPARQL 1.1 §9
names its predicates as SPARQL functions, SPARQL §17.6 already defines
an extension point, and the Lean evaluator exposes that point as an
ordinary field — `EvalEnv.ext : String → List EvalResult → Option
EvalResult`. A caller installs the table with
`{ EvalEnv.empty with ext := Geo.extFns }`. This is the purity
doctrine (PORT_NOTES §"Purity doctrine") paying off concretely: where
the F* side consults a registry the evaluator knows about, here the
table is an argument, so a whole spec family bolts on without
touching the evaluator or mutating anything global.

Guards pin the failure direction, which is the part that silently
corrupts answers if wrong: an unknown `geof:` name, a non-WKT
argument, wrong arity, an unparseable lexical form, and a CROSS-CRS
pair must each return `none` so the evaluator raises the §17.6 type
error — never `false`, which would look like a legitimate negative
answer. The no-CRS-transform rule is inherited from the F* port
verbatim.

### GeoSPARQL: three-valued predicates over all geometry kinds
(2026-08-22, completing the family)

The point-vs-polygon fragment is now the general dispatch. Added:
`segmentSubsegOf`/`pathWithinPath` (line-in-line),
`linestringEquals`, `lineIntersectsPolygon`, the `sf*Base` tables for
Point/LineString/Polygon/Empty, `sfTouchesBase`, and the
`Multi*`/`GeometryCollection` decomposition.

The design property that mattered to port faithfully is the F* module's
`option bool`: where the ported algorithm is INCOMPLETE it REFUSES
(`none`) instead of answering. Two named cases: a path covered by two
or more collinear outer edges across a bend, and two closed loops of
equal length listed from different starting vertices. Answering
`false` there would be indistinguishable from a real negative answer
to a user's query, which is the failure mode this whole three-valued
shape exists to prevent. `Geo/Functions.lean` maps a refusal to the
SPARQL §17.6 TYPE ERROR, so the evaluator raises rather than reports.

Decomposition combinators are Kleene three-valued: `combineExists`
returns `some true` on one witness even when siblings refused (a
witness settles an existential), but `some false` only when EVERY
component definitely said false. `combineForall` is the dual. Getting
this backwards would convert refusals into confident wrong answers at
exactly the point where compound geometries meet partial algorithms.

### CSVW: dialect description and the CSV reader (2026-08-22)

Opens the largest self-contained family still absent from the Lean
tree (F* CSVW is 5,283 lines across 6 modules, 270 W3C tests).
`CSVW/Dialect.lean` ports `csvw_dialect` from `CSVW.Metadata.fst` plus
the row reader it drives: quoting with doubled-quote escaping,
CRLF/LF/CR line endings, comment prefixes, row and column skipping,
blank-row handling, and the four trim modes.

Design point carried over deliberately: EVERY dialect property stays
`Option` in the description, and defaults are applied only at read
time in `Dialect.resolve`. Collapsing absent into the default earlier
would destroy the distinction the metadata inheritance rules depend
on — "not stated here, inherit from the parent" is not the same fact
as "stated to be the default value".

Two spec corners the guards pin because they are easy to get
backwards: `header: false` means zero header rows UNLESS
`headerRowCount` says otherwise (both properties interact, and
`headerRowCount` wins), and an explicitly EMPTY `quoteChar` means "no
quoting at all" rather than "use the default quote". Row numbers are
SOURCE line numbers and must survive skipping, because `csvw:rownum`
and every error report reference them.

### CSVW: URI template expansion (2026-08-22)

`CSVW/UriTemplate.lean` ports `CSVW.URITemplate.fst` — the RFC 6570
subset CSVW actually uses: level-1 `{var}` and level-2 `{#var}`. No
query form, path segments, lists, or modifiers, matching the F*
module's deliberate scope.

Ported WITH its war story, as a regression guard: RFC 6570 §3.2.4
prefixes a DEFINED `{#var}` expansion with a literal `'#'`, while an
UNDEFINED one produces no output at all. Dropping that prefix made
`countries.csv{#countryCode}` expand to `countries.csvAD` instead of
`countries.csv#AD`, silently breaking every aboutUrl/valueUrl
fragment template in the csv2rdf corpus. The guard pins both halves —
the '#' appears when the variable is defined and does NOT appear when
it is not.

CSVW's `_row`/`_sourceRow`/`_name` variables need no special handling
here; they resolve through the caller's lookup like any column name,
which keeps this module free of CSVW knowledge.

### CSVW: the metadata model and §5.1.1 inheritance (2026-08-22)

`CSVW/Metadata.lean` ports the datatype, column, schema, table and
table-group records plus the inherited-property chain. Scope stated as
the F* module states it: ten of the eleven inherited properties
(everything but `textDirection`) — a slice, not a completeness claim.

`Inherited.override` is why every field in this family stays `Option`.
`none` means INHERIT, and the group → table → schema → column chain
resolves it. A field defaulted early would shadow the parent value it
was meant to inherit, which is a silent wrong answer rather than a
crash. The guards walk the whole chain: a column override wins, a
schema value reaches the column, and with neither, the group's value
arrives.

Naming note with a reason: the metadata table record is `TableDesc`,
because `Table` already names the reader's PARSED CONTENT in
`Dialect.lean`. Metadata about a table and the rows read from one are
different things, and letting one name cover both would be a real
bug waiting to happen, not a style nit.

§5.6 column-name derivation is pinned in full, since its fallback
order is easy to shorten by accident: explicit `name`, then a title
tagged with the requested language, then an untagged title, then the
positional `_col.N` the spec mandates.

### CSVW: csv2rdf cell conversion (2026-08-22)

`CSVW/Conversion.lean` ports the cell-level half of
`CSVW.Conversion.fst`: the row-scoped variable lookup (`_row`,
`_sourceRow`, column names), `null` and `default` handling, the
`separator` list split, the §6.4.2 whitespace rule, and
aboutUrl/propertyUrl/valueUrl template resolution.

Three rules pinned because each is a silent-wrong-answer if flipped:

1. **The whitespace rule is per-datatype-base.** Only the string
   family and the structured literals (xml/html/json) preserve
   surrounding whitespace; every other base strips it before lexical
   parsing. That is what lets a `date` cell parse THROUGH its padding
   (`" 10/18/2010 "` → `2010-10-18`) while a `string` cell keeps it.
   An absent datatype defaults to string, so it preserves too.
2. **An empty cell with a `separator` yields NO elements**, not one
   empty element — the difference between zero triples and one triple
   with an empty object.
3. **A null cell still reports its property.** Standard-mode
   `csvw:describes` bookkeeping needs the subject and predicate even
   when no value triple is produced, so `convertCell` returns them
   alongside an empty object list rather than returning nothing.

Template resolution context carried from the F* module: aboutUrl /
propertyUrl / valueUrl resolve against the CURRENT TABLE's own
already-resolved URL, never against the document base a second time.

### CSVW: triple emission, minimal and standard modes (2026-08-22)

`CSVW/Emit.lean` closes the csv2rdf pipeline: converted cells become
RDF triples. BOTH modes are here — minimal (cell triples only) and
standard (plus `csvw:describes`, `csvw:rownum`, `csvw:url` row
scaffolding) — because the W3C manifest tests each mode separately,
and porting only one would score half the suite while looking done.

`typedLiteral` is the interesting piece. `literalWf` forbids
`rdf:langString`/`rdf:dirLangString` on an untagged literal, and a
datatype arriving from metadata could be either, so the obligation
cannot be discharged statically. Rather than admit it, the
constructor CHECKS and falls back to a plain string literal. Under the
no-`sorry` policy an unprovable obligation is not a reason to weaken
the policy — it is a signal that the function needs a runtime guard.

Rules the guards pin: a cell whose predicate does not resolve to a
valid IRI emits NOTHING rather than a malformed term, and does not
stop its siblings; a language tag beats a datatype (RDF 1.1 makes any
tagged literal `rdf:langString`); a `separator` cell emits one triple
per element sharing subject and predicate; and `valueUrl` produces an
IRI object rather than a literal.

### CSVW: value formats — booleans and numbers (2026-08-22)

`CSVW/Formats.lean` ports the boolean and numeric halves of
`CSVW.Formats.fst`. SCOPE IS STATED IN THE MODULE, not implied: date
/time patterns and the regex-valued duration `format` facet are not
here yet (the latter needs the XSD regex engine).

The three-way `FmtOutcome` is the reason that scope gap is safe.
`noFormat` ("no format applied, keep the cell") is a DIFFERENT
outcome from `invalid` ("a format was applied and the cell failed
it"). An unported format returns `noFormat`, so a format this port
cannot yet read never rejects a value it might have accepted.
Collapsing the two would turn every unported format into a spurious
validation failure — the conservative direction is not an accident,
it is the design.

Two rules the guards pin: a boolean `format` with NO `|` is
MALFORMED and rejects everything rather than falling back to the XSD
`true`/`1` space; and percent / per-mille scaling is done by shifting
the DIGIT STRING, not by float arithmetic, so `12.5%` is exactly
`0.125`.

### CSVW: csv2json output (2026-08-22)

`CSVW/Json.lean` ports `CSVW.Json.fst` — minimal and standard csv2json
modes. Kept as its OWN output rather than a rendering of the triples:
csv2json is a separate conformance suite and its shapes differ
(`describes` arrays, `rownum`/`url` members, `rdfs:comment`), so
deriving one from the other would lose exactly the distinctions the
tests check.

Three shape rules the guards pin, each an "absent vs empty"
distinction that is easy to get wrong and impossible to see in a
diff of passing counts:

1. A NULL cell contributes NO MEMBER, rather than a member with JSON
   `null`.
2. A `separator` column is ALWAYS an array, even with one element —
   the list-ness comes from the metadata, not from the cell content.
3. An empty comment list produces NO `rdfs:comment` member: csv2json
   says verbatim "If M.rdfs:comment is an empty array, remove the
   rdfs:comment property from M", so emitting `[]` is wrong output,
   not harmless output.

### CSVW: metadata validation and the error/warning line (2026-08-22)

`CSVW/Validate.lean` ports `CSVW.Validate.fst`, completing the main
CSVW module set (Dialect, Metadata, UriTemplate, Conversion, Emit,
Formats, Json, Validate).

The module exists to preserve ONE distinction. The W3C csvw suite has
two kinds of negative test: a `ValidationTest` must produce an ERROR,
a `WarningValidationTest` must produce a WARNING and still convert. A
port that flagged warnings as errors would fail every warning test
while looking stricter and more correct — the failure mode where being
wrong looks like being careful. Severity is therefore part of the
`Finding`, not a caller's interpretation, and `passes` ignores
warnings by construction.

Two rules carried with their classification, because both are exactly
what a later reader would "fix" into a bug:
- A datatype string that is not a built-in NAME is a WARNING, never a
  rejection (the suite classifies both the non-builtin and the
  absolute-URL case as `WarningValidationTest`).
- A NON-STRING `@id` is graceful degradation, not an error, so it is
  deliberately not flagged; only a blank-node `@id` is an error.

### ShEx: schema AST and node constraints (2026-08-22)

Opens the family with the largest test count still absent (1,182 W3C
tests; F* side is 3,053 lines across 3 modules). `ShEx/Schema.lean`
ports the mutually recursive shapeExpr/tripleExpr AST;
`ShEx/Validation.lean` ports §5.4 node-constraint satisfaction.

Three details carried deliberately:

1. **Numeric facets keep their verbatim JSON lexeme** as a `String`,
   as in the F* module. Parsing them early would fix a precision
   decision before the governing datatype is known, and ShEx compares
   them against the node's own lexical value. `compareDecimal`
   therefore compares two decimal STRINGS exactly — pad to common
   widths, then one lexicographic pass — so no float ever exists to
   round.
2. **Length facets count CHARACTERS, not bytes.** A guard pins `é`
   as length 1.
3. **An absent language or datatype in an ObjectValue means
   UNCONSTRAINED**, not "must be absent" — the opposite reading
   silently rejects every tagged literal.

Lean-specific: `extends` is a KEYWORD, so `Shape`'s field is
`extendsRefs`. The mutually recursive records had to become
inductives with hand-written accessors, since a Lean `structure`
cannot join a `mutual` block containing inductives.

NOT ported yet: shape satisfaction proper — triple expressions,
cardinality matching over neighbourhoods, EXTRA and CLOSED — which is
where the recursion through shape references lives.

### ShEx: shape satisfaction, EXTRA vs CLOSED (2026-08-22)

`ShEx/Shapes.lean` ports `satisfies(n, Shape, G)`: neighbourhood
construction, triple-expression matching with cardinality, and the
two clauses that follow it.

The module exists to keep ONE distinction straight, which the F*
module records as an actual bug caught during its own measurement run:

* `extra p` tolerates LEFTOVER arcs on predicate `p` — ones the
  constraint could not take because its [min,max] was full or its
  valueExpr failed — REGARDLESS of `closed`.
* `closed` bounds only arcs whose predicate the expression NEVER
  MENTIONS. It never relaxes a mentioned predicate's own cardinality.

Conflating them — letting "not closed" also grant a mentioned
predicate's leftover tolerance — is the bug. The two are computed in
separate steps here that never share a branch, and a guard pins the
exact case that distinguishes them: an OPEN shape with a failing
leftover arc on a mentioned predicate must FAIL without `extra`, and
pass with it.

Scope stated, not implied: no backtracking for ambiguous `OneOf`
siblings sharing a predicate (first satisfied branch wins), and no
recursion through shape references — an unresolved `ref` makes an arc
leftover rather than being silently accepted, which is the
fail-closed direction.

### RML: mapping model and term generation (2026-08-22)

`RML/Mapping.lean` ports the term-map core of `RML.Mapping.fst` /
`RML.Eval.fst`: constant / reference / template forms, templates with
RML's backslash escaping, the term types, and term generation from a
data record.

Two details carried with their reasons:

1. **`rml:IRI` and `rml:URI` are NOT synonyms.** `rml:URI` applies
   URI-safe (RFC 3986, ASCII-only) percent-encoding; `rml:IRI`
   applies IRI-safe (RFC 3987) encoding where most non-ASCII stays as
   itself. `"Zoë"` becomes `"Zo%C3%AB"` under one and stays `"Zoë"`
   under the other. The F* module records this as a CORRECTION to an
   earlier "legacy synonym" reading, so the distinction is carried
   here with a guard on exactly that string.
2. **An unresolved reference generates NO TERM**, and an absent field
   makes the WHOLE template produce nothing — not an empty string.
   Emitting `http://ex/` for a missing id would be a valid-looking
   IRI pointing at the wrong thing.

RML templates escape braces with a backslash; the CSVW RFC 6570
templates deliberately do NOT. The two look similar enough to merge
and must not be — noted in both modules.

### RIF Core: syntax and forward chaining (2026-08-22)

`RIF/Core.lean` ports the AST from `RIF.Core.Syntax.fst` and the
forward chain from `RIF.Core.Eval.fst`: terms, atoms (triple / frame /
member / sub / uniterm), bodies, rules, substitutions with
join-consistent extension, and closure to a fixed point.

The bound is REPORTED, not absorbed. `closure` returns the facts AND
whether the round bound was reached, because RIF Core with external
builtins can generate ground terms indefinitely, and a caller that
reports entailment from a truncated closure is reporting a guess. A
guard pins both directions: the ancestor program terminates before
the bound with the flag false, and hits it with the flag true when
given too few rounds.

Two fail-closed choices carried from the F* module: an unevaluated
`external` grounds to NOTHING rather than a placeholder, and a head
whose predicate does not ground to an IRI (or whose subject is a
literal) produces no triple rather than a malformed one.

Relevance beyond RIF itself: 4 of the 30 SPARQL entailment-regime
tests the Lean tree currently reports UNSUPPORTED are RIF-regime
tests (see the parity ledger), so this is a step toward those as well
as toward the rif-core suite.
---

## Stage: the RDF 1.2 W3C suites run (branch `lean4/rdf12`, 2026-08-22)

`lake exe l4w3c` now scores the `rdf12/` manifests. The full write-up
— how the version is selected, the sabotage record, the findings — is
in
[`docs/designissues/2026-08-22-lean4-w3c-harness.md`](../../docs/designissues/2026-08-22-lean4-w3c-harness.md)
§ "Status 2026-08-22 — the RDF 1.2 suites run"; what follows is the
F\*↔Lean ledger for it.

### Measured (verbatim)

```
rdf-n-triples/syntax: 29 pass, 0 fail, 0 skip, 0 unsupported (out of 29)
rdf-n-quads/syntax: 27 pass, 0 fail, 0 skip, 0 unsupported (out of 27)
rdf-turtle/syntax: 67 pass, 0 fail, 0 skip, 0 unsupported (out of 67)
rdf-turtle/eval: 29 pass, 0 fail, 0 skip, 0 unsupported (out of 29)
rdf-trig/syntax: 35 pass, 0 fail, 0 skip, 0 unsupported (out of 35)
rdf-trig/eval: 25 pass, 0 fail, 0 skip, 0 unsupported (out of 25)
rdf-xml/eval: 30 pass, 0 fail, 0 skip, 0 unsupported (out of 30)
rdf-n-triples/c14n: 41 pass, 0 fail, 0 skip, 0 unsupported (out of 41)
rdf-n-quads/c14n: 41 pass, 0 fail, 0 skip, 0 unsupported (out of 41)
rdf-semantics: 0 pass, 0 fail, 0 skip, 0 unsupported (out of 0)
  (manifest did NOT parse: manifest parse error at offset 9732: undefined prefix: test)
TOTAL: 324 pass, 0 fail, 0 skip, 0 unsupported (out of 324)
```

The F\* runner scores 242 (`--rdf12`) + 82 (`--rdf12c14n`) = 324 pass,
0 fail on the same nine manifests, suite for suite. It also scores
`rdf-semantics` at 41 pass, 3 fail, 3 skip (out of 47), which this tree
cannot yet reach — see the module-correspondence row for
`read_manifest`.

Regression gates on the same build: the seven RDF 1.1 suites at
`TOTAL: 1117 pass, 0 fail, 0 skip, 0 unsupported (out of 1117)` and
sparql11 `manifest-all.ttl` at `TOTAL: 601 pass, 0 fail, 0 skip, 30
unsupported (out of 631)`.

### Module correspondence (append)

| F\* | Lean | Notes |
|---|---|---|
| `w3c_runner.ml` `--rdf` / `--rdf12` / `--rdf12c14n` / `--rdf12entail` CLI flags | `Harness/Main.lean` `modeOfManifest` + the `mode : Mode` parameter of `Harness/Run.lean` `runTest` | the F\* selects the version per RUN, this tree per MANIFEST (off `mf:assumedTestBase`, falling back to the path), because `l4w3c` takes manifest paths and one invocation may mix the trees |
| `run_rdf12_test`'s `TestNTriplesPositiveC14N` / `TestNQuadsPositiveC14N` arms | `Harness/Run.lean`, the contiguous "RDF 1.2 canonical N-Triples / N-Quads" block | byte comparison against the `-c14n.{nt,nq}` oracle, no newline trimming, as in the F\* `actual = expected` |
| `RDF.NQuads.Serialize.fst` `canon_hex_upper`, `canon_byte_uchar`, `nq_canon_special_byte`, `nq_canon_escape_byte`, `nq_canon_walk`, `nq_canon_term`, `nq_canon_line_default`, `canonical_nt_document` | `Syntax/NTriples.lean` `canonHexUpper`, `canonUchar2`, `canonEscapeChar`, `canonEscapeLiteral`, `Term.toCanonicalNTriples`, `Triple.toCanonicalNTriples`, `Graph.toCanonicalNTriples` | the F\* walks UTF-8 BYTES, this walks CHARACTERS; equivalent because every escaped byte is < 0x80 and the U+FFFE/U+FFFF byte triples are exactly those codepoints |
| `nq_canon_line_graph`, `canon_nq_named_lines`, `canon_nq_named`, `canonical_nq_document` | `Syntax/NQuads.lean` `canonNamedLine`, `Dataset.toCanonicalNQuads` | the F\* graph name is a `string` (always `<iri>`); `NamedGraph.name` here is a `Subject`, so a blank-node graph label round-trips as `_:label` |
| `Parser.NTriples.fst` `parse_literal_12`, `parse_datatype_ws_12` | `Syntax/NTriples.lean` `readLiteral` (the `.rdf12` whitespace look-ahead) and `readDatatypeWs12` | the run is consumed only when a `@` or `^^` really follows, so a plain `xsd:string` literal leaves it for the triple parser |
| `Parser.RDFXML.fst` `extract_version`, `extract_dir`, `effective_dir`, `is_rdf_syntax_attr`'s three 1.2 names | `Syntax/RdfXml.lean` `updateVersion`, `updateDir`, `St.effectiveDir`, `rdfSyntaxAttrNames` (+`version`, `annotation`, `annotationNodeID`) | `St.dir` / `St.sawVersion12` are XML-scoped, restored for siblings by `restoreScope` exactly as the F\* `restore_scope` does |
| `Parser.RDFXML.fst` the `Some "Triple"` arm of `process_property_element` | `Syntax/RdfXml.lean` `propertyEltBody`'s `some "Triple"` arm | same version gate, same "exactly one element child making exactly one triple, else a syntax error" |
| `Parser.RDFXML.fst` `annot_reifier_opt` / `annot_of` / `reif_of` | `Syntax/RdfXml.lean` `annotReifier`, `annotTriples`, `reifyAll` | the F\* uses an `rdf:annotationNodeID` value verbatim as a blank-node label; this port sends it through `nodeIdLabel`, the same map `rdf:nodeID` uses, so the two attributes name the same node |
| `make_plain_literal lex lang dir` | `Syntax/RdfXml.lean` `mkPlainLiteral` (+ `RDF/Core.lean` `Literal.dirLangString`) | a direction with no language tag is ill-formed under `literalWf`, so it is dropped rather than made unrepresentable |
| `w3c_runner.ml` `read_manifest`'s LENIENT-WITH-REPORT manifest parse (issue #334) | `Harness/Manifest.lean` `parseTurtleRecover` / `parseManifestTextLenient` (2026-08-25) | until 2026-08-25 the Lean side parsed strictly and the `rdf12/rdf-semantics` manifest's undeclared `test:` prefix zeroed that one suite (`0 out of 0`, `no_manifest=1`) — the zero-test-pressure mechanism of [issue 602](https://github.com/danbri/factoidal/issues/602); now recovered with a printed `MANIFEST-RECOVERY` warning per undeclared prefix, first score 19 pass, 11 fail, 0 skip, 17 unsupported (out of 47) |

### Assumption report (append)

No `sorry`, no `axiom`, no `native_decide`, no `partial` in anything
this stage touched (`Syntax/NTriples.lean`, `Syntax/NQuads.lean`,
`Syntax/RdfXml.lean`, `Syntax/RdfXmlTheorems.lean`, `RDF/Core.lean`,
`Harness/Common.lean`, `Harness/Run.lean`, `Harness/Main.lean`). The
canonical serialisers are total: canonical form IS RDF 1.2, so unlike
`Term.toNTriples` they take no mode and have no failure case.
`Literal.dirLangString`'s well-formedness witness is `rfl` — the third
clause of `literalWf` does not scrutinise WHICH direction it is.

55 new `#guard`s: 26 in `Syntax/TurtleTests.lean` (one per RDF 1.2
Turtle/TriG production, each with its RDF 1.1 rejection), 16 in
`Syntax/SyntaxTests.lean` (canonical form and the whitespace
relaxation), 13 in `Syntax/RdfXmlTests.lean` (the four RDF/XML
additions).

### Not ported (and said so)

* A lenient manifest reader. The F\* has one and needs it for exactly
  one vendored file; this tree keeps the strict parse and reports the
  loss in the score line.
* The RDF 1.2 entailment regimes. `rdf12/rdf-semantics` names
  `RDFS-Plus`, which `RDF/Entailment.lean` has no counterpart for; the
  manifest does not load anyway.
* `sparql12`. The F\* runner has a `--sparql12` mode; nothing here
  reads those manifests yet.

### Findings against the F\* (not fixed here)

* **`Parser.NTriples.fst:514`, `parse_lang_tag`.** RDF 1.1 mode takes
  the maximal run of language-tag characters with no BCP47 subtag
  check, so `"chat"@en--ltr` parses as ONE tag, `en--ltr`, with an
  empty subtag. The RDF 1.2 path applies `valid_lang_subtags`
  (line 1176); the 1.1 path does not, and `readLangTag` here inherits
  it. An RDF 1.1 document therefore changes meaning if re-serialised
  in RDF 1.2 mode: the `rdf:langString` comes back looking like an
  `rdf:dirLangString`. A `#guard` in `TurtleTests.lean` pins the
  current answer. Fixing it changes RDF 1.1 ACCEPTANCE in both trees,
  so it belongs in its own change.

### JSON Schema: validation with a three-valued result (2026-08-22)

`JSONSchema/Validate.lean` ports `JSONSchema.Validate.fst` — draft
2020-12 core plus the validation vocabulary slice: type, const, enum,
the numeric range keywords, multipleOf, string/array length,
items/properties/required, allOf/anyOf/not, and the annotation
keywords.

Two design points decide whether this validator is HONEST rather than
merely green, and both are carried:

1. **The result is three-valued** — pass, fail, or UNSUPPORTED. A
   keyword outside the ported slice makes the verdict undetermined
   rather than passing. `vand` lets a definite failure dominate an
   unsupported sibling, `vor` lets a definite pass dominate one. Both
   directions matter: collapsing unsupported into pass inflates the
   score, into fail deflates it, and neither is the truth. A guard
   pins an unknown keyword returning `unsupported` and the same schema
   with a definite type failure still returning `fail`.
2. **Numbers are exact rationals parsed from the JSON lexeme**, never
   floats — `(numerator, power-of-ten denominator)`. `multipleOf` is
   decided on the cross product with no division, so `0.3` IS a
   multiple of `0.1`, which a float-based check famously gets wrong.
   `1.0` equals `1` for const/enum, and `integer` accepts a number
   whose VALUE is integral.

### XPath: the 1.0 number type (2026-08-22)

`XPath/Number.lean` ports `xpath_number` from `XPath.Eval.fst`. The
combination is deliberate and worth stating: XPath 1.0 numbers are
IEEE 754 doubles, so **NaN and ±Infinity are real values with
specified behaviour, not error states** — but the finite case is an
EXACT decimal (`mantissa / 10^scale`), not a float.

Both halves are observable. The IEEE half: `1 div 0` is `+Infinity`
rather than an error, `0 div 0` and `∞ + -∞` and `0 × ∞` are NaN, and
NaN compares unequal to EVERYTHING including itself. The exact half:
`0.1 + 0.2 = 0.3` holds, and `number('0.1')` equals the literal.
Binary rounding is not something any XPath test asks for; the special
values are asked for constantly.

`boolean()` on a number is false for zero AND for NaN — the rule that
surprises readers, so it has its own guard. `number()` on an
unparseable string is NaN rather than an error, and XPath 1.0 does
NOT accept exponent notation (`1e5` is NaN), which is also guarded.

The one approximation is marked in the source: a non-terminating
quotient is computed to a bounded 18-place scale, since exact decimal
division only terminates for some divisors.

Method note: a `#guard` caught my own wrong test constants here —
scale confused with divisor, `1.5` written as `finite 15 10` rather
than `finite 15 1`. Third time build-time checking has caught an
authoring error in a new area today.

### Schematron: the report model and the assert/report inversion
(2026-08-22)

`Schematron/Validate.lean` ports `Schematron.Validate.fst`: schema,
patterns, rules, assertions and the finding report.

THE INVERSION is the one thing Schematron implementations get wrong,
so it lives in exactly one function and is guarded in both
directions: an `<assert test="X">` produces a finding when X is
FALSE, a `<report test="X">` produces one when X is TRUE. They are
kept as SEPARATE finding constructors rather than one predicate
negated at the call site, so a consumer cannot lose the distinction.

Two more rules with guards, each producing confidently-wrong output
if flipped:
- Within a PATTERN the FIRST matching rule claims a node and later
  rules in that pattern do not fire for it; PATTERNS are independent
  of each other. Getting this wrong yields duplicate findings that
  read as genuine extra violations.
- An undecidable test yields an INDETERMINATE finding carrying its
  reason — for assert and report alike — and `hasViolations` does NOT
  count it, while `hasIndeterminate` reports it separately. The same
  refusal discipline as the Geo predicates, the CSVW formats and the
  JSON Schema validator.

The XPath evaluation and context selection are PARAMETERS, not a
global registry — purity doctrine, and it also makes the whole module
testable without an XPath engine.

### HTTP: the SPARQL endpoint's request/response layer (2026-08-22)

`HTTP/Server.lean` ports `SPARQL.HTTP.fst`, `.Routes.fst` and
`.Response.fst`: request model, query-string parsing, routing,
content negotiation and the response constructors. Everything is a
TOTAL FUNCTION from a parsed request to a response decision — sockets
and reads stay outside — so the whole Web surface is testable with no
network.

This closes a gap the parity ledger flagged against the project's own
framing: the Lean tree had the protocol SEMANTICS (Protocol,
GraphStore, ServiceDescription) but not the server that speaks them.

A REAL BUG in this port, caught by a `#guard` before it landed:
`formDecode` built one `Char` per percent-escape, so `%C3%A9` became
two Latin-1 characters instead of `é`. Percent-decoding must happen at
the BYTE level with UTF-8 interpretation at the end. That is the
classic mojibake bug and it would have corrupted every non-ASCII
query string. Fixed and guarded.

Spec details pinned because each is a protocol violation when wrong:
- A 405 MUST carry `Allow` (RFC 7231 §6.5.5); a bare 405 is
  non-conforming, not merely unhelpful.
- `HEAD` is allowed wherever `GET` is.
- `OPTIONS` is answered BEFORE path matching, so CORS preflight works
  on every endpoint including unknown ones.
- On a shared endpoint an `update=` parameter (or the
  `application/sparql-update` content type) selects update even on the
  query path — Protocol §2.2.
- `q=0` means NOT ACCEPTABLE and can never be chosen, even for the
  server's own first preference. q-values are scaled to integers so
  the ordering is exact rather than a float comparison.
- A malformed percent-escape is kept VERBATIM rather than dropped;
  deleting bytes from a query changes what was asked.

### Storage: HDT byte primitives (2026-08-22)

`Storage/Bytes.lean` opens the storage layer — VByte, little-endian
32-bit reads and writes, CRC8 and CRC32C, and the checksummed section
that HDT's format is built from.

This belongs in the Lean tree by the same rule that governs the F*
side: iron rule 11 puts byte ASSEMBLY in the formal source
(`serialize : data -> List UInt8`), leaving only `write_bytes`
outside. So the format is specifiable here and reading it back is a
total function over a byte list, with no I/O at all.

Two decisions worth recording:

1. **Checksums are typed `UInt8`/`UInt32`, not `Nat`.** The width is
   part of the format, so carrying it in the TYPE removes every
   "< 256" side obligation from the round-trip reasoning instead of
   discharging them one at a time. That restructure happened
   mid-increment, when the `Nat` version left exactly those goals
   dangling.
2. **HDT's VByte marks the LAST byte with the high bit** — the
   OPPOSITE of LEB128's continuation marker. A flipped polarity
   decodes every multi-byte number wrongly while single-byte values
   keep working, which is the failure mode that survives casual
   testing, so `vbyteEncode 5 == [133]` is guarded explicitly.

Corruption rejection is guarded in both halves: a flipped data byte
and a flipped preamble byte each make `Section.parse` return `none`.
A storage layer that reads on through a bad checksum turns a disk
error into wrong query answers.

TWO OBLIGATIONS ARE STATED IN THE SOURCE, not admitted: the general
VByte round trip (needs induction on `n / 128` with the accumulator
generalised) and the section round trip (needs a readU32LE-over-append
lemma). `#guard` covers both by evaluation meanwhile — including
VByte boundary values at 127/128/16383/16384.

### MathML: content evaluation and presentation rendering (2026-08-22)

`MathML/Core.lean` ports `MathML.Content.fst` and
`MathML.Present.fst`: the Content expression tree, exact-rational
evaluation, Presentation rendering with operator precedence, and the
content-vs-presentation classifier.

Rationals are EXACT and normalised to lowest terms, so `1/3 + 1/3 +
1/3` is exactly `1` — Content MathML denotes the mathematical value,
and a float would make that guard fail.

Division by zero REFUSES (`none`) rather than producing an infinity:
Content MathML has no such value, so inventing one would be answering
a question the vocabulary cannot ask. Same for an unbound symbol and
an unknown operator — every refusal path returns `none`, never a
default.

Rendering detail worth keeping: a NEGATIVE literal carries the loose
precedence of a `minus`, so it gets fenced inside a tighter parent
(`2^(-3)`, not `2^-3`). Both directions are guarded — a looser child
IS fenced, a tighter one is NOT.

The classifier lets CONTENT win when both vocabularies appear, matching
the F* order: a mixed document is processed as content markup, since
that is the half carrying meaning rather than layout.

### XSLT: template priorities and conflict resolution (2026-08-22)

`XSLT/Templates.lean` ports the SEMANTIC HEART of `XSLT.Transform.fst`
— §5.5 conflict resolution and §2.6.2 import precedence. Scope stated
plainly: the F* module is 4,183 lines covering instantiation,
attribute sets, number formatting, output serialisation and keys.
What is ported is the part that decides WHICH TEMPLATE FIRES, which is
where implementations disagree with each other and with the spec.

Priorities are scaled by TEN and kept as integers. XSLT's defaults are
0, -0.25, -0.5 and 0.5; scaling makes every comparison exact and takes
float ordering out of the one place where a tie decides which template
runs.

Two orderings that are bugs when reversed, both guarded:

1. **Import precedence is checked BEFORE priority.** Checking priority
   first lets an imported template with a specific pattern beat the
   importing stylesheet's override, which defeats the entire point of
   `xsl:import`.
2. **The compound test comes BEFORE the wildcard test** in
   `altPriority`, so `foo/*` scores 5 rather than -5. Reversing them
   makes compound patterns lose to bare ones.

Also pinned: at equal precedence and priority the LAST declared
template wins; a template in a different mode is not a candidate at
all; a name-only template never matches by pattern; and named lookup
for `call-template` resolves by import precedence rather than document
order. Pattern parsing keeps `//x` (relative descendant) distinct from
`/x` (root-anchored) — one slash apart, quite different meanings.

### Storage: the durable-UPDATE delta log (2026-08-22)

`Storage/DeltaLog.lean` ports the framing from
`RDF.Store.Columnar.DeltaLog.fst`. The COTTAS base file is immutable;
a SPARQL UPDATE appends to a log beside it, and compaction later folds
the log into a new base. That makes this framing the CRASH-SAFETY
BOUNDARY of the whole store, which is why it belongs in the formal
source rather than in a writer.

The checksum is a plain ADDITIVE mod-2^32 check and deliberately NOT a
cryptographic digest. Its only job is letting a replay reject a TORN
record without decoding it. Whole-log drift detection is a separate
mechanism (the sha256 hash-witness pattern); conflating them would put
a cryptographic cost on every append for a property appends do not
need.

Two behaviours guarded because they are what a storage layer gets
wrong under crash conditions:

1. **A torn tail is not an error.** A crash mid-append is EXPECTED,
   and recovery means "take every record that verifies, discard from
   the first that does not". `replay` returns the recovered records
   AND a clean/torn flag, so the caller can tell a tidy shutdown from
   a crash without that changing what was recovered.
2. **The epoch guard prevents double-apply.** A base compacted at
   epoch `n` must ignore log records from epoch ≤ `n`, or a replay
   re-applies updates the compaction already folded in. `shouldReplay`
   is strict-greater-than, and both boundary cases are guarded.

The four magic numbers are pinned as their documented ASCII bytes
(`DLE1`, `DLB1`, `DLOG`, `CEP1`), little-endian — a silently
byte-swapped magic would make every existing store unreadable.

### VC: the credential data model (2026-08-22)

`VC/Credential.lean` ports `VC.Credential.fst`, completing the Lean
VC module set alongside the existing Context, DataIntegrity, DidKey
and Multibase.

THE RULE THAT CARRIES SECURITY WEIGHT, and the reason it gets its own
guard: the base VC 2.0 context IRI must be the FIRST `@context` entry,
not merely present. JSON-LD context processing is ORDER-DEPENDENT — a
later entry can redefine terms an earlier one established — so
accepting a base context in second position would let a crafted
context silently redefine `issuer` or `credentialSubject`. The guard
pins both orders.

Verdicts carry a REASON string rather than being booleans: a
credential-verification failure that says only "false" is
unactionable, and the VC suite distinguishes failure modes. A
conjunction keeps the FIRST failure's reason, so the message names
the earliest problem rather than the last.

An EMPTY `credentialSubject` fails — a credential asserting nothing
about anyone is not a credential — and so does an empty array form.

Validity dates are checked for SHAPE only. Their ordering against
"now" belongs to a caller with a clock; this module stays a total
function of its input rather than reading one, per the purity
doctrine.

### CSVW: a reader probe over the real corpus, and the bug it found
(2026-08-22)

`Harness/CsvwProbe.lean` runs the Lean dialect reader against the
REAL vendored W3C csvw corpus — 177 `.csv` files off disk, never
synthetic input.

IT IMMEDIATELY FOUND A BUG the unit tests had missed: a FINAL line
terminator was creating a phantom one-cell row, so 85 of 177 files
read as "ragged". RFC 4180 makes the terminator optional on the last
record, so `"a\nb\n"` and `"a\nb"` are the same two rows. A synthetic
test does not catch this because one rarely writes the trailing
newline by hand — which is precisely the argument for running the
suite's own files. Fixed (`dropTrailingTerminator`) and guarded,
including the case it must NOT break: an INTERIOR blank line is still
a row.

After the fix: 170 read with uniform width, 7 read ragged, 0 failed
to read.

The probe reports RAGGED SEPARATELY rather than as failure, because
CSVW treats a wrong cell count as a VALIDATION error, not a parse
error, and the suite ships such files deliberately (test058,
test091). Counting them as failures would penalise correct behaviour.

The output states plainly that this is a READER-LEVEL check and NOT a
conformance score — it never compares against the expected `.ttl`,
which needs metadata resolution and graph isomorphism. Calling the
number "csvw: 170 pass" would be a lie by naming, so the probe says
so itself rather than trusting a reader of the log to remember.

### JSON-LD: the rest of the API — compact, flatten, fromRdf, html (2026-08-22)

`JSONLD/Compact.lean`, `Flatten.lean`, `FromRdf.lean` and `Html.lean`
port `JSONLD.Compact.fst`, `JSONLD.Flatten.fst`, `JSONLD.FromRdf.fst`
and `Parser.JSONLD.Html.fst`. With expansion and toRdf already in the
tree, this closes the five json-ld-api manifests the F\* runners cover.
`Harness/JsonLdApiProbe.lean` (`lake exe l4jsonld-api`) reads the real
manifests; `Harness/JsonLdProbe.lean` keeps toRdf and is untouched.

Measured from the repository root, beside the F\* numbers for the same
manifests:

| manifest | Lean (`l4jsonld-api`) | F\* runner |
|---|---|---|
| expand | 385 pass, 0 fail (out of 385) | 385 pass, 0 fail, 0 skip (out of 385) |
| compact | 245 pass, 0 fail, 1 local-override (out of 246) | 245 pass, 0 fail, 1 local-override, 0 skip (out of 246) |
| flatten | 58 pass, 0 fail (out of 58) | 58 pass, 0 fail, 0 skip (out of 58) |
| fromRdf | 53 pass, 0 fail, 1 local-override (out of 54) | 53 pass, 0 fail, 1 local-override (out of 54) |
| html | 50 pass, 0 fail (out of 50) | 50 pass, 0 fail, 0 skip (out of 50) |
| TOTAL | 791 pass, 0 fail, 2 local-override (out of 793) | same |

The two local-overrides are the SAME two fixtures the F\* runners
dispute — compact `#t0038` and fromRdf `#t0008`, both JSON-LD 1.0-only
expectations, both already argued in `tests/local-overrides/`. This
probe reads those files rather than carrying its own opinion.

Translation decisions worth recording:

1. **The comparison rule is the runners', not a new one.** All five F\*
   runners compare two JSON trees by `jsonld_expanded_equal`: RFC 8785
   canonical serialisation, then string equality. Object member order is
   insignificant, array order significant, numbers by canonical value —
   and there is NO blank-node relabelling, because the fixtures pin the
   exact `_:b0`, `_:b1` … labels the algorithms' own issuers produce.
   The Lean side calls `JSONLD.expandedEqual`, which is that rule.
2. **`option` became `Res`, and the extra information is real.** The F\*
   sources return a bare `option`, so the runners can only check THAT a
   negative test failed. This port returns `Except JsonLdError`, so the
   probe also checks the manifest's `expectErrorCode`: 140 of 144
   negative tests across the five manifests produce the exact code the
   manifest names. Four do not, and each is a different-but-legitimate
   failure reason, not a wrong answer:
   * expand `#ten04` (`invalid local context` vs `invalid @nest value`),
     `#ter33` (`invalid reverse property value` vs `invalid @reverse
     value`), `#tpi05` (`invalid @index value` vs `invalid value
     object`) — the same three the toRdf probe already reports;
   * compact `#te001` — the manifest says `compaction to list of
     lists`, but the fixture's INPUT already contains
     `{"@list": [{"@list": ...}]}`, which §5.1 Expansion rejects first
     with `list of lists`. Compaction never runs. The F\* engine takes
     the same route; its `option` return simply cannot show it.
   Five new error constructors were added to `JSONLD/Context.lean` for
   the codes the compact / flatten / html manifests name:
   `compactionToListOfLists`, `iriConfusedWithPrefix`,
   `conflictingIndexes`, `loadingDocumentFailed`, `invalidScriptElement`.
3. **`ac_previous` is the `prev` list.** F\*'s `active_context` carries a
   self-referential `ac_previous : option active_context`; this port's
   `ActiveContext` has `cur` plus a `prev` stack, which the expansion
   port had already established. Compaction's three uses map exactly:
   step 5's conditional pop is `if ac0.prev.isEmpty then ac0 else
   ac0.pop`, and step 11's non-propagating type-scoped context is
   `ac3a.setPrev ac2`.
4. **Byte scanning became character scanning.** The F\* originals index
   UTF-8 bytes (`Parser.FastString`); this tree indexes `Char`s. Every
   delimiter the compaction relativizer and the HTML extractor look for
   is ASCII (`: / # ? _ @ < > " '`), and a UTF-8 multi-byte sequence
   never contains an ASCII byte, so the two scans agree. The one place
   the difference is observable in principle is `cmpTermLess`, which
   compares term LENGTHS: a term with non-ASCII characters has a
   shorter char length than byte length. No suite fixture has one.
5. **`Ov` needed a hand-written `eqb`.** `JSONLD.FromRdf`'s
   intermediate value tree is a nested inductive (`lst : List Ov`), the
   shape `deriving DecidableEq` does not support — the same gap `Json`
   already documents. A mutual `Ov.eqb` / `Ov.eqbList` supplies the
   structural equality the spec's "unless the value is already in the
   array" check needs (fromRdf fixture 0017), with `BEq` from it. Not
   `deriving BEq` (pitfall #1).
6. **`scoped` is a reserved word in Lean 4.** `| some (scoped, defUrl) =>`
   is a parse error whose message points at the NEXT line and then
   cascades through the whole `mutual` block as "unknown identifier"
   for every later function. Same family as pitfall #8 (`local`, `/-`).
7. **`compactIri`'s spec-mandated self-probe uses `if h : depth = 0`.**
   §6.3 step 4.15 asks whether the value's `@id` itself compacts to a
   term that round-trips — one bounded recursive call. Written as
   `match depth with | 0 | d+1`, Lean cannot see `d < depth` inside a
   `let`; `if h : depth = 0 then ... else ... (depth - 1)` with
   `decreasing_by omega` does.

Sabotage test (the discipline this tree uses when extending): inverting
`cmpTermLess` to prefer the LONGEST term makes `lake build` fail at
three places — the theorem `cmpTermLess_length_le` in
`JSONLD/ApiTests.lean` and two of its `#guard`s — and drops the compact
manifest to 244 pass, 1 fail, 1 local-override (out of 246), the named
failure being `#ta038` "Index map round-tripping". Restoring the
comparator returns all of it. Worth noting how NARROW the corpus signal
is: one fixture out of 246, because the suite's contexts rarely define
two terms of different length for one IRI. The build-time theorem is the
stronger tripwire here, which is the argument for keeping both.

What is NOT ported: JSON-LD Framing (`JSONLD.Frame.fst`) — a separate
specification with a separate suite, and no manifest above needs it.
### CSVW: a REAL csv2rdf conformance runner, and what it measured
(2026-08-22)

`Harness/CsvwRdfRun.lean` runs the whole pipeline — Lean CSVW reader →
conversion → emit — and compares against the suite's OWN expected
`.ttl`, parsed by the Lean Turtle parser and compared by GRAPH
ISOMORPHISM. That comparison is what makes it conformance rather than
a probe. Isomorphism rather than triple-set equality because csv2rdf
mints blank nodes whose labels are arbitrary; comparing labels would
fail correct output.

📊 FIRST MEASURED RESULT: **0 pass, 7 fail, 2 skip** out of the 9
no-metadata manifest entries. 261 of 270 entries carry metadata
(an `implicit` member) and are not attempted — reported, not hidden.

DIAGNOSIS, from the numbers themselves: every failure produced roughly
a THIRD of the expected triples, and the expected `.ttl` files open
with `a csvw:TableGroup ; csvw:table [ a csvw:Table ; csvw:row [ a
csvw:Row ; csvw:describes [...`. The suite's no-metadata tests expect
STANDARD mode — the full TableGroup/Table/Row scaffolding — while the
runner's conversion path emits MINIMAL mode. `Emit.lean` has
`rowTriplesStandard`, but it produces per-row description only; the
group and table nodes above it are not built yet.

So the gap is NAMED and SIZED rather than guessed at: standard-mode
table and group assembly, roughly a third to two-thirds of each
expected graph. That is the next increment, and it is a much more
useful thing to know than "the port exists".

METHOD NOTE, paid for here: the first version of this runner paired
files by BASENAME and treated `test001.json` as input metadata. It is
not — it is the expected JSON OUTPUT of the csv2json suite. Pairing
must come from the manifest's own `action`/`result`, which is why the
runner now parses `manifest-rdf.jsonld` instead of guessing from
filenames.

### CSVW standard mode, and the comparison bug it uncovered
(2026-08-22)

Two landings in one, because the second was only visible after the
first.

**1. Standard-mode table and group assembly.** `CSVW/Emit.lean` gained
`rowNode`, `RowInput`, `tableTriplesStandard` and
`tableGroupTriplesStandard`: the `csvw:TableGroup` → `csvw:table` →
`csvw:Table` → `csvw:row` → `csvw:Row` scaffolding above the row
descriptions, plus the `rdf:type` triples the previous
`rowTriplesStandard` did not emit. The runner now picks the mode from
the manifest entry's own `option.minimal` member instead of running
everything one way.

Two details that are easy to get wrong and were:

- The `csvw:row` link and the row description must name the SAME blank
  node. `rowNode` is a named, exported function for exactly that
  reason; a table that minted its own label would produce orphan row
  nodes, and no isomorphism check can repair that.
- `csvw:rownum` reports the position within the table, the `#row=`
  fragment reports the SOURCE line. With a header they differ by one,
  so using either for both leaves the triple COUNT right and every row
  URL off by a line. `RowInput` carries both and the `#guard`s pin
  them apart.

Also fixed: `runOne` derived the expected `.ttl` name from the `.csv`
name. `test028` and `test029` both read `countries.csv` and expect
`test028.ttl` and `test029.ttl`, so both were reported as skips — a
silently narrowed denominator. The manifest's `action` and `result`
are now used verbatim.

**2. The comparison primitive was misreporting.** With standard mode
landed, `test001` and `test005` still failed — with the triple counts
EQUAL on both sides (60 vs 60, 106 vs 106). The graphs were correct.
`RDF/Isomorphism.lean` refused to search above `isoBnodeBudget = 16`
blank nodes, and csv2rdf standard mode mints two blank nodes per row
plus two for the table and group, so an 8-row table has 18. The search
refused, `Graph.isomorphic?` returned `false`, and the runner scored
it `fail`.

That is precisely the failure the module's own comment warns about —
"a bare `false` a caller could mistake for definitely-different" — and
it had been sitting in the test file as a recorded expectation:
`#guard Graph.isomorphic? (manyBnodes "a") (manyBnodes "b") = false`
on two graphs that ARE isomorphic (17 interchangeable blank nodes;
every mapping works). A refusal was written down as a difference and
then pinned.

Three repairs:

- **Node count was the wrong bound.** The cost is CANDIDATE
  ASSIGNMENTS TRIED, not blank nodes. `searchBijectionFuel` now
  carries an explicit work budget (`isoWorkBudget = 100000`) and
  returns the unspent fuel, so a caller can tell "searched everything,
  found nothing" from "gave up". Termination stays structural — a
  lexicographic `(rem.length, phase, cands.length)` measure over the
  mutual pair — because depth is already bounded by the blank-node
  count and making fuel the measure would hide that.
- `isoBnodeBudget` is now 128 and documented as a coarse guard on the
  polynomial parts (the certificate re-check is quadratic), not the
  bound on search breadth.
- `Graph.isomorphicOutcome` / `Dataset.isomorphicOutcome` report a
  WORK trip as `budgetExceeded` too, and `CsvwRdfRun` counts
  `budgetExceeded` in its own bucket. Folding a give-up into `fail`
  misreports the engine, which is what happened here.

Soundness is untouched: the search returns a CANDIDATE and
`Graph.isomorphismMap?` certifies it on the way out, so
`Graph.isomorphic?_sound` and the reflexivity theorems build unchanged
on the same axiom base (propext / Classical.choice / Quot.sound).

📊 MEASURED AFTER, csv2rdf no-metadata subset: **9 pass, 0 fail, 0
comparison-gave-up, 0 skip (out of 9)** — from 0 pass, 7 fail, 2 skip.
261 of 270 manifest entries still carry metadata and are not attempted.

📊 NO REGRESSION elsewhere, re-measured the same way: rdf manifest
**1031 pass, 0 fail (out of 1031)**; SPARQL 1.1 **601 pass, 0 fail, 30
unsupported (out of 631)**; OWL probe TOTAL 1060 pass, 354 fail (out
of 1457) with `owl2_profile_ql` 87 pass, 0 fail; RDF/XML
eval-isomorphic 130 pass, 2 fail (out of 132) — those two are
`rdfms-xml-literal-namespaces` XMLLiteral canonicalisation
differences, reported as `notEqual`, not budget trips.

METHOD NOTE, for the next session: a test that pins the CURRENT
behaviour of a give-up path pins the bug — the `= false` guard above
read as a passing test for as long as it stood. When a procedure
has a three-way outcome, the guards belong on the three-way outcome,
not on the Bool that collapses two of them.
## Stage: fourteen sound `[ext]` rows in the OWL RL closure (2026-08-22)

`RLRules.lean`'s header used to say the `[ext]` layer of the F\* engine
was out of scope because "a port of the table is a port of the table".
That reading was too strict: an extension with a stated OWL 2
RDF-Based Semantics justification is as reviewable as a table row, and
those rows were the whole of the profile-RL entailment gap. Fourteen
of them are now in, each carrying the semantic condition it rests on
in place of a table id, in `RLRules.lean`'s `[ext]` section, in both
engines, and with a licensing lemma and a T4 completeness case each.

### The rows, by family

**differentFrom synthesis** (5) — `eqDiffSym` (§5.8: inequality is
symmetric), `pdwToDiff` and `caxDwToDiff` (the Horn contrapositives of
prp-pdw and cax-dw: two things a disjointness forbids identifying must
be different), `fpDiffToDiff` and `ifpDiffToDiff` (the contrapositives
of prp-fp and prp-ifp). F\* names: `owl_rule_differentFrom_symmetry`,
`owl_rule_pdw_to_differentFrom`, `owl_rule_cax_dw_to_differentFrom`,
`owl_rule_fp_diff_to_diff`, `owl_rule_ifp_diff_to_diff`.

**chain and reflexivity** (2) — `chainToTrans` (§5.11 at `l = <p,p>`
IS §5.9's transitivity condition, so the row reads an equivalence in
one direction; F\* `owl_rule_chain_to_transitive`) and `prpRfl` (§5.9:
a reflexive property relates every member of `IR` to itself, so it
relates every IRI of the graph to itself; F\*
`owl_rule_reflexive_property`).

**Table 7 over the datatype map** (3) — `xsdAxioms` (the XSD numeric
subtype tower plus `rdf:type rdfs:Datatype` for each of its members),
`dtRangeIntersect` (two range axioms constrain to the intersection of
two value spaces; the four-entry table the F\*
`xsd_range_intersections` carries), `dtType1Builtin` (the premise-free
half: every D-interpretation recognises `xsd:string`, and every OWL 2
datatype map `xsd:integer`, so both are `rdfs:Datatype` from the empty
graph — WebOnt-I5.8-011).

**comprehension witnesses** (4) — `caxDwToComplement` and
`clsMaxqc1ToComplement` mint `_:__rl_comp__<c>`, the complement class
§5.14's comprehension condition supplies; `minCard1Comprehension`
mints `_:__rl_minc1__<p>`, the `minCardinality 1` restriction the same
section supplies; `caxAdcToDw` turns an `owl:AllDisjointClasses` list
into pairwise `owl:disjointWith` so all three cax-dw rows reach it
without each growing a list-walking body.

### What is CARRIED as an assumption rather than proved

`xsdAxioms` and `dtRangeIntersect` are true only if the
interpretation's datatype map recognises the XSD datatypes with the
XSD 1.1 §3.4 value spaces. That assumption is written out as
`XsdValueSpaceSubset` and the two tables list exactly which
containments are relied on; `xsdIntegerDecimal_subset` and
`xsdIntInteger_subset` DISCHARGE the two edges the Lean datatype map
of `RDF/Datatypes.lean` models (`int ⊂ integer ⊂ decimal`), which is
all of the tower that map knows. The other twelve edges are assumed
and marked assumed.

More generally: these lemmas prove LICENSING, not truth preservation.
`RLTheorems.lean`'s header already disclaims model theory for the whole
file — there is no `OWL.Semantics` port on the Lean side — and each
`[ext]` constructor carries its RDF-Based-Semantics argument in its own
doc comment instead of in a theorem. Do not read a `_sound` lemma here
as a soundness theorem against the Recommendation.

### Three rows Table 7 CANNOT have here

dt-eq, dt-diff and dt-type2 put a LITERAL in subject position
(`T(lt1, owl:sameAs, lt2)`). `RDF/Core.lean`'s `Subject` is an IRI or a
blank node, with no literal case — RDF 1.1 Concepts §3.1, which the
OWL 2 RL rule table steps outside of by writing generalised triples.
Reaching them means widening `Subject` across the whole tree. That is
a property of the term algebra, not a gap in this module's coverage.

### The guard that cost a measurement

`xsdAxioms` fires on a datatype POSITION (an XSD IRI in the object
slot under `rdfs:range`, `rdf:type`, `rdfs:subClassOf`, …), not on the
F\* `graph_mentions_xsd_iri`'s "any XSD IRI anywhere". The narrower
guard is not a simplification, it is a fix: `dtType1Builtin` puts
`xsd:integer rdf:type rdfs:Datatype` in every closure with no premise,
eq-ref then derives `xsd:integer owl:sameAs xsd:integer` from it, and
under the "mentions" guard THAT triple drives the whole tower plus its
scm-sco transitive closure into every closure the engine computes.
Measured: 116 triples and 6 rounds for a 3-triple `rdfs:subClassOf`
fixture with nothing to do with datatypes, `type-consistency` from
6417 ms to 11622 ms, and the `RLTests` idempotence guards (which assert
saturation at a FIXED fuel, so they see this) red. `owl:sameAs` is not
a datatype position, so restricting to a position cuts the loop at its
source, and the rows that motivate the tower are all `rdfs:range`.

The comprehension skolems are FUNCTIONS of their argument
(`__rl_comp__<c>`, `__rl_minc1__<p>`), not counters, for the same
class of reason: a counter would make every round grow the graph and
the fuel loop's "length did not change" stopping rule would never
fire. With a function, a second round mints the same node and `addOne`
drops it.

### Scores

Before (`cd formal/lean4 && lake exe l4owl-probe`, claude/main at
`8009b9b2b`):

```
profile-RL.rdf: 102 pass, 19 fail, 0 skip, 5 unsupported (out of 126)
profile-EL.rdf: 95 pass, 21 fail, 1 skip, 4 unsupported (out of 121)
profile-QL.rdf: 81 pass, 6 fail, 0 skip, 0 unsupported (out of 87)
type-positive-entailment.rdf: 297 pass, 109 fail, 0 skip, 6 unsupported (out of 412)   wall_ms=4036
type-inconsistency.rdf: 29 pass, 84 fail, 1 skip, 14 unsupported (out of 128)
type-consistency.rdf: 461 pass, 110 fail, 0 skip, 12 unsupported (out of 583)   wall_ms=6417
TOTAL: 1060 pass, 354 fail, 2 skip, 41 unsupported (out of 1457), cap_hits=0
profile-RL.rdf PositiveEntailmentTest: 11 pass, 18 fail, 0 skip, 1 unsupported (out of 30)
```

After:

```
profile-RL.rdf: 116 pass, 5 fail, 0 skip, 5 unsupported (out of 126)
profile-EL.rdf: 101 pass, 15 fail, 1 skip, 4 unsupported (out of 121)
profile-QL.rdf: 82 pass, 5 fail, 0 skip, 0 unsupported (out of 87)
type-positive-entailment.rdf: 314 pass, 92 fail, 0 skip, 6 unsupported (out of 412)   wall_ms=7091
type-inconsistency.rdf: 29 pass, 84 fail, 1 skip, 14 unsupported (out of 128)
type-consistency.rdf: 478 pass, 93 fail, 0 skip, 12 unsupported (out of 583)   wall_ms=11486
TOTAL: 1120 pass, 294 fail, 2 skip, 41 unsupported (out of 1457), cap_hits=0
profile-RL.rdf PositiveEntailmentTest: 25 pass, 4 fail, 0 skip, 1 unsupported (out of 30)
```

NO NEW FAIL anywhere: the FAIL multiset shrank by 60 units over 17
distinct cases and gained nothing. Every NegativeEntailmentTest line
held (profile-RL 6 pass 0 fail, profile-QL 3 pass 0 fail,
type-consistency 23 pass 0 fail), which is the check that matters most
for rows that ADD triples. `cap_hits` still 0. Wall clock is 1.76x and
1.79x the baseline on the two big catalogs — the closures are bigger
(the differentFrom rows are quadratic in a disjoint class extension by
construction, as the F\* rules are) and the round count moved only
1590 -> 1596 and 2186 -> 2194, so the cost is per-round work, not
extra rounds.

### Per-family FAIL accounting

| family | profile-RL cases closed |
|---|---|
| differentFrom synthesis | WebOnt-differentFrom-001, WebOnt-disjointWith-001, WebOnt-disjointWith-002, New-Feature-DisjointObjectProperties-001, owl2-rl-rules-fp-differentFrom, owl2-rl-rules-ifp-differentFrom |
| chain bridge | chain2trans1 |
| reflexive property | New-Feature-ReflexiveProperty-001 |
| XSD tower + range intersection | WebOnt-I5.8-006, WebOnt-I5.8-008, WebOnt-I5.8-009 |
| builtin dt-type1 | WebOnt-I5.8-011 |
| complement comprehension | DisjointClasses-001, New-Feature-ObjectQCR-002 |
| AllDisjointClasses to disjointWith | DisjointClasses-003 |
| minCardinality comprehension | WebOnt-I5.26-009, WebOnt-I5.26-010 |

Seventeen cases, 60 units across the six catalogs (a case counts once
per catalog it appears in and once per test type it declares).

### Remaining profile-RL failures, all five named

* `New-Feature-DisjointDataProperties-002` and
  `New-Feature-DisjointObjectProperties-002` — the conclusion is an
  `owl:AllDifferent` node with an `owl:members` COLLECTION of the
  three individuals. Materialising it needs a skolem LIST, n cells for
  n members, not the single-node skolems this stage introduced. The
  reasoning behind it (an `owl:AllDisjointProperties` axiom plus one
  edge per property makes the targets pairwise different) becomes
  reachable through `pdwToDiff` as soon as `AllDisjointProperties` is
  expanded pairwise the way `caxAdcToDw` expands
  `AllDisjointClasses`; only the LIST materialisation is missing.
* `WebOnt-I5.5-005` — `_:c owl:unionOf (a)`, the singleton-union
  comprehension. Same missing piece: a one-cell skolem list.
* `WebOnt-I4.6-005-Direct` — the F\* `[mode]` rule
  `owl_rule_named_equivClass_to_sameAs_mode`. `[mode]` rules fire only
  under a catalog semantics mode and there are no semantics modes on
  the Lean side, so this one is out of reach by design, not by gap.
* `New-Feature-Keys-006` (InconsistencyTest) — needs Table 7's dt-diff
  to fire prp-key against two literal key values, the row that cannot
  exist here while `Subject` has no literal case.

### Sabotage (done, then restored)

Removing `eqDiffSymFor` from `RLClosure.conclusionsList` alone does not
even BUILD: `RLClosureIndexed.conclusionsFromS_ofGraph` refuses,
because the two engines' row lists must match for the bridge. Removing
it from BOTH engines builds, and profile-RL PositiveEntailmentTest
drops from 25 pass to 23 pass, with `WebOnt-differentFrom-001` flipping
to `closure-gap: missing …#b owl:differentFrom …#a`; TOTAL drops from
1120 pass to 1112 pass. Restored, rebuilt, re-measured to the numbers
above. This is a STRONGER gate than the one the previous stage
recorded: it now takes two coordinated edits to sabotage a row, and
`RLTheorems`'s T4 proof refuses either of them on its own.

### Gates

`lake build` green (381 jobs). `indexedClosure_eq` still proved as a
LIST equality at every fuel — every new row went into both engines in
the same `rowFor`/`rowForS` shape, and each new `…ForS_ofGraph` bridge
lemma is `rfl` except `chainToTransForS_ofGraph` and
`caxAdcToDwForS_ofGraph`, which rewrite through the recursive walkers
first. `#print axioms` on `closure_sound`, `closure_extensive`,
`closure_complete_of_saturated`, `detectClash_sound`,
`indexedClosure_eq`, `mem_indexedClosure_iff`, `detectClashI_closureI`,
all fourteen new `_sound` lemmas and the two discharged value-space
edges: `[propext, Classical.choice, Quot.sound]` and nothing else.

### CSVW metadata: the parse, the pipeline, and four bugs the corpus
found (2026-08-22)

The csv2rdf runner could attempt 9 of 270 manifest entries. The other
261 reference a metadata document, so the whole remaining denominator
was behind a metadata parse. Three new modules and one wiring fix:

- `CSVW/MetadataParse.lean` — a metadata DOCUMENT into the model
  `Metadata.lean` already defined: `@context` (default language and
  base), table groups and single-table documents, inline
  `tableSchema`, columns with `titles` in all four shapes, every
  inherited property but `textDirection`, `datatype` in both forms,
  `dialect`, and common properties with prefix expansion. NOT parsed,
  and each named rather than pretended: `foreignKeys`,
  `transformations`, and a `tableSchema` given as a URL (metadata
  DISCOVERY, which is I/O).
- `CSVW/Common.lean` — common properties as RDF. A JSON-LD SUBSET
  with the boundary stated: `@value`/`@type`/`@language`/`@id`,
  arrays, nested nodes; not term definitions, `@vocab`, containers or
  `@graph`. An unhandled shape emits NO triple rather than a guessed
  one.
- `CSVW/Pipeline.lean` — the join. Columns match fields BY POSITION
  (tabular-data-model §8); `titles` derive a name, they never reorder.
- `Formats.lean` gained DATE/TIME pattern parsing, and
  `Conversion.prepareLexical` now actually CALLS `formatConvert`.

📊 MEASURED, csv2rdf: **90 pass, 115 fail, 0 comparison-gave-up, 5
skip (out of 210 attempted)**, from 9 pass out of 9 attempted. The 58
negative tests are NOT attempted and say so — they assert an error,
not a graph, and need the validator's outcome.

The four bugs the corpus found, all of which produce the RIGHT number
of triples with the wrong content — the failure mode a count check
cannot see:

1. **The `action` is not always a CSV.** 236 of the 270 entries name a
   METADATA document as their action; the CSV files come from its
   `url`/`tables`. A runner that assumed otherwise attempted 30 of 270
   and reported the rest as nothing at all.
2. **The header row supplies column titles** when the metadata does
   not (§8 step 4.6). Without that a table with no metadata gets
   `_col.1`, `_col.2`, … as its predicates: structurally right,
   semantically wrong. This REGRESSED tests 001–010 to failing the
   moment the pipeline replaced the ad-hoc path, and the triple counts
   stayed equal throughout.
3. **`format` was never applied.** `prepareLexical` did the whitespace
   rule and stopped, so a `date` column with `"format": "M/d/yyyy"`
   emitted `"10/18/2010"^^xsd:date` where the value is
   `"2010-06-02"`-shaped. Fixing it moved the score 46 → 78.
4. **`{_name}` and the datatype aliases.** A `propertyUrl` of
   `http://schema.org/{_name}` expanded to `http://schema.org/` for
   every column — a whole table collapsed onto one predicate — and
   `"datatype": "number"` minted `xsd:number`, which does not exist
   (`number` is a CSVW alias for `xsd:double`). Fixing both moved the
   score 78 → 90.

Also fixed while here: the metadata document's own directory is the
base for its table `url`s. `test011/tree-ops.csv-metadata.json` names
`tree-ops.csv`, which is `test011/tree-ops.csv` on disk; resolving it
against the tests root finds a DIFFERENT file of the same name at the
top level.

Named next steps, sized from the failure list rather than guessed:
metadata MERGING (§5.1 — several tests supply file, link and user
metadata and expect a defined precedence; `dc:label "file"` vs
`"metadata"` is the visible symptom), virtual columns, and the
`foreignKeys` reference tests whose second table the runner currently
skips.

METHOD NOTE: the `--dump=<manifest id>` switch on `l4csvw-rdf` prints
both graphs as sorted N-Triples. Every one of the four bugs above was
found by reading that diff, and none of them was visible in the
score line, which said "produced 24, expected 24" throughout.

### CSVW: per-cell subjects, virtual columns, and four value-level
rules the corpus enforces (2026-08-22)

Continuing the same measured loop, each step read off the
`--dump=<manifest id>` diff rather than guessed:

1. **The subject is per CELL, not per row.** `aboutUrl` is an
   inherited property, so different columns of one row can describe
   different things — the corpus has tables whose every row produces
   an event, a place and an offer, each with its own `aboutUrl` and
   each listed under that row's `csvw:describes`. `Emit` gained
   `CellOut` (a converted cell with the subject it hangs from) and
   `RowInput.subjects` (the DISTINCT subjects, one `csvw:describes`
   each). A row-level subject merged all three onto one node.
2. **VIRTUAL columns must not go through the cell rules.** A virtual
   column has no field, so its cell is empty — and an empty cell IS
   the null value, which `convertCell` correctly drops. Its value
   comes from `valueUrl` alone, so the pipeline builds its
   `CellResult` directly. Ten of twenty expected triples were missing
   in `test033` for this reason.
3. **Link properties need PREFIX EXPANSION after template
   expansion.** `schema:{_name}` is not a prefixed name until
   `{_name}` is filled in, so expansion belongs in the pipeline, not
   the parse. Left alone, `rdf:type` and `schema:MusicEvent` pass the
   `isIri` check — they have a colon — and produce triples on IRIs
   that denote nothing.
4. **A language tag applies only where the value is a STRING.** RDF
   1.1 has no language-tagged `xsd:normalizedString`. A stated
   non-string datatype wins over an inherited `lang`. An
   `EmitTests` guard asserted the OPPOSITE rule ("a language tag wins
   over a datatype") and had to be corrected — it was pinning
   behaviour, not the specification.
5. **An invalid language tag is ignored, not attached.** The corpus
   supplies `"lang": "notavalidlanguagetag"` and expects a plain
   literal. `isLangTagValid` checks the BCP 47 subtag shape.
6. **A datatype NAME the specification does not list is rejected.**
   `anySimpleType` and `anyType` are XSD types CSVW deliberately
   excludes; reading every name as `xsd:<name>` put
   `^^xsd:anySimpleType` on literals the expected graph leaves plain.
   `csvwDatatypeNames` is the permitted list.

📊 MEASURED, csv2rdf: **100 pass, 105 fail, 0 comparison-gave-up, 5
skip (out of 210 attempted)** — from 90 at the previous landing and 9
before the metadata parse existed.

Every one of these six produced the RIGHT number of triples with the
wrong content, except (2). The score line read "produced 19, expected
19" through four consecutive bugs.

### CSVW: invalid values, invalid metadata, and the XSD numeric
lexical spaces (2026-08-22)

Six more rules, same loop — each read off the `--dump` diff, each
producing the RIGHT triple count with wrong content:

1. **A non-string LINK property normalises to the EMPTY template**,
   not to nothing. With `"aboutUrl": true` the subject is the TABLE
   URL — the empty template resolved against the table — not a fresh
   blank node (tests 047/048/049).
2. **A numeric field must be a NUMBER.** The corpus supplies
   `"headerRowCount": "0"`, which is invalid, so the default of one
   header row applies. Accepting the string turned the header into a
   data row and added a whole extra row of triples.
3. **Header titles apply only when the table has NO schema.** A
   metadata schema REPLACES the embedded one, so a schema describing
   no usable column leaves the columns as `_col.1`, `_col.2`, … rather
   than falling back to the file's headings (test100 supplies
   `"columns"` as an object instead of an array).
4. **An invalid `tableSchema` acts as an EMPTY OBJECT** — a schema is
   present, with no columns (test107, `"tableSchema": 1`).
5. **An invalid column `name` is ignored** and the column falls back
   to its title. §5.6 restricts a name to the RFC 6570 variable
   syntax; `"name": "G I D"` with `"titles": "GID"` must produce
   `#GID`, and taking the name verbatim produced `#G%20I%20D`
   (test130).
6. **A cell that fails its datatype gets NO datatype.** `CellResult.
   literals` is now `List (String × Bool)` — the lexical form and
   whether the datatype applies. Emitting `^^xsd:decimal` on
   `"123,,456.789"` asserts something false about the value.

And the one that moved the most: **the XSD numeric lexical spaces are
checked even with no `format`.** The numeric path used to return
`noFormat` whenever no pattern, `groupChar` or `decimalChar` was
stated, so nothing was checked and every such cell got its base's
datatype — `3.2` as an `xsd:integer`, `123.456E7` and `NaN` as
`xsd:decimal`. `isIntegerLexical` / `isDecimalLexical` /
`isDoubleLexical` now decide, and grouping characters must SEPARATE
digits (two in a row is a validation error the corpus states in
words). `datatype.format` is also read as an OBJECT, which is where
`groupChar` actually lives.

📊 MEASURED, csv2rdf: **123 pass, 82 fail, 0 comparison-gave-up, 5
skip (out of 210 attempted)** — from 100 at the previous landing.

Two `FormatsTests` guards had to be CORRECTED rather than extended,
and both were pinning behaviour rather than the specification:
`formatConvert "integer" none … "42" == .noFormat` (it is `.valid`,
and the `noFormat` answer is why `3.2` reached the output typed) and
the date guards that asserted date formats were out of scope.

### CSVW: value constraints, the remaining lexical spaces, and where
the scaling suffix lives (2026-08-22)

Five more, same loop:

1. **The scaling suffix may be on the VALUE, not just the pattern.**
   §6.4.2 lets a cell carry its own `%` / `‰`, so `123456.789%` under a
   bare `{"groupChar": ","}` still divides by a hundred. Reading the
   suffix only from the pattern left the value a hundred times too
   large with the right datatype on it (test170).
2. **A pattern that does not contain the grouping character FORBIDS
   grouping.** `##0` says "no grouping", so `1,234` is not a number in
   that format and must not be silently regrouped (test286).
3. **The default `propertyUrl` uses SIMPLE expansion, not fragment
   expansion.** A column name is a template VARIABLE VALUE, so
   reserved characters are escaped: a column titled `##0` gives
   `#%23%230`, and passing `#` through produced `###0`, which
   truncates the fragment.
4. **The §5.11.2 value constraints are checked**, on the normalised
   form, with `decimalCompare` doing an EXACT decimal comparison
   rather than a float round trip. `minimum: 5` against a cell of `4`
   makes the cell invalid, so it keeps its text and loses the datatype
   (test203).
5. **`duration` and the date/time bases have lexical spaces even with
   no format.** A duration `format` is an XSD regex this slice cannot
   run, but the LEXICAL SPACE is checkable either way — which is what
   stops `Foo` becoming an `xsd:duration` (test279). Likewise a
   date/time column with no format must already be in the canonical
   XSD form; before this it accepted any text at all and stamped
   `xsd:date` on it.

📊 MEASURED, csv2rdf: **153 pass, 52 fail, 0 comparison-gave-up, 5
skip (out of 210 attempted)** — from 123.

Two more `FormatsTests` guards were CORRECTED rather than extended
(`formatConvert "date" none … == .noFormat`, and the duration one).
That is now FOUR guards in this file that pinned the absence of a
check. A `noFormat` return is not a neutral answer: it means "emit
this text under the column's datatype unchecked", and every one of
those guards was recording a wrong triple as expected behaviour.

### CSVW: integer ranges, column-name escaping, decimal patterns
(2026-08-22)

1. **An integer base's RANGE is part of its lexical space.** `1234` is
   not an `xsd:byte` at all, and emitting it with that datatype
   asserts a value the type does not contain. `integerBounds` carries
   the twelve bounded bases (test172).
2. **A column name in a default `propertyUrl` escapes `-` too.**
   `test246` names its columns `yyyy-MM-ddTHH:mm:ss.S` and expects
   `#yyyy%2DMM%2DddTHH%3Amm%3Ass.S` — the hyphen IS escaped while the
   dot is not, which is neither RFC 3986's unreserved set nor simple
   expansion. `encodeColumnName` records the set the corpus actually
   uses, with the test that measured it.
3. **A decimal PATTERN constrains digit counts and grouping
   positions**, not just the separator character. Sixteen tests
   (288–303 and 160) supply a perfectly good number and expect it
   REJECTED for not matching its column's pattern: `1` against
   `#,#00`, `12.34` against `#0.#`, `1,234,567` against `#,##,#00`
   (whose secondary group is 2, so the right shape is `12,34,567`).
   `parseNumPattern` / `regroup` / `matchesNumPattern` implement the
   UAX #35 subset the corpus uses; prefixes, suffixes, quoting and the
   negative subpattern are NOT read, and that is stated rather than
   guessed at.

📊 MEASURED, csv2rdf: **179 pass, 26 fail, 0 comparison-gave-up, 5
skip (out of 210 attempted)** — from 153.

Running total for the day: 9 pass out of 9 attempted → 179 pass out of
210 attempted, with the denominator itself growing from 9 to 210.

### CSVW: five more rules, and one where "cannot check" is the answer
(2026-08-22)

1. **The exponent marker in a number pattern is LITERAL.** A pattern
   written with `E` requires an `E` in the value: `10.10e10` does not
   match `0.00E0` (test157).
2. **An explicit `@id` on a datatype object names the literal's IRI**,
   overriding the one its `base` would give (test242).
3. **A column title must be LANGUAGE-COMPATIBLE to name its column.**
   A document with `"lang": "de"` whose column states
   `"titles": {"en": "On Street"}` has no usable title there, so the
   column is `_col.2`. `langCompatible` implements the BCP 47
   truncated match, with `und` matching anything (test148).
4. **`X` is the ISO 8601 BASIC timezone form**: hours, with minutes
   OPTIONAL. Reading only the hours left `+0800` with a trailing `00`
   the pattern could not match (test190).
5. **A common-property NAME must be an ABSOLUTE IRI**, not resolved
   against the document base. `"foo": "bar"` became `<…/tests/foo>
   "bar"` (test093) and `"@type": "Table"` became an `rdf:type` to
   `<…/tests/Table>` (test263) — predicates the documents never wrote.
   `absoluteIri?` requires a scheme; `@id` VALUES still resolve
   relatively, because those really are references.

And one where the honest answer is a refusal: **a `duration` with a
`format` gets NO datatype.** The facet is an XSD regex and this slice
has no engine for it, so the value cannot be SHOWN to satisfy it.
test194 states `"format": "^.$"`, which no duration can match, and
expects every cell plain — asserting the datatype anyway would claim a
validity the code did not establish. With NO format the lexical space
is still checkable, and it is what stops `Foo` becoming an
`xsd:duration`.

📊 MEASURED, csv2rdf: **186 pass, 19 fail, 0 comparison-gave-up, 5
skip (out of 210 attempted)** — from 179.

### CSVW: four more value rules (2026-08-22)

1. **The `S` count in a time pattern is the fraction-digit count,
   exactly.** `HH:mm:ss.S` does not accept `15:02:37.143`; reading the
   whole digit run let three digits through a one-digit pattern
   (test247).
2. **A `length` facet on a binary type counts decoded BYTES.**
   `base64Binary` with `length: 19` describes the nineteen bytes of
   "Send reinforcements", whose base64 text is twenty-eight characters
   (test195). `facetLength` does the per-base conversion.
3. **A BCP 47 primary subtag is 2–8 alphabetic characters.** A single
   letter is reserved, which is what makes `a-bad-language` invalid
   despite every subtag being well formed on its own — and the check
   now applies to a common property's `@language` as well as to a
   column's `lang` (test073).
4. **A bare `@type` names a CSVW CLASS.** The metadata document's
   `@context` IS the CSVW vocabulary, so `"@type": "Table"` means
   `csvw:Table`; resolving it against the document base produced an
   `rdf:type` to `<…/tests/Table>` (test263).

📊 MEASURED, csv2rdf: **190 pass, 15 fail, 0 comparison-gave-up, 5
skip (out of 210 attempted)** — from 186.

What is left, characterised rather than counted: six tests need
metadata MERGING (§5.1 — file, link and user metadata combined with a
defined precedence: 017, 034, 035, 036, 148, 149), two need the
`notes`/table-group shape 306/307 expect, and the rest are single
quirks (an invalid `@id` making the table node the document URL in
102; a double's exponent case in 158). The five skips are tables the
corpus does not ship — the metadata names a `-ref.csv` that is not in
the tree.

### CSVW: metadata discovery order, schema links, ordered lists,
rowTitles (2026-08-22)

1. **Metadata DISCOVERY has an order** (§5.2), and the runner was
   taking the LAST `implicit` entry. The order that fits the corpus:
   user metadata (`option.metadata`) > a `linked-metadata.json`
   standing for the `Link` header > the file-specific
   `<name>.csv-metadata.json` > the directory `csv-metadata.json`.
   Picking the wrong one applies a whole different description
   (test016 / test017 pull in opposite directions, which is what
   forced the order out into the open).
2. **A `tableSchema` given as a URL is a LINK, and it resolves.** The
   parse stays pure and records `schemaRef`; the runner reads the
   document and re-parses it as a schema. Fetching is the only part
   that needs I/O, and it belongs outside the pure module.
3. **`"ordered": true` makes a list-valued cell an RDF COLLECTION.**
   csv2rdf §5 says such a column's values keep their relative order,
   and only `rdf:first`/`rdf:rest` records that. Emitting them as
   separate triples loses the order silently — the count is the same
   and the graph says less (test306/307).
4. **`rowTitles` puts `csvw:title` on the ROW node** for each named
   column's value (test235/236).

📊 MEASURED, csv2rdf: **194 pass, 10 fail, 0 comparison-gave-up, 6
skip (out of 210 attempted)** — from 190.

📊 NO REGRESSION, re-measured: rdf manifest **1031 pass, 0 fail (out of
1031)**; SPARQL 1.1 **601 pass, 0 fail, 30 unsupported (out of 631)**.

The whole day, in one line: **csv2rdf went from 9 pass out of 9
attempted to 194 pass out of 210 attempted**, and the denominator grew
from 9 to 210 because the metadata parse now exists. Of the ten
remaining failures, four are single-quirk (an invalid `@id` naming the
table node, a double's exponent case, two title-language edges) and
the rest need multi-document metadata MERGING rather than selection.
The six skips are tables the corpus does not ship.

### csv2json: a second real conformance runner on the same pipeline
(2026-08-23)

`CSVW/JsonDoc.lean` + `Harness/CsvwJsonRun.lean` (`lake exe
l4csvw-json`) run the OTHER csvw suite — `manifest-json.jsonld` — over
the same annotated table the RDF pipeline builds. `Json.lean` already
had the row and document SHAPES; this is what joins them to a metadata
document and a CSV file.

📊 FIRST MEASURED RESULT: **181 pass, 23 fail, 6 skip (out of 210
attempted)** on the very first run, then **185 pass, 19 fail** after
one fix. That is what the shared pipeline bought: every metadata rule
paid for on the RDF side arrived working here.

Three things csv2json does NOT share with csv2rdf, each of which would
be a wrong answer if assumed:

1. **Keys are not always column names.** A cell is keyed by its column
   name when the column has the DEFAULT `propertyUrl`, and by the
   property URL otherwise — COMPACTED against the standard prefixes,
   so `http://schema.org/latitude` becomes `schema:latitude` while
   `http://www.geonames.org/ontology#countryCode`, which no prefix
   covers, is written out whole. Both forms appear in one object in
   test031, which is what makes the rule visible.
2. **Values are not always strings.** A numeric column's value is a
   JSON NUMBER and a boolean column's a JSON BOOLEAN — `42.546245`,
   not `"42.546245"`. A value that failed its datatype stays a string,
   because the string is what the file said and the number is a claim
   about it.
3. **Members that share a key MERGE into one array.** Two columns may
   carry the same `propertyUrl`, and csv2json puts their values in one
   member in relative order (test305/306/307). Emitting a second
   member of the same name produces an object that is not well formed
   as a mapping.

The comparison is STRUCTURAL: object members are a SET of pairs, array
items a SEQUENCE. That distinction is the point — csv2json fixes the
order of `row` and `describes` (which is why `"ordered"` columns exist
at all), while object member order carries no meaning. Comparing raw
text would fail correct output on whitespace; ignoring array order
would pass output that had lost the ordering the specification
requires. JSON NUMBERS are compared as numbers, not as source text, so
`1.0` and `1` agree.

### csv2json: four rules the JSON output does not share with the RDF
one (2026-08-23)

1. **A common property's NAME must be an absolute IRI here too.** A
   bare `foo` or `titles` is not a property, and writing it out as a
   member states something the document did not (test093, test275) —
   the same rule the RDF side already enforced, applied on the JSON
   side where it was missing.
2. **`rdf:type` is written `@type`, and its value IS compacted.**
   `"@type": "schema:MusicEvent"`, not an `rdf:type` member holding an
   absolute IRI (test032). Everywhere else a `valueUrl` VALUE stays
   absolute and only the KEY is compacted — `schema:about` is a member
   name, never a value (test038).
3. **A referenced object is NESTED, not listed alongside.** csv2json
   §6 inlines a `valueUrl` that names another cell's `aboutUrl`, so
   the event in test032 carries its place and its offer as nested
   objects. Listing all three side by side gives a `describes` array
   of the right length with the structure flattened out of it.
4. **JSON numbers compare as NUMBERS, exponent expanded.** `0.0e0`,
   `0.0` and `0` are one value; the parser keeps the source text, so
   comparing it failed correct output for a reason that is not a
   defect. The expansion is exact digit shifting, not a float round
   trip.

📊 MEASURED, csv2json: **195 pass, 9 fail, 6 skip (out of 210
attempted)** — from 185. csv2rdf unchanged at 194 pass, 10 fail.

### CSVW: the 58 negative tests, and the cross-check that keeps the
validator honest (2026-08-23)

Both runners now score the NEGATIVE tests, which were reported as "not
attempted" all along: a `NegativeRdfTest`/`NegativeJsonTest` asserts
that the metadata is REJECTED, so it is scored by
`CSVW.Validate.validate` rather than against an expected document.

`Validate.lean` was a thin slice — it caught 9 of the 58. The suite
names every rule it wants, so they went in as a set:

- `@id` must not be a blank node, on every object AND inside a common
  property; `@type` must be a term, a prefixed name or an absolute URL
  (`"not a link"` is none of the three), and never a blank node.
- `tables` is required, must be an array, must not be empty, and must
  hold objects; a table must have a `url`.
- Common properties may carry only `@id` / `@type` / `@value` /
  `@language`. `@context`, `@list`, `@set` and any other `@`-name
  reject. `@value` is exclusive: not both `@type` and `@language`, and
  no other member beside it; `@language` with no `@value` has nothing
  to tag.
- Datatype facets: `length` inside its own min/max, bounds that do not
  cross, inclusive and exclusive bounds mutually exclusive on a side,
  a non-empty range, a length facet only on a length-bearing base, a
  value range only on an ordered one. A datatype `@id` must not be a
  blank node NOR the URL of a built-in datatype — redefining
  `xsd:string` is not a definition.
- Schema structure: column names unique, virtual columns after real
  ones, a foreign key carrying only `columnReference` and `reference`,
  its source columns existing, and its DESTINATION table and columns
  existing in the same document.
- `@context` may carry only `@base` and `@language`.

📊 MEASURED: **58 pass, 0 fail (out of 58)** on both suites, from 9.

**The cross-check is the part worth keeping.** A negative score can be
bought with rules that reject everything, and nothing in the negative
column would ever disagree. So each runner also validates every
POSITIVE test's metadata and counts the documents the validator
wrongly rejects. It fired immediately at 3, and all three were the
same mistake: treating a WARNING as an error. `foreignKeys` given as a
non-array or holding a non-object member, and `titles` keyed by an
invalid language, are `ToRdfTestWithWarnings` — the document still
converts. That is the distinction `Validate.lean`'s own header says it
exists to preserve, and the new rules had broken it within the hour.

📊 CROSS-CHECK now reads **0** on both suites.

📊 TOTALS over the whole manifest, no longer over a subset:
**csv2rdf 252 pass, 10 fail, 6 skip (out of 270)**;
**csv2json 253 pass, 9 fail, 6 skip (out of 270)**.

### JSON Schema draft-07: the third real conformance runner
(2026-08-23)

`Harness/JsonSchemaRun.lean` (`lake exe l4jsonschema`) runs the 770
vendored draft-07 tests through `JSONSchema/Validate.lean`. The suite's
own `manifest.json` lists the files; each holds
`{description, schema, tests: [{data, valid}]}` groups.

📊 FIRST MEASURED RESULT: **407 pass, 1 fail (out of 408 decided), 362
undetermined**. `Validate.lean` was a slice: `type`, `const`, `enum`,
the numeric keywords, lengths, `items`, `required`, `properties`,
`allOf`, `anyOf`, `not` — and nothing else.

Now: **726 pass, 0 fail (out of 726 decided), 44 undetermined (out of
770)**.

What went in: `pattern` and `patternProperties` (on the verified
`Regex` engine already in the tree), `additionalProperties`,
`additionalItems`, `items` in its TUPLE form, `uniqueItems`,
`contains`, `minProperties` / `maxProperties`, `propertyNames`,
`oneOf`, `if`/`then`/`else`, `dependencies` in both forms, and `$ref`
with JSON-pointer resolution plus a document registry.

Three things worth carrying:

1. **`$ref` IGNORES its siblings** (draft-07 §8.3). Applying them
   alongside the referenced schema makes a document stricter than it
   says it is, and `ref.json`'s "ref overrides any sibling keywords"
   measures exactly that. It was the single decided-and-WRONG verdict
   in the whole suite.
2. **A `$ref` is a URI before it is a pointer.** `#/definitions/foo%22bar`
   names the member `foo"bar`; tokenising without percent-decoding
   looks for a member spelled with the escape and finds nothing.
3. **The three-valued verdict is what makes the number readable.** An
   UNDETERMINED test is counted separately, never as a pass and never
   as a failure. The first run's 362 undetermined were the honest
   report of a slice; folding them into `pass` would have read as
   "770 pass" for a validator that decided fewer than half of them.

The residue is NAMED: every draft-07 assertion keyword is implemented,
so the 44 are not a missing keyword. They are `$id` base-URI
resolution — a `$id` inside a document changing the base its `$ref`s
resolve against. That needs base tracking through the schema tree,
which is a distinct piece of work rather than another keyword.

The runner also attributes an undetermined verdict only to names in
KEYWORD position: inside `properties` the members are property NAMES,
and the first version reported `foo`, `bar` and `tilde~field` as
unimplemented keywords, which is noise that hides the real gap.

### Content MathML: the fourth conformance runner, and the arithmetic
it needed (2026-08-23)

`MathML/FromXml.lean` reads Content MathML markup into the `Expr` that
`Core.lean` evaluates, and `Harness/MathMLRun.lean` (`lake exe
l4mathml`) runs the 56-test corpus.

📊 **56 pass, 0 fail, 0 markup-not-read (out of 56)**.

The XML is read by the project's OWN verified parser
(`L4Factoidal.XML.Parser`), not a tag scanner written for the
occasion. Entity references, CDATA, comments and attribute
normalisation are the parser's job, and a second looser reader of the
same syntax is a second set of bugs.

`Core.eval` had the four operations and the six relations. The corpus
needed more, and each addition is exact or it REFUSES:

- `power` with a NEGATIVE integer exponent is the reciprocal; with a
  non-integer exponent it refuses, because that is not a rational
  power in general.
- `root` takes an optional `<degree>` and returns the exact `n`th root
  of a rational — both numerator and denominator must be perfect `n`th
  powers. `root` of 2 is `undef`, not 1.414…: Content markup denotes a
  VALUE, and a nearby float would state something the expression does
  not.
- `abs`, `quotient`, `rem`, `factorial`, `gcd`, `max`, `min` — the
  integer ones refuse a fractional argument rather than truncating it.
- **Relations CHAIN.** `eq` of three values holds when every adjacent
  pair does. Reading only the first two would call `2 = 2 = 3` true.

`undef` is an expected ANSWER in this corpus, not a skip: six tests
assert it, and the runner scores them like any other. It also
separates "the markup did not READ" from "the value is undefined" —
one is a gap in the front end, the other is the answer, and reporting
them as one number would hide a parser gap behind a correct-looking
score.

A `<cn>` reads `type="integer"` and `type="real"` through ONE decimal
reader: an integer is a decimal with no fraction, and reading them
apart would reject `type="integer"` written as `42.0`. `1.5e2` is
exactly `150`, via digit shifting rather than a float.

### The W3C XML Conformance Suite, scored (2026-08-23)

`XML/ConfProbe.lean` read a list of paths from standard input and
printed a verdict per file. That is a PROBE: it has no expected answer
to compare against, so it could not say whether a verdict was RIGHT.
Run with no input it reported "0 accepted, 0 rejected (out of 0
files)" — a clean-looking line describing nothing.

`Harness/XmlConfRun.lean` (`lake exe l4xmlconf`) reads the suite's own
sub-manifests — the `<TEST>` elements with their `TYPE` and `URI` —
and scores each verdict against what the suite says it should be. The
manifests are parsed by the same verified parser the tests exercise; a
separate manifest reader would be a second implementation of the
syntax under test.

📊 FIRST MEASURED RESULT: **1477 pass, 753 fail (out of 2230 in
profile)**, plus 28 optional-behaviour, 63 XML 1.1 and 56 non-UTF-8
tests reported OUT OF PROFILE rather than scored.

Three things the scoring had to get right, each of which would move
the number by hundreds:

1. **A `valid` and an `invalid` case must BOTH be ACCEPTED.**
   `invalid` means "violates the DTD", which a NON-VALIDATING parser
   is not asked to notice. Scoring `invalid` as "must reject" would
   have counted 57 correct verdicts as failures.
2. **Out of profile is not failure.** XML 1.1 is a different language
   and this parser reads UTF-8 only. Counting those as failures
   understates the parser; folding them into passes overstates it, so
   they are their own line.
3. **Three sub-manifests are ENTITY BODIES, not documents.**
   `sun-not-wf.xml` is a run of sibling `<TEST>` elements with no
   single root, because `xmlconf.xml` includes it as an external
   entity. Rejecting it IS the right verdict on it as a document, so
   the runner supplies the element the entity is included into rather
   than loosening the parser. Without that, three manifests and 159
   tests vanished from the denominator behind a one-line notice —
   exactly the silent narrowing this project keeps paying for.

🔴 THE GAP IS NAMED: of the 753 failures, **674 are `not-wf` documents
this parser ACCEPTS**, and they are almost all malformed INTERNAL DTD
SUBSETS — `<!ENTITY foo PUBLIC "id">` with no system id, a comment
inside a declaration, `<!ATTLIST doc a1 NMTOKEN v1>` with a bare
default, an `<![INCLUDE[ ]]>` in the internal subset. `parseIntSubset`
skips the subset loosely instead of parsing its grammar. The other 79
split into 36 documents wrongly rejected and the remainder.

That is one defect, not 674, and it is the next XML increment.

### XML: the internal DTD subset, parsed instead of skipped
(2026-08-23)

`parseIntSubset` stepped over `<!ELEMENT`, `<!ATTLIST`, `<!NOTATION`
and anything else beginning `<!` by scanning to the next `>` outside
quotes. That accepts a malformed declaration, and the W3C conformance
suite is largely made of them. It was ONE defect behind 674 wrong
verdicts.

The productions are now the grammar, and they REJECT. They do not
build a DTD model — this parser stays NON-VALIDATING, so a declaration
is checked for shape and then discarded.

- `[75] ExternalID` — the `PUBLIC` form REQUIRES its system literal.
  `<!ENTITY foo PUBLIC "some public id">` is malformed.
- `[12] PubidLiteral` — its character repertoire is restricted, and a
  character outside it is an error rather than a curiosity.
- `[45] elementdecl` with a REAL `[46] contentspec`, and `[52]
  AttlistDecl` with a real `[54] AttType` and `[60] DefaultDecl`. A
  bare token is not a default.
- `[82] NotationDecl`, whose `PublicID` form takes NO system literal —
  the one place `PUBLIC` differs from `ExternalID`.
- `[47]–[51]` content models as a GRAMMAR, not a balanced-paren blob:
  a model may not mix `,` and `|`, an occurrence indicator binds with
  no whitespace before it, and `[59] Enumeration` takes `|`, so
  `(a,b,c)` is an SGML-ism rather than an attribute type.
- `[61] conditionalSect` is an EXTERNAL-subset production. An
  `<![INCLUDE[` in the internal subset is a well-formedness error.

📊 MEASURED: **1477 → 1706 pass, 753 → 524 fail (out of 2230 in
profile)**.

Two rules had to be got exactly right, and the runner caught both
within minutes of writing them:

1. **`(#PCDATA)*` is legal with NO names.** `[51]`'s first alternative
   allows zero names before `)*`, so both `(#PCDATA)` and `(#PCDATA)*`
   are in the grammar. Requiring a name before the `*` rejected eight
   documents the suite calls valid — a strictness regression that a
   suite-less change would have shipped.
2. **A `valid` case must still be ACCEPTED.** The whole point of the
   new strictness is `not-wf`; the 42 documents still wrongly rejected
   are unchanged from before this landing, and every one of them is an
   EXTERNAL entity reference this parser deliberately does not load.

No regression: rdf manifest 1031 pass, 0 fail; csv2rdf 252 pass of
270. The XML parser feeds RDF/XML, so those are the numbers that would
have moved first.

Residue, named: 482 `not-wf` documents still accepted (mostly external
DTD subsets and parameter-entity replacement text, which this parser
does not read) and 42 `valid` documents rejected for the same reason
from the other side. Both are the external-entity boundary, not the
internal-subset grammar.

### ShEx validation scored, and the quadratic JSON parser it exposed
(2026-08-23)

Two new modules and a runner:

- `ShEx/FromJson.lean` — ShExJ (the JSON serialisation) into the
  `Schema` `Schema.lean` defines. The corpus ships BOTH forms for
  every schema (`0.shex` and `0.json`), and ShExJ is the
  specification's own abstract syntax written down. A ShExC parser is
  separate work; the two are not in tension, because a ShExC parser
  produces the same `Schema`.
- `ShEx/Satisfies.lean` — `satisfies(n, se, G)` with the SCHEMA in
  scope, so shape REFERENCES resolve. `Shapes.lean` stops at a
  reference and says so in its header; that is the right boundary for
  a module without the schema, but the suite is largely made of
  references, so nothing above it could be scored. The generalisation
  is ONE parameter — the value check — and `Shapes.lean`'s own
  functions are unchanged, so the EXTRA/CLOSED distinction its header
  exists to keep straight is reused, not re-derived.
- `Harness/ShExRun.lean` (`lake exe l4shex`).

📊 MEASURED: **889 pass, 249 fail (out of 1138 decided)**, 44 not read
(out of 1182).

🔴 THE FIND: the runner did not finish in TEN MINUTES, and the cause
was not ShEx. `JSON/Parser.lean` indexed a `List Char` by position, so
`charAt?` walked the list and the parser was QUADRATIC in the input.
The ShEx manifest is 747 KB. Converted to an `Array Char` — the same
choice `XML/Parser.lean` already made, for the same reason, with its
header saying so — the run went from **no result after 600 seconds to
2.9 seconds**.

That defect was in a shipping module, on the path of every
JSON-driven runner in the tree, and no test caught it: the CSVW
manifests are small enough that the quadratic cost read as "a bit
slow". It took a 747 KB input to make it a hang.

The correctness evidence SURVIVED the change. `JSON/Theorems.lean`
inducts over `List Char` structure; restating two theorems over
`(… : List Char).toArray` was the whole repair, and
`stringSegments_plain` — the general round-trip induction over a body
of ANY length — still holds. A rewrite that had to drop it would have
been a bad trade at any speed.

`refDepth` is 6, and small on purpose: `fuel` is not a step count.
Every level re-checks each arc's value expression and `eachOf`
re-matches each sub-expression against the whole neighbourhood, so the
work grows like a branching factor to the fuel. A first attempt at 24
did not finish either.

No regression: csv2rdf 252 pass of 270, csv2json 253 of 270, JSON
Schema 726 pass of 726 decided, MathML 56 of 56.

---

## Schematron: an XPath 1.0 subset, and 8 pass, 0 fail (out of 8)

`Schematron/Validate.lean` was ported early and left TWO parameters
open — `select` (does a rule's `@context` claim this node?) and
`evalTest` (what does this `@test` evaluate to?) — because the purity
doctrine keeps host services as arguments rather than a global
registry. Nothing supplied them, so the module had never met a
document. Three modules close that:

- `XPath/Mini.lean` — an XPath 1.0 SUBSET over the project's own XML
  tree. Its header states the accepted grammar in full and the ten
  functions it knows. Everything else REFUSES with a reason, and the
  refusal becomes `Schematron.TestResult.undecided`.
- `Schematron/FromXml.lean` — reads a `.sch` into `Schematron.Schema`.
  Names are matched on the LOCAL part, because the XML parser is
  deliberately non-namespace and a Schematron document writes
  `sch:pattern`.
- `Harness/SchematronRun.lean` (`lake exe l4schematron`).

📊 MEASURED: **8 pass, 0 fail (out of 8 decided)**, 0 undecided (out
of 8 cases in `third_party/testing/schematron/manifest.json`).

🔴 THE FIND, again in the shape this port keeps producing: **both bugs
returned a confident answer of the right type.** Neither crashed,
neither refused, and the runner counted both as decided.

1. `takeName` used `takeWhile isNameC`, and `:` is a name character
   because a QName writes `sch:pattern`. So `preceding-sibling::row`
   came back as ONE name and parsed as a CHILD step looking for an
   element literally called `preceding-sibling::row`. No document has
   one, so `count(…)` was 0, `0 < 1` was TRUE, and the assertion that
   should have fired reported a clean document. A misparse that
   yields a DEFINITE answer is worse than one that refuses: the
   refusal is counted apart, the wrong answer is counted as a pass.
2. `stepFrom` located the context node among its parent's children
   with `findIdx? (· == ctx)` — a STRUCTURAL comparison. `<row/><row/>`
   are equal VALUES, so the second row was found at index 0 and both
   rows reported zero preceding siblings. A sibling position is
   IDENTITY, not a value; `resolvePath` now carries the index, and the
   ancestor chain carries each ancestor's index too.

Bug 1 masked bug 2: with the axis misparsed, the identity defect could
not show. Fixing the parse turned one silent pass into a visible
failure, which is the only reason the second bug was found at all.

Both are pinned by `#guard` in `XPath/MiniTests.lean`, each with the
wrong answer it produced written next to it. `FromXmlTests.lean` pins
the reader, including that `assert` and `report` survive the read as
DIFFERENT things — the inversion `Validate.applyAssertion` depends on.

The undecided count is 0 here, and that is a fact about this corpus,
not a claim about XPath. Eight cases use `count`, `not`, `false`,
attribute tests, a child path, and one reverse axis. `book[1]`,
`substring-before`, and an ordering comparison against a string are
all refused — pinned as refusals, so the boundary is a test rather
than a promise.

---

## JSON Schema draft-07: 770 pass, 0 fail (out of 770), 0 undetermined

The suite was at 726 pass, 0 fail (out of 726 decided) with **44
undetermined**. Both causes were the same shape as everything else in
this port — the validator was RIGHT about everything it decided, and
the gap was in what it declined to decide.

**32 of the 44: `$id` and the base URI (draft-07 §8.2).** A `$ref` was
resolved as a JSON pointer into the top document, or looked up whole
in a registry. Neither is what draft-07 says: an `$id` sets the base
URI for everything below it, so a relative `$ref` means something
different depending on WHERE it is written. Three rules that are not
string concatenation:

- an `$id` composes with the NEAREST enclosing base, so `a.json` →
  `b/c.json` → `d.json` publishes `http://example.com/b/d.json`;
- a sibling `$ref` cancels the `$id` (§8.3 makes every keyword beside
  a `$ref` inert, `$id` included);
- a `$ref` is validated in the referenced schema's OWN scope, so a
  pointer written there points into ITS document. Substituting the
  destination and keeping the pointing document's scope is the
  suite's "naive replacement of `$ref` with its destination is not
  correct".

`collectIds` now registers EVERY `$id` in a document — anchors
(`"#foo"`) under `<base>#foo`, documents under their resolved URI —
and `validateIn` carries the base in force. A URN base
(`urn:uuid:…`) takes an absolute reference whole: RFC 3986 relative
resolution is not defined against a URN.

The third rule bit while writing its own `#guard`. The first draft
wrote `{"$id": "b.json", "$ref": "#/definitions/y"}` — which §8.3
makes unresolvable, because the sibling `$ref` cancels the very `$id`
the outer ref needs. The guard failed, the example was wrong, and the
comment now says why the inner `$ref` sits under an `allOf`.

**12 of the 44: a count bound written as a decimal.** `{"maxItems":
2.0}` is `2`. Six keywords matched `instRat v` against `some (n, 1)`
and returned `unsupported` for anything else, so six groups of the
suite got no verdict on a perfectly ordinary schema. `countAgainst`
scales the COUNT by the bound's denominator instead of turning the
bound into a float, so `3 ≤ 2.0` is decided as `30 ≤ 20` and the
arithmetic stays exact.

The runner now NAMES each undetermined group with how many of its
tests are in it, rather than printing a total. That is what turned
"44 undetermined, presumably remote refs" into two distinct causes in
one run — the count alone had been read as one gap for weeks, and one
of the two had nothing to do with `$ref` at all.

No regression: csv2rdf 252 pass, 10 fail (out of 270), csv2json 253
pass, 9 fail (out of 270), MathML 56 pass, 0 fail (out of 56),
schematron 8 pass, 0 fail (out of 8).

---

## CSVW: metadata discovery, `@base`, and exact-tag column naming

csv2rdf was 252 pass, 10 fail, 6 skip (out of 270); csv2json was 253
pass, 9 fail, 6 skip. All six skips read "table file not found", which
looks like a missing fixture and was not one. Three separate rules:

**§5.2 — discovered metadata that does not reference the requested
file MUST be ignored.** Five tests (117, 119, 120, 122, 123) put a
`csv-metadata.json` beside a CSV it does not describe. The runner
picked it up, the converter went looking for the table that document
DID name, and the run reported a missing file. The candidates are now
kept in discovery order — `Link` header, then
`<file>-metadata.json`, then the directory's `csv-metadata.json` —
and the first one that references the request wins; if none does, the
CSV is converted on its own. test122 and test123 need exactly that
fall-through: their first candidate does not describe the file and
their second does.

`describesTable` is in `CSVW/Pipeline.lean`, not in the runner. The
runner's job is to read candidate files; which one describes the
request is the specification's decision.

**§5.1 — `@base` in the `@context` moves the document's base URL.**
`Ctx.base` was parsed and then never used. test273 sets `"@base":
"test273/"` on a metadata document at the top level, so its `"url":
"action.csv"` names `test273/action.csv`. Disk paths now come from
resolving the url against the effective base and stripping the
suite's base URL, instead of concatenating a directory prefix.

That change exposed a second defect in the same place: the no-metadata
fallback built its table from the manifest's RELATIVE action name and
resolved it against a base that already ended in it, giving
`tests/test119/test119/action.csv`. The file was not found, and had it
been found the emitted subject would have carried the doubled path.
The fallback now takes the absolute requested URL.

**§5.6 — the column NAME takes a title whose language tag EQUALS the
document's.** The port used `langCompatible`, which truncates to the
shorter tag — so `"lang": "en"` accepted an `en-US` title (test149)
and, before the inherited-language fix below, `"lang": "de"` accepted
an `en` one (test148). Two different rules had been conflated:

* matching a CSV HEADER against a column's titles uses truncated
  matching, which is what the comment quoted in both tests describes;
* deriving the column NAME takes "the first titles value having the
  same language tag as default language" — an exact tag.

An untagged title still works, and not by an exception: §5.1.3 says a
natural-language property written as a plain string carries the
default language, so its tag equals the document's by construction.

A third fix was needed to see the second: `nameOf` read the language
from the `@context` only, so a table-level `"lang": "de"` was
invisible and every title matched. The language is the one INHERITED
at that column (§5.1.1), and the context language is the fallback.

📊 MEASURED: csv2rdf **260 pass, 8 fail, 0 skip (out of 270)**;
csv2json **261 pass, 7 fail, 0 skip (out of 270)**. Validator
cross-check 0 in both — no positive test's metadata is wrongly
rejected. Every skip is gone from both runners.

---

## CSVW value formats: four defects, all with the right triple count

csv2rdf went 260 → **264 pass, 4 fail, 0 skip (out of 270)**; csv2json
261 → **262 pass, 6 fail, 0 skip (out of 270)**. Every one of the four
produced the RIGHT NUMBER of triples with the wrong content, which is
the failure shape this port keeps meeting.

1. **A duration `format` is a regular expression, and was not being
   read as one.** tabular-metadata §5.11.3 says so outright. The
   branch returned `.invalid` for ANY stated format, on the ground
   that satisfaction could not be shown without an engine. The tree
   HAS one (`Regex.regexMatch`, `fn:matches` semantics — a search
   with `^`/`$` as anchors). Refusing to decide and deciding NO
   produce the same output here, a plain literal, which is exactly
   why the shortcut survived: nine rows of test193 were reported
   plain and the count never moved.

2. **A secondary group size only exists with two separators.**
   `#,#00` under UAX #35 means groups of three; the leading `#` is
   the "and any further digits" placeholder, not a size. Reading it
   as a secondary size of ONE demanded `1,2,3,4,567`, so
   `1,234,567` came out as a plain string with the right predicate
   and no datatype (test282). `#,##,#00` is the genuine case:
   primary 3, secondary 2.

3. **A written `+` was stripped unconditionally.** `+` is in the
   `xsd:decimal` lexical space, and test283's `+0` column expects
   `"+1"^^xsd:decimal` while its `%000` column expects `%+123` to
   become `1.23`. The sign is now dropped only where SCALING rebuilds
   the number anyway.

4. **A `double` writes its exponent marker lowercase.** test158
   expects `"0.0e0"^^xsd:double`, and no expected file in the corpus
   uses `E`. This is a stated DEVIATION from XSD's canonical mapping,
   not an instance of it: canonical `double` writes `E` and
   normalises the mantissa, so `10.10E1` would canonically be
   `1.010E2`. The value is the same either way; RDF literal equality
   is lexical, which is the only reason the difference is visible.

Two existing `#guard`s had to be CORRECTED rather than extended —
`parseNumber "decimal" {} "+42" == .valid "42"` and `parseNumber
"double" {} "123.456E7" == .valid "123.456E7"`. Each pinned the defect
it was written beside. That is now four separate landings in this port
where a guard preserved a wrong answer; the check is always the same
one — does the corpus agree with what this guard says?

Remaining csv2rdf failures: test034 and test035 (a table group whose
output is nearly twice the expected size), test036 (embedded metadata
in the CSV), test102 (`"@id": 1`, where the expected output names the
metadata document as the table node).

---

## csv2rdf: 270 pass, 0 fail, 0 skip — the whole manifest

Five more defects, closing the csv2rdf suite.

1. **`suppressOutput` on a TABLE was honoured by csv2json and ignored
   by csv2rdf.** test034 emitted 105 triples where 60 were expected —
   the two lookup tables it marks `suppressOutput` were converted in
   full. A suppressed table is still READ (other tables' foreign keys
   refer to it) and contributes nothing: no rows, no table node, no
   link from the group.

2. **`@id` on a table was parsed nowhere and used nowhere.** test036
   states `"@id": "http://example.org/tree-ops-ext"` and every triple
   about the table hangs off that IRI instead of a blank node. The
   group's `csvw:table` link has to agree, so the node is computed by
   one function (`tableNodeOf`) that both the link and the triples
   call.

3. **`notes` were not emitted.** A `notes` entry becomes a
   `csvw:note` triple, and its value is read exactly as a common
   property's value is — so it routes through `commonTriples` rather
   than being duplicated. test036's note is a nested `oa:Annotation`
   with its own `oa:hasBody`, which is the nested-node case that code
   already handled.

4. **An explicit `@value` object with no `@language` was being
   language-tagged.** The document's default language applies to a
   BARE STRING; `{"@value": "text/plain"}` is how JSON-LD says "this
   string, untagged". The port re-tagged it and produced
   `"text/plain"@en` where test036 expects `"text/plain"`.

5. **Two manifest entries were never attempted, and the denominator
   never said so.** test116 and test118 name `…csv?query`, and the
   entry filter tested `action.endsWith ".csv"`. The query is part of
   the URL — it appears in every emitted IRI, and test118 expects
   `<action.csv?query#name>` — and is stripped only where a URL
   becomes a path on disk. Both then pass with no further rule:
   test116's file metadata describes `test116.csv`, which is NOT the
   requested `test116.csv?query`, so §5.2 ignores it; test118's
   directory metadata writes `"url": "action.csv?query"` and matches.

One rule here is OBSERVED FROM THE CORPUS rather than derived from
the specification, and is labelled as such in the source: an `@id`
that is present but not a string makes the table take the metadata
document's own URL. test102 writes `"@id": 1` under the comment "@id
takes a URI, not an integer" and expects every triple on
`<…/test102-metadata.json>`. The specification says the value is
invalid; it does not say what identity the table then has. Falling
back to a blank node — the obvious reading — gives a graph of the
right SIZE with a different subject.

📊 MEASURED: **csv2rdf 270 pass, 0 fail, 0 comparison-gave-up, 0 skip
(out of 270 manifest entries)** — 212 positive and 58 negative.
Validator cross-check 0. csv2json is at **264 pass, 6 fail, 0 skip
(out of 270)**.

---

## csv2json: 270 pass, 0 fail, 0 skip — both CSVW suites complete

Four defects on the JSON side, after the shared metadata work above
took it from 253 to 265.

1. **`NaN` / `INF` / `-INF` were emitted as bare JSON numbers.** They
   are not JSON numbers, so the document was not JSON at all. That is
   the one defect in this whole run that ANNOUNCED itself — the
   runner's own comparison could not parse the output. Every other
   one produced a well-formed document of the right shape.

2. **A numeric cell kept its lexical form.** csv2json emits a JSON
   NUMBER, and JSON has no lexical space to preserve: `10.10e1` and
   `101.0` are the same number and the corpus writes the second
   (test155). The RDF output does keep the lexical form, because an
   RDF literal's lexical form is part of its identity; a JSON
   number's is not. `resolveExponent` folds the exponent into the
   digits, using the same decimal-point shift the `%` / `‰` scaling
   uses — generalised from `Nat` to `Int` so it can move the point
   right as well as left.

3. **One row title was wrapped in an array.** csv2json writes
   `"titles": "Andorra"` for a single title (test235, test236).

4. **`@id` and `notes` were missing from the table object**, and
   `suppressOutput` was honoured in minimal mode only. The `@id`
   comes from `tableNodeOf`, the same function the RDF path uses for
   the table's subject, so the two outputs cannot disagree about
   which table is which.

📊 MEASURED: **csv2json 270 pass, 0 fail, 0 skip (out of 270 manifest
entries)** — 212 positive and 58 negative, validator cross-check 0.
**csv2rdf stays at 270 pass, 0 fail, 0 skip (out of 270).** No
regression elsewhere: JSON Schema 770 pass, 0 fail (out of 770
decided), MathML 56 pass, 0 fail (out of 56), schematron 8 pass, 0
fail (out of 8).

---

## ShEx: 889 → 1075 pass, and 41 fewer entries unread

Six defects. Five of them made the validator ACCEPT too much, and the
whole of that shows only in the suite's NEGATIVE half — a validator
that accepts everything passes every positive test.

1. **A `datatype` constraint checked the IRI and not the LEXICAL
   SPACE.** ShEx 2.0 §5.4.3 requires both. `"1.0"^^xsd:integer`,
   `"NaN"^^xsd:decimal` and `"+1"^^xsd:negativeInteger` were all
   satisfied — 144 entries. `ShEx/XsdLexical.lean` decides the
   lexical space per datatype IRI, and a datatype it does not decide
   returns `none` rather than a silent `true`, so the gap stays
   countable.

   That module REUSES `CSVW/Formats.lean`'s lexical predicates rather
   than restating them. They live under CSVW because csv2rdf needed
   them first; their proper home is a shared `Xsd` module, and that
   move is deferred to its own landing with the two CSVW suites (270
   pass, 0 fail each) as its gate. A second copy of a lexical space
   drifts silently, which is the cobbling rule #7 forbids.

2. **`pattern`, `totalDigits` and `fractionDigits` were parsed and
   never applied.** The ShExJ reader had all three fields; nothing
   read them. `pattern` goes through `Regex.regexMatch` (`fn:matches`
   semantics), and the digit facets count digits of the VALUE, so
   `007.700` has two total and one fractional.

3. **A stem range's EXCLUSIONS were all read as IRIs.** ShExJ writes
   a bare string, and what it means depends on the range's KIND: an
   IRI in an `IriStemRange`, a literal VALUE in a `LiteralStemRange`,
   a language TAG in a `LanguageStemRange`. Reading every one as an
   IRI made literal and language exclusions match nothing, so the
   excluded nodes were admitted. Exclusions can also be nested STEMS
   (`IriStem` inside an `IriStemRange`), which the old
   `List ObjectValue` could not express at all.

4. **An ordering facet could not compare an `xsd:double`.** The
   literal writes `1.0E2`, the facet writes `100`, and
   `compareDecimal` parsed neither side's exponent — so it returned
   "undecidable", which the caller reports as UNSATISFIED. Twelve
   positive tests failed on values that satisfy their facet.

5. **A `pattern` on a blank node was refused.** The suite states that
   it matches the LABEL (`1nonliteralPattern`). That is not obvious —
   a label is not part of the graph's meaning — so the code says who
   decided it.

6. **41 entries were reported "data Turtle not read", and were.** The
   suite's data files use relative IRIs (`<x> :p1 "p1-0"`) and its
   entries name relative focus nodes (`"focus": "x"`), both relative
   to the data file's own URL. The runner parsed with NO base, so the
   graph was rejected outright. Both now resolve against the
   retrieval URL the manifest's own `@context` gives. A told blank
   node (`"_:abcd"`) and a typed-literal focus
   (`{"@value": "ab", "@type": …}`) are read too — the second had been
   read as a plain string, which is a DIFFERENT term and matched
   nothing.

📊 MEASURED: **1075 pass, 104 fail (out of 1179 decided)**, 3 not read
(out of 1182). Was 889 pass, 249 fail (out of 1138 decided), 44 not
read. The decided denominator grew by 41 because those entries are now
read at all.

The 104 remaining are ShEx 2.1 features, not defects in what is here:
`EXTENDS` / `RESTRICTS` (15), cardinality on nested closed shapes
(12), recursion through a value reference (7), and the `start` shape
expression (9). Each is engine work with a named shape, which is why
they are listed rather than summarised as "the rest".

---

## XML conformance: a lenient DTD parser, and a denominator that asked
## the wrong questions

Was 1706 pass, 524 fail (out of 2230 in profile). Now **1744 pass, 126
fail (out of 1870 in profile)**. Two halves, and they are different
kinds of change — one fixed the parser, the other fixed the question.

**The parser: `[70]`–`[76]`, `[28]` and `[69]` were barely checked.**
`parseEntityDecl` SKIPPED TO THE NEXT `>` for every shape but a quoted
entity value, and `parseDoctype` scanned over anything at all between
the root Name and the internal subset. So all of these were accepted
as well-formed:

- `<!ENTITY foo PUBLIC "some public id">` — `[75]`'s PUBLIC form
  requires a SystemLiteral;
- `<!ENTITY e PUBLIC "whatever""e.ent">` — and the space between the
  two literals;
- `<!ENTITY ent PUBLIC"PublicID" "nop.ent">` — and the space after
  `PUBLIC`;
- `<!ENTITY e "whatever" -- a comment -->` — a declaration ends at
  `S? '>'`;
- `<!ENTITY foo SYSTEM "foo.eps"NDATA eps>` — `[76]` begins with `S`;
- `<!ENTITY %pe "…">` — `[72]` requires the space after `%`;
- `<!ENTITY ge CDATA "…">` — `CDATA` is not an `[73]` EntityDef;
- `<!ENTITY % pe SYSTEM "n.ent" NDATA unknot>` — `[74]` admits no
  NDataDecl;
- `<!DOCTYPE doc -- a comment -- []>` — `[28]` admits `(S ExternalID)?`
  between the Name and the subset and nothing else;
- `% pe;` — `[69]` is `'%' Name ';'`, with no space.

Every one is a document the parser said YES to. That is the direction
that hides: a checker which ACCEPTS malformed input reports nothing,
while one that rejects valid input announces itself on the next run.

**The denominator: 372 cases were being scored that this parser is not
asked about.**

- **313 for editions 1–4 only.** The suite marks each case with the
  EDITIONS of XML 1.0 it is about, and the runner ignored the
  attribute. The Fifth Edition REPLACED Appendix B's enumerated
  BaseChar / CombiningChar / Digit / Extender classes with the ranges
  this parser uses, so `EDITION="1 2 3 4"` asks a question the Fifth
  Edition does not ask. All 313 were `not-wf` cases scored as
  failures.
- **59 Namespaces-in-XML cases.** `rmt-ns10-004` is
  `<a:foo xmlns:a="…"/>` with an undeclared prefix: namespace-ill-formed
  and XML-well-formed. This parser is NON-NAMESPACE by design and its
  header says so, so it accepted them correctly and was marked wrong.
  The namespace layer is `XML/Namespaces.lean` and is measured
  separately.

Neither group is folded into PASSES. They are reported in buckets of
their own, beside the XML 1.1 and non-UTF-8 buckets that were already
there — the parser is not being asked, so neither a pass nor a failure
is the truth about it. Nine cases that had been passing by accident
moved out of the score with the rest of their edition, which is why
the pass count fell while the parser got stricter.

📊 MEASURED: **1744 pass, 126 fail (out of 1870 in profile)**; out of
profile and reported: 24 optional-behaviour, 55 XML 1.1, 56 not UTF-8,
313 editions 1–4, 59 namespaces.

The 126 remaining are 84 documents accepted that should be rejected
and 42 rejected that should be accepted. Most of both need the same
missing feature: the EXTERNAL DTD SUBSET. `<!DOCTYPE doc SYSTEM
"p61fail1.dtd">` puts the error in a file the parser never opens, and
`valid/ext-sa/*` puts the entity definitions there. The system
identifier is now recorded on `Doctype.systemId` — recorded, not
fetched, because fetching needs I/O and the parser is a pure function.

---

## XML: an entity's replacement text is CONTENT, not characters

The parser refused any entity whose replacement text held a `<`:
"entity replacement text contains markup; unsupported". That refusal
was honest — better than splicing markup in as text — and it rejected
documents the specification calls well-formed. §4.4.2 (Included) says
the replacement text is processed as though it were part of the
document at the reference, so it is REPARSED as `[43] content` and its
nodes spliced in.

The rule that makes this work is §4.5, and getting it wrong costs a
test either way:

* a CHARACTER reference is expanded when the replacement text is
  BUILT, so `<!ENTITY e "&#60;foo></foo>">` has the replacement text
  `<foo></foo>` and reparsing gives an ELEMENT (`valid/sa/024`);
* a GENERAL-entity reference is BYPASSED there and included at the
  reference site instead, so `<!ENTITY e "&lt;foo>">` still has the
  replacement text `&lt;foo>` and reparsing gives the TEXT `<foo>`
  (`valid/sa/088`).

A first attempt expanded everything and reparsed the result. That
turned `&lt;` into markup and lost `valid/sa/088`. A second attempt
kept everything raw and reparsed that. That left `&#60;` as a
reference and lost `valid/sa/024`. The two cases are a matched pair,
and the only version that holds both is the specification's own:
normalise the EntityValue at declaration — character references in,
general-entity references left alone.

`parseTextContent` also has to STOP before a markup-carrying
reference, or `<doc>a&e;b</doc>` goes down the character path and is
rejected on the `<` that the character path is right to reject.

📊 MEASURED: **1766 pass, 104 fail (out of 1870 in profile)**, from
1744. Every `valid/sa` and `valid/not-sa` case that had been rejected
now passes.

The 104 remaining need EXTERNAL entities — `valid/ext-sa/*` puts the
entity text in a separate file, and `o-p61fail1` and its neighbours
put the ERROR in the `.dtd` the DOCTYPE names. `Doctype.systemId`
records the identifier; nothing fetches it yet.

---

## XML: external entities and the external DTD subset — 1819 pass, 51 fail

The parser read no external resource at all. `Doctype.systemId`
recorded the identifier and nothing fetched it, so
`<!DOCTYPE doc SYSTEM "p61fail1.dtd">` put the ERROR in a file the
parser never opened, and `valid/ext-sa/*` put the entity DEFINITIONS
there.

`parseXMLWith` takes a `Resolver` — `String → Option String`, a
system identifier to its text. A PARAMETER, not a registry: the parser
stays a total function of explicit inputs and the I/O lives in the
runner, which reads the document's own directory. `parseXML` is
`parseXMLWith (fun _ => none)`, spelled out so "read nothing" stays a
choice somebody made rather than a default nobody noticed.

Four pieces:

1. **An external general entity** (`<!ENTITY e SYSTEM "001.ent">`) has
   its text fetched at declaration and enters the table like an
   internal one. `[78] extParsedEnt` allows a leading
   `[77] TextDecl`, which is stripped — left in place it reads as a PI
   whose target is `xml`, which `parsePi` rejects.

2. **The external subset** (`[30] extSubset`) is parsed after the
   internal one, because §2.8 reads them in that order and §4.2 lets
   the FIRST declaration of a name win.

3. **Conditional sections** (`[61]`) — `INCLUDE` recurses, `IGNORE`
   skips to the matching `]]>`, and both NEST. They are an
   external-subset production, so `<![` in the internal subset stays
   the error it was.

4. **Parameter entities**, in their own table. §4.1 makes `%foo;` and
   `&foo;` different names, so one table would have conflated them.

`parseSubset` replaced `parseIntSubset`: the internal subset, the
external subset and an INCLUDE section admit the same declarations and
differ only in where they END (`]`, end-of-entity, `]]>`) and whether
a conditional section is allowed. One loop with a `SubsetEnd`
parameter, rather than three that drift apart.

🔴 The piece that is not a loop: §4.4.8 lets a parameter-entity
reference stand INSIDE a markup declaration in the external subset.
`<!ELEMENT child1 (a ,%choice1;,c )>` puts one in the middle of a
content model, where the declaration parser meets a `%` it has no
production for and rejects the document. `peScan` expands references
throughout the subset text in one left-to-right pass, collecting
parameter entities as declarations go by. A forward reference is left
unexpanded rather than guessed at; the declaration parser then reports
it.

📊 MEASURED: **1819 pass, 51 fail (out of 1870 in profile)**, from
1766. 12 of the 51 are documents rejected that should be accepted, 39
accepted that should be rejected.

No regression: csv2rdf 270 pass, 0 fail (out of 270), csv2json 270
pass, 0 fail (out of 270), JSON Schema 770 pass, 0 fail (out of 770
decided), MathML 56 pass, 0 fail (out of 56), schematron 8 pass, 0
fail (out of 8), ShEx 1075 pass, 104 fail (out of 1179 decided).

---

## XML: `[9] EntityValue` and `[10] AttValue` are productions

Two more families, both in the accept direction.

**An entity value was a run of characters.** `normalizeEntityValue`
copied everything through but a character reference, so
`<!ENTITY foo "&">` was well-formed (`not-wf-sa-113`, `-114`), and so
was `<!ENTITY e "<![CDATA[Tim & Michael]]>">` — CDATA is not
recognised inside an entity value, so that `&` is as bare as any
other (`not-wf-sa-159`). `[9]` admits `[^%&"]`, a PEReference or a
Reference, and its characters must be `[2] Char` (`not-wf-sa-175`).
§4.4.8 also puts a parameter-entity reference in an entity value out
of bounds in the INTERNAL subset (`not-wf-sa-160`, `-162`).

**An attribute DEFAULT is an attribute value**, and none of its
constraints was checked. `expandEntityValue` already decides every
one of them — declared, non-recursive, no `<` — so the check is a
call rather than a new rule. The word in WFC: Entity Declared is
"already": an entity declared AFTER the ATTLIST does not count
(`not-wf-sa-180`). The check runs in the internal subset only, since
the WFC is conditional on the document being standalone and an
external subset may declare in a part not yet read.

**And one denominator fix.** `valid/ext-sa/007`, `008` and `014` hold
their entity text in UTF-16. The parser is UTF-8 only and says so, so
the reference came back undeclared and the document was rejected — a
transcoding gap scored as a parser failure. A case whose NAMED entity
file will not decode now joins the non-UTF-8 bucket, where the
non-UTF-8 documents already were. Only files the document names
count: a stray undecodable file in the directory says nothing about
the case.

📊 MEASURED: **1840 pass, 22 fail (out of 1862 in profile)**, from
1819 pass, 51 fail (out of 1870). Out of profile and reported: 24
optional-behaviour, 55 XML 1.1, 64 not UTF-8, 313 editions 1–4, 59
namespaces.

The 22 left are a long tail with no shared cause: 15 accepted that
should be rejected (`[32]` SDDecl, `[41]` Attribute, `[77]` TextDecl,
`[28a]` and a handful of one-off errata cases) and 7 rejected that
should be accepted (four byte-order cases, `ext02`, `o-p28pass5`,
`valid/not-sa/023`).

---

## RML-Core: a suite that had no runner — 60 pass, 0 fail (out of 60)

`RML/Mapping.lean` held term generation and templates and nothing
else: no mapping reader, no source reader, no evaluator, no runner.
Five modules close that.

- `RML/JsonPath.lean` — the JSONPath SUBSET an `rml:iterator` and an
  `rml:reference` need, with the accepted grammar stated in full. A
  path outside it does not parse and selects NOTHING; the corpus
  writes one malformed path and it is a negative case.
- `RML/Value.lean` — a source value and the datatype it carries by
  itself. A JSON source is TYPED and RML says so: a reference to `10`
  produces `"10"^^xsd:integer`. A record cannot be a
  `String → Option String` lookup, because the type is already gone
  by the time the term is built.
- `RML/Model.lean` — the mapping as a value, kept apart from the
  graph it is read out of and from the evaluation that runs it. A
  mapping graph is arbitrary RDF and reading it fails in many ways;
  evaluation is a total function. Mixing them makes "this mapping is
  malformed" and "this record has no value" the same kind of answer.
- `RML/FromGraph.lean` — the reader.
- `RML/Eval.lean` — the evaluator. Sources are SUPPLIED, not read:
  reading a file needs I/O, and deciding what a mapping means does
  not.
- `Harness/RmlRun.lean` (`lake exe l4rml`).

📊 MEASURED: **60 pass, 0 fail, 0 comparison-gave-up (out of 60
compared)**; 15 NEGATIVE cases not attempted (this slice has no
mapping validator, so it makes no claim about them); 1 fixture not
read.

That last one is the corpus's, not the parser's: `RMLTC0027b`'s
`output.nq` writes `<http://example.com/Person/Emily Smith>`, and an
`IRIREF` may not contain a space. The runner names the file and the
reason rather than reporting a bare parse failure.

### The comparison is one graph isomorphism over the whole DATASET

A dataset is not a bag of graphs to compare one at a time: a blank
node may appear in the default graph AND in a named one, and matching
each graph separately would let two different datasets pass. Every
quad is encoded as a triple whose predicate carries the graph name —
both parts percent-encoded, so the encoding is injective — and the
two encoded graphs are compared once. Blank nodes then have to line up
ACROSS graphs, which is what dataset isomorphism means.

### Eight defects, and what each one looked like

Every one of them produced a graph of the RIGHT SHAPE:

1. `defaultTermType` reads the FORM only, so a subject map written
   `rml:subjectMap [ rml:reference "$.FirstName" ]` defaulted to a
   LITERAL and produced no subject. POSITION decides this, and only
   the caller knows the position (`asIri` / `asLiteral`).
2. `rml:baseIRI` was not read, so a template producing `Carlos` was
   not an IRI and generated nothing.
3. A join condition was stored as a reference STRING, so
   `rml:childMap [ rml:template … ]` lost its template.
4. The `rml:subject` SHORTCUT was read in a branch of its own, which
   dropped the predicate-object maps with it.
5. `rml:subjectMap [ rml:termType rml:BlankNode ]` states a term type
   and NO form, meaning a fresh blank node per record. `generateTerm`
   had no form to work from.
6. A `rml:languageMap` went through the IRI default, so
   `{$.language}-{$.region}` produced `http://example.com/en-GB`
   where the tag `en-GB` was meant. A `rml:datatypeMap` is the
   opposite case and does want an IRI.
7. A TEMPLATE over a multi-valued reference produces one term per
   COMBINATION. Taking the first lost half of `RMLTC0025c` — with
   the right predicate and the right objects on the half that
   survived.
8. Graph maps UNION across levels, they do not override. Treating a
   predicate-object map's graph as a replacement put one quad in one
   graph where the corpus expects it in two.

### Scope

RML-Core only. `rml-io`, `rml-cc`, `rml-fnml` and `rml-star` are laid
out differently and need modules this port does not have — function
maps, RDF-star terms, collections and containers, non-file sources.
Pointing the runner at them reports almost everything NOT READ, which
is the truth about them and not a score.

---

## RIF Core: a second suite that had no runner — 24 pass, 2 fail (out of 26 decided)

`RIF/Core.lean` modelled a RIF rule as RDF TRIPLES. That could not
state what the corpus asks: no membership, no subclass, no positional
atoms, no built-ins, so `ex:a # ex:D` and
`pred:literal-not-identical("1"^^xs:integer "1"^^xs:string)` were
both unsayable. It is REPLACED rather than kept beside the new
modules — two models of one thing is exactly the confusion its own
header warned about, and nothing else in the tree imported it.

Five modules and a runner:

- `RIF/Syntax.lean` — the abstract syntax. A constant is a LEXICAL
  FORM plus a SYMBOL SPACE, not an RDF term: RIF has `rif:iri`,
  `rif:local` and every XSD datatype as symbol spaces, and
  `pred:literal-not-identical` compares the PAIR.
- `RIF/Ps.lean` — the Presentation Syntax parser, grammar stated in
  full. 80 of the corpus's 80 documents parse.
- `RIF/Builtins.lean` — the built-in library, three-valued.
- `RIF/Engine.lean` — bounded forward chaining, local-constant
  scoping, and Core SAFENESS.
- `Harness/RifRun.lean` (`lake exe l4rif`), which also carries the
  RDF-compatibility mapping: a triple is a frame, `rdf:type` is
  membership, `rdfs:subClassOf` is subclass.

📊 MEASURED: **24 pass, 2 fail (out of 26 decided)**; 13 UNDECIDED,
1 not read, 6 import-rejection cases not attempted.

### UNDECIDED is the whole point here

RIF-DTB defines **197 built-ins**. This slice decides a named subset.
A rule whose body needs one of the others cannot fire, so the closure
is INCOMPLETE, and an entailment read off it is a guess. `entails`
returns `.undecided`, and the runner counts those apart — 13 of them,
all the date/time, duration, list and binary families.

The same rule covers an IMPORT under an entailment regime this port
does not implement. Reading an OWL-Direct import as plain RDF made
`Non-Annotation_Entailment` entail a triple that OWL keeps inside an
annotation — a wrong answer produced with complete confidence, which
is the failure mode this whole discipline exists to catch.

### Seven defects, six of them found by a case that said the opposite

1. `(* … *)` is an ANNOTATION, not a comment. Treating `(` as an open
   paren made every annotated document unparsable.
2. `-` is a name character, so `ex:a->1` scanned as the name `ex:a-`.
   A frame written without spaces is ordinary RIF.
3. A conclusion file is a BARE FORMULA with no prologue, and its
   prefixes come from the premise beside it — or, where the premise
   only imports a graph, from that graph's own `@prefix` lines.
4. `pred:is-literal-T` asks about the VALUE SPACE, not the datatype
   IRI: `"1"^^xs:integer` IS a literal of `xs:decimal`. Comparing
   IRIs made 24 of the corpus's assertions false and the rule they
   guarded never fired.
5. `1` and `true` are the same `xs:boolean` VALUE. Comparing lexical
   forms made `pred:boolean-less-than("0" "1")` false.
6. A local constant is DOCUMENT-scoped: the premise's `_p` and the
   conclusion's are different symbols. Spelling them the same made
   the premise entail the conclusion, which `Local_Predicate` and
   `Local_Constant` say must not happen.
7. SAFENESS is part of being a RIF Core document and a parser cannot
   see it. Boundness PROPAGATES in two ways the first version missed:
   `?x = ?y` binds `?y` once `?x` is, and `pred:iri-string` binds
   either side from the other. One pass over the body called two
   ordinary documents unsafe.

Named residue: `EBusiness_Contract` and
`RDF_Combination_Constant_Equivalence_4` are decided and WRONG — the
second needs RDF constant equivalence (a plain literal and an
`xs:string` literal denoting one thing), which is a semantics
question rather than a missing built-in.

No regression: csv2rdf 270 pass, 0 fail (out of 270), csv2json 270
pass, 0 fail (out of 270), JSON Schema 770 pass, 0 fail (out of 770
decided), RML-Core 60 pass, 0 fail (out of 60), schematron 8 pass, 0
fail (out of 8).

## XSLT 1.0 and a real XPath 1.0 engine (2026-08-23)

Landed `L4Factoidal/XPath/{Data,Expr,Eval}.lean` — the XPath 1.0 data
model, grammar and evaluator — and `L4Factoidal/XSLT/Transform.lean`,
which reads a stylesheet, instantiates it and serialises the result
tree. Runner: `lake exe l4xslt`, over the 88 vendored cases of
`third_party/testing/xslt` (a subset of `w3c/xslt30-test`).

**Score: 84 pass, 3 fail (out of 87 decided), 1 refused (out of 88
manifest entries).** For comparison the F* engine scores 87 pass, 0
fail, 1 skip on the same corpus.

### Why a second XPath module rather than extending `XPath/Mini.lean`

`Mini` addresses a node by a `/tag[i]/tag[j]` PATH STRING built from
ELEMENTS ONLY. That is the right model for Schematron, whose findings
name a node to a human. It cannot carry XSLT: `text()`, `comment()`,
`processing-instruction()` and `node()` address nodes that path has no
name for. Extending `Mini` would have changed the node identity
Schematron already depends on, so `Full` is a second model in its own
namespace (`L4Factoidal.XPath.Full`) and `Mini` is untouched.

The namespace split was forced by the library root failing to import:
both models need a type called `Step` and a function called `eval`,
and they are different types and different functions. That failure is
the good outcome — the alternative is two `Step`s shadowing each
other.

### Twelve defects, and what each of them produced

Every one produced a document of the RIGHT SHAPE with the wrong
content. None produced an error.

1. **`::` scanned into the name.** `:` is a Name character, so
   `self::a` tokenised as ONE name that the node-test reader took for
   a child element called `self::a`. The pattern parsed cleanly and
   matched nothing. `[5] QName` carries at most one colon; the
   tokenizer now stops before a second.
2. **Insertion sort skipped past equal keys.** `xsl:sort` is stable
   (§10). Skipping while `y ≤ x` put a node after its equals; the fix
   skips only while `y` is STRICTLY smaller. `sort-001` sorts `Hello`
   and `617-939-5938`, both NaN, and asks for them in document order
   in the ascending AND the descending pass — 11 sort cases at once.
3. **`|` split inside predicates.** Splitting `match="*[self::a|
   self::b]"` on every `|` gave two fragments, neither of which
   parses, so the template matched nothing while the stylesheet
   looked fine. The splitter now tracks brackets and quotes.
4. **A name-only template has no pattern.** Running the empty string
   through the pattern parser made it unreadable and refused the whole
   stylesheet for a template that matches nothing by design.
5. **`data-type` and `order` are ATTRIBUTE VALUE TEMPLATES.** Taking
   `data-type="{$typer}"` literally made it neither `number` nor
   `text`, and the engine fell back to a text sort: a correctly
   ordered list under the wrong ordering.
6. **A FilterExpr's predicate saw a one-element context.** Encoding
   `(a|b|c)[last()]` as a `self::node()` step with the predicate
   attached gave every node `last() = 1`, so the filter kept
   everything. `Expr.filter` now evaluates the predicate against the
   whole filtered set.
7. **A comment split one text node into two.** §3.4 strips a
   whitespace-only text node from the stylesheet. A comment between
   two runs of character data splits what is one text node in the
   prepared stylesheet, the first half often whitespace-only.
   Stripping before merging deleted indentation the transform is
   supposed to emit.
8. **An empty text node is not a node.** Keeping one made an element
   with no content serialise as `<td></td>` rather than `<td/>` — the
   same infoset, a different document under the canonical comparison
   the suite makes.
9. **`exclude-result-prefixes` was ignored.** Every literal result
   element carried every namespace declaration in scope on it,
   including ones the stylesheet had explicitly excluded.
10. **`xsl:element` with an unprefixed name said nothing about its
    namespace.** §7.1.2 puts such a name in the DEFAULT namespace,
    which may be NONE; emitting no declaration let the element
    inherit the enclosing result element's default namespace and
    become a different element.
11. **A redeclared prefix moved to the end of the context.** That
    list is the order the result element's declarations are written
    in, so a stylesheet that redeclares a prefix to the same URI
    produced the right declarations in the wrong order.
12. **A node-set from a second document was walked against the
    first.** `document('')//ped:test` carries addresses that only
    mean something against the stylesheet's own tree; reading them
    against the source tree silently selected nothing.

Two arithmetic rules were also written out rather than left to
whichever `/` Lean's `Int` denotes: `Int.fdiv` for `floor`/`ceiling`
and `Int.tdiv` for `mod` and `div`. Lean's `/` on `Int` is Euclidean,
which floors for a positive divisor — right for `floor` by accident,
wrong for `mod`, whose remainder takes the sign of the DIVIDEND
(§3.5).

### Three features that are NOT XPath 1.0, and are implemented anyway

Each is marked as an out-of-version extension where it appears, so no
reader takes it for 1.0. Each is implemented because the F* engine
this module ports implements it and because the alternative — ignoring
it — is certainly wrong.

- **The value comparisons `eq ne lt le gt ge`** (XPath 2.0). Two
  numbers compare numerically; anything else compares as strings by
  codepoint, so `'20' lt '180.3'` is FALSE. That is what
  `boolean-026` and `boolean-027` ask for and no more; widening it to
  the 2.0 type system would be inventing behaviour no test states.
- **The double literal `1e3`** (XPath 2.0). Without it the tokenizer
  produced the number `1.0` followed by a name `e2` and the whole
  expression failed to parse. `Num.ofString` — XPath 1.0's
  `number()` — still says NaN for `"1e3"`, because changing that
  would change what `number(.)` says about a string; the exponent
  lives in a separate `Num.ofLexeme` used by the TOKENIZER only.
- **`xsl:copy-of copy-namespaces="no"`** (XSLT 2.0). Ignoring the
  attribute would copy namespaces where the test asks for them to be
  dropped, and emit a document of the right shape carrying
  declarations nobody asked for.

### What the runner refuses, and why that is a third bucket

`transform` returns `Outcome.refused` with a reason for an XSLT
element outside the implemented set, a match pattern it cannot parse,
or an expression it cannot evaluate. The runner counts those apart —
never as a pass, never as a failure. One case remains:

- `select-5901` — `document('select-59.xml')`. `XPath.Eval` does no
  I/O: `Ctx.docs` is a map the CALLER supplies, and the runner fills
  it by scanning the stylesheet text for each `document('literal')`
  and loading the file beside the stylesheet. `select-59.xml` is not
  in the corpus — the vendoring renamed each environment's source
  file — so the runner names the missing URI in the refusal. That is
  a corpus fact, not an engine gap, and a supplied-but-absent
  document is a refusal rather than an empty tree the stylesheet
  would quietly transform into nothing.

### The three residual failures, named

- `copy-3102` — namespace declarations in a different ORDER. The
  suite's expected files are not self-consistent about this: sorting
  by prefix (what C14N does) fixes this case and breaks
  `conflict-resolution-1301` and `copy-3701`, whose expected files
  keep declaration order with the default namespace NOT first.
  Declaration order matches the most of them.
- `node-1601` — the order of the `namespace::` axis, which XPath 1.0
  leaves implementation-defined. The expected file's order is neither
  declaration order, nor its reverse, nor alphabetical.
- `namespace-4801` — `xsl:copy` of a node from the stylesheet's OWN
  document. Defect 12 fixed the path evaluation; the copy still reads
  its namespace context from the primary document, because `Rt` holds
  one document. Fixing it means threading the document through
  `Item`.

### A comparison artifact worth writing down

49 of the 84 decided cases first landed in the whitespace bucket for
ONE reason: the vendored expected files carry CRLF line endings, and
every XML processor — this project's parser included — applies §2.11
line-end normalisation on input. Comparing engine output against the
RAW BYTES of the expected file therefore differed on every line of
every document that has one. Applying §2.11 to the expected text is
reading it as XML rather than as bytes; it is not a loosening of the
comparison. The runner's remaining `pass-loose` bucket applies the
same whitespace collapse to both sides.

No regression: `lake build` green over 511 targets, which runs every
`#guard` in the tree.

## GRDDL (2026-08-23)

Landed `L4Factoidal/GRDDL/Discovery.lean` — a port of
`formal/fstar/GRDDL.Discovery.fst` — and `Harness/GrddlRun.lean`
(`lake exe l4grddl`) over the 68 tests of the vendored W3C GRDDL
suite. GRDDL was blocked on XSLT and became reachable the moment the
engine landed: a GRDDL transformation IS an XSLT stylesheet.

**Score: 19 pass, 22 fail (out of 41 decided); 10 name no
transformation this stage can follow, 17 need a document the vendored
docroot does not carry, 0 refused (out of 68 manifest entries).** The
F* runner scores 18 pass, 50 fail (out of 68) on the same corpus,
counting every non-pass as a failure.

### What the runner buckets apart, and why

A GRDDL result is a GRAPH, compared by isomorphism — blank-node
labels are not part of what one means. Beyond pass and fail there are
three buckets, each carrying the name of what is missing:

- **no transformation found** — the source names no transformation
  this stage can follow and is not itself RDF/XML, so there is
  nothing to glean;
- **unavailable** — a document the test needs is not mirrored under
  `docroot/`. The IRI is printed. This runner makes no network
  request, and a case that would need one is not a failure of the
  engine;
- **refused** — a stylesheet the engine declined, or output that is
  not well-formed RDF/XML, with the reason. This is now ZERO.

### Three engine gaps the corpus found, all in XSLT

1. **`xsl:message` was unimplemented**, so six cases refused. §13
   sends its content to a message stream, never to the result tree,
   so it contributes no nodes; `terminate="yes"` ends processing,
   which is a refusal rather than a partial document.
2. **`xsl:import` and `xsl:include` were unimplemented**, so ten
   `inline-rdf` cases refused with nothing said about why. Both are
   implemented, with import PRECEDENCE (§2.6.2) carried on every
   template and `xsl:call-template` resolved by precedence rather
   than by document order. As with `document()`, the imported trees
   are supplied by the CALLER: `XSLT.importHrefs` says which hrefs a
   stylesheet wants, the runner fetches them from the docroot, and
   nothing in the engine opens a file.
3. **A `call-template` naming no template failed silently deep inside
   instantiation.** It is now named up front, which is what turned
   those ten cases from an opaque refusal into an honest
   "unavailable": the stylesheet imports
   `http://www.w3.org/2003/g/xml-attributes`, which the vendoring did
   not capture.

### One GRDDL defect, worth its own line

The transform's output describes the SOURCE — `rdf:about=""` denotes
it — so a relative reference in that output resolves against the
source's EFFECTIVE base, which a root `xml:base` or an XHTML
`<base href>` may move. Using the fetch IRI instead named the wrong
subject while producing exactly the right NUMBER of triples: six
cases differed in one IRI and nothing else.

### Seven of the 22 failures are corpus drift, and the runner says so

Several vendored inputs were re-fetched from a W3C server that had
upgraded its own links to `https`, while the expected-output files
beside them still say `http`. A transform can then be exactly right
and still produce a different IRI. The runner reports which failures
differ ONLY by that scheme — as a SUB-COUNT of the failures, never as
a separate bucket, because the two graphs really are different
graphs.

The remaining 15 are real: multi-transformation merges that come up
short (`three-transforms` produces 1 of 3, `four-transforms` 2 of 4,
`multiprofile` 5 of 8), which is the one-level-not-a-fixpoint limit
`Discovery.lean`'s header states.

## ShExC: 442 match, 0 mismatch, 0 declined (out of 442)

`L4Factoidal/ShEx/Compact.lean` reads the ShEx compact syntax.
`Harness/ShExCRun.lean` (`lake exe l4shexc`) is a DIFFERENTIAL runner
over `third_party/testing/shex/schemas/`: every fixture there ships a
`.shex` and a ShExJ `.json` twin of the same schema, so the corpus is
its own oracle. The compact reader builds a tree, `FromJson.lean`
builds a tree from the JSON, and `SchemaEq.lean` compares them.

📊 MEASURED: **442 match, 0 mismatch, 0 declined (out of 442 `.shex`
files)**. The ShEx validation suite is unchanged at **1075 pass, 104
fail (out of 1179 decided)**, 3 not read — the two readers now agree
without either moving.

### Why a differential and not an expectation file

A ShExC parser has no separate ground truth: the schema IS the
answer. Comparing the two front doors turns the corpus into the
oracle and points at a disagreement without either side having to be
blessed. The runner keeps four buckets — match, mismatch, declined,
no reference — and a REFUSAL is never scored as a mismatch: a
construct outside the implemented grammar is visibly unparsed, never
a schema that validates the wrong graphs.

That separation is what made the work tractable. The first run read
365 match, 53 mismatch, 24 declined. The 24 refusals named exactly
two grammar holes; the 53 mismatches were four content defects. Had
refusals been folded into the failures, one number would have covered
six unrelated causes.

### The defects, and what each produced

Every one produced a schema of the RIGHT SHAPE with wrong content, or
a refusal where an answer existed. Each is pinned in
`L4Factoidal/ShEx/CompactTests.lean` beside the fixture that paid for
it.

1. **`//` was scanned as an empty regular expression.** The regex
   scanner reached `/` first and read `//` as a PATTERN with no
   characters, leaving the annotation's predicate and object as loose
   tokens. Every annotated schema then died at the closing brace
   ("expected '}', found //" — `1inversedotAnnot3`, `kitchenSink`,
   `_all` and 11 more). `//` is now punctuation, tested before the
   regex branch.
2. **`@fr` had no token.** `@` was punctuation only, so a language
   tag in a value set reached the shape-reference reader and refused
   with "expected an IRI, found @" (9 fixtures). A shape label always
   carries a colon or angle brackets and a language tag never does,
   so one character of lookahead in the tokenizer separates them.
   `@~` — EVERY language — is a language stem whose stem is empty,
   and stays `punct "@"` because there is no tag to carry.
3. **A wildcard stem range took the wrong kind.** `[. - "v1"]` is a
   `LiteralStemRange` and `[. - @fr-be]` a `LanguageStemRange`; only
   the exclusions say which. Assuming an `IriStemRange` built a range
   over a family the excluded nodes cannot belong to, so the
   exclusions did nothing. The kind now travels with each exclusion
   and the range reads it off them.
4. **`{` after a node constraint was always a shape definition.**
   `ex:literal ["a" "b"]{2,3}` made `2` a predicate and refused the
   whole schema (`kitchenSink`). A `{` followed by a number is a
   repeat range; the guard file pins BOTH readings so the fix is not
   a licence to drop shape definitions.
5. **A shape definition's own annotations were left on the floor.**
   `<S1> { … } // <p> <o>` — the statement reader then saw a loose
   `//` where the next shape label belonged (4 fixtures).
6. **Numeric facets were compared as spellings.** `MININCLUSIVE 05`,
   `5`, `5.0` and `05.00E0` all denote five, and the ShExJ twin
   writes whichever form its serialiser chose. `canonNumericLexeme`
   now normalises on both sides — a disagreement about spelling was
   being reported as a disagreement about the schema, and this one
   defect accounted for 48 of the 53 mismatches.
7. **A UCHAR was carried through verbatim.** `<http://a.example/p1>`
   built a predicate spelled with the escape rather than `.../p1` — a
   different IRI, so a different schema. In a regular expression the
   rule is narrower: a UCHAR is a way of WRITING a character and is
   decoded, while every other backslash escape belongs to the pattern
   and is carried through untouched. Decoding all of them would turn
   `\t` into a tab and change what the pattern matches; decoding none
   left `a` where the twin has `a`.
8. **A language tag kept its case.** RDF 1.1 Concepts §3.3 puts the
   lowercase form in the value space: `"x"@en-UK` and `"x"@en-uk` are
   one literal. Both readers now lowercase.

### The rule this corpus keeps teaching

Defects 3, 6, 7 and 8 all produced a well-formed schema that a
consumer would accept and act on. Only a second reader of the same
document caught them. Where a format has two serialisations, the
differential between them is worth more than any expectation file we
could write, because it needs no blessing and cannot go stale.

## OWL DL: the class-expression reasoner, steps 2 and 3

`L4Factoidal/OWL/ClassExpr.lean` (step 1) reads a class expression
out of a graph. Two consumers read that one AST, which is what makes
a disagreement between them about what a restriction MEANS impossible
by construction:

* `Materialise.lean` (step 2, `formal/fstar/Tableau.fst` §§5–9) —
  POSITIVE-SOUND membership. It writes entailed `rdf:type` triples
  and never detects unsatisfiability.
* `Refute.lean` (step 3 wave 1, `formal/fstar/Tableau.Refute.fst`) —
  the REFUTATION calculus. It answers "no model exists" and never
  writes a triple.

Tracked at https://github.com/danbri/factoidal/issues/548 .

### Three values, and which one is missing from each side

`Materialise.isMember` answers `some true` / `some false` / `none`.
`Refute.refute` answers `some false` / `none` — and has no
`some true` ON PURPOSE.

The F* module does return `Some true` for a saturated clash-free
branch, and its own header then tells callers to treat it exactly
like `None`, because the calculus is incomplete. A value that no
caller may act on is a trap: sooner or later something scores
"consistent" on it. Wave 1 does not have the value to misuse.

`none` is always sound on both sides. It means the caller falls back
to the OWL RL closure, which decides fewer things and decides them
right.

### The positive-soundness gate, and what it refuses

`cePositiveSound` decides which `some true` may be WRITTEN INTO the
graph. It admits `named`, `hasValue`, `someOf`, `minCard`,
`minQualCard` and Boolean combinations of those. It refuses:

* `allOf` — a successor this graph has not seen could violate the
  filler, so "every KNOWN successor is in C" does not entail `∀p.C`;
* `maxCard`, `exactCard` and their qualified forms — a positive
  membership needs `owl:sameAs` reasoning or a unique-name
  assumption, and the module has neither;
* `complement` — needs classical negation.

The gate is STRUCTURAL: a refused shape anywhere inside a Boolean
combination closes it. Withholding an entailment is sound; asserting
one a model can falsify is not.

### No unique-name assumption, stated twice because it is where
refuters go wrong

Two different IRIs may denote one individual unless the graph says
`owl:differentFrom`. So:

* a successor COUNT is a lower bound. `≥ k` may fire on it; `≤ k`
  may not, except in the trivial `k = 0` case;
* `≤ 1 p` with two named successors is NOT refuted. Adding one
  `owl:differentFrom` triple between them refutes it. Both readings
  are pinned in `RefuteTests.lean`, next to each other, because the
  pair is the check — either alone can be passed by an engine that
  has the rule backwards.

### An existential witness is never counted

`Materialise` and `Refute` both mint witnesses, and both keep them
out of cardinality counts. A witness may coincide with an existing
successor in some model; counting one fabricates a clash. A
`hasValue` edge is different — it holds in every model — so it IS
counted. `REdge.counts` carries the distinction in the type.

Witness minting is deterministic (the blank node's name is a
function of the individual and the property) and depth-capped. The
determinism is what makes a second pass mint nothing new; without it
a cyclic TBox grows the graph without end.

### The defect step 2 found in step 1

`ClassExpr.parseCeOfSubject` called `parseClassExpr`, which maps
every IRI straight to `named` without reading anything. So a NAMED
class expression — an IRI subject carrying `owl:onProperty` and
`owl:someValuesFrom`, which OWL 2 RDF-Based semantics says denotes
exactly `∃p.C` — came back as the opaque class itself, and every
membership it entails went unwritten. The marker-reading body is now
`parseCeMarkers`, shared by both entries.

The defect was invisible until a consumer asked the function for
something only it could answer. A parser with no consumer is a
parser with no test.

### A quadratic dedup, and the shape of that bug

The materialisation pass deduplicated subjects with
`acc.contains s` plus `acc ++ [s]` — quadratic in both halves, run
over every subject of a CLOSED graph. On the 41 384-triple
`type-consistency` premise that turned a two-minute probe run into
one still going after fifteen minutes. A hash set makes it one pass.

Worth naming because of how it presented: not as a wrong answer, not
as a crash, but as a run that never came back. The measurement was
the only thing that could have caught it, and only because there was
a BEFORE number to compare against.

`materialiseWithBudget` now caps the membership pass by (individual,
class expression) pairs and REPORTS the cap. The probe scores a
budget hit as a cap hit, so an absence verdict on a capped premise is
a failure rather than a pass — the same rule the closure budget
already follows.

### The probe's `--dl` regime

`lake exe l4owl-probe --dir third_party/testing/owl --dl` runs the
materialisation pass between two closures and consults the refuter on
both consistency judges. A refutation of a premise the catalog
asserts CONSISTENT is scored as a FAILURE. A refuter measured only on
the cases it is meant to close cannot be caught fabricating a
contradiction; scoring both directions from one flag is what makes
the number mean something.

### The `--dl` regime, measured

`lake exe l4owl-probe --dir third_party/testing/owl` with and
without `--dl`, 2026-08-23:

| Catalog | RL closure only | RL + materialisation + refuter |
| --- | --- | --- |
| profile-RL.rdf | 117 pass, 9 fail (out of 126) | 118 pass, 8 fail |
| profile-EL.rdf | 102 pass, 18 fail, 1 skip (out of 121) | 107 pass, 13 fail, 1 skip |
| profile-QL.rdf | 82 pass, 5 fail (out of 87) | 82 pass, 5 fail |
| type-positive-entailment.rdf | 315 pass, 93 fail, 4 unsupported (out of 412) | 318 pass, 90 fail, 4 unsupported |
| type-consistency.rdf | 485 pass, 94 fail, 4 unsupported (out of 583) | 485 pass, 94 fail, 4 unsupported |
| type-inconsistency.rdf | 30 pass, 97 fail, 1 skip (out of 128) | 67 pass, 60 fail, 1 skip |
| **TOTAL** | **1131 pass, 316 fail, 2 skip, 8 unsupported (out of 1457)** | **1177 pass, 270 fail, 2 skip, 8 unsupported** |

The F\* line for the one catalog that has one:
`owl2_dl_inconsistency` is 126 pass, 1 fail (out of 127) on
`type-inconsistency.rdf`. Wave 1 reaches 67 pass, 60 fail (out of
127 decided). The 60 are what waves 2 and later are for.

⚠️ `type-consistency.rdf` is UNCHANGED at 485 pass, 94 fail — and
that is a net figure hiding a trade, which is exactly what
anti-pattern #3 forbids leaving unsaid. `--dl` GAINS three
positive-entailment cases in that catalog (`WebOnt-someValuesFrom-001`,
`-003`, `somevaluesfrom2bnode`) and LOSES three consistency cases
(`WebOnt-description-logic-018`, `-020`, `-021`), where the RL clash
detector fires on the materialised graph. Those three are the named
residue of this landing.

### Three defects the corpus found in one afternoon

**A spelling difference is not a value difference.** The refuter's
first `provablyDistinct` said two literals are distinct when they
share a datatype and differ in lexical form. That is false almost
everywhere: `"1"` and `"01"` are one `xsd:integer`, `"1.0"` and
`"1.00"` one `xsd:decimal`, and two `rdf:XMLLiteral`s differing only
in insignificant whitespace are one value. `WebOnt-miscellaneous-202`
asserts exactly that last case as CONSISTENT, with a functional
property carrying two spellings of one XML literal — and the rule
refuted it. Distinctness is now claimed only for `xsd:string`, where
the lexical form IS the value.

The general shape: a refuter that reads formatting as meaning
invents contradictions out of whitespace, and it does so
CONFIDENTLY, on a premise a human would call obviously satisfiable.

**A witness must not be counted, including by consumers.** The
materialisation pass writes its existential witness into the graph,
and the RL clash detector downstream counts blank nodes like any
other name. On three consistent `WebOnt-description-logic` premises
that counted witness fired the detector against a bound the
individual's REAL successors do not exceed. The pass now WITHHOLDS a
witness where a max-cardinality bound or an `owl:FunctionalProperty`
declaration could be breached.

Stripping every witness edge from the output was tried first and
measured WORSE — ten `type-inconsistency` passes and five across the
profile catalogs lost to save three — because the closure does real
work on the witnesses it can count soundly. The measurement is what
settled it; the first fix was the more obviously "correct" one.

**A vacuous truth is not an entailment.** `∀p.C` is `some true` for
an individual with no known `p`-successor, and the blank-node
membership pass wrote that membership into the graph, where the
closure propagated it through `rdfs:subClassOf`. It is not entailed:
an unseen successor could violate the filler. The positive-soundness
gate now applies to the blank-node pass as well as the named one.
The F\* module gates only its named pass; this is the stricter
reading, and it is the one that keeps `materialise`'s output
entailed by its input.

### Wave 2, and the cost of it

`lake exe l4owl-probe --dir third_party/testing/owl --dl`, 2026-08-23:

| Catalog | RL closure only | Wave 1 | Wave 2 |
| --- | --- | --- | --- |
| profile-RL.rdf | 117 pass, 9 fail (out of 126) | 118 pass, 8 fail | 118 pass, 8 fail |
| profile-EL.rdf | 102 pass, 18 fail, 1 skip (out of 121) | 107 pass, 13 fail | 109 pass, 11 fail |
| profile-QL.rdf | 82 pass, 5 fail (out of 87) | 82 pass, 5 fail | 82 pass, 5 fail |
| type-positive-entailment.rdf | 315 pass, 93 fail, 4 unsupported (out of 412) | 318 pass, 90 fail | 318 pass, 90 fail |
| type-consistency.rdf | 485 pass, 94 fail, 4 unsupported (out of 583) | 485 pass, 94 fail | 485 pass, 94 fail |
| type-inconsistency.rdf | 30 pass, 97 fail, 1 skip (out of 128) | 67 pass, 60 fail | 80 pass, 47 fail |
| **TOTAL** | **1131 pass, 316 fail** | **1177 pass, 270 fail** | **1192 pass, 255 fail (out of 1457)** |

Wave 2 added the role box (bottom and top properties), the TBox rules
(edge-proved membership, conjunction introduction, provably-empty
named classes normalised to `owl:Nothing`), and
`L4Factoidal/XSD/Facets.lean` — the OWL 2 datatype map as a decidable
value space, which the two datatype clash rules read.

⚠️ The `--dl` run takes **26 minutes 34 seconds**. The RL closure
alone over the same corpus takes well under one. This is a named
performance gap, not a hidden one, and it is why `--dl` is a flag and
not the default.

Where the time is, measured on `type-consistency.rdf` alone (the
worst catalog):

| Regime | Wall |
| --- | --- |
| RL closure only | 17 s |
| `--dl --refute-budget 1` (materialisation, refuter effectively off) | 5 m 10 s |
| `--dl` (default budget 16) | over 10 m |

So the materialisation pass plus its second closure is about five
minutes, and the refuter adds more. Both halves need work; neither is
a single hot spot.

### Four performance defects fixed in wave 2, each measured

Named because each was found by a NUMBER and not by reading, and
because the first fix in two of the four cases was the wrong one:

1. **A per-branch search depth is a product, not a sum.** Giving each
   branch the full depth lets a node with `d` disjuncts grow a tree
   of `d^depth` states. The budget is now THREADED, so siblings draw
   from one pool.
2. **`labelsOf` was a `filter`-then-`flatMap` over the node list.**
   Ids are unique, so it is a lookup; `clashNodes` calls it once per
   node, which made it quadratic per round.
3. **The successor lookups scanned the graph as a LIST.** They now
   read the indexed store, which the tree already had.
4. **The sub- and superproperty closures were fixpoints recomputed
   per property per node per round.** They are computed once at
   `initState`.

Fixes 1, 3 and 4 each looked like the answer and each moved
`type-inconsistency` by nothing at all. What actually moved it was
finding, by a budget sweep, that ONE case
(`WebOnt-description-logic-504`) accounted for 71 of the 76 seconds.
The lesson is the one `skills/measuring-inference` already states:
find which phase the time is in BEFORE fixing anything. Four
plausible mechanisms became four work orders, and three of them were
free.

### The `--refute-budget` sweep

📊 `type-inconsistency.rdf`, out of 127 decided:

| Budget | Score | Wall |
| --- | --- | --- |
| 6 | 80 pass, 47 fail | 2.8 s |
| 16 | 80 pass, 47 fail | 5.2 s |
| 24 | 81 pass, 46 fail | 76 s |

The default is 16. `--refute-budget 24` reproduces the 81, and the
whole difference is `WebOnt-description-logic-504`. A cap that hides
which test it costs is a silent cap; this one names it.

## CORRECTION to the wave-2 performance section above

The section "Four performance defects fixed in wave 2, each
measured" is **wrong**, and so is the sentence that says three of the
four bought nothing. What actually happened is worse and more useful.

Three of those four edits **were never applied to the file.** The
scripts that made them read the file, made every replacement in
memory, and wrote it back at the END — so an `AssertionError` on a
LATER replacement discarded every earlier one, after the script had
already printed its progress. The build that followed compiled the
UNCHANGED file, reported success, and the measurement that followed
measured the unchanged file. Then the commit message said the fixes
had landed.

Verified afterwards by grepping the file for each change: the
indexed successor lookups and the memoised role closures WERE
present; the threaded search budget, the `labelsOf` lookup and the
hoisted per-axiom label reads were NOT. A fourth item,
`differentFromIdx`, was defined and never called — dead code
described in a commit message as a fix.

📊 With all of them actually applied, the whole `--dl` run goes from
**26 minutes 34 seconds to 4 minutes 30 seconds** — a 5.9× speedup —
and the score goes UP by one case. So the conclusion "three of the
four bought nothing" was drawn from a measurement of code that did
not contain them.

### The rules this buys

1. **A script that edits a file must write after EACH replacement,
   or verify the write.** All-or-nothing batching plus per-step
   progress printing is a lie generator: the output says four edits
   landed, the file has one.
2. **A green build is not evidence that an edit landed.** The
   unchanged file also builds.
3. **Before writing a performance claim into a commit message, GREP
   THE FILE for the change.** One `grep -c` per claim. The wave-2
   commit made five claims and three were false; one `grep -c` each
   would have caught all three in under a minute.
4. **A measurement is a measurement OF A BUILD.** Record which build,
   and re-measure after any edit that was not verified to land.

This is the same family as anti-pattern #27 (an agent commit landing
on a newer tip silently drops module-list entries — the build exits 0
and the feature is not built). Both are: the tooling reported success
for work that did not happen.

## Wave 3: the ≤-rule, and the run that got 5.9× faster

📊 `lake exe l4owl-probe --dir third_party/testing/owl --dl`

| Catalog | RL only | Wave 1 | Wave 2 | Wave 3 |
| --- | --- | --- | --- | --- |
| profile-RL.rdf | 117 pass, 9 fail (out of 126) | 118 pass, 8 fail | 118 pass, 8 fail | 118 pass, 8 fail |
| profile-EL.rdf | 102 pass, 18 fail, 1 skip (out of 121) | 107 pass, 13 fail | 109 pass, 11 fail | 109 pass, 11 fail |
| profile-QL.rdf | 82 pass, 5 fail (out of 87) | 82 pass, 5 fail | 82 pass, 5 fail | 82 pass, 5 fail |
| type-positive-entailment.rdf | 315 pass, 93 fail, 4 unsup (out of 412) | 318 pass, 90 fail | 318 pass, 90 fail | 318 pass, 90 fail |
| type-consistency.rdf | 485 pass, 94 fail, 4 unsup (out of 583) | 485 pass, 94 fail | 485 pass, 94 fail | 485 pass, 94 fail |
| type-inconsistency.rdf | 30 pass, 97 fail, 1 skip (out of 128) | 67 pass, 60 fail | 80 pass, 47 fail | 81 pass, 46 fail |
| **TOTAL** | **1131 pass, 316 fail** | **1177 pass, 270 fail** | **1192 pass, 255 fail** | **1193 pass, 254 fail (out of 1457)** |

| | Wall |
| --- | --- |
| Wave 2 as committed | 26 m 34 s |
| Wave 3, with the wave-2 fixes actually applied | 4 m 30 s |

### The ≤-rule, and why the first version of it did nothing

`clashForLabel`'s `maxCard` case counts only PROVABLY DISTINCT
successors and never counts witnesses at all. A node with more
successors than `≤ k p` allows, none of them forced apart, is not
seen by it — and that is the shape of seventeen
`WebOnt-description-logic` inconsistency fixtures. The SHIQ ≤-rule
closes it: identify two successors not yet forced apart, pool their
labels, and keep going.

The first implementation REWROTE EDGES: redirect every `extra` edge
mentioning the absorbed node, move its labels, drop its node. On an
isolated hand-built graph it worked and `refute` returned
`some false`. On the corpus it changed NOTHING.

The reason: the `--dl` regime runs the materialisation pass FIRST,
and that pass writes its own existential witnesses INTO the graph.
By the time the refuter sees them they are graph-asserted blank
nodes, not entries in `extra` — and an edge in the input graph cannot
be rewritten. Every successor that mattered came from there.

The fix is the F\* module's own answer for named individuals, applied
to all of them: identification at READ TIME. `RState.ident` records
(absorbed, representative) pairs; `labelsOf` pools the group's labels
and `successorsOf` maps its results through the representative, so a
merge REDUCES the count a `≤ k` bound is measured against without
touching an edge.

⚠️ Worth keeping: the hand-built guard passed for the rewriting
version. A single synthetic graph proved the rule correct and said
nothing about whether it would ever FIRE on the real input — which is
the `measuring-inference` lesson about synthetic shapes lying about
real vocabularies, in the one place I did not expect it.

### Closure scaffolding is now inert

`RLRules.lean` materialises `__rl_`-prefixed blank nodes as support
triples for blank-node conclusion matching, with an encoding
deliberately looser than the class expression they resemble. The
refuter was parsing them as real class expressions. The F\* module
guards against exactly this and says reading them literally
MANUFACTURES refutations of consistent premises; the guard is now
ported. It changed no score on this corpus, which is what a
soundness guard that is not yet being violated looks like.

### Wave 3b — the one line the ≤-rule was waiting on

After the ≤-rule landed, `type-inconsistency.rdf` moved by ONE case.
Following hazard #27's own rule — instrument whether the rule fires
before assuming it is incomplete — a scratch driver ran
`WebOnt-description-logic-003` through the real pipeline and printed
the state:

```
premise triples: 36
closed: 136 triples, 3 rounds
materialised: 144 triples
reclosed: 166 triples
axioms: 67, nodes: 23
quiet after 1 rounds
pendingMerge: (some 6)
  merge bw_f1 <- bw_f3 => open'
  merge bw_f1 <- bw_f2 => open'
  … all six open'
refute 16: none
```

The rule FIRED — six candidate pairs — and every branch stayed open.
The pooled labels of the merged nodes did not contain the
contradiction, because one filler had never been put on any node at
all.

`ensureWitnesses` tested whether `i` had `k` `p`-successors. It has
to test whether `i` has `k` `p`-successors CARRYING THE FILLER. The
difference is invisible while every existential's filler is a named
class, because the materialisation pass emits `(_:bw rdf:type C)`
for those. For an anonymous filler — `∃f2.¬p1`, where `¬p1` is a
blank node — it emits the EDGE ONLY. The count then said
"discharged", no witness was minted, and `¬p1` was never a label
anywhere.

One line, seven cases:

📊 `type-inconsistency.rdf`, out of 127 decided: 81 pass, 46 fail →
**88 pass, 39 fail**. TOTAL 1193 → **1200 pass, 247 fail (out of
1457)**, in 4 m 33 s. No catalog regressed.

The shape worth keeping: an existential rule that counts EDGES
instead of MEMBERSHIPS is right on every example whose filler is
named, and silently drops the obligation on every example whose
filler is not. Both hand-built guards in `RefuteTests.lean` used
named fillers. The corpus case that exposed it used an anonymous one,
and the failure it produced was not a wrong answer — it was a rule
one layer up firing correctly and finding nothing.

### Wave 3c — the budget the threading paid for, and four graph rules

Once the budget was actually THREADED, its cost became close to
linear in it, so the default could be raised. The old per-branch
form could not afford that: at 24 it took 76 seconds.

📊 `type-inconsistency.rdf`, out of 127 decided:

| Budget | Score | Wall |
| --- | --- | --- |
| 16 | 88 pass, 39 fail | 1.9 s |
| 24 | 90 pass, 37 fail | 2.2 s |
| 40 | 90 pass, 37 fail | 2.8 s |
| 64 | 92 pass, 35 fail | 3.5 s |
| 200 | 92 pass, 35 fail | 6.6 s |
| 400 | 92 pass, 35 fail | 9.6 s |

64 is the new default — where the curve flattens. Above it nothing
more closes: the rest need RULES, not budget. `WebOnt-description-
logic-003` was one of them, and the instrumented run showed why —
all six merge branches clashed, and only the budget stood between
that and a verdict.

Four graph-level violations added, each a shape with no model and no
expansion needed:

* **G6** — `owl:Thing owl:equivalentClass owl:Nothing`. Direct
  Semantics requires a non-empty domain and interprets `owl:Thing`
  as the whole of it.
* **G7** — two DIFFERENT properties declared
  `owl:propertyDisjointWith` sharing a subject-object pair. (G3
  already had the self-disjoint case, which the RL marker misses for
  the opposite reason.)
* **G8** — two members of one `owl:AllDisjointProperties` sharing a
  pair.
* **G9** — an `owl:AsymmetricProperty` with a pair in both
  directions, or an `owl:IrreflexiveProperty` with a reflexive pair.

Each is pinned in `RefuteTests.lean` NEXT TO the nearest satisfiable
graph. The pairing is the check: either half alone can be passed by
an engine that has the rule backwards.

### 📊 Where the OWL probe stands

`lake exe l4owl-probe --dir third_party/testing/owl [--dl]`,
2026-08-23:

| Catalog | RL closure only | `--dl` |
| --- | --- | --- |
| profile-RL.rdf | 117 pass, 9 fail (out of 126) | 118 pass, 8 fail |
| profile-EL.rdf | 102 pass, 18 fail, 1 skip (out of 121) | 110 pass, 10 fail, 1 skip |
| profile-QL.rdf | 82 pass, 5 fail (out of 87) | 83 pass, 4 fail |
| type-positive-entailment.rdf | 315 pass, 93 fail, 4 unsup (out of 412) | 318 pass, 90 fail, 4 unsup |
| type-consistency.rdf | 485 pass, 94 fail, 4 unsup (out of 583) | 485 pass, 94 fail, 4 unsup |
| type-inconsistency.rdf | 30 pass, 97 fail, 1 skip (out of 128) | 94 pass, 33 fail, 1 skip |
| **TOTAL** | **1131 pass, 316 fail, 2 skip, 8 unsupported (out of 1457)** | **1208 pass, 239 fail, 2 skip, 8 unsupported** |

4 m 50 s. The F\* line for `type-inconsistency.rdf` is 126 pass, 1
fail (out of 127); the Lean tree reaches 94 pass, 33 fail.

⚠️ `type-consistency.rdf` is unchanged in both columns and still
hides the same trade Addendum 4 named: three positive-entailment
cases gained, three consistency cases lost
(`WebOnt-description-logic-018`, `-020`, `-021`).

## HDT: the container reader, and a fixture pair that nothing measured

`third_party/testing/hdt/` has held two HDT v1 files since 2026-07-28.
They were written by the reference implementation, hdt-cpp 1.3.3, and
the directory's README records a published SHA-256 for each. The F\*
tree reads them. The Lean tree had no reader, so the fixtures
contributed no Lean number at all.

`L4Factoidal/HDT/Container.lean` is the port of
`formal/fstar/HDT.Container.fst`. It parses the container skeleton:
the Global control information (`$HDT` cookie, format IRI, properties,
CRC16), the Header control information and its N-Triples metadata
text, the Dictionary control information and the byte boundaries of
its four Plain-Front-Coding sections, and the Triples control
information. Every control block's CRC16 is checked.

### Three F\* definitions have no work to do here

The F\* module is 644 lines; the Lean module is 502. The difference is
not compression — it is three definitions that exist only to work
around the F\* tree's I/O boundary.

| F\* definition | Why it exists there | Why it is absent here |
|---|---|---|
| `hdt_file_size`, `hdt_probe_fail_pow`, `hdt_size_bsearch` | `Parquet.Footer.parquet_read_range_hex` does not report a file size, so the size is discovered by an exponential probe and a binary search over read attempts | `IO.FS.readBinFile` returns a `ByteArray` and `.size` is a field |
| `hdt_bytes_of_hex`, `collect_bytes` | that boundary hands back a hex STRING, which must be decoded before anything can index it | `readBinFile` gives bytes |
| `nat_xor` | bitwise XOR built out of `/`, `%` and `*`, because `FStar.UInt32`'s stdint externals have no js_of_ocaml realisation | `UInt16.xor` is a primitive |

The container parsing itself is ported rule for rule.

### One deliberate difference, and it is a correction

`bytes_to_string_acc` in F\* maps each byte through
`Parser.NTriples.safe_char_of_int`: one character per byte, Latin-1
style. In OCaml that reproduces the file's bytes, because an OCaml
string IS a byte string. A Lean `String` is UTF-8, so the same
per-byte mapping re-encodes every byte above 0x7F as two bytes and
corrupts UTF-8 header metadata. `bytesToString` decodes the range as
UTF-8 first and falls back to the per-byte mapping only when the range
is not valid UTF-8. On ASCII input — every control block — the two
agree byte for byte. Neither fixture has non-ASCII header metadata, so
this difference is not yet exercised by a test.

### The measurement

`lake exe l4hdt` (Harness/HdtProbe.lean), from the repository root:

**HDT container: 2 pass, 0 fail (out of 2).**

A pass count of 2 is weak evidence on its own. The stronger check is
`tools/hdt-tree-differential.sh`, which runs both trees' probes with
`--verbose` and diffs the output. Both print the same skeleton: every
control block's byte offsets, format IRI, property string and CRC16
(stored AND computed), the header data range, the four PFC sections'
boundaries, string counts, packed byte counts and block sizes, the
triples data offset, and the header triple count from each tree's own
N-Triples parser.

**HDT container, F\* vs Lean 4: 2 agree, 0 differ (out of 2)** — 28
skeleton lines identical per fixture. One line of wording differs (the
F\* probe names its parser module, the Lean probe does not) and the
script normalises it rather than leaving a difference to appear every
run.

Both fixtures report `format=<http://purl.org/HDT/hdt#HDTv1>`, 22
header triples, `order=1`, and dictionary string counts of
(shared 0, subjects 1, predicates 1, objects 1) for
`rdf-mt-test002.hdt` and (39, 45, 22, 134) for
`rml-core-ontology.hdt`.

### The two lemmas

`L4Factoidal/HDT/ContainerTheorems.lean` ports
`lemma_parse_control_info_rejects_bad_cookie` and
`lemma_bad_global_cookie_rejects_container`. The module is a READER,
so the writer/reader round-trip property that applies to companion-file
modules has nothing to say about it. What its consumers rely on is
that a corrupted container is refused rather than accepted as some
other structure. Both hold by unfolding, and `#print axioms` reports
`[propext, Classical.choice, Quot.sound]` for each — no `sorry`, no
`axiom`, no `native_decide`.

### Still absent

`HDT.Dictionary` (519 F\* lines, the PFC dictionary decode and the
ID↔term mapping) and `HDT.Triples` (316 lines, the bitmap triples
decode). Until those land, the Lean tree can say what an HDT file
contains but cannot read a triple out of one. `bin/hdt-probe/check.sh`
already pins the F\* side of both stages, so the target numbers are
known before the port starts.

## HDT stage 2: the PFC dictionary, and a byte/character correction

`L4Factoidal/HDT/Dictionary.lean` ports
`formal/fstar/HDT.Dictionary.fst`: CRC8 and CRC32C over the payloads
stage 1's CRC16 does not reach, log-array integer unpacking, Plain
Front Coding block decode, both access patterns (`decodeSection` for a
full dump, `pfcExtract` / `pfcLocate` for lookup), the four-section ID
space, and the dictionary-string ↔ `Term` mapping.

### Four F\* definitions are absent

`nat_sub` joins the three that stage 1 dropped. The F\* module defines
a saturating subtraction because its byte offsets are `nat` and Z3
cannot re-derive the container invariants that keep the differences
non-negative. Lean's `Nat` subtraction already truncates at zero, so
`a - b` IS `nat_sub a b`. `bit_divisor` also shrinks: the F\* module
enumerates the eight shift cases to hand Z3 a positive literal, where
Lean writes `2 ^ shift`.

### One correction: the common prefix is measured in BYTES

`pfc_read_suffix` in F\* takes the front-coded common prefix with
`FStar.String.sub prev 0 plen`. `plen` is a byte count read from the
file; `FStar.String.sub` counts CHARACTERS. The two agree on ASCII and
diverge above 0x7F. `pfcReadSuffix` splices `prev.toUTF8.extract 0 plen`
with the suffix bytes and decodes the result, which is what the format
specifies.

Both vendored fixtures are pure ASCII in every dictionary section, so
no test distinguishes the two. The F\* module's own header records the
same ASCII-only scope. This is written down as a difference, not
claimed as a fixed defect: nothing has exercised it.

The same ASCII-only caveat applies to `pfcLocate`'s binary search,
which assumes the block heads are in the format's byte-wise order
while Lean's `String` `<` compares codepoint sequences.

### A bracketed IRI is accepted, in both trees

`termOfString "<http://example.org/a>"` returns the IRI
`<http://example.org/a>` — brackets included — rather than rejecting
it. `isIri` (port of `RDF.Term.is_iri`) is the minimal gate the whole
tree applies: non-empty and contains a colon. HDT stores IRIs
unbracketed and hdt-cpp never writes a bracketed one, and the
string↔term round trip still holds for it, so this is recorded in the
module's `#guard`s rather than guarded against.

### The measurement

`lake exe l4hdt --verbose` now prints the three stage-2 blocks in the
same line shapes as `bin/hdt-probe/hdt_probe.ml`, and
`tools/hdt-tree-differential.sh` diffs them along with the container
skeleton.

**HDT container, F\* vs Lean 4: 2 agree, 0 differ (out of 2)** — 42
container and dictionary lines identical per fixture, up from 28.

Per fixture, matching the pins in `bin/hdt-probe/check.sh`:

| | rdf-mt-test002 | rml-core-ontology |
|---|---|---|
| shared: decoded / expected / term-parse | 0 / 0 / 0 | 39 / 39 / 39 |
| subjects | 1 / 1 / 1 | 45 / 45 / 45 |
| predicates | 1 / 1 / 1 | 22 / 22 / 22 |
| objects | 1 / 1 / 1 | 134 / 134 / 134 |
| all four CRCs per section | OK | OK |
| per-section ID round trip | 3 pass, 0 fail (out of 3) | 240 pass, 0 fail (out of 240) |
| role-level round trip | 3 pass, 0 fail (out of 3) | 279 pass, 0 fail (out of 279) |

The role-level figure is where the shared-section arithmetic is
exercised: 84 subject IDs (39 shared + 45 subjects), 22 predicate IDs,
173 object IDs (39 shared + 134 objects).

Build-time `#guard`s check CRC8 and CRC32C against their published
catalogue check values over the nine bytes `123456789` — 0xF4 for
CRC-8/SMBUS and 0xE3069283 for CRC-32/ISCSI. Those check the
parameters, not the code's agreement with itself.

### Still absent

`HDT.Triples` (316 F\* lines): the BitmapTriples decode — the two
bitmaps, the two log-array sequences, and rank/select over them. The
Lean tree can say what an HDT file's dictionary holds but cannot
enumerate a triple. The F\* probe's stage 3 already pins the target
numbers: for `rml-core-ontology.hdt`, 343 id-triples decoded with 0
unresolved, and enumeration equal to the source `.nt` as sorted
N-Triples.

## HDT stage 3: BitmapTriples, and the enumeration matches the source

`L4Factoidal/HDT/Triples.lean` ports `formal/fstar/HDT.Triples.fst`.
With it the HDT group is complete: 1,479 F\* lines across three
modules, all ported.

### The structure

The Triples section holds four sub-structures in the order hdt-cpp
writes them: bitmap(Y), bitmap(Z), log-array(Y), log-array(Z). ArrayY
holds one predicate ID per (subject, predicate) pair in subject-major
order, and BitmapY[i]=1 marks the last such pair for its subject.
ArrayZ holds one object ID per triple in the same order, and
BitmapZ[i]=1 marks the last object of its (subject, predicate) pair.
Subject IDs are the dictionary's `Role.subject` space.

So the file is a two-level SPO forest, and `childrenRange` is the one
primitive that decodes a range at either level.

`rank1` and `select1` are linear scans with no auxiliary index.
Everything above them reaches a bitmap only through `rank1`, `select1`
and `childrenRange` — never through `bitAt` or raw byte offsets,
except inside those three definitions. Replacing the scans with
superblock and block popcount counters changes those three and nothing
else.

### Differences from the F\*

`nat_sub` is absent, as in stage 2. `walk_y_positions` and
`hdt_enumerate_subjects` accumulate with `acc @ new`, which is
quadratic in the triple count; both accumulate reversed here and
reverse once.

### The measurement

`tools/hdt-tree-differential.sh` now passes each fixture's source
document to both probes and diffs the stage-3 blocks too.

**HDT reader, F\* vs Lean 4: 2 agree, 0 differ (out of 2)** — 54
container, dictionary and triples lines identical per fixture, up from
42.

| | rdf-mt-test002 | rml-core-ontology |
|---|---|---|
| all six triples-section CRCs | OK | OK |
| triple count (ArrayZ entries) | 1 | 343 |
| (s,p) pairs (ArrayY entries) | 1 | 335 |
| num subjects (BitmapY ones) | 1 | 84 |
| dictionary role max, independently | 1 | 84 |
| bitmapY `rank1(select1 k) = k+1` | 1 pass, 0 fail (out of 1) | 84 pass, 0 fail (out of 84) |
| bitmapZ same | 1 pass, 0 fail (out of 1) | 335 pass, 0 fail (out of 335) |
| id-triples decoded (unresolved) | 1 (0) | 343 (0) |
| enumeration vs source, sorted N-Triples | MATCH | MATCH |

The last row is the strongest check either tree makes. It enumerates
every triple out of the HDT file, resolves all three IDs through the
dictionary, serialises the result and the source `.nt` as canonical
N-Triples, sorts, and compares. A single term, ID or bit decoded
wrongly fails it. The differential script refuses to report agreement
for a fixture whose Lean run did not reach that MATCH, so a run that
stopped early cannot pass as a clean one.

The `num subjects` row is a cross-check rather than a restatement:
the count comes from BitmapY's ones, and the row below it comes from
the dictionary section sizes, which are independent.

### What HDT still does not do here

The reader is complete; the write path is not ported and neither tree
has one — `bin/hdt-probe/` reads, and `third_party/testing/hdt/
mini_rdf2hdt.cpp` is how the fixtures were made. Stage 5 of the
program plan (indexed rank/select behind the same three names) is
open in both trees.

## XSD.IEEE754: checked against a correctly-rounded implementation, not against itself

`L4Factoidal/XSD/IEEE754.lean` ports `formal/fstar/XSD.IEEE754.fst`:
decimal lexical to IEEE-754 value, for `xsd:double`, `xsd:float` and
`rdf:JSON` numbers. Every definition is exact big-integer rational
arithmetic; no floating point appears anywhere in the module.

### Three F\* definitions shrink

`pow2` and `pow10` become `2 ^ n` and `10 ^ n` — the F\* recursions
exist to carry a `pos` refinement. `bitlen` becomes `Nat.log2 n + 1`
for `n > 0`, the same function its recursion computes. `mul_pos` is
absent: it keeps a `pos` type through a multiplication without per-site
SMT nudging, and Lean's `Nat` multiplication carries no such
obligation.

### The test is the point

A test that restates the rounding algorithm proves nothing about it.
`IEEE754Tests.lean` holds 66 lexicals converted by CPython's `float()`
— a correctly-rounded `strtod` — with the bit patterns read out by
`struct.pack('>d', …)` and `struct.pack('>f', …)`, and compares them
against this module's output through `fvalToBits64` / `fvalToBits32`.

**66 rows match, bit for bit, in binary64 and binary32. 0 differ.**

The table is chosen for the cases where an implementation goes wrong,
not for round numbers:

| Case | Why |
|---|---|
| `9007199254740992` … `95` | the 2^53 boundary: four consecutive integers pin the ties-to-even direction where doubles stop being exact |
| `16777216`, `16777217`, `16777219` | the 2^24 boundary, same question for binary32 |
| `1.0000000000000001` vs `…02` | one-ulp neighbours: one rounds down, one up |
| `5e-324`, `2.5e-324`, `2.4e-324` | the smallest subnormal and its exact halfway point — ties-to-even at the bottom of the grid |
| `2.2250738585072011e-308` | the decimal that hung PHP's `strtod` in 2011, and its normal neighbour |
| `1.8e308`, `1e400` | overflow to infinity, at two magnitudes |
| `1e-46` | underflow to zero, below the subnormal grid |
| `1000`, `1e3`, `0.001e6`, `100000e-2` | one value, four lexicals |
| 60-digit exact expansion of a double | a long digit string that must not lose the tie |
| `-0.0`, `INF`, `-INF`, `NaN` | signed zero, both infinities, the value equal to nothing |

`fvalToBits64` and `fvalToBits32` exist only for that comparison.
Nothing in the port uses them.

### Two engine defects found, filed not fixed

https://github.com/danbri/factoidal/issues/552, present identically in
BOTH trees, so neither is a port regression:

1. `FILTER(?v = "1.0"^^xsd:double)` returns **zero** rows against data
   holding `"1"^^xsd:double` and `"1.0"^^xsd:double`, where SPARQL 1.1
   §17.3 requires two. `FILTER(?v = 1.0e0)` on the same data returns
   two. A numeric literal TOKEN becomes a numeric expression node and
   is promoted; a typed-literal node stays a term and never reaches
   `numericCompare`. Repo anti-pattern #6 at a place nothing had
   checked.
2. `=` on two `xsd:double` operands compares EXACT DECIMAL values
   (`parseDoubleToScaled`), not IEEE-754 values, so
   `"9007199254740992"^^xsd:double = "9007199254740993"^^xsd:double`
   is false where the specification makes it true — both lexicals
   denote 2^53. `XSD.IEEE754.doubleValueEq` decides this correctly and
   is checked against CPython on exactly that pair, but only the
   D-entailment regime calls it. Two parts of the engine disagree
   about which doubles are the same value.

The primitives are right in both trees; what is missing is the wiring.
`literalValueEqNumeric` and `valueCompare ∘ literalPromote` both answer
`"1"^^xsd:double = "1.0"^^xsd:double` correctly when called directly.

## SHACL: the 1.2 suite was vendored and never run

`l4shacl` takes a manifest path, so the SHACL 1.2 suite was always
reachable. Its default is the SHACL 1.0 `data-shapes-test-suite`, and
that is the only row the dashboard carried. Pointing it at the other
manifests, with `tools/lean-shacl-scores.sh`:

| Suite | Lean 4 | F\* |
|---|---|---|
| shacl 1.0 core | 98 pass, 0 fail (out of 98) | 98 pass (out of 98) |
| shacl 1.2 core | 103 pass, 30 fail (out of 133) | 138 pass (out of 138) |
| shacl 1.2 node-expr | 0 pass, 2 fail (out of 2) | 142 pass (out of 142) |
| shacl 1.2 sparql | 22 pass, 3 fail (out of 25) | 25 pass (out of 25) |
| shacl 1.2 rules | 0 pass, 0 fail (out of 0) | 88 pass (out of 88) |

⚠️ `out of 2` and `out of 0` are not pass rates. The probe did not READ
those tests: the shnex tests are typed `sht:EvalNodeExpr` and link
entries with `mf:entries`, while `Harness/ShaclProbe.lean` recognises
`sht:Validate` and walks `mf:include`; the rules directory has no
`manifest.ttl` at all, only `manifest-rules.ttl`, whose tests use
`srt:` types. Pointed at the right file the probe reports
`zero_tests=1` in its `HARNESS-DIAG` line, so the diagnostic that
exists to catch this did fire.

The script labels the unread rows as unread, because printing `out of
0` beside `out of 88` without saying so is anti-pattern #3.

Three separable pieces of work, filed as
https://github.com/danbri/factoidal/issues/553:

1. 30 real failures on shacl 1.2 core, read correctly and answered
   wrongly — 13 in `core/node`, 11 in `core/property`, 3 in
   `core/targets`, 2 in `core/misc`, 1 in `core/validation-reports`.
   `sh:targetWhere` and `sh:conformanceDisallows` look like
   unimplemented SHACL 1.2 features rather than bugs in existing code.
   The core denominator is also 133 against the F\* tree's 138, so five
   more are unread even in the row that mostly works.
2. 3 failures on shacl 1.2 sparql.
3. node-expr and rules need `SHACL.NodeExpr` (713 F\* lines) and
   `SHACL.Rules` (438) ported AND the probe extended. Doing the harness
   half first gives a large honest failure count instead of a silent
   zero, which is the better intermediate state.

## A batch of five: Dep, RDFS delta evaluation, and three accessor modules

| F\* module | Lines | Lean |
|---|---|---|
| `Dep.Reachability` | 170 | `L4Factoidal/Dep/Reachability.lean` |
| `RDFS.Closure.SemiNaive` | 421 | `L4Factoidal/RDFS/SemiNaive.lean` |
| `RDF.Dataset.Graphs` | 27 | `L4Factoidal/RDF/DatasetGraphs.lean` |
| `SPARQL.Update.Analysis` | 31 | `L4Factoidal/SPARQL/UpdateAnalysis.lean` |
| `SPARQL.Query.Analysis` | 53 | `L4Factoidal/SPARQL/QueryAnalysis.lean` |

### `Dep.Reachability`

The verified reachability core the module-liveness tool calls instead
of an unverified Python breadth-first search. Its point is that the
theorem's premises — `isClosed` and `contains` — are DECIDABLE and the
driver re-checks them on the algorithm's real output, so neither the
fuel bound nor the closure implementation is trusted.

`reaches` is a `Type`-valued GADT in F\* because the proof recurses on
the derivation term; in Lean it is a `Prop`-valued inductive proved by
`induction`. `no_root_reaches`'s `FStar.Classical.impl_intro` and
`introduce … with` block disappear, because `¬P` IS `P → False` in
Lean. `#print axioms` reports `[propext, Quot.sound]` for both
theorems.

The `#guard`s check that `isClosed` REJECTS a set that is not closed.
Without that, the checks that the algorithm's output passes `isClosed`
would prove nothing about whether the re-check has teeth.

### `RDFS.SemiNaive`

Delta evaluation: apply a rule only where at least one premise is new,
`Δout = (ΔB1 ⋈ B2_full) ∪ (B1_full ⋈ ΔB2)`. Both terms are needed;
dropping either loses derivations.

Every row of `RDFS.Closure` has the shape `Graph → Triple → List Triple`
with the searched graph first, so one combinator (`rowDelta`) states the
delta term once for all six rows. The F\* module writes it out by hand
for each of its twelve.

`closureSemiNaiveChecked` runs the delta loop and then applies one full
naive `step`. If that adds nothing, the result is a fixed point of the
naive step containing the input, and since the naive closure is the
least such fixed point the two are equal. If it adds something, the
result is discarded and `closureFix` runs. **A hole in the delta
reasoning costs a slow run, never a wrong answer.**

**Measured**, `lake exe l4rdfs-semi`:

**delta vs naive closure: 6 agree, 0 differ (out of 6)** — subclass
chains and property hierarchies at 20, 50 and 100 input triples,
closures of 210 to 5,056 triples.

**delta loop reached the fixpoint without the fallback: 6 of 6.** This
second line is the one that matters: a run where the fallback fired
would still report `agree`, because the fallback returns the naive
answer. Reporting only the first line would be a vacuous pass.

⚠️ **Speed is NOT measured, and the module exists for speed.** Three
timing attempts all reported 0 ms for both closures while the process
spent 90 s of CPU on a run whose largest input is 100 triples. The
clock and the forcing technique both work — a standalone binary using
the same `clockAfter` reports 5723 ms for a 20-million-step fold — so
what is unestablished is where the 90 s goes. `isNaiveFixpoint` and
`sameGraph` are both superlinear in the closure size and either could
dominate, but that is a hypothesis, not a measurement. The harness
prints no speed column, because one that always reads 0 reads as
"instant" when the truth is "not measured". Tracked in
https://github.com/danbri/factoidal/issues/554.

### The three accessor modules

`RDF.Dataset.Graphs` is `FROM NAMED`'s universe as a pair list plus a
named-graph lookup. Its F\* `graph_ref` is `iri` with a comment saying
the type also carries the `_:<label>` blank-node graph-name convention;
Lean's `NamedGraph.name` is already `Subject`, so the convention is in
the type rather than in a comment on a string.

`SPARQL.Update.Analysis` is `updateHasLoad`, which the HTTP layer
consults before rejecting an update with 501. `SPARQL.Query.Analysis`
is `bgpsInQuery`, which the explain dump walks. Both were migrated out
of OCaml in the F\* tree per iron rule #1 and stay that way here.

`SPARQL.QueryAnalysis`'s `#guard`s compare rendered forms rather than
values: `TriplePattern` derives `Repr` and not `BEq`. The order check
asserts BOTH that `collectBgpsAux` returns last-seen-first AND that
`bgpsInQuery` returns source order, so a reverse that silently stopped
happening would fail.

## A batch of four: manifests, blank-node scoping, format labels, JSON escaping

| F\* module | Lines | Lean |
|---|---|---|
| `RDF.Canonical.Manifest` | 38 | `L4Factoidal/RDF/CanonicalManifest.lean` |
| `RDF.Dataset.Merge` | 69 | `L4Factoidal/RDF/DatasetMerge.lean` |
| `RDF.Format` | 103 | `L4Factoidal/RDF/Format.lean` |
| `SPARQL.JSON.Escape` | 97 | `L4Factoidal/SPARQL/JsonEscape.lean` |

### `RDF.Dataset.Merge`: a difference the type system absorbs

`rename_graph_name` in F\* takes a plain string and tests for a `"_:"`
prefix, because the F\* `named_graph`'s name slot is IRI-typed and
blank-node graph labels ride inside it as the literal string
`"_:<label>"` — the Parser.NQuads convention, also used by TriG and
JSON-LD. Lean's `NamedGraph.name` is `Subject`, which is `iri | bnode`,
so a blank-node graph name IS a blank node and the prefix goes straight
on its label. The string-prefix test disappears, and with it the chance
of a graph name that merely LOOKS like a blank node being renamed.

The `#guard`s state the bug the module exists for — the Jena ARQ probe's
graph-09 and graph-10b, where `_:x` from two separately loaded files
joined — as a check that `_:x` from two documents does NOT collide after
renaming, and that `_:x` used twice WITHIN one document still does.
Both directions are needed: a rename that freshened every occurrence
would pass the first and fail the second.

### `RDF.Format`: two tables that must not be one

`format_of_extension` takes a LEADING DOT (`".ttl"`); `format_of_string`
takes a bare label (`"ttl"`). The F\* name `format_of_string` is
`formatOfLabel` here, because both functions take a string and only
their guards say they are not interchangeable. Those guards are
explicit: `formatOfExtension "ttl"` is `none` and
`formatOfLabel ".ttl"` is `none`.

The F\* module uses an `if`/`else if` chain rather than a `match` on
string literals because KaRaMeL's C extraction rejects the latter
(warning 250). Lean has no such constraint; the chain is kept so the two
trees' tables are one diff apart rather than a restructure apart.

### `SPARQL.JSON.Escape`: the byte-versus-codepoint trap, twice

The F\* module's header records what its first implementation got wrong,
and both failures are the same distinction:

1. Escape pairs mirrored relative to a final `rev` — `"n\\"` instead of
   `"\\n"`. The npm bundle was the first strict-JSON consumer and
   crashed on it.
2. Pass-through bytes at or above 0x80 double-encoded, because the walk
   read BYTES while the extracted `string_of_list` re-encoded each list
   element as a UTF-8 CODEPOINT. `"café"` became `"cafÃ©"`.

F\* fixed both by slicing maximal runs of non-special bytes with
`fs_byte_sub`, which is byte-transparent.

The Lean tree has no `Parser.FastString` counterpart by design, so this
walks `String.toUTF8` and builds a `ByteArray`, decoding once at the
end. A byte at or above 0x80 is copied into the output buffer and never
passes through `Char`, so failure 2 cannot occur; the escape strings are
byte literals, so failure 1 cannot occur. The `#guard`s check both
anyway, and they check the BYTE LENGTH of `"café"` and `"日本語"` rather
than the rendered string — a double-encoding that round-trips through
`Char` can still print plausibly.

One more guard states a rule that is easy to get wrong in the other
direction: 0x7F DEL is NOT escaped. "Control character" and "byte below
0x20" are different sets, and only the second one is the rule.

## A batch of three: the two circuit breakers and the annotation filter

| F\* module | Lines | Lean |
|---|---|---|
| `SPARQL.Eval.Limits` | 128 | `L4Factoidal/SPARQL/EvalLimits.lean` |
| `SPARQL.Eval.TimeBudget` | 133 | `L4Factoidal/SPARQL/TimeBudget.lean` |
| `OWL.DirectMapping.Filter` | 71 | `L4Factoidal/OWL/DirectMappingFilter.lean` |

### `EvalLimits`: both properties proved, not demoted

The F\* module proves the row cap's two properties, and so does this
one — `takeCapped_length_le_cap` is what makes the breaker a breaker,
and `takeCapped_unlimited_id` is what makes a disabled cap free. Both
carry `[propext, Quot.sound]`.

One restatement: the F\* helper lemma puts an `if taken >= max_rows`
inside its conclusion. Here `taken < c.maxRows` is a hypothesis and the
at-cap case is its own lemma. Same content, and Lean's `omega` closes
the arithmetic without the `if` in the way.

The `#guard`s state the sentinel in the direction that is easiest to get
backwards: a cap of 0 is UNLIMITED, not "keep nothing". Getting it wrong
turns "no cap" into "every query returns empty".

### `TimeBudget`: the Lean tree's realisation surface here is EMPTY

The F\* module carries one `assume val now_ms : unit -> ML int`. It is
its only OCaml realisation, acceptable under iron rule #11(a) as pure
I/O, with its own stub patch (`202_now_ms.sh`).

This module mentions no clock at all. `mkBudgetSecs`, `mkBudgetMs` and
`pollAt` take the current reading as an ARGUMENT; the caller reads
`IO.monoMsNow` once, at the edge. That is the rule `SPARQL/Expr.lean`'s
`EvalEnv.now` already states for §17.4.5.1 `NOW()` — "read once, at the
edge, and passed in; never an ambient clock call" — applied to the same
kind of dependency. So the F\* tree's one `assume val` here has no Lean
counterpart, and the budget logic is a total function of its inputs.

The F\* `ML`-effect `poll` becomes `pollAt`; a caller writes
`pollAt b (← IO.monoMsNow)`.

The `#guard`s pin the sentinel round-trip that matters: `mkBudgetSecs
now 0` must be `noBudget` and NOT a deadline equal to `now`. A deadline
equal to `now` is already expired, so getting it backwards turns "no
timeout" into "already timed out". They also pin the tolerated
backward jump the F\* header describes: a clock that goes backwards
un-expires the budget rather than trapping it.

### `DirectMappingFilter`: the declarations survive the filter

Triples whose predicate is declared `rdf:type owl:AnnotationProperty`
(or the legacy `owl:OntologyProperty`) are excluded before an
OWL-Direct closure sees the graph.

The DECLARATION triples themselves survive, because their predicate is
`rdf:type` and `rdf:type` is never itself so declared. The mapping
specification excludes annotation ASSERTIONS, not the declarations that
identify them, and a filter written as "drop every triple mentioning an
annotation property" gets this wrong. It is a `#guard`.

The F\* module's scope note is carried over verbatim in substance: this
is the "declared in the same graph being filtered" case, which is what
the vendored RIF Core corpus exercises. The built-in OWL 2 annotation
properties that need no declaration, and the `owl:annotated*`
reification triples, are NOT handled — no corpus test exercises them
and adding them speculatively is anti-pattern #4.

### And one module that will not be ported

`RDF.List.Helpers` (195 lines) is tail-recursive replacements for
`FStar.List.Tot`'s `append` and `concatMap`, which overflow the OCaml
stack on long lists — issue #94 on the Turtle path, and the 2026-04-26
BGP filter-map incident. Lean's `List.append` already has a
tail-recursive `@[implemented_by]`, so the module's reason for existing
is absent. It joins `Parser.FastString.*` in the by-design column.

## RDFS-Plus, and a rule row that would have gone missing quietly

`L4Factoidal/RDFS/RDFSPlus.lean` ports
`formal/fstar/RDF.Entailment.RDFSPlus.fst` (93 lines): RDFS plus a small
practical OWL subset — `owl:sameAs` (symmetry, transitivity,
substitution into subject, object and predicate position),
`owl:inverseOf`, `owl:SymmetricProperty`, `owl:TransitiveProperty`,
`owl:FunctionalProperty`, `owl:InverseFunctionalProperty`,
`owl:equivalentClass`, `owl:equivalentProperty`.

The claim level is carried over unchanged: every row has a proved
licensing and truth-preservation lemma in the F\* tree, and **no
chain-level completeness is claimed for this tier**. `owl:sameAs`
introduces equality reasoning, and the Herbrand construction behind the
ρdf completeness theorem does not survive quotienting by sameAs
classes.

### The row that had no Lean counterpart

The F\* step calls `owl_rule_inverseOf_domain_range_flip`, which
`L4Factoidal/OWL/RLClosure.lean` did not have. It is now there as
`inverseOfDomRngFlipFor`, next to prp-inv1 and prp-inv2 — that is its
home when the rest of `OWL.Closure` lands, not the RDFS-Plus module.

The row is not in OWL 2 RL/RDF Table 9. It is sound under both Direct
and RDF-Based Semantics because the extension of an inverse property
pair is the transposition of the other's, and without it the closure
derives the INSTANCE-level consequences but not the schema triple. W3C
SPARQL entailment `sparqldl-11` is what catches the absence.

Dropping it silently was the real risk: the closure would still reach a
fixed point, still pass every `#guard` about sameAs and transitivity,
and derive fewer schema triples than the F\* one. The `#guard` that
`{ :parent owl:inverseOf :child . :parent rdfs:domain :Person }` yields
`:child rdfs:range :Person` is what makes the row load-bearing.

### `eq-ref` stays out, and a check keeps it out

`x owl:sameAs x` for every node is deliberately absent — a noise row
that manufactures one triple per node without feeding any downstream
rule, excluded for the same reason `RDFS.Closure`'s step excludes rdfs6
and rdfs10. Two `#guard`s assert it does NOT appear. An exclusion with
no check for it is an exclusion that comes back.

Every `#guard` is paired with a check that the closure is strictly
larger than its input, so none of them can pass by deriving nothing.

## RDF.Pretty and SPARQL.Explain — and a measurement I got wrong

| F\* module | Lines | Lean |
|---|---|---|
| `RDF.Pretty` | 235 | `L4Factoidal/RDF/Pretty.lean` |
| `SPARQL.Explain` | 104 | `L4Factoidal/SPARQL/Explain.lean` |

### What `RDF.Pretty` deliberately does NOT carry

The F\* module used to hold `term_to_ntriples`, a SECOND N-Triples term
renderer that wrote a literal's lexical form verbatim. It was described
as "for display, not wire", and every consumer treated its output as
wire: `factoidal --dump` and the COTTAS store's object column both went
through it. That is issue #339 (dump emitted output the project's own
parser rejected) and issue #443 (import then query DESTROYED any literal
containing a quote, a newline or a backslash).

The F\* tree DELETED the function rather than fixing it, because making
it escape would have made it byte-identical to
`nq_term_to_string`, and a second name for one rendering is what let the
two drift. This port carries the same absence, and a `#guard` states the
remaining renderer's verbatim behaviour explicitly — so nobody "fixes"
it into a second serialiser.

### `SPARQL.Explain` is absent for a DIFFERENT reason than in F\*

The F\* header says the estimator loop that builds explain rows from a
store is still in OCaml, "blocked on time-budget infra in F\*". That
block is now gone in the Lean tree — `SPARQL.TimeBudget` is ported. The
loop is still absent here, but because `SPARQL11.Store` is not ported.
Different reason, same shortfall, and worth writing down rather than
inheriting the F\* sentence unexamined.

## ❌ A measurement error, and the correction

Earlier in this session I wrote, in the gap document and in a GitHub
comment: "An audit of the whole not-covered list found no other false
negative." **That was wrong.**

The audit matched squashed MODULE NAMES. That method cannot see a
CONSOLIDATION — one Lean module covering two F\* modules under a third
name — and cannot see a rename that changes more than punctuation. It
found `DID.Key` and stopped, and I reported its silence as evidence.

A second audit compared DEFINITION NAMES: every `let` / `val` / `type`
of each not-covered F\* module against every `def` / `abbrev` /
`structure` / `inductive` / `theorem` in the Lean tree, normalised for
case and underscores. It found four more, 1,298 F\* lines:

| F\* module | Lines | Actually covered by |
|---|---|---|
| `RDF.Entailment.Simple` | 182 | `L4Factoidal/RDF/Entailment.lean` |
| `RDF.Entailment.Regime` | 271 | the same file |
| `Parser.CSVResults` | 610 | `L4Factoidal/SPARQL/ResultsCsvTsv.lean` |
| `RDF.Pretty` | 235 | ported this session |

The first two are the consolidation case exactly: one Lean module covers
simple entailment AND the D / RDF / RDFS regimes, which the F\* tree
splits across two files. Its own header says so; a name-based audit
could not read it.

⚠️ One narrow behavioural gap inside that coverage: the F\* `match_term`
takes a POSITION-AWARE literal comparison
(`leq : inside_tt -> literal -> literal -> bool`), because a directional
language string is opaque — case-sensitive — only INSIDE a triple term.
Lean's `entailsWith` has no position flag. The coverage is substantive
but not complete, and the difference is what the W3C
`opaque-dir-language-string` fixtures exercise.

**The rule this pays for:** an audit that finds nothing is evidence
about the AUDIT before it is evidence about the code. State the method
next to the result, and pick a method that can see the failure you are
looking for. Module-name matching cannot see a consolidation, so its
silence about consolidations meant nothing.

## ❌❌ The coverage figure was wrong twice, and the second method was in the tree

Two corrections in one day, both because the AUDIT was wrong rather than
because code landed. Recorded together so the next reader can tell which
number they are looking at.

| Reported | Method | Real |
|---|---|---|
| 120 of 220 | squashed module-name matching | 125 |
| 125 of 220 | + definition-name matching | **130** |

### What each method could not see

**Module names** cannot see a CONSOLIDATION — one Lean module covering
two F\* modules under a third name — nor a substantive rename.
`L4Factoidal/RDF/Entailment.lean` covers BOTH `RDF.Entailment.Simple`
and `RDF.Entailment.Regime`, and its own header says so in its first
sentence. `Parser.CSVResults` became `SPARQL.ResultsCsvTsv`.

**Definition names** are closer but still a proxy. They missed
`RDF.Entailment.Simple` too: Lean writes `termMatch` and `matchSubject`
where F\* writes `match_term` and `match_subj`.

### The method that works, and it was sitting there

**A Lean module's header names the F\* module it ports.** Extracting
every `formal/fstar/X.fst` mention from every Lean header and reading
the sentence around each settles it directly. Five more engine modules,
3,015 F\* lines:

| F\* module | Lines | What the Lean header says |
|---|---|---|
| `RDF.Entailment.RDFS.RhoDFClosure` | 1996 | "Ports the rule set of" |
| `RDF.IRI` | 530 | "Port of" |
| `Parser.SRX` | 291 | "Port of … (parsing)" |
| `Parser.JSONResults` | 160 | "Port of … (parsing)" |
| `SPARQL11.IRI.Resolve` | 38 | both F\* modules delegate to one core |

It settled two the OTHER way as well, which a ratio-based audit would
have scored as near-misses: `SPARQL.FullText` is not covered and
`SPARQL/Parser.lean` says "no Lean" in as many words; `JSONLD.Frame` is
not covered and `JSONLD/Expand.lean` merely lists it as a sibling. And
`Parser.JSONLD` is claimed only as "Port of the toRdf half", so it stays
in the not-covered column rather than being counted on a guess.

### Two fixes, not one

1. `tools/lean-port-gap.py` now GENERATES the classified summary
   (engine / proof / by-design). It was hand-typed, and it drifted three
   times in one session — once per batch of ports, because every landing
   meant editing four numbers by hand and the classification was never
   recomputed.
2. The rule is written into `skills/workflow-gotchas-debugging`
   (hazard #28) and CLAUDE.md (anti-pattern #28): an audit that finds
   nothing is evidence about the AUDIT's reach before it is evidence
   about the code.

### Where that leaves the port

**130 of 220 F\* modules have a Lean counterpart.** Not covered: 63
engine modules / 46,503 lines, 21 proof modules / 24,529 lines (the
wrong measure for that column — the Lean tree has its own theorem
layer), 6 by-design / 1,853 lines.

## SPARQL.FullText — the module the Lean tree said it did not have

`L4Factoidal/SPARQL/FullText.lean` ports
`formal/fstar/SPARQL.FullText.fst` (223 lines): the `text:query`
extension, slice 1 — exact token match, no scoring. `SPARQL/Parser.lean`
recorded its absence in as many words ("whose encoding lives in
`SPARQL.FullText.fst` — no Lean"). That sentence is now stale in the
right direction.

**No ranking claim.** There is no `score_bm25` and no `rank_results`;
a caller applies `limit` in dataset order only. That is slice 1's scope.

### A wrong reason, corrected before it landed

The module header first said: "Lean has `String.toLower`, which is not
the same function — it is Unicode-aware", and a `#guard` asserted the
two folds DISAGREE on `"ÉCOLE"`.

The guard failed. **Measured: Lean's `String.toLower` is ASCII-only.**
`"ÉCOLE".toLower` is `"École"` — `Char.toLower` maps `A`–`Z` and nothing
else — so it agrees with the F\* fold exactly on that input.

The explicit fold stays, for a smaller and true reason: the tokeniser's
floor is part of slice 1's contract and should not move because a
standard-library function's folding scope widened in a later toolchain.
The `#guard` now pins the AGREEMENT rather than asserting a difference
that does not exist.

Worth recording because the failure mode was the same one hazard #28 is
about: I wrote a confident claim about a function's behaviour and gave
it a check that would have passed either way had I stated it loosely.
It only failed because the assertion was sharp.

### Why the object argument is a tagged literal

jena-text's `(property "term" limit)` is ordinary SPARQL collection
syntax, which the parser desugars into an `rdf:first`/`rdf:rest` chain
in a SIBLING pattern joined to the main triple — not a second triple
pattern in the BGP a per-triple evaluation hook sees. Resolving that
generically needs a pattern-level rewrite pass, and it is not what real
magic-property engines do: Jena's ARQ intercepts the argument list
during algebra compilation, before it could become literal `rdf:first`
matching against data with no such triples.

So the parser recognises `text:query` before the generic collection
desugaring runs and encodes the resolved query into one tagged literal.
The field and limit ride in the LEXICAL FORM, delimited by U+001F, so
the user's raw search term is never parsed or escaped — only split out
of its two delimiter-bounded neighbours. A `#guard` round-trips a term
containing commas, semicolons and quotes to state that.

### The guards that state what "exact token match" means

- `"ell"` must NOT match `"Hello"`. That is the difference between this
  and a `CONTAINS` filter.
- An empty query matches anything; an empty candidate matches nothing.
- Order and repetition do not matter, which makes it a token-SET test.
- A literal of any other datatype decodes to nothing — the marker
  datatype is the gate, and without it the codec would read a user's
  ordinary string literal as a query.

## SPARQL.Update.Sandbox — the policy, with checks that state the threat

`L4Factoidal/SPARQL/UpdateSandbox.lean` ports
`formal/fstar/SPARQL.Update.Sandbox.fst` (323 lines). Migrated in the
F\* tree out of `factoidal_http.ml` per iron rules #1 and #15: the policy
is semantics, the HTTP status codes are glue.

### The hand-rolled string scan disappears

The F\* `replace_all_aux` walks the haystack character by character with
`FStar.String.length` and `.sub`, and its own comment says that matches
the previous byte-level OCaml "only when the haystack is ASCII — which
is the case for our auth template". Lean's `String.replace` does the
whole substitution, and `splitOn` gives the prefix, so 60 lines of scan
become two definitions. On ASCII templates the two trees agree; on a
non-ASCII template Lean's is codepoint-correct where the OCaml was
byte-based, and neither tree has a test for that.

`templatePrefix` scans for the literal `{authid}` ANYWHERE, not for the
first `{`. The F\* module pins the stray-brace case with `assert_norm`;
here it is a `#guard`:
`templatePrefix "https://e.org/{x}/{authid}/graph"` is
`"https://e.org/{x}/"`, not `"https://e.org/"`.

### The `#guard`s say what the sandbox is FOR

A policy module's tests are worth little if they only check the happy
path, so each one states a way out of the sandbox and asserts it is
closed:

- an unwrapped template is WRAPPED, not rejected — that is the rewriting
  half of the policy, and a port that only rejected would still pass a
  "rejects other graphs" test;
- a template already wrapped in the sandbox graph is NOT double-wrapped;
- a VARIABLE graph target is rejected — a wrapper that could bind to any
  graph is not a wrapper that targets the sandbox;
- `DEFAULT`, `NAMED` and `ALL` are each rejected separately, because each
  is a different way to reach outside;
- `ADD`, `MOVE` and `COPY` check BOTH ends. A check on the destination
  alone would let data be copied OUT of another graph, and that is the
  one a plausible implementation gets wrong;
- `LOAD` is rejected here as well as at the HTTP layer — two gates, on
  purpose;
- an update stops at the FIRST rejection, so an update whose second
  operation is out of bounds does not have its first applied;
- an accepted update keeps its operations IN ORDER. The accumulator is
  reversed, and an unreversed one would pass every single-operation
  check above.

## Two more: the OWL test-type classifier and the regime dispatch

| F\* module | Lines | Lean |
|---|---|---|
| `OWL.Tests.Manifest` | 28 | `L4Factoidal/OWL/TestsManifest.lean` |
| `RDF.Entailment.RegimeDispatch` | 53 | `L4Factoidal/RDFS/RegimeDispatch.lean` |

### `TestsManifest`

Five test-type IRIs, classified. The `#guard`s state the two ways a
loose classifier goes wrong: the namespace ALONE is not a test type, and
an unknown suffix inside the namespace is not either. A "starts with the
namespace" check accepts both, and would count every ontology term in
that namespace as a test.

### `RegimeDispatch`, and one narrowing worth stating

`x-rdfscore` selects the ρdf closure, `x-rdfsplus` selects the RDFS-Plus
closure, and everything else falls through.

The claim levels are carried over unchanged. `x-rdfscore`'s definition
IS a theorem — on fragment data the answers are exactly the ρdf-entailed
consequences, sound and complete. `x-rdfsplus` makes **no chain-level
completeness claim**: every OWL row runs under proved licensing and
truth lemmas, but `owl:sameAs` equality breaks the Herbrand construction
behind the completeness theorem.

⚠️ The fall-through is NARROWER than the F\*'s. F\* falls through to
`OWL.Closure.entailment_closure_for_query`, which owns the W3C-named
regimes ("RDFS", "OWL-RL", …) and performs the comprehension-witness
strip. The Lean fall-through is `OWL.RL.closure` directly: there is no
witness scaffolding to strip (the F\* banner notes the two new closures
mint none either), but the W3C-named regimes are not yet split out, so a
caller asking for `"RDFS"` gets the OWL RL closure. Stated here rather
than left to be found.

### A guard I wrote and then deleted

The first version had two `#guard`s of the shape `P || !P` — written to
say "the fall-through may or may not derive this". They are tautologies:
they pass whatever the code does, which is the opposite of a check.

They are replaced by one that has content: `x-rdfscor` (a near-miss for
`x-rdfscore`) must produce a DIFFERENT closure size from `x-rdfscore`.
If the regime match were a prefix test rather than equality, the two
would be equal and the guard would fail.

## RDF.Vocabulary.Axioms — a table generated, not retyped

`L4Factoidal/RDF/VocabularyAxioms.lean` ports
`formal/fstar/RDF.Vocabulary.Axioms.fst` (258 lines): the finite RDF and
RDFS axiomatic triple tables from RDF 1.1 Semantics, as literal triple
lists, auditable line by line against the specification without
executing anything.

### The two tables were extracted mechanically

The 46 rows were parsed out of the F\* source — every
`{ s = S_IRI …; p = …; o = T_IRI … }` — and re-emitted as Lean, not
retyped. A table whose whole purpose is line-by-line auditability
against a specification is the worst possible place for a transcription
slip, and 46 rows by hand is where one happens.

`#guard`s pin both counts (8 RDF, 38 RDFS, 46 total) and check for
duplicates. A dropped row is the failure mode a table like this has, and
nothing else in the tree would notice one.

### ⚠️ The table is NOT wired into any closure, and that is a measured
decision

Seeding the RDFS closure with `finiteAxiomaticTriples` was attempted in
the F\* tree and DISABLED after measurement. Every suite stayed
byte-exact except OWL 2 profile-RL ConsistencyTests: **76 pass, 0 fail →
75 pass, 1 fail**, with `New-Feature-ObjectQCR-002` becoming an
unexpected inconsistency.

The seeded schema axioms inflate the closure's `rdf:type` set through
rdfs2 and rdfs3 far enough to trip the sound-but-narrow N=1
qualified-cardinality complementOf scaffolding (issue #236) into a
spurious cls-com clash. That is an unsoundness, not an improvement, so
the seed is off in both trees.

If re-attempting: the RDF-versus-RDFS regime split still applies. The
bare closure under the "RDF" regime must NOT receive the RDFS rows —
RDF Semantics scopes the two axiomatic sets to different entailment
regimes.

### The infinite families stay rule-generated

`rdf:_1 rdf:type rdf:Property` and the rest of the `rdf:_n` families are
excluded, per the specification's own note on infinitude. The
container-membership rule emits what it needs for whatever finite set of
`rdf:_n` IRIs appears in a given graph, and rule generation is CORRECT
for an infinite family. A `#guard` checks `rdf:_1` does NOT appear in
the table — a table claiming to enumerate an infinite set would be
duplicating the rule as well as being wrong.

## The COTTAS block starts: the presence bitmap, with the I/O at the edge

`L4Factoidal/Cottas/PresenceBitmap.lean` ports
`formal/fstar/RDF.CottasStore.PresenceBitmap.fst` (257 lines) together
with the parts of `RDF.CottasStore.OnDiskIndex.fst` that decide what the
`.presence` bytes MEAN. (Only the presence module is claimed as covered;
`OnDiskIndex` also carries the dictionary header and much else.)

### Where the ten `assume val`s went

`OnDiskIndex.fst` declares **ten** `assume val` I/O primitives —
`mmap_companion_open`, `read_companion_u32_le`, `read_companion_byte`
and the rest — and every read in the F\* presence module goes through
them, served by OCaml glue that mmaps the companion at boot.

None has a Lean counterpart. `IO.FS.readBinFile` returns a `ByteArray`
and every definition here is a pure function of it; reading happens once,
at the edge, in `openBitmap`. **The Lean tree's realisation surface for
this module is EMPTY where the F\* tree's is ten declarations plus their
glue.** Same shape as the HDT container, where the file-size probe and
hex decode had nothing to do.

### The safe-direction defaults ARE the contract

A prune is an optimisation, so its correctness is one-sided: a `false`
must mean "no row here"; a `true` may be wrong, in the safe direction.
Every default is carried over:

| Situation | Answer |
|---|---|
| `rg` or `tok` out of range | `false` |
| byte read off the end | `true` |
| companion did not open | `true` |
| header invalid | `true` |
| column unbound | `true` |

The asymmetry in the first two rows is the interesting part and the
`#guard`s state it. An out-of-range INDEX is a caller contract violation
— a token id no dictionary produced — and `false` is correct, because no
row can hold a token that does not exist. An out-of-range READ means the
FILE is short, which says nothing about the data, so the only safe
answer is to include. A port that made the two agree would be wrong in
one of them, and would still pass a test that only exercised valid
input.

### The `#guard`s build a bitmap rather than describing one

`mkPresence` writes the header and packs the bits, so the format is
stated by construction. One guard then checks the WHOLE 3×5 grid —
every set bit reads back and no unset bit does — which is where a
bit-order or row-major error shows up. Checking four known-set positions
would not catch a transposed index.

### The soundness theorem, and what it does NOT establish

`rgContainsToken_sound` is the contrapositive the call site needs: given
that the bitmap agrees with the ground truth, a `false` means the token
really is absent. It depends on **no axioms at all**.

⚠️ The F\* module is explicit that the same lemma is proved *in the form
stated* while the real obligation is elsewhere: nothing shows
`BuiltCorrectly` HOLDS of any particular `.presence` file. That needs a
ghost projection from the on-disk bytes to each row group's token set,
plus a writer-side lemma that the builder respects it. Neither tree has
either. The statement is what callers rely on; the producer-side
obligation is open in both, and this port does not close it.

## The COTTAS prune chain, complete: compound bitmap and plan pruning

| F\* module | Lines | Lean |
|---|---|---|
| `RDF.CottasStore.CompoundPresenceBitmap` | 362 | `L4Factoidal/Cottas/CompoundPresenceBitmap.lean` |
| `SPARQL.Plan.Pruning` | 256 | `L4Factoidal/Cottas/PlanPruning.lean` |

With `PresenceBitmap` these three are the whole row-group prune path:
875 F\* lines, and about 900 more lines of OCaml `Hashtbl` mirrors that
the F\* modules were written to retire.

### Why the compound bitmap exists, stated as a check

A row group can hold predicate `p` in one row and object `o` in another
and never both in the same row. The three per-column gates cannot see
that; the joint `(p, o)` bitmap can.

The `#guard` says exactly that, on a fixture built for it. Row group 0
holds predicate 1 and object 4 individually, so every per-column gate
passes, and the compound gate rejects the pair:

```
#guard predicateCanMatch (some hpp) 0 (some 1)              -- present
#guard objectCanMatch (some hp) 0 (some 4)                  -- present
#guard !compoundPoCanMatch (some hc) 0 (some 1) (some 4)    -- not together
#guard !rgCanMatch 0 … (some hc)                            -- ruled out
#guard  rgCanMatch 0 … none                                 -- NOT ruled out
```

The last two lines are the pair that matters: the same query, with and
without the compound handle, gives different answers. A port that
dropped the compound conjunct would pass every per-column check while
losing the entire benefit, and only that contrast catches it.

### The byte order is the algorithm

The pair record stores `objId` in bytes 0..3 and `predId` in bytes 4..7,
so the whole little-endian u64 is `(predId << 32) ||| objId` — which
means ascending u64 order IS lexicographic `(predId, objId)` order, and
a binary search over the packed region works with no decoding at all.
`#guard`s pin that: `pairCode 1 2 < pairCode 1 5 < pairCode 3 4`, and
`pairCode 0 4294967295 < pairCode 1 0` for the carry boundary.

### Decisive `false` versus safe `true`, again

Two answers are decisive and everything else over-includes:

- an EMPTY row-group pair list is `false` — the writer said there are no
  pairs here;
- a completed search with no hit is `false`.

A TRUNCATED file over-includes. The `#guard`s put those side by side —
the same query answering `false` on the full file and `true` on the
truncated one — because collapsing the two is the plausible mistake and
it is invisible on valid input.

### The identity property is a theorem, not a hope

`filterCandidatesByPrune` with nothing bound and no companion open is
the IDENTITY on its input. Turning the optimisation off must not change
an answer, and that is now proved rather than assumed.

### The inherited gap, unchanged

Both soundness lemmas hold GIVEN that the on-disk file agrees with the
ground truth, and neither tree shows that of any actual file. The writer
is in OCaml; the producer-side proof needs a ghost projection from bytes
to each row group's contents plus a lemma that the builder respects it.
This chain inherits that gap and does not widen it.

## The presence writer, and a theorem I nearly shipped that proved nothing

`L4Factoidal/Cottas/PresenceWriter.lean` ports
`formal/fstar/RDF.CottasStore.PresenceWriter.fst` (242 lines): the
`.presence` serialiser, migrated in the F\* tree out of the OCaml glue
because the file-format header is a rule-#11 decision.

### The Lean port is WIDER than the F\*, for a concrete reason

The F\* module writes the HEADER and leaves the BITMAP to OCaml. Its own
comment gives the reason: a parliament-sized `.presence` is about
12.5 MB, and materialising that as an F\* `list FStar.Char.char` would
allocate millions of cons cells. So it ships two entry points and the
round-trip lemma covers only the small one.

`ByteArray` is a packed buffer with no cons-cell cost, so there is no
reason to split the cases. `buildPresence` writes the whole file,
bitmap included.

### ❌ And then a theorem that assumed its own conclusion

That widening put the writer and the reader in one tree as pure
functions, which makes the producer-side obligation PROVABLE for the
first time — `PresenceBitmap`'s soundness lemma holds only given
`BuiltCorrectly`, and neither tree proves it because the F\* writer is
OCaml.

So the module ended with a theorem under the heading "the producer-side
obligation, closed":

```lean
theorem buildPresence_correct …
    (hagree : ∀ rg tok, rg < numRgs → tok < numTokens →
                rgContainsToken h rg tok = occurs rg tok) :
    BuiltCorrectly h occurs
```

It type-checked. It is worthless. `BuiltCorrectly h occurs` unfolds to
exactly `hagree` with its bounds re-indexed through two other
hypotheses, and the proof body was `exact hagree …`. The theorem assumes
what it claims.

It is DELETED, not weakened. A theorem that assumes its conclusion is
worse than none, because it makes the commit message and this document
say an open obligation is discharged — and the next reader stops looking
for the real proof.

Caught by re-reading the statement against the definition before writing
the commit message. Not by the type checker, which was happy, and not by
any test. Now hazard #29 and anti-pattern #29.

### What is established, and what would close the gap

**Established:** the `#guard`s check that the writer and the reader
agree at EVERY in-range position, at four shapes including `1 × 17` and
`8 × 8` — both of which cross byte boundaries — and that the fixtures
set and clear real bits, so the agreement is not vacuous. Plus the
serialise/parse round trip, and refusal of a wrong magic, a wrong
version, and a short bitmap.

**Not established:** the same statement for all sizes. That needs a
bit-packing lemma — byte `bitIndex / 8` of `buildBitmapBytes` has bit
`bitIndex % 8` set exactly when `occurs` holds there — which means
reasoning about a `UInt8` fold of `|||` against powers of two.

**What the port DID change:** the proof is now POSSIBLE rather than
structurally blocked. Both sides are pure functions in one tree instead
of split across an OCaml writer. That is a different sentence from "the
obligation is closed", and collapsing the two is what produced the bad
theorem.

### One asymmetry worth naming

The READER over-includes on a short file — the safe answer at query
time. The PARSER refuses one. Both are right for their job: a query must
not lose rows, and a caller round-tripping a file wants to know it is
truncated. `#guard`s state both.

## RDF.CottasStore.CompoundPresenceWriter → `L4Factoidal/Cottas/CompoundPresenceWriter.lean`

The `.po.presence` serialiser: the writer whose reader is
`Cottas/CompoundPresenceBitmap.lean`.

**Wider than the F\* module, for the `PresenceWriter` reason.** F\*
writes the 20-byte `COPO` header and leaves the row-group offset index
and the packed pair codes to the OCaml glue, because building them as
an F\* list costs millions of cons cells at corpus scale. `ByteArray`
has no such cost, so `buildCompoundPresence` writes the whole file.

**The offset convention is corrected, not carried over.** The F\*
module's `parse_compound_presence` reads the last offset entry as a
COUNT OF PAIRS. The OCaml writer and the F\* reader both use BYTE
OFFSETS from the start of the file, so the F\* parser returns `None` on
every `.po.presence` file the project writes, and its round-trip lemma
covers no real file. Only `serialize_compound_presence_header` is on
the shipping path, which is why it survived. Filed as
<https://github.com/danbri/factoidal/issues/555>. The Lean module uses
byte offsets and carries a `#guard` that computes the F\* rule on a
real file and shows the requested count exceeds the file size.

**The reader's precondition moves from a comment to a proof.** The
binary search in `rgCouldContainPair` needs each row group's pair list
sorted ascending by `pairCode`. In F\* that is a caller obligation,
written in a comment as "NOT enforced here". Here
`buildCompoundPresence` sorts and de-duplicates, and

```lean
theorem sortPairs_sorted (l : List (Nat × Nat)) : sortedByCode (sortPairs l) = true
```

proves the output satisfies it. `#print axioms` reports
`[propext, Quot.sound]`. The two supporting lemmas are
`allCodesGt_weaken` and `allCodesGt_insertPair`; strict `<` in
`allCodesGt` makes duplicate-freedom part of the same statement.

**Not proved: writer-reader agreement.** As in `PresenceWriter`, the
`#guard`s check `rgCouldContainPair` against the ground-truth pair set
over the whole `predDictSize × objDictSize` grid at four shapes. That
is computational evidence, not a proof for all shapes, and the module
says so. No theorem taking the agreement as a hypothesis was written —
see anti-pattern #29.

**Cross-check.** A `#guard` compares `buildCompoundPresence` byte for
byte against `CompoundPresenceBitmap.mkCompound`, the reader module's
own independently written fixture builder.

## `L4Factoidal/Cottas/SortByKey.lean` — not a port

An insertion sort keyed by a `Nat`, with `sortByKey_sorted`. It exists
because two COTTAS writers need the same property: the reader binary-
searches a region, so the writer must emit that region strictly
ascending by a key. `CompoundPresenceWriter` keys pairs by `pairCode`,
`OffsetsWriter` keys subject ids by themselves. The order is STRICT, so
one predicate states ascending order and duplicate-freedom together.

`CompoundPresenceWriter.sortPairs_sorted` was proved standalone first
and now delegates here; the proof exists once.

## RDF.CottasStore.OffsetsWriter → `L4Factoidal/Cottas/OffsetsWriter.lean`

The `.p.offsets` serialiser: `(row group, predicate)` to the sorted
subject ids of that bucket.

**Same three changes as `CompoundPresenceWriter`, plus one more.**

1. It writes the whole file rather than only the 16-byte `COTO` header.
2. It uses BYTE offsets. `parse_offsets` in F\* reads the last index
   entry as a COUNT OF SUBJECT IDS, while the OCaml writer sets
   `cur = data_offset0 = 16 + 8 * (num_rgs * num_preds + 1)` and
   advances by `4 * bucket_length` — its own comment says "byte offset
   where row-list starts". So the F\* parser returns `None` on every
   `.p.offsets` file the project writes. This confirms point 3 of
   <https://github.com/danbri/factoidal/issues/555>, which asked
   whether this module carried the same fault as
   `CompoundPresenceWriter`. It does.
3. Each bucket is sorted and de-duplicated by the writer, and
   `buildOffsets_bucketsSorted` proves it, via the shared
   `sortByKey_sorted`.
4. **An out-of-range subject id fails the write instead of truncating
   it.** F\*'s `serialize_u32_list` returns `[]` at the first entry at
   or above 2^32, which drops every remaining payload byte while the
   header still declares the full count. The result is a short file
   that no reader can parse, produced with no error at write time.
   `buildOffsets` returns `none` for the whole file.

**Checked, not proved.** `#guard`s cover the round trip at five shapes,
each bucket read back at its own `(rg, pred)` coordinates (a
multiset-only check would pass on symmetric buckets), out-of-range
coordinates, a truncated payload, the three COTTAS magic numbers being
distinct, and the F\* count rule applied to a real file. Writer-reader
agreement is not proved, as in `PresenceWriter`.

## RDF.CottasStore.SubjectOffsetsWriter → `L4Factoidal/Cottas/SubjectOffsetsWriter.lean`

The `.s.offsets` file: one contiguous global row range per subject.
Simpler than `.p.offsets` because `BaseWriter` sorts rows by
`(s, p, o, g)` subject-primary, so a subject occupies ONE range and a
`(start, end)` pair per subject is exact.

**This module does NOT carry the offset-unit fault of
<https://github.com/danbri/factoidal/issues/555>.** Its element count
comes from the header field `num_subjects`, never from a payload entry,
so the question the other two writers get wrong does not arise here.
Its F\* round-trip lemma covers the files the project writes.

**Proved:** `unflattenRanges_flattenRanges`, the Lean counterpart of
`lemma_unflatten_flatten`. `#print axioms` reports `[propext]`. The
byte-level round trip is `#guard`-checked at four shapes and is not
proved — that needs inverse lemmas for `readU32Le` and `readU64Le` over
`ByteArray`, which no module in this tree has yet.

**One change:** an endpoint at or above 2^64 fails the whole write.
F\*'s shared `serialize_u64_list` returns `[]` at the first such entry,
dropping the rest of the payload while the header still declares the
full subject count.

**A distinction the guards pin:** an empty range and an absent subject
are different answers. Subject 1 in the fixture owns no rows and gives
`some 0`; subject 3 is not in the file and gives `none`. An end before
its start counts as empty rather than as an underflow, matching
`row_positions_count_from_bounds` in
`RDF.Store.Columnar.OffsetIndex`.

## RDF.CottasStore.LazyDict → `L4Factoidal/Cottas/LazyDict.lean`

The populate-on-demand column dictionary: four indexed views over one
COTTAS column's distinct tokens (id → term, id → raw token, key → id,
raw token → id), all populated together on the first lookup.

**Ten `assume val`s become zero.** In F\* the container is
`assume new type lazy_dict (a : Type0)` and every operation is an
`assume val` in the `ML` effect, realised in OCaml as four `Hashtbl.t`,
a populate thunk, a loaded flag and a mutex. Here `buildLoaded` and all
four lookups are pure functions over `Std.HashMap`, and the only `IO`
is `ensure`, which reads one `IO.Ref` and populates once. The
build-time `#guard`s therefore cover the dictionary's whole meaning;
what they do not cover is exactly the ref, and the module says so.

**No abstract type needed.** F\* pins `lazy_dict` to `Type0` and keeps
it abstract because a concrete record field propagated universe
constraints into `SPARQL11.Store`'s mutually recursive `eval_*` block
("Error 89: incompatible universe sets", issue #254, reverted in
f442c13). Lean has no such constraint.

**No mutex.** Two concurrent first touches would each run the populate
thunk. That wastes work without changing the answer, since the thunk is
a function of the file's bytes. Stated in the module header as the line
to revisit under real concurrency.

**Proved:** `lookupIdInList_mem` — a hit names a pair really in the
list. `[propext, Quot.sound]`. The F\* originals carry no such lemma.

## RDF.CottasStore.LazyDictRegistry → `L4Factoidal/Cottas/LazyDictRegistry.lean`

Path-keyed lookup of a store's four column dictionaries. Five
`assume val`s become zero.

**Its F\* reason for existing does not apply here.** The F\* module is a
universe workaround: putting `lazy_dict` fields on
`cottas_ondisk_handle` propagated universe parameters into
`SPARQL11.Store`'s mutual block. Lean has no such constraint, so the
Lean `LazyDict` could sit in a handle record directly.

**Its FUNCTION does apply.** Several parts of the engine open the same
store by path and should share already-populated dictionaries. So the
module is kept, and the keying — the whole of its content — is a pure
`Registry β` whose `#guard`s run at `β := Nat`. The process-global ref
and the four typed accessors are the only `IO`.

The guards pin that a path is matched WHOLE: a prefix of a registered
path, a path with one as a prefix, and a case variant are all misses.
They also pin that re-registering replaces, which is what makes
`unregisterLazyDicts` the fix for a store rewritten under the same
path — the hazard the header names.

## RDF.Store.Columnar.OffsetIndex → `L4Factoidal/Cottas/OffsetIndex.lean`

The `.p.offsets` reader: per `(row group, predicate)`, the ascending
row positions inside that row group whose predicate token is that
predicate. Built on the handle `Cottas/OffsetsWriter.lean` opens, so
the two halves share one header parser and cannot drift apart about the
layout. The F\* reader composes `OnDiskIndex.fst`'s
`read_companion_u32_le` / `read_companion_u64_le` /
`mmap_companion_open` `assume val`s over an mmap.

**⚠️ The F\* soundness predicate is weaker than its own comment.**
`offsets_built_correctly`'s comment says a correctly built file's
"count successful u32 reads at start_off..start_off+4*(count-1) yield
exactly that ground-truth list". The predicate says only
`cv.cv_count = length (rows_with_pred rg p)`. A file whose counts are
right and whose row positions are all wrong satisfies it.

`OffsetsBuiltCorrectly` is the faithful port of the predicate, so
`rowPositionsFor_count_sound` is the same theorem the F\* module has.
`OffsetsBuiltCorrectlyStrong` states what the comment describes. Three
`#guard`s make the difference visible: the fixture satisfies both, and
a second ground truth with the SAME counts and different positions
satisfies the count predicate and fails the strong one.

**Non-vacuity.** The soundness theorem's hypotheses are checked
satisfiable by a `#guard` over the fixture's whole grid, so the theorem
is about a file that exists.

**`empty` versus `noInfo`.** `empty` is the decisive answer the index
exists for — skip the row group. `noInfo` is the over-include. A guard
pins that a truncated file gives `noInfo` and never `empty`: collapsing
those two would turn a read failure into a skip and drop rows.

## RDF.Store.Columnar.SubjectOffsetIndex → `L4Factoidal/Cottas/SubjectOffsetIndex.lean`

The `.s.offsets` reader, on the handle `SubjectOffsetsWriter` opens.
One contiguous global row range per subject.

`rangeForSubject_count_sound` depends on NO axioms. Its hypotheses are
checked satisfiable by a `#guard` that compares the fixture's four
ranges against a ground truth, including the empty subject the theorem
is about.

**One constructor fewer than F\*.** The F\* `subject_range_decision`
keeps "out-of-range subject id" distinct from "no info" while noting
that today's only caller treats them the same. Here it is one
constructor, with the reason written down: nothing in the tree consumes
the distinction, and `rangeForSubject` still separates the two cases,
so a future caller can have them back without changing the type.

A guard also pins that the fixture's four ranges tile the row space
with no gap and no overlap, which is what the subject-primary global
sort means and what makes one range per subject exact.

## RDF.Store.LazyTermCache → `L4Factoidal/Cottas/LazyTermCache.lean`

The two-direction term-id cache: id → typed value and canonical key →
id. Six `assume val`s and one abstract type become none. Same
pure-core-plus-one-`IO.Ref` shape as `LazyDict`.

`LazyDict` has four directions because the COTTAS runtime needs raw
parquet column tokens beside typed values; HDT needs two, because its
Front-Coded dictionary IS the canonical form.

**Unused in both trees, and the F\* header says why.** Issue #253 was
scoped to replace `ballyhoo_hdt_runtime.sh`'s term-id allocator and
closed a different way on 2026-07-06: that patch is deleted and
`Parser.BallyhooHDT` calls the verified HDT readers directly, with no
cache in the path. The module stays as a candidate memoisation seam.
The port carries the same status.

**`size` does not populate here, and `LazyDict.size` does.** The F\*
comments differ — this one says "0 before populate; fixed positive nat
after" and `LazyDict`'s says nothing — and the port follows each. Two
functions with the same name and different triggering behaviour is a
trap, so both modules now say which one they are.

## RDF.CottasStore.OnDiskIndex → `L4Factoidal/Cottas/OnDiskIndex.lean`

The `.dict` reader and the companion-set boot helpers. Seven
`assume val`s become none.

The module's presence half is not duplicated: `PresenceBitmap.fst`
opens this module and calls its `presence_test_bit`, and the Lean port
put that function in `Cottas/PresenceBitmap.lean`, which this module
imports.

**The `ids` array is a permutation, and the fixture makes it one.**
`ids` is sorted so `token(ids[i])` ascends, and the binary search reads
`ids[mid]` before decoding. A fixture whose `ids` were the identity
would pass even for a reader that searched by id, so `mkDict` builds
one whose `ids` genuinely permutes: five tokens given in id order and
sorted into a different order on disk. A `#guard` then finds every
token at its own id and rejects four near-misses, including `"zebras"`
and `"apple "`.

**Codepoint order and byte order, stated rather than assumed.** The
writer producing `ids` compares bytes; this reader compares codepoints
through Lean's `compare`. UTF-8 preserves codepoint order under
bytewise comparison, which is why the search works at all. Two
`#guard`s pin that on non-ASCII pairs, and a third round-trips a
five-token non-ASCII dictionary.

**A token slice that is not valid UTF-8 is refused.** F\*'s
`read_companion_string` is an `assume val` and nothing states what it
does with a corrupt slice. `dictDecodeToken` goes through
`String.fromUTF8?`.

**Proved:** `presenceBitIndexBounded`, the F\* lemma
`presence_bit_index_bounded` — every bit index this reader computes for
an in-bounds `(rg, tok)` fits the extent the writer sized its buffer
to. `[propext, Quot.sound]`.

**The token-count cross-check.** `companionStatusOk` requires the
`.dict` and `.presence` headers to agree on the token count, because
they describe one column. A guard pins that a five-token dictionary
beside a four-token bitmap is refused.

## RDF.CottasStore.PageCache → `L4Factoidal/Cottas/PageCache.lean`

The LRU page cache: an assoc list with age stamps, keyed by
`(row group, column)`, evicting the smallest age past capacity.

**One cache instead of two.** The F\* module carries the same LRU
bookkeeping twice — `pcache_*` over `cottas_column` and `dpcache_*`
over `list string` — and its own comment gives a call-site reason
rather than a design one: "Kept as a separate small type instead of
parameterizing `page_cache` over a type variable, to avoid touching
every existing `page_cache`-typed call site for an unrelated change."
Here it is polymorphic, so both are instantiations and the bounds
lemmas are proved once instead of twice.

**Three of `PageCache.Bounds.fst`'s four lemmas are proved here**:
`replaceEntry_length`, `pcacheGet_length` and
`pcachePut_capacity_bound`. The third is the one with content, and the
F\* module says what it buys: an edit that drops the eviction step
becomes a verification error rather than a production memory spike.
Supporting lemmas: `findOldest_isSome`, `findOldest_mem`,
`dropEntry_length_of_mem`, `entriesAfter_length_le`, `capEntries_le`.
`pcachePut_capacity_bound` reports
`[propext, Classical.choice, Quot.sound]`; `pcacheGet_length` reports
`[propext]`.

The fourth F\* lemma, `walk_candidate_rgs_search_limited_bound`, is
about the LIMIT-pushdown walker in `RDF.CottasStore.fst` (2,825 lines),
which is not ported. It is not here, and
`RDF.CottasStore.PageCache.Bounds` stays counted as NOT covered for
that reason.

**Not ported:** the cache-wrapped decode wrappers, which call
`Parquet.Footer`. The Lean tree has no Parquet reader.

**The eviction guard tests the policy, not just the size.** `(0,0)`
goes in, then `(0,1)`; reading `(0,0)` back makes `(0,1)` least
recently used, so a third insert must evict `(0,1)`. A cache evicting
by insertion order would drop `(0,0)` and still pass a size-only test.
A second guard runs twenty puts into a cache of three and checks both
the bound and that the survivors are the three most recent.

## RDF.CottasStore.DictWriter → `L4Factoidal/Cottas/DictWriter.lean`

The `.dict` serialiser, whose reader is `Cottas/OnDiskIndex.lean`. The
two were ported separately and the `#guard`s check them against each
other: every token of a `serializeDict` output decodes at its own id
and encodes back through `dictEncodeToken`.

**The byte-versus-codepoint defect class cannot arise here.** The F\*
module's own comment records that it carried
<https://github.com/danbri/factoidal/issues/445> latently until
`RDF.Bytes.fst` stopped agreeing with `String.length` by accident — the
two coincided only for ASCII. Same class as
<https://github.com/danbri/factoidal/issues/551> in `HDT.Dictionary`.
In Lean the writer works from `String.toUTF8` and the reader from
`String.fromUTF8?`, so there is no length to pick wrongly. Guards
round-trip `"é"`, `"ü"`, `"中"` and `"日本語"` through the whole file,
and pin `tokByteLen "日本語" = 9` against `"日本語".length = 3`.

**No live callers in either tree.** The F\* header says the import path
uses `BaseWriter.serialize_cottas_v2`, not this format. Nothing in the
Lean tree calls it either.

**⚠️ The sortedness invariant stays a CALLER obligation**, as in F\*.
`ids[i] = i` is correct only for tokens stored in ascending order. That
differs from `OffsetsWriter` and `CompoundPresenceWriter`, where the
same kind of invariant moved into the writer and was proved — the
difference is the key type. Those sort by `Nat` and
`Cottas/SortByKey.lean` proves that sort correct; sorting by `String`
needs the trichotomy and transitivity of `String`'s `compare`, which
nothing in this tree has proved. `sortTokens` is provided and
`#guard`-checked, not proved, and that proof is what would close the
gap.

## SHACL.Rules → `L4Factoidal/SHACL/Rules.lean`, and a suite that now runs

The `.srl` rule-language evaluator: SHACL 1.2 Rules. `RULE` / `DATA`
blocks translate to SPARQL CONSTRUCT queries and a bottom-up fixpoint
applies them until nothing is added.

`Harness/ShaclRulesRun.lean` (`lake exe l4shacl-rules`) reads the four
sub-manifests. The Lean tree had never run this suite: the `l4shacl`
probe does not recognise the `srt:` test types and the rules manifests
link entries with `mf:entries` rather than `mf:include`, so it walked
in and reported "out of 0" —
<https://github.com/danbri/factoidal/issues/553>.

📊 Measured 2026-08-23:

| Sub-suite | Lean | F\* |
|---|---|---|
| `rules/syntax` | 51 pass, 11 fail (out of 62) | 62 pass, 0 fail (out of 62) |
| `rules/wellformed` | 7 pass, 0 fail (out of 7) | 7 pass, 0 fail (out of 7) |
| `rules/stratification` | 8 pass, 0 fail (out of 8) | 8 pass, 0 fail (out of 8) |
| `rules/eval` | 11 pass, 0 fail (out of 11) | 11 pass, 0 fail (out of 11) |
| **total** | **77 pass, 11 fail (out of 88)** | **88 pass, 0 fail (out of 88)** |

**All 11 failures are one cause, and it is not in this module.** The
Lean SPARQL 1.2 parser does not accept reifying triple patterns
`<< s p o >>` or annotation blocks `{| … |}`. Its own header already
declared that absence; what was missing was a number, and this is it.
Filed with the reproduction and the eleven file names as
<https://github.com/danbri/factoidal/issues/556>.

**⚠️ Two approximations carried over from F\* with its own words.**
`srlStratifiable` is "a conservative approximation" — it flags
new-term recursion and negation over derived data, and the F\* comment
says a full negative-cycle analysis over the predicate graph "is future
work". `filterSafe` checks only the FIRST `FILTER` in a body. Both are
ported unchanged, because changing them would change which tests pass,
and that is a decision about the engine rather than about the port.
Both are marked in the module header.

## SHACL.NodeExpr → `L4Factoidal/SHACL/NodeExpr.lean`, and the second unread suite

SHACL 1.2 node expressions (SHACL-AF §5, the `shnex:` vocabulary). The
evaluator reads the expression node straight off the graph and
dispatches on which `shnex:` predicate it carries.

📊 `lake exe l4shacl-nodeexpr` (`Harness/ShaclNodeExprRun.lean`),
measured 2026-08-23: **140 pass, 0 fail, 2 unsupported (out of 142)**,
against F\*'s 142 pass, 0 fail (out of 142). The two unsupported are
`sht:Validate` entries in `constraints/` — ordinary validation tests
that belong to `l4shacl`. They are COUNTED rather than dropped, so the
denominator is the suite's own and F\*'s 142 is 140 + 2.

**One function where F\* has five.** The F\* evaluator is a mutual block
of five with a lexicographic measure `%[fuel; tag; length]`: the list
walks recurse at the same fuel while `eval_ne` recurses at `fuel - 1`.
Here the four helpers are not recursive — `eval_ne_list` is a
`flatMap`, `eval_ne_flatmap` a `flatMap` with a different focus,
`eval_ne_keyed` a `map`, `eval_ne_argvals` a `flatMap … |>.take 1` —
each calling `evalNe` only at the already-decremented fuel, and
`eval_ne_intersect` becomes a fold over already-computed lists. So the
measure is `fuel` alone.

**Adapted to the Lean SHACL API.** `node_conforms` in F\* calls
`collect_shape_violations` against a materialised
`shacl_class_closure`; the Lean validator exposes neither. `nodeConforms`
re-targets the named shape at the single value node, clears every other
shape's targets and asks `validate` whether the result conforms — the
same judgment by a different route. `instancesOf` filters subjects by
`isShaclInstance`, which walks `rdfs:subClassOf` without materialising
triples.

### 🧹 Two harness bugs of mine, caught by the first run

Both produced WRONG numbers that looked plausible, so both are recorded.

1. **The suites were parsed in RDF 1.1 mode.** Six files failed to
   parse with "triple term `<<( )>>` requires RDF 1.2 mode", and each
   counted as one failure, so the run read 138 where the suite has 142
   — an under-reported denominator, which is the shape anti-pattern #25
   is about. `parseTurtle` takes a `mode` argument and both runners now
   pass `.rdf12`.
2. **The comparison key dropped the base direction.** `keyOf` rendered
   datatype and language tag but not `direction`, so
   `"hello"@en--ltr` and `"hello"@en` compared equal. Three tests
   (`langdir`, `hasLangdir`, `strlangdir`) were reported as failures
   whose "expected" and "got" strings looked nearly identical — the
   tell. With direction rendered, all three pass.

The rule both point at: a harness that renders terms for comparison
must render every field the data model distinguishes, and must parse
the fixtures in the mode the suite is written for. A denominator below
the reference tree's is a bug in the harness until proved otherwise.

## OWL2.SyntaxDL → `L4Factoidal/OWL/SyntaxDL.lean`

The OWL 2 DL species checker: given the RDF graphs of a W3C OWL 2 test
case's documents, decide `test:DL` against `test:FULL`. Purely
syntax-directed — no reasoning, no closure. Nine per-triple checks plus
punning, non-simple properties under cardinality, and the document
header discipline.

**The scope note is carried across because it is measured, not
aspirational.** The F\* header records that the checks are the subset of
the Mapping to RDF Graphs reverse mapping and the Structural
Specification global restrictions "that the corpus actually
discriminates on, validated check-by-check against all 489
species-annotated cases in `third_party/testing/owl/all.rdf` (323
species-DL, 166 species-FULL-only)". Two graph-identical premise pairs
carry opposite verdicts, which is why `speciesIsDl` takes the
conclusion document as well as the premise.

**Every check gets a MINIMAL PAIR in the `#guard`s**: a graph that
passes and the same graph perturbed so exactly one check fires. A
checker tested only on violations would not distinguish "rejects
everything" from "rejects the right thing". The pairs cover reserved
subjects, undeclared predicates, the `rdf:type` object rule, the
`owl:onProperty` filler, an object property with a literal object,
datatype usability, `rdf:List` node arity, punning, and the header
rule — including that a BLANK NODE typed both `owl:Class` and
`owl:Restriction` is legitimate, which is what the `"I"` key prefix in
the punning check protects.

The last pair is the difference between the two entry points: a
header-less graph with a clean body is rejected by `speciesIsDl` and
accepted by `speciesIsDlFunctional`, because a successful
functional-syntax parse proves the `Ontology(…)` header.

**Not yet measured against the corpus.** The F\* module's 489-case
validation is not re-run here — that needs the OWL test-case manifest
reader, which the Lean tree does not have. The `#guard`s check the
checks; they do not reproduce the corpus number, and this note says so
rather than letting the F\* figure read as the Lean one's.

## SPARQL.Plan.AccessPath → `L4Factoidal/Cottas/AccessPath.lean`

The per-row-group access-path chooser: `skip`, `offsetJump cv`, or
`fullScan`. Built on the two modules ported just before it —
`Cottas/OffsetIndex.lean` for the index and `Cottas/PlanPruning.lean`
for the bounds record.

`skip` is the decisive answer and the one that must be right;
`fullScan` is the over-include and is always sound. A `#guard` walks
every route to `fullScan` — no handle, unbound predicate, out-of-range
row group, truncated file — and none of them reaches `skip`, because a
`skip` on missing information would drop rows.

**`chooseAccessPath_skip_sound` states the chain the F\* module leaves
as a comment.** There, the soundness argument is prose pointing at
`OffsetIndex.row_positions_for_count_sound`: a `skip` comes only from
`CD_Empty`, which comes only from a zero count, which that lemma turns
into "no matching row". Here it is one theorem with those steps
discharged, on `[propext, Quot.sound]`.

## SPARQL.Plan.Streamable → `L4Factoidal/SPARQL/PlanStreamable.lean`

The parse-stream fast-path recogniser: which queries can be answered by
folding over the parser's output without ever building a term graph.
The F\* header carries the measurement that motivates it — a one-row
`COUNT(*)` over 888,949 triples peaked at 731 MiB RSS on the
materialise path and 44 MiB on the streaming one.

**Two soundness conditions are carried across in force, and each gets
its own `#guard`.**

The DOMAIN SPLIT: a plain `?s ?p ?o` queries only the default graph and
`GRAPH ?g { ?s ?p ?o }` only the union of named graphs, so on N-Quads
input the two count DISJOINT subsets of the document and neither counts
every line. Four guards pin `streamInDomain` on both plans against both
kinds of item.

PAIRWISE DISTINCTNESS on the named-graph shape: `GRAPH ?g { ?g ?p ?o }`
and `GRAPH ?g { ?s ?p ?s }` carry an implicit equality that a
position-by-position bound match does not honour, so streaming them
would silently OVER-count. Four guards pin each rejection —
`?g` in the subject, `?g` in the object, a repeated `?s`, a repeated
predicate variable.

**`StreamBound` is stated locally.** The F\* module reuses
`triple_pattern_bound` from the algebra; the Lean algebra has no such
record, so the three fields are declared here with the same shape.

## RML.Sources → `L4Factoidal/RML/Sources.lean`

The RML logical-source iterator model: source rows, the CSV logical
source (an RFC 4180 tokenizer plus the header-row binding model), and
the iterate / reference entry points for both JSON and CSV.

**The JSONPath half was already here.** `RML/JsonPath.lean` ports the
same subset, surveyed from the same corpus, so this module calls it
rather than restating the grammar. `jsonIterate` and
`jsonReferenceValues` are thin wrappers.

**The CSV tokenizer stays local, for the F\* module's own reason.** The
SPARQL 1.1 CSV/TSV RESULTS format is a different dialect — bare IRIs
and typed-literal lexical conventions belong to that format, not to
arbitrary tabular data — so reusing it would import conventions RML
does not have.

**Two data-error rules that must NOT be best-effort**, both from the
vendored suites, both making the whole source empty rather than
partially usable, and both pinned by `#guard`:

* an invalid iterator path (`"$.students[*]]"`, RMLTC0002g) gives NO
  iterations, not a best-effort parse of the well-formed prefix;
* a data row whose field count differs from the header's
  (RMLSTC0010a/b) invalidates the WHOLE source — no rows at all —
  rather than truncating or padding that row.

"Returns fewer rows" and "returns no rows" are easy to confuse and only
one is right, so both guards state the count.

**The scanner is structural where F\* uses fuel.** The F\* version
indexes a string by position with `fuel = length + 1`; here the
character list decreases structurally, and matching `'"' :: '"' :: rest`
as one pattern makes the doubled-quote escape a structural step too.
Same tokenizer, no fuel argument.

**The dialect layer is kept separate.** `csvParseRows` is the normative
RML and csv2rdf path and takes no dialect; `csvParseRowsDialect` adds
the CSVW §8 `trim` and `skipColumns`. A guard pins that the two agree
when the dialect is the default, which is what makes the no-dialect
path byte-for-byte unchanged.

## Parser.BallyhooHDT → `L4Factoidal/HDT/Store.lean`

The store boundary between a SPARQL backend and the three verified HDT
reader stages. The F\* header records what it retired: this file used to
shell out to an external `hdtSearch` CLI through 555 lines of
unverified OCaml (`ballyhoo_hdt_runtime.sh`, the #253 debt), and stage
4 deleted that runtime.

**The port goes one step further on I/O.** The F\* reader still reaches
file bytes through `Parquet.Footer`'s byte-range primitive;
`HDT/Container.lean` reads the file once with `IO.FS.readBinFile`. So
`openGraphStore` is the only `IO` in the whole Lean HDT stack, and
`search`, `estimate`, every `encode*` and every `decode*` are pure
functions of a `ByteArray`.

**The decode sentinels are carried across unchanged and pinned.** Every
id reaching a decode came from a successful encode or a navigation
result, so the failure branches are unreachable in practice — but they
must be total, and the sentinels
(`urn:factoidal:hdt-decode-error`, a `hdt-decode-error` blank node)
make a failure VISIBLE rather than silently dropped. Guards check that
all three differ from each other and that id 0 is refused before the
dictionary is consulted.

**A row missing any position yields no triple**, rather than being
completed with a sentinel: the sentinels are for a decode that was
attempted and failed, not for an absent position. That distinction has
its own guard.

Measured after the port: `lake exe l4hdt` still reports 2 pass, 0 fail
(out of 2) over the vendored `.hdt` fixtures.

## RDF.Turtle.Serialize → `L4Factoidal/Syntax/TurtleSerialize.lean`

The Turtle pretty-printer: a `@prefix` header, `;`-joined predicate
lists, `,`-joined object lists, one block per subject. The Lean tree
had NO Turtle serialiser at all before this — the false-positive audit
in the same landing is what surfaced that, since the module had been
counted as covered by `JSON.Serialize`.

**The abbreviations are the correctness surface, and both are checked
against the parser.** A prefixed name is emitted only when
`Syntax.validatePnLocal` — the parser's own validator, not a second
approximation of the grammar — accepts the local part; otherwise the
full `<iri>` form goes out. The `a` keyword is used for `rdf:type` in
PREDICATE position only, and a guard pins that `rdf:type` in OBJECT
position still prints as an IRI.

**The round trip is CHECKED here and could not be in F\*.** The F\*
banner records the attempt and its outcome: the literal path goes
through byte primitives that stay opaque to the solver, so not even
`nq_escape_literal "a" == "a"` reduces, and wire correctness is pinned
at the CLI level instead. In Lean `escapeLiteral` is an ordinary
computable function, so `#guard`s run
`parseTurtle (turtleOfGraphAuto g) = g` on four concrete graphs —
including one whose literal carries a quote AND a backslash, and one
whose IRI cannot be compacted so the `<…>` fallback is exercised.

That is evidence at four shapes, not a theorem for all graphs, and the
module header says which it is.

**Numeric and boolean literals are not sugared**, as in F\* —
correctness over sugar. The datatype IRI is still abbreviated, since
that is pure compaction.

## `RDF.Store.Loader` → `L4Factoidal/RDF/StoreLoader.lean`

The store-loading front door: pick a parser from the file extension,
parse the bytes, and hand back a graph or a reason it failed. It is
small because everything below it is already ported — the value is the
dispatch table and the failure cases, which the Lean tree did not have
in one place before.

**The measurement note that belongs with this landing.** The alias
table previously mapped `RDF.Store.Loader` onto `JSONLD.Loader`, which
loads a JSON-LD document and shares nothing with this module but the
last name component. That entry was one of seven wrong matches the
2026-08-23 heuristic audit removed (anti-pattern #31). This port makes
the alias real.

## `Math.Expr` — a port that was WRITTEN and then DELETED

A 510-line `L4Factoidal/Math/Expr.lean` was written for
`formal/fstar/Math.Expr.fst`: the exact-rational value type, the
arithmetic, exact power and root, decimal parsing, the symbolic AST and
a fuel-bounded evaluator. It built on its own and its `#guard`s passed.

The FULL-TREE build then failed:

```
import L4Factoidal.Math.Simplify failed, environment already contains
'L4Factoidal.Math.mAdd' from L4Factoidal.Math.Expr
```

`L4Factoidal/MathML/Core.lean` already carries the same maths core —
the same five-constructor `Expr` AST, `normRat`/`addRat`/`mulRat`/
`divRat`/`cmpRat`, `powNat`, `exactRootNat`/`exactRootRat`,
`factorialInt`, `asInt` and `eval` — embedded in the MathML namespace,
and `Math/Simplify.lean` carries a THIRD arithmetic
(`MVal := Option (Int × Int)`) beside it.

**The new file was deleted rather than landed.** A second copy of the
arithmetic is what anti-patterns #4 and #15 are about. The alias table
now records `Math.Expr` → `MathML.Core` as a PARTIAL cover, naming the
two pieces that are absent from the Lean tree entirely: `parse_decimal`
and the reasoned `MV_Undef` failure value (`MathML.Core` uses a bare
`Option`, so a caller cannot tell "not a number" from "divided by
zero"). The layering inversion and the suggested fix are
<https://github.com/danbri/factoidal/issues/557>.

## `RDF.Store.Capabilities` → `L4Factoidal/RDF/StoreCapabilities.lean`

The store capability seam: one record of functions in place of the
backend tag six dispatchers used to match on. `StoreCaps` is the read
seam, `StoreWriteCaps` the write seam, `Store` the pair, `DatasetCaps`
the graph-scoped composition, and `unionCaps` the read-only federation.

**The split is kept, and it is the reason this port could land at
all.** The F\* module carries only the types, the in-memory builder and
the union combinator; the COTTAS-on-disk builder and the delta overlay
live in sibling modules so this one reaches no file or memory-map call.
Those two siblings are NOT ported here, because each needs a module the
Lean tree still lacks — `RDF.CottasStore` and
`RDF.Store.Columnar.DeltaMerge`.

**Three types moved to the home the F\* tree gives them.**

* `ColNeed` is now in `RDF/Graph.lean`, matching `RDF.Graph.Executable`.
* `PatternBound` is now in `SPARQL/Algebra.lean`, matching
  `SPARQL11.Algebra`. `SPARQL/PlanStreamable.lean`'s `StreamBound` had
  been a second copy of the same three fields — its own comment said so
  ("the Lean algebra has no such record") — and is now an abbreviation
  of `PatternBound`. One record, two readers, as in F\*.
* `DeltaEntry` and its payload bytes are now in
  `Storage/DeltaLog.lean`. That module had been ported framing-only, so
  the write seam had no entry type to refer to. Sections 3 and 4 of
  `RDF.Store.Columnar.DeltaLog.fst` — length-prefixed strings, terms,
  subjects, triples, graph names and the five-constructor payload — are
  now there with round-trip `#guard`s that all carry a NON-EMPTY tail,
  so a parser that consumed the wrong number of bytes fails the check
  instead of passing on a buffer that ended where it stopped.

**Two limits are inherited from F\* and both are refusals.** A triple
term serialises to a bare tag byte and `parseTerm` refuses tag 3, so it
cannot round-trip through the delta log; the F\* banner says the same.
A `rdf:dirLangString` literal serialises its language tag but not its
direction, so the parsed literal has a tag and no direction, which
`literalWf` rejects — the record is refused rather than accepted with
the direction silently dropped. Both are pinned by `#guard`.

**The `Option` fields mean opposite things and the module says so.**
`distinctPredicates` is a pure fast path: `none` costs time.
`solveSelective` STANDS IN for `solve`: a caller that reads `none` for
one member of a composition and skips that member drops rows. The
guards check that the selective answer equals the plain answer at three
different `ColNeed` values.

**The union's LIMIT pushdown is the per-member form, not the naive
one.** Solving every member in full and then truncating returns the
same list at a different cost: a member with real on-disk pushdown would
be made to decode its whole result before the union threw it away. Each
member is asked for its remaining budget only, and a later member is not
touched at all once the budget is spent.

**The empty-member rule for DISTINCT predicates is checked.** A union
of two non-empty in-memory members cannot enumerate cheaply and says
`none`. A union whose non-advertising members are all EMPTY can, and
returns the empty list — the case a blanket refusal used to get wrong.

## `RDF.Store.Columnar.DeltaMerge` → `L4Factoidal/RDF/StoreDeltaMerge.lean`

Merge-on-read: fold a replayed delta log into one graph's diff, then
compose that diff with a base read result at query time. No I/O — the
module consumes already-replayed batches and already-decoded base rows.

**The theorem is the deliverable.**
`mergeOnRead_matches_applyEntries` says that reading base-plus-delta
returns exactly the triples that applying the SAME entries directly to
the base graph would have produced, for any bound. It is proved for the
whole vocabulary a delta entry can express — INSERT DATA, DELETE DATA,
CLEAR and DROP on one graph, in sequence — by an induction over the
entry list carrying a per-triple membership invariant.

It is stated as MEMBERSHIP, not list equality, and that is the right
statement rather than a weakening: both sides are graphs, a graph is a
set of triples, and the two lists genuinely differ in order because
`mergeOnRead` appends the delta's additions after the surviving base
rows while the reference model keeps each triple where it first landed.
A basic graph pattern has no order guarantee in SPARQL.

**Four supporting results had to be proved first, and three of them
belong to lower modules, so they landed there.**

* `RDF/Core.lean`: `Triple.eqb_symm` and the four symmetry lemmas under
  it (`langTagEq`, `langTagOptionEq`, `Subject.eqb`, `Literal.eqb`,
  `Term.eqb`). The tree had reflexivity and transitivity but not
  symmetry. The F\* module proves the same lemmas about the same
  functions and records the same reason: the merge proof compares a
  QUERY value against a STORED one in one place and two STORED values in
  another, and bridging those needs a genuine equivalence relation.
* `RDF/Graph.lean`: `mem_append`, `mem_graph_add`, `mem_graph_remove`
  and `mem_filter_congr` — what membership becomes after each set
  operation, in terms of the ENGINE equality. A `List.mem` fact says
  nothing about `Graph.mem`, which compares with `Triple.eqb`.
* `SPARQL/Algebra.lean`: `boundMatches`, `tripleMatchesBound`,
  `boundMatches_congr` and `mem_tripleMatchesBound`.

**`Graph.remove` moved from `SPARQL/Update.lean` to `RDF/Graph.lean`**,
beside `Graph.add` and `Graph.mem`. The F\* tree keeps `graph_remove`
with the other two; having it in an update module put a set operation
somewhere a store proof could not reach without importing the SPARQL
update stack.

**`tripleMatchesBound` is `List.filter`, not the F\* accumulator.** The
F\* source uses an accumulator plus a final reverse and its comment gives
the reason — on the extracted OCaml, a three-million-row bucket
overflowed the stack when the recursion built its result after the
recursive call. Lean has no such problem and the two return the same
list in the same order.

**One proof-engineering note worth carrying forward.** The state
invariant was first written as `if dr.cleared then … else …`, a branch
whose CONDITION mentions the record. Every step of the induction
rewrites that record, and the rewrite motive then fails to typecheck
because the `Decidable` instance is pinned to the old record. Rewriting
the invariant as one boolean expression — `composedMem` — removed the
dependence and the induction went through. Same truth table, and the
module says so at the definition.

## `RDF.Store.Capabilities.Delta` → `L4Factoidal/RDF/StoreCapabilitiesDelta.lean`

`overlay`: a base read seam plus one graph's resolved delta, as a read
seam of the same type. No new constructor, no new field.

**An empty delta is a no-op by construction** — the empty branch returns
the wrapped seam with one flag flipped. Checked field by field against
the unwrapped base.

**Two capabilities behave differently under a live delta, for opposite
reasons, and the module states both.** `distinctPredicates` becomes
`none`: the base's dictionary pages were written at compaction time and
cannot mention a predicate that exists only in the delta, so enumerating
from them would DROP a GROUP BY row. `solveSelective` stays `some` and
ignores `need`: it stands in for `solve`, and a caller that skips a
`none` member drops rows, so it must answer — correctly, if without
acceleration.

**The estimate is not claimed exact, and a guard shows it.** With one
tombstone the overlay estimates 2 where the exact count is 1. That is
the approximation the flag permits, pinned rather than left implicit.

## `RML.VirtualSource` → `L4Factoidal/RML/VirtualSource.lean`

RML as a queryable store rather than a materialised graph: a
`StoreCaps` over a decoded mapping and its already-read source
documents, answering a bound triple pattern without re-running the full
materialising evaluation per query.

Three of the four pushdown levels are ported as the F\* module has
them — structural narrowing by constant subject or constant predicate,
record-level subject pushdown, and no pushdown for a bound object or a
join. Scope is the default graph only, as there: a triple routed to a
named graph is DROPPED rather than misrouted, and
`supportsNamedGraphs` is `false` so the flag says so.

**A deliberate divergence, and the reason for it.**
`RML/Eval.lean`'s `quadsOfMap` was split into `quadsOfRecords`, which
takes records ALREADY PAIRED with their index, and `quadsOfMap`, which
is that applied to every record. The virtual source filters the paired
list, so a surviving record keeps the index it had in the source.

The F\* module filters the record list and then re-indexes it
(`List.Tot.mapi` inside `eval_triples_map`), and the index becomes the
blank node's label (`row_seed = tm_id ^ "#r" ^ idx`, then
`T_BNode row_seed`). So the blank node generated by source record `k`
is labelled from `k` under an unbound pattern and from its position
among the SURVIVING records under a bound one. Every blank node the
record generates moves — the subject when the subject map is a blank
node, and any object-position blank node, since one seed goes to every
term map in the record.

That has a wrong-answer consequence the module's own design does not
survive: it says a join-shaped query is answered by joining two triple
patterns over the same store at the SPARQL level, and under
re-indexing the second pattern's bound blank node cannot match. Filed
as <https://github.com/danbri/factoidal/issues/558>. This port keeps the
original index, and two `#guard`s pin the labels a bound query returns
so the difference is a recorded decision rather than an accident.

**The safety property is checked, not assumed.** `pushdownIsInvisible`
asks whether a bound solve equals the unbound solve filtered by the
same bound, and it is checked at seven bounds including one that matches
nothing. Alongside it, `rmlSolveTrace` shows the pushdown really does
iterate fewer records: one record of three for a bound subject against a
template subject map.

RML core suite after the `quadsOfMap` split: 60 pass, 0 fail (out of
60) — unchanged.

## `JSONLD.Frame` → `L4Factoidal/JSONLD/Frame.lean`

The JSON-LD 1.1 Framing algorithm: expand, flatten to a node map, match
nodes against the frame, embed the matched references, wrap in
`@graph`, compact against the frame's context.

📊 **jsonld-frame: 29 pass, 63 fail (out of 92)**, against the F\* tree's
recorded 28 pass, 64 fail (out of 92). A new harness,
`Harness/JsonLdFrameRun.lean` (`l4jsonld-frame`), reads the real
`frame-manifest.jsonld` and compares with the same RFC 8785 rule every
other JSON-LD runner in this project uses. Run it from the repository
root; `lake exe` runs from `formal/lean4`, where the corpus is not.

The remaining 63 need what neither tree implements: `@default`,
`@omitDefault`, `@requireAll` OR-matching, the other `@embed` modes,
`@reverse`, `@included`, named graphs, and value-object matching inside
a property frame.

**The frame is expanded under a different grammar, and the Lean
expander did not have it.** `ActiveContext.frameExpansion` was already a
field — carried so the port's shape matched the F\* source — but nothing
read it. `JSONLD/Expand.lean` now does, in two places: an `@id` that is
an array of IRIs or the empty object is a frame PATTERN rather than an
invalid value, and the five framing directives survive as raw members
instead of being dropped as keyword lookalikes. Without the second,
the frame's own `@explicit` never reaches the algorithm, so a pair of
`#guard`s frames the same document with and without it and shows the
outputs differ.

`expandDocument` takes `frameExpansion` with a default of `false`, so
every existing call site is unchanged, and only the FRAME is expanded
with it set — never the input being framed. That asymmetry is the
algorithm's.

**The top-level `@graph` follows `omitGraph`, not the result's shape.**
The option defaults to FALSE under `json-ld-1.0` processing and TRUE
under 1.1, which is why the suite's expected outputs are split between
the two shapes — 35 of 92 carry a top-level `@graph` and 56 do not.
Compaction with `compactArrays` collapses `{"@graph": [node]}` to the
bare node and drops the key, so under 1.0 the wrapper has to be put
back. Measuring this was what found it: wrapping unconditionally scored
15 pass, 63 fail (out of 92); reading the option scored 29.

Regression check after the expander change: toRdf 467 pass, 0 fail
(out of 467); the other five json-ld-api manifests 791 pass, 0 fail,
2 local-override (out of 793) — both unchanged.

## `RDFS.SchemaSplit` → `L4Factoidal/RDFS/SchemaSplit.lean`

Close the class and property hierarchy once, on the schema alone, then
push the result at the instance data — instead of letting the two
transitivity rows re-derive the whole transitive closure on every round
of the general loop.

**The side condition, and why it is needed.** RDFS is reflective: a
graph that says `:p rdfs:subPropertyOf rdfs:subClassOf` and `:A :p :B`
makes an ordinary DATA triple inject a schema edge, and any design that
closes the schema first and never revisits it loses that derivation.
Three clauses block the first-order routes. The F\* banner carries the
row-by-row enumeration behind them and it is not repeated here — anyone
extending the rule table has to re-run it there.

**The enumeration is not load-bearing at runtime, and that is the part
worth carrying over.** The dispatcher does not trust it: it runs the
fast path, then CHECKS that the loop derived no schema edge the
pre-computed closure did not already carry, and takes the general loop
if that fails. `schemaStableCheck` is the stated hypothesis of the
equivalence claim, not the runtime gate. All three fallbacks — a dense
schema fragment, a walk that exhausted its budget, a failed post-hoc
check — go to the untouched general loop.

**Three theorems, matching the F\* module's.**
`schemaStableCheck_sound` and `_complete` say the detector decides
exactly the declarative condition; completeness is what rules out a
detector that is merely `false`, which would make the fast branch dead
code. `emitEdge_shape` and `emitFromNode_shape` pin that every emitted
triple carries the WALKED predicate and the WALKED source — a wrong
predicate would silently move data into the schema fragment and a wrong
subject would fabricate an edge nothing licenses.
`scBfs_visited_grows` says the walk never drops a node it justified.

**The equivalence claim is checked the same way the F\* module checks
it — by measurement, not proof.** `agrees` compares
`closureFixDispatch` against `closureFix` as SETS at seven graphs,
including the reflective witness that VIOLATES the side condition,
where the post-hoc check is what has to catch the injection. Three more
guards keep it from passing vacuously: the closure really does derive
rows on the test graph, the dispatcher really does take its fast branch
there, and the derived subclass conclusion is present in its answer.

**What the Lean tree splits differently.** The F\* dispatcher wraps
`rdfs_closure_with_reflexivity`, whose reflexivity harvest sits in the
same module as the twelve rows. In Lean the six recursive rows are
`RDFS.Closure` and the harvest is in `RDFS.FullClosure`, so the
dispatcher here wraps `RDFS.closureFix` — the ρdf core closure — and the
F\* module's two-pass reflexivity shape has no counterpart to reproduce.

Regression check: 914 pass, 0 fail, 30 unsupported (out of 944) on the
rdf-turtle and sparql11 manifests — unchanged.

## `SPARQL.Protocol.Client` → `L4Factoidal/SPARQL/ProtocolClient.lean`

The client half of SPARQL 1.1 Protocol §2.1: build a query request by
any of the three dispatch methods, and turn a parsed HTTP response into
a typed result. It parses nothing itself — it DISPATCHES to the result
and graph parsers the tree already has.

**`ResponseFormat` and `mediaTypeToFormat` landed in
`SPARQL/Protocol.lean`**, which is where the F\* tree keeps them. That
module's own header had listed content negotiation as NOT PORTED, with
the reason that the protocol tests assert on status class rather than
media type. That reason holds for the SERVER direction. A client needs
the other direction — read the media type a server actually sent, pick
the parser — so the half the client needs is now there and the header
says which half is still absent.

**Sniffing the query form is a bias, not a decision, and the module
proves it cannot become one.** `sniffQueryKind` skips the prologue and
returns the first form keyword, without tracking literals or comments,
so it can be wrong. It feeds only the Accept header's q-value ORDER, and
a `#guard` checks that BOTH orderings list every media type this client
can parse — so a wrong guess costs ordering, never a 406. Response
handling goes by the response's actual `Content-Type`.

**The three failure shapes are kept distinct and checked apart**: a
malformed body is `parseError`, an unrecognised media type is
`unknownContentType` carrying the raw body, and a non-2xx status is
`httpError` carrying status and body so the server's own error detail
survives. Collapsing any two would hide which one happened. The status
test is on the CLASS, pinned at 199, 204, 299 and 300.

One guard is there because §2.1.2 is easy to get wrong: direct POST puts
the query in the BODY but still sends the graph-URI parameters in the
QUERY STRING.

Regression: 601 pass, 0 fail, 30 unsupported (out of 631) on the
sparql11 manifest — unchanged.

## `RIF.Core.Translation` → `L4Factoidal/RIF/Translation.lean`

RIF Core to SPARQL algebra: the RIF/RDF/OWL combination spec's
desugaring (`o[p->v]`, `o # c`, `sub ## sup`), the positional-atom
encoding, conditions to basic graph patterns, rule heads to CONSTRUCT
templates.

**This gives the Lean tree a SECOND route to RIF answers, and the
checks use it.** The F\* tree answers RIF by translating to SPARQL and
running the SPARQL engine; the Lean tree already answers it by direct
forward chaining (`RIF.Engine`). So this port replaces nothing. The
last block of `#guard`s runs one rule both ways — the engine's closure,
and the translated body pattern evaluated against the same facts with
the head instantiated — and compares the answers. A bug shared by both
routes would defeat that, so it is evidence rather than proof; what it
catches is a translation that quietly loses a conjunct or mis-places an
argument, which is exactly what the encoding below invites.

**The positional-atom encoding is internal bookkeeping, and every rule
in it is pinned.** Arity 2 is the direct triple. Arity 0 and 1 have no
subject-object pair, arity ≥ 3 has no triple at all, so those reify
through a fixed subject or an anchor blank node with one
`urn:rif-uniterm:argᵢ` satellite per argument. Three properties are
checked rather than asserted:

* the arity-1 argument goes in OBJECT position, so a body variable binds
  the genuine value and a literal argument needs no encoding at all;
* the anchors are FUNCTIONS OF THE VALUE — equal values reach the same
  label, different values and different datatypes do not — which is what
  makes the assertion side and the query side agree;
* two distinct atom occurrences get distinct anchor variables, without
  which two atoms in one body would be forced to describe one fact.

**Partiality stays hard where it means something.** A literal subject is
genuinely ill-typed in the three RDF-shaped atoms and stays `none`; in
the positional atom's own subject slot it is not ill-typed and takes the
deterministic blank node. A failure inside a conjunction rejects the
whole body, because a body that silently loses a conjunct matches too
much. `translateProgramDiag` reports WHICH rule failed rather than
leaving a caller to count.

`PatternTerm`, `PatternSubject` and `TriplePattern` gained
`DecidableEq` in `SPARQL/Algebra.lean` — needed to compare a translated
pattern against an expected one at all.

Regression: sparql11 601 pass, 0 fail, 30 unsupported (out of 631) —
unchanged. The rif-core runner is unaffected by construction: its root
imports `RIF.Engine`, not this module.

## `RDF.Entailment.Simple.Spec` → `L4Factoidal/RDF/EntailmentSimpleSpec.lean`

Simple entailment, transcribed from RDF 1.1 Semantics §4 (INSTANCE) and
§5.3 (the interpolation lemma), computing nothing and calling nothing.

**Why the tree now has two definitions of one relation, and what the
second one buys.** `RDF.Entailment` already defines `SimpleEntails`
through `Triple.instance?`, a total FUNCTION that computes the
substituted triple — the right shape for the decision procedure to be
proved against, and what the tree's soundness theorem talks about. This
module states the same relation the way the specification states it: a
RELATION, one clause per term kind. Without it, "the decision procedure
is sound" is a statement about a definition this project wrote. With
`spec_iff_simpleEntails` proved, that definition is tied to a
transcription a reader can check against the specification's own
sentences with no algorithm in the way.

**Three theorems.** `tripleInst_iff` relates the relational and computed
forms one triple at a time (through `subjInst_iff` and `termInst_iff`,
which recurse into RDF 1.2 triple terms). `spec_iff_simpleEntails`
lifts it to graphs. `spec_iff_instanceSubgraphForm` proves the collapse
the specification's own wording invites: "a subgraph of A is an
instance of B" names an INTERMEDIATE graph, and the form a refinement
proof uses does not. Right to left is immediate; left to right has to
BUILD that graph, and the witness is `b.filterMap (Triple.instance? m)`
— the image of `b` itself. The F\* tree proves the same equivalence in
a sibling module, so it is checked in both trees rather than assumed in
either.

**The side condition is kept out of the specification.** `LitExact`
names the literals where the tree's two coarser literal branches —
case-insensitive language tags, and `rdf:XMLLiteral` by canonical XML —
cannot fire. Both are D-entailment behaviours and neither is licensed by
SIMPLE entailment, so they belong to a soundness proof's hypothesis and
not to the transcription.

## `RDF.Entailment.RDF.Spec` → `L4Factoidal/RDF/EntailmentRdfSpec.lean`

Rung two of the entailment ladder, transcribed from RDF 1.1 Semantics
§8: the two-row rule table, the axiomatic triples, and what it means
for a graph to be RDF-closed. Like the simple-entailment transcription
it computes nothing about the engine.

**The datatype set stays a parameter.** §8 defines RDF entailment
"recognizing D", with `rdf:langString` and `xsd:string` always in D.
Fixing D would make the rdfD1 row unstatable without prejudging which
datatypes an implementation recognises.

**rdfD1 is specified and NOT implemented, on purpose.** Neither tree
implements it. It is here so the rule table is COMPLETE in the document
and the gap is visible — a table with a row quietly missing reads as a
table with no gap. Its conclusion MINTS a fresh blank node, so the
relation carries the label as an explicit parameter plus a freshness
condition rather than hiding it in an existential: a rule that may
invent a name is not a function of its premise alone.

**rdfD1 is also why `RdfClosed` names only rdfD2.** A graph closed
under a rule that mints fresh blank nodes is not finite. The
specification text handles this the same way, by taking the closure
"towards E".

**Three bridges named rather than left implicit**, so a proof can cite
them instead of re-noticing a disjunct: `finiteRdfAxioms_sound` (the
transcribed table is sound for the semantic-side recognizer — soundness
only, since the `rdf:_n` family is infinite and is handled by a schema
rather than by enumeration), `rdfD2_stepLicensed`, and
`rdfClosed_absorbs_rdfD2`.

The finite table is REUSED from `RDF.VocabularyAxioms` rather than
copied. One `#guard` pins the thing about rdfD2 that is easy to get
backwards: the conclusion's subject is the premise's PREDICATE.

## `RDF.Entailment.RDFS.Spec` → `L4Factoidal/RDF/EntailmentRdfsSpec.lean`

Rung three: RDF 1.1 Semantics §9's thirteen-row rule table, the
axiomatic triples, the two condition-level consequences that are NOT
rows, RDFS-closedness, and the ρdf fragment. The definitions compute
nothing about the engine.

**The quantifier order is the content.** `RdfsLicensed g t` reads its
premises off `g`, the INPUT graph, never off a growing accumulator.
That is what makes per-row soundness compose through a fixed-point
driver, and it is strictly stronger than "licensed by the output".

**Four rows are specified and NOT implemented**: rdfs4a, rdfs4b, rdfs8
and rdfs13 are absent from both trees' core closures. Writing them down
is what makes the gap visible. The two bnode-minting rows are excluded
from `RdfsClosed` for the reason rung two excludes rdfD1 — a graph
closed under a name-minting rule is not finite.

**Two consequences are named apart because they are not rows.** §9
states reflexivity of the subclass and subproperty extensions as
SEMANTIC CONDITIONS, which makes `xxx rdfs:subClassOf xxx` hold for any
ENDPOINT of a subclass triple, with no `rdf:type` premise — a different
route from rdfs10's. Naming it is what lets a reflexivity harvest carry
a licence instead of being a witness of unsoundness.
`RdfsMemberSubproperty` is the third of the family: RDFS-entailed by the
EMPTY graph, but not itself axiomatic.

**The engine appears only in the theorems, and only in one direction.**
`rdfs11For_derives` and `rdfs5For_derives` prove that every conclusion
those two rows emit is a derivation the table licenses, and
`rdfs11_licensed` carries one of them up to `RdfsLicensed`. They are
the transitivity pair — the rows whose two premises are linked through
`subjTerm`, which is where a transcription is most likely to diverge
from the table.

`subjTerm_of_toSubject?` is the bridge the proofs need: the row's own
generalized-RDF side condition arrives as a `Term.toSubject?` success
and the specification states it as a `subjTerm` equation.

**The remaining obligation is named in the file.** rdfs7, rdfs2, rdfs3
and rdfs9 have no licence theorem yet; each needs its own extraction of
a DECLARATION premise from the fold, rather than the two-triples-of-one-
shape pattern the transitivity pair follows.

A `#guard` pins the generalized-RDF side condition itself: rdfs11 does
NOT fire when the middle term is a literal, which is the clause an
implementation is most likely to drop.

Regression: rdf-turtle 313 pass, 0 fail (out of 313) — unchanged.

## `RDF.Entailment.Simple.ModelTheory` → `L4Factoidal/RDF/Semantics.lean`

The model-theoretic side of the entailment ladder, and the
INTERPOLATION LEMMA proved in both directions.

The three `*.Spec` modules transcribe the SYNTACTIC characterisations.
This module supplies the structures those characterisations are
supposed to be about — interpretations, denotation, satisfaction,
entailment, ICEXT — so the two sides are related by proof instead of by
assertion.

**RDF 1.1 Semantics §5.2 is the DEFINITION**: "A graph G simply entails
a graph E when every interpretation which satisfies G also satisfies
E." §5.3's "a subgraph of G is an instance of E" is a LEMMA about it,
not the definition, and `interpolationLemma` proves the `iff` rather
than assuming it. `simpleEntails_iff_mt` then carries the tree's own
decision procedure across: when it says yes, it is saying something
about every interpretation.

**The enlargements are named, and the completeness proof is where they
had to be checked.** The interpretation record is a SUPERSET of the
genuine simple interpretations — `iext` totalised over the domain
rather than typed on IP, `iLit` total, assignments total. Each enlarges
the class, which makes a SOUNDNESS result stronger and a COMPLETENESS
result harder. `interpolationComplete` is where that bill comes due,
and it is paid: the Herbrand record is buildable in the enlarged type.

**`iTt` is the quarantine point.** An RDF 1.2 triple term has no
denotation in either baseline's model theory, so the Herbrand
interpretation gives it a CONSTANT — which would make two distinct
triple terms denote one resource. That is why both graphs carry a
triple-term-free hypothesis, and why the hypothesis is on the theorem
rather than hidden in the construction.

**The interpretation core comes from `OWL.Semantics.fst`**, which is
NOT thereby covered: its thirty-odd OWL semantic-condition bundles are
absent, and only the core plus `icext` is here. The alias table records
`RDF.Entailment.Simple.ModelTheory` alone.

`subjTerm_of_toSubject?` moved from `EntailmentRdfsSpec` to
`EntailmentSimpleSpec`, beside `subjTerm`, since three modules now need
it.

## `OWL.Semantics` → `L4Factoidal/OWL/Semantics.lean`

The semantic conditions the OWL RL rules read, each cited to its OWL 2
RDF-Based Semantics table row, plus the semantic sequences (`SeqIs`)
those rows are indexed by. The interpretation structure itself landed
with `RDF.Semantics` in the previous commit; this completes the module.

**Every condition is the WEAKEST reading its row implies.** Only-if
halves and IP/IC membership side conditions are dropped unless the row
is itself an iff. Dropping a condition ENLARGES the interpretation
class, and a soundness result over a larger class is stronger — so a
rule proved sound against these is sound against genuine OWL 2
RDF-Based interpretations.

Three rows ARE full iffs, because two engine rules read opposite halves
of one condition: `sameAsIdentity`, `hasValue` (cls-hv1 forward, cls-hv2
backward) and `inverseOf` (prp-inv1, prp-inv2). Weakening any of those
would leave the second rule of its pair unlicensed.

**The pilot bundle is proved satisfiable BOTH ways, and that is the
point.** A bundle nothing satisfies makes every `EntailsUnder`
statement about it vacuously true. So does a bundle satisfied only by
the interpretation whose IEXT is everywhere true, which satisfies every
graph and would leave `PilotEntails` as the everything-relation.
`trivial_satisfies_pilot` rules out the first; `separating_satisfies_
pilot` with `separating_rejects` and `pilot_not_everything` rule out the
second.

The separating interpretation needs its own shape, and the reason is
recorded: `CondSameAsIdentity` is an IFF, so an everywhere-true IEXT
fails it. IEXT of the resource `owl:sameAs` denotes is the diagonal and
every other resource relates everything — which needs `owl:sameAs` to
denote something no other IRI does. That is the only place in the file
where two IRIs have to be told apart.

The F\* tree keeps these witnesses in `RDF.Semantics.HypothesisWitness`,
written after a draft theorem whose hypothesis was FALSE verified
cleanly and proved nothing.

**Five predicates did NOT come across, and the reason is structural.**
The F\* module carries `ig_wf_pred`, `ig_wf_sp`, `ig_wf_subj`,
`ig_wf_obj` and `ig_wf_po` — hypotheses about the shape of its
string-keyed `indexed_graph` bucket snapshot, each needing a key
injectivity side condition. The Lean tree's index is `OWL.RL.Index`, a
`Std.HashMap`-backed structure whose lookups are total functions with
their own lemmas. Transcribing predicates about a data structure this
tree does not have would be a second copy of nothing.

## `RDF.Entailment.RDFS.ModelTheory` → `L4Factoidal/RDF/EntailmentRdfsModelTheory.lean`

The RDF and RDFS semantic conditions, and every rule row proved TRUE
under them.

**This is what turns the transcribed tables into a specification.** The
two `*.Spec` modules give the syntactic rule tables of §8 and §9. On
their own they are a transcription nobody has checked against the
semantics. `rdfsLicensed_true` closes the loop: every triple the
licensing relation licenses is true in every interpretation that meets
the conditions and satisfies the premises. An engine proved to emit only
LICENSED triples is thereby proved to emit only TRUE ones — which is the
whole point of having proved two of `RDFS.Closure`'s rows licensed in
the previous landing.

**Twenty-one lemmas, one per case of the licensing relation.** Thirteen
rule rows, rdfD2, the two axiom families, and the three consequences
that are not rows. Each concludes under the SAME assignment the premises
hold under, because no row here mints a fresh blank node — which is
exactly why the bnode-minting rows were excluded from `RdfsClosed` two
landings ago.

**Two composition theorems make it usable.**
`rdfsStepLicensed_holds` says a pass that emits only licensed triples
preserves truth; `rdfsStepLicensed_entails` turns that into
`RdfsEntails`. That is the shape a fixed-point driver composes, and it
is why the licensing relation reads its premises off the INPUT graph
rather than off a growing accumulator.

**The conditions are the weakest readings**, as at the OWL rung:
only-if halves and IP/IC membership side conditions dropped where the
specification's sentence is an implication rather than an equality.
`CondSubClassOfIc` and `CondSubPropertyOfIp` are the exceptions the
endpoint-reflexivity consequences need, and they are exactly §9's own
"x and y are in IC" clause.

`CondDomain` and `CondRange` are REUSED from `OWL.Semantics` rather
than restated: §9 and OWL 2 RDF-Based Semantics Table 5.8 state the
same condition, and the F\* tree shares them the same way.

## `RDF.Semantics.HypothesisWitness` → `L4Factoidal/RDF/SemanticsHypothesisWitness.lean`

Satisfiability witnesses for the hypotheses the refinement theorems
restrict on.

**A theorem whose hypothesis is UNSATISFIABLE proves nothing and
verifies cleanly.** That is not hypothetical: the first draft of an
RDFS closure-soundness theorem in the F\* tree assumed a property of
every graph that is FALSE, and the prover reported all verification
conditions discharged. Until that was caught the guard against a repeat
was a paragraph of prose. This module makes it machine-checked in the
Lean tree too.

**Each bundle gets TWO witnesses, because there are two ways to say
nothing.** A bundle satisfied by NOTHING makes `EntailsUnder` over it
the everything-relation by vacuity. A bundle satisfied only by the
everywhere-true IEXT makes it the everything-relation for the opposite
reason, because every interpretation in the class satisfies every
graph. `trivial_rdf_conditions` and `trivial_rdfs_conditions` rule out
the first; `separating_rdf_conditions`, `separating_rdfs_conditions`,
`separating_rejects`, `rdf_entails_not_everything` and
`rdfs_entails_not_everything` rule out the second.

The separating interpretation has two truth values, every IRI denoting
`true` and every literal `false`, with IEXT holding when the predicate
is `true` and either the object is `true` or the subject is `false`.
Every condition's conclusion is reachable under it, and a triple with an
IRI subject and a LITERAL object is not — which is the graph it refuses.

**Both axiom conditions rest on one checked fact**: every triple in the
transcribed axiomatic tables has an IRI object. That is decided by
evaluation over the tables rather than argued, so a future table edit
that added a literal-object row would fail here rather than silently
weaken the witness.

**The data-side predicates get a NON-EMPTY witness**, and
`witnessExact_nonempty` says so. `GraphExact` excludes two specific
literal shapes, so a witness that avoided them by accident — the empty
graph above all — would not show the predicate is satisfied by anything
interesting.

**Where the honest answer is a gap, it is recorded.** The F\* module
reaches only a DEGENERATE witness for two hypotheses and labels them.
Neither has a counterpart here: the index predicates do not exist in
this tree (`OWL.Semantics`'s header records why), and the chain
predicate belongs to `RDF.Entailment.RDFS.ChainWf`, which is not ported.
A witness module whose gaps are invisible is the same failure as a
theorem whose hypothesis is invisible.

## `RDF.Entailment.Simple.Boundary` → `L4Factoidal/RDF/EntailmentSimpleBoundary.lean`

The document-in, verdict-out path, and label independence.

**What the module does NOT claim, stated first in its own header**: it
does not claim the N-Triples parser implements the N-Triples grammar.
That needs a declarative grammar semantics — "document D denotes graph
G", transcribed from the Recommendation — and a proof that the parser
computes it. Neither tree has one. Nothing here substitutes for it, and
the composition theorem exists precisely to ISOLATE the parser as the
one remaining unproven link.

**Label independence is the part with mathematical content.** A
parser's abstract graph is determined only up to its choice of
blank-node labels: `_:b0` from a document and `_:genid1` from a
generated-label path are the same graph, and RDF 1.1 Concepts §3.4 says
so. If the verdict could depend on those labels, no theorem about
abstract graphs would transfer to documents.

**Injectivity is required and is not decoration.** Relabelling by an
ARBITRARY map can only specialise the pattern — a non-injective map
merges blank nodes, and a merged pattern is harder to satisfy — so
`spec_rename_specialises` needs no inverse. The converse does, and the
injectivity is supplied as a RECORDED INVERSE rather than an abstract
property, because the transported substitution is the original composed
with that inverse and the left-inverse equation is what makes it work.

**One deliberate weakening from the F\* statement, and it is named in
the file.** The F\* theorem is about its shipping BOOLEAN, because that
tree has the decision procedure's completeness. This tree has soundness
only, so the theorem here is about the RELATION and a `#guard` checks
the boolean's invariance on a concrete relabelled pair — evidence, not
the theorem.

`Graph.renameBnodes` is reused rather than redefined; the F\* module
defines its own only because its tree keeps that operation elsewhere.

## `RDF.Entailment.RDFS.DatatypeClash` → `L4Factoidal/RDF/EntailmentRdfsDatatypeClash.lean`

D-inconsistency detection under RDFS D-entailment, for the two shapes
that are decidable: an ill-formed literal under a recognised datatype,
and a range declaration onto a recognised datatype used with a literal
of a different one.

**The recognised-datatype gate is the whole design.** An unrecognised
datatype's lexical form is not checked at all — that is the rdf-mt
suite's own framing, where a test passes when the implementation is
"configured to recognize all the datatypes in the list of recognized
datatypes". Four `#guard`s pin the gate in both directions, because a
detector that ignored it would report clashes the semantics does not
require.

**Rule (b) gates on the RANGE's target only, not on the literal's own
datatype.** The fact being decided is membership in `C`'s value space,
and `C` is recognised — which is why a fixture whose only recognised
datatype is `xsd:integer`, with a plain-literal object typed
`xsd:string`, is still a clash.

**The whole graph is threaded through, and that is not stylistic.**
Searching the shrinking recursion suffix instead would silently miss a
clash whenever the matching literal triple sorts BEFORE the
`rdfs:range` declaration — exactly the order the rdf-mt range-clash
fixtures come in. The F\* source records that its own single-parameter
version failed its vacuity guards for this reason; a `#guard` here
checks the reversed order directly.

**Incomplete BY DESIGN, and the file says so.** A graph whose only
inconsistency is a malformed `rdf:XMLLiteral` under a datatype the
literal checker does not model is reported as "not proven
inconsistent" — correctly, not silently — and a caller must not paper
that over as a pass.

`literalIllFormed` is reused verbatim from `RDF.Datatypes` rather than
re-derived: it already carries the whitespace-strict numeric lexical
grammar the XSD whitespace-facet tests probe.

## Not ported by design: the four F* index-key-repair modules

`RDF.Indexed.KeyInjectivity` (963 F\* lines),
`RDF.Entailment.RDFS.SepFree` (697), `RDF.Indexed.Completeness` (651)
and `RDF.Entailment.RDFS.ChainWf` (368) — 2,679 lines together — have
no Lean counterpart and will not get one.

**What they repair.** The F\* index builds its bucket key by
concatenating strings with a U+001F separator. That key is not
injective, because `is_iri` admits U+001F, and
`RDF.Semantics.HypothesisWitness.theorem_sp_key_not_injective`
exhibits the collision. `KeyInjectivity` recovers injectivity from a
one-sided U+001F-free side condition and discharges
`ig_wf_sp (build_indexed g)` from it. `SepFree` proves row by row that
every RDF and RDFS closure rule sends a U+001F-free graph to a
U+001F-free graph, because the one-graph discharge does not carry
through a closure CHAIN. `ChainWf` folds the rows into one step lemma
and inducts it over `closure_iter`. `RDF.Indexed.Completeness` proves
the bucket-coverage direction from three interface axioms about
`FStar.String.compare`, because the keys are strings and the buckets
are sorted by string order.

**Why none of it applies here.** `OWL/RLClosureIndexed.lean` keys its
five buckets on STRUCTURED values in a `Std.HashMap` — `Subject`,
`WfIri`, `Term`, `Subject × WfIri`, `WfIri × Term`. There is no
separator character, no composite string key, and no string ordering
in the picture. The well-formedness statement is an equation between a
lookup and a filter:

```lean
def BucketWf {κ : Type} [BEq κ] [Hashable κ]
    (m : Std.HashMap κ (List Triple)) (key : Triple → κ) (g : Graph) : Prop :=
  ∀ k, (m.getD k []).reverse = g.filter (fun u => key u == k)
```

`Index.Wf.ofGraph (g : Graph) : Wf (ofGraph g) g` holds for every
graph with no hypothesis; `Wf.withSubjPred_eq` and its four siblings
give soundness and completeness as one equality; `closureI_toGraph`
lifts it to a per-fuel LIST equality between the indexed closure and
the list closure. Porting the four modules would add four files
proving nothing the tree does not already have, under weaker
hypotheses.

**The one thing that would change this.** If the Lean tree adopts a
serialised or string-keyed index — for an on-disk store, or a wasm
export with a flat key space — the injectivity obligation returns and
these four F\* modules are the design to follow. Recorded at
<https://github.com/danbri/factoidal/issues/559>.

`tools/lean-port-gap.py` now classifies all four as
"F\*-only machinery with no Lean counterpart by design", and tests
that class BEFORE the proof suffixes, since `RDF.Indexed.Completeness`
ends in `.Completeness`.

## RDF.Store.Combine — folding several datasets into one

`formal/fstar/RDF.Store.Combine.fst` (85 lines) →
`L4Factoidal/RDF/StoreCombine.lean`.

The F\* fold regroups `dataset_backend` named graphs by IRI, and has to
inspect the `graph_backend` tag to keep unions FLAT: when a bucket
already holds a `GB_Union` it appends to that union's member list, and
when the bucket holds a single backend it wraps both into a fresh
two-element union.

The Lean seam has no tag. `unionCaps : List StoreCaps → StoreCaps` takes
a member list, so the fold collects the list per IRI and calls
`unionCaps` once at the end. Flatness comes from collecting before
combining, not from an arm that maintains it.

**Copied verbatim: the no-wrapper rule.** A one-element input list is
returned unchanged, and a bucket with one member becomes that member.
`unionCaps [c]` is NOT `c` — it overwrites `flags`, setting
`supportsUpdate := false` and `estimateIsExact := false`. Wrapping a
lone in-memory store would silently demote it from an exact estimate to
an approximate one and from writable to read-only. Two `#guard`s pin
that, one for the whole dataset and one for a single-member bucket.

**Order proved, not asserted.** `combineNamed_solve` states that the
rows for any name are every input's rows for that name, concatenated in
input order, and it holds for names no input carries (both sides empty).
`combineDatasetCaps_default_solve` states the same for the default
graph, and all three arms of the combiner satisfy it — the empty list
because `unionCaps []` solves to nothing, the one-element list because
`flatMap` over a singleton is that element's own rows.

**One deliberate keep from the F\* fold:** duplicate names WITHIN one
input dataset all contribute. `datasetCapsLookupNamed` returns a first
match, so a dataset carrying the same name twice would otherwise lose
its second entry on combination. `capsForName` filters rather than
looks up, and the theorems are stated in those terms.

## SPARQL.Diagnostics — trace strings, minus the backend tag

`formal/fstar/SPARQL.Diagnostics.fst` (78 lines) →
`L4Factoidal/SPARQL/Diagnostics.lean`.

`queryFormString` is a direct port. The other two renderers diverge, and
the file's header states the trade.

The F\* `graph_backend_kind_string` prints a constructor name —
`GB_List`, `GB_HDT`, `GB_Union[...]` — so a person can match a trace
line to the `--data` / `--data-cottas` / `--data-hdt` flag that produced
it. There is no such constructor in the Lean tree: `StoreCaps` replaced
the backend tag with a record of functions, which is the change the seam
exists to make.

`storeCapsKindString` renders `StoreCapsFlags` instead —
`Store[+named +update +stream +exact -decodefail]`. That is the
information the tag stood in for, stated as what the store CAN DO rather
than what it IS. What it loses: two stores with identical flags render
identically, so an HDT file and a bare COTTAS base are not
distinguishable from a trace line. A `#guard` pins that sameness, so a
later reader meets it as a recorded trade rather than as a defect.

The reason the F\* module gives for keeping these renderers beside the
types they describe — a missing case fails the totality check instead of
printing nothing — carries over unchanged to Lean's exhaustiveness
check.

## SPARQL11.Algebra.BGPRefinement — what an answer of evalBgp MEANS

`formal/fstar/SPARQL11.Algebra.BGPRefinement.fst` (2,234 lines) →
`L4Factoidal/SPARQL/BgpRefinement.lean`. Layer 2 of the query-rung
reduction: substitute a solution back into the basic graph pattern and
every triple lands inside the graph.

```lean
theorem evalBgp_instantiates_into_graph (b : Bgp) (g : Graph) {mu : Binding}
    (h : mu ∈ evalBgp b g) : ∀ t ∈ instBgp b mu, Graph.mem t g = true
```

**No second substitution was written.** The F\* `instantiate_tp` /
`instantiate_bgp` live in `SPARQL11.Algebra.fst`; the Lean tree already
had them as `instSubject` / `instObject` / `instTriple` in
`SPARQL.Update` (the INSERT-template instantiator) and
`constructPredicate` in `SPARQL.Query`. `instTriple fresh mu tp` at
`fresh := id` IS `instantiate_tp tp mu`, so `instBgp` is one line over
it and every lemma is stated about the shipping function. A private copy
would have let the two drift, and the theorem would then be about the
copy. `fresh` exists because SPARQL 1.1 Update §4.1.3 makes a blank node
written in a TEMPLATE fresh per solution; a basic graph pattern being
matched has no such rule, so `id` is the correct instance rather than a
convenience.

**The conclusion is `Graph.mem`, and `t ∈ g` is FALSE.** `Graph.mem`
compares with `Triple.eqb`, the engine equality; list membership
compares structurally. Two places in the matcher keep a term that is
only `eqb`-equal to the graph's own:

* `tryBindTerm`'s var case, when the variable is ALREADY bound — the
  binding is not updated, so the substitution returns the first term
  bound to that variable;
* `tryBindTerm`'s literal case — the pattern's own literal is kept and
  only compared.

A pattern writing a language tag `en` against a graph holding `EN`
matches, because `langTagEq` is case-insensitive, and the instantiated
triple is then not a member of the graph list. Four `#guard`s pin that
case in both directions, with a length pin so neither quantified guard
is vacuous.

The F\* module takes the other route: `bgp_frag` demands exact literal
constants, so the two literals coincide and the F\* conclusion can be
structural. This port proves the theorem for EVERY basic graph pattern
with no fragment predicate. The two agree where both apply; this one
also covers patterns the F\* fragment excludes.

**Triple terms are proved, not excluded** — the `tripleTerm` arms of
every lemma are discharged, including the one where an instantiated
object position must be read back as a subject.

Supporting lemmas, all proved: `Extends` (a match only ADDS bindings)
with `refl`/`trans`/`bind`; `tryBindSubject_extends`,
`tryBindTerm_extends`, `tpMatch_extends`, `evalBgpFrom_extends`;
`instSubject_mono`, `constructPredicate_mono`, `instObject_mono`,
`instTriple_mono`; `toTerm_toSubject?`, `toSubject?_of_eqb_toTerm`,
`constructPredicate_of_instObject`; `tryBindSubject_inst`,
`tryBindTerm_inst`, `tpMatch_inst`.

**What this is FOR.** `SPARQL11.EntailmentRegime.RDFS` (1,115 lines,
not ported) composes layer 2 with the ρdf closure to get the RDFS
entailment regime theorem. This is the half of its input that does not
mention entailment.

## SPARQL11.EntailmentRegime.RDFS — layer 3, the composed regime theorem

`formal/fstar/SPARQL11.EntailmentRegime.RDFS.fst` (1,115 lines) →
`L4Factoidal/SPARQL/EntailmentRegimeRdfs.lean`. It proves no new
entailment content: it JOINS the two layers at the graph
`RDFS.closure g fuel`, which is what the F\* banner says layer 3 is for.

* Layer 1: `RDFS.closure_sound` / `RDFS.closure_complete_of_saturated`.
* Layer 2: `SPARQL.evalBgp_instantiates_into_graph`.

**Soundness is unconditional** — no fragment predicate, no saturation
hypothesis, no groundness hypothesis:

```lean
theorem rdfsRegime_bgp_sound (g : Graph) (q : Bgp) (fuel : Nat) {mu : Binding}
    (h : mu ∈ evalBgp q (RDFS.closure g fuel)) :
    ∀ t ∈ instBgp q mu, RdfsLicenses g t
```

`RdfsLicenses g t` is `∃ u, RDFS.Derives g u ∧ u.eqb t = true`. The
existential is the exact strength both layers deliver: layer 2 lands at
`Graph.mem` and `RDFS.closure_complete_of_saturated` does too, and both
compare with `Triple.eqb`.

**The exact fragment is a COROLLARY, not the scope.**
`rdfsRegime_bgp_sound_exact` gives `RDFS.Derives g t` outright when the
closure is `GraphExact` and the answer triple is `TripleExact`. Reaching
it needed three new lemmas, all proved here:
`literalExact_eqb_eq`, `termExact_eqb_eq`, `tripleExact_eqb_eq` — the
engine equality collapses to record equality exactly where `LitExact`
holds, since `Literal.eqb` is coarser in only two places
(`rdf:XMLLiteral` canonical-XML comparison, case-insensitive language
tags) and `LitExact` rules out both. The F\* module instead SCOPES its
whole statement to `graph_frag` / `bgp_frag`.

**Completeness is CONDITIONAL and the gap is not closed here.**
`EvalBgpCompleteAt q c mu` — "the evaluator returns `mu` whenever `mu`'s
instantiation of `q` sits inside `c`" — is a hypothesis, not a lemma.
The F\* tree closed its version in its own part 9; this port has not.
`rdfsRegime_bgp_complete_conditional` and
`rdfsRegime_ask_complete_conditional` both carry it, and the file says
so in its header rather than leaving a reader to infer it.

**Saturation is a hypothesis for a reason.** `RDFS.closure` is
fuel-bounded, so with the fuel exhausted the closure is not the RDFS
closure and completeness is false. Every completeness statement carries
`step (closure g fuel) = closure g fuel`. Soundness carries no such
hypothesis: a short closure derives less, and less is still sound. A
`#guard` pins the zero-fuel case returning nothing.

**Anti-vacuity.** Every theorem here is an implication about answers, so
guards showing an empty evaluator would satisfy all of them and say
nothing. The pins therefore state positive counts: the query returns 0
rows on the raw graph and 1 over the closure, ASK is false then true, the
instantiation has length 1, and a class the graph never mentions still
returns nothing — the last one being what says the engine is not
answering everything.

## RDF.Entailment.RDFS.FixedPoint — the length test, and why Lean can close it

`formal/fstar/RDF.Entailment.RDFS.FixedPoint.fst` (1,566 lines) →
`L4Factoidal/RDFS/FixedPoint.lean`.

`closure` stops when one round leaves the graph LENGTH unchanged. A
length test is not obviously a fixed-point test: a round that both ADDS
a triple and DROPS one leaves the length alone while the content
changes, and every completeness result downstream rests on that stopping
rule meaning what it says.

**The F\* module could not close it.** Its banner records the finding:
the length test is faithful there only modulo a key-injectivity gap, and
that gap is WIDER than the index-key one, because `graph_dedup_sort`'s
key folds literal content through an ad hoc `"^^"` join rather than a
control-character separator. So it proves saturation-stability in the
form its machinery supports and stops at the length-test theorem, with
section 8 giving the combinatorial fact that blocks it.

**Why this tree can.** The blockage follows from one design decision.
The F\* round ends in `graph_dedup_sort` — a full re-sort by string key
with key-duplicates dropped, so a round can add and drop at once.
`RDFS.step` is `addAll g (stepConclusions g)`, and `addAll` folds
`Graph.add`, which appends or does nothing: it never drops, never
reorders, never consults a key. A round cannot lose a triple, so the
length can only stay equal by nothing having been added — and that IS
the fixed point.

What the module carries:

- `StepSaturated` — the semantic fixed point, membership-wise in the
  engine equality, with no length bookkeeping in it.
- `ConclusionsPresent` — the rule-by-rule form.
- `lengthTest_faithful` — the three are ONE condition, in both
  directions, with no key-injectivity hypothesis, no canonicity
  hypothesis and no fragment. This is the F\* module's theorem (a).
- `step_extensive` — unconditional. The F\* version needs a
  `no_dup_keys` canonicity hypothesis for the final dedup-sort; there is
  no dedup-sort here for it to attach to.
- `closure_eq_of_stepSaturated` — the loop cannot walk past a fixed
  point, at any fuel.
- `closure_complete_of_stepSaturated` — what the faithfulness BUYS: the
  stopping rule the engine runs is the condition the completeness
  theorem needs.

**Not claimed:** that the F\* proof is wrong. The obligation is absent
under a different `add`. If this tree adopts a key-sorted dedup for the
closure round, the obligation returns and the F\* module is the account
to follow. Recorded at
<https://github.com/danbri/factoidal/issues/560>; sibling finding at
<https://github.com/danbri/factoidal/issues/559>.

**Anti-vacuity.** A fixed-point module is satisfied vacuously by a graph
on which no rule fires, so the pins use a graph where rdfs9 DOES fire:
the length test fails on the input, the round adds exactly one triple,
the second round is the fixed point, more fuel changes nothing, and the
derived triple is present. A zero-fuel pin shows an unsaturated closure,
which is why the completeness statements carry the hypothesis.

## Parser.RIFXML — the RIF Core XML serialization

`formal/fstar/Parser.RIFXML.fst` (1,349 lines) →
`L4Factoidal/RIF/Xml.lean`. Two stages, as in the F\* source:
`XML.parseXML` builds the tree, and this module walks it into the
`RIF.Syntax` AST. The XML scanner is untouched.

**A namespace of its own.** `L4Factoidal.RIF.Xml`, not
`L4Factoidal.RIF`. The presentation-syntax front end `RIF.Ps` already
declares `parseTerm` and `parseConst`, and the root import failed on the
clash. Keeping the two front ends in separate namespaces is also what a
reader wants. `L4Factoidal.XML` is not opened either: both namespaces
declare a `Document`, so the XML side is written `XML.Node` /
`XML.Attribute` throughout.

**Element names match on the LOCAL name**, as in the F\* source: the
suite emits `Atom` and `rif:Atom` interchangeably. That accepts a
document putting RIF names in the wrong namespace; the F\* module makes
the same trade, and what these tests score is rule structure.

**One deliberate divergence, and it is a correctness gap that this port
does NOT close.** The F\* parser decodes an `rdf:PlainLiteral` constant —
whose lexical space packs `text@lang` — into a language-tagged or
`xsd:string` RDF literal. This port keeps the packed form. Two reasons,
both about tree consistency rather than the specification:

1. `RIF/Ps.lean` already produces the packed form. Decoding in one front
   end and not the other would make the same RIF document parse to
   different terms depending on which syntax it arrived in.
2. `Tm.const` carries a lexical form and a symbol space with NO
   language-tag slot, so a language-tagged literal is not representable
   in the RIF AST at all.

The fix belongs in `RIF.Translation.termOfConst`, the one place both
front ends pass through and the place that already builds an RDF
`Literal` (which does have `langTag`). Recorded, with the consequence
spelled out, at <https://github.com/danbri/factoidal/issues/561>.

**Fuel.** The walkers are fuel-bounded because the
`firstChildWithLocalName` indirection defeats the termination checker —
in Lean for the same reason as in F\*. The same generous budget is
carried so the difference stays a nuisance rather than a semantic
choice.

**Pins.** A fact document, a `Forall`-wrapped `Implies`, an `Import`
carrying its profile, an empty `Group`, and a bare `<Group>` fragment
with no `Document` wrapper. Two negative pins — text that is not XML,
and XML that is not RIF — because a parser that accepted everything
would satisfy every positive pin. Each positive pin states what it got
rather than that it got something.

## RIF.Core.Conformance — safeness and import rejection

`formal/fstar/RIF.Core.Conformance.fst` (801 lines) →
`L4Factoidal/RIF/Conformance.lean`, in the namespace
`L4Factoidal.RIF.Conformance` alongside `RIF.Xml`.

Two families of decision:

- **Safeness** — W3C RIF Core §6.1: rule argument-safeness plus the
  no-free-variables condition.
- **Import rejection** — the RIF-RDF/OWL combination spec's per-import
  validity conditions: a variable frame property under OWL-Direct,
  forbidden `rif:iri` / `rdf:PlainLiteral` datatypes in an imported
  graph, incomparable entailment profiles, an empty OWL-Direct import,
  a constant used in two roles across the imports closure, and the two
  OWL-Direct vocabulary-separation violations.

**Structural, over the XML tree.** It reasons about `External`, `Equal`,
`Or` and `Exists` — constructs the evaluator gives no semantics to — and
only needs to know THAT they are present and how they interact with
bound-ness. It also has to keep working on documents `RIF.Xml` REFUSES:
the `Multiple_Context_Error` fixture's imported document carries a
multi-slot frame in head position, which the single-atom-head rule
rejects, and a conformance verdict must not depend on the rule being
evaluable. The one exception is the vocabulary-separation check, which
reads parsed `Atom`s because it is about the content of ground frame
facts rather than the document's shape.

**The `And` case is a FIXPOINT, not a fold.** An `Equal` chain
`?x = ?y, ?y = ?z` needs more than one pass to settle: `?y` becomes
bound only after `?x` does, and `?z` only after `?y`. A `#guard` pins a
three-link chain, so a later simplification to a single fold fails
visibly.

**Narrowness stated rather than implied**, for the three checks that are
narrower than the condition they are named after:
`importedGraphIsEmpty` is not an OWL 2 DL well-formedness checker,
`owlDirectSeparationInconsistent` is not an OWL 2 DL consistency
checker, and `noFreeVariables` compares used against declared variables
GLOBALLY rather than per-`Forall`-scope — a document declaring `?x` in
one rule and using a different `?x` free in another would pass. No
fixture has that shape; the limit is written down rather than left to be
found.

**Pins in BOTH directions.** A conformance checker answering `true` for
everything passes every positive fixture, so each check has a negative
pin beside it: an unsafe rule whose head names an unbound variable, a
free variable never declared, a fact carrying a variable, a `b` position
refused an unbound argument, and an incomparable profile pair.

**Two Lean-specific traps hit on the way.** `local` is a reserved
keyword, so the builtin-pattern parameter is `localNm`. A `/-- … -/` doc
comment cannot attach to a `mutual` block — it has to be `/-! … -/`.

## Measurement: four renamed ports were missing from the alias table

Found 2026-08-23 by the opposite method to the one that found the
bare-leaf inflation. Every not-covered module was searched for by file
name inside the Lean tree, and each of the seven hits was READ in
context. Four were ports whose Lean header says so:

| F\* module | Lean counterpart |
|---|---|
| `Parser.JSONLD` | `JSONLD.ToRdf` |
| `RDF.CottasStore.PageCache.Bounds` | `Cottas.PageCache` |
| `SPARQL.Protocol.RoundTrip` | `SPARQL.ResultsTheorems` |
| `OWL.RL.Refinement` | `OWL.RLTheorems` |

Three hits were NOT ports and stay counted as not covered:
`OWL.Semantics.Soundness` (named under `RLTheorems`' own "What is NOT
proved"), `RDF.Entailment.RDFS.Completeness` (the F\* module proves
model-theoretic completeness through a Herbrand interpretation; the Lean
`complete_of_saturated` is the syntactic statement — different
theorems), and the `Parser.JSONLD` mention inside `JSON/Serialize.lean`,
which cites its writer shape rather than claiming a port.

Both directions of the measurement error have now bitten in one session:
a matching rule too loose, then an alias table too sparse. Run the
name search before quoting a coverage number, and read each hit rather
than counting it.

## Parser.BallyhooCOTTAS — the eager-load COTTAS dataset store

`formal/fstar/Parser.BallyhooCOTTAS.fst` (241 lines) →
`L4Factoidal/Cottas/Ballyhoo.lean`.

**The eleven `assume val`s become a record of functions.** The F\* module
declares an abstract `cottas_handle` and eleven assumed operations over
it — open, close, summary, named graphs, four encoders, four decoders,
`search` — each realised in OCaml glue. Lean's port has no `assume val`
and no axiom: the operations are fields of `StoreOps`, supplied by
whoever builds the store. This is the same move `RDF.StoreCapabilities`
already made for the backend tag.

Two things follow, both gains:

1. The derived functions get ordinary equations, so they can be
   REASONED about. The F\* module's own comments record that three of
   them were lifted out of glue (issue #448 wave 2) precisely so their
   relationship to `search` would be stated rather than implicit. Here
   the relationship is definitional and the comments become theorems:
   `estimate_eq_search_length`, `predicatePresent_iff`,
   `graphCandidates_present` and `graphCandidates_complete` — the last
   two saying the candidate filter is exact in BOTH directions, so a
   caller that skipped a graph it returns would drop rows and a caller
   that trusted it would miss none.
2. A test can build a `StoreOps` from a list of quads with no file and
   no glue, which is exactly what the pins do.

**The decoders return `Option`, and the F\* ones do not.**
`cottas_decode_subject : … -> Tot subject` is total in F\* because its
OCaml realisation RAISES on an unknown reference and F\* cannot see that.
A reference the dictionary does not hold has no subject, so the Lean
type says so, and `rowToQuad` drops such a row exactly as it already
drops a row with an unbound position.

**The three-state graph bound is kept, and so is its reason.**
`GraphBound` is `unbound` / `default` / `named`, not `Option GraphRef`:
the optional form conflated "no constraint on the graph column" with
"the caller means the default graph", which let a plain basic graph
pattern over the default graph union in every named graph's rows. Three
`#guard`s pin that the three states give three different answers.

**The documented sharp edge is pinned rather than reproduced silently.**
On the eager-load path an UNKNOWN graph IRI encodes to `unbound` — no
constraint — rather than to an empty result. That is the F\* behaviour
on the same path, it is the dead-code path there too, and a `#guard`
records it so a later reader meets it as a known edge instead of a bug.

## Tableau.CountingOracle — the counting fragment, decided not delegated

`formal/fstar/Tableau.CountingOracle.fst` (1,663 lines) →
`L4Factoidal/OWL/CountingOracle.lean`.

The refutation tableau decides OWL 2 DL consistency for everything
except finite-model cardinality COUNTING, where the contradiction is a
linear system over the sizes of named classes. This module is that
fragment: recognised, extracted, encoded, and — for the systems the
corpus produces — decided inside the verified boundary.

**The single `assume val` becomes a PARAMETER.** F\* assumes
`z3_check_sat : string -> nat -> Tot z3_verdict`, realised by glue that
returns `Z3_Unknown` in its Phase 0. Lean has no `assume val` and no
axiom, so `SatOracle` is a function a caller supplies and `noOracle` is
the Phase-0 stub written out. This is not a workaround: an assumed value
is a fact the proof rests on, a parameter is an input the theorems
quantify over. `classSizeUnsat` never consults the oracle, and its
soundness theorem holds for every oracle, because the decision is the
Farkas validator rather than the solver.

**What is proved.** `farkasSound`: when `farkasCheck` accepts a
multiplier vector, NO integer assignment satisfies the system. The
supporting arithmetic — `zeros_len`, `vscale_len`, `vadd_len`,
`comb_len`, `linDot_zeros`, `linDot_vscale`, `linDot_vadd`, `comb_dot`,
`weighted_ge` — is all proved, with no Mathlib: `Int.mul_add`,
`Int.mul_assoc`, `Int.add_mul`, `Int.mul_le_mul_of_nonneg_left`, and
`omega` after generalising each product to an atom (`omega` rejects
nonlinear terms, which is why the products are generalised first).
`classSizeUnsat_sound` lifts it to the system built from a graph.

**What is NOT proved, and the header says so in the same words the F\*
banner does.** That UNSAT of the class-size system IMPLIES the closure
is inconsistent under Direct Semantics. The FIBER / BIJECTION /
DISJOINT-UNION / ONEOF arguments licensing each row are prose in both
trees. `classSizeUnsat g = true` reads "the linear system this module
builds from `g` has no integer solution, and that is proved" — NOT "`g`
is inconsistent, and that is proved". A reader who took the theorem for
a consistency result would be taking prose for a proof.

**One structural improvement over the F\* layout.** F\* has two copies
of the class-size relation readers — one emitting SMT text (§6b), one
emitting `lin_constraint` records (§8b) — and a comment saying they
mirror each other. Here the readers (`fiberOf`, `bijOf`, `unionPairOf`,
`classHasOneOf`) are written ONCE and both the SMT encoder and the
linear-system builder call them, so the two describe one system by
construction rather than by inspection.

**dl-909 is still not decided, on purpose.** Its class-size system is
genuinely satisfiable — the all-empty assignment with `|only-d| ≥ 1` is
a model — so no certificate exists and the checker returns false.
Deriving `|finite| ≥ 1` would need an unsound nonemptiness rule.

**Pins in both directions.** The min-2-above-max-1 clash extracts two
axioms that SHARE one count variable (the pin that would fail if the
key were per-triple); a datatype facet and an authored `owl:complementOf`
each take a graph OUT of the fragment; an engine-generated `__rl_`
complement does NOT, which is the pin stopping the reject scan from
over-reaching; a graph with no counting construct is rejected. For the
validator: the certificate for `x = 0` with `x ≥ 1` is accepted, one
with a negative multiplier on a `≥` row is refused, one whose combined
coefficients are not zero is refused, and the searcher finds nothing for
a satisfiable system.

## Two more not ported by design: MemLemmas and ColumnSeq

Added to the by-design column 2026-08-23, alongside the four
index-key-repair modules already there.

**`OWL.Semantics.MemLemmas` (442 F\* lines)** is membership-preservation
infrastructure for the F\* `bucket_tree` build. About half of it IS that
index machinery — `tree_ok`, `lemma_tree_ok_lookup`,
`lemma_slt_tree_ok`, `lemma_build_bucket_ok`, and five
`lemma_build_indexed_wf_*` instantiations. The other half is lemmas
about `List.Tot.sortWith`, `partition` and `rev`, which exist ONLY
because that build sorts and partitions.

The Lean index does neither. `Index.ofGraph` folds `HashMap.insert`;
`BucketWf` is an equation between a lookup and a filter; `Wf.ofGraph`
holds for every graph with no hypothesis. There is nothing for a
membership-preservation lemma to preserve through, and
`OWL/RLTheorems.lean` proves the same OWL RL soundness results with none
of it.

**`RDF.CottasStore.ColumnSeq` (163 F\* lines)** is `assume new type
cottas_column` plus O(1) accessors, realised in OCaml as
`string option array`, with a list bridge. Its own banner gives the
reason: the F\*-pure decoders in `Parquet.Footer` produce
`list (option string)`, every walk cons-cell-chases through the heap,
and F\* needs an array-shaped abstract type to retire the OCaml perf
shim.

Lean has `Array` natively and totally. `Array.size`, `arr[i]?` and
`Array.toList` are the entire module — no abstract type, no assumed
accessor, no bridge.

Both recorded on <https://github.com/danbri/factoidal/issues/559>, which
now carries all six modules and the one condition that reverses each: a
serialised or string-keyed index for the first five, a decoder needing
an abstract column handle for `ColumnSeq`.

## SPARQL payload-token lemmas — an F* impossibility that is an induction here

`L4Factoidal/SPARQL/TokenizerLemmas.lean`. Groundwork for
`SPARQL11.Parser.AskBgpRoundTrip`, and NOT a completed port of it — see
"What is not done" below.

**What F\* reports.** `SPARQL11.Parser.AskBgpRoundTrip.fst`'s banner
declares its string round-trip stage IMPOSSIBLE, with the cause named:
`FStar.String.sub`'s ulib specification exposes only a length
refinement, no lemma relating its output characters to the input's
content, so no lemma can be STATED connecting a printed payload back to
the token extract via `substring`. It adds that this blocks every
payload-carrying token, and that the companion `TokenRoundTrip` module's
flagged gap has the same cause one level lower.

**Why Lean is not blocked.** `SPARQL/Tokenizer.lean` never goes through
an opaque substring: `scanIriBody`, `scanWhile` and `scanVarName`
consume a `List Char` and return one, and `String.ofList` is applied
once at the very end. The relationship between a printed payload and the
scanned token is an equation about `List.append`, proved by induction on
the payload with no library obligation.

Proved: `scanWhile_append`, `scanIriBody_append`, `skipWs_of_ne_ws`,
`processIriEscapes_id`, `nextToken_iri`, `nextToken_var`. Each states
the RESIDUE as well as the token, because a lemma pinning only the token
would not compose into a walk over a whole query.

The side conditions are the printer's obligations and carry the content:
an IRI body may hold no `>` and no `\`, its first character must be one
the `<` disambiguation reads as an IRIREF rather than as less-than, and
a variable name is drawn from what `scanVarName` accepts. Four `#guard`s
pin those on concrete input, including `< 3` scanning as less-than and
`<a>b>` ending at the FIRST `>`.

**What is not done, and why the coverage number did not move.** Three
pieces remain before the F\* module counts as ported: the ASK-fragment
predicate and printer; a `tokenizeLoop` chaining lemma (the fuel is
seeded from the whole input length, so composing per-token steps needs a
decreasing-measure argument); and the token-level parse back to the AST,
which is the part the F\* module DID complete. Recorded at
<https://github.com/danbri/factoidal/issues/562>.

Two Lean notes for a later reader. `conv_lhs`, `by_contra`, `tauto` and
`ring` are Mathlib tactics and this tree has no Mathlib — use
`conv => lhs; unfold f`, an explicit `cases h : e`, `Or.inl`, and the
`Int` lemmas plus `omega` after generalising each product to an atom.
And `::` binds tighter than `++`, so `'?' :: name ++ rest` is
`('?' :: name) ++ rest`; a rewrite stated about `'?' :: (name ++ rest)`
will not fire until `List.cons_append` has normalised the goal.

## The ASK string round-trip — the stage F* reports as impossible

`L4Factoidal/SPARQL/TokenizeChain.lean` and
`L4Factoidal/SPARQL/AskRoundTrip.lean`, on top of
`TokenizerLemmas.lean`.

```lean
theorem tokenize_printAsk (b : FragBgp) (h : FragBgpOk b) :
    tokensOf (tokenize (printAsk b)) = expectedTokens b
```

Printing a fragment `ASK { s p o . … }` query and tokenizing the result
gives back the tokens it was printed from — the stage
`SPARQL11.Parser.AskBgpRoundTrip.fst` reports as IMPOSSIBLE, for a
`FStar.String.sub` interface reason `TokenizerLemmas.lean`'s header
records in full.

**The two halves are complementary, and neither tree has both.** The F\*
module's own stage list marks (1) the fragment predicate, (2) the
printer, (3) the fuel-cost formula, and (b)–(d) the token-level parse
back to the AST as DONE, and (a) the string round-trip plus (e) the full
string-to-AST theorem as IMPOSSIBLE. This tree now has (1), (2) and (a);
it does NOT have (b)–(d) or (e). So the module is not ported, and the
coverage number does not move — what changed is which half is missing.

**Fuel stopped mattering first.** `tokenizeLoop_fuel` proves that above
the input length the fuel does not change the answer, and it needs no
knowledge of `nextToken`: the loop already carries its own progress
guard (`if rest.length ≥ cs.length then stop`), so a recursive call
always shrinks the list and a strong induction on that length is enough.
`tokenizeLoop_cons` is then a plain unfolding, and the walk over a
printed query is an induction with no arithmetic side conditions.

**The printer emits no whitespace** — `ASK{<a><b><c>.}`. Every token
boundary in the fragment is unambiguous without one, so the proof needs
no reasoning about `skipWs` beyond "the next character is not
whitespace". A space-inserting printer would be equally correct and
would add an offset to every step.

**`nextToken_ask` needs TWO side conditions**, and the second is easy to
miss: the character after the keyword may not be a name character (or
the keyword would be longer) and may not be `:` (or the whole thing is a
prefixed name, not a keyword). The first does not imply the second,
because `:` is not a name character.

**The side conditions are pinned as failures, not just as hypotheses.**
An IRI body containing `>` prints to text that tokenizes to something
SHORTER than expected — the token closes early — and a body starting
with a digit makes `<` scan as the less-than operator. Both are `#guard`s
asserting the round trip FAILS, so neither hypothesis can be mistaken
for bookkeeping.

Recorded at <https://github.com/danbri/factoidal/issues/562>.

## SPARQL11.Parser.TokenRoundTrip — a WIDER fragment than the F* one

`formal/fstar/SPARQL11.Parser.TokenRoundTrip.fst` (1,391 lines) →
`L4Factoidal/SPARQL/TokenRoundTrip.lean`, with
`L4Factoidal/SPARQL/SkipWsLemmas.lean` underneath.

```lean
theorem tokenize_printTokens (ts : List Token) (h : ∀ t ∈ ts, TokOk t) :
    tokensOf (tokenize (String.ofList (printTokens ts))) = ts ++ [Token.eof]
```

**The fragment is wider, in both directions the F\* module names as out
of reach.** The F\* fragment is the single-character delimiters and the
single- and two-character operators. Its own FINDING says the
payload-free KEYWORDS were left out because the lexer reaches them
through `scan_word` + `keyword_of_word`, so its combinator lemmas do not
transfer; and the companion `AskBgpRoundTrip.fst` later reports that the
real obstruction is one level lower, in `FStar.String.sub`'s interface,
and blocks every PAYLOAD-carrying token too. Neither obstruction exists
here, so this fragment adds `iri`, `var`, `a` and `ASK` to the twenty
single-character tokens.

**Twenty tokens, one theorem.** `tokChar : Token → Option Char` is the
table, and `nextToken_tokChar` is a single induction over it rather than
twenty near-identical lemmas. The tokenizer's if-chain is decided per
character by `simp`, which is what makes one proof cover all of them.

**The separator needed a fuel argument of its own.** Every token is
printed with a space after it — the same disambiguation the F\* module
uses — so the walk has to step over a leading space at each turn. That
is `nextToken_cons_ws`, and it rests on `skipWsComments_fuel`: `skipWs`
seeds its fuel from the remaining input length, so dropping a character
changes the fuel as well as the list. The proof needs
`scanToEol_length` (a comment scan returns a suffix) to make the `#`
branch well-founded.

**The separator is pinned as load-bearing, not assumed.** Three
`#guard`s show what happens without it: `<a>` lexes as one IRI token,
`!=` as one `ne` token, and `! =` as two. A printer that omitted the
space would not round-trip, and the pins say so rather than the prose.

**`ParserTheorems.lean`'s header was stale and is updated in the same
landing** (iron rule #14). It said the round-trip theorem "is not
stated" because the port ships no printer; two fragment printers and
their round trips now exist. The sentence still holds for the statement
it is about — both stop at the TOKENS, and neither says the parser
recovers an AST — and the header now says which is which.

## RIF.Core.Refinement — and a round semantics that differs

`formal/fstar/RIF.Core.Refinement.fst` (364 lines) →
`L4Factoidal/RIF/EngineTheorems.lean`. The two properties the RDFS
closure already has, stated for `RIF.closure`:

- `closure_extensive` — the fixpoint never drops an input fact, at any
  round bound.
- `step_licensed` — every fact one round emits is the head-instantiation
  of SOME rule of the program under SOME substitution the body matched.

**A real difference in the engines, not in the proofs.** The F\*
`one_round_aux` fires the rules IN SEQUENCE against the graph it is
building, so a later rule sees the earlier rules' new triples WITHIN THE
SAME ROUND — `RIF.Core.Eval`'s own comment flags that order-dependence,
and the F\* refinement module needs the "two-graph src/seed" idiom
because of it: its licensing statement quantifies over a snapshot
EXTENDING the round's input.

`RIF.step` here folds over the rules accumulating into `acc`, but every
rule matches against the round's ORIGINAL `facts`. So a round is a
function of its input alone, rule order does not change what it derives,
and licensing is a SINGLE-graph statement naming the round's own input.

**The difference is pinned, not asserted.** For `A(x) → B(x)` and
`B(x) → C(x)` over `A(a)`, one round here derives `B(a)` and nothing
else — under sequential firing the same round would also derive `C(a)`.
Two `#guard`s show rule ORDER does not change that, one shows `C(a)`
arrives on the second round (so the difference is per-round, not in the
limit), and one shows a single round is genuinely not enough, which is
what makes the others say something.

**What licensing does NOT say**, stated in the file: that a derived fact
is TRUE under any semantics. It says the engine only emits
head-instantiations of its own rules — a PROVENANCE property. Truth
needs a model theory the RIF port does not carry, and calling this
soundness would be reading provenance as truth.

**One reusable piece.** `mem_foldl_append` — membership in an
append-accumulating `List.foldl` is membership in the seed or in one
item's contribution — is what keeps both licensing inductions short.
`step_eq_fold` first rewrites `step` into that shape, naming each rule's
contribution (`ruleContrib`) and blocked flag (`ruleBlocked`) so the
rewrite is one `congr` rather than a case analysis.

---

## `SPARQL11.Expression.Refinement` → `SPARQL/ExprRefinement.lean` (2026-08-23)

**Not already covered, despite the overlap.** `SPARQL/ExprTheorems.lean`
already proves the §17.2.2 rows and the §17.3 truth tables. It states
them about the engine's own `ebv`, `boolAnd`, `boolOr` and `boolNot`.
The F\* module does something else: it writes a SECOND transcription of
each W3C table, from the specification text, and then proves the engine
equal to it. That second transcription is what was missing, so the two
Lean modules are kept side by side.

**What the second transcription buys.** F\* issue #365 recorded two
places where the engine and the table had drifted apart: a non-empty
`rdf:langString` literal read as truthy (the table's String row is the
un-tagged case only), and `.and`/`.or`/`.not` folding a type error into
a definite Boolean instead of propagating it. The F\* tree found both by
comparing the engine against `ebv_spec`/`spec_and`, then aligned the
engine. The Lean port was made from the aligned engine, so
`ebvSpec_agrees` and `specAnd_agrees` hold with no carve-out — and
`ebvSpec_langString`, `eval_and_true_error_agrees`,
`eval_or_false_error_agrees` and `eval_not_error_agrees` pin the four
former divergence witnesses so a later edit cannot reopen them.

**The evaluator-arm theorems are unconditional.** `eval_and_matches_spec`
and its two siblings take no hypothesis about the operands, so no row of
the table can be lost through a hypothesis that never holds — the
vacuous-theorem check the F\* tree applies to the same statements.

**§17.4.1.7 needed new groundwork.** The plain-string equality lemma
needs `strCompare a b = 0 ↔ a = b`; the Lean tree only had reflexivity
in one direction. The chain is `intCompare_eq_zero_iff` →
`listCharCompare_eq_zero_iff` (induction, with `Char.ext` over
`UInt32.toNat` injectivity for the head character) →
`strCompare_eq_zero_iff` (via `String.ofList_toList`), plus the Boolean
forms `intCompare_beq_zero` and `strCompare_beq_zero` that the operator
mapping actually applies. The F\* side gets the same fact from
`SO.string_compare_zero_iff_eq`.

**Out of scope here as in the F\* source.** General cross-lexical value
equality over decimals and doubles ("1.0" = "1.00") needs a spec for
what the scaled-value parse computes. The two reflexivity theorems
included need no such spec: the parse is a total function of the lexical
form and is applied twice to one string.

Coverage after this landing: 189 of 220 F\* modules covered, 31 not
covered.

---

## `RDF.Entailment.Simple.Refinement` → `RDF/EntailmentSimpleRefinement.lean` (2026-08-23)

**An engine gap came out first.** The F\* module proves the shipping
backtracking search COMPLETE for the specification. Stating that in Lean
found the statement false of the port: `matchObject` bound a top-level
blank node but fell straight to `termMatch` for an RDF 1.2 triple term,
and `termMatch` compares a triple term's subject and interior object by
identity. So `a p <<( a p _:b )>>` matched only a premise carrying the
same interior label, and `simpleEntails` answered `false` on a pair the
substitution `_:b` to `c` relates. The F\* `match_term`
(`RDF.Entailment.Simple.fst:94`) always recursed; the port had dropped
the recursion. The arm now recurses, and
`entailsSimple_tripleTerm_interior_bnode` pins the witness.

**Sound and complete, both unconditional — unlike the F\* source.** The
F\* soundness half carries a `graph_exact` side condition, with
`simple_entails_not_sound_unconditionally` as the witness that it cannot
be dropped. The cause is named in that module's banner: the shipping
`literal_eq` folds language-tag case and compares two
`rdf:XMLLiteral`-typed literals by exclusive canonical XML, so it is
strictly coarser than literal term equality. This tree's
`literalStrictEq` is `==` on `Literal`, whose `BEq` comes from
`DecidableEq`, so it IS literal term equality and neither half needs a
side condition. Reporting the F\* condition here would name a
restriction the Lean statement does not carry. The coarser comparisons
live in the regime variants (`literalValueEq D`), whose specification is
model-theoretic and is not ported.

**Two properties of the search, proved apart.** Completeness cannot go
through "the search finds the witness mapping", which is false — the
search commits to the first candidate that works and may return a
different mapping than the given substitution describes. So:

1. `searchInstance_isSome` — the route the witness substitution picks
   out succeeds, so `List.findSome?` returns SOMETHING. It claims
   `isSome` and nothing about which mapping.
2. `searchInstance_certifies` — whatever it returns, `instanceCert`
   re-checks successfully.

`entailsWith_complete` composes them.

**The idiom that carries a step's match to the end.** Each matcher's
soundness lemma is stated for EVERY later mapping, not only for the one
it returns: `∀ m', Extends m' m1 → ps.instance? m'.toFun = some gs`.
That quantifier is what lets an early triple's match survive the
bindings the later triples add, and it removes the need for a separate
"the label stays bound" invariant. `Mapping.lookup` reads the first
entry, so a prepend could shadow; the search never prepends a label it
already holds, which is what makes `Extends.cons` provable.

Coverage after this landing: 190 of 220 F\* modules covered, 30 not
covered.

---

## `SPARQL11.Algebra.Spec` → `SPARQL/AlgebraSpec.lean` (2026-08-23)

A declarative statement of the SPARQL 1.1 algebra, transcribed from
§18.3, §18.4 and §18.5, that computes almost nothing and mentions no
function and no type of `SPARQL/Algebra.lean`. Its only
project-internal import is `RDF/Core.lean`, and that single import line
is the mechanical independence check — the same one the F\* source
states about its `open` list.

**Two layers, kept apart.** §18.5 defines each operator twice: as a SET
of solution mappings and by a cardinality clause. Part 3 states the set
layer, part 4 the bag layer. Distinct is why they must stay apart — its
set layer is "the same elements", so all of its content is in
`distinctCardSpec`, and letting the set layer stand in for the
definition would lose the operator.

**The representation is not the meaning.** A solution mapping is a
partial function carried as an association list, because that is what
the evaluator produces and nothing should translate at the refinement
boundary. `SMapEq` says two lists denote one mapping; every definition
is stated over `sval` rather than over the domain list, so it is
insensitive to layout by construction, and `compatible_congr_left`,
`merge_unique` and `mult_congr` check that.

**One lemma pins a REPRESENTATION hazard rather than a definition.**
`compatible_refl` looks trivial. It is worth stating because the F\*
evaluator's `sm_compatible` is not reflexive on a duplicate-key list
(`lemma_sm_compatible_not_refl_with_dup_keys`, 2026-07-29). Proving
reflexivity of the SPECIFICATION relation is what places that
difference on the representation and not on the definition. `smapWf`
names the well-formed representations, and two `#guard`s show a
duplicate-key list is badly formed yet denotes a perfectly good
mapping.

**Merge is a relation, not a function.** `IsMerge mu1 mu2 mu` avoids
committing any downstream statement to a list layout;
`mergeCanonical_isMerge` supplies the witness that keeps it from being
vacuous, and `merge_unique` says the merge is determined up to
`SMapEq`.

**Term identity is transcribed, not delegated.** `termIdEq` is written
out from RDF 1.1 Concepts §3.3 — same lexical form character by
character, same datatype IRI, same language tag NOT case-folded, same
base direction — rather than using the derived `DecidableEq`, so the
transcription can be diffed against the specification text.
`termIdEq_sound` and `termIdEq_complete` tie it back.

**What is not here.** The refinement proof itself
(`SPARQL11.Algebra.Refinement.fst`, 2497 lines) is a separate module
and is not ported. Without it this file is a statement, not a result
about the evaluator.

Coverage after this landing: 191 of 220 F\* modules covered, 29 not
covered.

---

## `RDF.NTriples.RoundTrip` → `Syntax/NTriplesRoundTrip.lean` (2026-08-23, PARTIAL)

**Counted as NOT covered.** The module carries the serialiser-injectivity
half and the print-safe IRI fragment; the F\* source also reaches an IRI
round trip, and this does not. Aliasing it would move the coverage
number without carrying the result.

**Two different blockers, easy to confuse.** The F\* source's Finding 1
is that its parser is unreachable for ANY input: every byte goes through
five `assume val` FastString primitives and the axiom set has no
base-VALUE fact, so `fs_byte_at "<" 0 == 0x3C` fails. Its Finding 2(b)
is that the F\* serialiser routes every literal through
`nq_escape_literal`, blocking literals on the serialiser side — which is
why the F\* fragment is IRIs and blank nodes only.

Neither transfers. `readIriRefBody` and `escapeLiteral` are ordinary
Lean functions over `List Char`; they reduce and the module's `#guard`s
run them. What stops the Lean round trip is that `readIriRefBody` has
ten match arms, two carrying six- and ten-character escape patterns, and
Lean's per-arm equation-lemma generation for it exhausts the container's
memory. Measured: `#check @readIriRefBody.eq_11`, in a file whose only
other content is the import, is killed by the OOM killer. The step lemma
elaborates in about 34 seconds and several gigabytes in isolation and
does not survive being placed next to any other declaration.

Filed as <https://github.com/danbri/factoidal/issues/565> with the
refactor — split the scanner into a shallow-match one-character step
function plus a driver — that unblocks it. That touches a shipping
parser with its own test surface, so it is separate work.

**Why a fragment at all, and this part IS proved.** `RDF.isIri` asks
only for a non-empty string containing a colon, so `a:b>c` is a
well-formed `WfIri` and is not print-safe: serialising it emits
`<a:b>c>` and the parser stops at the first `>`, recovering `a:b` and
leaving `c>` unread. A `#guard` runs that witness. No unrestricted
round-trip statement is true whatever proof machinery arrives, and
`iriPrintSafe` names the IRIs on which the two sides agree.

Coverage after this landing: unchanged at 191 of 220 covered, 29 not
covered.

---

## `RDF.Entailment.RDFS.Completeness` → `RDFS/RhoDfCompleteness.lean` (2026-08-23)

**The converse half of the RDFS rung.** `RDF/EntailmentRdfsModelTheory.lean`
proves every rule row TRUE under the semantic conditions. This module
proves the other direction on a named fragment: on a ρdf-CLOSED graph,
ρdf entailment and simple entailment pick out the same pairs.

**Saturation is the whole argument.** The canonical model is the
Herbrand interpretation of the closed graph, reused unchanged from the
simple rung. Each of the six ρdf conditions is discharged the same way:
read the two Herbrand premises back as triples of `c`, name the ρdf
rule instance whose conclusion is wanted, and let `RhoDfClosed c` put
that conclusion in `c`. That third move is where closedness does the
work, and it is why the theorem is about closed graphs rather than
arbitrary ones.

**Two conditions of the fragment, each earned by one rule.** `rdfs3`
moves a term from object into subject position, so it cannot fire on a
literal or triple term; `rdfs7` moves a term into a predicate slot, so
a `rdfs:subPropertyOf` object must be an IRI. Only `herb_cond_range`
and `herb_cond_subPropertyOf` take the fragment hypothesis — the other
four do not, and their statements say so.

**Naming.** `RDF/EntailmentRdfsSpec.lean` already has `RhoDfGraph`,
which says the ρdf vocabulary never occurs outside the predicate slot.
That is a different condition. This module's predicate is
`RhoDfModelFragGraph`, and the header says why the two exist.

**Finding C-1 is carried as theorems, not as prose.** The F\* module
records that "RDFS entailment = simple entailment of the RDFS closure"
is false and cannot be repaired by narrowing the fragment. The first
witness is now a pair: `rdfsEntails_subclassSelfLoop` (from
`[X rdfs:subClassOf Y]`, RDFS entails `[X rdfs:subClassOf X]`, through
`CondSubClassOfIc` then `CondSubClassOfRefl`) and
`rhoDf_not_entails_subclassSelfLoop` (the same pair is not
ρdf-entailed, by the Herbrand countermodel). The second theorem depends
on `herbrand_rhoDfConditions`, so the countermodel is admissible rather
than merely asserted.

Coverage after this landing: 192 of 220 F\* modules covered, 28 not
covered.

**A measurement note belongs with this landing.** The alias was added,
the count did not move, and the reason was a `git stash` cycle that had
dropped the edit to `tools/lean-port-gap.py`. See the tenth correction
in `docs/designissues/2026-08-23-lean-port-gap.md`, and the extended
rule 2 in `skills/counting-coverage/SKILL.md`.

---

## `SPARQL11.Algebra.Refinement` layer 1 → `SPARQL/AlgebraRefinement.lean` (2026-08-23)

**Partial by design, and the count does not move.** The F\* module is
2,497 lines. This is its first layer. `SPARQL11.Algebra.Refinement`
stays on the not-covered list and no alias was added — see the ninth
correction in `docs/designissues/2026-08-23-lean-port-gap.md`.

**In:** UNION at the set and bag layers, unconditionally. FILTER at both
layers under `FExprCongr`. The compatibility bridge and its witness.
**Out:** JOIN, LEFTJOIN, EXTEND, PROJECT, DISTINCT, the BGP vertical.

**FILTER needs a hypothesis, and the hypothesis is the F\* source's own
finding FC-1.** The evaluator applies the condition to each ROW of the
list; §18.5 applies it to the MAPPING. Those agree only if the
condition cannot tell two lists denoting one mapping apart. It is a
hypothesis here rather than a theorem because this module's `FExpr` is
§18.5's abstract predicate, exactly as the specification states it.

**The compatibility bridge is where the two sides genuinely differ.**
`Binding.compatible` decides agreement with `Term.eqb`, which bottoms
out in `Literal.eqb` — language-tag case folded, `rdf:XMLLiteral`
lexical forms compared by exclusive canonical XML. `Compatible` demands
`t1 = t2`. So the engine's test is strictly COARSER:
`compatible_of_Compatible` holds, its converse does not, and
`compatible_not_Compatible_of_coarse` is the witness. Same shape as
finding SR-2 in the F\* source and finding SE-1 on the
simple-entailment vertical.

**A second hypothesis the F\* banner predicts.** `compatible_of_Compatible`
needs `noRepeats (sdom mu1)`. `Binding.compatible` tests EVERY pair in
the list; `sval` sees only the first binding for a variable. A
duplicate-key list therefore makes the two disagree, and the
specification's own header says exactly this about `sm_compatible` in
the F\* tree — it pins the difference on the REPRESENTATION.

**Why the concrete witness pair is a `#guard`, not a `decide`.**
`langTagEq` calls `String.toLower`, which is `String.mapAux`, and the
kernel does not reduce it: `decide` gets stuck at
`(String.mapAux Char.toLower "en" "en".startPos).1.1.toList`. So the
theorem is stated over ABSTRACT literals with the conflation as a
hypothesis, and two `#guard`s carry the satisfiability evidence on the
compiled evaluator. They are what stop the theorem being vacuous, and
they run on every `lake build`. The abstract form is also stronger: it
holds of every pair the engine conflates, not only of `"x"@en` versus
`"x"@EN`.

**One reusable piece.** `binding_lookup_eq_sval` — the engine's
`Binding.lookup` and the specification's `sval` are the same partial
function, written with different argument order and `=` against `==`.
Every later join lemma will need it.

---

## `RDF.Entailment.RDFS.Refinement` — the RS-1 witness (2026-08-24)

**Partial, and the count does not move.** The F\* module is 1,613 lines
and about 95 declarations, most of them `rdfs_rule_*_licensed`. The
Lean tree already carries that per-row pattern in
`RDFS/ClosureTheorems.lean` and `RDFS/FullClosureTheorems.lean`, but
against `RDF.Entailment.RDFS.RhoDFClosure` and against a
proof-theoretic derivation relation, so those files do NOT cover this
module. No alias was added.

What is ported here is the finding RS-1 vertical:
`RDFS/ReflexivityWitness.lean`.

**The fact the fix rests on.** The pre-fix `rdfs_reflexivity_axioms`
emitted `C rdfs:subClassOf C` for every `C` typed `owl:Class`. rdfs10
fires on `rdfs:Class`, not `owl:Class`, so the emission was not
RDFS-entailed. `selfloop_not_axiomatic` states that the self-loop is in
no axiom table of either vocabulary, for every IRI and every datatype
map and container slice, so no later edit can justify the emission by
declaring the triple axiomatic.

**The statement needs no side condition, and the reason is worth
recording.** Both open axiom families emit only `rdf:type`,
`rdfs:domain` and `rdfs:range` rows, so neither can produce a
`rdfs:subClassOf` triple at all. The F\* source's note that "every
axiomatic `rdfs:subClassOf` row has distinct endpoints" applies only to
the fixed table. `containerAxioms_pred` and `datatypeAxioms_pred` say
this in one line each.

**What the same fact costs in each tree.** The F\* proof carries
`--fuel 50 --ifuel 2 --z3rlimit 600 --split_queries always
--using_facts_from '*,-RDFS.Closure.emit_once_term'` and about thirty
lines of comment. Its own record: z3 returned "unknown because
(incomplete quantifiers)" at 75 of a 240 rlimit; the budget later went
600 to 1200; and one unrelated symbol had to have its facts EXCLUDED,
because its definition equation in the SMT context tipped a borderline
`assert_norm` block — raising rlimit to 1200 and fuel to 100 did not
recover it.

The Lean proof is a case split on a finite table. No budget, no query
splitting, no fact filtering. The two proofs establish the same fact
and differ only in what the host makes hard. That is instance five of
the pattern in
`docs/designissues/2026-08-24-what-the-lean-port-found.md`, and the
first one where the difficulty is in the PROOF rather than in the code.

**One trap.** `decide` refuses a goal with a free variable, so
`(owlClassReflTriple c).p = rdfType` must be reduced through
`selfloop_pred` to the closed `rdfsSubClassOf = rdfType` first.

---

## `SPARQL11.Algebra.strip_rewrite_internal_vars` + `OWL.QueryEval` wiring → `SPARQL/RewriteVarStrip.lean` (2026-08-24)

**A gap found INSIDE a module the tool counts as covered.**
`SPARQL11.Algebra` is aliased to `SPARQL.Algebra` and counts as
covered, but `strip_rewrite_internal_vars` and its two helpers were not
in the Lean tree. An alias is a statement about a module, and a module
is not one result. Rule 6 of `skills/counting-coverage` says covered
means the result is carried; for a module this large, the honest
reading is that the alias covers the module's PRINCIPAL result, and
individual functions can still be missing. Worth a systematic check
later, and noted here so the 192 figure is read correctly.

**What is ported.** `isRewriteInternalVar` (the seven prefixes),
`stripRewriteInternalVarsMu`, `stripRewriteInternalVars`, and the three
`OWL.QueryEval` wrappers with the rewrite as a PARAMETER.

**The constraint CLAUDE.md states in prose is now a theorem.** CLAUDE.md
says the strip "must stay at the top level" because inner Select_All
sub-selects re-expose the anchor var for the enclosing JOIN, and
stripping inside decorrelates it.
`strip_inside_join_admits_spurious_row` is that, machine-checked: two
rows disagreeing on `_sv_1` do not join, and after stripping they do,
so the stripped join returns a row the unstripped join does not.
Moving the strip inward does not lose a column — it changes which rows
come back.

**`OWL.QueryEval` stays not covered, and no alias was added.**
`OWL.QueryRewrite` is 1,799 lines and unported, so the wrappers take
the rewrite as a parameter. The Lean side cannot run an OWL-rewritten
query. What IS carried is the composition and the strip placement,
which is the part CLAUDE.md flags as load-bearing.

**One trap.** `String.startsWith` does not reduce in the kernel — same
family as `String.mapAux`. `rfl` and `decide` both fail on
`isRewriteInternalVar "_sv_1" = true`. The tree's own `strStartsWith`
(`SPARQL/Expr.lean`, `listIsPrefix` over `toList`) does reduce, and
switching to it made the classification theorem and the join witness
close by `rfl`.

---

## The IRIREF scanner refactor — unblocking the N-Triples round trip (2026-08-24)

`Syntax/IriScan.lean`. Groundwork for
<https://github.com/danbri/factoidal/issues/565> and therefore for
`RDF.NTriples.RoundTrip`.

**The blocker, restated.** `Lexing.readIriRefBody` is a ten-arm
recursive match, two arms carrying six- and ten-character literal
patterns. Lean's well-founded recursion generates one equation lemma
per arm, and generating them exhausts the container's memory. No
equations means no rewriting, so the round trip cannot be stated about
it at all.

**The fix, and why it works.** Move the deep patterns out of the
recursion. `iriNextStep` does all the pattern matching and does NOT
recurse, so its match compiles to a plain case tree. `scanIriBody`
recurses on a three-constructor `IriStep`, so its equations are three
small ones — `scanIriBody_close`, `scanIriBody_fail`,
`scanIriBody_emit`, all proved here. Those three are exactly what
`readIriRefBody` cannot give.

**Termination is now one lemma.** `iriNextStep_emit_shorter`: an `emit`
step consumed at least one character. It is provable arm by arm
precisely because `iriNextStep` does not recurse.

**Two `let`s had to go.** `split` cannot see through a `let` compiled
to `have`, so the escape arms' `let cp := ...` blocked the termination
proof. The `\u` and `\U` tails are now one shared `iriEmitAt` helper —
shorter, and `iriEmitAt_emit` reduces both arms of the big proof to one
line each. The plain-character arm's `let cp := c.toNat` was inlined.

**Not yet swapped in.** `Syntax.Lexing` still uses `readIriRefBody`.
Ten `#guard`s check that `scanIriBody` and `readIriRefBody` agree on
the same input — including both escape forms, both malformed escape
forms, an unterminated body, a forbidden character and the empty
input — but a full equality would need the equations that cannot be
generated, which is the whole problem. Swapping the shipping lexer over
is a separate landing so that a transcription error meets the 325
`#guard`s of the syntax tests on its own commit.

**Axiom note.** Both theorems report `[propext, Quot.sound]` — narrower
than the usual three, with no `Classical.choice`.

---

## The IRIREF scanner swap (2026-08-24)

Step 1 of the three on
<https://github.com/danbri/factoidal/issues/565>. `Syntax.Lexing`'s
`readIriRefBody` is now the split scanner, so its equation lemmas can be
generated — `readIriRefBody_close`, `readIriRefBody_fail`,
`readIriRefBody_emit`, all in `Syntax/IriScan.lean`. That is what the
N-Triples round trip needs and what the ten-arm version could not
supply.

**How it was gated, and why the obvious gate was not enough.** The old
scanner was kept for one commit as `readIriRefBodyLegacy` and the two
were `#guard`ed against each other over 36 inputs — every escape width,
every forbidden codepoint, malformed escapes, a surrogate, raw control
characters, unterminated and empty input — agreeing on answer, error
position AND error message. The next commit deleted the oracle and kept
its certified answers as 39 literals.

The reason for that ceremony: of the 325 `#guard`s in `SyntaxTests`,
`TurtleTests` and `RdfXmlTests`, exactly one touches an escape inside an
IRIREF, and it is a rejection case. No test in any suite decodes a `\u`
or `\U` inside `<…>`. An earlier status message in this session claimed
those 325 guards would catch a transcription error here. They would
not. Filed as
<https://github.com/danbri/factoidal/issues/567>.

**A negative control was run.** Setting one expected offset to a wrong
value makes the build error, so the pinned table is not vacuous. Worth
doing whenever a table of expectations replaces a differential check —
otherwise the table's silence proves nothing.

**One deliberate difference.** The old scanner was STRUCTURAL recursion
on the input list; the new one is well-founded recursion on `cs.length`,
because the step classifier returns a `rest` Lean cannot see as a
structural subterm. Behaviour is unchanged, but definitional unfolding
differs, so a proof that relied on the old one reducing by `rfl` needs
one of the three equations instead.

**Traps paid for again.** `/-- … -/` cannot attach to a `#guard` (use
`/-! … -/`); `"\u{1F600}"` is not a valid Lean literal here (use
`String.singleton (Char.ofNat 0x1F600)`); and `private` in Lean 4 is
module-scoped, so an oracle consumed by a sibling module cannot be
private.

---

## The N-Triples IRI round trip — step 2 of #565 (2026-08-24)

The scanner split unblocked what `Syntax/NTriplesRoundTrip.lean`'s own
header had recorded as unprovable. That header is now corrected in
place, with the record of why it was true kept.

**Proved.** `readIriRefBody_printSafe`: on the print-safe fragment the
scanner reads back exactly the characters the serialiser wrote, stops
at the closing `>`, reports the offset just past it, and leaves nothing
unread. `readIriRef_toNTriples` at the token entry point, and
`readSubject_toNTriples` one step further out — through the parser's
re-validation, so the term recovered is the term serialised rather than
merely the same characters. `mkIri_val` is the re-validation step:
`WfIri` is a subtype, so the proof component is irrelevant.

The induction is the three lines the module predicted. A safe character
always takes the `emit` arm, because `IriSafeChar` excludes both `>`
(through the forbidden-codepoint set, which contains `0x3E`) and `\`.

📊 **The coverage count did NOT move, and that is correct.**
`RDF.NTriples.RoundTrip` also carries the object-position term round
trip and `checkpoint_a_closed_triple_round_trip`, a whole-triple
statement. Neither is here, so no alias was added and the module stays
on the not-covered list. Checked before writing that: the tool has no
alias for it, so the still count is a genuine not-covered rather than a
dropped edit — the failure mode the tenth correction records.

**Traps.** `String` is byte-array backed in this toolchain, so
`c.toString ++ String.ofList tl = String.ofList (c :: tl)` does not hold
by `rfl` and needs `String.ext`. And `i.val.toList.length =
i.val.length` IS `rfl`, so `by simp` on it fails with "no progress" —
`simp` cannot make progress on a goal that is already closed by
reflexivity.

---

## `RDF.NTriples.RoundTrip` — COVERED (2026-08-24)

📊 **192 → 193 of 220.** The commit is this one; the enabling commits
are `d09e828b224`, `fbbd2c4628a`, `80ee4521da2` (the scanner split) and
`cf5ca30bfe9` (the IRI round trip).

Generalising the scanner lemma over a TRAILING REMAINDER is what
unlocked the rest: in a serialised triple each IRI is followed by more
line, so a theorem returning rest `[]` cannot be chained.
`readIriRefBody_printSafe` now takes a tail, and subject, predicate and
object positions follow in three lines each.

**The closed-triple round trip is stronger than the F\* one.** F\*'s
`checkpoint_a_closed_triple_round_trip` is stated for ONE CONCRETE
TRIPLE — `"x:"`, `"y:"`, `"z:"`, recovered position literal `16`, as its
own banner says. `readTriple11_closed_roundTrip` quantifies over any
three print-safe IRIs. The offset is existentially quantified because
it is parser bookkeeping; the recovered TRIPLE and the unread REMAINDER
are both pinned, and `tripleToNTriples_closed` shows the input really is
the shipping serialiser's output rather than a hand-built lookalike.

**Why covered while carrying about a third of the declarations.** The
F\* module's other dozen results are UTF-8 byte-walking lemmas —
`lemma_build_string_*`, `nth_byte_index_iri`,
`lemma_utf8_enc_char_iri_safe`, the `lemma_scan_iri_end_*` family. They
exist because `FStar.String` is byte-indexed through axiomatised
primitives, so reading one character means reasoning about one to four
bytes and their lead and continuation ranges. `List Char` needs none of
them. Instance twelve of the pattern in
`docs/designissues/2026-08-24-what-the-lean-port-found.md`, and the same
reason the fourteen by-design modules want no counterpart.

**Traps.** `skipWs` goes through `List.span.loop`, which does not reduce
under `simp` without `isNtWs` unfolded IN THE HYPOTHESIS as well as the
goal — `simp only [isNtWs, ...] at h` first. And an existential witness
cannot be supplied by `refine ⟨_, ?_⟩` before the goal is reduced;
reduce first, then `exact ⟨_, rfl⟩`.

---

## `SPARQL11.Parser.AskBgpRoundTrip` — the parser direction pinned, not proved (2026-08-24)

The text-to-tokens half was already there (`tokenize_printAsk`). The
F\* module's top-level result is the whole round trip: parsing the
printed query recovers `GP_BGP b`, general over any fragment BGP with a
trailing token stream and enough fuel — the same trailing-remainder
shape the N-Triples work needed.

**Checked that it is true before deciding how to state it.** Running
the shipping `parseSparql` on `printAsk` of a one-triple BGP recovers a
one-pattern BGP and the ASK form. Three `#guard`s pin that on every
build, so the statement to be proved is known true rather than hoped
for.

**Not proved, and the chain is named.** Six layers, each conditional on
the next, matching the fifteen lemmas the F\* module spends on it:
`pPrologue` no-op, `resolveIriTokens` identity on absolute IRIs,
`pAskBody`, `pGroupGraphPattern`, `pTriplesBlock`, and fuel accounting.
Layer 5 is the work: the Lean `pTriplesBlock` calls
`pSubjectWithExtras` and `pPredObjList`, which fan out into property
paths, collections, blank-node property lists and annotations — the F\*
counterparts are `lemma_parse_subject_with_extras_1`,
`lemma_parse_pred_obj_list_1`, `lemma_parse_object_list_simple_1`,
`lemma_parse_object_with_extras_1`, `lemma_parse_annotations_dot`,
`lemma_ggp_add_triple_acc` and `lemma_ggp_join_acc_empty`.

That is a multi-session job, not a landing. `SPARQL11.Parser.AskBgpRoundTrip`
stays not covered and no alias was added.

**The doc-comment trap, hit a third time.** `/-- … -/` cannot attach to
a `#guard`. It is in these notes twice already and still cost a build
cycle. When adding guards, write `/-! … -/` first and never the other.

---

## `OWL.QueryRewrite` layer 1 → `OWL/QueryRewriteCore.lean` (2026-08-24)

Partial. The F\* module is 1,799 lines, 961 of them code, 83 top-level
declarations. This is the layer underneath the rewrite: node identity
for anonymous nodes, the RDF-collection walk through a BGP, and the two
flat extractors. `OWL.QueryRewrite` stays not covered and no alias was
added.

**What is here.** `markerKey` / `subjectMarkerKey` / `sameAnonNode`
(a marker bnode reaches the rewriter either as a real
`PatternTerm.bnode` or as a variable the runner renamed to
`_bnode_<id>`, and both must key the same), `bgpFindFirstObj`,
`walkCollectionAcc` / `walkCollection` fuel-bounded by the BGP length,
and `extractFlatIntersection` / `extractFlatUnion`.

**One property worth having before anything is built on this.**
`walkCollection_mem` and `extractFlatIntersection_mem`: every operand
the walk returns is the object of a triple already in the BGP. That is
what stops the rewrite emitting a class the query never mentioned — the
kind of claim a rewriter needs before it can be trusted to preserve
answers. It rests on `bgpFindFirstObj_mem`, which is the same statement
one layer down.

**Why the walk is fuel-bounded.** Each step consumes one
`rdf:first`/`rdf:rest` pair, so the BGP length bounds it, exactly as in
the F\* source. A truncated or malformed collection returns what it
collected rather than failing, and the caller decides — `#guard`s pin
both the well-formed and the truncated case.

**Known narrowness, unchanged.** CLAUDE.md records the shipping rewrite
as sound-but-narrow at
<https://github.com/danbri/factoidal/issues/236>. This layer only
decides what the operands are; it does not touch that.

**What remains for the module.** The rewrite itself, the `GraphPattern`
traversal that finds candidate `?x rdf:type _:c` triples, the UNION
construction for `owl:unionOf`, and the Phase 4 nested cases. Also
`OWL.QueryEval` (51 lines), whose composition and strip placement are
already ported in `SPARQL/RewriteVarStrip.lean` with the rewrite as a
parameter — porting the rewrite fills that parameter and covers both
modules.

**Namespace note.** `strStartsWith` lives in `L4Factoidal.SPARQL`
(`SPARQL/Expr.lean`), `rdfFirst`/`rdfRest`/`rdfNil` in
`L4Factoidal.RDFS`, and `owlIntersectionOf`/`owlUnionOf` in
`L4Factoidal.OWL.RL` — not `L4Factoidal.OWL`. Three separate opens.

---

## `OWL.QueryRewrite` layer 2 → `OWL/QueryRewriteFlat.lean` (2026-08-24)

Layer 1 decided what the operands of a flat class expression are. This
decides what happens to the BGP. Still partial — the `GraphPattern`
traversal, the UNION ladder and the Phase 4 nested cases remain — so no
alias, and coverage stays 193 of 220.

**Three kinds of triple, and every triple is exactly one.** Marker
bookkeeping (`owl:intersectionOf`, `owl:unionOf`, `rdf:type owl:Class`,
and the collection's `rdf:first`/`rdf:rest` cells) is deleted, because
it describes the class expression rather than the data. A consumer
(`?x rdf:type _:c`) is replaced by one triple per operand. Everything
else is kept.

**The property this layer owes.** `rewriteBgpIntersection_mem`: every
output triple is either an input triple, or `⟨s, rdf:type, o⟩` for an
`s` that already appeared as a consumer subject and an `o` that is one
of the operands. With layer 1's `extractFlatIntersection_mem` — every
operand is itself an object in the BGP — that says **the rewrite
invents no IRI**.

That is not answer-preservation. Answer-preservation needs the
entailment regime, and is exactly where the narrowness recorded at
<https://github.com/danbri/factoidal/issues/236> lives (the anchor
multiplies rows per P-edge and drops vacuous-truth individuals). It is
the weaker claim that has to hold first, and it is the one a reader can
check against the module's own definition of the three kinds.

`rewriteBgpStripMarker_mem` is the union branch's counterpart: the
residue every branch shares is a sub-BGP of the input.

**Reusable.** `mem_foldl_append` — membership in a left fold that only
appends — carries both proofs. The RIF port needed the same shape; it
is worth hoisting if a third caller appears.

**Ten `#guard`s on the worked example** from the module header, plus an
unrelated triple that must survive untouched, plus the no-marker case.
Two of them assert the NEGATIVE: after rewriting, no triple is
bookkeeping and none is a consumer. Those are what would catch a
partial deletion.

---

## `OWL.QueryRewrite` layer 3 → `OWL/QueryRewritePattern.lean` (2026-08-24)

The UNION ladder, the marker scan, and the `QueryPattern` traversal.
With this the FLAT path — Phase 3 in the F\* source, `owl:intersectionOf`
and `owl:unionOf` over named classes — is complete end to end: find the
markers, extract the operands, rewrite the BGP, assemble the branches.

Phase 4's nested class expressions and the restriction combinators
(`owl:someValuesFrom`, `owl:allValuesFrom`, the cardinality family,
`owl:complementOf`) are not here, so the module stays not covered and
no alias was added. Coverage remains 193 of 220.

**Why the union branch gets a DISTINCT sub-select.** SPARQL `UNION` is
bag-semantic; OWL `unionOf` is set-theoretic. One `?x` matching two
operands would contribute two rows. The wrapper dedupes the CE-expanded
portion without forcing DISTINCT on the user's outer projection, which
would break bag-semantic queries that never mentioned OWL.

That placement is the same discipline as the internal-variable strip,
and the two now sit on opposite sides of the same rule: the wrap
belongs at the CE-emission site, the strip at the FINAL projection.
`SPARQL/RewriteVarStrip.lean` proves the strip half
(`strip_inside_join_admits_spurious_row`); this layer implements the
wrap half.

**Only 2+ branches are wrapped.** A zero-branch union collapses to
`empty` and a one-branch union to the BGP itself; neither can
duplicate, so wrapping would be dead AST. Two `#guard`s pin both
special cases, because they are the ones a later simplification would
quietly drop.

**What is proved.** `unionLadder_leaves`: the left-deep ladder contains
exactly the branches it was given, in order. A fold that builds a
left-deep tree is easy to write so it drops the head or re-associates,
and neither shows up in a spot check.
`rewritePattern_bgp_noMarker`: a BGP with no flat marker comes back
unchanged — the "safe to apply unconditionally" claim the F\* banner
asserts, for the fragment the traversal reaches.

**One deliberate hole, named in the code.** `rewritePattern` does NOT
descend into `.subSelect`, because that carries a whole `Query` and
needs the Query-level pass. The F\* source puts it in the same place.

---

## `OWL.QueryRewrite` layer 4 → `OWL/QueryRewriteRestriction.lean` (2026-08-24)

The restriction classifier the nested (Phase 4) path needs: given a
marker key, which kind of restriction is it, and is its filler itself a
class expression?

The EXPANSION that consumes this is not here. In the F\* source that is
`expand_ce_subject`, 460 lines, and CLAUDE.md records the known
narrowness living inside it —
<https://github.com/danbri/factoidal/issues/236>: the N=1 qualified
`CE_MaxCardinality` rewrite emits an anchor triple that MULTIPLIES rows
per P-edge and drops vacuous-truth individuals. So `OWL.QueryRewrite`
stays not covered, no alias, coverage 193 of 220.

**The discipline this layer encodes, and why it is not obvious.** Not
every restriction is a rewrite target:

* `owl:someValuesFrom` with a NAMED-class filler is NOT — the OWL-RL
  closure's canonical-bnode materialisation is the correct path, and a
  query rewrite would compete with it (`simple2`).
* `owl:someValuesFrom` with a class-expression filler IS (`simple5`,
  `simple8`).
* `owl:allValuesFrom` always is, whatever the filler.

`svf_namedFiller_not_target` proves the first line rather than leaving
it to the reader — it is the one a later simplification would drop,
because "handle all restrictions uniformly" looks like a tidy-up.

**`restrictionHasNestedFiller` is where three notions of class
expression have to agree**: a flat marker, another restriction, or an
`owl:complementOf` bnode. Any of the three makes a filler nested.

**Vocabulary added.** `owl:cardinality`,
`owl:minQualifiedCardinality` and `owl:qualifiedCardinality` were
absent from `OWL/Vocabulary.lean`; `owl:maxCardinality`,
`owl:maxQualifiedCardinality` and `owl:minCardinality` were already
there. The three complete the family the classifier tries.

**Two traps.** Editing a vocabulary file and then running `lake env
lean` on a dependant reads the STALE `.olean` — build the dependency
first or the new names read as unknown. And a blanket
`open L4Factoidal.OWL.RL` collides with `L4Factoidal.RDFS` on
`rdfType`; the earlier layers already use a selective open, and this
one now does too.

---

## `OWL.QueryRewrite` layer 5 → `OWL/QueryRewriteExpand.lean` (2026-08-24)

The recursive class-expression expander, counterpart of the F\*
source's `expand_ce_subject`. Three arms are here — intersection,
union, existential restriction — plus the leaf. `owl:allValuesFrom`,
the three cardinality arms and `owl:complementOf` are not.

**The boundary is a design decision, not a transcription choice, and it
is the owner's.** CLAUDE.md records the shipping cardinality rewrite as
sound-but-narrow at
<https://github.com/danbri/factoidal/issues/236>: the N=1 qualified
`CE_MaxCardinality` rewrite emits an anchor triple that MULTIPLIES rows
per P-edge and drops vacuous-truth individuals.

Porting it faithfully reproduces that narrowness. Fixing it in Lean
makes the two trees stop computing the same thing — the one property
the differential method rests on, and the reason every finding in
`2026-08-24-what-the-lean-port-found.md` is checkable. Neither is mine
to pick, so this layer stops at the boundary and says why in the module
header.

**The fall-through is proved sound, not assumed.**
`expandCeSubject_unhandled_is_leaf`: an unported arm produces the
pre-rewrite triple. That is the F\* source's own discipline, stated at
its fuel-exhaustion case — *"at worst this is the pre-rewrite
behaviour … Sound — never adds solutions."* Proving it means an
unported arm degrades to the identity rather than to something wrong,
which is what makes stopping at the boundary safe rather than merely
convenient.

**Two modules share one convention, and a `#guard` checks it.** The
existential arm's fresh variable is `_sv_<marker key>`, and
`SPARQL.isRewriteInternalVar` is what strips it from the final
projection. Neither module works if the prefixes drift, so
`isRewriteInternalVar (svVarName "r") == true` runs on every build.
That is worth more than either module's own tests: it is the seam.

**Status of the module.** Five layers in — operands, BGP rewrite, union
ladder and traversal, restriction classifier, expander. The flat path
is complete; the nested path is complete except for the arms above.
`OWL.QueryRewrite` stays not covered, coverage 193 of 220.

---

## `SPARQL/JoinRefinement.lean` — layer 2 of `SPARQL11.Algebra.Refinement`

Layer 1 did UNION and FILTER, and built the bridge between the engine's
`Binding.compatible` and §18.3's `Compatible`. This layer is what that
bridge was for: JOIN.

**The engine's merge prepends, so the bridge is a relation.**
`Binding.merge` puts each new binding at the FRONT, so its result is not
`mu1 ++ mu2` and the list order is the engine's, not the
specification's. §18.3 states merge as a relation on `sval` for exactly
this reason. `merge_isMerge` is the lemma the whole layer rests on, and
it is where the prepending is handled: the induction generalises over
the LEFT mapping, because the engine grows that side.

The statement is `∀ (mu2 mu1 : SMap)` in that order. `mu2` first is not
a style choice — Lean's structural recursion needs the argument it
recurses on to come first, and the recursive call in the `none` arm
passes a DIFFERENT left mapping (`(w, t) :: mu1`).

**Two directions, two hypotheses, neither a weakening.**
`join_spec_complete` needs `noRepeats (sdom m)` on the left mappings:
the engine tests every pair in the list while `sval` reads only the
first, so a duplicate-key list makes the two disagree.
`join_spec_sound` needs an exactness hypothesis as well, because
`Literal.eqb` folds language-tag case, which makes the engine's test
strictly coarser than §18.3's. Layer 1's
`compatible_not_Compatible_of_coarse` is the witness that dropping it
is not available. Each hypothesis names the fragment on which the
shipping engine DECIDES the specification's relation.

**Commutativity is stated about `Occurs`, not about list equality.**
§18.3's merge is symmetric on compatible arguments, so `join o1 o2` and
`join o2 o1` answer the same SET. They do not answer the same LIST,
because `Binding.merge` is order-sensitive. A theorem claiming list
equality would be false; one claiming set equality is what §18.5 says.

**Status of the module.** Two layers in — UNION and FILTER, then JOIN.
`SPARQL11.Algebra.Refinement` is 2,497 F\* lines and stays not covered.
Coverage 193 of 220.

---

## `RDF/ListHelpers.lean` — `RDF.List.Helpers`, and a by-design entry that was half wrong

The F\* module gives tail-recursive `append`, `concatMap` and `assoc`
with equivalence proofs against the standard library. Its header names
the two stack-overflow incidents that paid for it: the Turtle parser
path (<https://github.com/danbri/factoidal/issues/94>) and the BGP
filter-map path, 2026-04-26.

**Lean core already ships two of the three.** `List.appendTR` and
`List.flatMapTR` exist, each tagged with a `@[csimp]` lemma
(`List.append_eq_appendTR`, `List.flatMap_eq_flatMapTR`). A `@[csimp]`
lemma rewrites the definition at CODE GENERATION time, so the compiled
program runs the tail-recursive version while every proof still sees the
structural one. No call site changes. The F\* tree has no such
mechanism, so the same work there is a module of hand-written functions,
hand-written equivalence lemmas, and an edit at every call site.

**`appendTr_eq_core` is the sharper result.** `List.appendTR as bs` is
`as.reverse.reverseAux bs` — reverse the left list, then `reverseAux` it
onto the right. That is the F\* `append_aux` accumulator strategy, arm
for arm. Two independent implementations reached one function, and the
theorem says so rather than a comment claiming it.

`concatMapTr` and `List.flatMapTR` are NOT the same algorithm: the F\*
version accumulates a reversed list, the Lean core version accumulates
into an `Array`. Both equal `flatMap`, which is what
`concatMapTr_eq_core` states. The difference is allocation, not result.

**Why it was ported although the coverage tool called it by design.**
`RDF.List.Helpers` was in `BY_DESIGN_EXACT` in `tools/lean-port-gap.py`.
The reasoning was right about the cause and wrong about the conclusion.
The three F\* functions run on the SPARQL and RIF hot path, so a
differential comparison of the two trees needs both sides to exist. The
transcription is arm for arm against the F\* source; the two core-library
theorems are extra checks the port buys, not substitutes for it.

The by-design entry is now removed with the reason recorded in the tool.
Coverage moved 193 to 194, and this landing is the cause.

`assocTr` is stated over `BEq`, because Lean's `List.lookup` is
`BEq`-based while F\*'s `assoc` takes an `eqtype`. The F\* header says
`assoc_tr` exists for naming symmetry rather than for stack safety, and
that reading carries over: `List.lookup` is already tail-recursive.

Eleven `#guard` checks, five `#print axioms` lines, all `[propext]` or
`[propext, Quot.sound]`. `lake build` green at 792 jobs.

---

## `OWL/QueryRewriteJoins.lean` — layer 6, and a comment turned into a theorem

`rewrite_query` runs `normalise_joins` before the class-expression
rewriter. The reason is in the F\* source: the SPARQL parser splits a
basic graph pattern at every period, so

    ?x a [ owl:intersectionOf (:A :B) ] .

parses to a tree of small `GP_BGP` leaves under `GP_Join`, with the
class-expression marker and its `rdf:first`/`rdf:rest` chain in
different leaves. The rewriter works one BGP at a time and finds
nothing until the leaves are folded back together.

**The claim the F\* source makes in a comment.** The header says the
flattening "preserves SPARQL semantics (GP_Join of two BGPs =
BGP-concat)". That is a statement about §18.5 evaluation, sitting next
to a function on the shipping OWL query path, proved in neither tree.

**What this layer proves.** `evalBgp_append` is the list identity:

    evalBgp (b1 ++ b2) g = (evalBgp b1 g).flatMap (evalBgpFrom g b2)

Exact — same list, same order, same multiplicities — because
`evalBgpFrom` seeds the second half with each row of the first. Four
`*_extends` theorems say the seed survives: `tryBindTerm`,
`tryBindSubject`, `tpMatch` and `evalBgpFrom` each agree with the input
mapping on every variable the input already bound. So coalescing never
overwrites a binding the left BGP made.

**What it does not prove, and why that is stated.** The full claim is

    Occurs mu (evalBgp (b1 ++ b2) g)
      ↔ Occurs mu (join (evalBgp b1 g) (evalBgp b2 g))

`evalBgp_append` reduces the left side to a seeded run of `b2`; the
right side runs `b2` from the empty mapping and filters with
`Binding.compatible` afterwards. Bridging them needs a lemma comparing
seeded and unseeded `tpMatch` on one graph triple, and `tpMatch` threads
the mapping through subject, predicate and object in sequence, so a
pattern with a repeated variable does not decompose into per-position
facts. Tracked as
<https://github.com/danbri/factoidal/issues/568>. Nothing in the module
assumes it.

Both sides use `Term.eqb` — `tryBindTerm`'s bound-variable arm and
`Binding.compatible` — so the `Literal.eqb` coarseness recorded as
finding A5 applies equally to both and is not the obstacle.

**Traps paid for here.** `QueryPattern` lives in `SPARQL/Expr.lean`,
which imports `SPARQL/Algebra.lean`, not the other way round; importing
only `SPARQL.JoinRefinement` leaves `QueryPattern` unknown, and
`autoImplicit` turns the unknown name into an implicit variable so the
error reads "expected type QueryPattern is not of the form `C ...`"
rather than "unknown identifier". `unfold f at h` leaves the outer
`match` unreduced, so `rw [h_lookup] at h` finds nothing until a
`dsimp only at h` fires the iota reduction. `QueryPattern` derives no
`BEq`, so the `#guard` checks go through two small projections
(`bgpSize`, `isJoin`) instead of comparing patterns.

**Status of the module.** Six layers in. `OWL.QueryRewrite` is 1,799 F\*
lines and stays not covered. Coverage 194 of 220.

---

## `RDF/StoreCapabilitiesCottas.lean` — `RDF.Store.Capabilities.Cottas`, and the first laws `StoreCaps` has ever carried

The F\* module builds the read-only capability record for a COTTAS file
on disk. Its own banner states the property that makes it reviewable:
"zero new logic, one-to-one mapping" — every field wraps the entry point
the matching `GB_CottasOnDisk` dispatcher arm already called.

**The purity doctrine.** The F\* module reaches `RDF.CottasStore`, which
is `assume val` I/O: mmap, file ranges, dictionary pages. Those are not
assumptions in the Lean tree. `CottasReadOps` is the record of the eight
entry points the builder wraps, taken as a parameter, and `capsOfCottas`
is the wiring over it.

**`StoreCaps` carried no laws at all.** `RDF/StoreCapabilities.lean` has
no theorems, so nothing in the tree said what a backend record must
satisfy — not the union combinator, not the in-memory builder, not the
dataset seam. A claim about a wiring layer is exactly the kind that
decays: a later edit adds a `take`, a swap or a default and the comment
still says zero.

`StoreCapsLawful` states five laws — `limitAgrees`, `countIsSolve`,
`estimateExact`, `selectiveAgrees`, `presenceSound` — and
`capsOfCottas_lawful` derives all five from facts about the reader and
nothing else. That is what "zero new logic" means, said so a later edit
breaks the build instead of the comment.

**Two backends, one statement.** `capsOfIndexed_lawful` proves the same
contract for the in-memory builder that was already in the tree, with no
hypotheses. Checking two backends against ONE statement is the point of
having the statement.

**Which laws are vacuous where, said out loud** (hazard #24). For the
COTTAS record `estimateExact` is discharged by the flag, because the
builder advertises `estimateIsExact := false` — correct for a reader
whose bounds-present branch approximates, and it means the contract
constrains nothing about that record's `estimate`. For the in-memory
record `selectiveAgrees` is discharged by `solveSelective := none`.
`presenceSound` has teeth for both.

**One faithfulness decision.** The F\* source notes that the
`backend_predicate_present` dispatcher ignores the graph scope, and that
the wrapper "matches that exactly rather than fixing it". The Lean
`CottasReadOps.predicatePresent` therefore takes no scope either.
Changing it would have been a silent behaviour edit dressed as a port.

Nine `#guard` checks, one of them the satisfiability evidence hazard #24
asks for before a theorem with hypotheses is trusted. `lake build` green
at 796 jobs. Coverage 194 to 195 of 220; this landing is the cause.

---

## `OWL/QueryRewriteNested.lean` + `OWL/QueryEval.lean` — layer 7 and the entry point

Layer 7 is the part of `OWL.QueryRewrite` that finds markers ANYWHERE
in a BGP, including inside another marker's filler, plus the nested BGP
rewrite and `rewriteQueryPattern`. `OWL/QueryEval.lean` is the 51-line
F\* wiring module that composes the rewrite with the three top-level
evaluators.

**One marker type, two Lean types.** The F\* `ce_combinator` is one type
carrying the flat combinators and the restriction family. The Lean
layers had split it into `CeCombinator` and `Restriction`, which is
better for the classifier and useless for the marker list, so
`MarkerKind` puts them back together.

**Three passes, in the F\* order.** `findFlatMarkersAcc`, then
`addRestrictionMarkersAcc` over the BGP, then `addInnerRestrictionsAcc`
walking transitively into fillers with fuel of BGP length plus one.
`owl:someValuesFrom` is added only when its filler is itself nested,
because a named filler is already handled by the closure;
`owl:allValuesFrom` and `owl:complementOf` are added unconditionally,
and the F\* source gives the reason for complement — the closure has no
canonical materialisation for class complement, so the rewriter is the
only path.

**The OR that has to stay an OR.** `isNestedBookkeeping` strips a triple
when its subject is a marker and its predicate is class-expression meta,
OR when its subject is on some marker's `rdf:first`/`rdf:rest` chain.
The F\* source records why this is not an `else if`: a nested class
expression can have the parser reuse one blank node as BOTH a marker and
a list cell. Two `#guard` checks pin the case where the two readings
differ — `isNestedBookkeeping [("d", …)] ["d"] dualRoleTriple` is `true`
while the same triple with an empty chain list is `false`, and
`isCeMetaPred rdfFirst _` is `false`, so an `else if` on `isMarker`
would have kept the triple. A later edit that makes it an `else if`
fails the build.

**`OWL.QueryRewrite` is still NOT covered, and that is the right
answer.** Layer 5 deliberately holds back the universal restriction, the
three cardinality arms and `owl:complementOf` in `expandCeSubject`,
because porting them faithfully reproduces the
<https://github.com/danbri/factoidal/issues/236> narrowness and fixing
them makes the two trees stop computing the same thing. That is an owner
decision. An alias for `OWL.QueryRewrite` was added, measured, and
REMOVED for exactly that reason: coverage is an explicit decision, and
seven layers of machinery is not the same as a complete module.
`OWL.QueryEval` IS covered, and it is the cause of 195 to 196.

**Traps paid for here.** All five earlier rewrite layers share ONE
namespace, `L4Factoidal.OWL.QueryRewriteCore`, whatever the file is
called; opening a namespace named after the file fails. `cases tp.p` on
a projection inside a `foldl` body makes `generalize` produce an
ill-typed motive — prove the branch condition constant as its own lemma
(`isAnyTopConsumer_nil`) and rewrite with it instead. `QueryPattern`
derives no `BEq`, so a `#guard` comparing two patterns has to project
first.

**Status.** Coverage 195 to 196 of 220. The remaining not-covered list
is 24 modules: 7 engine (14,997 lines), 3 proof (7,975), 14 by design
(8,993).

---

## `OWL.QueryRewrite` completed — four arms, five leftovers, and two port defects

The module is now covered. Getting there took three things, and the
third is the one worth reading.

**1. The four held-back expander arms are ported.** Universal
restriction, the three cardinality kinds and `owl:complementOf` are
transcribed from the F\* source, including their stated limits: minimum
cardinality over-approximates for N >= 2; maximum cardinality falls
back to the leaf for N >= 2 and for unqualified N = 1; exact
cardinality emits the minimum side only for N >= 1; universal
restriction supports a named-class or union filler and nothing else;
complement targets DISJOINTNESS rather than absence, because a
`FILTER NOT EXISTS` would be closed-world.

**The `maxQualifiedCardinality` 1 narrowness is REPRODUCED, not
repaired.** The anchor triple multiplies rows per P-edge and drops
individuals for which max-1 holds vacuously
(<https://github.com/danbri/factoidal/issues/236>). A repair here would
make the two trees compute different things, and the differential
comparison is what makes every finding in
`docs/designissues/2026-08-24-what-the-lean-port-found.md` checkable.
Repairing it is a separate decision, better taken with both trees in
hand than during a transcription. An earlier note in this file recorded
the port as blocked on that decision; it was not — faithful
transcription is the port's job, and repair is the deviation that needs
sign-off.

`expandCeSubject_unhandled_is_leaf` was DELETED rather than weakened. It
said the unported arms produce the leaf, which is now false. Three
theorems replace it and are true of the finished expander: a restriction
with no IRI-valued `owl:onProperty`, a complement whose target is not a
named class, and running out of fuel each produce the pre-rewrite
triple.

**2. Five definitions the rewriter never calls are ported anyway.**
`concatBgps` and `combinatorOfPred` have no call site in the F\* module;
`tpIsCeMarkerPredicate`, `bgpHasCeMarker` and `patternHasCeMarker` are a
diagnostic cluster used only by each other, and `rewrite_query`'s
comment records that the last of them "no longer drives a top-level
sm_distinct flip". Skipping a definition because a reader judges it
unimportant leaves an unrecorded hole; the judgement is written down
instead.

**3. The audit that made coverage a decision found two port defects.**
Before claiming the module covered, every `let` in its 1,799 lines was
matched to a Lean definition by hand. Thirty names differ in spelling
and each was resolved individually — vocabulary IRIs that live in
`OWL/Vocabulary.lean`, renames such as `ps_marker_key` to
`subjectMarkerKey`, and `rewrite_query_for_owl_direct`, which is an
alias of `rewrite_query`.

It also found this, which no build failure and no existing test would
have:

* `rewriteBgpFlat` applied only the FIRST flat marker of either kind.
  The F\* `rewrite_bgp_flat` applies EVERY intersection marker in order,
  then the first union marker. A BGP with two intersection markers, or
  an intersection followed by a union, was rewritten differently in the
  two trees.
* The `someValuesFrom` arm accepted any `PatternTerm` as
  `owl:onProperty` and put it in the predicate position. The F\* arm
  matches `Some (PT_IRI p_iri)` and falls back to the leaf. `patternIri`
  is now the guard on every arm that reads `owl:onProperty`.

Both are fixed and both carry a `#guard`. The lesson is recorded as
group E in the findings document: a module that builds, proves its
theorems and passes its own tests can still have drifted, because its
tests were written from the same misreading. The only thing that checks
a transcription is reading the source again, definition by definition.

**Status.** Coverage 196 to 197 of 220. Not covered is 23 modules:
6 engine (13,198 lines), 3 proof (7,975), 14 by design (8,993).

---

## `SPARQL/StoreBackend.lean`, `StorePlan.lean`, `StoreFastPath.lean` — three of four layers of `SPARQL11.Store`

The F\* module is the backend-neutral store layer: the algebra stays the
semantic source of truth and this layer dispatches physical
triple-pattern access.

**Layer 1, the seam.** `GraphBackend`, `capsOfBackend`, and the six
`backend_*` forwarders. The F\* banner states the discipline —
"`caps_of_backend` is the ONE dispatch point a new backend touches",
and each dispatcher "is now a one-line forwarder through
`caps_of_backend`'s single dispatch point". Six theorems say that, so a
backend cannot grow a second dispatch path without one of them failing.

The purity doctrine applies at the backend types: an HDT store, a
COTTAS dataset and a COTTAS on-disk store are handles into `assume val`
I/O, so each becomes the operations it offers. `BackendReadOps` is
`search`, `estimate` and `predicatePresent`, which is all the two DEAD
arms need — the F\* banner names them dead itself ("GB_HDT, and the dead
in-memory GB_COTTAS path … no live construction site, same for
GB_List"). They are ported anyway, for the reason the previous landing
gives: dropping an arm on the reader's judgement leaves an unrecorded
hole.

`capsOfReadOps_lawful` and `capsOfList_lawful` put both dead arms under
`StoreCapsLawful`, and here `estimateExact` is NOT vacuous — these arms
advertise an exact estimate, so the law constrains them where it did
not constrain the COTTAS record.

**Layer 2, planning.** `patternBoundFor` grounds a triple pattern under
a solution mapping. Three of its rules are RDF, not optimisation, and
each is a theorem: a triple-term SUBJECT pattern never grounds, a
variable bound to a literal never grounds a PREDICATE, and a
triple-term OBJECT grounds only when all three positions do. A bound
that is too tight silently drops rows, which is why these are stated
rather than trusted.

`chooseBest_perm` is the planner's correctness obligation: the chosen
pattern together with the returned rest has the same length as the
input, so the planner reorders work and never adds or drops a pattern.
The F\* source states the cost intent in a comment; the safety property
was unstated in both trees.

**Layer 3, the fast paths.** Streaming `COUNT(*)` and LIMIT pushdown,
with their detectors. Every rejection is load-bearing, because falling
through to the materialise path is always correct and matching a subtly
different shape is not. Six theorems pin the rejections a later
widening would be tempted to drop, including the one the F\* source
argues at length: `GRAPH ?g { tp }` with a VARIABLE graph is refused,
because an unbound `?g` ranges over every named graph, so a non-grouped
`COUNT(*)` over that shape is a SUM over N backends — a different
evaluation shape, not a mechanical widening.

`evalLimitSingleTp_bounded` says the LIMIT path never returns more rows
than the limit, however the backend behaves, because the result is
truncated after the pattern match as well as before it.

**A vacuity check that was worth running** (hazard #29).
`detectStreamingCountStar_rejects_distinct` closes its last case by
`rfl`, which looks like a theorem that does not use its hypothesis. It
does: with the hypothesis removed from the statement, the same script
fails on the un-reduced `if q.modifier.distinct …` chain. The check was
run explicitly and the result is recorded next to the theorem, together
with the `#guard` that the detector returns `some` on a clean query —
the other half, which rules out a detector that is constantly `none`.

**One representation difference, stated.** The F\* `q_having` is an
`option` and its detectors test `Some?`; the Lean `Query.having` is a
`List Expr` and the same test is "not empty". Both mean "the query has
a HAVING clause" and the rejection fires on the same queries.

**Status.** `SPARQL11.Store` stays NOT covered. Twenty-four of its 44
`let`s are matched; the remainder is one more layer — the dataset seam
(`dataset_caps_of_backend`, `lookup_named_backend`,
`materialize_dataset_backend`, the backend constructors),
`eval_pattern_backend`, `eval_fulltext_tp_backend`, the GROUP BY
streaming family, and the two query entry points. Coverage stays 197 of
220.

---

## `SPARQL/StoreDataset.lean` — layer 4, and `SPARQL11.Store` complete

The dataset seam, the backend-routed pattern evaluator, the GROUP BY
streaming family, and the two query entry points.

**Where the two trees genuinely differ, stated rather than hidden.** The
F\* `eval_pattern_backend` recurses structurally through FILTER,
LEFTJOIN and BIND, and materialises the dataset only for the three arms
it cannot do natively — FILTER/LEFTJOIN carrying an EXISTS, LATERAL, and
property paths. The Lean tree cannot, and the reason is architectural.
`QueryPattern.lowerWith` compiles a FILTER condition into a CLOSURE over
the active graph and a LATERAL right operand into a function of the left
row; those closures are how the Lean algebra states §18.6's EXISTS, and
they are built at lowering time. A backend-routed evaluator here either
rebuilds the whole lowering or delegates.

This module delegates. BGP, JOIN, UNION, MINUS, `GRAPH <constant>` and
the empty pattern are backend-native; every other arm materialises and
runs the algebra evaluator. **What that costs is performance on those
shapes, not correctness** — the delegate is the algebra evaluator, which
is the semantic source of truth in both trees, and it is the same device
the F\* source uses for its own hard arms, applied to more of them. Four
theorems pin which arms are native so the list cannot drift silently.

**The cross-check.** `evalBgpBackend_allVars_list` proves that on a list
backend, an all-variable one-pattern BGP evaluated through the backend
equals the same BGP evaluated by the algebra. It is one pattern because
the planner reorders longer BGPs, and all-variable because a bound
position makes the backend pre-filter — proving that pre-filter never
drops a row the match would keep is a separate lemma about
`boundMatches` against `tpMatch`.

**Two backends the Lean tree cannot construct, and three it does not
need.** `cottas_ondisk_dataset_backend` discovers its named graphs by
READING the store; `cottas_with_delta_dataset_backend` reads and parses
a delta log under the `ML` effect. Under the purity doctrine the read
is a parameter, so both take the graph list they would have discovered.
`indexed_graph_backend_for` and its two siblings build only the index
BUCKETS a pattern needs; they have no Lean counterpart by design, for
the reason already recorded for the `RDF.Indexed.KeyInjectivity` group —
the Lean index is a `Std.HashMap` keyed on structured values, so there
are no six buckets to choose between.

**A dead definition, ported.** `eval_select_query_backend_bgp` has NO
call site in the F\* module: it sits inside the mutually recursive group
and is never invoked. It is ported anyway, with that fact written down,
on the same discipline as the unreferenced definitions of
`OWL.QueryRewrite`. Folding it into the materialise arm would have LOST
its behaviour rather than preserved it: it returns `none` when the query
needs grouping, and the Lean materialise arm does not need that escape
because `selectPost` runs the whole post-WHERE pipeline.

**ASK cannot read an empty answer as `false`.** When the answer is empty
AND any backend reports a decode failure, `evalAskBackend` returns
`none`. The F\* source explains: a column that fails to decode
contributes zero rows silently, so "genuinely empty" and "could not
read" are indistinguishable downstream, and ASK would turn a read
failure into a wrong answer with a clean exit.
`evalAskBackend_none_on_decode_failure` is that as a theorem.

**The audit's own reach was a finding** (hazard #28). The first pass
matched only `^let` and reported 24 of 44 names covered. It could not
see the mutually recursive `and`-bound group, which is where
`eval_pattern_backend`, both query entry points and the fuelled BGP
evaluator live — the four largest definitions in the module. The
corrected regex matches `let`, `let rec` and `and`, finds 50 names, and
the alias in `tools/lean-port-gap.py` carries it so the next reader
audits with a method that can see what it is looking for.

**A trap that cost a build cycle.** A compound `cd formal/lean4 &&
python3 - <<EOF` run from a shell already IN `formal/lean4` fails at the
`cd`, so the edit never applies — and the `lake build` that follows
reports SUCCESS, because it built the unchanged file. The tell is that a
name the edit was supposed to add is still unknown one command later.
Verify an edit landed (`grep -c`) before trusting the build that follows
it.

**Status.** `SPARQL11.Store` is covered. Coverage 197 to 198 of 220.
Not covered is 22 modules: 5 engine (11,746 lines), 3 proof (7,975),
14 by design (8,993).

---

## `SPARQL/AskBgpRoundTrip.lean` — the impossibility, resolved at its cause

`SPARQL11.Parser.AskBgpRoundTrip.fst` is proof-only and marks its
headline result IMPOSSIBLE. Its header names the cause exactly:

> `FStar.String.sub`'s specification in this ulib snapshot exposes ONLY
> a length refinement, no lemma relating its output characters to the
> input string's content — so no lemma can be stated, let alone proved,
> connecting a printed payload string back to the token.

and notes the obstruction blocks EVERY payload-carrying token, with a
sibling module's own flagged gap having the same cause one level lower.

**The wall is the host library's string interface, and nothing else.**
The Lean tokenizer works on `List Char` end to end: `scanIriBody` and
`scanVarName` are ordinary list recursions. So the lemma F\* cannot
STATE is here an ordinary induction, and both payload scans the F\*
header names are proved:

* `scanIriBody_printed` — scanning a printed IRIREF body returns the IRI
  text and the rest of the input.
* `scanWhileVar_printed` and `scanVarName_printed` — the same for a
  variable name.

That is finding A1 made concrete. It is not about RDF, not about
SPARQL, and not about the parser.

**The hypotheses are RDF facts, not proof conveniences.**
`scanIriBody_printed` needs the IRI text to carry no `>` and no
backslash: `>` ends the IRIREF and a backslash starts an escape, so an
IRI carrying either does not print and scan back to itself. That is
§19.8 [139]'s own character rule. Two `#guard` checks exhibit a text
that fails it, so the side condition cannot be mistaken for decoration.
`scanVarName_printed` needs [143] VAR1's character class, checked the
same way.

**One faithfulness decision.** The F\* fragment predicate excludes one
specific IRI — the full-text query predicate — because that predicate
routes the object grammar through a bespoke argument form. The Lean
version takes the excluded list as a PARAMETER rather than hard-coding
an IRI into a syntactic fragment, and a `#guard` exercises the
exclusion.

**What is proved and what is checked, said plainly.** The payload
lemmas are proved. The end-to-end string round trip is CHECKED by
`#guard` on three concrete queries — printed, tokenized, compared
against the expected tokens, and parsed back to an AST. The general
theorem needs two mechanical steps first: fuel normalisation for
`tokenizeLoop`, and a per-token consumption lemma so its no-progress
guard can be shown never to fire. Both are written up in
<https://github.com/danbri/factoidal/issues/569>.

**Coverage is NOT claimed.** `SPARQL11.Parser.AskBgpRoundTrip` stays
not covered while its headline theorem is a check rather than a proof,
and its roughly thirty token-level parse lemmas are about the F\*
parser's own internals. Coverage stays 198 of 220. Marking it covered
because the module exists and builds would be exactly the name
resemblance `skills/counting-coverage` forbids.

---

## `Syntax/NQuadsStreaming.lean` — layer 1 of `RDF.NQuads.Streaming`

The F\* module answers a precise version of the owner's question: a
consumer folds over ARBITRARY byte-chunk boundaries — as bytes arrive
off a socket, with no guarantee a boundary lands on a line boundary —
and the claim is that this gives the same dataset as parsing the whole
input at once.

**The wall the F\* module walked around, and why Lean has none.** Its
banner records a decision taken DURING the work, not going in: build
the splitter on `FStar.String.list_of_string` at the CODEPOINT level
rather than on `Parser.FastString`'s byte-indexed `fs_byte_sub`.
Proving "slice at k, slice from k, concatenate, get the input back"
through `fs_byte_sub` needs a bridging lemma routing through
`utf8_decode_all (utf8_bytes s)`, and recovering `s` from that
composition is the SINGLE-DECODER ROUND TRIP theorem
`Parser.FastString.Spec.fst`'s own banner documents as ATTEMPTED and
PARKED after three tries
(<https://github.com/danbri/factoidal/issues/374>).

The Lean parser works on `List Char` throughout. The split is a list
split and `splitCompleteLines_reconstruct` is a short induction. There
is no byte layer to bridge and nothing to park — the same shape as
findings A1 and A9c.

**Three theorems, each a property the fold depends on.**
`splitCompleteLines_reconstruct` says nothing is lost at a boundary.
`splitCompleteLines_carry_no_newline` says the carry is a genuine
partial line, never a whole one held back.
`splitCompleteLines_complete_ends_newline` says what reaches the parser
is whole lines.

**Fuel is never threaded across a boundary.** `parseFrom` computes it
from the list it is given — the same `length + 1` discipline
`parseNQuads` uses for a whole document — so each call gets its own
provably-sufficient budget. `parseFrom_fuel_is_local` states that.

**What is proved and what is checked.** `streamParse_single_chunk` is
proved: it is the case that needs no line-boundary concatenation lemma.
The mid-boundary behaviour is CHECKED — two lines streamed as two
chunks split mid-line, as three chunks with both boundaries mid-line,
and with a boundary exactly on the newline, each giving the dataset the
batch parse gives.

The homomorphism itself is NOT proved. It needs
`lemma_parse_nquads_acc_concat_line_general`'s Lean counterpart, and
the scaffolding around that lemma is the bulk of the F\* module's 3,438
lines. Tracked as <https://github.com/danbri/factoidal/issues/570>.

**A build-time cost worth naming.** Every `#guard` runs at build time,
and a streaming check with N chunks makes N parser calls. A first
version used realistic `http://example.org/...` IRIs and a
one-chunk-per-character case; `lake env lean` on that single file did
not finish in ten minutes. The checks now use short `<a:1>`-style IRIs
and at most three chunks, which exercises exactly the same boundary
cases. A `#guard` that takes minutes is a test nobody will keep.

**Coverage is NOT claimed.** `RDF.NQuads.Streaming` stays not covered
while its headline theorem is unproved. Coverage stays 198 of 220.

---

## `Syntax/LexShift.lean` — the lemma two open proofs were both waiting on

Two remaining proofs needed the same fact, and neither could finish
without it: the N-Quads streaming homomorphism
(<https://github.com/danbri/factoidal/issues/570>) and the SPARQL
ASK-BGP string round trip
(<https://github.com/danbri/factoidal/issues/569>). Both reduce to
"parsing `a ++ b` factors through the state parsing `a` reached", and
in both the only obstacle is that the parser threads a character
POSITION so an error can say where it happened. Positions inside `b`
are then offset by `a.length`.

**The reusable fact:** shifting the starting position shifts the
reported position and changes nothing else.

`Shifts f` states it once — running `f` from `pos + d` leaves the same
remaining input and reports `d` more. `skipWs`, `skipToEol`,
`skipComment` and `skipEol` each satisfy it, by ordinary induction on
the input list. `Shifts.comp` composes them, and
`skipWsCommentEol_shifts` is the three-step tail the quad-line loop runs
after every quad.

**`parseQuadLinesAcc_shift` is the payoff.** The whole quad-line loop
shifts: fuel and the dataset are untouched, and only the reported
position moves. It takes the quad reader's own shift property as an
explicit HYPOTHESIS (`QuadReaderShifts`) rather than assuming it, so the
residual for BOTH open issues is now one named lemma about
`readNQuad11` and `readNQuad12` — not an open-ended homomorphism.

**Four traps paid for here, all about `simp` and matches.**

1. `Shifts` is a DEFINITION, so `simp` cannot use `skipWs_shifts`
   directly. The four `*_shift` corollaries restate the same facts as
   bare equations, which is the form `simp` needs. Without them the
   rewrite silently does not fire and the `split` that follows splits on
   an un-rewritten scrutinee.
2. `rw` will not rewrite the SCRUTINEE of a match. The quad step is
   `match mode with | .rdf11 => readNQuad11 pos cs | …`, so the proof
   has to `cases mode` first and let the match reduce; a hypothesis
   stated over `(match mode with …)` applied to arguments does not match
   the goal's `match mode with … applied` form either.
3. `split` on `match step with | .error … | .ok …` numbers its cases in
   DEFINITION order, so `h_1` is the error case. Writing the branches in
   the other order gives an inaccessible `ParseError` where a `Nat` was
   expected, which is a confusing way to learn the ordering.
4. A recursive call that looks like it should unify and does not is
   usually carrying the wrong ARGUMENT, not the wrong shape: the ok
   branch continues with `addQuad ds t g`, not `ds`, and passing `ds`
   produced a page of unification output about positions that were
   already correct.

**Coverage is unchanged at 198 of 220.** This module is scaffolding for
two ports, not a port of its own — there is no F\* module named
`LexShift`. Counting it would be inventing coverage.

---

## `Cottas/BaseWriterPrims.lean` — layer 1 of `RDF.CottasStore.BaseWriter`

The F\* module is the native writer for the COTTAS base Parquet file.
Its banner says why it exists: until it landed, store creation and
compaction shelled out to pycottas/DuckDB and only the delta log had a
native writer. Iron rule 11 puts the byte assembly in the formal source
— `serialize_cottas : list cottas_quad -> Tot (list u8)` — leaving the
OCaml side with an atomic write and nothing else.

This layer is the bottom of it: zigzag, LEB128, little-endian integers,
bit widths, bit packing, padding.

**An encoder is only correct against a decoder**, so where the Lean
tree carries the decoder the round trip is PROVED rather than checked:
`zigzagDecode_encodeNat` and `zigzagDecode_encodeInt` for both zigzag
forms, `uvarintDecode_encode_small` for the single-byte LEB128 case.

**The polarity that matters.** LEB128 sets the high bit on every byte
EXCEPT the last: the high bit means CONTINUE. HDT's VByte in
`Storage/Bytes.lean` sets it on the LAST byte instead. Both formats
live in this tree and differ by exactly that bit. Getting it backwards
decodes every multi-byte number wrongly while single-byte values keep
working, which is the failure mode that survives casual testing.
`uvarintDecode_encode_small` and `uvarintEncode_single_byte` are proved
at exactly that boundary, and `#guard` pins 127, 128, 16383 and 16384.

**What is checked rather than proved.** The general multi-byte LEB128
round trip needs a bound of the form `n < 128 ^ (fuel + 1)` threaded
through the recursion. That is its own piece of work, and the module
says so rather than leaving the reader to infer it from the absence of
a theorem. The bit-packing side is checked too, because its decoder is
in `Parquet.Footer`, which is not ported.

**A `sorry` was written and removed rather than landed.** The first
draft of the general round trip left a `sorry` in the multi-byte case.
It is deleted, not weakened and not admitted: the repo policy is no
`sorry`, and a theorem that cannot be proved yet is a `#guard` plus a
sentence saying so.

**Status.** `RDF.CottasStore.BaseWriter` stays NOT covered — this is
one layer of about five (Thrift field writers, the
DELTA_LENGTH_BYTE_ARRAY encoder, dictionary encoding, the Parquet page
and metadata builders). Coverage stays 198 of 220.

---

## `Cottas/BaseWriterThrift.lean` — layer 2 of `RDF.CottasStore.BaseWriter`

Parquet's file metadata is a Thrift struct in the COMPACT protocol, so
every field the writer emits goes through one of these. Each has a
matching read in `Parquet.Footer`, and the F\* source names the decoder
next to each writer.

**Fifteen is the boundary in two rules, and it lands on opposite
sides.** A FIELD header is one byte when the id is 1 to 15 more than
the previous one — a delta of exactly 15 still fits. A LIST header is
one byte for a count BELOW 15 — a count of exactly 15 does not fit and
moves to a plain varint after a `0xF_` byte. Reading the two as the
same rule is the mistake `fieldHeader_short_at_15`,
`fieldHeader_long_at_16` and `listHeader_long_at_15` exist to catch,
with `#guard`s on both at once.

**Zigzag or plain, per field.** `i32` and `i64` values are ZIGZAG
varints. A binary field's LENGTH is a PLAIN varint, and so is a
long-form list count. Mixing them produces values that are right only
when they are zero, which is exactly the kind of defect a small test
misses.

**The issue this layer must not reintroduce.**
<https://github.com/danbri/factoidal/issues/445>: a binary field's
length prefix is the UTF-8 BYTE length, never the codepoint count. The
two coincide for ASCII, which is why the original defect survived. The
Lean writer takes `s.toUTF8.toList.length`, and a `#guard` on `"é"`
pins the case where the two differ — one codepoint, two bytes.

**Status.** `RDF.CottasStore.BaseWriter` stays NOT covered: two layers
of about five. Coverage stays 198 of 220.

---

## `Cottas/BaseWriterColumn.lean` — layer 3 of `RDF.CottasStore.BaseWriter`

The column encoders. The F\* banner explains the format choice:
DELTA_LENGTH_BYTE_ARRAY for every column, not RLE_DICTIONARY, because
DLBA is correct for ANY cardinality and is the simpler encoder to get
bit-exact on a first pass. Dictionary encoding for the low-cardinality
columns is a size optimisation, not a correctness requirement.

**`min_delta` is the TRUE block minimum, and that is not a detail.** A
longer value followed by a shorter one gives a NEGATIVE delta.
Subtracting the true minimum is what makes every adjusted value
non-negative so it can be bit-packed at all; encoding `min_delta = 0`
would produce a value the packer cannot represent.
`dlbaDeltas_negative_when_shrinking` exhibits the shrinking case as a
theorem rather than leaving it to a reader to imagine.

**Two adjacent header fields, two different encoders.** `first_value`
is zigzagged as a NAT, `min_delta` as an INT. They sit next to each
other in the block header, and using one encoder for both is right only
when the value is zero.

**`packedBits_whole_bytes`** says the packed bit list is a whole number
of bytes: the values are padded to `miniblocks * 32` and each
contributes `bitWidth` bits, so the total is a multiple of 8 whatever
the width. That is what lets `packBitsToBytes` consume the list exactly,
with no leftover — the function's own precondition, now proved rather
than assumed by every call site.

**The definition-level section is always one run.** Every row's term is
present — a default-graph quad stores the `DEFAULT` sentinel, never a
Parquet null — so it is one RLE run of `value_count` copies of level 1
behind a little-endian 32-bit length. The empty case is genuinely empty
rather than a zero-length run, which a reader would otherwise try to
decode.

**A guard caught a mistake in its own expected value.** The first
`defLevelSection 3` check expected `[3, 0, 0, 0, …]`, reading the
32-bit prefix as the VALUE count. It is the BYTE length of the run
section, which is 2. The check failed at build time and the expected
value was corrected — which is the point of pinning bytes rather than
lengths.

**Status.** `RDF.CottasStore.BaseWriter` stays NOT covered: three
layers of about five, with dictionary encoding and the Parquet page and
metadata builders left. Coverage stays 198 of 220.

---

## `Cottas/BaseWriterDict.lean` — layer 4 of `RDF.CottasStore.BaseWriter`

Dictionary encoding, and the choice between it and DLBA. The predicate
and graph columns of a COTTAS file repeat heavily, so RLE_DICTIONARY is
much smaller for them; the F\* source keeps BOTH encoders and picks per
column by MEASURING, which is the only way to be right for a column
whose cardinality is not known in advance.

The pipeline is: values, sort, dedup, index, per-row lookup through a
balanced tree, maximal runs.

**Dedup only works on a SORTED list, and that is now a checked fact.**
`dedupSortedStr` compares adjacent elements and nothing else, so on
unsorted input it silently keeps duplicates — and a dictionary with
duplicates gives two indices for one value, which no reader can detect.
`dedup_unsorted_keeps_duplicates` exhibits exactly that, as a theorem
rather than a warning in a comment.

**`groupRuns` collapses ADJACENT equal indices only**, which is what
RLE means. `groupRuns_nonAdjacent_stays_split` pins `[1, 2, 1]` staying
three runs against `[1, 1, 1]` becoming one.

**Three places in this writer put the two varint kinds side by side.**
A run header is `(run_length << 1) | 0` as a PLAIN varint; a Thrift
binary length is a PLAIN varint; an `i32` value is a ZIGZAG one. And a
PLAIN dictionary entry is neither — it is a little-endian 32-bit
length, the opposite of DLBA's varint length block. Each is `#guard`ed
with its own bytes.

**The measurement goes both ways.** `encodeColumnChooseSmaller` builds
both encodings and keeps the shorter, and `#guard` covers a repeating
column choosing the dictionary AND an all-distinct column choosing
DLBA, so the comparison cannot silently become a constant.
`encodeColumnChooseSmaller_is_one_of` says the answer is always one of
the two the sizer built.

**A banned tactic, caught and removed.** One theorem was first written
with `native_decide`, which this tree forbids. The kernel does not
reduce `String` comparison, so `decide` cannot close it either — so the
fact is a `#guard` with a sentence saying why, not a theorem with an
escape hatch.

**Status.** `RDF.CottasStore.BaseWriter` stays NOT covered: four layers
of five, with the Parquet page, schema, row-group and file-metadata
builders left. Coverage stays 198 of 220.

---

## `Cottas/BaseWriterFile.lean` — layer 5 of `RDF.CottasStore.BaseWriter`

The Parquet file structure: page headers, schema, column metadata and
chunks, row groups, file metadata, and the whole-file assembly.

**The layout, as a theorem.** A Parquet file is
`PAR1 | pages | metadata | metadata length (LE u32) | PAR1`. The
trailing length comes BEFORE the closing magic, and that is what lets a
reader seek to the metadata rather than scan for it.
`serializeCottas_shape` states the five parts in order, because a file
that loses either magic or the length is unreadable by any tool rather
than subtly wrong.

**Offsets are cumulative, and that is the part that breaks.** Each
column chunk records where its data page starts. `buildRowGroup`
threads a running offset through the four columns and hands the next
one out; `buildRowGroups` chains that across row groups starting at
`magicHeader.length`, because the pages begin after `PAR1`, not at
zero. An offset short by those four bytes gives a file every byte of
which is correct except where it says the data is.
`magicHeader_length` and `rowGroup_nextOffset` pin both halves.

**Two schema details found by cross-checking, not by reasoning.** The
F\* source records both, and both are `#guard`ed here so a later
tidy-up cannot drop them as redundant:

* A schema leaf carries `converted_type = UTF8` (field 6). Without it
  DuckDB presents the column as BLOB rather than VARCHAR — found by a
  `parquet_scan` cross-check.
* Field 1 of the file metadata stamps 445, not the Parquet-conventional
  1, so the reader can reject a store this writer did not produce. An
  owner decision at
  <https://github.com/danbri/factoidal/issues/445>: no migration path,
  no back-compatible reader.

**Two Lean traps.** `meta` is a reserved token, so the row-group
record's field is `metaBytes`. And `String.toUTF8` does not reduce in
the kernel, so `magicHeader` is a literal byte list with a `#guard`
tying it back to `"PAR1"` — a computed form makes every fact about the
header uncheckable at build time, which is how the first draft ended up
unable to prove that four bytes are four bytes.

**Status, from a definition-level audit.** 124 F\* names, 61 unmatched
by spelling. Most resolve as renames or as accumulator variants the
Lean port folds into their non-accumulator forms. Twenty do NOT: the
eight writer-v2 builders that actually EMIT an RLE_DICTIONARY page
(layer 4 has the sizing and the choice; layer 5 wires only the v1 DLBA
path into `serializeCottas`), `build_dictionary_page_header`, and
eleven hex round-trip lemmas about the version field.
`RDF.CottasStore.BaseWriter` therefore stays NOT covered, and coverage
stays 198 of 220.

---

## `Cottas/BaseWriterFileV2.lean` — layer 6, and `RDF.CottasStore.BaseWriter` complete

Layer 5 wired the v1 path, which writes DELTA_LENGTH_BYTE_ARRAY for
every column. The F\* banner records what that cost:

> v1 always writes DELTA_LENGTH_BYTE_ARRAY: correct for any cardinality
> but pays the full string bytes on every row, every column, even for
> p/g whose whole point is massive repetition.

v2 adds the RLE_DICTIONARY emit path and closes a roughly sixty-fold
size premium against pycottas.

**Two columns are FORCED, two are measured, and the asymmetry is the
design.** `p` and `g` repeat by construction — the graph column is
mostly one `DEFAULT` sentinel — so measuring them would only confirm
the obvious. `s` and `o` can be all-distinct, and then the dictionary
is bigger. `rowGroupV2_forces_p_and_g` states the forcing so it cannot
be tidied into "encode every column the same".

**The offset field that is two fields.** A dictionary-encoded chunk
carries field 9 (the DATA page) and field 11 (the DICTIONARY page). The
dictionary comes first, so field 11 is the chunk start and field 9 is
that plus the dictionary page length. The F\* source records this as bug
history: a reader treating them as one offset reads the index stream as
if it were the dictionary. A DLBA chunk has no field 11 at all, which
is why these are two builders rather than one with a flag, and
`columnMetadataV2_dlba_delegates` says the DLBA case calls the v1
builder unchanged.

**A `#guard` that asserted something false.** The first draft claimed
v2 is smaller than v1, full stop. It is not: on a two-row file of short
strings the dictionary page's own header outweighs the saving. The
check now runs BOTH ways — smaller on eight repeating rows of long
strings, and NOT smaller on the two-row case — so the claim in the
module is the one that is true.

**A vacuous theorem, caught and replaced.** `chunkStart + dictPageLen ≥
chunkStart` is true whatever the hypothesis says, and Lean's unused-
variable warning is what exposed it (hazard #29). It is replaced by
`columnMetadataV2_dlba_delegates`, which says something a later edit
could break.

**Coverage IS claimed, from a definition-level audit.** 124 F\* names,
53 unmatched by spelling, every one resolved by hand: 25 accumulator
variants folded into their non-accumulator forms (the F\* accumulators
exist for OCaml stack safety, which Lean core's `@[csimp]` rewrites
handle — finding A11), 10 renames or stdlib substitutions, 4 per-column
projections that are `rows.map (·.s)` in Lean, and 14 `lemma_*` hex
round-trip lemmas that have no Lean counterpart BY DESIGN — their
subject is `Parquet.Footer`'s hex-string reader, the layer finding A4
is about, and the Lean tree reads bytes rather than hex. The byte-level
fact those lemmas establish is `#guard`ed here.

The audit and its reasoning are written into the alias in
`tools/lean-port-gap.py`, so the claim is checkable rather than
asserted. Coverage 198 to 199 of 220.

## RDF.CottasStore, layer 1 — the handle and the dictionary boundary

`Cottas/OnDiskStore.lean` ports the part of `RDF.CottasStore` that needs
no file: the handle record, the canonical dictionary keys, the
term/token conversions in both directions, and the predicate-presence
and named-graph answers the handle gives from its own fields.

**Ten `assume val`s, and what each became.** Two are real I/O
(`cottas_ondisk_open`, `cottas_ondisk_close`) and are not in this layer.
The other eight are the two directions of one dictionary
(`ondisk_id_to_*_token_global`, `ondisk_lookup_*_id_global`), assumed in
F\* only because a lazily-opened handle keeps its assoc-lists empty and
the OCaml runtime answers from a hash table. They are now the fields of
`TokenTables`, taken as a parameter.

The F\* source states the correctness requirement as a comment:

> "Soundness: the assume-val outcome must be observably equivalent to
> `revmap_lookup h.coh_*_raw_revmap tok` on a fully-populated handle."

Nothing in F\* can check that — an `assume val` has no body to compare
against. Here it is `TokenTables.AgreesWith`, `tablesOfHandle` is the
instance that satisfies it, and `buildQpRow_agrees` is the consequence:
under agreement the fast path and the assoc-list path build the same
row.

**One finding.** `idToRawToken` and `idToRawTokenViaGlobal` are the same
id→token step by two routes, and they DIVERGE out of range.
`idToRawToken` returns the `\x00`-prefixed sentinel, which matches no
row, so the query returns nothing. `idToRawTokenViaGlobal` returns
`none`, which `cellMatch` reads as NO CONSTRAINT, so the query returns
every row on that column. Opposite answers, and neither signature says
so. Every F\* caller short-circuits an unresolvable bound before this
point, so it is not live today.
`idToRawTokenViaGlobal_outOfRange_differs` states it so a later edit
meets a theorem instead of rediscovering it.

Proved: `listNth_eq_getElem?` (the engine's index helper is the standard
one), `namedGraphsAux_nth` (a graph's reference IS its dictionary
position), `graphCellMatch_default` (a default-graph bound matches the
`"DEFAULT"` cell and nothing else — issue 267's fix as an iff),
`idToRawToken_outOfRange`, `tokenToSubject_partial_falls_back` (a cell
with a trailing byte is a rejection, not a truncation).

Not yet ported: the row-group filters and counts, the row-group and
candidate walks, and the public search/estimate/count entry points.
Coverage is NOT claimed for `RDF.CottasStore` yet.

## RDF.CottasStore, layer 2 — the row-group filters and counts

`Cottas/OnDiskFilter.lean` ports the five near-identical walks over one
row group: `filter_zipped_rows_seq`, `filter_zipped_rows_tok_seq`,
`count_zipped_rows_seq`, `filter_zipped_rows` and `count_zipped_rows`.
The F\* comments state three relations between them — "identical match
logic", "same as `filter_zipped_rows` but counts only", "legacy
list-shape filter retained" — and nothing checks any of them. Five
near-identical recursions is the shape where an edit lands in four.

Proved: `countSeq_eq_filterTokSeq_length_start` (the count IS the length
of the filter's answer), `filterSeq_eq_map_filterTokSeq_start` (the
reference-shaped filter is the token-shaped one with `buildQpRow`
mapped over it), `countList_eq_filterListTok_length` and
`filterList_eq_map_filterListTok` (the same pair for the list shape),
`filterTokSeq_sound` (every row returned matches all four bounds).

**A wrong claim caught before landing, and how.** The first draft's
header warned that the indexed and list shapes recover differently from
a misaligned row group: the indexed walk skips a short column's index
and CONTINUES, the list walk stops dead. Its evidence was a pair of
`#guard`s — a three-cell column for one shape against a one-cell list
for the other. That is two functions on two different inputs, which
cannot show a difference between the functions.

The claim is false. A column's size is fixed, so `i < c.size` is
monotone in `i`: once any column is exhausted the indexed walk skips
every remaining index, so it contributes rows for exactly the indices
below the shortest column, which is the set the list walk reaches.
`filterTokSeq_eq_filterListTok_start` proves the two shapes return the
same list when the indexed walk is given `rowGroupRowCount` — misaligned
row group included. The `#guard`s now compare the two shapes on ONE
input.

Coverage for `RDF.CottasStore` is still NOT claimed: the row-group and
candidate walks and the public search/estimate/count entry points remain.

## RDF.CottasStore, layer 3 — the walks over row groups

`Cottas/OnDiskWalk.lean` ports the row-group loops. The F\* source has
two ways of choosing which row groups to visit — a contiguous range
driven by fuel, and an explicit candidate list from
`plan_candidate_rgs` — and about a dozen near-identical recursions
across search, estimate, token-shaped, cached and global variants.

The column read is I/O (`pcache_decode_in_row_group` and its global and
table-indexed siblings, `assume val` underneath). `ColumnReader` is that
read taken as a parameter: row-group index and column index to an
optional column.

Proved: `allRgs_eq_range` (the F\* count-up-then-reverse loop is
`List.range`), `walkRange_eq_walkCandidates` (the unpruned range scan
and the candidate walk over every row group are one walk — the
assumption the whole pruning design rests on, since if they disagreed
then turning pruning on would change results rather than only time),
`walkRangeCount_eq_length` and `walkCandidatesCount_eq_length`,
`walkCandidatesTok_sound` (layer 2's per-row-group soundness carried
through the loop).

**Fuel is observable, not decoration.** The F\* range walk stops when
either the fuel or the row-group count runs out. Lean does not need the
fuel to terminate, so a port could drop it — but a caller passing fuel
below the row-group count gets a partial scan with no error, which the
`#guard`s now pin.

⚠️ **Filed rather than fixed:** a row group whose columns fail to decode
is skipped and the walk continues, so a corrupt row group and an empty
one give the same answer and no caller can tell them apart. The F\*
comment says "skipped (silently empty)". Transcribed as-is, exhibited by
a `#guard`, and raised for a decision at
<https://github.com/danbri/factoidal/issues/571> — changing the recovery
is a behaviour change on the shipping query path, not a refactor.

Coverage for `RDF.CottasStore` is still NOT claimed: the LIMIT-pushdown
walks, the candidate planning, and the public search/estimate/count
entry points remain.

## RDF.CottasStore, layer 4 — LIMIT pushdown

`Cottas/OnDiskLimit.lean` ports the second family of walks, the one a
`LIMIT`-bearing query uses: `filter_zipped_rows_limited_tok_seq`,
`walk_candidate_rgs_search_limited` and their siblings.

`RDF/StoreCapabilities.lean` already states the law such a path must
satisfy — `StoreCapsLawful.limitAgrees`, "a limited read returns the
prefix the unbounded read would have returned" — and nothing in the F\*
tree connects the limited family to the unlimited one at all.
`walkCandidatesLimitedTok_prefix` is that connection: the limited
walk's answer, flipped into row order, is the unlimited walk's answer
flipped and truncated. Early exit is a refinement of the full scan, so a
`LIMIT` query cannot return a row the unlimited query would not, nor
stop before it has `limit` of them.

Supporting results: `filterTokSeq_append` and `walkCandidatesTok_append`
(a walk started from a non-empty accumulator appends to it and never
inspects it), `filterLimitedTok_count` (the count the F\* walks carry
alongside the list IS the list's length, so it is not a second source of
truth an edit can desynchronise), `filterLimitedTok_flag` (the early-exit
flag holds exactly when the count reached the limit — the fact that
makes the walk's stop branch and its recurse branch agree).

**A branch that decides nothing.** The F\* end-of-row-group arm returns
`(acc_rev, acc_count, acc_count >= limit)`, but that arm is reachable
only when the same test already failed one guard earlier, so the flag it
computes is always `false`. Transcribed as written; `filterLimitedTok_end`
states that the computation is dead. Deleting it would be a change to
the F\* source, which this port does not make.

Every statement here is about the FLIPPED list. Both families accumulate
in reverse, and stating the prefix property on the accumulator instead
would turn "the first `limit` rows" into "the last `limit` rows".

Coverage for `RDF.CottasStore` is still NOT claimed: candidate planning
(`plan_candidate_rgs`, the dictionary cache, the compound predicate-object
prune, the subject-range prune) and the public search/estimate/count
entry points remain.

## RDF.CottasStore, layer 5 — candidate-row-group planning

`Cottas/OnDiskPlan.lean` ports `plan_candidate_rgs` and everything under
it: the dictionary cache and its populate loop, `list_string_mem`, the
per-column candidate computation, and the sorted merge intersection.
The dictionary-page read is I/O and becomes `DictReader`, a parameter.

**"Never wrong answers", as a theorem.** The F\* source states the
safety rule twice in comments — a row group absent from the dictionary
cache is INCLUDED, a "safe fallback that may cost a wasted data-page
decode, never wrong answers". That is the claim the entire pruning
design rests on, and the one a later edit is most likely to break, since
making the planner one notch more selective looks like a pure speed win
right up until it drops a row group that held a match.
`planCandidateRgs_complete` proves it under one hypothesis,
`DictReaderSound`: a dictionary page, when present, lists every token its
column holds in that row group. It may list more, and it may be absent;
it may not omit. That is the Parquet dictionary-page contract, and
stating it rather than assuming it is what makes the conclusion
checkable.

**Two facts the F\* source needs and does not establish.**

1. `list_nat_intersect_sorted` is a merge, so it is correct only on
   ascending inputs — unsorted inputs silently drop elements. Nothing in
   the F\* tree says its inputs are sorted.
   `computeCandidateRgs_eq_filter` proves the per-column planner IS
   `(List.range rgCount).filter`, which gives sortedness for free
   (`computeCandidateRgs_sorted`).
2. The planner intersects REPEATEDLY, so the second intersection's left
   input is a previous intersection's output.
   `intersectSortedRgLists_sublist` proves the result is a sublist of the
   left input, so sortedness survives the chain. Without it the merge is
   being fed something it is only correct on by accident.

`planCandidateRgs_unbounded` closes the loop with layer 3: with no bound
on any column the plan is every row group, which
`walkRange_eq_walkCandidates` already showed is the unpruned scan.

Only completeness of the intersection is proved, not soundness. That is
deliberate: dropping a needed row group is a wrong answer, keeping an
unneeded one is a wasted decode. The safety claim needs the first.

Coverage for `RDF.CottasStore` is still NOT claimed: the compound
predicate-object prune, the subject-range prune, and the public
search/estimate/count entry points remain.

## RDF.CottasStore, layer 6 — the public entry points

`Cottas/OnDiskSearch.lean` ports `cottas_ondisk_search_tok`,
`cottas_ondisk_search_limited_tok`, `cottas_ondisk_estimate_tok`, the
bound builder and the row-to-quad conversions. The store's I/O surface
becomes `StoreIo`, one record.

`searchTok_eq_fullScan` is what every layer below was for: under prunes
that only drop row groups holding no match, the pruned search returns
exactly what an unpruned scan of every row group returns. `PruneSound`
names the property a future prune has to satisfy, and nothing else about
it has to be re-argued. Supported by `walkCandidatesTok_sublist_eq`,
which is where `Nodup` earns its place — it is what rules out a skipped
row-group index reappearing later in the candidate list.

Also proved: `searchTok_sound` (soundness survives the entry point) and
`searchLimitedTok_prefix` (LIMIT at the entry point is the unlimited
search truncated).

The compound predicate-object prune and the subject-offset prune are
modelled as opaque `List Nat → List Nat` parameters rather than
transcribed. That is deliberate: `compound_po_dict_encode` resolves ids
through the `.p.dict` sorted-rank id space, NOT through
`ondisk_lookup_*_id_global`'s first-occurrence-order space, and the F\*
source documents at length that mixing them prunes the one row group
holding the pair — a wrong zero, not a slow query. Keeping the prune
opaque keeps that choice outside the port instead of transcribing an
id-space confusion into a second tree.

## RDF.CottasStore, layer 7 — exact counting, distinct predicates, the subject-range prune

`Cottas/OnDiskCount.lean`.

⚠️ **The selective exact-count is not the full count.**
`count_selective_matches_seq` was added so `COUNT(*)` over `{ ?s a ?o }`
stops decoding the subject and object columns it never reads. The F\*
source presents it as the same quantity computed cheaper. The full count
requires all four cells to decode before counting a row; the selective
count requires only the graph cell, because `bound_col_match` on an
absent bound returns `true` without inspecting anything. A row with a
null in an UNBOUND column is therefore counted by one and dropped by the
other. `countSelective_eq_countSeq` proves the equality under the
conditions that make them agree — four columns of equal length, every
cell present — and a `#guard` pair exhibits the divergence on a row that
violates the second. Raised at
<https://github.com/danbri/factoidal/issues/572>.

`collectDistinct_none_of_missing` states the opposite recovery from
layer 3's: one missing dictionary page aborts the WHOLE distinct-predicate
answer rather than contributing zero predicates for that row group. The
F\* banner asks for exactly that, and the contrast with the row-group
walk is deliberate in the source.

**A finding that turned out not to be one.** The subject-range overlap
test reduces, on an empty range `[s, s)`, to `s < cumEnd && cumStart < s`
— true for any row group strictly containing `s`. Checking the caller
before writing that up: `cottas_ondisk_subject_candidate_rgs` returns
`Some []` when the subject's range count is zero, three lines before it
would call the loop. So the loop never sees an empty range, and this is a
caller-enforced precondition, not a defect.
`rangeOverlaps_empty_reports_overlap` records it as such, because the
precondition appears nowhere in the loop's own type.

Two `#guard`s in this module's first draft asserted false things, both
mine: one put a predicate token in the subject bound position, and one
expected the empty-range case to prune to nothing. Both were caught by
the build, and the second is what sent me to read the caller.

## RDF.CottasStore, layers 8 and 9 — selective decode, and the count-exact fast paths

`Cottas/OnDiskSelective.lean` ports the row-index-selective search: it
decodes an unbound column's values only at the indices that already
matched on the cheap columns. The F\* entry point's banner states the
differential gate's premise outright — "identical row/row-group ORDER to
`cottas_ondisk_search_tok` … `need` only changes which UNBOUND columns
get decoded, never which rows match or their order" — and that is two
claims, both proved: `matched_iff_rowSelected` (the selective gate holds
exactly where `rowSelected` returns a row) and
`selectiveRows_need_invariant` (narrowing `need` changes neither the row
count nor the graph values nor the order).

The accumulator in `buildSelectiveRows_graph_invariant` is deliberately
allowed to DIFFER between the two walks as long as it already agrees on
`g`. That generalisation is not decoration: the two walks build rows
whose other three positions genuinely differ, and an induction demanding
identical accumulators cannot get past its own first step.

`Cottas/OnDiskCountExact.lean` ports the last eight definitions: the
predicate- and subject-offset-index fast paths, the eligibility guard,
the summation, the four-way dispatcher, and the selective row's
conversion to a triple. `offsetIndex_paths_disjoint` proves the F\*
comment that justifies trying both fast paths in sequence.
`sumOffsetCounts_none_of_fullScan` proves that one unusable row group
abandons the whole sum, because a partial sum would silently undercount
— the same all-or-nothing discipline as `collectDistinct_none_of_missing`
in layer 7.

**A vacuous theorem, caught and deleted.** A draft of layer 8 carried a
`matchedIndicesSeq_eq_filterTokSeq` whose right-hand side reduced to its
own left-hand side, closed by `rfl`. It proved nothing while reading
like the module's headline result — anti-pattern #29's exact shape, in
its worst form. It was deleted rather than weakened, and
`matched_iff_rowSelected` is the statement that carries the content.

## Coverage: 199 → 200

`RDF.CottasStore` is now covered, and the alias in
`tools/lean-port-gap.py` carries the audit method beside the result.
Every one of the 125 names matched by
`^(let (rec )?|and |assume val |noeq type |type )` was resolved BY HAND.
A name-shape pre-pass matched 51 of the 125; that number is recorded as
evidence about the PASS, not about the code (hazard #28). The count
moved by exactly one module and by exactly 2,825 lines, which is this
module's own length — no other classification shifted.

Remaining: 3 engine (`Parquet.Footer`, `RDF.NQuads.Streaming`,
`SPARQL11.Parser.AskBgpRoundTrip`), 3 proof, 14 by design.

## SPARQL11.Parser.AskBgpRoundTrip — the theorem F\* calls impossible

`SPARQL/AskBgpRoundTripString.lean` proves
`askBgp_string_roundtrip`: printing a query in the ASK-BGP fragment and
tokenizing the result gives back exactly the tokens the query denotes.

The F\* module reaches this statement and stops. Its banner marks stage
(a) IMPOSSIBLE and proves the impossibility with a counter-probe: in that
ulib snapshot `FStar.String.sub` exposes a length refinement and nothing
relating its output characters to its input, so no lemma can be STATED
connecting a printed payload back to the token's extract — which blocks
every payload-carrying token, not just this fragment's.

The Lean lexer scans `List Char`. `scanIriBody` and `scanVarName` have
ordinary equation lemmas, and the connection is an ordinary induction.
The obstruction was never about RDF or SPARQL; it was one library's
interface to one datatype. Separating those two kinds of fact is what the
two-tree design is for, and this is the clearest case of it so far.

**How the proof goes.** The printed query is cut into chunks, one per
token, each carrying its LEADING separator — forced, because `nextToken`
calls `skipWs` first, so a trailing space would be left unconsumed and
`LexesTo` would be false. `tokenizeLoop_chunks` folds the lexer along
the chunk list; `chunkChars_query` shows the chunks concatenate to the
printed string; `chunksOk_query` discharges the per-chunk obligations.

**And a second defect, from writing the side condition.**
`LexesTo` quantifies over what follows a chunk, so the theorem needs to
say exactly which IRI bodies round-trip. §19.8 [139] admits any body
without `>`, `\`, or a control character. This lexer additionally
requires an acceptable FIRST character, so `<1abc>` — a valid IRIREF —
lexes as four tokens. Both trees carry it, and the committed binary
rejects the query while accepting the same query with an alpha-initial
IRI. Filed as <https://github.com/danbri/factoidal/issues/573>;
`iriFirstOk` is the honest side condition until it is fixed, and a
`#guard` pins that the engine really does mis-lex the case.

Neither this defect nor issue 572 came from running a test. The test
corpora contain no digit-initial IRI. They came from having to state a
theorem precisely enough to prove it.

## Coverage: 200 → 201

Engine modules 3 → 2, lines down by exactly 852 — this module's own
length. Remaining: 2 engine (`Parquet.Footer`, `RDF.NQuads.Streaming`),
3 proof, 14 by design.

## Parser locality — the wall both trees hit, and a coverage entry that was wrong

`Syntax/Locality.lean` starts the Lean counterpart of
`Parser.NTriples.Locality`, and its landing corrects a defect in
`tools/lean-port-gap.py`.

**The tooling defect.** `Parser.NTriples.Locality` was classified
by-design — "no Lean counterpart because the reason it exists is absent
in Lean" — and it was the ONLY entry in that set with no reason recorded
beside it. Every other one carries its argument. This one could not,
because the argument is false.

The F\* module's banner says why it exists: two theorems,
`theorem_stream_eq_batch` and the N-Triples round trip, both need "a
reader behaves identically on `complete ^ carry` at any position inside
`complete` as it does on `complete` alone", and F\* cannot reach that
cheaply because Z3 has no associativity theory for
`FStar.String.strcat` over symbolic operands.

The Lean tree does not escape that obligation. A list-based reader can
still read past the end of a prefix: `List.span isBnodeChar` stops at
end-of-input on `_:abc` and consumes the `d` on `_:abcd`. So
`readBlankNodeLabel` is NOT local without a stopped-short side
condition, and two `#guard`s exhibit the pair. What differs is the
register — list suffixes rather than byte offsets, so the proofs are
structural inductions — which is a reason the Lean version is smaller,
not a reason it is unnecessary.

Reclassified as PROOF (the module's own header calls it PROOF-ONLY and
it is not in `build-ocaml.sh`), with the argument written down. Coverage
does not move: 201 either way. Only the reason changed, and now there is
one.

**What is proved.** The pilot the F\* program itself chose — the IRI
scanner: `iriEmitAt_local`, `iriEmitAt_ne_close`, and
`iriNextStep_close_local` (a step that closed an IRIREF closes at the
same place on longer input).

**What is not, named.** `iriNextStep_emit_local` and everything above
it: `readIriRefBody`, `readIriRef`, `readBlankNodeLabel`, `readLiteral`,
and the `readNQuad11` composition. Without those,
`RDF.NQuads.Streaming`'s streaming-equals-batch theorem cannot be stated
in this tree either, which is why that module stays uncovered. The emit
case is not blocked on an idea — it is the close case's analysis with
the two escape arms surviving instead of discarded — but it is left
unproved rather than half-proved, because a named gap is checkable and a
weakened theorem is not. Tracked at
<https://github.com/danbri/factoidal/issues/570>.

⚠️ A `#guard` in that module also pins that the step is NOT local when
input runs out mid-escape: `\u00` alone fails, `A` emits. That is
the side condition earning its place in the statement.

## Locality, continued — and a definition of mine that was false

Four more results in `Syntax/Locality.lean`, and a correction to the
module landed one commit earlier.

**The correction.** That landing defined locality with the side
condition "the reader stopped with a non-empty remainder". The
definition is FALSE. `readBlankNodeLabel` pushes a trailing `.` BACK
into its remainder, because §19.8 forbids a label ending in a dot. So on
`_:ab.` it answers `("ab", 4, ['.'])` — remainder non-empty — while its
span still ran to the end of the input. One more character gives
`("ab.c", 6, [])`, a different label.

Measured, not reasoned:

```
readBlankNodeLabel 0 "_:ab."      = .ok ("ab",   4, ['.'])
readBlankNodeLabel 0 "_:ab." ++ "c" = .ok ("ab.c", 6, [])
```

The general lesson is now in the module header: no condition on a
reader's OUTPUT can express "it stopped because of something it saw",
because a reader may hand back characters it chose not to keep. The
condition belongs on the INPUT and is per-reader. `ReaderLocal` is gone;
`BnodeStopsInside` replaced it for this reader, and `readIriRefBody`
turned out to need no condition at all — a successful IRI parse means
the closing `>` was seen.

The proof is what found this. The `droppedList = []` branch would not
close, and the reason it would not close was that the statement was
wrong.

**Newly proved.** `iriNextStep_emit_local` — the gap named in the
previous landing, now closed: the same case analysis as the close case
with the two escape arms surviving instead of discarded, plus the
plain-character arm where the equation compiler leaves `c ≠ '\'` as two
negative facts about the tail rather than one about the head.
`readIriRefBody_local` and `readIriRef_local` — the recursion above it,
via three non-dependent arm equations, because the shipping definition's
`match h : iriNextStep pos cs with` binds the step's own equation for
its termination argument and a dependent match cannot have its scrutinee
rewritten. `span_append_of_stopped` and `readBlankNodeLabel_local`.

**Still open**, and unchanged in kind: the literal, datatype and
language-tag readers, and the `readNQuad11` composition, without which
`RDF.NQuads.Streaming`'s streaming-equals-batch theorem cannot be
stated. <https://github.com/danbri/factoidal/issues/570>.

## Locality, third round — and the wall that stops it

`Syntax/LocalityLiteral.lean` adds `readLangTagRun_local`. That is the
only new result, and the reason is worth recording.

⚠️ **`readStringLiteralBody` cannot be unfolded in this container.** It
has nineteen arms, two of which match on four and eight `hexVal`
scrutinees at once. Any tactic that unfolds it forces those apart.
Measured three ways — functional induction with `simp_all`, a single
`rw` then `simp_all`, and a per-arm `Except.map` helper with `simp only`
— peaking at 10.5 to 12 GB and taking SIGKILL, or timing out while still
climbing. The memory climbs steadily from the start in every case, so it
is the unfolding, not a runaway in one branch.

This is <https://github.com/danbri/factoidal/issues/565> again, one
reader over. That issue was the same shape for `readIriRefBody` — ten
arms, equation generation exhausted memory — and the fix was
`Syntax/IriScan.lean`: a non-recursive step classifier plus a three-arm
recursion whose equations are provable. `readIriRefBody_local` exists
today only because that refactor already happened. Filed as
<https://github.com/danbri/factoidal/issues/574>.

**What that blocks.** `readNQuad11` locality composes from the
sub-readers. Proved so far: `readIriRefBody_local`, `readIriRef_local`,
`readBlankNodeLabel_local` (with `BnodeStopsInside`),
`readLangTagRun_local`, `span_append_of_stopped`. Blocked:
`readStringLiteralBody`, `readStringLiteralQuoted`, hence `readLiteral`,
`readObject11`, `readNQuad11`, hence
`RDF.NQuads.Streaming`'s streaming-equals-batch theorem
(<https://github.com/danbri/factoidal/issues/570>).

`readDatatype_local` is not blocked in principle — it delegates to
`readIriRef`, already proved — but it is downstream of the literal
reader in the only composition that needs it, so landing it alone would
be a lemma with nothing to feed. It goes in with the rest once 574
clears.

**Why the module is split.** `LocalityLiteral.lean` exists for a build
reason, not a conceptual one: the elaboration above was heavy enough to
kill `Syntax.Locality` when attempted inside it.

## The string-literal reader, split — issue 574 cleared

`readStringLiteralBody` is now a non-recursive step (`strLitNextStep`)
plus a three-arm recursion, the shape `Syntax/IriScan.lean` gave the
IRIREF body for
<https://github.com/danbri/factoidal/issues/565>. This clears
<https://github.com/danbri/factoidal/issues/574>.

**Why it was needed.** As one nineteen-arm recursion, unfolding this
reader forced apart the `\u` and `\U` arms' four- and eight-way `hexVal`
matches. Measured at 10.5 to 12 GB before SIGKILL, three ways. Split, the
step-locality lemma proves in seconds.

**How it is gated.** The committed nineteen-arm definition is kept as
`readStringLiteralBodyLegacy`, a private differential oracle with no
callers, and 27 `#guard`s compare the two across every arm: plain text,
immediate close, text after the close, all eight ECHARs, both UCHAR
forms, bad hex, truncated escapes, an unknown escape, a trailing
backslash, a surrogate codepoint, raw newline and carriage return, and
unterminated input. Three further guards pin decoded VALUES, so the
table is not merely self-consistent.

⚠️ Both sides are compared through `toOption`, so a difference in an
error MESSAGE would not be caught — the failing arms are pinned by both
sides agreeing on `none`, not on which error. That is stated next to the
table.

The oracle should be deleted once the table has run green for a while,
the same lifecycle the IRIREF swap used.

**What the split cost, and what repaid it.** The recursion is now on
`cs.length`, so it no longer reduces by `rfl` — eleven concrete
`rfl` proofs in `SyntaxTheorems.lean` had to be redone. Three arm
equations (`readStringLiteralBody_close` / `_fail` / `_emit`) plus nine
literal-shaped `@[simp]` lemmas restore the property, and the two UCHAR
theorems and the surrogate-rejection theorem now go through the arm
equations explicitly. Those equations are the point: the nineteen-arm
version had NO usable equations, which is what 574 was.

**Gate.** `lake build` green at 850 jobs. W3C suites through the changed
lexer: N-Triples 70 pass, 0 fail (out of 70); N-Quads 87 pass, 0 fail
(out of 87); Turtle 313 pass, 0 fail (out of 313).

## String-literal locality, and the hex4 / hex8 factoring — 2026-08-24

`Syntax/LocalityLiteral.lean` now carries the string-literal reader's
locality, which the module header used to say was blocked. A reader is
LOCAL when a run that stopped inside its input answers the same on
longer input, with the remainder grown by exactly what was appended.
That is what a streaming N-Quads fold needs from every reader: a chunk
boundary must not change how the text before it parses.

Proved, all with axioms `[propext, Classical.choice, Quot.sound]` or
less, no `sorry`, no user `axiom`, no `native_decide`:

* `strLitNextStep_emit_local`, `strLitNextStep_close_local`
* `readStringLiteralBody_local`, `readStringLiteralQuoted_local`
* `readLangTagRun_local` (kept, unchanged)

### What was in the way, and what moved it

The step/recursion split landed earlier cleared
<https://github.com/danbri/factoidal/issues/574> for the RECURSION. It
did not clear it for the STEP. `strLitNextStep`'s `\u` arm matched on
four `hexVal` results at once and its `\U` arm on eight, so a proof
that reached those arms split into 16 and 256 cases, with the other
seventeen arms already split around them. `simp_all` over that reached
10.5-12 GB and took SIGKILL.

`hex4` and `hex8` (in `Syntax/Lexing.lean`) decode the digits into one
`Option Nat`, so each arm now splits two ways. The refactor changes no
behaviour, and the check on that is the `#guard` table already in the
file: 27 inputs run through both the split reader and
`readStringLiteralBodyLegacy`, at build time. ✅ Build green at 850
jobs with the table in it.

The second obstacle was not memory. Lean's equation compiler turns
overlapping patterns into a case tree, so an arm reached only because
the earlier arms failed does not carry those failures as hypotheses:
the plain-character arm gives `c` and `rest` and nothing saying `c` is
not a quote. `strLitNextStep_plain` and `strLitNextStep_badEscape`
state the guards and prove them by `unfold` then `split`. `grind`
closes the case `simp_all` leaves, because it instantiates a
hypothesis carrying binders.

### Gate

✅ Lean W3C runner, re-measured after the change:

* N-Triples 70 pass, 0 fail (out of 70)
* N-Quads 87 pass, 0 fail (out of 87)
* Turtle 313 pass, 0 fail (out of 313)

### What this does not yet reach

`RDF.NQuads.Streaming` (3,438 F\* lines) is still not covered. The chain
from here is `readDatatype` -> `readLiteral` -> `readObject11` ->
`readNQuad11` -> the restart lemma for `parseQuadLinesAcc` -> the
stream-equals-batch theorem.

⚠️ `readLiteral` will carry side conditions, and they are real, not
bookkeeping. In RDF 1.1 mode the reader branches on what follows the
closing quote: `@` starts a language tag, `^^` starts a datatype,
anything else ends the literal as `xsd:string`. If the remainder after
the quote is empty, or is exactly `['^']`, then appending text CHANGES
which branch fires. The theorem must exclude those two shapes. Both are
excluded in practice by the line terminator, which is why the streaming
use is not blocked by them.

Worth recording about the F\* side: `RDF.NQuads.Streaming` does not
prove reader locality at all. It takes `line_witness` values as
hypotheses and shifts them with `lemma_*_shift`, because
`parse_nquads_acc` walks a `string` with an integer offset and a
restart at an offset needs those shifts. The Lean parser walks a
`List Char`, so a restart is the same function on a suffix, and
locality is provable outright instead of assumed. That is the
differential experiment paying out: the witness machinery is a property
of F\*'s string representation, not of N-Quads.

## Line-level reader locality — 2026-08-24

`Syntax/LocalityLine.lean` carries locality up from the lexical readers
to the pieces a whole statement is built from. Nine theorems, axioms
`[propext, Classical.choice, Quot.sound]` or less, no `sorry`, no user
`axiom`, no `native_decide`:

`skipWs_local`, `readLangTag_local`, `readDatatype_local`,
`readLiteral11_local`, `readBlankNodeLabel_local'`, `readSubject_local`,
`readPredicate_local`, `readObject11_local`, `readGraphLabel_local`.

### The side conditions, and why each one is real

Three exclusions appear, and none is bookkeeping — each names an input
where the reader genuinely answers differently on longer input.

⚠️ **Empty remainder.** A whitespace run or a language-tag run that
reached the end of its input keeps running into whatever is appended.

⚠️ **A remainder of exactly `['.']`.** `readBlankNodeLabel` on `_:ab.`
reads the label `ab` and leaves `['.']`; on `_:ab.c` it reads the label
`ab.c` and leaves nothing. The dot belongs to the label unless something
after it stops the run.

⚠️ **A remainder of exactly `['^']`.** RDF 1.1 `readLiteral` branches on
what follows the closing quote — `@` for a language tag, `^^` for a
datatype, anything else ends the literal as `xsd:string`. One more `^`
turns the third branch into the second.

All three are met by a reader looking at a line that still has its
terminator, which is the case the streaming N-Quads fold needs.

### Guarding against an unsatisfiable hypothesis

Per the discipline that a hypothesis nothing can meet proves nothing,
the module ends with `#guard`s over an ordinary object slot
(`"x" .` plus a newline): the remainder is non-empty, is not `['.']`,
is not `['^']`, and the reader returns the same term, the same end
position and a remainder longer by exactly the appended text. They run
at build time.

### Gate

✅ Build green at 852 jobs, guards included.
✅ Lean W3C runner: N-Triples 70 pass, 0 fail (out of 70); N-Quads 87
pass, 0 fail (out of 87); Turtle 313 pass, 0 fail (out of 313).

### Next

`readOptGraphLabel_local` and `readNQuad11_local`, then the restart
lemma for `parseQuadLinesAcc`, then the stream-equals-batch theorem that
covers `RDF.NQuads.Streaming`
(<https://github.com/danbri/factoidal/issues/570>).

`readNQuad11_local` should need only `rest ≠ []`: the line ends at `.`,
so every intermediate remainder still holds that terminator and meets
the three exclusions above.

## A whole N-Quads statement is local — 2026-08-24

`readOptGraphLabel_local` and `readNQuad11_local` close the reader chain.
Axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`, no user
`axiom`, no `native_decide`.

`readNQuad11_local` carries ONE side condition, `rest ≠ []`, and the
line terminator is what discharges everything else. A statement ends at
`.`; if anything at all follows that dot, then each earlier remainder
still holds it, so none of them is empty, `['.']`, `['_']` or `['^']` —
the four shapes the readers underneath exclude. The proof derives all
eleven of those facts from `rest ≠ []` and the `'.' :: rest` match, then
rewrites the longer run stage by stage.

⚠️ The condition is not bookkeeping. Measured, not reasoned out:

```
<http://a/s> <http://a/p> <http://a/o> _:g.      parses, graph _:g, remainder []
<http://a/s> <http://a/p> <http://a/o> _:g.x     FAILS: expected '.' terminator
```

One more character and the blank-node label swallows the dot, so the
statement loses its terminator. That guard pair is the refutation of
`readNQuad11_local` without `rest ≠ []`, and it is in the module as two
`#guard`s next to two more showing a terminated line grows its remainder
by exactly the appended text.

### Gate

✅ Build green at 852 jobs with all guards.
✅ Lean W3C runner: N-Triples 70 pass, 0 fail (out of 70); N-Quads 87
pass, 0 fail (out of 87); Turtle 313 pass, 0 fail (out of 313).

### Next

The restart lemma for `parseQuadLinesAcc` (fuel monotonicity plus the
per-line locality above), then `splitCompleteLines` and the
stream-equals-batch theorem, which is what covers `RDF.NQuads.Streaming`
(<https://github.com/danbri/factoidal/issues/570>).

## Every reader hands back a suffix — 2026-08-24

`Syntax/LocalitySuffix.lean`. The locality modules say a reader answers
the same on longer input; this one says WHERE the answer sits — the
remainder is a suffix of the input — and `readNQuad11_dot` says more:
the statement's terminating `.` is still findable in the input,
immediately before the remainder.

That last one is what the streaming fold needs. A chunk is cut after its
last newline, so the text handed to the parser ends with a newline. If a
statement's remainder were empty the input would end with the `.`
instead, and `readNQuad11_dot` refutes it. Without that,
`readNQuad11_local` cannot be applied at all, because its side condition
is exactly "the remainder is not empty".

The step functions carry the argument: every arm of `iriNextStep` and
`strLitNextStep` consumes a prefix of fixed length, so the remainder is
`cs.drop w`, and a drop is a suffix. `iriNextStep_emit_drop` and
`strLitNextStep_emit_drop` state that; the rest is transitivity.

⚠️ The blank-node reader is the one place where the suffix is not
immediate. Its trailing-dot branch hands back `'.' :: afterBody`, and
that dot came out of the LABEL rather than out of the input at that
position, so the proof splits the label at its last character to find
it again.

Nineteen theorems, axioms `[propext, Classical.choice, Quot.sound]` or
less, no `sorry`, no user `axiom`, no `native_decide`.

✅ Build green at 854 jobs.

### Next

`parseQuadLinesAcc` fuel monotonicity (a run that already succeeded
cannot notice more fuel), then the line-boundary concatenation lemma
that `Syntax/NQuadsStreaming.lean`'s header names as the one thing
missing, then the homomorphism
`finish (chunks.foldl feedChunk initialState) = parseNQuads (…)`
(<https://github.com/danbri/factoidal/issues/570>).

## Streaming: the offset is threaded, and fuel is independent — 2026-08-24

Two steps toward the homomorphism
`finish (chunks.foldl feedChunk initialState) = parseNQuads (…)`,
which `Syntax/NQuadsStreaming.lean`'s header names as the one thing it
was missing (<https://github.com/danbri/factoidal/issues/570>).

### `StreamState` now carries the absolute offset

⚠️ A change from the F\* design, taken deliberately. `RDF.NQuads.Streaming`'s
`feed_chunk` calls `parse_nquads_acc complete 0` — every chunk restarts
the offset at zero — and pays for it with the `lemma_*_shift` family,
which is a large part of its 3,438 lines.

Two reasons to thread it instead, and the first is a defect the F\*
design has: a parse error in the fifth chunk should name its place in
the DOCUMENT, not in whatever buffer the consumer happened to assemble.
The second is that with the offset threaded, the streaming run and the
batch run hand the same positions to the same readers, so no shift
lemma is needed to compare them.

`NQuadsStreaming` has no consumers outside the library, so the change
is contained. Its 20 build-time `#guard`s, including the three that
split a document mid-line, still pass.

### Fuel independence

`parseQuadLinesAcc11_fuel_indep`: two runs with different fuel agree as
long as each budget exceeds the input length. That is what lets the
streaming run, whose fuel comes from one chunk, be compared with the
batch run, whose fuel comes from the whole document.

The proof needs to know each round consumes at least one character, and
that now follows from the suffix module: `readNQuad11_len` reads it off
`readNQuad11_dot`, since `'.' :: rest` being a suffix of the input makes
`rest` strictly shorter.

ⓘ Stated for `.rdf11`, which is the mode the F\* module's own theorem is
about. The RDF 1.2 reader admits triple terms in the object slot and
needs its own `readNQuad12_dot` before the same argument runs.

### Gate

✅ Build green at 854 jobs.
✅ Lean W3C runner: N-Triples 70 pass, 0 fail (out of 70); N-Quads 87
pass, 0 fail (out of 87); Turtle 313 pass, 0 fail (out of 313).

### Next

Locality for `skipToEol` / `skipComment` / `skipEol`, then the
line-boundary concatenation lemma, then the homomorphism.

## Skip locality, and positions that count characters — 2026-08-24

Two modules, both prerequisites for the line-boundary concatenation
lemma (<https://github.com/danbri/factoidal/issues/570>).

### `Syntax/LocalitySkips.lean`

A chunk handed to the streaming parser ends with a newline. These
lemmas turn that into the side conditions the readers need:

* `span_snd_ne_nil_of_last` — a span stops when the last character
  fails its test, so a whitespace run never runs off the end of a
  chunk;
* `getLast?_of_suffix` — a non-empty suffix keeps the last character,
  so "still ends with a newline" survives every reader;
* `skipToEol_local`, `skipComment_local`, `skipEol_local`.

⚠️ Each locality lemma carries a side condition and each is real. A
`skipToEol` that ran off the end keeps running. A `skipComment` on an
empty input can be turned into a comment by appending a `#`. A
`skipEol` on exactly `['\r']` becomes a CRLF pair when a `\n` arrives.

### `Syntax/LocalityCount.lean`

Every reader's returned position is its starting position plus the
number of characters it took, stated as
`p' + rest.length = pos + cs.length` so `omega` can use it. Eighteen
theorems, from the two step functions up to `readNQuad11_counts`.

This is what makes the streaming module's threaded offset CORRECT
rather than merely plausible. `feedChunk` advances its stored offset by
`complete.length`; these theorems say the parser's own position
advanced by exactly that much. Without them the stored offset would be
an assumption, and a parse error in a later chunk could name the wrong
place — which is the defect the threading was meant to fix.

It is also the Lean counterpart of the F\* module's `lemma_*_shift`
family: both exist so a restart can be lined up with a run that never
stopped. The F\* version shifts byte offsets through `Parser.FastString`;
here the position is a plain character count over a `List Char`.

### Gate

✅ Build green at 858 jobs.

### Next

The concatenation lemma itself: parsing `complete ++ carry`, where
`complete` ends with a newline, equals parsing `complete` and then
parsing `carry` from where it stopped. Every piece it needs is now in
place — per-line locality, the terminator's position, fuel
independence, skip locality, and positions that count characters.

## The line-boundary concatenation lemma — 2026-08-24

`Syntax/NQuadsConcat.lean`. `Syntax/NQuadsStreaming.lean`'s header names
ONE thing as missing: that parsing `a ++ b`, where `a` ends in a
newline, equals parsing `b` from the state parsing `a` reached. That is
the F\* module's `lemma_parse_nquads_acc_concat_line_general`, and the
bulk of its 3,438 lines. `parseQuadLines11_concat` is it.

Axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`, no user
`axiom`, no `native_decide`. ✅ Build green at 860 jobs.

ⓘ Stated in ok-form: it assumes the `complete` half parses. That is the
direction the streaming fold needs, since the fold has already run that
half and holds its dataset.

⚠️ The converse is NOT proved, and it is not free. "If the combined run
succeeds then the `complete` half does" needs the fact that no reader
consumes a raw newline. That is true of this grammar — IRIs forbid raw
control characters, literals forbid a raw newline, and inline
whitespace is space and tab only — but there is no proof of it in the
tree. Without the converse, the streaming parser could in principle
reject a document the batch parser accepts; the ok-form lemma rules out
the other way round, which is the direction that would give a WRONG
dataset rather than an error.

### What each round of the proof needs

The proof walks one round of the parser at a time over four branches
(blank or comment line, LF, CR, statement). Every round needs four
things, and each comes from a module below this one:

* the round answers the same on the longer input — `skipWs_local`,
  `skipComment_local`, `skipEol_local`, `readNQuad11_local`;
* what is left still ends with a newline — `getLast?_of_suffix` over
  the suffix lemmas;
* the position advanced by exactly what was consumed —
  `Syntax.LocalityCount`, which is what makes the two runs line up;
* the remaining fuel is still enough —
  `parseQuadLinesAcc11_fuel_indep`.

### Next

The homomorphism itself,
`finish (chunks.foldl feedChunk initialState) = parseNQuads (…)`, by an
induction over the chunk list carrying: the text consumed so far ends
with a newline, the stored offset is its length, and parsing it from
zero gives the stored dataset (<https://github.com/danbri/factoidal/issues/570>).

## Streaming equals batch — 2026-08-24

`Syntax/NQuadsHomomorphism.lean`: `streamParse11_eq_batch` — whatever
dataset the chunk fold produces, parsing the whole document at once
produces the same one. Proved by the fold invariant
(`foldl_feedChunk_inv`): the text consumed so far ends at a line
boundary, the stored offset equals its length, and parsing it from
position zero yields the stored dataset; each `feedChunk` step extends
the invariant by `parseQuadLines11_concat`.

Axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`, no user
`axiom`, no `native_decide`. `NQuadsStreaming.lean`'s "not proved here"
header section is replaced by a pointer to the proof.

Stated for a fold that ends without error. Equating the ERROR cases
needs the converse concatenation direction recorded in
`NQuadsConcat.lean`'s header.

Remaining for `RDF.NQuads.Streaming` coverage: the generic-consumer
half (`stream_consume` / `batch_consume` and their agreement theorem),
next.

## The generic N-Quads consumer — 2026-08-24

`Syntax/NQuadsFold.lean` ports the consumer half of
`RDF.NQuads.Streaming.fst`: a caller supplies
`consume : α → Triple → Option Subject → α` and receives every quad,
chunked (`streamConsume`) or whole (`batchConsume`), with no `Dataset`
built. `streamConsume11_eq_batch` is the agreement theorem.

Per the abstraction steer (CLAUDE.md, Standing decisions), fuel
independence and the line-boundary concatenation lemma are stated once
here over `α`. They are the proofs from `NQuadsStreaming.lean` /
`NQuadsConcat.lean` with `Dataset` generalised to `α` and `addQuad` to
`consume`; the proof text is otherwise unchanged, because those proofs
never inspect the accumulator. `parseQuadLinesAcc_eq_fold` ties the
shipping parser to the fold at `consume = addQuad`, so the dataset case
is an instantiation.

Six `#guard`s run a counting consumer chunked and whole, with chunk
boundaries mid-line, and check the graph-label slot reaches the
consumer.

Axioms `[propext, Classical.choice, Quot.sound]` on all five theorems;
no `sorry`, no user `axiom`, no `native_decide`.
✅ Build green at 864 jobs; Lean W3C runner unchanged (N-Triples 70
pass, 0 fail (out of 70); N-Quads 87 pass, 0 fail (out of 87); Turtle
313 pass, 0 fail (out of 313)).

Next: the `skills/counting-coverage` definition-level audit of
`RDF.NQuads.Streaming.fst` against the Lean modules, before any
coverage number moves.

## The parent7 query path answers correctly — 2026-08-24

`OWL/QueryMaterialise.lean` + wiring in `OWL/QueryEval.lean`, pinned by
`OWL/QueryEvalRegimeTests.lean`.

Measured before: the W3C entailment test parent7 returned 0 rows
through `evalSelectOwl`; the correct answer is one row (`:Dudley`).
Cause: the rewrite's shape search expects a canonical restriction node
in the data, which the F\* closure materialises (over-broadly, filtered
by the anchor — <https://github.com/danbri/factoidal/issues/236>) and
the Lean closure never did.

Repair: `augmentForQuery` adds, per maximum-qualified-cardinality-one
shape in the query, one canonical node with its four shape triples and
one membership triple per individual `Mat.isMember` PROVES (the
filler-bound rule). Every added membership is entailed; unprovable
memberships are not added. Measured on the fixture: five triples
added, member set exactly `{Dudley}` — no `Bob` (successor of unknown
class), no over-typing.

Measured after: 1 row, `?parent = :Dudley`, through the full pipeline
(Turtle parse → RL closure → SPARQL parse → rewrite → eval). The pin
runs that pipeline at build time and requires exactly one row, which
rules out both wrong answers (0 rows, extra rows) at once.

✅ Build green at 868 jobs. Lean W3C runner unchanged.

ⓘ Backport candidate for the F\* tree, per the owner's ruling that the
trees should behave the same: replace the closure's over-typing +
anchor filtering with proof-gated query-time materialisation.

## OWL entailment regimes wired into the Lean runner — 2026-08-24

`Harness/Run.lean`: a test naming `OWL-Direct` or `OWL-RDF-Based` now
runs — OWL 2 RL closure (`RL.closureFix`) of every fixture graph, then
the OWL query path (`QueryEval.evalSelectOwl` / `evalAskOwl` /
`evalConstructOwl`, which includes the query-time canonical
materialisation) — instead of being declared unsupported wholesale.
This is the blindness that hid the parent7 defect: the regime tests
existed, and the runner refused all thirty.

📊 sparql11 `entailment` suite, Lean runner:

* before: 40 pass, 0 fail, 30 unsupported (out of 70)
* after: **59 pass, 7 fail, 4 unsupported (out of 70)**

The 4 unsupported name the RIF regime only. The 7 failures are real
and now visible; F\* passes all 70. The failure shapes:

* three tests expect entailed members of restrictions the rewrite's
  BGP expansion cannot reach (`min 1` through `owl:equivalentClass`,
  `some Female`, `paper-sparqldl-Q3`);
* two tests get EXTRA rows binding closure-introduced blank nodes
  (`_:anon_*`) — answers under the regimes must not expose blank nodes
  the queried graph does not have;
* `sparqldl-11` needs `rdfs:domain`/`owl:Thing` schema answers;
  `simple 2` under investigation.

Each is a work item against the F\* score, not a regression: every one
of these tests reported "unsupported" yesterday.

## Entailment regimes: 7 failures repaired, suite green — 2026-08-24

📊 sparql11 `entailment` suite, Lean runner:

* before: 59 pass, 7 fail, 4 unsupported (out of 70)
* after: **66 pass, 0 fail, 0 skip, 4 unsupported (out of 70)**

The 4 unsupported name the RIF regime only; every OWL/RDFS regime test
passes. F\* passes 70 of 70 (it implements the RIF regime). The
repairs, in dependency order:

1. **`Mat.typeCEsOf` expands named types** (`OWL/Materialise.lean`,
   `namedSuperCEs`): an asserted type that is a NAMED class is
   followed through `rdfs:subClassOf` and `owl:equivalentClass` (both
   directions) to the class expressions provably above it. Sound:
   `i ∈ C` with `C ⊑ D` or `C ≡ D` gives `i ∈ D`. This is what lets
   `Mat.isMember` prove `:Alice ∈ (≥ 1 :hasChild)` from
   `:Alice a :Parent` + `:Parent ≡ (∃ :hasChild . owl:Thing)`
   (parent4), and `:paper1 ∈ (∃ :publishedAt . ¬:Workshop)` from
   `:ConferencePaper ⊑ (∃ :publishedAt . :Conference)` +
   `:Conference owl:disjointWith :Workshop` (paper-sparqldl-Q3).
2. **Unqualified `minCardinality` N ≥ 1 stops rewriting to the edge
   pattern** (`OWL/QueryRewriteExpand.lean`): the edge pattern
   `subj p ?v` missed members whose membership is type-derived with no
   asserted edge, and over-approximated N ≥ 2. The branch now
   re-emits the ORIGINAL pattern (type triple + the marker's shape
   triples); `QueryMaterialise.augmentForQuery` guarantees the queried
   graph holds a realising node whose members are exactly the
   `Mat.isMember`-proved individuals, so the original pattern matches
   with exact counting.
3. **`∃ p. F` with a nested filler gets comprehension witness edges**
   (`OWL/QueryMaterialise.lean`): that query form IS rewritten to the
   edge pattern, so membership triples are invisible to it. For each
   individual whose membership only the type route proves, the
   augmentation adds `i p _:w` and `_:w a c'` — the existential the
   type asserts, read back as a blank node. Added only when the known
   successors do not already prove membership, so no row is doubled.
   Named-filler `∃ p. F` is never rewritten and keeps being served by
   the membership triples (parent2).
4. **`inverseOfDomRngFlipFor` is now IN the closure**
   (`OWL/RLClosure.lean`): the rule was defined, documented — its doc
   comment even names `sparqldl-11` — and never registered in
   `conclusionsList`. Registered, with full soundness threading: four
   `Derives` rows (`invFlipDomRng`/`invFlipRngDom` and their reverse
   readings) in `RLRules.lean`, `inverseOfDomRngFlipFor_sound`, the
   dispatch case in `conclusionsFrom_sound`, four simulation cases in
   `complete_of_saturated` (`RLTheorems.lean`), and the store mirror +
   agreement lemma in `RLClosureIndexed.lean`. With the flip,
   `:child rdfs:domain :Parent` + `:child owl:inverseOf :parent`
   yields `:parent rdfs:range :Parent`, and scm-cls + scm-rng2 lift it
   to `owl:Thing` — the two expected sparqldl-11 rows.

Also in this batch (`Harness/Run.lean`): answers drop rows binding
blank nodes the queried graph does not contain (the closure's witness
nodes are not legal answer terms), and variables in CLASS position
(object of `rdf:type` / `rdfs:domain` / `rdfs:range` /
`owl:equivalentClass`, either side of `rdfs:subClassOf`) bind class
names only. Individual-position blank-node answers stay (owlds02).
No `eraseDups` anywhere: expected files contain duplicate rows
(bind07, sparqldl-10) — answers are bags.

## RIF entailment regime wired: suite complete — 2026-08-24

📊 sparql11 `entailment` suite, Lean runner:

* before: 66 pass, 0 fail, 0 skip, 4 unsupported (out of 70)
* after: **70 pass, 0 fail, 0 skip, 0 unsupported (out of 70)** — parity
  with the F\* runner.

New library module `L4Factoidal/RIF/Saturate.lean` — the FUNCTION of
the F\* `RIF.Core.Tests.saturate_with_program` / 
`materialise_import_graph` pair:

* `factsOfTriple` (RIF-RDF Compatibility §3: frame always; `rdf:type`
  also membership; `rdfs:subClassOf` also subclass) and its REVERSE
  `tripleOfGAtom` — derived frames, memberships and subclass atoms
  come back as triples, `pos` atoms have no RDF form, and a constant
  survives only if its lexical form passes `isIri` / `literalWf`.
* `saturateGraph`: facts → `Engine.closure` fixpoint (100 rounds, the
  F\* `default_fuel`) → derived triples appended, deduplicated.
  Rule-local constants are qualified first, so a rule's `_x` cannot
  capture a data blank node.

`Harness/Run.lean` glue, mirror of the F\* runner's consumer side:
the four SPARQL entailment tests name RIF-XML rule documents the
SPARQL suite does not bundle; they resolve by `mf:name` against the
vendored mirror `third_party/testing/rif/tc/`. DOCTYPE/entity
preprocessing, `Import` location→local-file resolution, and the
profile dispatch (`RDF`/`RDFS` → `RDFS.closureFix`, `OWL-*` →
`OWL.RL.closureFix`, `Simple`/none → plain triples) before
saturation; evaluation is then the PLAIN query path.

## SPARQL 1.2 reified triples + annotation blocks — 2026-08-24

Issue #556. Port of `parse_reified_triple_pattern`, `parse_reifier_id`
and `parse_annotations` from `SPARQL11.Parser.fst` into
`L4Factoidal/SPARQL/Parser.lean`: bare reified triples
`<< s p o (~ reifier)? >>` in subject and object position, and the
`~ VarOrReifierId?` / `{| predicateObjectList |}` annotation sequence
after a simple-predicate object. Same desugaring as the F\*: a reified
triple denotes its reifier (named by `~`, else a fresh blank node),
which takes the triple's place in the enclosing position and carries
one extra pattern `reifier rdf:reifies <<( s p o )>>`; the triple is
NOT itself asserted. Components reuse the restricted triple-term
parsers (no collections; predicate var/IRI/`a` only); annotations are
reachable only from `pObjectListSimple`, never `pObjectListPath`. All
of it is v12-gated at the tokenizer (the five tokens exist only under
the v12 flag), so the 1.1 grammar is untouched.

📊 Scores (Lean runner `l4w3c`):

* sparql12 syntax-triple-terms-positive: before 21 pass, 74 fail,
  18 unsupported (out of 113) → after **95 pass, 0 fail,
  18 unsupported (out of 113)**.
* sparql12 syntax-triple-terms-negative: **63 pass, 0 fail,
  2 unsupported (out of 65)** — unchanged, no regression.
* sparql12 eval-triple-terms: before 15 pass, 26 fail (out of 41) →
  after **38 pass, 3 fail (out of 41)**. The 3 remaining failures are
  the UpdateEvaluationTests; the update PARSER accepts all three
  fixtures at `.v12` (probed directly), but
  `Harness/Run.lean`'s `runUpdateEvaluation` calls
  `parseSparqlUpdate` without a version argument, defaulting to
  `.v11` — a harness gap, not a grammar gap (the query path already
  passes `.v12` for rdf12-mode suites).
* sparql11 syntax-query: **94 pass, 0 fail (out of 94)** — unchanged.

## sparql12 complete — 2026-08-24

📊 sparql12 family, Lean runner: **254 pass, 0 fail, 0 skip, 0
unsupported (out of 254)** — from 76 pass, 158 fail, 20 unsupported
this morning. Landings, in order: suite mode plumbing (fixtures,
queries, updates, expected graphs parse as 1.2), the reified-triple/
annotation grammar port (issue #556), the update-runner 1.2 mode, the
evaluator fixes (ill-formed `xsd:boolean` has no value; `STRLANG`
requires a non-empty tag — both defects shared by the F\* engine
behind a lenient runner comparison, issue #577), and the un-suffixed
`PositiveUpdateSyntaxTest`/`NegativeUpdateSyntaxTest` type names in
the dispatcher.

## Common Logic + IKL bootstrap (`CL/*.lean`, 2026-08-25)

The first LEAN-FIRST component: there is no F\* original. Owner
direction (2026-08-25): implement IKL and Common Logic "in parallel
expressions for both F\* and Lean 4. It is ok to do Lean first." The
F\* twin is the follow-up item on
<https://github.com/danbri/factoidal/issues/580>; every `CL` definition
uses inductive datatypes, structural recursion through explicit list
helpers, and explicit fuel where recursion is not on a direct suffix,
so the transcription is mechanical.

| Lean 4 | Source of truth | Notes |
|---|---|---|
| `L4Factoidal/CL/Syntax.lean` | ISO/IEC 24707 clause 6.1, Annex A; IKL guide "IKL Overview" | terms/sequences/sentences with IKL `(that S)` as one `Term` constructor; `isPureCL` characterises the ISO/IEC 24707 subset |
| `L4Factoidal/CL/Clif.lean` | ISO/IEC 24707 Annex A.2.2; IKL guide | CLIF lexer (quoted strings, enclosed names, sequence markers), fuel-bounded S-expression parser and reader, serialiser, 17 round-trip `#guard`s |
| `L4Factoidal/CL/Semantics.lean` | ISO/IEC 24707 §6.2–6.3; IKL guide + Appendix B | unsegregated-universe interpretations, `Prop`-valued satisfaction, `EntailsUnder`; IKL `iProp` + `IklRespectsThat`, with the cancelling-parentheses law `sat_assert_that` proved |
| `L4Factoidal/CL/Examples.lean` | IKL guide sentences (transcribed + adapted) | 20 build-time `#guard`s; four satisfaction theorems over a finite interpretation |

Not covered (named in each module header and on the issue):
`cl:text`/`cl:module`/`cl:imports` and importation semantics,
`cl:comment`, `/* */` lexical comments, IKL numeric quantifiers and
special name forms, role sets, datatype/string/number theories,
propositional identity (`=p`) and the guide's structural axioms, and
any completeness result.

## OWL three-valued verdict + negation goals (`OWL/Refute.lean`, `OWL/NegationGoals.lean`, 2026-08-25)

Issue <https://github.com/danbri/factoidal/issues/586>: the Lean
refuter's public verdict collapsed quiescence and budget-out into one
`none`, so the F\* wire contract (`consistent: true|false|null`) could
not be served. The `search` function already distinguished the three
outcomes; the change exposes them and integrates rather than
duplicates.

| Lean 4 | Source of truth | Notes |
|---|---|---|
| `OWL/Refute.lean` `tableauConsistent` | `Tableau.Refute.fst` `tableau_consistent` | verdict meanings mirrored exactly: `some false` = clash on every branch or immediate violation; `some true` = quiescence (NOT completeness); `none` = budget out. `refute` is now its refutation-only projection — one search path; `refute_eq_false_iff` proves the two views agree on refutation |
| `OWL/NegationGoals.lean` | `Tableau.Refute.fst` §11a/11b (`negation_goals` + builders) | structural/content split (incl. the named-subject boolean-marker exception), the seven negation arms, the `≤0 p.{y}` encoding of `¬p(x,y)` over `Vocabulary.litNni0`. One unsupported conjunct collapses to `none` (caller keeps its closure verdict) |
| `Wasm/Ops/Reason.lean` `owlIsConsistent` / `owlEntails` + `Wasm/Dispatch.lean` | `bin/npm-entry/entry_jsoo.ml` | envelopes field for field (`consistent`/`entailed` true\|false\|null, `via`, `reason`, fuel as a decimal string in opts, default 20000); chain = `OWL.RL.closureFix` then the refuter, the Lean tree's counterpart of the F\* entry's closure-then-`tableau_consistent` |

Correspondence with the declarative calculus (`OWL/Tableau.lean`):
stated rule-for-rule in `Refute.lean`'s header; `RefuteTests.lean`
carries an instance-level paired witness (one contradiction refuted by
the executable search AND by an explicit `Refuted` derivation). The
general abstraction — a clash trace serialised as a `Refuted`
derivation — is the certificate-checker rung, follow-up 6 on the
issue.

📊 `lake exe l4owl-probe --dir third_party/testing/owl [--dl]`
re-measured before and after at the same HEAD: identical column for
column (RL TOTAL 1131 pass, 316 fail, 2 skip, 8 unsupported, out of
1457; `--dl` TOTAL 1208 pass, 239 fail, 2 skip, 8 unsupported, out of
1457) — expected, since the harness consumes the `refute` projection
and the search is unchanged. `Wasm/native-smoke.sh` 43 pass, 0 fail
(out of 43), seven new cases: consistent / inconsistent / budget-out
(fuel named in the reason) / cyclic-TBox-settles / entails-via-closure
/ countermodel / entails-budget-out.

## D-semantics repair: triple-term-interior ill-typed literals + rdf-semantics suite pressure (2026-08-25)

Repair of <https://github.com/danbri/factoidal/issues/602> under the
decided spec anchor: RDF 1.2 Semantics W3C Working Draft (7 April
2026, <https://www.w3.org/TR/rdf12-semantics/>, a WD, not a REC) — §5
`I(E) = IT(I(E.s), I(E.p), I(E.o))` composed with §7.1 "any triple
containing the literal must be false", as encoded by the W3C rdf12
`malformed-literal` test. The EXECUTABLE's interior collection was
correct; the totalized model theory (`RDF.DInterpCond`) was the
defective layer. Failing-pin-first: the pin
`dEntailsMt_tt_illtyped` was run against the pre-repair semantics and
failed (the superseded `dEntailsMt_tt_gap` proved its negation), then
the semantics was repaired until it passed.

What changed:

* `RDF/Entailment.lean`: canonical collector pair
  `Term.mentionedLiterals` (interiors included, D-inconsistency) /
  `assertedLiterals` (top level only, `rdfs:range`), each citing its
  WD clause; `termIllTypedMention`; no catch-all `_` over `Term` in
  verdict folds (`hasRangeClash`, `Regime.bindable` written out).
* `RDF/EntailmentRdfsDatatypeClash.lean`
  `hasIllFormedRecognizedLiteral` now uses the canonical collector —
  it was the OPPOSITE polarity from `hasIllFormedLiteral` in the same
  tree, silently. F\* side tracked in
  <https://github.com/danbri/factoidal/issues/604>.
* `Unified/DSchema.lean`: `DInterpCond` clause 2 and
  `dExclusionSchema` generalised from literals to terms with ill-typed
  mentions (`dExclusionTerm`, blank nodes universally bound);
  `unified_adequate_d` unchanged in statement, reproved; NEW
  `RDF.regimeEntails_d_sound_mt` (unconditional soundness of the
  executable D-regime) and `unified_adequate_d_decided_sound` (the
  decided corollary's sound half, no `GraphTtFree`); the complete half
  is the registry's named open lemma (D-Herbrand literal quotient +
  bindable-restricted search completeness). `dEntailsMt_tt_gap`
  REMOVED; its content survives as
  `topLevel_exclusion_insufficient_for_tt` over the superseded
  `DInterpCondTopLevel` (strictness: `ttSep_not_dCond`).
* `Harness/Manifest.lean`: lenient-with-report manifest parse
  (`parseTurtleRecover` / `parseManifestTextLenient`, the F\* runner's
  issue-334 policy) — undeclared prefixes recovered into
  `urn:x-manifest-recovery:<pfx>#` with a printed `MANIFEST-RECOVERY`
  line. This restores the rdf12 rdf-semantics suite, which had
  reported 0 pass, 0 fail (out of 0), `no_manifest=1` since it landed
  (upstream undeclared `test:` prefix).

📊 MEASURED (same HEAD, `lake exe l4w3c`):

```
rdf-semantics: 19 pass, 11 fail, 0 skip, 17 unsupported (out of 47)   -- FIRST READING
entailment: 70 pass, 0 fail, 0 skip, 0 unsupported (out of 70)
rdf-mt: 39 pass, 0 fail, 0 skip, 0 unsupported (out of 39)
sparql11 manifest-all: 631 pass, 0 fail, 0 skip, 0 unsupported (out of 631)
rdf11 six + rdf12 nine suites: 1355 pass, 0 fail, 0 skip, 0 unsupported (out of 1355)
```

rdf-semantics first-reading decomposition: `malformed-literal`,
`malformed-literal-control`, `malformed-literal-accepted` PASS (the
repair's anchor tests). The 17 unsupported are xsd:float / xsd:double
/ rdf:JSON value models this tree does not carry (refused by name).
Of the 11 fails: `malformed-literal-no-spurious` and
`malformed-literal-bnode-neg` are NegativeEntailmentTests whose action
graph the SAME suite declares D-inconsistent (`malformed-literal`,
`mf:result false`) — under the WD's classical entailment an
inconsistent premise entails everything, so those two expectations
contradict the suite's own inconsistency verdict (upstream question,
to be raised on w3c/rdf-tests); the remaining 9 (`literal-type`,
`opaque-literal`, `opaque-language-string`±control,
`opaque-dir-language-string-control`, `annotation`,
`annotation-unfolded`, `triple-terms-propositions`, `reifies-range`)
are pre-existing engine gaps first exposed by this suite loading, not
regressions. F\* committed binary, same day:
`w3c_runner entailment` 70 pass, 0 fail (out of 70).

Method hazard write-up: hazard #33 in
`skills/workflow-gotchas-debugging/SKILL.md` (iron rule 14, same
landing).

## Stage: HACL\* SHA-256 as a host-passed hasher (2026-09-02)

Merkle admission of a persisted Shardborough store hashes every
65,536-byte chunk of every artifact plus every interior tree node. With
the pure Lean `Crypto.sha256` (roughly 5 MB/s) that dominated both the
full read and the activation of the 25 MB gene store.

What landed:

| File | Change |
|---|---|
| `L4Factoidal/Crypto/SHA2Native.lean` (new) | `@[extern "l4_hacl_sha256"] opaque sha256Hacl (m : @& ByteArray) : ByteArray`, with the trust statement, the crypto-policy citation, and the contract (a message over 2^32-1 bytes is refused with the EMPTY `ByteArray`, since HACL\*'s length parameter is a `uint32_t`) |
| `ffi/hacl_ed25519.c` | `l4_hacl_sha256`: one length check, then `Hacl_Hash_SHA2_hash_256`. No arithmetic. The translation unit was already compiled and linked on both targets (`extern_lib libl4hacl`, `Wasm/build-wasm.sh`) because Ed25519 needs SHA-512 |
| `L4Factoidal/Storage/BlockMerkle.lean` | `structure Hasher where digest : ByteArray → ByteArray`; `pureHasher := ⟨sha256⟩`; every operation restated as `leafWith`/`nodeWith`/`nextLevelWith`/`rootWith`/`rootOfChunksWith`/`proofWith?`/`applyStepWith`/`verifyWith`, taking the hasher first. The old names are exactly those at `pureHasher`, so every existing caller, `#guard` and theorem is unchanged in meaning |
| `L4Factoidal/Storage/BlockArtifact.lean`, `ChunkedArtifact.lean` | `digestWith` / `verifyWith`, `fromChunksWith?` / `verifyChunkWith`, with the unsuffixed names as the `pureHasher` instances |
| `Harness/NativeHasher.lean` (new) | `nativeSha256`, `nativeHasher`. Under `Harness/` so the verified library never depends on an extern for its own semantics, and so `Wasm/build-wasm.sh` (which skips every `Harness_*` translation unit) keeps the browser worker's closure unchanged — it checks CRC, not Merkle |
| `Harness/PosixRangeIO.lean`, `ShardActivate.lean`, `IndexedBlockV3Convert.lean`, `IndexedBlockV3Materialize.lean`, `PredicateShardPack.lean`, `ShardPublish.lean` | pass `nativeHasher` / call `nativeSha256` |
| `Harness/VcProbe.lean` | new section 5, `sha256 differential` |
| `.github/workflows/verify-lean4.yml` | `lake exe l4vc-probe` added as a required step |

Why a PARAMETER and not `@[implemented_by] sha256`: build-time
`#guard`s run in the Lean INTERPRETER, which cannot call an extern (a
`#guard` on one fails with "could not find native implementation").
An `@[implemented_by]` on `sha256` would therefore have deleted the
FIPS 180-4 vectors of `Crypto/SHA2Tests.lean` from the build. The pure
function stays the specification, stays what every theorem is about,
and stays what the WASM target evaluates.

The substitution is sound only because the two hashers agree on every
input, and one of them is opaque, so that cannot be proved here. It is
MEASURED: `lake exe l4vc-probe`'s `sha256 differential` section
compares them on the FIPS 180-4 vectors, the empty message, 1/55/56/63/
64/65-byte inputs (the SHA-256 block and padding boundaries), the
1,000,000×'a' FIPS message and a 1 MiB deterministic pseudo-random
buffer — 13 pass, 0 fail (out of 13) — and the probe exits non-zero on
any mismatch.

Measured on the 25 MB gene collection (single runs, wall clock, nothing
else running; BEFORE was taken by pointing `nativeSha256` back at the
pure `Crypto.sha256` and rebuilding, so the two runs differ only in the
hasher):

| Operation | Before | After |
|---|---|---|
| `l4block-id-v3-query` `SELECT (COUNT(*) …)` over the whole manifest | 7.49 s | 3.94 s |
| `l4block-shard-activate` on a fresh copy of the generation | 52.95 s | 13.81 s |
| `l4block-shard-pack` of `chromosome.ttl` (9,227 triples) | 1.01 s | 0.72 s |

The BYTES do not change: the `chromosome.ttl` pack output directory is
identical before and after (`diff -r`), and `predicate-0.ibk3` still
hashes to `01484578d6b9696d0298a20898b8a2bf209f7477cc938002c35aa1c55611068a`.
Activation of the existing gene generation still succeeds against the
roots a pure-hasher packer wrote, which is the same fact from the
reader's side.

Gates after the landing: `lake build` (919 jobs) clean;
`lake exe l4vc-probe` 71 pass, 0 fail (out of 71);
`bash Wasm/native-smoke.sh` 63 pass, 0 fail (out of 63);
`bash tools/w3c-persisted-census.sh` 535 executed, 0 refused (out of
535).

Not done: `Sha256Stream` (the incremental hash `PredicateShardPack`
uses for the source-file identity of a packed generation) has no
streaming HACL\* counterpart bound, so that one hash stays pure Lean.
`L4Factoidal/Storage/ShardManifest.lean`'s `verifyEntry`/
`openVerified?` (the IBK2 `Reader` boundary) were left on `pureHasher`
— they are not on the IBK3 paths measured above.
