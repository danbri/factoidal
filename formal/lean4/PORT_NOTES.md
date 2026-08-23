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
| `eval_select_item` / `eval_select_items_row` row+position context | `Query.lean` `evalSelectItemsRow`, `evalSelectItemsFrom` | same two seeds |
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
declarations — the Lean tree's single permitted `extern` family under
the crypto-policy skill's Lean 4 amendment (signatures via HACL\* FFI
only; never a hand-written implementation). Trust statement, in full,
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
| `w3c_runner.ml` `read_manifest`'s LENIENT-WITH-REPORT manifest parse (issue #334) | *(no counterpart)* | `Harness/Manifest.lean` parses strictly; the `rdf12/rdf-semantics` manifest's undeclared `test:` prefix therefore zeroes that one suite, reported as `0 out of 0` with `no_manifest=1` rather than hidden |

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
