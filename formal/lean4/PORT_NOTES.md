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

Not proved: completeness at saturation for the eight new rows (T4 of
`ClosureTheorems.lean` covers the six rdfs-core rows; the extension is
the same argument per row and is the named obligation); any
model-theoretic statement (D-interpretations are not ported, so the
regime comparisons `literalValueEq` carry guards, not theorems).

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
