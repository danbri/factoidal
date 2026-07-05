# bin/rif-runner — vendored W3C RIF Core test runner

Stand-alone CLI with two parts:

1. The original 4 vendored RIF Core test cases under
   `third_party/testing/rif/tc/`, paired with the SPARQL 1.1
   entailment manifest's `.rq`/`.srx` fixtures — end-to-end RIF-XML
   rule parsing, `<Import>` companion-graph resolution,
   forward-chaining saturation, and the real SPARQL 1.1 evaluator
   (not a triple-membership shim).
2. A directory walker over the full vendored W3C RIF Core dialect
   corpus (`third_party/testing/rif-core-suite/`, see that
   directory's `README.md`), evaluating `PositiveEntailmentTest`/
   `NegativeEntailmentTest` cases directly from their
   premise/conclusion RIF-XML documents — no SPARQL-manifest `.rq`/
   `.srx` needed, since the corpus is self-contained.

```
rif_runner [-v|--verbose]
```

No arguments needed: both parts always run. Part 1's four cases
(mf:name from
`third_party/testing/w3c/sparql/sparql11/entailment/manifest.ttl`,
IRIs `:rif01 :rif03 :rif04 :rif06`) are a hardcoded lookup table —
see the module comment in `rif_runner.ml` for why a general manifest
walker is not worth building for exactly four fixtures. Part 2 walks
`third_party/testing/rif-core-suite/Core_v1.22/Approved/*` directly
(no hardcoded per-test table).

## Pipeline

1. `Parser_RIFXML.parse_rif_program_with_imports` — RIF-XML rules +
   `<Import>` URL list. The internal-subset `<!DOCTYPE ... [ <!ENTITY
   ...> ]>` prolog every vendored `.rif`/`.rdf` fixture opens with is
   stripped and its entities inlined first (`expand_doctype_entities`)
   since `Parser.XML.fst` has no DTD support — pure textual
   preprocessing, same category as `bin/owl-runner`'s
   `catalog_entities` expansion.
2. Merge the manifest `qt:data` `.ttl` with every resolved `<Import>`
   companion graph. `Modeling_Brain_Anatomy`'s import declares
   `<profile>http://www.w3.org/ns/entailment/OWL-Direct</profile>`;
   its rule body needs `rdf:type MaterialAnatomicalEntity` on
   individuals the ontology only asserts via `rdf:type Gyrus` +
   `rdfs:subClassOf`, so that companion graph is closed under
   `RDF_Graph_Executable.owl_rl_closure_with_reflexivity` +
   `Tableau.tableau_materialise` before merging
   (`apply_import_closure`). `RDF_Combination_Blank_Node`'s import
   declares plain `.../entailment/RDF` and is merged as-is.
3. `RIF_Core_Eval.fixpoint` — fuel-bounded forward-chaining
   saturation (fuel 100; `Prims.nat` is `Z.t` in this codegen, so the
   fuel argument must be `Z.of_int 100`, not a bare OCaml `int`).
4. The `.rq` query runs through `SPARQL11_Parser` +
   `OWL_QueryEval.{eval_select_query_owl,eval_ask_query_owl}` +
   `SPARQL11_Algebra` — the same parser/evaluator every other W3C
   runner in this repo uses — compared against the expected `.srx`
   via `Parser_SRX`. Blank nodes in the query pattern (rif06's
   `[] a ex:named`) are rewritten to existential variables via
   `SPARQL11_Algebra.rewrite_query_bnodes_pattern`, mirroring
   `bin/w3c-runner/w3c_runner.ml`'s entailment-regime dispatch.

Deliberately NOT used: `RIF.Core.Tests.run_rif_ask_triple` /
`run_rif_select_rows` / `run_rif_entailment_check`. Those are
simplified ground-triple-membership shims (see
`formal/fstar/RIF.Core.Tests.fst` section 3/4) that never run a real
SELECT projection or ASK boolean evaluation — using them would mean
this runner isn't actually testing the SPARQL query, just checking a
raw triple is present.

## Part 2: the Core-suite corpus walker

Each corpus test is self-contained: a `-premise.rif` RIF-XML document
(rules AND ground facts — a fact parses to a rule with an empty body
per `Parser.RIFXML.parse_fact_atom`) and a `-conclusion.rif`
(`PositiveEntailmentTest`) or `-nonconclusion.rif`
(`NegativeEntailmentTest`) RIF-XML document naming the fact(s) whose
entailment is under test.

1. Read + DOCTYPE-preprocess both documents (same
   `expand_doctype_entities` as Part 1).
2. Scan both raw texts for RIF-XML element tags this project does
   not model at all (`<External>`, `<List>`, `<Equal>`, `<Exists>`,
   `<Or>`, `<Naf>`/`<Neg>`) — if found, SKIP naming the construct.
3. `parse_rif_program_lenient` — a thin textual-reshaping wrapper
   around `Parser_RIFXML.parse_rif_program_with_imports` that fixes
   two shapes the corpus uses but `Parser.RIFXML.fst`'s
   `extract_group_from_doc`/`parse_group_children` do not recognise
   (both discovered while building this walker, both **pure text
   reshaping, not new parsing capability** — see the code comments
   at `wrap_bare_fact_in_group` / `ensure_group_present` in
   `rif_runner.ml`):
   - a bare fact element as the whole document root (most
     `-conclusion.rif`/`-nonconclusion.rif` files) is wrapped in
     `<Group><sentence>...</sentence></Group>` — without the
     `<sentence>` wrapper, `parse_group_children` silently treats an
     unwrapped child as "unknown metadata" and drops it rather than
     failing, which up until this fix produced silent **empty**
     rule lists (a `bgp = []` "vacuous entailment" false pass/fail,
     not a parse error) for corpus tests whose conclusion is a bare
     fact — a real bug this project would not want to ship;
   - a `<Document>` with only `<directive><Import>...` children and
     no `<Group>` at all (premise is 100% import-derived, e.g.
     `RDF_Combination_Constant_Equivalence_1`) gets an empty
     `<payload><Group></Group></payload>` spliced in before
     `</Document>`.
4. Determine the `<Import><profile>` entailment regime the same way
   Part 1's hardcoded table does (`Simple`/`RDF`/`RDFS` →
   `No_Closure`/`RDFS_Closure`, `OWL-Direct` → `OWL_Direct_Closure`);
   unrecognised profiles SKIP.
5. `RIF_Core_Eval.fixpoint`-saturate the (closure-applied) import
   graph under the premise program — the premise's own ground facts
   materialise on round 1 of this same fixpoint, so no separate
   "load facts" step is needed.
6. Translate every conclusion fact's head atom to a SPARQL
   `triple_pattern` via `RIF_Core_Translation.translate_atom` (reused
   on a fact's HEAD position rather than a rule BODY — its type,
   `rif_atom -> option triple_pattern`, does not care which position
   its argument came from) and ask whether that BGP has ≥1 solution
   over the saturated premise via `OWL_QueryEval.eval_ask_query_owl`
   — the same machinery Part 1 drives, so blank nodes in the
   conclusion BGP get the same existential treatment via
   `SPARQL11_Algebra`'s internal `rewrite_query_bnodes_pattern` step.
   `PositiveEntailmentTest` passes when the ASK is true;
   `NegativeEntailmentTest` passes when it is false.

`PositiveSyntaxTest`/`NegativeSyntaxTest` (RIF Core dialect
"safeness" grammar restriction) and `ImportRejectionTest`
(vocabulary-separation / DL-consistency rejection) are
unconditionally SKIPPED — `Parser.RIFXML` is a structural RIF-XML →
AST parser with no dialect-safeness checker and no import-rejection
consistency checker, and building either is out of scope for this
slice (new F* modules, not runner glue).

## Score

Measured 2026-07-05 (initial corpus landing: 7 pass, 3 fail, 36 skip
of 46 for Part 2; updated same day after fixing 2 of the 3 FAILs —
see below):

- **Part 1 (original 4 vendored SPARQL-manifest cases): 4 pass, 0 fail (out of 4).**
- **Part 2 (vendored W3C RIF Core dialect corpus): 9 pass, 1 fail, 36 skip (out of 46).**
- **Combined: 13 pass, 1 fail, 36 skip (out of 50).**

Skip buckets (by construct/reason):

| Count | Reason |
|---|---|
| 16 | `External` (builtin predicate/function calls) |
| 6 | RIF Core dialect safeness-condition checking not implemented |
| 6 | import-rejection / vocabulary-separation consistency checking not implemented |
| 3 | Parser_RIFXML could not parse the premise (Uniterm/Atom arity ≠ 2 — `Local_Constant`, `Local_Predicate`, `Positional_Arguments`, each using a unary Uniterm fact/atom RIF.Core.Syntax has no encoding for) |
| 2 | `Equal` (equality atom) |
| 1 | `List` (RIF list terms) |
| 1 | conclusion.rif not in the vendored corpus (packaging gap in the official Core_v1.22 zip — `RDF_Combination_Constant_Equivalence_Graph_Entailment`) |
| 1 | `Exists` (existential quantification — `RDF_Combination_Blank_Node`'s **corpus-path** conclusion; note this same test already PASSES via Part 1's hardcoded `rif06` path, which uses a hand-authored `.rq`/`.srx` pair instead of the official `-conclusion.rif`) |

**What extending the F\* parser would unlock** (not attempted this
slice, per brief): the 16 `External` skips are almost all
`Builtins_*`/`Chaining_strategy_*`/`Guards_and_subtypes`/
`EBusiness_Contract`/`Factorial_Forward_Chaining` — RIF-BLD built-in
predicate/function calls layered on top of Core, out of this
project's declared RIF scope (see `docs/claude-rules/scope.md`).
`Equal`/`Exists`/`List` are genuine RIF Core constructs (equality
atoms, existential quantification, list terms) that a real Core
parser extension would need; each appears in only 1-2 tests here.

Of the original 3 FAILs, 2 are now fixed in F\* and 1 remains (a
corpus data defect, not fixable without breaking correct RDF
datatype-IRI semantics):

- `RDF_Combination_Constant_Equivalence_3` — **fixed.** The
  conclusion's `<Const type="&rdf;PlainLiteral">with language
  tag@en</Const>` needed to decode to a plain literal `"with language
  tag"@en` (RIF-in-RDF's `rdf:PlainLiteral` symbol space packs
  `text@lang` as one string, `text@` with an empty tag denoting a
  plain `xsd:string`). `Parser.RIFXML.fst` gains
  `is_plain_literal_type_marker` + `plain_literal_const`: on the
  `rdf:PlainLiteral` type marker, split the lexical form on its last
  `@` (`find_last_at`, same traversal shape as the existing
  `find_last_colon` used by `local_name`) into text/lang, producing a
  language-tagged literal when the tag is non-empty, else a plain
  `xsd:string`. `const_from_type` dispatches to it before falling
  through to the generic `typed_literal_const` path.
- `Non-Annotation_Entailment` — **fixed.** The imported `dc:title`
  predicate is typed `owl:OntologyProperty` (annotation-only) on an
  `owl:Ontology` individual; under the OWL 2 Direct Semantics
  RDF-compatible mapping, ontology-annotation triples are excluded
  from the "regular" graph before entailment checking, so the RIF
  rule `?x dc:title ?y => ?x hasTitle ?y` must never fire. New module
  `OWL.DirectMapping.Filter.fst` — deliberately standalone rather
  than an edit to `RDF.Graph.Executable.fst` (owned by a concurrent
  work item the same wave this was fixed; the filter only needs that
  file's already-exported `triple`/`rdf_graph`/`wf_iri` types) —
  exports `exclude_annotation_triples`: drop every triple whose
  predicate is declared (elsewhere in the same graph)
  `rdf:type owl:AnnotationProperty` or the legacy OWL 1 DL
  `owl:OntologyProperty`. `rif_runner.ml`'s `apply_import_closure`
  calls it on the imported companion graph before the OWL-Direct
  closure steps (`owl_rl_closure_with_reflexivity` +
  `Tableau.tableau_materialise`) run, so the annotation assertion
  never reaches the closure or the rule match. Scope note: this
  covers the "predicate declared annotation/ontology-only in-graph"
  case the corpus exercises; it does not special-case the built-in
  OWL 2 annotation properties needing no declaration (`rdfs:label`,
  `rdfs:comment`, `owl:versionInfo`, ...) or
  `owl:annotatedSource`/`Property`/`Target` reification — no vendored
  test here exercises those, so extending speculatively would be
  scope creep without a driving test.
- `RDF_Combination_Constant_Equivalence_4` — **still fails; a corpus
  data defect**, not an engine gap: both `import001.rdf` (datatype
  `file:///C:/work/eclipse_workspaces/.../XMLSchema#string`) and
  `import001.ttl` (`@prefix xs: <www.w3.org/2001/XMLSchema#>`, no
  scheme) declare a malformed `xsd:string` datatype IRI that does not
  match the conclusion's correct `http://www.w3.org/2001/XMLSchema#string`
  — present in the official W3C `Core_v1.22.zip` distribution as
  authored in 2010, uncorrected in the "Second Edition". Left as a
  labelled FAIL (not moved to a SKIP bucket): the pipeline fully
  processes this test end to end and it genuinely does not entail
  under a correct datatype-IRI comparison, which is a different kind
  of honesty gap than the SKIP buckets above (constructs/checks not
  yet implemented at all). `rif_runner.ml`'s `run_corpus_suite`
  appends a `KNOWN-DEFECT: ...` note to this specific test's FAIL
  line (`known_corpus_defect_note`) pointing back at this section
  rather than silently leaving a bare "expected entailed=true, got
  false".

## Why the source lives here, not in `formal/fstar/ocaml-output/`

Per CLAUDE.md iron rule #11, hand-written consumer-side OCaml does
not belong in `formal/fstar/ocaml-output/` — that directory is
reserved for F\*-extracted output and `assume val` glue patches. This
runner is a consumer of the F\*-extracted RIF engine + SPARQL
evaluator, so it lives under `bin/<consumer>/` per the migration
epic [#200](https://github.com/danbri/factoidal/issues/200) Section D.

## Build

Compiled in an isolated `mktemp` scratch dir (copy the required
extracted `.ml` modules in, compile there, copy the resulting binary
out) — the same isolation `formal/fstar/build-ocaml-serializer.sh`
uses, so this doesn't poison `formal/fstar/ocaml-output/`'s `.cmi`/
`.cmx` artifacts for whatever `build-ocaml.sh` invocation is
in flight. Module list mirrors `bin/owl-runner`'s
`COMMON_MODULES` (`build-ocaml.sh`'s `compile` step) — this list
transitively includes `Parquet_Footer.ml`, which needs the
`experimental_ocaml_glue/parquet_zstd_stubs.c` C stub linked in (same
as `build-ocaml.sh`'s `PARQUET_NATIVE_STUBS` block) or the link fails
with `undefined reference to caml_parquet_zstd_decompress_hex`:

```
eval $(opam env --switch=fstar)
SCRATCH=$(mktemp -d)
cp formal/fstar/ocaml-output/*.ml "$SCRATCH"/
cp bin/rif-runner/rif_runner.ml "$SCRATCH"/
cd "$SCRATCH"
ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix -linkpkg -w -8-14-26 \
  $COMMON_MODULES \
  -ccopt -I/usr/include ../../../formal/fstar/experimental_ocaml_glue/parquet_zstd_stubs.c \
  -cclib -L/usr/lib/x86_64-linux-gnu -cclib -lzstd \
  rif_runner.ml -o rif_runner
```
(`$COMMON_MODULES` is the exact string from `build-ocaml.sh`'s
`compile` step — not reproduced here to avoid drift.)

**`OWL_DirectMapping_Filter.ml` caveat (as of the Non-Annotation_Entailment
fix, 2026-07-05):** `rif_runner.ml` now calls
`OWL_DirectMapping_Filter.exclude_annotation_triples`, but
`OWL.DirectMapping.Filter.fst` was deliberately **not** added to
`build-ocaml.sh`'s `ALL_MODULES`/`COMMON_MODULES` lists this wave —
that script is shared with concurrent work and the new module's only
consumer today is this runner. Until a follow-up wires it into the
three lists (per the `fast-verify-extract`/`workflow-gotchas-debugging`
skills' "new module" rule), build this runner with
`OWL_DirectMapping_Filter.ml` inserted into `$COMMON_MODULES` by hand
(right after `OWL_Vocabulary.ml`, since it depends only on
`RDF_Graph_Executable.ml`), and extract it directly rather than via
`build-ocaml.sh extract`:

```
fstar.exe --z3version 4.13.3 --codegen OCaml --odir formal/fstar/ocaml-output \
  --cache_checked_modules formal/fstar/OWL.DirectMapping.Filter.fst
```

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/owl-runner/README.md`, `bin/w3c-runner/README.md`
- `formal/fstar/RIF.Core.Eval.fst`, `RIF.Core.Translation.fst`,
  `RIF.Core.Syntax.fst`, `Parser.RIFXML.fst`
