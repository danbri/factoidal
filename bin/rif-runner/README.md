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
   not model at all (`<List>`, `<Or>`, `<Naf>`/`<Neg>`) — if found,
   SKIP naming the construct. (`<External>`/`<Equal>` graduated to
   real evaluation on 2026-07-05; `<Exists>`-quantified CONCLUSIONS
   graduated on 2026-07-10 — declared variables stay free and the
   entailment ASK treats them existentially.)
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
(vocabulary-separation / DL-consistency rejection) are checked by new
module `RIF.Core.Conformance.fst` (added 2026-07-05) — see "RIF Core
conformance checking" below.

## External(...)/Equal builtin evaluation (added 2026-07-05)

`Parser.RIFXML.fst` now parses `External(...)` in both its uses —
term/function position (`<content><Expr>...</Expr></content>`,
nested inside an atom's arguments or an `Equal`'s right-hand side,
e.g. `func:numeric-add`) and formula/predicate position
(`<content><Atom>...</Atom></content>`, a standalone body conjunct,
e.g. `pred:numeric-greater-than`) — into two new
`RIF.Core.Syntax.rif_term`/`rif_body` constructors,
`RIF_TermExternal`/`RIF_BodyExternal`, plus `Equal(left, right)` into
`RIF_BodyEqual`. `RIF.Core.Translation.split_body` separates a rule
body into its ordinary atoms (still BGP-joined via `eval_bgp`, exactly
as before) and these "extra conditions"; `RIF.Core.Eval.fire_rule`
evaluates the extras per candidate binding, in the body's original
left-to-right order, via new module `RIF.Core.Builtins.fst`:

- `EC_External(op, args)`: a builtin PREDICATE filter — keep the
  binding iff the builtin evaluates to `Some true`.
- `EC_Equal(lhs, rhs)`: if `lhs` is a variable not yet bound, this is
  a BIND (`?N = External(func:numeric-add(?N1 1))`, needed by
  `Factorial_Forward_Chaining`'s builtin-function chaining); otherwise
  a ground equality filter, using cross-type numeric comparison
  (reusing `SPARQL11.Algebra.value_compare`) so e.g. `"2"^^xs:integer
  = numeric-divide(6 3)` compares equal by VALUE against the resulting
  `xsd:decimal`, not by strict datatype identity.

`RIF.Core.Builtins.fst`'s scope (see its own module comment for the
full rationale): the numeric function/predicate family
(`numeric-add`/`subtract`/`multiply`/`divide`/`integer-divide`/
`integer-mod`, `numeric-equal`/`not-equal`/`less-than`/`less-than-
or-equal`/`greater-than`/`greater-than-or-equal`), `boolean-equal`/
`less-than`/`greater-than`, `literal-not-identical`, and
`is-literal-<T>`/`is-literal-not-<T>` for a fixed datatype list
(decimal/double/float/integer/long/int/short/byte/negativeInteger/
nonNegativeInteger/nonPositiveInteger/positiveInteger/unsignedLong/
unsignedInt/unsignedShort/unsignedByte/hexBinary/base64Binary/anyURI/
boolean/XMLLiteral), plus XSD/rdf "constructor function" casts
(`External(xs:boolean(...))`, `External(rdf:XMLLiteral(...))`, ...)
targeting those same datatypes. The 2026-07-10 wave added the full
string family, the rdf:PlainLiteral family (over the decoded
`xsd:string`/`rdf:langString` form), `pred:iri-string` in both its
ground-filter and BINDING-PATTERN-execution forms, and the
EBusiness_Contract dateTime slice — see the Score section's
disposition table. Still deliberately NOT covered (each an honest
SKIP naming the unimplemented builtin IRI, per
`find_unsupported_builtin` in `rif_runner.ml`): List builtins and
the full date/time/duration family beyond that slice.

Two important discoveries from the corpus's own test data (see
`RIF.Core.Builtins.fst`'s comments at the relevant functions for the
full reasoning): for the numeric/binary datatypes `is-literal-<T>`
checks the argument's LEXICAL FORM against T's lexical space, NOT
its declared datatype tag —
`Guards_and_subtypes` requires BOTH `is-literal-decimal("3"^^
xs:integer)` AND `is-literal-integer("3"^^xs:decimal)` to hold, which
only a lexical-only check satisfies (a subtype check would only ever
satisfy one direction). The exception is `anyURI`/`XMLLiteral`, whose
XSD lexical space is essentially unconstrained (any string) — for
those two specifically, `Builtins_anyURI`/`Builtins_XMLLiteral`
require the declared datatype tag to actually match.

## Uniterm arity (0, 1) and internal encoding (added 2026-07-05)

`RIF.Core.Syntax` gained `RIF_Uniterm : rif_term -> list rif_term ->
rif_atom` for generic positional atoms `p(a1 ... an)` whose arity is
NOT 2 (arity-2 still routes through the pre-existing `RIF_Triple`,
unchanged). Arity 0 (`p()`, e.g. the Builtins_\* battery's `ex:ok()`)
and arity 1 (`p(a)`, e.g. `Positional_Arguments`' `ex:gold(?Customer)`,
`Chaining_strategy_numeric-add_1`'s `ex:a(?x)`) are given a translation
in `RIF.Core.Translation.translate_atom`; arity ≥ 3 has none (no
vendored fixture needs it). Internal-only encoding, never exposed to
any external RDF-semantics check, shared by both the assertion side
(`RIF.Core.Eval.instantiate_atom`) and the query side
(`translate_atom`) so it round-trips correctly:

```
p()   ==>  (rif_uniterm_nullary_subject, p, rif_uniterm_true_marker)
p(a)  ==>  (rif_uniterm_nullary_subject, p, a)
```

The argument goes in OBJECT position (not subject) specifically so a
rule body like `ex:a(?x)` correctly binds `?x` to its genuine value
(needed for `Chaining_strategy_numeric-add_1`/`_2`'s builtin-function
chaining) rather than an opaque marker, and so a literal argument
(`ex:gold("John Doe")`) needs no special-casing at all (object
position has no literal restriction). `RIF_Triple`'s arity-2 case
additionally uses a lenient subject conversion
(`rif_term_to_uniterm_subject`/`resolve_uniterm_subject`) that maps a
literal-valued first argument to a deterministic blank node
(`literal_subject_bnode_label`) rather than rejecting it outright —
sound for GROUND assert/ASK-query use (`Positional_Arguments`'
`ex:discount("John Doe" 10)`), but NOT value-preserving if that
relation is later queried in a rule BODY with a variable in that
position (`Factorial_Forward_Chaining`'s `ex:factorial(?N1 ?F1)` — see
the KNOWN-GAP note in the Score section below). `RIF_Frame`/
`RIF_Member`/`RIF_Sub` keep the original STRICT `rif_term_to_subject`/
`resolve_subject` (a literal subject there is a genuine RDF-in-RIF
combination typing error, matching SPARQL CONSTRUCT §16.2's
silent-drop convention).

## RIF Core conformance checking (added 2026-07-05)

New module `RIF.Core.Conformance.fst` — structural analysis directly
over `Parser.XML`'s `xml_node` tree (independent of
`RIF.Core.Syntax`/`Translation`/`Eval`, since it needs to reason about
constructs, `Or`/`Exists`/`External`/`Equal`, this project does not
give full entailment semantics to):

- **Safeness + "no free variables"** (`check_document_safe`, W3C RIF
  Core §6.1): a rule is safe iff every variable in its head, and
  every variable anywhere in its body, is "bound" — computed as a
  fixpoint over the body's And/Or/Exists/Equal/External/ordinary-atom
  structure (`bound_closure`; And unions each conjunct's contribution
  to a fixpoint, since Equal chains like `?x=?y, ?y=?z` need several
  passes; Or requires safety in EVERY disjunct given the same incoming
  context; External looks up a per-builtin BINDING PATTERN table —
  most RIF-DTB builtins require every argument pre-bound, but
  `pred:iri-string`/`pred:list-contains` have an alternate pattern
  that lets them PRODUCE a binding, e.g. `Core_Safeness_3`'s
  `External(pred:iri-string(?x ?z))` with `?z` bound and `?x` not).
  Separately, every `<Var>` occurring outside a `<declare>` must be
  declared by SOME `<Forall>`/`<Exists>` in the document
  (`no_free_variables` — `No_free_variables`'s `?price` is used but
  never declared).
- **Import-rejection** (§5): per-fixture dispatch to the specific
  RIF-RDF/OWL combination-spec condition each exercises —
  `has_variable_frame_property` (OWL-Direct requires every Frame
  slot's property to be a constant, not a variable —
  `OWL_Combination_Invalid_DL_Formula`), `imported_graph_is_empty`
  (OWL-Direct + an empty imported graph can't be a valid OWL 2 DL
  ontology — `OWL_Combination_Invalid_DL_Import`, narrow by design,
  matching that fixture's own stated criterion),
  `graph_has_forbidden_rif_datatype` (`rif:iri`/`rdf:PlainLiteral`
  typed literals are not permitted in an imported RDF graph —
  `RDF_Combination_Invalid_Constant_1`/`_2`), and
  `has_incomparable_profile_pair` (Simple/RDF/RDFS form one comparable
  chain; OWL-Direct is a separate, incomparable branch —
  `RDF_Combination_Invalid_Profiles_1`). `Multiple_Context_Error`
  (a non-`rif:local` constant used in more than one syntactic role —
  Uniterm-predicate vs. Frame-slot-property — across the imports
  closure) is checked since 2026-07-10 by
  `multiple_context_violation_xml`, a role collection over the RAW
  XML trees of every document in the closure (see the Score section's
  disposition table for why XML-level rather than Syntax-level).

## Score

**History: 13 pass, 1 fail, 36 skip (of 50) before 2026-07-05's
External/safeness/import-rejection/arity work; 34 pass, 4 fail, 12
skip after it.** Current, measured 2026-07-10 (the tail-burndown
wave):

- **Part 1 (original 4 vendored SPARQL-manifest cases): 4 pass, 0 fail (out of 4).**
- **Part 2 (vendored W3C RIF Core dialect corpus): 42 pass, 0 fail, 1 local-override, 3 skip (out of 46).**
- **Combined: 46 pass, 0 fail, 1 local-override, 3 skip (out of 50).**

The one remaining non-pass in Part 2 (`RDF_Combination_Constant_Equivalence_4`) is a **corpus data defect**, not an engine gap. As of 2026-07-17 it is dispositioned via a **local override**
(`tests/local-overrides/rif/RDF_Combination_Constant_Equivalence_4.override`) — a documented, distinctly-counted disagreement with a defective fixture (see `tests/local-overrides/README.md`). The runner reports it on an `OVERRIDE` line (still printing the observed `entailed=false`), counts it separately from both passes and fails, and **now exits 0** (no undispositioned reds). If a future change ever makes that test pass on its own, the runner prints a plain `PASS` and flags the override as stale/removable — an override never masks a success.

### The 2026-07-10 tail burndown (34/4/12 -> 46/1/3)

Per-test dispositions of the 4 fails + 12 skips that made up the
2026-07-05 tail:

| Test (was) | Now | How |
|---|---|---|
| Factorial_Forward_Chaining (KNOWN-GAP FAIL) | **PASS** | Uniterm ARGUMENT-VALUE satellites: `instantiate_atom_all` emits `(enc(a1), urn:rif-uniterm:arg1, a1)` alongside the classic arity-2 triple; a body atom with a VARIABLE first argument joins through the satellite and re-binds the genuine literal value (RIF.Core.Translation §1c + RIF.Core.Eval §1b) |
| Local_Constant, Local_Predicate (KNOWN-GAP FAILs) | **PASS** | rif:local constants are document-scoped per RIF-BLD §3.3: `Parser.RIFXML.scope_local_constants` renames `urn:rif-local:<lex>` to `urn:rif-local:<scope>:<lex>`; the runner parses premise and conclusion under different scopes |
| RDF_Combination_Constant_Equivalence_4 (KNOWN-DEFECT FAIL) | **LOCAL-OVERRIDE (2026-07-17)** | Both the zip's import files AND the archived authoritative wiki source (re-checked 2026-07-17) declare a malformed datatype IRI (a Windows local path `file:///C:/.../XMLSchema#string` in the RDF/XML, a scheme-less `www.w3.org/2001/XMLSchema#` prefix in the Turtle) that does not match the conclusion's `xsd:string`; under a correct datatype-IRI comparison the test genuinely does not entail. The pipeline fully processes it end to end and correctly returns `entailed=false`. Now dispositioned via `tests/local-overrides/rif/RDF_Combination_Constant_Equivalence_4.override` (distinctly counted, exit 0) rather than left a red |
| Builtins_String (skip: is-literal-string) | **PASS** | full RIF-DTB string family in RIF.Core.Builtins: compare/concat/string-join/substring/string-length/upper-case/lower-case/encode-for-uri/iri-to-uri/escape-html-uri/substring-before/-after/replace (via the SPARQL REPLACE regex realisation), contains/starts-with/ends-with/matches, and VALUE-SPACE is-literal-\<T\> for the xsd:string-derived datatypes (string/normalizedString/token/language/Name/NCName/NMTOKEN) |
| Builtins_PlainLiteral (skip: is-literal-PlainLiteral) | **PASS** | rdf:PlainLiteral family over the DECODED xsd:string/rdf:langString form: PlainLiteral-from-string-lang, string-from-PlainLiteral, lang-from-PlainLiteral, PlainLiteral-compare, matches-language-range, is-literal-(not-)PlainLiteral, and the rdf:PlainLiteral constructor cast |
| EBusiness_Contract (skip: is-literal-dateTime) | **PASS** | the dateTime slice: is-literal-dateTime (accepting xs:date operands at midnight — the Approved fixture itself applies dateTime guards to `"2008-07-22Z"^^xs:date` and expects them to hold), func:subtract-dateTimes -> xsd:dayTimeDuration, func:days-from-duration; plus n-ary reification for its arity-3 `cpt:delivered` relation |
| Builtins_Time (skip: is-literal-date) | **SKIP (named)** | the full date/time/duration family is ~60 builtins (add/subtract/multiply/divide durations, timezone-from-\*, year-from-\*, ...); only the EBusiness slice is implemented. The skip names the first unimplemented builtin (currently is-literal-dateTimeStamp) |
| IRI_from_RDF_Literal (skip: Exists) | **PASS** | \<Exists\>-quantified conclusions parse (declared vars stay free; the entailment ASK treats free variables existentially) + pred:iri-string's alternate BINDING-PATTERN execution (`RIF.Core.Eval.apply_iri_string_binding` produces `?z := <iri>` from a bound string) |
| RDF_Combination_Blank_Node corpus twin (skip: Exists) | **PASS** | the \<Exists\> conclusion parse above (Part 1's rif06 already passed via the SPARQL-manifest path) |
| OWL_Combination_Vocabulary_Separation_Inconsistency_1, _2 (skips: Equal conclusion) | **PASS** | `RIF.Core.Conformance.owl_direct_separation_inconsistent` detects the two OWL-Direct individual/data-value vocabulary-separation violations the fixtures exercise (an individual typed as an XSD datatype; a declared owl:ObjectProperty valued by a literal); an inconsistent combination entails everything, including the `"a" = "b"` conclusion. Narrow by design — not a general OWL 2 DL consistency checker |
| Multiple_Context_Error (skip: cross-document role tracking) | **PASS** | `RIF.Core.Conformance.multiple_context_violation_xml` collects Uniterm-\<op\> predicate IRIs and \<Frame\> slot-property IRIs over the RAW XML trees of the imports closure and rejects on overlap (`ex:discount` in both roles). XML-level because the imported document's multi-slot-frame rule HEAD is not a shape the rule parser accepts — the conformance check must not depend on evaluability |
| RDF_Combination_Constant_Equivalence_Graph_Entailment (skip: conclusion not in zip) | **PASS** | this test's conclusion is an RDF GRAPH, not a RIF condition — a `-conclusion.rif` never existed (404 in the earliest Wayback captures). The conclusion Turtle is vendored from the archived W3C wiki (see the PROVENANCE.md next to it) and the runner evaluates graph-entailment conclusions via `RIF.Core.Translation.graph_to_bgp` |
| Builtins_List, NestedListsAreNotFlatLists (skips: List) | **SKIP (named)** | RIF List terms are not modelled in RIF.Core.Syntax — a real syntax/translation/eval extension, not attempted this wave |

Score deltas verified with a fail-set diff at every step: no
previously-passing test regressed at any point (fail set shrank
monotonically {4 fails} -> {1 fail}; Part 1 4/4 and the SPARQL
631 pass, 0 fail / RDF 1031 pass, 0 fail floors held on the same
rebuilt binaries).

### Architecture notes for the 2026-07-10 wave

- **Uniterm satellites + n-ary reification** (RIF.Core.Translation
  §1c, RIF.Core.Eval §1b): arity-2 facts now also assert
  `(enc(a1), urn:rif-uniterm:arg1, a1)`; arity >= 3 facts reify as
  `(anchor, p, true)` + one `urn:rif-uniterm:arg<i>` satellite per
  argument, with the anchor a deterministic function of the
  predicate + argument values. Body atoms with variable first
  arguments (arity 2) or any arity >= 3 shape translate to the
  corresponding joins. The Eval saturation lemma (fixpoint never
  removes triples) was extended to the list-of-triples head firing.
  The Eval smoke test's transitivity rules moved from RIF_Triple to
  RIF_Frame — matching RAW RDF triples is the FRAME shape per the
  RIF-RDF combination spec; a variable-first-argument RIF_Triple is
  now the arity-2 Uniterm shape and joins through its satellite.
- **String-family is-literal-\<T\> is VALUE-SPACE membership**: the
  argument must denote a string at all (its own datatype is in the
  string family — `is-literal-not-normalizedString("1"^^xs:integer)`
  holds because the integer 1 is not a string value), and the string
  must satisfy T's facets. This is the third dispatch category next
  to the lexical-space (numeric/binary) and declared-tag
  (anyURI/XMLLiteral) categories from 2026-07-05.
- **func:substring corpus quirk, preserved deliberately**: the
  Approved Builtins_String fixture expects `substring("foobar", 3) =
  "bar"` (0-based) but `substring("foobar", 0, 3) = "fo"` (XPath
  1-based window) — the two forms disagree on base; the fixture is
  the authority (see fn_rif_substring2/3's comment).
- **rif:local scoping**: `scope_local_constants` is a post-parse
  rename over the program (no parser threading); locals WITHIN one
  document keep joining, cross-document same-lexical locals no
  longer conflate.

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

`OWL.DirectMapping.Filter.fst` and (2026-07-05) `RIF.Core.Builtins.fst`
/ `RIF.Core.Conformance.fst` are all wired into `build-ocaml.sh`'s
`ALL_MODULES`/`COMMON_MODULES`/`FSTAR_MODULES` lists — a plain
`./build-ocaml.sh extract` (or the targeted single-module loop in the
`fast-verify-extract` skill) picks them up with no manual list
surgery needed.

## Cross-references

- Migration epic: [#200](https://github.com/danbri/factoidal/issues/200) Section D
- Pattern reference: `bin/owl-runner/README.md`, `bin/w3c-runner/README.md`
- `formal/fstar/RIF.Core.Eval.fst`, `RIF.Core.Translation.fst`,
  `RIF.Core.Syntax.fst`, `Parser.RIFXML.fst`
