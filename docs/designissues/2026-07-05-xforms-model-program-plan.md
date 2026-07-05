# XForms model-layer program plan ("browserless XForms")

Scoping doc for a verified XForms **computation model** — the
instance + binds + dependency graph + recalculation engine defined by
XForms 1.1/2.0 (§4, §6-§7), deliberately **without** the submission
layer (§11) or the UI/controls/actions layers (§8-§10, §12). Modeled
on the stage structure in
[`2026-07-05-rml-program-plan.md`](2026-07-05-rml-program-plan.md),
[`2026-07-05-vc-program-plan.md`](2026-07-05-vc-program-plan.md), and
[`2026-07-05-csvw-program-plan.md`](2026-07-05-csvw-program-plan.md).

## Owner directive and scope fence

XForms conflates four largely-orthogonal concerns: (1) an XML
instance document plus a *binding* layer (`xf:bind`) that computes
derived values and validity from it — the "spreadsheet" half; (2)
UI controls (`xf:input`, `xf:repeat`, …) that render bound nodes;
(3) XML Events/actions (`xf:setvalue`, `xf:dispatch`, …) that mutate
state on user interaction; (4) submission (`xf:submission`) that
sends the instance somewhere over HTTP. This program takes **only
(1)**: instance + binds → dependency graph → recalculation, expressed
as a pure function from an edit to a new state plus a validity
report. No UI controls, no `xf:repeat`, no XML Events/actions, no
submission — egress is the FP npm API returning data (Stage 3),
consumed by hand-written Observable cells in a docs-hub demo
(Stage 4), not by a submission POST. This is explicitly **not
conformant XForms** — it is the reactive core XForms bundles with a
UI and transport layer this project has no interest in rebuilding.

Why this is in scope for an RDF/SPARQL engine project at all: the
"spreadsheet" model (declarative binds, dependency-driven
recalculation, typed validation) is a generically useful pure
computation over XML that this project's `Parser.XML.fst` AST already
supports as an input format, and Stage 1's XPath 1.0 engine has a
second, independent consumer already named in this codebase's own
backlog (see "Dual-use" below) — so the XPath investment pays for
itself twice even if the XForms bind/recalc layers (Stages 2-4) never
ship.

## Stages

| Stage | Deliverable | Acceptance criteria | Gate |
|---|---|---|---|
| 1 | `Parser.XPath.fst` + `XPath.Eval.fst` — XPath 1.0 core (expression parser + evaluator over `Parser.XML`'s `xml_node`) | **This task.** Verifies under z3 4.13.3, no `--lax`/`--admit_smt_queries`. Spec-clause-cited unit test suite (this program's own, no vendored corpus — see "Test suite" below), scored as "N pass, N fail (of N)". Axis/function coverage table published (see the accompanying implementation report). No dependents yet — this stage is a leaf, useful on its own to RML's XML source gap (see Dual-use). | none |
| 2 | Bind/recalc engine (`XForms.Bind.fst` or similarly named) | Binds = XPath-selected node sets carrying `calculate`/`constraint`/`relevant`/`required`/`readonly`/`type` properties (XForms 1.1 §7.3-§7.8). Dependency graph extracted from `calculate` expressions' node-set references (which binds' computed values feed which other binds — the same "reactive recomputation" problem a spreadsheet solves for cell formulas). **Cycle detection is spec-required, not optional** (XForms 1.1 §7.6.1's `xforms-compute-exception`/recalculate ordering assumes an acyclic graph; a `calculate` cycle is a document error) — implemented as an F\* **termination proof**: recalculation is a fold over a topologically-sorted bind list, fuel bounded by the dependency DAG's depth (the standard `decreases` idiom this codebase already uses for fuel-bounded fixpoints, e.g. `SHACL.Validation.fst`'s closure loop), so an attempted cyclic recalculation is rejected structurally rather than looping. Recalculation itself is a pure function `old_state -> edit -> (new_state & validity_report)` — no I/O, no mutation, matching the owner directive's "engine must be pure." Validation reuses `XSD.Datatypes.fst`'s existing datatype checks (the `type` MIP dispatches to XSD facet/lexical validation already built for SHACL/CSVW) rather than a new type-checking layer. | Stage 1 |
| 3 | FP npm API surface, mirroring `fn.js`'s existing style | `xformsModel(instanceXml, bindingsSpec)` returns an immutable handle (parses instance via extracted `Parser.XML`, binds via extracted bind-decoder, builds the dependency graph once). `setValue(handle, xpath, value)` returns `{instance, validity, changed[]}` — a pure snapshot-in/snapshot-out call, no submission, no side effect beyond the returned value (egress is the return value itself, per the owner directive). `changed[]` is the recalculation fold's touched-bind list, letting a UI layer (Observable, React, whatever) know which cells to re-render without a full re-diff. | Stage 2 |
| 4 | Docs-hub demo post with live Observable cells | A hub post embeds the vendored Observable runtime (already used elsewhere in the docs hub per `site-and-dashboard`) driving `xformsModel`/`setValue` from Stage 3 live in the browser — an instance + a bind sheet + an editable cell that shows recalculation ripple through dependent binds, no server round-trip. | Stage 3 |

## Dual-use: the Stage 1 XPath engine also unlocks RML's XML source

[`2026-07-05-rml-program-plan.md`](2026-07-05-rml-program-plan.md)'s
Module plan section (`RML.Sources.fst`) and its Staged plan Stage 4
row both name an XPath-subset evaluator over `Parser.XML`'s
`xml_node` as an explicit, not-yet-built gap: "Only an XPath subset
evaluator is new" (Fit section), and Stage 4's row reads "XPath
subset + XML logical source | `rml-io`'s XML-sourced `RMLSTC0*` tests
(~7 of 32) | Stage 2" — still unbuilt as of this plan's writing (RML's
own Stage 3 closed CSV, Stage 4 XPath/XML remains open). That plan's
own corpus survey found RML's actual XPath usage narrow — "child-axis
steps..., one instance of a descendant shorthand (`//Friends/
Character`), and `text()` leaf references..., no predicates, no axes
beyond child/descendant, no functions besides `text()`" — a strict
subset of what Stage 1 here builds (full axis set, predicates,
the core function library). **This program's Stage 1 output is a
superset of what RML's Stage 4 needs**; RML's Stage 4, whenever it
lands, should consume `Parser.XPath`/`XPath.Eval` directly rather than
writing a second, narrower XPath evaluator — flagged here so whichever
program reaches its own Stage 4/1 gate first does not duplicate the
other's work (same "coordinate, don't duplicate" posture the CSVW plan
took toward RML's CSV tokenizer).

## Test suite: no standalone W3C XPath 1.0 corpus exists

Checked directly rather than assumed, per this series' own
discipline: **there is no dedicated W3C XPath 1.0 conformance test
suite.** The landscape:

- **QT3 test suite** (`w3c/qt3tests`, the suite behind
  `w3.org/TR/xpath-functions-31`-family conformance dashboards)
  targets **XPath/XQuery 3.1** (and predecessors 2.0/3.0) — it tests
  the FLWOR-capable, typed, XSD-schema-aware successor language, not
  XPath 1.0's untyped four-type-system core this stage implements.
  Many XPath 1.0 constructs (axes, node tests, the core function
  subset this stage covers) survive unchanged into 3.1, but the QT3
  fixtures are written against 3.1 semantics (sequences instead of
  node-sets, `xs:` schema types, `+`/`-` on nodes without XPath 1.0's
  string/number coercion quirks) and would need non-trivial
  back-porting or cherry-picking to serve as XPath 1.0 fixtures, not
  a drop-in vendor.
- **XPath 1.0 conformance historically rode inside the OASIS/W3C XSLT
  1.0 test suite** (XSLT stylesheets exercise XPath expressions as
  part of templates; there was never a standalone "XPath 1.0 test
  suite" published by the W3C XSL/XML Query WGs). The XSLT 1.0
  conformance corpus most commonly cited today is the **OASIS/NIST
  XSLT conformance suite** (via `xmlsoft.org`'s mirrored copy or the
  historical `oasis-open.org/committees/xslt-conformance` archive) —
  every test case is a full stylesheet transform (source XML +
  `.xsl` + expected output), so XPath coverage is diffused across
  ~2000 XSLT test cases and entangled with template matching, `xsl:
  for-each`, output serialization, and XSLT's own extension
  functions — none of which this program builds. Extracting "just the
  XPath-expression-shaped assertions" from that corpus is a
  significant filtering/curation project of its own, disproportionate
  to Stage 1's scope.

**Decision for Stage 1: spec-clause-cited unit tests, own corpus, no
vendored suite** — the same fallback posture `VC`'s plan takes for
its cryptosuite stages (hand-derived fixtures) when no offline W3C
corpus exists. Every test in this stage's test executable names the
XPath 1.0 section it exercises in its test name/comment (e.g. "§3.4
number = node-set comparison"), which is the honest substitute for a
vendored pass/fail scoreboard: there is no "N of M" upstream corpus to
report against, only "N pass, N fail (of N)" against a hand-built,
cited set.

**Options for a vendored suite, deferred, not decided here:**

1. **Do nothing further** — keep the hand-written spec-cited unit
   suite as the permanent conformance signal for this narrow XPath
   1.0 subset. Cheapest, matches the reality that no better corpus
   exists in a directly-usable shape.
2. **Curate a small XPath-only extract from the OASIS XSLT suite** —
   scan the ~2000 XSLT test cases for ones whose `<xsl:value-of
   select="...">`/`<xsl:if test="...">` expressions exercise a single
   isolable XPath feature, and hand-lift those expressions (plus their
   source XML fixture and expected string output) into a small local
   fixture set, citing provenance per test. Nontrivial curation labor,
   not scheduled.
3. **Track QT3/XPath 3.1 fixtures as a stretch, once XPath 2.0+ is
   ever in scope** — if this project later builds an XPath 2.0/3.x
   evaluator (a much larger undertaking, not implied by this plan),
   revisit QT3 as the real vendored target then; it is not a fit for
   the 1.0-only engine built here.

Revisit this list if the owner wants an upstream-badge-style score
before shipping the docs-hub demo (Stage 4); none of Stages 1-4 above
are gated on resolving it.

## Number semantics

XPath 1.0 numbers are defined as IEEE 754 double-precision floating
point (§1: "A number represents a floating-point number... using the
double type defined in [IEEE 754]"). This codebase's SPARQL evaluator
does **not** carry a bit-level IEEE double type anywhere — `SPARQL11.
Algebra.fst`'s `ER_Dbl` promotes `xsd:double` values to a **lexical
string** wrapping a scaled-decimal pair `(int, nat)` (`parse_to_scaled`
/`parse_double_to_scaled`, lines ~1281-1400), i.e. an arbitrary-
precision rational approximation formatted through decimal string
conversion, not a 64-bit float register. `XPath.Eval.fst`'s number
type (`xpath_number`) follows the **same representation strategy**
(a signed-mantissa/scale pair, `XN_Finite : value:int -> scale:nat ->
xpath_number`) rather than inventing a third numeric encoding, per the
brief's instruction to reuse the promoted-type approach — but it does
**not** import `SPARQL11.Algebra` directly (kept out of this stage's
two-file territory; the shared representation is a design choice, not
a code dependency). Two explicit, disclosed divergences from strict
IEEE 754 follow from this choice:

1. **No signed zero.** IEEE 754 distinguishes `+0.0` from `-0.0`
   (`1 div -0` differs in sign from `1 div 0`); this program's
   `XN_Finite` mantissa is a plain `int`, so `-0` normalizes to `0`
   and the two are indistinguishable. `1 div 0` and `1 div -0` both
   produce `XN_PosInf` (or would, if the divisor's literal sign were
   trackable) — flagged here rather than silently wrong; a fixture
   exercising `-0`'s sign specifically is not in this stage's test
   list.
2. **NaN/Infinity are tagged sentinels, not float bit patterns.**
   `xpath_number` is `XN_NaN | XN_PosInf | XN_NegInf | XN_Finite int
   nat` — arithmetic on `XN_Finite` values is exact rational
   arithmetic (scaled-decimal, same as SPARQL's), not binary
   floating-point rounding, so this engine cannot reproduce IEEE 754's
   rounding-error behavior (e.g. `0.1 + 0.2 <> 0.3` in real double
   arithmetic; here `0.1 + 0.2 = 0.3` exactly, since scaled-decimal
   arithmetic is exact where representable). This is a **materially
   more precise** result for any XPath expression that stays within
   the scaled-decimal representation's precision, at the cost of not
   bit-matching a real IEEE 754 implementation's rounding artifacts on
   pathological inputs. Documented, not silently assumed.

`string(number)` formatting follows XPath 1.0 §4.4's stated rules
(NaN → `"NaN"`, positive/negative infinity → `"Infinity"`/
`"-Infinity"`, integers print without a decimal point, non-integers
print in plain decimal — XPath 1.0 number *literals* have no
E-notation in their own grammar, unlike `xsd:double`'s lexical space,
so `number()` string-to-number conversion also does not accept
E-notation per the grammar's `Number ::= Digits ('.' Digits?)? | '.'
Digits` production; this is *not* a limitation introduced by this
engine — it is what the spec itself defines for the `Number`
production actually used by numeric literals and by `number()`'s
string-conversion grammar).

## Comparison semantics note (§3.4)

XPath 1.0 §3.4's node-set comparison rules are famously terse for the
relational operators (`<`, `<=`, `>`, `>=`) when one or both operands
are node-sets: the spec's literal wording ("the result of performing
the comparison on the string-values of the two nodes") is widely read
two ways by implementers. This engine follows the de facto standard
(and libxml2/most production XPath 1.0 engines') interpretation:
`=`/`!=` compare node-set string-values directly (existential over
node pairs); `<`/`<=`/`>`/`>=` involving a node-set convert the
node-set side's string-values to **numbers** before the existential
comparison (matching the "node-set and number" comparison rule
literally stated one paragraph earlier in the same section, applied
symmetrically). Cited here so a future reader auditing this engine's
`value_compare`-equivalent function does not mistake it for a spec
misreading.

## Module plan

- **`formal/fstar/Parser.XPath.fst`** — expression-text → AST parser.
  Uses `Parser.Combinators`/`Parser.FastString` the way `Parser.XML`
  does (byte-indexed scan for the ASCII-delimited grammar: operators,
  axis names, node-test syntax, numeric literals are all ASCII;
  string literals and name characters may carry non-ASCII bytes,
  passed through opaquely as substrings, same posture as `Parser.
  XML`'s attribute/text bodies). Full XPath 1.0 grammar for the
  scope below: `LocationPath`, `Step`, `AxisSpecifier` (abbreviated
  and full syntax), `NodeTest`, `Predicate`, `Expr` through its
  operator-precedence cascade (`OrExpr` → `AndExpr` → `EqualityExpr`
  → `RelationalExpr` → `AdditiveExpr` → `MultiplicativeExpr` →
  `UnaryExpr` → `UnionExpr` → `PathExpr` → `FilterExpr` →
  `PrimaryExpr`), `FunctionCall`, `VariableReference`, `Number`,
  `Literal`. A single mutually-recursive parser block, fuel threaded
  from input length (not a bare constant, per the extraction-semantics
  trap list) so termination is provable without an artificial
  expression-depth ceiling that could silently truncate a
  deeply-nested real-world bind expression.
- **`formal/fstar/XPath.Eval.fst`** — the evaluator. Context =
  `{ node-set item; position; size; variable bindings }` per XPath
  1.0 §1's context model. Node-set items are built from `Parser.
  XML`'s already-parsed `xml_node` tree via a context wrapper that
  threads the ancestor chain alongside each item (no global
  document-order index table needed — see the implementation report
  for why the ancestor-chain design makes `ancestor`/`ancestor-
  or-self`/`parent` axes structural recursions rather than a separate
  indexing pass). Result type = the four-way sum `node-set | boolean
  | number | string` XPath 1.0 §1 defines. Depends only on `Parser.
  XML` (for `xml_node`/`xml_attribute`) and `Parser.XPath` (for the
  AST) — no dependency on `SPARQL11.Algebra` (see Number semantics
  above for why the numeric representation is parallel, not shared,
  code).

## Open decisions

1. **Bind-language surface for Stage 2.** XForms binds can be
   expressed either inline (`ref`/`bind` attributes directly on
   controls — out of scope here, no controls) or via a standalone
   `<xf:bind>` tree under `<xf:model>`. Stage 2 should decode only the
   standalone `<xf:bind nodeset="..." calculate="..." .../>` tree
   shape (itself XML, parsed via the same `Parser.XML`), since that is
   the shape a headless/pure engine actually receives from Stage 3's
   `bindingsSpec` argument — confirm this covers whatever shape the
   Stage 3 npm API wants to expose before committing to a decode
   schema.
2. **Nested binds.** XForms allows `<xf:bind>` elements to nest
   (a child bind's `nodeset` is evaluated relative to its parent
   bind's matched node-set, XForms 1.1 §7.3). Decide at Stage 2
   whether nested-bind relative-nodeset resolution is in scope
   initially or deferred — it composes cleanly with Stage 1's
   node-set-valued expressions (a nested bind's `nodeset` evaluates
   against each item of the parent bind's resolved set) but adds a
   second dimension to the dependency-graph extraction algorithm.
3. **MIP conflict resolution.** XForms 1.1 §7.8.2 defines a specific
   resolution order when multiple binds target overlapping node-sets
   with contradictory Model Item Properties (e.g. two binds both
   setting `relevant` on the same node with different expressions).
   Decide at Stage 2 whether to implement the spec's full conflict
   table or start with "last bind wins" and cite the gap, mirroring
   this program-plan series' own "measure, then decide precisely" 
   posture rather than guessing ahead of a fixture.
4. **`type` MIP breadth vs. `XSD.Datatypes.fst` coverage.** The CSVW
   plan (this same series) already found `XSD.Datatypes.fst` covers
   only `dateTime` among the date/time family and no custom
   format-facet interpretation; whichever program (this one or CSVW's
   own Stage 4) extends `XSD.Datatypes` first should do so once, not
   twice — coordinate before Stage 2 needs `type="xsd:date"` or
   similar validation.
5a. **Union (`|`) does not deduplicate or sort into document order
   (§3.3's contract).** Stage 1's `XE_Union` is plain list
   concatenation of the two operand node-sets — correct for
   `count(a | b)` on disjoint sets (what this stage's own tests
   exercise) but over-counts / mis-orders when the two sides overlap.
   `xctx_item` is `noeq` (see the Module plan) so a document-order
   comparator needs a hand-written structural key, which is also
   exactly what a real fix for Open decision 5's following/preceding
   axes would need (a document-order index) — do both together in
   Stage 1.5 rather than half-fixing union alone.
5. **Following/preceding/sibling axes deferred to Stage 1.5.** Stage 1
   implements the eight axes the brief named as required (`child`,
   `descendant`, `descendant-or-self`, `parent`, `self`, `attribute`,
   `ancestor`, `ancestor-or-self`) plus documents the remaining four
   (`following`, `preceding`, `following-sibling`,
   `preceding-sibling`) as Stage 1.5, not Stage 1, to keep this
   stage's proof surface and test matrix bounded — see the
   implementation report for the exact reason they are tractable to
   add later (the same ancestor-chain-based item representation
   generalizes to them without a redesign, given a document-order
   flattening pass that Stage 1 does not build). `id()` and `lang()`
   are likewise deferred to Stage 1.5 per the brief.
