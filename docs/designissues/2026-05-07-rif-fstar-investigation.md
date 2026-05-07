# 2026-05-07 — F\* RIF engine investigation

## Status

Design investigation. Doc-only. Decision pending. No code lands until
the open questions in the final section are resolved by the user.

The current W3C SPARQL 1.1 score in
[`docs/test-results/latest.json`](../test-results/latest.json) is
626 pass, 1 fail, 4 skip (out of 631). All 4 skips are
RIF entailment-regime tests under the `entailment` suite. This
document explores whether a minimal F\*-verified RIF Core engine
can resolve those 4 skips, and at what cost.

## Background

### What is RIF

The W3C Rule Interchange Format (RIF) is a family of dialects for
exchanging rules between rule-based systems on the Web, published as
W3C Recommendations in 2013. The dialects are layered:

- RIF-Core — the Horn-rule subset shared by all RIF dialects. Maps
  cleanly onto Datalog with a fixed set of built-ins.
- RIF-BLD (Basic Logic Dialect) — Horn rules with equality, function
  symbols, and frame syntax. Strictly extends Core.
- RIF-PRD (Production Rule Dialect) — production rules with side
  effects (assert, retract, modify). Operationally distinct from
  Core/BLD.
- RIF-FLD (Framework for Logic Dialects) — meta-framework for
  defining new logic dialects; not a runnable system.

The relevant specs are
[RIF Core](https://www.w3.org/TR/rif-core/) and the
RDF-combination semantics in
[RIF RDF and OWL Compatibility](https://www.w3.org/TR/rif-rdf-owl/).
RIF Core has three concrete syntaxes: Presentation Syntax (human
notation), RIF-XML (interchange), and a mapping into RDF graphs.
The W3C test corpus uses RIF-XML.

### What the 4 skipped tests require

Source — `formal/fstar/ocaml-output/w3c_runner.ml:441-451`. The
runner detects the `sparql:entailmentRegime` IRI on each query and
tags `ent:RIF` / `ent:RIF-Core` regimes as `RIF-Skip`, returning
`Skip "RIF not implemented"`.

The 4 tests are all in the `entailment` suite of the W3C SPARQL 1.1
test corpus:

1. RIF Logical Entailment (referencing RIF XML)
2. RIF Core WG tests: Frames
3. RIF Core WG tests: Modeling Brain Anatomy
4. RIF Core WG tests: RDF Combination Blank Node

All four declare the `ent:RIF-Core` regime; none require BLD or PRD.
The test inputs reference RIF rule documents in RIF-XML, the data
graph is RDF, and the expected answer is the SPARQL solution set
under RIF-Core entailment of the data + rules combination.

The W3C RIF-Core test corpus is the wider source —
[RIF Test Cases wiki](https://www.w3.org/2005/rules/wiki/RIF_Test_Cases)
— and the SPARQL `entailment` suite picks four of those that have
SPARQL queries layered on top.

The actual RIF-XML rule files for the SPARQL `entailment` tests are
not currently in `third_party/testing/` (the SPARQL entailment test
directory in the local corpus is empty under
`third_party/testing/w3c/sparql/sparql11/entailment/`; the runner
discovers them via the upstream manifest at runtime). Vendoring
those test artefacts is a prerequisite to any code work and is part
of the "test-driven viability check" below.

### Why this might be in scope

The project mandate is "verified RDF/SPARQL from F\*". RIF Core
sits squarely on RDF — its semantics are defined as inference over
RDF graphs — and the four skipped tests are W3C SPARQL 1.1
entailment-regime tests. A small, verified RIF-Core engine that
reuses the existing SPARQL/algebra infrastructure would convert
4 skips into 4 passes without expanding the project's verified
surface much.

### Why this might NOT be in scope

RIF-XML is a non-trivial XML language with a schema, datatypes,
External calls to built-ins, and a mapping spec
([RIF/RDF/OWL](https://www.w3.org/TR/rif-rdf-owl/))
that has known edge cases (blank nodes in rule heads, equality
reasoning, datatype-aware unification). The verification cost of
a fixpoint inference engine in F\* is non-trivial. If the cost
exceeds "make 4 tests pass", the right move is to leave them
permanently skipped with a documented rationale.

## Scope decision: which RIF dialect

The minimum dialect that can pass the 4 SPARQL entailment-regime
tests is RIF-Core. Out of scope for this investigation:

- RIF-BLD — adds equality reasoning over arbitrary terms and
  function symbols. Would require congruence closure plus
  termination guarantees that do not hold in general.
- RIF-PRD — production-rule semantics with side effects. Does not
  fit the monotonic bottom-up Datalog evaluation model and would
  duplicate machinery already present in SPARQL Update.
- RIF-FLD — a meta-framework, not a runnable engine.

### What RIF-Core actually requires

From [RIF Core §2-§3](https://www.w3.org/TR/rif-core/), a minimal
viable engine needs:

1. Atomic formulas of the form `p(t1, ..., tn)` — but in the
   RDF-combination profile most atoms reduce to triples (binary
   atoms) or frames (see below).
2. Frame atoms `o[p1 -> v1; p2 -> v2; ...]` — syntactic sugar that
   compiles into one triple per slot under the RDF mapping
   ([RIF/RDF/OWL §5](https://www.w3.org/TR/rif-rdf-owl/#sec-rif-rdf)).
3. Class membership atoms `t # cls` and subclass atoms
   `c1 ## c2` — compile to `rdf:type` and `rdfs:subClassOf` triples.
4. Conjunction in rule bodies (`And(...)`).
5. Existential variables in rule bodies (`Exists ?x (...)`).
6. Universal rule quantification `Forall ?x (head :- body)`.
7. A small set of built-ins:
   `pred:numeric-equal`, `pred:numeric-less-than`, etc., plus the
   guard predicates from
   [RIF Datatypes and Built-Ins](https://www.w3.org/TR/rif-dtb/).
8. Datatype handling consistent with the existing SPARQL
   `xsd:integer` / `xsd:decimal` / `xsd:double` / `xsd:string`
   / `xsd:dateTime` infrastructure.

What RIF-Core explicitly excludes:

- Function symbols in rule heads (no Skolem functions, no list
  constructors). This is what makes Core Datalog-equivalent.
- Negation (no `Not`, no negation-as-failure).
- Equality in rule heads (no `=` as a producer).
- Production-rule actions.

Termination: RIF-Core programs are stratified Datalog modulo
built-ins. With finite RDF data and no function-symbol recursion,
the bottom-up fixpoint terminates in O(|rules| \* |data|^arity)
steps. This is the standard Datalog termination story and lines up
with the project's iron rule against `--lax` — termination is
provable, not assumed.

## SPARQL stack reuse map

Concrete mapping from RIF-Core concepts to existing F\* modules.
This is the load-bearing table — agents working the migration use
it to avoid duplicating machinery.

| RIF Core concept | F\* module that already covers it | Gap to fill |
|---|---|---|
| Atomic triple-shaped atom `p(s, o)` | `SPARQL11.Algebra.triple_pattern` (line 301) | None — direct reuse |
| Frame atom `s[p -> o]` | `SPARQL11.Algebra.triple_pattern` after expansion | Translation step (1 frame slot to 1 pattern) |
| Frame atom with multiple slots `s[p1->o1; p2->o2]` | `SPARQL11.Algebra.bgp` (line 358) | Translation: each slot to one pattern, conjoined |
| Class-membership `t # C` | `triple_pattern` with predicate fixed to `rdf:type` | Translation |
| Subclass `C1 ## C2` | `triple_pattern` with predicate `rdfs:subClassOf` | Translation |
| Conjunction `And(a1, ..., an)` in body | `bgp = list triple_pattern` | None — `bgp` is exactly conjunction |
| Body with filter built-in `pred:numeric-less-than` | `SPARQL11.Algebra.expr` + `GP_Filter` (line 506) | Translation: built-in IRI to SPARQL expr |
| Existential body variables | SPARQL evaluator already does this (variables in BGPs are existentially quantified) | None |
| Rule head as triple template | `SPARQL11.Algebra.QF_Construct` (line 566) | Use CONSTRUCT to materialise inferred triples |
| Variable binding from body to head | `solution_mapping` (lines 80-119) | None — exactly what SELECT already produces |
| Forward-chaining fixpoint | NEW — see proposed architecture | New module |
| RDF graph data model | `RDF.Graph.Executable.rdf_graph` | None — direct reuse |
| Dataset (default + named graphs) | `RDF.Graph.Executable.rdf_dataset` | None — RIF Core single-document case ignores named graphs |
| Datatype-aware equality | SPARQL evaluator's `eval_result` + numeric promotion (line 730, 1226) | Reuse via SPARQL filter expr lowering |
| Rule-application trace | `SPARQL.Diagnostics` and `SPARQL.Explain` | Optional: derived-triple provenance |
| RIF-XML concrete syntax parser | `Parser.RDFXML` shares XML scaffolding; `Parser.XML` if present | New (RIF-XML is its own grammar) |

The load-bearing observation: a RIF-Core rule
`Forall ?x ?y (head(?x, ?y) :- body(?x, ?y))` is exactly
`CONSTRUCT { head_template } WHERE { body_bgp }` in SPARQL 1.1.
Forward chaining is repeated CONSTRUCT-and-merge until fixpoint.
The SPARQL evaluator already does CONSTRUCT correctly; the new
work is the fixpoint loop and the RIF-XML parser.

The OWL-RL closure and `OWL.QueryRewrite` / `OWL.QueryEval` are the
existing precedent: an extra entailment regime layered on top of
the SPARQL evaluator. RIF-Core would follow the same pattern.

## Proposed architecture

```
formal/fstar/RIF.Core.Syntax.fst       -- ADT for RIF Core rule, atom, frame
formal/fstar/RIF.Core.Translation.fst  -- RIF Core to SPARQL 1.1 algebra
formal/fstar/RIF.Core.Eval.fst         -- forward-chaining fixpoint
                                          (built on SPARQL evaluator)
formal/fstar/Parser.RIFXML.fst         -- RIF-XML concrete syntax parser
                                          (extends Parser.XML scaffolding)
formal/fstar/RIF.Core.Tests.fst        -- W3C RIF Core test runner shim
```

### `RIF.Core.Syntax.fst`

The verified ADT for RIF-Core. Defines:

```
type rif_term =
  | RT_Var      : string -> rif_term
  | RT_Const    : rdf_term -> rif_term       // reuse RDF.Graph.Executable
  | RT_Frame    : rif_term -> list (rif_term * rif_term) -> rif_term

type rif_atom =
  | RA_Triple   : rif_term -> rif_term -> rif_term -> rif_atom
  | RA_Frame    : rif_term -> list (rif_term * rif_term) -> rif_atom
  | RA_Member   : rif_term -> rif_term -> rif_atom        // t # C
  | RA_Subclass : rif_term -> rif_term -> rif_atom        // c1 ## c2
  | RA_Builtin  : wf_iri -> list rif_term -> rif_atom

type rif_body =
  | RB_Atom     : rif_atom -> rif_body
  | RB_And      : list rif_body -> rif_body
  | RB_Exists   : list string -> rif_body -> rif_body

noeq type rif_rule = {
  vars : list string;       // universally quantified
  head : rif_atom;          // RIF Core: head is a single atom
  body : rif_body;
}

type rif_program = list rif_rule
```

This module is pure Tot and verifies trivially. It sits above
`RDF.Graph.Executable` and below everything else. Sized roughly
80-150 LoC including dataype IRIs and basic equality predicates.

### `RIF.Core.Translation.fst`

Compiles a `rif_rule` to a pair `(triple_pattern_list, bgp)` —
the head template and the body BGP — suitable for feeding to the
existing SPARQL evaluator's CONSTRUCT path. Built-ins in the body
become `expr` filter clauses. Frames decompose into one triple per
slot per [RIF/RDF/OWL §5](https://www.w3.org/TR/rif-rdf-owl/#sec-rif-rdf).
Existential body variables are SPARQL fresh variables.

```
val translate_rule
  : rif_rule
  -> Tot (list triple_pattern * group_graph_pattern)
```

No fixpoint, no graph state — pure translation. Sized roughly
200-300 LoC. Verifies if the input ADT is well-formed; the result
is consumed only by the evaluator that already verifies its own
inputs.

### `RIF.Core.Eval.fst`

The fixpoint loop. Repeatedly:

1. For each rule, run the translated CONSTRUCT against the current
   graph using the existing SPARQL evaluator (`eval_construct_query`
   or its OWL analogue).
2. Take the union of the resulting triples, merge with the current
   graph using set semantics.
3. Repeat until no new triples appear (fixpoint reached) or the
   step cap is hit (safety net).

```
val rif_closure
  : rif_program
  -> rdf_graph
  -> n:nat              // step cap (fuel)
  -> Tot rdf_graph

val rif_entails
  : rif_program
  -> rdf_graph
  -> rif_atom           // ground atom to check
  -> n:nat
  -> Tot bool
```

The fuel-bounded form keeps the function `Tot` (total) without
needing a termination metric on the abstract closure. Verification
strategy is discussed below.

Sized roughly 300-500 LoC including the convergence test and the
graph-union helper. The convergence test reuses
`RDF.Graph.Executable`'s graph equality.

### `Parser.RIFXML.fst`

Parses the RIF-XML concrete syntax into `rif_program`. RIF-XML is
not RDF/XML — it has its own grammar described in
[RIF Core §A](https://www.w3.org/TR/rif-core/#XML_Serialization).
The parser can reuse XML-tokenisation infrastructure shared with
`Parser.RDFXML` if a generic `Parser.XML` layer is factored out;
otherwise it ships its own scanner.

Scope-limit: parse only the subset of RIF-XML actually exercised
by the 4 SPARQL `entailment` test inputs. Document the unparsed
features as `assume val` ... no, do not — per iron rule 4 the
parser must be in F\*, so the unparsed features become explicit
parse errors that fail loudly rather than silent gaps.

Sized roughly 400-700 LoC depending on subset. The W3C RIF-Core
WG tests use a fairly small slice.

### `RIF.Core.Tests.fst`

The runner shim. For each `RIF-Core` regime test:

1. Parse the data graph (Turtle / RDF-XML — already supported).
2. Parse the RIF-XML rule document via `Parser.RIFXML`.
3. Compute the closure under `rif_closure` with a sensible fuel.
4. Run the SPARQL query in the test against the closed graph
   using the existing evaluator.
5. Compare the result to the expected `.srx` / `.csv` / `.tsv`.

This module replaces the `RIF-Skip` tag in
`formal/fstar/ocaml-output/w3c_runner.ml:441-451` and is the
extraction point. The runner shim itself is verified F\* like the
other test runners. The OCaml `w3c_runner.ml` continues to do
filesystem I/O and dispatch only.

Sized roughly 100-150 LoC.

## Termination + verification story

RIF-Core programs without function symbols are Datalog. Datalog
fixpoint computation terminates because the Herbrand base over
finite data is finite and rule application is monotonic — every
step adds triples or stops. The number of steps is bounded by
|Herbrand base| which is bounded by |constants in data ∪ rules|
to the maximum predicate arity (here mostly 2 — RDF triples).

For F\* verification, three options, in order of increasing
formal cost:

### Option A: Fuel-bounded fixpoint (recommended)

The public `rif_closure` takes an explicit `n:nat` step cap and
recurses on `n`. Termination is automatic — `n` is the
well-founded measure. A separate lemma proves "if `n` is at least
the Herbrand-base size, the result is a fixpoint":

```
val rif_closure_is_fixpoint_at_bound
  : program:rif_program
  -> g:rdf_graph
  -> Lemma
      (let bound = herbrand_size program g in
       let closed = rif_closure program g bound in
       rif_closure program closed 1 = closed)
```

This is the same pattern as the existing OWL-RL closure and the
project's other fuel-bounded `Tot` functions. Verifies with the
existing z3 setup, no `--lax`. Effort: low.

### Option B: Refinement type for "Datalog program"

Define a refinement
`type datalog_program = p:rif_program{no_function_symbols p}`
and prove an unconditional termination lemma for the closure on
that subset. More elegant; modestly more verification cost; the
syntactic check is `Tot bool` and easy.

### Option C: Hard step cap as runtime guard only

Punt on the lemma, ship Option A with a configurable cap, and add
a runtime warning if the cap is hit. This is what the W3C SPARQL
test corpus likely exercises (small rule sets, small data) but
provides no formal guarantee. Not recommended given iron rule 10.

Recommendation: Option A, with Option B layered on top once the 4
tests pass. The fuel-bounded fixpoint is enough for the W3C tests
and verifies cleanly. The "Datalog refinement" lemma can land in a
follow-up without changing the public API.

## Test-driven viability check

Before any code lands, verify the 4 skipped tests are actually
RIF-Core (not BLD or PRD), and inventory their inputs.

### Step 1: locate the test artefacts

The local SPARQL `entailment` test directory under
`third_party/testing/w3c/sparql/sparql11/entailment/` is currently
empty in this worktree. The runner discovers tests via the upstream
manifest at
`https://www.w3.org/2009/sparql/docs/tests/data-sparql11/entailment/`.
Vendoring the four RIF test inputs (RIF-XML rule files + RDF data
+ SPARQL queries + expected `.srx`) is the prerequisite to any
code work. Each test consists of:

- An `.rq` file (the SPARQL query under the entailment regime).
- A data graph file (`.ttl` or `.rdf`).
- A rule document (`.rif` in RIF-XML).
- An expected results file (`.srx` typically).
- A manifest entry naming all of the above with the
  `sparql:entailmentRegime ent:RIF-Core` annotation.

### Step 2: per-test inventory (to be filled by code work)

For each of the 4 tests:

1. RIF Logical Entailment (referencing RIF XML) — exercises the
   RIF-XML parser entry point and a tiny rule set; the SPARQL
   query asks for inferred triples.
2. RIF Core WG tests: Frames — exercises frame syntax
   (`o[p->v]`) translation to RDF triples per
   [RIF/RDF/OWL §5](https://www.w3.org/TR/rif-rdf-owl/#sec-rif-rdf).
3. RIF Core WG tests: Modeling Brain Anatomy — exercises subclass
   and class-membership reasoning over a small ontology.
4. RIF Core WG tests: RDF Combination Blank Node — exercises the
   blank-node handling rule of the RDF combination spec; this is
   the test most likely to surface a corner case (blank nodes in
   rule heads have specific semantics —
   [RIF/RDF/OWL §6](https://www.w3.org/TR/rif-rdf-owl/#sec-rdf-combination)).

After locating the actual test files, this section becomes a
concrete checklist with file paths, rule LoC counts, and expected
inferred-triple counts.

### Step 3: confirm RIF-Core sufficiency

The four tests are explicitly under the W3C SPARQL "RIF Core"
banner (test 1's title says "RIF XML" generically but its manifest
entry uses `ent:RIF-Core`). None of them require BLD function
symbols, PRD actions, or full equality reasoning. Confirmable by
reading the upstream manifest before any F\* work begins.

### Step 4: rough LoC estimate per module

| Module | Estimated LoC | Confidence |
|---|---|---|
| `RIF.Core.Syntax.fst` | 80-150 | high |
| `RIF.Core.Translation.fst` | 200-300 | medium |
| `RIF.Core.Eval.fst` | 300-500 | medium |
| `Parser.RIFXML.fst` | 400-700 | low (depends on subset) |
| `RIF.Core.Tests.fst` | 100-150 | high |
| Total verified F\* | 1080-1800 | medium |

For comparison: `OWL.QueryRewrite.fst` is in the same order of
magnitude and the OWL-RL Datalog closure rules in
`RDF.Graph.Executable.fst` are a few hundred LoC. The proposed
RIF-Core engine is comparable in size to the existing OWL-RL
infrastructure.

## What this does NOT do

- Does not implement RIF-BLD, RIF-PRD, or RIF-FLD.
- Does not implement RIF function-symbol recursion (would break
  the Datalog termination story).
- Does not implement equality reasoning in rule heads (RIF-BLD
  feature).
- Does not implement negation-as-failure (not in RIF-Core).
- Does not aim to compete with full Datalog engines (Soufflé,
  RDFox, IRIS-Reasoner). The bar is "make the 4 skipped W3C
  SPARQL entailment tests pass with verified F\* code".
- Does not replace `OWL.QueryRewrite` / OWL-RL — they share
  infrastructure (the SPARQL evaluator and the graph union
  primitive) but the rule sets and entry points are independent.
- Does not introduce new `assume val` declarations beyond what
  the existing parsers already use for I/O. The inference engine
  itself is fully verified F\*.

## Open questions

These need user weigh-in before code starts:

1. Vendor an existing verified Datalog engine, or hand-roll? A
   quick search turns up no maintained F\*-native Datalog engine.
   Coq's
   [DDlog formalisation](https://github.com/Polytopia/dedukti-datalog)
   and Idris/Agda Datalog formalisations exist but porting any of
   them to F\* is comparable in cost to writing the engine, and
   the project's iron rule 7 ("no cobbling") prefers hand-rolling
   in F\*. Recommendation: hand-roll, reuse SPARQL evaluator.
2. RIF-XML parser: full RIF-XML, or just the subset the four
   W3C tests use? Full RIF-XML costs 2-3x the LoC for features
   the project will likely never exercise. Recommendation: ship
   the test-driven subset, with explicit parse errors for
   unsupported productions, and link the RIF-XML grammar
   coverage table from this doc.
3. Termination story: fuel-bounded (Option A), refinement-typed
   (Option B), or runtime-guarded only (Option C)? The author's
   recommendation is Option A first, with B as a follow-up.
4. Should the RIF closure be cached on the graph (analogous to
   the OWL-RL closure cache) or recomputed per query? The W3C
   tests are tiny and recomputation is cheap; production use is
   out of scope.
5. RIF built-ins: which subset is the minimum for the four tests?
   `pred:numeric-equal`, `pred:literal-not-identical`, `pred:isLiteralOfType`?
   Inventory comes out of the test-artefact survey (Step 1 above).
6. How should the runner report a RIF parse error vs a closure
   non-termination (cap hit)? Today the `RIF-Skip` tag swallows
   both. Suggest distinct test-result states `RIF-ParseFail` and
   `RIF-Cap-Hit` so regressions are visible in the dashboard.

## Rough effort estimate

Per module, T-shirt sizing:

| Module | Size | Notes |
|---|---|---|
| `RIF.Core.Syntax.fst` | XS | Pure ADT, mirrors OWL.QueryRewrite style |
| `RIF.Core.Translation.fst` | S | Pure translation; verifies on the SPARQL evaluator's input shape |
| `RIF.Core.Eval.fst` | M | Fixpoint loop + termination story |
| `Parser.RIFXML.fst` | M-L | Depends on subset; XML scaffolding may already exist |
| `RIF.Core.Tests.fst` | XS | Small shim, follows `OWL.Tests.Manifest.fst` pattern |
| Vendoring + manifest wiring | S | One-time test-corpus cost |
| Aggregate | M-L | Roughly 1-2 weeks of focused F\* work after the open questions are resolved, assuming Option A termination story and test-driven RIF-XML subset |

If the `Parser.RIFXML` work blows out (the W3C test inputs use
exotic productions), aggregate moves to L-XL. Mitigation: the
test-driven subset is bounded by the 4 test inputs.

## Recommendation

Pursue, conditionally. The RIF-Core engine fits the project's
"verified F\* SPARQL stack" thesis cleanly: the rule-as-CONSTRUCT
mapping makes the inference engine a thin fixpoint over the
existing evaluator rather than a parallel reasoning system. The
termination story is provable in F\* without `--lax`. The 4
skipped tests are concrete, achievable, and visible in the
dashboard.

Conditional on:

- The four W3C test artefacts being available (Step 1 above) and
  confirming `ent:RIF-Core` regime (Step 3).
- The RIF-XML subset stays bounded by the test inputs (Open
  question 2 resolved as "test-driven subset").
- The user accepting Option A termination (fuel-bounded) as the
  initial verification target.

If the RIF-XML parser turns out to need substantially more than
the test-driven subset to be robust enough to ship as a public
F\* module, the calculus changes — at that point the right move
is to leave the 4 tests permanently skipped with this document
as the rationale.

## References

- W3C RIF Core — https://www.w3.org/TR/rif-core/
- W3C RIF RDF and OWL Compatibility — https://www.w3.org/TR/rif-rdf-owl/
- W3C RIF Datatypes and Built-Ins — https://www.w3.org/TR/rif-dtb/
- W3C RIF Test Cases —
  https://www.w3.org/2005/rules/wiki/RIF_Test_Cases
- W3C SPARQL 1.1 Entailment Regimes —
  https://www.w3.org/TR/sparql11-entailment/
- Local recovery roadmap —
  [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md)
- Local entailment plan —
  [`docs/designissues/2026-04-23-entailment-plan.md`](2026-04-23-entailment-plan.md)
- Existing tableau OWL plan (precedent for an extra entailment
  regime as an F\* module) —
  [`docs/designissues/2026-04-19-tableau-owl-plan.md`](2026-04-19-tableau-owl-plan.md)
- Runner detection of `ent:RIF` / `ent:RIF-Core` —
  `formal/fstar/ocaml-output/w3c_runner.ml:441-451`
- Test scoreboard with the 4 skips —
  `docs/test-results/latest.json`
