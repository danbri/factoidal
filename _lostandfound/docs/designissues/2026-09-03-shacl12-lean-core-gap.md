# SHACL 1.2 Core in the Lean tree: the denominator gap, the proof
coupling, and the remaining constraint families

Status: current. Records the 2026-09-03 investigation into the Lean
`l4shacl` runner's score against `third_party/testing/shacl/shacl12-test-suite/tests/core/manifest.ttl`,
and the fixes landed the same day.

## Scores

Measured before this landing: 103 pass, 30 fail (out of 133).
Measured after: 113 pass, 20 fail (out of 133).
F* engine on the same suite (`docs/test-results/latest.json`, key
`shacl12_core`): 138 pass, 0 fail (out of 138).

## The denominator: 133 against 138

The F* and Lean runners walk the SAME `mf:include` tree
(`tests/core/manifest.ttl` includes `complex`, `misc`, `node`, `path`,
`property`, `targets`, `validation-reports`; each of those includes one
file per test). Counting `mf:include` lines directly in each
sub-manifest gives 138 (2+10+46+11+56+10+3). The Lean runner's own
per-directory totals matched exactly for `complex` (2), `node` (46),
`path` (11), `targets` (10), and `validation-reports` (3) — the walk is
not the defect. Two directories were short: `misc` counted 7 of 10,
`property` counted 54 of 56.

Cause, with evidence: `l4shacl` printed, before its report, five
`Turtle parse error: parse error at offset N: expected '.' after
triple` lines, one per missing test:

- `core/misc/deactivated-003.ttl`
- `core/misc/message-002.ttl`
- `core/misc/severity-003.ttl`
- `core/property/reifierShape-001.ttl`
- `core/property/reifierShape-002.ttl`

All five use the RDF 1.2 / Turtle 1.2 "annotation syntax" — a triple
followed by `{| ... |}`, which reifies the triple and asserts the
bracketed predicate-object pairs about its reifier. Example
(`core/misc/message-002.ttl`):

```turtle
ex:TestShape
  sh:datatype xsd:integer {| sh:message "Test message"@en |} ;
  sh:targetNode ex:InvalidNode ;
.
```

The Lean Turtle parser (`L4Factoidal/Syntax/Turtle.lean`) does not
recognise `{| ... |}`; a file that uses it fails to parse, and
`ShaclProbe`'s harness treats an unreadable manifest entry as absent —
not counted in either the pass or the fail bucket, and not printed in
`Totals`. This is a Turtle 1.2 parser gap, not a walk defect: the
manifest's `mf:include` line for each of these five files IS visited:
the file behind it just does not parse. The F* engine's Turtle parser
supports the annotation syntax (confirmed by its 138/138 score
including these five tests), so the two engines' denominators diverge
on this feature specifically, not on manifest traversal.

**Not fixed in this landing.** Implementing RDF 1.2 triple-term
annotation syntax is a Turtle/RDF-parser change (per repository iron
rule 4, parsers belong in F* first — but the intended target for full
scope is the Lean tree per the 2026-08-29 standing decision), touching
grammar shared by every other suite that runs through the same parser.
That is a properly-scoped parser task on its own, tracked separately
from the SHACL constraint-component work below.

## The proof coupling: why this took more than five files

`ShaclTheorems.lean` proves `validate_conforms_iff` — a real iff, not a
one-directional soundness lemma — between the EXECUTABLE
`collectShapeViolations`/`evalOneConstraint`/`evalAggregateNonRec`/
`simpleValueCheck` and a DECLARATIVE mirror (`Spec.Conforms`,
`Spec.ValueSatisfies`, `Spec.FocusSatisfies`), built by induction on
the fuel parameter. Two things follow for any new `Constraint`
constructor that gets REAL (not vacuous) executable semantics:

1. If the constructor's executable check is reached through
   `simpleValueCheck`'s wildcard fallback inside `evalOneConstraint`,
   `Spec.ValueSatisfies`'s matching case MUST NOT stay at its `_ =>
   True` default — `simpleValueCheck_iff'`'s own wildcard case
   (`simp [simpleValueCheck, Spec.ValueSatisfies]`) will try to prove
   `(some true = ... ∨ none = ...) ↔ True` and fail to discharge it the
   moment the check can return `some false` for real input. The fix is
   an explicit named case in `isSimple`, `simpleValueCheck_iff`, and
   `simpleValueCheck_iff'`, mirroring the existing `.datatype`/
   `.languageIn` cases.
2. The same applies to `evalAggregateNonRec_eq_nil_iff` for aggregate
   (focus-node-level) components, and to `conformance_iff`'s explicit
   `cases cc with` list for any component that needs shape-graph
   lookups (`sg`) or fuel (recursive components like `sh:and`/`sh:or`/
   `sh:node`).

`lake build` catches every missing case as a compile error (Lean's
`cases`/`match` exhaustiveness), so nothing here can go silently wrong
— but each new constraint with real executable semantics costs a
matching `Spec` case and a proof, not just a decoder-and-evaluator
change. This is why the ten fixes landed here were chosen as the ones
whose per-value or per-focus-node check could reuse an existing proof
pattern almost verbatim (`.datatype`'s `Subtype.ext`-based literal
check, `.disjoint`'s path-membership check, `.cls`'s `isShaclInstance`
check), and why the larger constraint families below were left
unfixed rather than rushed.

A second, separate hazard the same investigation surfaced: `Spec.GraphConforms`
calls the EXECUTABLE `shapeFocusNodes` directly (no parallel
declarative target-evaluator to keep in sync), so a `Target` /
`decodeTargets` / `evalTarget` change carries none of the proof
overhead above — the `sh:ShapeClass` implicit-target and `sh:shape`
data-target fixes below needed no `Spec` or theorem changes at all.

## What was fixed (10 tests, all in `ShaclTheorems.lean`-provable form)

1. **List-valued `sh:datatype` / `sh:class` / `sh:nodeKind`
   ("one of").** SHACL 1.2 lets these three take an `rdf:List` of
   values instead of a single one; the value must match ONE of the
   list. New `Constraint.datatypeIn` / `.clsOneOf` / `.nodeKindOneOf`,
   reported under the SAME `sh:*ConstraintComponent` IRI as their
   singular form. Fixes `core/node/datatype-003`,
   `core/property/datatype-004`, `core/property/class-002`,
   `core/node/nodeKind-002`.
2. **`sh:singleLine`.** The value's lexical form must contain no
   Unicode line-break character (U+000A/B/C/D). Fixes
   `core/property/singleLine-001`.
3. **`sh:rootClass`.** The value (an IRI) must be the given class or a
   transitive `rdfs:subClassOf` descendant of it — reuses the existing
   `superClasses` closure (already reflexive). Fixes
   `core/property/rootClass-001`.
4. **`sh:subsetOf`.** The mirror image of `sh:subsetOf`'s existing
   sibling `sh:disjoint`: every value node must ALSO be a value of the
   compared path (one violation per value that is not). Fixes
   `core/property/subsetOf-001` and `-002`.
5. **`sh:ShapeClass` implicit target.** SHACL 1.2 §2.1.3.1: `a
   sh:ShapeClass` makes a node both class and shape on its own,
   regardless of separate `rdfs:Class`/`sh:NodeShape` typing.
   `decodeTargets`'s `isClass && isNodeShape` implicit-class check
   gained an `|| isShapeClass` branch. Fixes
   `core/targets/targetClassImplicit-002`.
6. **`sh:shape` data-side target.** SHACL 1.2: a DATA triple `N
   sh:shape S` makes `N` a focus node of shape `S` — the inverse of
   the shape-declared targets. New `Target.dataShape`, added
   unconditionally to every IRI-identified shape's target list
   (matching the F* `T_DataShape` reading) and evaluated against the
   data graph in `evalTarget`. Verified safe against every OTHER
   loaded suite (`grep -rl "sh:shape "` over the SHACL 1.0/1.2 test
   trees found no other use of the predicate) before landing, since it
   changes which shapes count as "roots" in `validate`. Fixes
   `core/targets/shape-001`.

## What was investigated and left failing, with the reason

- **`sh:closed sh:ByTypes`** (`core/node/closed-003`, `-004`, 2
  tests). Needs the union of `sh:property` paths from every OTHER
  `ByTypes`-closed node-shape whose class classifies the focus node
  (via `rdf:type`, subclass-closed) — doable inside
  `evalAggregateNonRec` (which already carries `sg`), but the `Spec`
  side needs a matching existential over `sg` and a
  `evalAggregateNonRec_eq_nil_iff` case proving it, which was not
  completed in this session.
- **`sh:minListLength` / `sh:maxListLength` / `sh:uniqueMembers` /
  `sh:memberShape` / `sh:uniqueValuesFor` / `sh:someValue`**
  (`core/node` and `core/property`, 14 tests combined). All genuinely
  new SHACL 1.2 Core components (F* already implements all six —
  `CC_MinListLength`/`CC_MaxListLength`/`CC_UniqueMembers`/
  `CC_MemberShape`/`CC_UniqueValuesFor`/`CC_SomeValue` in
  `formal/fstar/SHACL.Validation.fst`). `sh:memberShape` and
  `sh:someValue` need shape-graph lookups and fuel (like `sh:and`/
  `sh:or`), so they need an explicit new case in `conformance_iff`'s
  `cases cc with`, not just `Spec.ValueSatisfies`/`FocusSatisfies`.
  `sh:uniqueValuesFor` is a cross-focus-node, whole-shape pass (F*
  evaluates it once per shape over ALL focus nodes, not per focus
  node), which does not fit the existing per-focus-node/per-value
  evaluation loop (`collectShapeViolations`) at all — it needs a new
  top-level pass alongside `validate`'s `roots.flatMap`.
- **`sh:nodeByExpression`** (`core/node/nodeByExpression-001`, 1
  test). Behaves like `sh:node` (needs `sg` + fuel) but reports a
  different component IRI; needs the same `conformance_iff` case
  extension as `sh:memberShape`.
- **`sh:targetWhere`** (`core/targets/targetWhere-001`, 1 test). SHACL
  1.2 lets a shape's `sh:targetWhere` value be a NESTED SHAPE (not a
  raw SPARQL WHERE clause, despite the name) whose CONFORMING nodes
  become the target's focus nodes. F*'s `shape_focus_nodes` handles
  this via a `target_where : list shape_ref` field evaluated with
  `collect_shape_violations` over every candidate subject — i.e. it
  needs the SAME shape-conformance recursion that
  `Spec.GraphConforms` uses, making it a `Spec`/proof-coupled change
  despite living in the target layer (unlike the two target fixes
  landed above, which needed no proof changes at all).
- **`sh:Debug` / `sh:Trace` diagnostic severities**
  (`core/misc/severity-004`, `-005`, 2 tests). SHACL 1.2 adds two
  severities below `sh:Info` that are still reported as results but do
  NOT make the report non-conformant. The fix touches `validate`'s own
  `conforms := results.isEmpty` formula — the field
  `validate_conforms_iff` states an EXACT iff against, over ALL
  results regardless of severity. Weakening `conforms` to exempt
  Debug/Trace makes that iff's `.mp` direction (`validate.conforms =
  true → Spec.GraphConforms`) genuinely false for data with only
  Debug/Trace violations (the report would say "conforms" while
  `Spec.GraphConforms` — which has no severity concept — says it does
  not). Landing this needs `validate_conforms_iff` restated (most
  likely split into a one-directional soundness lemma, since the
  reverse direction is the one that breaks) BEFORE the code change,
  not after; not something to rush inside a score-focused commit.
- **`sh:conformanceDisallows`** (`core/validation-reports/
  conformance-disallows-001`, 1 test). Confirmed NOT an engine
  feature: the F* side's `bin/shacl-runner/shacl_runner.ml` handles it
  entirely in the TEST HARNESS (a consumer tool, iron rule 11) —
  `apply_conformance_disallows` reads `sh:conformanceDisallows` off the
  EXPECTED report and recomputes the actual report's `sh:conforms`
  against that severity set before comparing, rather than the engine
  computing it. The Lean `Harness/ShaclProbe.lean` runner needs the
  equivalent comparison-side accommodation; this was identified but
  not implemented in this session.

## What must NOT move

Re-measured after this landing, unchanged:

- `data-shapes-test-suite/tests/core`: 98 pass, 0 fail (out of 98)
- `data-shapes-test-suite/tests/sparql`: 22 pass, 0 fail (out of 22)
- `shacl12-test-suite/tests/sparql`: 22 pass, 3 fail (out of 25)
- `l4shacl-rules`: 88 pass, 0 fail (out of 88)
- `l4shacl-nodeexpr`: 140 pass, 0 fail, 2 unsupported (out of 142)
- `l4w3c --quiet` SPARQL 1.1: 631 pass, 0 fail (out of 631)

The last one matters because `sh:subsetOf`/`sh:disjoint` share
`evalPath` with the SPARQL property-path evaluator, and the
`SparqlTheorems.lean` custom-constraint-component proof
(`evalCustomComponent_eq_nil_iff`) pattern-matches `Constraint`
exhaustively by name (no wildcard) — a second location, beyond
`ShaclTheorems.lean`, that needed the five new constructors added to
its case list before `lake build` would pass.
