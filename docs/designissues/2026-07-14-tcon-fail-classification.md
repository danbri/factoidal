# OWL 2 DL type-consistency: classifying the 18 remaining fails

Date: 2026-07-14. Status: ANALYSIS (no F* or OCaml changes in this
commit). Baseline: `bin/linux-x86_64/owl_runner
third_party/testing/owl/type-consistency.rdf --regime dl`, 334 pass,
18 fail (out of 352 scored), 2 skipped (functional-syntax-only), out
of 354 total ConsistencyTest cases in the catalog. Reproduced on this
branch (`.claude-runs/tcon-dl-20260714.log`) and cross-checked against
the same-day committed run in
`formal/fstar/ocaml-output/owl_type_consistency_results.log`
(2026-07-14 08:44:38 UTC) — both agree on all 18 names and modes.

Companion to the type-inconsistency completion program in
[`docs/designissues/2026-07-10-owl2-dl-completion-program.md`](2026-07-10-owl2-dl-completion-program.md),
which took type-inconsistency 66/70 -> 110 pass via five tableau
waves and left the classification of type-consistency's 18 fails as
open work. This document does that classification.

## Headline finding

Of the 18 fails, **16 are a single harness scoring bug, not a
reasoner or parser gap**. The premise ontologies for these 16 tests
are intentionally, syntactically-validly EMPTY (`<rdf:RDF
xmlns:rdf="..."/>` or `<rdf:RDF ...></rdf:RDF>` with zero child
elements) — the corpus author's pattern for "vocabulary-inherent
entailment" tests, where the interesting claim lives in the sibling
PositiveEntailmentTest's conclusion (e.g. "rdfs:comment is an
owl:AnnotationProperty", entailed from RDF/RDFS/OWL semantics alone,
no ABox needed) and the ConsistencyTest is a trivial sibling asserting
"this empty ontology is of course consistent."

`bin/owl-runner/owl_runner.ml`'s `run_consistency_test` (and the same
pattern in `run_positive_entailment` / `run_negative_entailment`)
cannot distinguish "the RDF/XML parser threw because the input was
malformed" from "the RDF/XML parser correctly returned zero triples
because the input legitimately has zero triples" — both collapse to
`g_p = []`, and the runner treats `g_p = []` as `Fail_parse_premise`
unconditionally:

```ocaml
(* bin/owl-runner/owl_runner.ml:1017-1024, run_consistency_test *)
| Some p_lex ->
  let p_src = expand_catalog_entities p_lex in
  let base = info.iri in
  let g_p_authored =
    try Parser_RDFXML.parse_rdfxml_with_base base p_src
    with _ -> [] in
  let g_p = load_imports_into_premise info imports_lookup g_p_authored in
  if g_p = [] then Fail_parse_premise
  else begin ... end
```

The other 2 fails are a genuine narrow parser edge case (1 test) and
the pre-existing, previously-documented XMLLiteral-equality soundness
gap (1 test, `WebOnt-miscellaneous-202`).

None of the 18 share a root cause with the type-inconsistency side's
17 in-flight fails (nominals/oneOf `dl-502`, double blocking
`dl-626`/`dl-627`, finite-model counting `dl-909`/`dl-910`/`one=two`,
`dl-504` DPLL budget-outs) — those are missing-tableau-capability
gaps; type-consistency's fails are a harness bug plus two narrow,
unrelated edge cases. See "Cross-reference with tinc" below.

## The 18, classified

| test | failure mode | feature family | root cause | fix sketch | shared with tinc? |
|---|---|---|---|---|---|
| `WebOnt-Class-001` | FAIL/parse-premise | empty-premise misclassification | premise is `<rdf:RDF xmlns:rdf="..."/>` (0 triples, syntactically valid); runner's `g_p = []` check can't tell "parser threw" from "parser correctly returned empty" | see "Fix sketch A" below | No |
| `WebOnt-I5.5-001` | FAIL/parse-premise | empty-premise misclassification | same pattern, premise `<rdf:RDF xmlns:rdf="..."/>` | Fix sketch A | No |
| `WebOnt-I5.5-002` | FAIL/parse-premise | empty-premise misclassification | same pattern | Fix sketch A | No |
| `WebOnt-Nothing-002` | FAIL/parse-premise | empty-premise misclassification | premise `<rdf:RDF ...></rdf:RDF>` (0 children) | Fix sketch A | No |
| `WebOnt-imports-010` | FAIL/parse-premise | empty-premise misclassification | premise `<rdf:RDF xmlns:rdf="..."/>` | Fix sketch A | No |
| `rdfbased-sem-class-nothing-type` | FAIL/parse-premise | empty-premise misclassification | premise `<rdf:RDF ...></rdf:RDF>`, 0 children — "type of owl:Nothing" is a vocabulary-inherent PE claim, empty ABox | Fix sketch A | No |
| `rdfbased-sem-class-thing-type` | FAIL/parse-premise | empty-premise misclassification | same pattern (owl:Thing) | Fix sketch A | No |
| `rdfbased-sem-prop-backwardcompatiblewith-type-annot` | FAIL/parse-premise | empty-premise misclassification | same pattern (owl:backwardCompatibleWith) | Fix sketch A | No |
| `rdfbased-sem-prop-comment-type` | FAIL/parse-premise | empty-premise misclassification | same pattern (rdfs:comment) | Fix sketch A | No |
| `rdfbased-sem-prop-deprecated-type` | FAIL/parse-premise | empty-premise misclassification | same pattern (owl:deprecated) | Fix sketch A | No |
| `rdfbased-sem-prop-incompatiblewith-type-annot` | FAIL/parse-premise | empty-premise misclassification | same pattern (owl:incompatibleWith) | Fix sketch A | No |
| `rdfbased-sem-prop-isdefinedby-type` | FAIL/parse-premise | empty-premise misclassification | same pattern (rdfs:isDefinedBy) | Fix sketch A | No |
| `rdfbased-sem-prop-label-type` | FAIL/parse-premise | empty-premise misclassification | same pattern (rdfs:label) | Fix sketch A | No |
| `rdfbased-sem-prop-priorversion-type-annot` | FAIL/parse-premise | empty-premise misclassification | same pattern (owl:priorVersion) | Fix sketch A | No |
| `rdfbased-sem-prop-seealso-type` | FAIL/parse-premise | empty-premise misclassification | same pattern (rdfs:seeAlso) | Fix sketch A | No |
| `rdfbased-sem-prop-versioninfo-type` | FAIL/parse-premise | empty-premise misclassification | same pattern (owl:versionInfo) | Fix sketch A | No |
| `FS2RDF-literals-ar` | FAIL/parse-premise | literal/datatype-parsing edge case | premise deliberately uses non-canonically-cased XSD datatype IRIs (`#datetime`, `#unsignedint`, `#negativeinteger`, `#anyuri`, `#hexbinary`, `#ncname`, `#nonnegativeinteger`, ... — all lowercase local names, distinct opaque datatype IRIs from the real `xsd:dateTime` etc.) AND one property value is `rdf:datatype=".../XMLLiteral"` (lowercased `#xmlliteral`) whose element content is itself a nested `<rdf:RDF>...<owl:Ontology/>...<rdf:Description>...</rdf:RDF>` block — content that must be captured as opaque XML text, not walked as further RDF/XML node structure. Root cause is most likely the parser treating the nested `<rdf:RDF>` as a real nested description (RDF/XML has no such nesting) rather than literal content of the enclosing XMLLiteral-typed property element, producing a parse failure or corrupt triple set that the runner's `[]` fallback then reports as the empty-premise family conflates it with. Needs isolated single-test repro under the F* toolchain to confirm parser-exception vs corrupt-output. | `Parser.RDFXML.fst`: confirm the `rdf:datatype=".../XMLLiteral"` property-element path treats element content as opaque XML text (D3-style capture) regardless of whether that content happens to look like more RDF/XML, not just the `rdf:parseType="Literal"` path. Distinct from Fix sketch A — this is a genuine parser gap, not a harness gap. | Possibly (current-state.md notes "datatype/parse families in tinc" as open, unconfirmed whether it is literally this fixture or a sibling one — no `FS2RDF-literals` identifier exists in `type-inconsistency.rdf`, so at most a family-level, not fixture-level, overlap) |
| `WebOnt-miscellaneous-202` | FAIL/unexpected-inconsistency | XMLLiteral value-equality (soundness gap, pre-existing, tracked every wave) | premise declares `first:fp` as `owl:FunctionalProperty` and asserts it twice on one `owl:Thing`, with two `rdf:parseType="Literal"` (XMLLiteral) values that differ only in insignificant whitespace between XML elements/attributes (`<br/><img .../>` vs the same markup reformatted across lines). RDF 1.1's XMLLiteral value space is defined via exclusive-canonical-XML string equality, not raw lexical-string equality — the two values ARE equal in RDF's model theory. `RDF.Term.fsti`'s `literal_eq` (line 195-198) and `rdf_term_eq` (line 201-206) compare `lexical_form` as plain strings with no XMLLiteral special case, so `Tableau.Refute.fst`'s successor-dedup (`dedup_terms_ident`, feeding `countable_successors`/`all_successors`, section 4/5 per the module's C3/C4 counting-clash rule) sees 2 "distinct" fillers for a property `inject_functional` has labelled `<= 1 fp`, and clashes — a false positive. | `RDF.Term.fsti`: add an XMLLiteral-aware equality branch to `literal_eq` — when `l1.datatype = l2.datatype = rdf:XMLLiteral`, compare canonical-XML forms (or, if a full exclusive-c14n implementation is out of scope, a narrower but still sound normalisation: parse both as XML infosets and compare element/attribute structure ignoring inter-element whitespace) instead of raw `lexical_form`. Scoped, narrow — only changes XMLLiteral-typed literal comparison, does not touch any other clash rule or datatype. Verify against `WebOnt-miscellaneous-202` specifically and re-run the full DL soundness gate (must stay at exactly one or zero `unexpected-inconsistency`, not regress upward). | No (tcon only, by definition — this is the one case the whole 2026-07-10 program has carried forward every wave) |

**Total: 16 (empty-premise) + 1 (FS2RDF literal/XMLLiteral parsing) +
1 (WebOnt-miscellaneous-202 XMLLiteral equality) = 18.**

## Fix sketch A (the 16-test family)

Site: `bin/owl-runner/owl_runner.ml`, four call sites share the same
pattern (`grep -n 'g_p = \[\]' bin/owl-runner/owl_runner.ml`):

- line 890 — `run_positive_entailment`
- line 941 — `run_negative_entailment`
- line 1024 — `run_consistency_test` (the one that produces all 16
  fails classified above)
- line 1091 — `run_inconsistency_test` (not implicated in today's 18,
  but carries the identical bug — an empty premise can never BE
  inconsistent, so an InconsistencyTest with a genuinely empty premise
  would legitimately fail as `Fail_unexpected_consistency` today, not
  `Fail_parse_premise` — the mislabel doesn't change pass/fail there,
  only the reported reason, so it is lower priority but should move
  in the same commit for consistency of the four call sites)

The fix distinguishes "parser raised an exception" (genuine failure)
from "parser returned `Ok []`" (legitimate empty document) by not
collapsing both into the bare OCaml `[]` today:

```ocaml
let g_p_authored =
  try Some (Parser_RDFXML.parse_rdfxml_with_base base p_src)
  with _ -> None
in
match g_p_authored with
| None -> Fail_parse_premise
| Some g_p_authored ->
  let g_p = load_imports_into_premise info imports_lookup g_p_authored in
  (* g_p = [] here is a VALID trivially-consistent premise, not a
     parse failure — do not short-circuit *)
  let (closure_rl, closure) =
    try apply_closure_stages g_p
    with _ -> (g_p, g_p) in
  if capped_is_inconsistent closure || dl_refutes closure_rl
  then Fail_unexpected_inconsistency
  else Pass
```

This is a `bin/<consumer>/` change (rule #11 exempt — the runner is a
consumer tool, not inside the verified-library boundary); no `.fst`
change needed for this family. Estimated effect: 334 -> 350 pass, 18
-> 2 fail (out of 352) in one commit, holding the soundness gate
(zero new `unexpected-inconsistency`) trivially, since every flipped
test's premise is provably empty (checked by inspection above, not
just by the parser's say-so).

Caution: `load_imports_into_premise` could in principle turn a
textually-empty premise into a non-empty graph via `owl:imports` — none
of the 16 fixtures above declare imports (confirmed by reading each
premise block; none contain `owl:imports`), so this doesn't change the
16-test estimate, but the general fix must still route through
`load_imports_into_premise` before the emptiness question is asked
(as shown above) rather than gating on `g_p_authored` alone.

## Cross-reference with type-inconsistency's 17 in-flight fails

Per `docs/claude-rules/current-state.md` and the completion-program
doc, type-inconsistency's remaining fails cluster into: nominals/oneOf
(`dl-502` — actually a 3-SAT-style propositional case per its
description, "classic 3 SAT problem", not literally a nominal test —
see caveat below), double blocking (`dl-626`/`dl-627`, both marked
"needs double blocking" in the corpus description), finite-model
counting (`dl-909`/`dl-910` integer-multiplication pigeonhole,
`one=two` finite-model cardinality arithmetic), and `dl-504` (DPLL
budget-out).

**Caveat on `dl-502`:** the corpus's own `test:description` for
`WebOnt-description-logic-502` is "This is the classic 3 SAT problem,"
not a nominals test — `current-state.md`'s "dl-502 nominals" label
may be describing the FIX APPROACH (satisfiability via case-split,
adjacent to the nominals/oneOf branching machinery) rather than the
TEST CONTENT. Re-verify against the actual fixture before scoping a
"nominals" wave around it.

> **UPDATE 2026-07-17 (#299/#209 nominal-DPLL wave):** the fixture was
> worked on paper and the engine measured — dl-502 is NOT a DPLL
> budget-out. It returns a definite `FAIL/unexpected-consistency` with
> zero refuter cap-trips because the multiply-defined `owl:oneOf`
> constraints that encode the 9 boolean variables are never LOADED
> into the tableau (`Tableau.fst:303` reads first-`oneOf`-only;
> `OWL.Closure.fst` has no `oneOf` rule). The flip is blocked upstream
> of the refuter, not by search budget. Full root cause + F1/F2/F3
> design in `w3c-completeness-ledger.md` § "dl-502 nominal-DPLL wave".

None of these mechanisms — double blocking, pigeonhole/finite-model
merge search, 3-SAT-style deep branching, DPLL budget tuning — appear
anywhere in the 18 type-consistency fails. The type-consistency fails
are dominated by a harness bug (16/18) plus two narrow, self-contained
parsing/equality edge cases (2/18) that do not touch
`Tableau.Refute.fst`'s branching or counting machinery in the same way
the tinc fails do (WebOnt-miscellaneous-202 touches the counting
machinery's INPUT — literal equality — not the branching/merge logic
itself).

The one soft link: `current-state.md` lists "datatype/parse families
in tinc" as open work, which MIGHT share code paths with
`FS2RDF-literals-ar`'s datatype-IRI-casing and XMLLiteral-content
parsing if the tinc-side datatype/parse fails turn out to exercise the
same `Parser.RDFXML.fst` datatype-literal path. Unconfirmed — the tinc
fail list was not re-derived in this pass (out of scope: this
document's brief was the 18 tcon fails); a future pass should name the
tinc "datatype/parse" fails explicitly and check for shared fixture
patterns (nested XML content inside a typed literal, non-canonical
XSD IRI casing) before claiming a real wave-sharing win.

## Ranked wave list

1. **Wave TC-1 — empty-premise harness fix** (`bin/owl-runner/owl_runner.ml`,
   4 call sites, ~15 line diff). Flips 16 of 18 tcon fails
   (334 -> 350 pass, 18 -> 2 fail out of 352). Zero F* changes, zero
   soundness risk (every flipped premise is a verified-by-inspection
   empty graph). Difficulty: LOW (harness/consumer-tool change, no
   `.fst` verify cycle). Flips 0 tinc tests (tinc's InconsistencyTest
   runner's identical bug at line 1091 cannot flip any CURRENT tinc
   fail from FAIL to PASS — an empty premise is never inconsistent, so
   it was already scoring correctly as fail, just under the wrong
   label; only the reported reason string changes there). Do this
   wave first — it is the highest tests-flipped-per-line-changed ratio
   in either fail set.
2. **Wave TC-2 — XMLLiteral canonical equality** (`RDF.Term.fsti`
   `literal_eq`, plus whatever extraction/build cycle that triggers).
   Flips `WebOnt-miscellaneous-202` specifically — closes the ONE
   soundness exception every OWL2 DL wave report has carried since
   2026-07-10. Difficulty: MEDIUM (needs a real, sound XML-canonical-
   form comparison, not a hack — must not weaken `literal_eq` for any
   non-XMLLiteral datatype, and must re-run the full DL soundness gate
   after). Module: `RDF.Term.fsti` (used pervasively — touch with
   care, re-verify all dependents). Flips 0 tinc tests directly, but
   removing this exception lets future soundness-gate reports drop
   the "(WebOnt-miscellaneous-202, pre-existing)" qualifier entirely,
   which every wave-landing report currently has to carry.
3. **Wave TC-3 — FS2RDF-literals-ar parser fix** (`Parser.RDFXML.fst`,
   XMLLiteral/`parseType=Literal` content capture). Flips 1 test.
   Difficulty: MEDIUM — needs the parser's literal-content path
   confirmed against RDF/XML's actual grammar (content of a
   `rdf:parseType="Literal"` or `rdf:datatype=".../XMLLiteral"`
   property element is raw XML text, never re-entered as node
   structure, even if it happens to contain `<rdf:RDF>`-shaped
   markup). Isolate with a standalone single-fixture repro under the
   F* toolchain before touching the shared parser module — confirm
   parser-exception vs corrupt-triple-set first (this document did not
   reach that confirmation; flagged above). Sequence AFTER Wave TC-2
   since both touch XMLLiteral handling and a shared design pass
   (canonical XML representation) may serve both.

Waves 1-3 clear all 18 tcon fails (334 -> 352 pass, 0 fail out of
352), a state neither type-inconsistency nor type-consistency has
reported before on this corpus. None of the three waves is a
prerequisite for, or blocked by, the tinc program's double-
blocking/finite-model/nominals work — they can run fully in parallel
with `dl-909`/`dl-910`/`dl-502`/`dl-626`/`dl-627` waves.

## Method note

Ran `FACTOIDAL_OWL_CAP_SEC=20 bin/linux-x86_64/owl_runner
third_party/testing/owl/type-consistency.rdf --regime dl` on this
worktree after `tools/ensure-test-env.sh` (exit 0); full log at
`.claude-runs/tcon-dl-20260714.log`. Verdict lines and totals agree
with the same-day committed
`formal/fstar/ocaml-output/owl_type_consistency_results.log`. Every
premise ontology cited above was read directly out of
`third_party/testing/owl/type-consistency.rdf`'s embedded
`test:rdfXmlPremiseOntology` literals (line numbers cited inline
during investigation, omitted here since the file is regenerated by
the W3C corpus maintainers and line numbers are not stable identifiers
— use the `test:identifier` string with `grep` to relocate any
fixture).
