# Current State (Honest Assessment)

Last refreshed: 2026-08-12 (prose sync only — see the 2026-08-12 entry
below; the file's own log entries below it were last appended
2026-07-30 and are unchanged history, not stale claims).

**Update 2026-08-12 (site/docs prose sync against `docs/theorem-registry.md`
and the 2026-08-11 landings, #380-#419):**
- ✅ W3C current, from `docs/test-results/latest.json` (2026-08-12
  07:05 UTC, commit `84ded26`): SPARQL 631 pass, 0 fail (of 631); RDF
  1031 pass, 0 fail (of 1031); combined 1662 pass, 0 fail (of 1662,
  100% of runnable). xmlconf 1447 pass, 0 fail, 1138 skip (of 2585).
  The old "627 pass + 4 known RIF" framing that appears in older log
  entries below was a runner-CWD artifact (#418): `w3c_runner`'s
  `rif_rules_path_for` used a hardcoded relative path, so running from
  `ocaml-output/` instead of the repo root produced exactly 4 spurious
  RIF-entailment failures. From the repo root: 631 pass, 0 fail.
- ✅ FastString migration COMPLETE, steps 0-6 (branch `js-equivalence`,
  task #47): equivalence corpus 93,846 pass, 962 expected-fail, 0
  unexpected fail (of 94,808), identical under native OCaml and under
  Node via js_of_ocaml. Zero `assume val`s left in the FastString
  family except the documented `unsafe_char_of_d7ff`; the
  `FStar.String.sub`/`concat` ulib walls are closed with zero new
  axioms.
- ✅ Streaming theorem program COMPLETE (#402 closed): the fully-generic
  consumer theorem (`theorem_stream_consume_eq_batch`, any consumer
  type/function/chunk split) plus the dataset-specific theorem and the
  parser theorem are all proved; #402's residue list is empty.
- ✅ New symbolic theorems: IRI round-trip on plain well-formed ASCII
  strings, N-row SRJ serializer shape, and token round-trip re-proved
  on the new `Parser.FastString.fs_byte_sub`-based lexer foundation
  (task #52 migrated the lexer's 13 `String.sub` call sites).
- ✅ XML normalization spec bugs fixed (#381, branch `xml-norm`):
  `normalize_line_endings` and `normalize_attr_literal_ws` land as
  pre-passes in `Parser.XML.fst`; xmlconf and SPARQL/RDF totals
  unchanged (same numbers as above).
- ✅ `simple_entails` SE-1 fixed (#324, branch `simple-entails`): the
  loose `literal_eq` (case-folded language tags, XML-canon-equated
  `rdf:XMLLiteral`) is replaced by a strict field-by-field
  `literal_term_eq`; regression pins both directions.
- ✅ npm package renamed to `factoidal` (#403, landed via PR #412),
  never published under the old placeholder name (`@danbri/foafos`).
  This sweep found and fixed six site files PR #412 missed — live
  `../npm/foafos/browser.js` import paths in three demo pages
  (RIF, JSON-LD Playground, COTTAS) that would 404 in the browser,
  since `docs/npm/foafos/` no longer exists.
- ✅ The review kernel (`docs/review-kernel.md`, #403 G1, landed
  2026-08-11) is now linked from the front page (`docs/index.md`),
  hub post 16, and the RDF/SPARQL conformance pages — it was not
  linked from any public surface before this sweep.
- ⚠️ NOT independently re-verified this sweep (left unchanged, flagged
  for a future measurement-bearing session): the per-suite score
  tables and "measured on 2026-07-30" dates on
  `docs/web/conformance/{rdf,sparql,owl2}.md`. The registry confirms
  the RDF/SPARQL totals are unchanged since that run, but those pages'
  own rule is "fresh measurement or nothing" and re-running all three
  binaries end to end was out of scope for a docs-only sweep.

**Update 2026-07-30 (OWL absence-verdict correction, #326 — some
published OWL numbers move DOWN on purpose):**
- 🔴 `bin/owl-runner/owl_runner.ml` scored a ConsistencyTest or
  NegativeEntailmentTest as PASS when the reasoning that should have
  found the counter-evidence was abandoned on a per-test budget. Both
  kinds pass on the ABSENCE of a derived fact, and a truncated closure
  satisfies absence trivially, so the pass was an artifact of giving up.
  Forced-cap check on `profile-RL.rdf`, before: Consistency 76 pass and
  NegativeEntailment 6 pass with EVERY closure abandoned. After:
  Consistency 0 pass / 76 unsupported, NegativeEntailment 0 pass / 6
  unsupported. Unforced runs are unchanged.
- ✅ All nine OWL catalogs re-measured in ONE pass (2026-07-30, 2127s
  wall, budgets as `generate-report.sh --run` sets them) so the nine
  committed logs agree with each other and with the binary for the first
  time. The stale ones were badly stale: `owl_profile_rl_results.log`
  published 28 pass, 2 fail against the binary's 30 pass, 0 fail, and
  three logs published PE 173 pass, 31 fail against the binary's 195
  pass, 9 fail.
- 📊 Corrected numbers: `type-consistency` Consistency **337 pass, 15
  fail (out of 352)** — all 15 fails are `unsupported` (cap escape), was
  352 pass, 0 fail in the same run before the gate. `semantics-direct`
  Consistency **336 pass, 15 fail (out of 351)**, same cause.
  `type-positive-entailment`'s Consistency section **197 pass, 7 fail
  (out of 204)**. `type-negative-entailment`'s Consistency section **22
  pass, 1 fail (out of 23)**. `profile-EL` aggregate **119 pass, 1 fail
  (out of 120)**.
- ✅ Unmoved, as designed: PE **195 pass, 9 fail (out of 204)** and
  type-inconsistency **126 pass, 1 fail (out of 127)**, same FAIL names
  — both kinds pass on the PRESENCE of a derived fact, so a truncated
  closure already showed up as a FAIL. Zero NegativeEntailmentTests
  escaped their budget in any catalog, so no NE verdict moved. `profile-RL`
  30/6/76/14 and `profile-QL` 20/3/58/6 unchanged, `syntax-dl` species
  319 pass, 2 fail unchanged.
- 🧹 Escape audit: the nine formerly-silent closure fallback arms now log
  their stage and exception; two witness-layer arms and eight outer
  `try apply_closure* with _ ->` arms were counting nothing at all and now
  do; the marker-scan and refuter cap-trips (which returned "nothing
  found" for a search that never finished) are counted and gate the
  absence verdict. `HARNESS-DIAG-OWL` carries the per-kind counts and
  names every corrected test.
- ⚠️ 15 distinct tests are affected, all Consistency; named on
  `/web/conformance/owl2/`. They are a performance gap, not a wrong
  answer: the assertions may well hold on a complete closure, and the
  point of the change is that we could not tell.

**Update 2026-07-28 (dashboard regen + WebOnt-imports-002 runner fix):**
- 📊 `docs/test-results/latest.json` was under-reporting ~10 already-fixed
  OWL profile tests (stale since an `OWL.Closure.fsti` edit earlier the
  same day); regenerated via `formal/fstar/generate-report.sh` (no hand
  edits): `owl2_profile_el` **118 pass, 2 fail (out of 120)** (was 108
  pass, 12 fail), `owl2_profile_ql` **85 pass, 2 fail (out of 87)** (was
  83 pass, 4 fail). The 4 remaining fails across both are
  `WebOnt-I5.26-010` + `WebOnt-I5.5-005` (see `docs/claude-rules/
  scope.md`'s OWL 1 Full comprehension-principle section — these are
  the 2 permanent failures, cited once per profile catalog).
  `owl_rl_positive_entailment` unchanged at 28 pass, 2 fail (out of 30).
- 🧹 `bin/owl-runner/owl_runner.ml`'s `load_imports_into_premise` used
  to merge every `test:importedOntology` catalog link into the premise
  unconditionally, so `WebOnt-imports-002` (a NegativeEntailmentTest
  checking that an unimported namespace's axioms must NOT be pulled in)
  scored the wrong verdict. Fixed by gating the merge on a plain
  triple-membership check (does the premise, as assembled so far,
  actually assert `_ owl:imports <iri>`?), iterated to a fixpoint since
  the corpus itself has a transitive-imports test
  (`WebOnt-imports-003`). Also fixed: the catalog's
  `test:importedOntology` link points at a synthetic wrapper node, not
  the real ontology IRI asserted in the premise's `owl:imports` triple —
  resolved via the wrapper's `test:importedOntologyIRI` sibling
  property. Gated on all four DL catalogs: `type-positive-entailment`
  **140 pass, 64 fail (out of 204)** (FAIL name list byte-identical to
  the pre-fix baseline — no regression), `type-negative-entailment`
  **23 pass, 0 fail (out of 23)** (standalone catalog, unaffected),
  `type-consistency`'s NE section **23 pass, 0 fail (out of 23)**
  (was 22/1 pre-fix — `WebOnt-imports-002` confirmed flipped, the exact
  target), `type-inconsistency` **124 pass, 3 fail (out of 127)**
  (unchanged, same 3 named fails), `type-consistency` **352 pass, 0
  fail (out of 352)** (unchanged).

**Update 2026-07-16 (the day-closure run, ~20 gated landings):**
current headline numbers, all measured on the shipped tree:
- 📊 OWL 2 DL type-inconsistency **123 pass, 5 fail (out of 128), zero
  oracle-assisted** (concrete-domain intervals +4, inverse-lifted
  subPropertyOf +4, verified-regex pattern-facet clash +1; remaining 5
  dispositioned — dl-909 disputed-fixture pending owner on #299).
- 📊 type-consistency **352 pass, 0 fail (out of 352)**, soundness
  exceptions ZERO; PE **135 pass, 69 fail (out of 204)** (+30 today via
  negate-and-refute waves); NE 22/1.
- 📊 CSVW csv2rdf **265 pass, 5 fail (out of 270)** (four rounds +
  regex format arm; discovery family in scope per owner).
- 📊 XSLT **83 pass, 5 fail (out of 88)**; GRDDL honestly rescored
  **15 pass, 53 fail, 0 skip (out of 68)** (stage 3 parked by owner).
- 📊 JSON-LD five suites zero-fail, skips 17 -> 4 (all documented).
- **Verified regex engine (#304) phases 1–4 landed**: fully-proven
  derivative core (incl. And/Not), proven fast path, XSD pattern
  parser, and the `regex_match` assume val RETIRED — SPARQL
  REGEX/fn:matches now runs on the verified engine (`regex_replace`
  is the one remaining Str seam, #63).
- RDF 1.2 / SPARQL 1.2 (#305): term model + text/line syntaxes landed
  and verified — RDF 1.2 syntax/eval 212 pass, 0 fail; SPARQL 1.2 248
  pass, 6 fail (out of 254). Still open: RDF/XML 1.2, c14n-1.2 (86) +
  entailment (74) suites, 6 SPARQL eval fails, RML-star mapping gen, and
  browser/npm-API + dashboard wiring (JS `parse`/`query` still 1.1-only).
  (The earlier "14/84 true gap" census predated the syntax/eval landings.)
- Dispositions table landed in the completeness ledger (day-closure
  /goal): every residual fail/skip named with a one-line disposition.

**Update 2026-07-15 (evening, eight gated landings):** the OWL numbers
below are superseded — current: **type-consistency 352 pass, 0 fail
(out of 352)** (empty-premise harness fix +16, XMLLiteral c14n
equality, RDFXML XMLLiteral opaque capture) and **type-inconsistency
114 pass, 14 fail (out of 128) with zero oracle-assisted** (verified
Farkas-certificate class-size reasoner decides dl-910 + one=two;
dl-909 out-of-fragment per the Wave-C refutation note). **The
soundness gate is now ZERO `unexpected-inconsistency`** — WebOnt-202
is retired; any doc/gate saying "exactly one" is historical. The z3
runtime oracle (Z33kr, #296) landed (Phase 0+1) and is retired-in-
practice the same day. CSVW csv2rdf 218 -> **235 pass, 35 fail (out
of 270)** over two burndown rounds (triage ledger:
`2026-07-15-csvw-csv2rdf-fail-triage.md`; discovery/.well-known
family confirmed in scope by owner). PE 103 -> 105 pass (out of 204).
Task list migrated to GitHub issues (#297–#303 created; see #198).
CLAUDE.md gains "Reading owner steers" (prioritization vs prohibition,
phone-triage register, emoji palette).

- **OWL 2 DL type-inconsistency 70 -> 110 pass, 18 fail (out of 128)**
  via five tableau waves in `Tableau.Refute.fst`: datatype facet
  satisfiability (Wave B), role box (subPropertyOf/FunctionalProperty/
  transitive into the refuter), contrapositive unfolding of
  definitions + exact-cardinality-0 NNF, SHIQ ≤-rule witness merging,
  and named-individual identification + stored FP max-1 bounds.
  Soundness gate held throughout: exactly one unexpected-inconsistency
  (WebOnt-miscellaneous-202, pre-existing, tcon only).
- **OWL 2 DL type-consistency 334 pass, 18 fail (out of 352).**
- **vc20-api 51 -> 59 pass, 0 fail (out of 59) — suite fully green**:
  relatedResource structural/digest checks (VCDM 2.0 s5.3, +5) and the
  JSON-LD named-graph/`@container: @graph` VP expansion fix (+3).
- **vc-di-eddsa 26 -> 31 pass, 0 fail (out of 31) — suite fully
  green**: proof sets/chains + `previousProof` chaining landed.
- **Hub post-28 (sigmoid/logistic)**: F*-verified bounded exp (error
  < 1e-9), `fn.sigmoidPoints`, MathML + live sliders; post28 tests
  14 pass, 0 fail.
- Floors unchanged: SPARQL 631 pass, 0 fail; RDF 1031 pass, 0 fail;
  hub 233 pass, 1 fail (pre-existing post18 env check).
- Still open (do not claim done): dl-909/910 + one=two (finite-model
  cardinality arithmetic), dl-626/627 (DL-materialise cap), dl-504
  (DPLL), datatype/parse families in tinc; 18 tcon fails.

Previous refresh: 2026-07-13 day shift (nine landings, continuing the
overnight wave below; same gate regime — floors, named diffs,
soundness where applicable):
- **VC vc20_api 47 -> 51 pass, 8 fail (of 59)** (3b9dd9f): the
  /presentations/verify route — pure shim wiring, the F* checker
  already dispatched VC-vs-VP by type. Remaining 8 triaged: 5
  relatedResource (unimplemented in VC.Credential), 3 JSON-LD
  named-graph expansion (VCDM v2 marks verifiableCredential/proof as
  "@container": "@graph"; canonicalization drops the subtree — a
  JSONLD.* item, not a shim/VC one).
- **Clean competitive baseline committed** (4c09b83): GROUP BY
  officially a WIN (1.93s vs Jena TDB2 2.13s); all engines agree on
  all six queries.
- **Bound-predicate counts read the predicate offset index** (0043ca1):
  q2 1.2s -> 0.28s warm; q5 GROUP BY 1.31s -> 0.32s (the fast path's
  per-predicate counts inherit it).
- **Subject offset sidecar `.s.offsets`** (d4c526a + 6b75469 merged-tree
  rebuild): rows are subject-primary sorted so one (start,end) global
  row range per subject is exact (~1.4MB for 91,871 subjects, magic
  COTS); q3 point lookup 3.15s -> 2.35s median, byte-identical answers,
  graceful fall-through on stores lacking the file. The O column
  deliberately NOT built (contiguity doesn't hold; .po.presence covers
  the co-bound case). Row-GROUP-level win; the containing group still
  fully decodes.
- **Indexed-decode line REFUTED and closed** (577df13 ledger): real
  dictionary-page-indexed resolution measured q6 at ~20s vs 9.5s eager
  — third negative; needs bytes/arrays representation or token-level
  batched join. Branches preserved.
- **profile-QL honestly scored** (b6f9b0d): 83 pass, 4 fail (of 87) —
  scoring already existed, latest.json only carried the 6-test Inc
  line; profile-EL gains the same aggregate.
- **XSLT 75 -> 79 pass, 9 fail (of 88)** (#302 burndown): flips
  boolean-026 (E-notation numeric literals in Parser.XPath),
  namespace-1701 (global variable select evaluated against the source
  DOCUMENT node, not the root element), construct-node-026
  (`processing-instruction('target')` node test in XSLT match
  patterns), and sort-043 (xsl:sort case-order collation). xpath unit
  91/0 held; xml-conformance 1414/0/1171 and GRDDL 9/8/51 unchanged.
  Residual 9 are the namespace-node model (copy-0601, match-045,
  namespace-4101/4501/4801, node-1601), document-node prolog/epilog
  comments (copy-2601, select-1001), and id()/DTD-ID patterns (id-016)
  — all in-scope but larger; none PSVI/schema-dependent.
- **EECC interop corpus vendored** (d976bf5): vc-verifier-rules +
  webuild-attestations (Apache-2.0 verified, PROVENANCE.md; AGPL
  verifier excluded), bin/eecc-runner over 51 real-world fixtures —
  first score 4 pass, 0 fail, 51 categorized skips (of 55 checks).
- **#293 fixed** (79fabd5): extract-staleness digest now covers the
  sibling .fsti; disk-storage-format skill's stale native-writer claim
  corrected.
- In flight at refresh time: eddsa proof-sets (A1), OWL2 spy-points.

Previous same day (overnight wave, ten landings on
claude/main; every landing gated on floors RDF 1031/0 + SPARQL 627+4
known RIF-entailment, OWL soundness where applicable, and named
fail-set diffs):
- **XSLT 69 -> 74 pass, 14 fail (of 88)** in two landings: absolute-path
  axes + `attribute::` match patterns (9a71201), then namespace
  declarations ordered by PROVENANCE — stylesheet order for
  LRE-declared, sorted for source-copied — resolving the
  conflict-resolution-1301 / copy-3102 coupled pair (e27ce3e).
- **VC vc20_api 22 -> 47 pass, 12 fail (of 59)** (40bda97): the
  `VC.Credential` structural checker (117/0 offline) wired into the
  vc-api-shim's issue/verify via a new `vcCheckCredential` npm ABI
  export; remaining 12 = VP verification route + relatedResource
  digests (unimplemented features, tracked on #288).
- **OWL2 DL type-inconsistency 66 -> 68 pass, 49 fail (of 117)**
  (435ee2a): owl:inverseOf-aware edge walking/counting in the tableau
  + the CE_OneOf nominal machinery; soundness held at exactly one
  unexpected-inconsistency (WebOnt-202). Two probes that moved 0 tests
  were built, measured, and NOT landed first — the refuted hypotheses
  (bare O-rule; qualified-cardinality-over-nominal) sharpened the
  target to inverse roles, and the next increment (anonymous-inverse
  restrictions + merge/pigeonhole for the 4 spy-point tests) is on
  #209. QL scoping measured: profile-QL Inc 6 pass, 0 fail in 0.08s —
  efficiency is a non-issue; the QL work item is COVERAGE (87 catalog
  entries, only 6 scored).
- **GROUP BY on COTTAS: 23.05s -> 1.31s (17.6x), ahead of Jena TDB2's
  1.79s** (f99bb64): streaming fast path (detector + Parquet
  dictionary-page distinct-predicate enumeration + a COMPOSING union
  capability — the first cut's blanket None in union_caps kept the
  path dead on the CLI, which always wraps stores as GB_Union; the
  compositional fix is the load-bearing piece). Answer agreement exact
  vs the in-memory path; aggregates 47/0.
- **#294 fixed** (035a2e4): unbounded full-scan SELECT over 889k rows
  no longer stack-overflows (eval_select_items_rows was the last
  missed cons-after-recurse from the Sin7 family).
- **Hub notebooks: 17 posts converted to named reactive cells**
  (declare-once/reference-everywhere, net -185 lines of duplicated
  cell data; 9 posts left alone deliberately — their per-cell data
  differs by design); hub suite 223 pass, 5 fail (of 228, the 5
  pre-existing env fails) (0337593 + merge 6ab2daa).
- **js bundle** rebuilt centrally folding all of the above (595ef55).
- **OPTIONAL/FILTER design landed** (deda096,
  2026-07-13-optional-filter-selective-decode.md): measured q6
  decomposition corrects the column-skip premise — the cost is eager
  4-column row-group decode BEFORE filtering; mechanism =
  row-index-selective decode; stages 1-3 LANDED (c809db6:
  differential gate 14 pass, 0 fail incl. the full-corpus byte-equality
  case; q5 1.44s; full-scan + #294 fix verified post-merge). Stage 4
  (the q6 detector) was built, measured, and NOT landed: q6 REGRESSED
  9.5s -> 15.9s because the indexed-decode glue realises indexed access
  as full-column-decode-then-filter (its documented fallback), so the
  selective path pays the eager cost plus overhead. The follow-up
  (branch indexed-decode-fix) implemented real dictionary-page-indexed
  resolution and measured q6 at ~20s — WORSE than both the fallback
  glue (15.9s) and the eager path (9.5s): three consecutive negative
  measurements. Conclusion: row-index-selective STRING decode cannot
  beat eager decode on the current hex-string cell representation for
  spread-across-all-row-groups shapes; the q6 gap (now 11.77s vs 2.74s
  in the 2026-07-13 clean baseline) needs either the representational
  fix (bytes/arrays on the decode path) or a token-level batched join.
  Both refuted branches preserved with full measurements.
- Build-infra: #293 filed (extract-state digest ignores .fsti —
  bit twice tonight); toolchain installer hardened earlier the same
  day (fstar.lib deps, tolerant apt, z3 switch pin).

Previous (2026-07-10 refresh: RIF tail burndown: **RIF 46 pass, 1
fail, 3 skip (of 50)** — up from 34/4/12 on 2026-07-05. The 2026-07-10
wave added the RIF-DTB string + rdf:PlainLiteral builtin families,
the EBusiness dateTime slice, pred:iri-string binding-pattern
execution, Exists-quantified conclusions, Uniterm argument-value
satellites + n-ary reification (retired the Factorial KNOWN-GAP),
per-document rif:local scoping (retired the Local_Constant/
Local_Predicate KNOWN-GAPs), OWL-Direct vocabulary-separation
inconsistency detection, cross-document constant-role tracking for
Multiple_Context_Error, and a wiki-vendored RDF-graph conclusion for
Constant_Equivalence_Graph_Entailment. The 1 remaining fail is the
RDF_Combination_Constant_Equivalence_4 corpus data defect (present in
the archived authoritative wiki source too); the 3 skips are List
terms (2) + the full date/time/duration builtin family (1), each
named. Floors held: SPARQL 631 pass, 0 fail; RDF 1031 pass, 0 fail.
See bin/rif-runner/README.md's disposition table.)

Previous (2026-07-05 goal wave: **ShEx 1181 pass, 1 mismatch
(upstream fixture defect), 0 deferred, 0 skipped (of 1182)** —
descendant-witness semantics from the inheritance paper, verified by
differential probe against @shexjs/validator. **RML rml-core 76
pass, 0 fail (of 76)** — joins (index-paired joinless RefObjectMaps
per spec), error-fixture validations, battery-visible rml_runner.
**RIF 34 pass, 4 labelled fails, 12 precise skips (of 50)** — DTB
builtins module, safeness/conformance checker, import-rejection
table; every entry scored or construct-named. **JSON-LD 460 pass,
1 fail, 6 skip (of 467)** — commit `a69aa2c`, the goal line: the 1
fail is the documented Ryu-class float-formatting case, the 6 skips
are JSON-LD 1.0-only tests. (The interim 437/22/8 from `2d3bddc` —
29 flips: CTD negatives, nested lists, @import merge, forward refs,
misc — was superseded the same day; if two same-day entries
disagree, resolve by commit order, not prose position.) KaRaMeL pipeline GREEN: krml installed
(~12 min recipe re-validated), 4 modules F-star->C->gcc with a 10/10
demo (tools/karamel-c-build.sh); SPARQL11.Algebra monomorphization
overflow confirms the stratification need. Bundle modularity
measured: parse-only entry 59KB gz vs 144KB full. Unit list gained
the new RIF modules (25/25). Floors held.)

Previous (ShEx-completion wave B: **1176 pass, 6
mismatch, 0 deferred, 0 skipped (of 1182)**. Runner side: focus
base-resolution fix (+25), recursive cycle-safe Imports (+17),
ShapeExternal (+4), bnode shape labels (+2), base-threaded schema
decoding (+2). Semantics side: diamond-dedup ancestor resolution,
running-intersection chain matching, unbounded-completion
restriction, abstract shapes per the inheritance paper's Definition
4 (+12). The 6 remainders: 1 upstream fixture defect
(start2RefS2.json has p1 where the canonical .shex has p2) + 5
vitals-RESTRICTS tracing to a distinct same-predicate exact-valued
TripleConstraint pairing gap in tc_choose_acc — one focused
follow-up. All floors held.)

Previous (ShEx-completion wave A: **1115 pass, 42
mismatch, 25 deferred, 0 skipped (of 1182)** — stage 4 backtracking
partition search, stage 5 recursion (coinductive visited-stack),
stage 6 EXTENDS per the inheritance-semantics paper, SemActs with
the Test extension, ShapeMap-form tests, 23 hand-translated ShExJ
twins with provenance (tests/shex-shexj-twins/), plus an XSD
leading-plus datatype fix. Remainder precisely triaged: 25
mismatches are a runner base-resolution bug, ~13 need
multi-ancestor/abstract inheritance, 18 deferred need Imports, 4
ShapeExternal, 2 bnode shape labels, 2 relative-IRI bases — wave B
in flight. All floors held: SHACL 120/120, RDFC 86/86, JSON-LD
404/52/11, SPARQL 631/0, RDF 1031/0, unit 23/23, npm 60/61.)

Previous (wave-10 battery: **OWL 2 RL maximally
complete** — PE 28 pass, 2 fail (the documented-impossible
comprehension pair), 0 skip; NE 6/0; Consistency 76/0/0;
Inconsistency 14/0/0 — via three new closure rules
(transitive-to-chain scaffold, cls-hv1/hv2, dt-range-clash) + the
Consistency functional-syntax path. JSON-LD toRdf 404/52/11 — the
@graph-container cluster fell to a spec decision table (plain
@container:@graph wraps unconditionally; @id/@index maps
conditionally — one dispatch arm changed, zero regressions across
the 27 previously-implicated tests). RIF 13 pass, 1 KNOWN-DEFECT
fail (W3C zip defect), 36 bucketed skips (of 50) — PlainLiteral
lang-tag decoding + OWL-Direct annotation exclusion
(OWL.DirectMapping.Filter.fst); rif_runner now has a build stanza
(manual installs were being silently reverted by chain rebuilds).
RML stage 2: RML.Sources.fst (JSON iteration + JSONPath subset) +
RML.Eval.fst (full term-map evaluation, IRI-safe encoding per spec)
— 60 pass, 6 documented mismatches, 10 stage-5/6 skips (of 76
rml-core JSON tests, scratch driver; runner is stage 8). Held: RDFC
86/86, SHACL 120/120, ShEx 1022, SPARQL 631/0, RDF 1031/0, unit
23/23, npm 60/61.)

Previous (wave-9 battery: JSON-LD toRdf 399 pass,
57 fail, 11 skip of 467 (alias-@value dispatch, fromMap
pop-suppression, property-scoped ordering; @graph-container fix
attempted, found to regress 22 tests, reverted with diagnosis). OWL
functional-syntax parser landed (Parser.OWLFunctional.fst) — zero
skips left in PE/Inconsistency, every non-pass now diagnosed: PE
27/3/0 (2 comprehension impossible + 1 needs chain-to-transitive
rule), Inconsistency 12/2/0 (both need cls-hv/datatype-range rules),
NE 6/0, Consistency 75/0/1. RIF measured against the real W3C Core
corpus (46 tests vendored): 11 pass, 3 fail, 36 skip of 50 total —
skips bucketed by construct (16 BLD builtins, 6 syntax-safeness, 6
import-rejection, …), 1 fail is a 2010-era defect in the official
W3C zip. RML stage 1: five kg-construct suites vendored (224
tests), RML.Mapping.fst decodes 73 of 76 rml-core mapping docs (3
are error fixtures). Held: RDFC 86/86, SHACL 120/120, ShEx
1022/11/123/26, SPARQL 631/0, RDF 1031/0, unit 23/23, npm 60/61.)

Previous (wave-8 battery — three suites now
complete: **RDFC-1.0 86 pass, 0 fail (of 86)** (Map tests compared
structurally per the suite README; HNDQ poison budget implements the
NegEval abort), **SHACL 120 of 120**, **RIF 4 of 4**. OWL 2 RL:
NegativeEntailment 6/0 via semantics-flavor dispatch (Direct vs
RDF-Based mode threading), Consistency 75/0 + 1 functional-syntax
skip, Inconsistency 11/0 + 3 FS skips, PE 27 + 2 comprehension
(definitively scoped out in scope.md) + 1 FS skip — every non-pass is
documented-impossible or awaits the planned functional-syntax parser
(docs/designissues/2026-07-05-owl-functional-syntax-plan.md). ShEx
battery-visible via bin/shex-runner: 1022 pass, 11 mismatch, 123
deferred, 26 skipped (of 1182) — XSD float/digit-facet fixes + regex
{0,m}/control-escape fixes flipped 20. JSON-LD toRdf 389/67/11
(protected-terms + processingMode clusters). Regex glue: #276+#277
fixed, 71-case pin battery, unit suite 23 files. RML program plan:
docs/designissues/2026-07-05-rml-program-plan.md. SPARQL 631/0, RDF
1031/0, npm 60/61 all held.)

Previous (wave-7 battery: JSON-LD toRdf 379 pass
77 fail 11 skip of 467 (+5, type-scoped context fixes); ShEx stage 3
triple-expression matching — 1005 of 1182 validation-manifest entries
match expected verdicts (31 triaged mismatches, 146 correctly
deferred); regex ? quantifier glue fixed (#276, 38-case unit pin
battery, unit suite now 22 files); canonicalize #272 hashing tail
fixed — 100k bnode-heavy 462.9s to 4.83s (96x), 300k timeout to
16.2s, byte-identical, rdfc10 84/1/1 exact; SPARQL 631/0 + RDF
1031/0 + SHACL 120/120 + OWL floors + npm 60/61 all held.
Process note: patch-script changes REQUIRE invalidating the
manifest entries of the modules they patch — see fast-verify-extract
skill.)

Previous (wave-6 battery: SPARQL 631/0, RDF
1031/0, RDFC-1.0 84 pass 1 fail 1 stub of 86, **SHACL suite complete:
core 98/0 report-isomorphism + sparql 22/0 of 22** (custom constraint
components, ASK+SELECT validators, $shapesGraph/$currentShape), OWL
RL PE 27/2/1 + NE 4/2 + Inconsistency 11/0/3, JSON-LD toRdf 374/82/11
of 467, RIF 4/0, ShEx stage 2 node-constraint validation 43 of 44
reachable manifest entries (regex ? glue bug #276 accounts for the
1), XSD.Datatypes foundation module landed (slice 1), dump-nq #272
tail fixed: near-flat ~40k triples/s from 10k to 300k (was 12k/s
degrading to stack overflow at 300k), unit 21/21 + npm 60/61 green.
Note: w3c_runner shows 2 RIF entailment fails when run from
ocaml-output/ — cwd-dependent file resolution, run from repo root.)

Spot-check 2026-07-03 (`bin/linux-x86_64/w3c_runner --all` on a fresh
clone with submodules initialised): SPARQL 631 pass, 0 fail; RDF 1031
pass, 0 fail. OWL 2 RL positive-entailment via `generate-report.sh`:
20 pass, 10 fail (out of 30). Turtle throughput re-measured the same
day: ~100k triples/s, near-linear to 1M triples (details in
`performance.md`). The module inventory and `assume val` tables below
were refreshed 2026-07-03 from the live tree.

This file is a **periodic refresh doc** — it goes stale within a week.
Update after material progress (suite-score movements, new F\* modules,
resolved `assume val`s).

## Standing priorities (as of 2026-07-16)

**Active /goal (owner, 2026-07-21, verbatim):** _"important fixes
urgent: RDF/XML 1.2, RDF 1.2 canonicalization (86) and entailment (74)
suites, the 6 residual SPARQL 1.2 eval fails, RML-star mapping
generation, and dashboard wiring (automate it for future seamless
expansion)."_

Current state against that goal (2026-07-21):
- SPARQL 1.2 eval fails: the goal says "6 residual"; wave 1 already
  cleared 3 (not-not, dup-VALUES-var, variable-GRAPH update →
  **sparql12 251/3**), so **3 remain**: nested-aggregate rejection,
  triple-term ordering (order-2), STRLANGDIR UTF-8 SRJ ingestion. All
  root-caused with fix sketches (see the day's SPARQL-1.2 investigation).
- Dashboard wiring: rdf12/sparql12 rows land in latest.json + a visible
  "W3C Working Drafts" section (done); the **automation** part — a suite
  registry so future suites auto-report without hand-editing
  generate-report.sh — is the next dashboard task.
- RDF/XML 1.2, RDF 1.2 c14n (86) + entailment (74), RML-star mapping
  gen: not started; these are the bulk of the remaining 1.2 work.

**Umbrella (reaffirmed owner, 2026-07-21):** drive conformance to 100%
for every standard. The /goal above is the current urgent slice.
Tracked under epic #305.

**Active /goal (owner, 2026-07-16, day-closure):** every W3C + ShEx
suite either fully green or every residual fail named with a one-line
written disposition (disputed-fixture / dependency-blocked /
planned-family); retire the last OCaml regex glue via the verified
engine; then publish reality — dashboard, README, site, and
completeness ledger refreshed to match the tree, closing with an
owner-readable day report. Also active (owner, 2026-07-16): the RDF
1.2 / SPARQL 1.2 upgrade investigation (un-parks the 2026-07-11
"RDF 1.2/star parked" steer; epic + measured census in flight on
branch rdf12-investigation).

**Umbrella /goal (owner, 2026-07-15): full standards compliance for all
W3C specs plus ShEx, with performance always also a priority.** This
is the umbrella: every W3C spec we touch (RDF, RDFS, OWL 2 all
profiles, SPARQL 1.1, SHACL, RDFC-1.0, JSON-LD, CSVW, GRDDL, RIF,
XSLT/XPath, VC/DID) driven to full conformance, plus ShEx (a Community
Group spec, explicitly in scope by owner direction), with measured
performance treated as a co-equal priority on every landing — a
compliance win that regresses wall-time needs its own measurement and
justification, per skills/perf-benchmarking. The deliverables and
directives below all serve this goal; a dashboard red always jumps
the queue.

**Prior /goal (owner, 2026-07-12):** three named deliverables, on top
of the standing directives below:

1. **OWL2 efficiently implemented, including the QL and DL/tableau
   flavours.** DL runs through `Tableau.Refute.fst` (wave program below);
   QL currently scores profile-QL Inc 6 pass, 0 fail and needs a
   dedicated efficiency + coverage pass (EL sits at 9 pass, 5 fail);
   "efficiently" means measured suite wall-time, not just pass counts.
2. **A solid XSLT, as comprehensive as possible without needing PSVI —
   ditto XPath.** XSLT 1.0 at 69 pass, 19 fail (of 88) with an active
   burndown (axes, match patterns, namespace order); the remaining fails
   are triaged into in-scope essentials vs PSVI/XPath-2.0-dependent
   (schema-aware) items, which stay out of scope by owner decision.
3. **Notebook cell cross-references everywhere.** The hub's reactive
   named-cell machinery (`reactive-cells.mjs`, posts 26–30) becomes the
   norm: all ~25 older posts (01–25, index, README) convert from
   anonymous redeclare-per-cell style to declare-once named cells so
   every doc supports referencing earlier cells' variables; gated per
   post by `tests/hub/postNN` (anti-pattern #28 applies).

**Standing directive (owner, 2026-07-11): on-disk SPARQL backend to
industry-mainstream perf** — inserts, reliability, query speed, disk
usage — holding 100% standards compatibility. Measured baseline
2026-07-12 (gene 889k quads, docs/test-results/competitive-bench.json):
disk usage WON (COTTAS 992K vs Jena TDB2 105M, ~108x); answers agree
with Jena+pyoxigraph on all 6 queries. **GROUP BY WON 2026-07-13**
(`f99bb64`, streaming fast path: detector + Parquet dictionary-page
distinct-predicate enumeration + a composing union capability): q5
23.05s -> 1.31s (17.6x), now ahead of Jena TDB2's 1.79s, answer
agreement exact vs the in-memory path, aggregates 47 pass, 0 fail.
Remaining gaps by measurement: OPTIONAL/FILTER 8.83s vs 2.07s (4.3x —
needs column-aware decode, a genuinely different fix; see the
2026-07-12 investigation's §e), point lookup 2.35s vs 0.93s (2.5x, S/O
offset sidecar). Priority order now: OPTIONAL/FILTER column-aware
decode, then the S/O offset sidecar; full-scan aggregates and GROUP BY
both beat TDB2.

**Prior /goal (owner, 2026-07-11), still standing:** the north star —
exemplary and FULL implementation of every official W3C RDF/semweb spec
we touch (RDF 1.2/star was un-parked 2026-07-16 — syntax/eval landed,
see above; protocols un-parked too), tracked in
[`w3c-completeness-ledger.md`](w3c-completeness-ledger.md), with full
coverage as the FOUNDATION FOR AUTOMATED PERF RESEARCH and every
capability getting an npm API + Hub page. Re-rank when one lands; a
dashboard red always jumps the queue. Three named thrusts carry it now:

**Update 2026-07-14 (obsolescence sweep):** thrusts 1 and 2 below have
both moved substantially since the baseline numbers were written —
OWL2 DL type-inconsistency is now 110 pass, 18 fail (out of 128, was
66/117 below); vc20_api and vc_di_eddsa are both fully green (59/0 and
31/0 respectively, was 22/59 and 26/31 below). See the dated ledger
entry at the top of this file for the wave-by-wave detail. The
narrative below is kept as the historical reasoning that shaped this
work, not the current score.

1. **OWL2 DL to full coverage** (epic #209). The staged wave program is
   [`2026-07-10-owl2-dl-completion-program.md`](../designissues/2026-07-10-owl2-dl-completion-program.md)
   (Waves A nominals · B datatype facets · C FP/IFP + finite-model · D
   PE-via-refutation + FS-only unskip · E budget/heuristics). Baseline:
   DL type-inconsistency 66 pass, 51 fail (of 117, 11 skip); soundness =
   exactly one `unexpected-inconsistency` (WebOnt-202, #236). **A first
   Wave-A probe was built, verified, and measured, then NOT landed**: a
   `CE_OneOf` nominal AST + `owl:oneOf` parsing + a sound
   `differentFrom`-all clash rule verified clean and held the soundness
   gate (exactly one `unexpected-inconsistency`), but scored 66/51
   UNCHANGED — the bare-O-rule clash fires on no corpus test — so it was
   reverted rather than land a zero-movement scaffold. The refuted
   hypothesis sharpens the real target: the corpus's nominal
   inconsistencies come through **counting over a nominal filler class**
   (`≥n P.{m nominals}`, n>m), not the bare O-rule, so the next attempt
   must build nominals together with nominal-aware cardinality and the
   lazy-merge/union-find machinery (Wave A proper + a bite of Wave C),
   landing only when it moves the number. Every wave holds the floors and
   the one-WebOnt-202 soundness exception.
2. **VC/DID conformance against the new interop environments** (epic
   #288) — plan in
   [`2026-07-11-vc-canivc-eecc-plan.md`](../designissues/2026-07-11-vc-canivc-eecc-plan.md).
   canivc.com (we run 3 of 10 suites) + EECC (Apache-2.0 fixtures to
   vendor; AGPL verifier as an HTTP interop target, never vendored).
   Tracks A2→A1→A3→B1→B2→B3→C. A2 first, biggest jump / no new crypto:
   wire `VC.Credential`'s structural checker (already 117 pass, 0 fail)
   into the vc-api-shim HTTP verify/issue path — the shim does zero
   structural validation today, the single root cause of vc20_api 22
   pass, 37 fail (of 59). Then the vc-di-eddsa gaps (26/5), a DID
   Resolution Result envelope, BitstringStatusList, ECDSA/P-256 (stretch,
   HACL\*-closure + wasm-gated). No hand-rolled crypto; shim stays
   zero-semantic-logic (rule #11).
3. **Verified-and-fast on-disk indexes + query optimization** — this is
   the perf-research foundation made concrete; deep dive in
   [`2026-07-11-ondisk-indexes-query-optimization-deep-dive.md`](../designissues/2026-07-11-ondisk-indexes-query-optimization-deep-dive.md).
   Ranked next-phase, toward dropping the rule-#11 qualifier: (1) a
   subject/object row-offset sidecar to close the bound-lookup gap
   (COTTAS 2.17s point / 4.07s join vs Jena TDB2 1.16–3.88s, same
   corpus); (2) Roaring Phase E as the shared rank/select core for that
   sidecar + HDT stage 5; (3) KaRaMeL-stratify `SPARQL11.Algebra`/`Store`
   (unblocks 16 C/wasm modules incl. the join executor); (4) finish the
   rule-#11 caveat-drop — storage companion writers Option-B→A, query
   retire #118/#254; (5) real cardinality estimation off the on-disk
   dictionaries (wire the unwired `SPARQL.Plan.Estimate/Pruning/
   AccessPath`); (6) zstd/RLE_DICTIONARY-v2 in the native writer to close
   its 12× size gap.

Landed 2026-07-05/06 database program (the read-write DB goal):
**Durable SPARQL UPDATE stages 1-4 + 8** — append-only delta log
with F\*-proved framing round-trips (five I/O `assume val`s under
issue #282, realised four ways: Unix, KaRaMeL C externs, IndexedDB
in the browser, in-memory buffer), merge-on-read with a proved
apply-entries equivalence lemma, compaction via atomic symlink swap
with an epoch guard in the read path, and `factoidal-http --rw`
serving SPARQL UPDATE + Graph Store Protocol. Crash-safety measured:
SIGKILL harnesses across the write stages (270+25+25 kill points)
accept zero torn or corrupt states; 6 concurrent readers during 40
writes observed 0 inconsistent reads. **Native COTTAS writer**
(`RDF.CottasStore.BaseWriter.fst`) — `factoidal import` / `compact
--native-writer`, DuckDB-byte-exact, removing Python from the store
lifecycle entirely (v1 emits DLBA+UNCOMPRESSED at ~133 B/quad on
disk, ~60x pycottas-zstd; RLE_DICTIONARY v2 in flight). **Unified
store architecture** — `store_caps`/`dataset_caps` capability seam
(`RDF.Store.Capabilities.fst`), `caps_of_backend` as the single
dispatch point (12 ad-hoc dispatchers deleted), delta overlay and
named graphs land through the same seam. **In-memory bytes store**
(`--data-cottas-mem`) — 64.4 B/quad for a corpus COUNT, 160.9 for
lookups, vs 877 B/quad on the heap store. **Perf vs peers**
(`2026-07-06-competitive-benchmark-results.md`): GROUP BY 600s→27s
(O(n²) append fixed; ~13x linear constant vs Jena remains), point
lookups 62s→17.7s (bound-side encode in flight); COTTAS full-scan
aggregates beat Jena TDB2. **Tri-target write path** — the delta log
runs natively, as KaRaMeL-extracted C (12/12 demo), and under
js\_of\_ocaml + wasm\_of\_ocaml with IndexedDB persistence proven
across real page reloads. **HDT stages 1-4** — verified container/
dictionary/triples readers plus SPO pattern resolution through the
capability seam (`57cb2ee`): `Parser.BallyhooHDT.fst` is pure Tot F\*,
12 assume vals + the opaque handle type eliminated, the 555-line
`ballyhoo_hdt_runtime.sh` shim deleted (#253), `--data-hdt` on the
CLI, 74/74 fixture checks + 6/6 backend-parity queries. Stage 5
(indexed rank/select shared with the Roaring track) is the remaining
HDT item. Hub grew to 18 posts; post 18 runs the durable-log
lifecycle live.

Landed 2026-07-05 wave 4 (all six agents gate-evidenced together):
SHACL phase 3 — core 98 pass, 0 fail (of 98) under the suite's full
report-isomorphism rule (was conforms-only), sh:sparql dispatch in
pure F\* with 17 pass, 5 fail (of 22; fails = custom constraint
components, documented); JSON-LD options block — toRdf 374 pass, 82
fail, 11 skip (of 467, was 307): @direction/rdfDirection, property
index containers, canonical xsd:double, well-formedness gates,
@prefix, keyword-lookalikes; RIF — live in-browser demo (rifSmoke +
general rifEval via Parser.RIFXML) AND bin/rif-runner running the 4
vendored W3C RIF cases end-to-end: 4 pass, 0 fail (scope.md updated
from "permanent SKIP" to supported subset); npm functional/dataflow
API (fn.js: frozen FnDataset, backend interface for future on-disk
COTTAS, builder seam for streaming parsers, memoized RDFC hashes,
cell/derive); all demo pages migrated to the npm package (legacy
client is now UI-only); unit run-all + build-ocaml.sh link order
fixed for the new SHACL→SPARQL11_Parser dependency.

Landed 2026-07-04 night wave: JSON-LD remote contexts + @import +
document base via the JSONLD.Loader seam (issue #275 closed) - toRdf
307 of 467; SHACL core validator slice 1 - 91 of 98 W3C core tests,
factoidal validate --shapes as the user tool (the goal's largest gap
is now a scored, burning-down number).

Landed 2026-07-04 evening wave: RDFC-1.0 to 82 pass, 3 fail, 1 stub
(of 86 - all remaining out of scope; within scope DONE) [**SUPERSEDED
2026-07-05**: the "out of scope" disposition was PREMATURE/WRONG — the 3
poison "evil" fails (test044c/045c/046c) and the poison-clique NegEval stub
(test074c) were all SOLVED the next day by the HNDQ work-budget approach
(docs/designissues/2026-07-05-rdfc10-poison-budget.md). RDFC-1.0 is now
**86 pass, 0 fail, 0 stub (of 86) — fully complete, nothing out of scope**];
OWL RL PE
25 of 30 (suite runs in 0.6s); JSON-LD toRdf 287 of 467; RDFS closure
33.2s to 1.39s on 27k triples (O(N^2) join order fixed); RFC 3986
IRI resolution as the first reusable-foundations module; JSON-LD
Playground demo + npm-on-Pages mirror; dev loop: no-op extract 48min
to 1s, layered-parallel extraction, hints measured-and-rejected,
affected-suite runner.

Landed 2026-07-04 (all gate-evidenced on claude/main): Later the same day: JSON-LD
Phases 3a+3b (W3C toRdf 33 -> 181 pass of 467); #269/#270 closed;
#272 serializer speedup (dump-nq 162 -> 12069 triples/s at 10k;
still superlinear at 100k, issue open); #273 RDF/XML overflow AND
silent >5k-triple truncation fixed (50k parses exactly); Turtle
pretty-printer (factoidal dump-turtle, 17/0 round-trip suite);
graphs API slice 1 (graphs list/get/hash/diff + npm graphs()/
canonicalHash(), 9/0); parse+serialize bench live on the dashboard. 2c and 2d
below; #262 sameAs closure rewrite; #21 exact on-disk counts; #267
COTTAS dataset semantics + #268 backend property paths (backend
parity 36 of 36, zero knowns); #271 canonicalize/dump-nq UTF-8
corruption + the mirrored-JSON-escape bug in SPARQL.JSON.Escape;
JSON-LD Phase 1 (RFC 8259 parser + expanded-form toRdf, 10 of 10
local fixtures) with the Phase 2 W3C-manifest runner scaffolded; PE
slice 1 (22 of 30). Three of the four serializer-side bugs were the
same bytes-vs-codepoints disease — the RDF.Unicode foundation module
in item 4 is where that class of bug goes to die.

1. **#118 — retire the COTTAS on-disk OCaml runtime** (928 lines of
   unverified glue). As of 2026-07-06 the production query path no
   longer calls it (`sc_solve`/`sc_estimate` rewired to F\* `_tok`,
   `9750eb7`/`9c3d160`); three non-production consumers still do, so the
   patch remains and #118 (delete it) is still open. Plan doc scoped,
   ukparliament-bench gated; row-by-row state in
   `docs/designissues/fstar-ocaml-boundary-audit.md`. Retiring it (zero
   live callers) is the precondition for dropping the rule-#11
   qualifier.
2. **#262 — OWL-RL sameAs closure blow-up** — diagnosed 2026-07-03
   (`2026-07-03-owl-rl-sameas-blowup-diagnosis.md`): measured O(k⁶)
   per closure step (163.87 s at a 24-individual sameAs clique); fix
   sketch is snapshot-fold + bucket lookups for the five sameAs
   rules. NOT the cause of the 10 PE fails; it bites ConsistencyTests
   — which currently **mask** the stall by passing on the un-closed
   graph after a 30 s cap trip (soundness hazard) — and the
   entailment-regime simple1 stall.
2b. **The 10 OWL RL positive-entailment fails** (20 pass, 10 fail of
   30 — the dashboard red) are semantic gaps, not timeouts: 7 missing
   bnode class-expression conclusions
   (complementOf/AllDifferent/unionOf/Restriction), 2 XSD
   range-hierarchy gaps, 1 no-premise. Separate work item from #262;
   needs rule-coverage additions in the OWL-RL rule set. Fix sketches:
   `2026-07-03-owl-rl-pe-fails-fix-sketch.md` (path to 27 pass, 2
   documented fails, 1 skip).
2c. **[DONE 2026-07-04]** Backend eval path skips the bnode-pattern rewrite — found by
   the Jena probe refresh (`2026-07-03-jena-probe-refresh.md`),
   invisible to the W3C dashboard: bnode-pattern SELECT/ASK via the
   CLI's default route match 0 rows (`SPARQL11.Store.fst` ~752 misses
   the `rewrite_query_bnodes_pattern` call the algebra path makes).
   Small F\* fix; gate on the jena basic probe returning to 20 of 20.
2d. **[DONE 2026-07-04]** No per-file blank-node scoping at dataset load — `_:x` in
   separately loaded files spuriously joins (`factoidal_cli.ml:112`;
   Jena graph probe 9 of 11, was 11 of 11). Bnode labels are
   document-scoped per RDF 1.1; decide loader-namespacing vs F\*
   dataset-merge fix.
3. **[DONE 2026-07-10]** Shrink `--admit_smt_queries` in
   `SPARQL11.Parser.fst` — both pragma regions removed (119 admitted
   definitions → 0); the file verifies in full under z3 4.13.3 with no
   `--lax`.
4. **Stratification + reusable foundations** — split
   `RDF.Graph.Executable` and `SPARQL11.Algebra` per the roadmap in
   `skills/fstar-module-style/SKILL.md`; commit-sized slices, suites
   green at each step. Owner directive 2026-07-04: the split's
   FIRST-CLASS deliverables are reusable foundation modules shared by
   every parser/serializer/evaluator instead of today's scatter —
   `RDF.IRI` (RFC 3986/3987; today: SPARQL11.IRI.Resolve +
   Parser.IRI + per-parser fragments), `XSD.Datatypes` (value spaces,
   canonical forms, numeric promotion; today embedded in
   SPARQL11.Algebra), `RDF.Unicode` (UTF-8/codepoints/escapes; today
   assume-vals + per-parser char logic — the new Parser.JSON escape
   handling should consume it), `RDF.LanguageTag` (BCP47 well-formed
   + case-insensitive comparison — fixes the known literal_eq gap
   where @en-US and @en-us compare unequal). JSON-LD phases 3-4 need
   RDF.IRI + RDF.Unicode, so extraction of those two leads.
5. **[SUITE COMPLETE, 2026-07-05 wave 6] SHACL** —
   `SHACL.Validation.fst` is a full validator: core 98 pass, 0 fail
   (of 98) under the suite's report-isomorphism comparison; sparql
   section 22 pass, 0 fail (of 22) including custom constraint
   components (sh:parameter + ASK/SELECT validators) and
   $shapesGraph/$currentShape pre-binding — the whole vendored suite
   passes, 120 of 120. `factoidal validate --shapes` is the user
   tool. One `assume val` left (`eval_sparql_target_select`,
   SPARQL-SELECT targets, unreachable in the suite, #181 stub patch). (`third_party/testing/shex` is
   ShEx, a different shapes language — program plan in
   `docs/designissues/2026-07-05-shex-program-plan.md`.)
6. **[DONE, 2026-07-05] RDFC-1.0 as a tool** — `factoidal
   canonicalize FILE` shipped; suite at 84 pass, 1 fail, 1 stub (of
   86) with SHA-256 + SHA-384 (the fail is a vendored-fixture
   artifact, the stub the poison-clique NegEval deferral — both
   documented out of scope). Canonical hashes feed the graphs API,
   the npm fn API's content identity, and cache keys. Remaining perf:
   canonicalize's own 100k+ HFDQ-hashing tail (#272 fixed the
   serializer side; hashing side still superlinear).
7. Small, fold into any session: `tests/local`
   scripts that need external corpora get skip-or-fetch treatment
   (parser regressions done 2026-07-03; ukparliament bench corpus is
   absent from fresh clones and self-skips in CI).
8. **`dump-nq`/`canonicalize` superlinear scaling + RDF/XML stack
   overflow** — found 2026-07-04 while building
   `tools/bench-parse-serialize.sh` (see `perf-benchmarking` skill).
   `factoidal count` scales linearly as expected (~80-90k triples/s
   through 1M), but on the *same* bnode-free fixtures
   `factoidal-dump-nq` and `factoidal canonicalize` are severely
   superlinear: `dump-nq` on 1,000 triples takes ~0.65s, on 2,000
   triples ~12.9s (should be ~1.3s if linear); `canonicalize` shows
   the same shape (1,000: ~0.46s, 2,000: ~8.6s). Both blow through a
   120s/run cap well before 100k triples — the new bench records this
   as a documented skip rather than hanging. Separately, RDF/XML
   parsing (`factoidal count FILE.rdf`) crashes with `Stack overflow`
   above ~10k triples, independent of the above. Not diagnosed or
   fixed here — needs a GitHub issue and a profiling pass (candidate
   suspects: whatever "sorted N-Quads" dedup/sort path `dump-nq` and
   `canonicalize` share that `count` doesn't use; non-tail recursion
   in `Parser.XML`/`Parser.RDFXML` for the stack overflow).

Perf experiment queue (ranked, from
`2026-07-03-shapes-canon-storage-strategies.md`): E1 characteristic-set
row clustering in the COTTAS writer (zero reader changes, measured on
ukparliament bench); E2 per-CS statistics sidecar for
`cottas_ondisk_estimate`; E3 canonical-hash sidecars + Merkle roll-ups
riding on `factoidal canonicalize` (item 6).

Standing discipline: **every session watches for perf optimisation
opportunities** while doing anything else — a suspicious phase in the
`Server-Timing` breakdown, a super-linear shape in a loop you read, a
list scan a bitmap could kill. Don't fix out-of-scope perf smells
mid-task; measure enough to file them here or as an issue, then
finish the task. Speed claims still need their own measured commit
(`perf-benchmarking` skill).

Done recently: in-memory index-build wall (#259, verified fixed
2026-07-03 — 137s → 2.2s on lifesci Q01, linear to 1M quads);
rdf-canon totals in latest.json; parser-regressions external-corpus
skip; SHACL suite vendored; current-state inventory refresh
(2026-07-03).

## F\* Specifications

Repository contains 90 F\* modules totalling 47517 lines of code. Key modules:

```
formal/fstar/

Core (RDF/SPARQL evaluation):
  SPARQL11.Algebra.fst            8793 lines, 11 assume val (query evaluator; +1 2026-08-22: extension_function_call, the §17.6 host registry hook, issue #463 — count re-measured with grep -c "^assume val", the old "13" had drifted)
  SPARQL11.Parser.fst             4522 lines (fully verified, zero admits since 2026-07-10)
  RDF.Graph.Executable.fst        4152 lines

Query planning (on-disk backend infrastructure):
  RDF.CottasStore.fst             2929 lines,  3 assume val (2026-08-24: was 10.
   Eight of the ten were the two directions of one token dictionary, not
   I/O; they are now the fields of `cottas_token_tables`, with the
   `Type0` predicate `token_tables_agree_with` replacing the prose
   soundness comment, `tables_of_handle_agree` proving the
   populated-handle instance, and `build_qp_row_agrees` deriving the
   caller-visible consequence. The three left are `cottas_ondisk_open`,
   `cottas_ondisk_close`, and `ondisk_token_tables_global` -- all I/O.
   Line count re-measured with wc -l; the old "1528" had drifted.)
  RDF.CottasStore.OnDiskIndex.fst  407 lines,  7 assume val
  SPARQL11.Store.fst               780 lines
  (RDF.CottasStore.OnDiskRuntime.fst — 117 lines, 15 assume val — DELETED
   #448 "Delete & dedupe", dead module, no caller anywhere in the tree;
   history: commit on branch delete-dead-store-modules)

RDF parsers (all F*-extracted):
  Parser.Turtle.fst               1918 lines
  Parser.RDFXML.fst               1159 lines
  Parser.NTriples.fst             1025 lines
  Parser.TriG.fst                  525 lines
  Parser.NQuads.fst                518 lines
  Parser.XML.fst                   680 lines (non-validating XML foundation)
  Parser.SRX.fst                   273 lines (SPARQL Results XML)
  Parser.CSVResults.fst            610 lines
  Parser.JSONResults.fst           408 lines
  Parser.IRI.fst                   447 lines
  Parser.Combinators.fst           396 lines (parser combinator foundation)

OWL/RIF:
  OWL.QueryRewrite.fst            1796 lines
  RIF.Core.Eval.fst                470 lines
  Tableau.fst                      1103 lines

Query planning and diagnostics:
  SPARQL.Protocol.fst             1229 lines
  SPARQL.HTTP.fst                  579 lines

Miscellaneous support:
  Parquet.Footer.fst              2591 lines,  3 assume val
  RDF.Canonical.fst               1142 lines,  1 assume val
  SHACL.Validation.fst            2546 lines,  1 assume val (phase 3: reports + sh:sparql)
  Parser.FastString.fst            342 lines,  0 assume val (re-founded on Parser.FastString.Spec.fst, G4/#358, 2026-08-10; sole surviving assume val for this family is unsafe_char_of_d7ff in the sibling Parser.FastString.CharBoundary.fst, 57 lines)
  Parser.BallyhooHDT.fst           352 lines,  0 assume val (STALE row -- stage 4, 2026-07-06, retired every assume val; not re-audited here, flagged in passing)
  Parser.BallyhooCOTTAS.fst        241 lines, 13 assume val (STALE row -- #448 wave 2 module 1, 2026-08-16, lifted 4 of 17; not re-audited here, flagged in passing)
  (Parser.BallyhooHDTQ.fst — 270 lines, 13 assume val — DELETED #448
   "Delete & dedupe", dead module, no caller anywhere in the tree;
   history: commit on branch delete-dead-store-modules)
  (Parser.BallyhooBloom.fst — 0 assume val — DELETED #448 "Delete &
   dedupe", zero callers anywhere; history: commit on branch
   delete-dead-store-modules)

Build and test harness:
  Makefile                         verify + extract-c targets
  build-ocaml.sh                   F* -> OCaml -> js_of_ocaml pipeline
  ocaml-patches.sh                 master script: applies all patches from
                                   minimal_regrettable_glue_code_each_with_an_open_issue/
  minimal_regrettable_glue_code_each_with_an_open_issue/
                                   individual patch files, each named
                                   <issue>_<description>.sh with GitHub issue
```

Inventory summary: 90 modules, 47517 lines total. The per-module `assume val` figures in the block above are a 2026-08-09 snapshot and their sum (141) is superseded: the measured count on 2026-09-03 is **82 across 18 modules**. Re-run the command in the `assume val` inventory section below rather than adding the rows up.

## Rule-by-rule proof program (owner-approved 2026-08-04, live)

Two lemma kinds per engine rule, tracked against the 84-function
engine ledger at the foot of `OWL.RL.Spec.fst`:

- **Licensing** (syntactic: every emission is input or one W3C-row
  application) — `OWL.RL.Refinement.fst`. Proved: eq-sym, eq-ref,
  prp-symp, scm-eqc1, scm-eqp1 — **5 of 34** row-implementing rules
  (+6 rows covered via the RDFS family in
  `RDF.Entailment.RDFS.Refinement.fst`). eq-trans in flight. prp-inv
  parked (task #36, proof-shape trap #3 in `fstar-module-style`).
  Two ledger claim-drift corrections came out of this: the
  `equivalent_class` / `equivalent_property` entries claimed
  cax-eqc/prp-eqp rows but implement scm-eqc1/scm-eqp1.
- **Truth-preservation** (semantic: emissions true in every model of
  the row's condition) — `OWL.Semantics.Soundness.fst`. Proved:
  domain, range, sameAs-symmetry, oneOf, sameAs-reflexivity family —
  **~5 of ~84**.
- **Index-hypothesis discharge (#338, CLOSED 2026-08-04)** — three
  modules make the wf hypotheses real: `RDF.Indexed.KeyInjectivity`
  (`sp_key` injective one-sided on U+001F-free keys; `ig_wf_sp` for
  separator-free graphs), `RDF.Entailment.RDFS.SepFree` (per-row
  conclusion cleanliness), `RDF.Entailment.RDFS.ChainWf`
  (`graph_sep_free g ==> closure_chain_wf g` with empty and
  non-empty machine-checked instances) — so
  `rdfs_closure_entails` now applies to concrete graphs, and the
  index-reading OWL rules (eq-trans, prp-trp, scm-eqc2, scm-eqp2,
  cls-hv*) are unblocked for licensing with `requires ig_wf_sp ig`.

## ⚠ Verification Gaps — Be Honest About These

**SPARQL11.Parser.fst** — CLOSED 2026-07-10. The file formerly carried
two `--admit_smt_queries true` pragma regions covering 119 definitions
(the mutually recursive expression and UPDATE parser blocks). Both
regions are gone: structural helpers were hoisted out of the fuel-based
mutual recursion with their own decreases metrics, prefix-map entries
now carry `wf_iri` by type, fixed vocabulary IRIs are proven well-formed
by `assert_norm`, and LIMIT/OFFSET results are ascribed to `nat`. The
whole file verifies under z3 4.13.3 with no `--lax` and no admitted
obligations.

**ASK query comparison in w3c_runner.ml** — ~~does not check the expected
boolean value~~ **FIXED (verified 2026-07-19)**: `w3c_runner.ml:1297-1298,
1488-1489` now evaluates the ASK boolean via the F\* evaluator and compares
it against the expected `.srx`/`.srj` boolean. ASK tests no longer pass
unconditionally; the pass count is not inflated by this.

**Blank node comparison** in the test runner — ~~simplified (any bnode
matches any other)~~ **FIXED (verified 2026-07-19)**: `w3c_runner.ml:751`
uses `RDF_GraphIsomorphism.graphs_isomorphic_outcome` (real
canonicalization-based isomorphism, `Iso_Equal`/`Iso_NotEqual`/
`Iso_BudgetExceeded` with a logged budget fallback), not lenient bnode
matching. (These two paragraphs were stale in the *optimistic-undersell*
direction — the runner is stricter than they claimed — an instance of the
doc-rot the 2026-07-19 audit flagged.)

## Known Gaps in RDF.Graph.Executable.fst

The F\* RDF graph spec uses **syntactic equality only**. It lacks:

- **Language tag case-insensitivity**: `literal_eq` compares `lang_tag` with `=`
  (string equality). Per RDF 1.1, `@en-US` and `@en-us` denote the same value.
- **Plain literal ↔ xsd:string equivalence**: Per RDF 1.1, `"foo"` (plain) and
  `"foo"^^xsd:string` are the same value. The spec treats them as distinct.
- **Datatype value equivalence**: `"010"^^xsd:integer` and `"10"^^xsd:integer`
  denote the same value. The spec compares lexical forms as strings.
- **RDFS closure rules**: No subClassOf/subPropertyOf inference, no domain/range
  type inference, no container membership property axioms.

These are not exotic features — they are what the W3C rdf-mt test suite tests.

## OCaml Output (extracted + test glue)

```
formal/fstar/ocaml-output/
  RDF_Graph_Executable.ml    F*-extracted OCaml
  SPARQL11_Algebra.ml        F*-extracted OCaml (patched for assume vals)
  SPARQL11_Parser.ml         F*-extracted SPARQL parser
  Parser_Combinators.ml      F*-extracted parser combinators
  Parser_NTriples.ml         F*-extracted N-Triples parser
  Parser_Turtle.ml           F*-extracted Turtle parser
  Parser_NQuads.ml           F*-extracted N-Quads parser
  Parser_TriG.ml             F*-extracted TriG parser
  Parser_XML.ml              F*-extracted XML parser
  Parser_RDFXML.ml           F*-extracted RDF/XML parser
  Parser_SRX.ml              F*-extracted SRX (SPARQL Results XML) parser
  Parser_CSVResults.ml       F*-extracted CSV/TSV results parser
  w3c_runner.ml              W3C manifest reader + test runner CLI (I/O glue)
  fstar_int_stubs.js         js_of_ocaml int stubs
```

Hand-coded parsers have been deleted. Legacy copies remain in `junk/do_not_use/hand_coded_parsers/` as a warning.

## assume val inventory

**82 assume val declarations across 18 modules**, measured 2026-09-03.

Re-run the count instead of trusting this number. From the repository
root:

```sh
# how many
grep -rhE '^[[:space:]]*assume val ' formal/fstar \
     --include='*.fst' --include='*.fsti' | wc -l
# how many modules, and which
grep -rcE '^[[:space:]]*assume val ' formal/fstar \
     --include='*.fst' --include='*.fsti' | grep -v ':0$' | sort -t: -k2 -rn
```

Measured 2026-09-03, largest first: `Parser.BallyhooCOTTAS` 13,
`SPARQL11.Algebra` 11, `RDF.CottasStore.LazyDict` 9,
`RDF.CottasStore.OnDiskIndex` 7, `RDF.Store.LazyTermCache` 6,
`RDF.Store.Columnar.DeltaLog` 5, `RDF.CottasStore.LazyDictRegistry` 5,
`VC.DataIntegrity` 4, `RDF.CottasStore.PageCache` 4,
`RDF.CottasStore.ColumnSeq` 4, `RDF.CottasStore` 3, `RDF.Canonical` 3,
`Parquet.Footer` 3, and one each in `Tableau.CountingOracle`,
`SPARQL.Eval.TimeBudget`, `SHACL.Validation`,
`Parser.FastString.CharBoundary`, `JSONLD.Loader`.

⚠️ This section said "138 across 20 modules" until 2026-09-03 and
carried its own note that the table was stale when written. CLAUDE.md
iron rule 3 said "~148". Neither figure was re-measured; both are now
corrected against the command above. A number in a document with no
command beside it is a claim, not a measurement.

The per-module tables below are the 2026-08-09 snapshot and are NOT
re-audited to the 2026-09-03 count. Read them for WHICH declarations
exist and why, never for HOW MANY.

Summary by module (largest first, as of 2026-08-09):

**SPARQL11.Algebra.fst** (11 assume vals — query evaluator core; verified
against the tree 2026-08-09 — `regex_match`/`regex_replace` are GONE from
this list: both retired to pure, verified F\* over the
Regex.Syntax/Exec/XSDPattern derivative engine, issue #304 phases 4-5.
`eval_expr_ebv`/`eval_expr_fwd`/`eval_exists_fwd` are GONE too: all three
are now concrete recursive F\* definitions — the last one,
`eval_exists_fwd`, retired by merging `eval_pattern_store`,
`substitute_existentials`(+`_list`/`_opt`), and `eval_exists` into one
`let rec ... and ...` clique, termination via `pattern_size`/`expr_size`
+ a lexicographic phase tiebreak):

| assume val | Purpose | Stub |
|-----------|---------|------|
| `hash_md5` | MD5 hash | OCaml `Digest` (issue #63 patch) |
| `hash_sha1` | SHA-1 hash | OCaml `Digest` (issue #63 patch) |
| `hash_sha256` | SHA-256 hash | OCaml `Digest` (issue #63 patch) |
| `hash_sha384` | SHA-384 hash | OCaml `Digest` (issue #63 patch) |
| `hash_sha512` | SHA-512 hash | OCaml `Digest` (issue #63 patch) |
| `string_uppercase_unicode` | SPARQL UCASE | `250_unicode_case_mapping.sh` |
| `string_lowercase_unicode` | SPARQL LCASE | `250_unicode_case_mapping.sh` |
| `fx_current_datetime` | SPARQL NOW() | `287_fx_current_datetime.sh` |
| `service_endpoint_lookup` | SPARQL SERVICE | `57_service_client_bind.sh` (host-defined per spec) |
| `eval_subselect_fwd` | forward decl (subqueries) | wired in `62_forward_ref_wiring.sh` |
| `eval_property_path_fwd` | forward decl (property paths) | wired in `62_forward_ref_wiring.sh` |

**Other modules with assume vals** (128 total, not re-audited this
landing — this figure predates the correction above and may itself
carry unrelated drift): Ballyhoo HDT parsers (47: Parser.BallyhooCOTTAS.fst 17, Parser.BallyhooHDTQ.fst 17, Parser.BallyhooHDT.fst 13 — STALE as of #448 wave 2, 2026-08-16: BallyhooCOTTAS is now 13 (4 lifted, module 1), BallyhooHDTQ is now 13 (4 lifted, module 2), BallyhooHDT is now 0 (stage 4, 2026-07-06, predates this sweep) — the 47-figure below has NOT been subtracted, out of scope for this HDTQ-only audit, same policy as the FastString parenthetical two clauses down), on-disk store/indexing (44: RDF.CottasStore.OnDiskRuntime.fst 15, RDF.CottasStore.fst 10, RDF.CottasStore.OnDiskIndex.fst 7, RDF.CottasStore.LazyDict.fst 9, RDF.CottasStore.LazyDictRegistry.fst 5), fast string parsing (STALE as of 2026-08-10 FastString re-founding — was 7: Parser.FastString.fst, now 0 there / 1 moved to the sibling Parser.FastString.CharBoundary.fst; the 7-figure below has NOT been subtracted out of the 128 total, since that would require re-auditing the whole breakdown, out of scope for this FastString-only sweep), lazy term caching (10: RDF.Store.LazyTermCache.fst 6, RDF.Store.HDTTermCacheRegistry.fst 4), misc (11: Parquet.Footer.fst 3, RDF.CottasStore.ColumnSeq.fst 3, SHACL.Validation.fst 3, Util.Log.fst 5).

## Plain-English Status Summary (as of 2026-05-07)

Factoidal is a formally verified RDF/SPARQL implementation written in F\* and
tested against the official W3C conformance suites. SPARQL UPDATE, HTTP
protocol, GSP, and SERVICE are live. The core SPARQL evaluator + updater
passes 630 of 631 applicable query/syntax/update/protocol tests (99.8%),
with perfect scores across every suite except entailment, where one OWL
case still fails (RIF-style rule entailment, out of scope for OWL-DL).
Suites at 100%: add, aggregates (47/47), basic-update (13/13), bind,
bindings, cast (6/6), clear, construct (7/7), copy, csv-tsv-res, delete,
delete-data, delete-insert, delete-where, drop, exists, functions (75/75),
grouping, http-rdf-update (19/19), json-res, move, negation (12/12),
project-expression, property-path (33/33), protocol (34/34), service (7/7),
service-description (3/3), subquery (14/14), syntax-fed, syntax-query
(94/94), syntax-update-1 (54/54), syntax-update-2, update-silent (13/13).

On the RDF parsing side, **all six RDF suites are at 100%**: rdf-turtle
313/313, rdf-trig 356/356, rdf-n-triples 70/70, rdf-n-quads 87/87,
rdf-xml 166/166, rdf-mt 39/39 (1031/1031 combined).

(ASK query comparison and blank-node graph isomorphism in the test
runner: see "⚠ Verification Gaps" above — both were fixed 2026-07-19,
not lenient.)

## W3C Test Results (as of 2026-05-07)

**SPARQL 1.1 — 630 pass, 1 fail (out of 631)**

Per-suite: add 8/8, aggregates 47/47, basic-update 13/13, bind 10/10,
bindings 11/11, cast 6/6, clear 4/4, construct 7/7, copy 6/6, csv-tsv-res 6/6,
delete 19/19, delete-data 6/6, delete-insert 17/17, delete-where 6/6,
drop 4/4, entailment 69/70, exists 6/6, functions 75/75, grouping 6/6,
http-rdf-update 19/19, json-res 4/4, move 6/6, negation 12/12,
project-expression 7/7, property-path 33/33, protocol 34/34, service 7/7,
service-description 3/3, subquery 14/14, syntax-fed 3/3, syntax-query 94/94,
syntax-update-1 54/54, syntax-update-2 1/1, update-silent 13/13.
Single remaining fail: one entailment case (RIF-style rule entailment,
out of scope for OWL-DL).

**RDF 1.1 — 1031 pass, 0 fail (out of 1031)**

Per-suite: N-Triples 70/70, Turtle 313/313, N-Quads 87/87, TriG 356/356,
RDF/XML 166/166, rdf-mt 39/39. RDF/XML reached 166/166 after the 2026-04-23
through 2026-05-07 fixes (reification, UTF-8 char refs, RFC 3986 resolver,
NCName codepoint validator, mutual-exclusion rules, xml:base scoping,
empty-property-element-as-bnode, parseType="Literal" canonicalisation,
duplicate-rdf:ID tracking, processing-instruction-in-property-element).

**Combined: 1661 pass, 1 fail (out of 1662).**

Session delta (from morning baseline 1514/81):

  +1   SPARQL REPLACE: codepoint-aware UTF-8
  +3   SPARQL UPDATE ADD/COPY/MOVE no-op on missing source
  +6   Turtle/TriG reject forbidden-char UCHAR escapes
  +1   TriG reject bare collection as sole statement
  +3   RDF/XML allow rdf:Seq/Bag/Alt as property element names
  +1   Parser.XML encode numeric char refs as UTF-8
  +1   codepoint-aware NCName validator
  +5   rdf:bagID + RDF 1.1 attribute mutual-exclusion rules
  +2   xml:base/lang/namespaces don't leak to siblings
  +4   delegate RDF/XML IRI resolution to RFC 3986 v2
  +1   reject rdf:li as attribute
  +8   reification quads from rdf:ID on property elements
  +1   split node vs property mutual-exclusion rules
  +4   empty-property-element with property attrs → bnode object
  +1   strip fragment from xml:base
  +1   reify parseType="Collection" with rdf:ID
  ≡    bnode labels without leading `_:` (cosmetic; runner's lenient
       bnode compare hid it but downstream serialisers now round-trip)
  = +43 net.

**RDF 1.1 Model Theory — 39 pass, 0 fail (39 total)**

All rdf-mt tests pass: literal equivalence, datatype handling, RDFS closure
rules, language tag normalization, value-space entailment with consistent
blank node mapping.

## What rdf-mt Actually Tests (39 tests)

| Category | Count | What It Tests | F\* Status |
|----------|-------|---------------|------------|
| Simple matching | 7 | Language tag distinction, URI matching, reification non-entailment | **PASS** |
| Literal/datatype semantics | 20 | Value equivalence, plain↔xsd:string, lang tag case, ill-formedness | **PASS** |
| RDF closure rules | 4 | Container membership (rdf:\_n), rdfs:member superProperty | **PASS** |
| RDFS closure rules | 14 | subClassOf, subPropertyOf, domain, range, intensional semantics | **PASS** (via ocaml-patches.sh closure) |
| Advanced model theory | 3 | Value space disjointness, completeness axioms | **PASS** |

## What Was Removed (junk/do_not_use/)

Everything in `junk/do_not_use/` is **vibe-coded or derived from vibe-coded
artifacts**. Do not use it. Do not revive it.

## The Plan

### Architecture

```
F* formal spec (the product)
    |
    v
fstar.exe --codegen OCaml (extraction, proof-erased)
    |
    v
OCaml test runner (minimal I/O glue only)
    |-- reads W3C manifest files from disk (I/O)
    |-- calls F*-extracted parsers for .rq/.ttl/.nt/.nq/.trig/.rdf/.srx
    |-- calls F*-extracted evaluator
    |-- compares actual vs expected (using F*-extracted comparison)
    |-- emits pass/fail per test
    v
W3C SPARQL 1.1 + RDF 1.1 conformance results
```

### Phase 1 — SPARQL test infrastructure (DONE)

W3C test runner works. SPARQL 1.1 query/syntax/update/protocol coverage
is 630 pass, 1 fail (out of 631). See "W3C Test Results (as of
2026-05-07)" above for the per-suite breakdown.

### Phase 2 — Fix RDF semantics in F\* (MOSTLY DONE)

1. **Language tag case-insensitive comparison** — DONE (`lang_tag_eq` in F\*)
2. **Plain literal ↔ xsd:string equivalence** — DONE (`literal_value_eq`)
3. **Datatype value space equivalence** — DONE (`datatype_value_eq`, `normalize_integer_lexical`)
4. **RDFS closure rules** — DONE (`rdfs_closure` with subPropertyOf, domain, range, subClassOf, container membership)
5. **Simple entailment** (blank node as existential variable) — DONE.
   rdf-mt 39 pass, 0 fail (out of 39; docs/test-results/latest.json,
   key "rdf-mt"). `RDF.Entailment.Simple.fst` implements the
   blank-node homomorphism search used by the SPARQL entailment
   regime (`RDF.Entailment.Regime.fst`).

### Phase 3 — F\* parsers (IN PROGRESS)

Replace hand-written OCaml parsers with F\*-extracted implementations.

**Parser architecture**: `Parser.Combinators.fst` provides the combinator
foundation (pchar, pstring, psat, pbind, pmap, palt, pmany, etc.). All parsers
are built on this. `Parser.XML.fst` is a **non-validating XML parser** — it
reads well-formed XML into a tree but does NO DTD processing, NO external entity
resolution, NO schema validation. Only predefined entities (&amp; &lt; &gt;
&quot; &apos;) and character references (&#123; &#x1A;). Namespace prefixes are
preserved as part of element/attribute names (namespace URI resolution is the
RDF/XML layer's job, not the XML parser's).

1. N-Triples parser in F\*
2. Turtle parser in F\*
3. N-Quads parser in F\*
4. TriG parser in F\*
5. RDF/XML parser in F\* (uses Parser.XML.fst — non-validating XML parser)
6. CSV/TSV results format parser in F\*
7. SRX (SPARQL Results XML) parser in F\*
8. SPARQL query parser in F\* (SPARQL11.Parser.fst started)

### Phase 4 — Close SPARQL gaps

Working from test failures, extend the F\* SPARQL spec:

1. **Result formats** — JSON Results (`application/sparql-results+json`),
   CSV (`text/csv`), TSV (`text/tab-separated-values`) serializers in F\*.
   SRX parser already exists; JSON/CSV/TSV result parsers needed for test
   comparison. ~20 tests blocked.
2. **SPARQL UPDATE** — INSERT DATA, DELETE DATA, INSERT/DELETE (with WHERE),
   LOAD, CLEAR, DROP, ADD, MOVE, COPY, CREATE. Requires mutable graph store
   model in F\*. 205 tests. Tracked by #59.
3. **SPARQL Protocol** — HTTP interface for query and update operations.
   34 tests. Requires HTTP server, which can use `assume val` with OCaml
   stub (see I/O and networking below).
4. **SERVICE (federated query)** — Requires HTTP client to contact remote
   SPARQL endpoints. 7 tests. Tracked by #57.
5. **Service Description** — 3 tests.

### Phase 5 — I/O, Networking, and Async

F\* extracted code is pure/total by default. Networking (SERVICE, Protocol,
LOAD) requires I/O effects. Strategy:

- **`assume val` for I/O primitives.** Declare HTTP client/server operations
  as `assume val` in F\* with OCaml stubs. This keeps the verified boundary
  around query semantics while allowing real network operations.
- **Simple synchronous blocking API.** For `web_fetch : url -> result`, a
  blocking OCaml stub using `Unix.open_connection` or `Cohttp_lwt_unix` is
  the simplest approach. Good enough for test runner and CLI usage.
- **Async considerations for extracted applications.** When F\*-extracted code
  runs in a larger async context (e.g., a web server), the blocking stubs
  become a problem. Options:
  1. **Thread pool** — run blocking F\* calls in a thread pool, integrate
     with Lwt/Async via `Lwt_preemptive.detach` or similar.
  2. **Effect-polymorphic F\*** — F\* has `Effect` and `PURE`/`DIV`/`ST`
     effect system. In principle, I/O effects can be modeled, but extraction
     of effectful code to async OCaml is not well-supported by F\* today.
  3. **js_of_ocaml + promises** — for browser/Node targets, blocking I/O
     is impossible. The js_of_ocaml path would need promise-based stubs
     with continuation-passing, which is architecturally different.
  The current plan: start with blocking stubs (#57), document the limitation,
  and track async extraction as a separate research issue.

### Phase 6 — Verified extraction pipeline

- Low\* rewrite for standalone C extraction via KaRaMeL
- CI: verify F\* → extract → test → sign
