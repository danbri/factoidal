# RDF 1.2 and SPARQL 1.2 semantics in the F\* tree

Date: 2026-09-07. Tree: `formal/fstar` (the F\* engine). Worktree branch
`wt/fstar-rdf12`. A sibling record covers the Lean 4 tree; the coordinator
merges the two.

Owner instruction that opened this work, 2026-09-07, verbatim:

> "For RDF/SPARQL 1.2, we MUST HAVE THE SEMANTICS. It is the foundation for
> EVERYTHING WE ARE DOING HERE. If 1.2 semantics is problematic we need a
> tight testcase explaining this. Both Lean4 and F\*. Test both
> comprehensively, and look for additional opensource 1.2 tests for both RDF
> and SPARQL."

## 1. Measured state, before this work

Every vendored RDF 1.2 and SPARQL 1.2 manifest, run through
`bin/darwin-arm64/w3c_runner` at commit `2715d520c`, 2026-09-07.
Corpus: `third_party/testing/w3c` submodule, pinned commit
`35c503a6323db83c2e54ff404387210c20d57c18`
(provenance: `third_party/testing/w3c-rdf12-PROVENANCE.md`).

| Suite (runner flag) | Result |
|---|---|
| `--rdf12` rdf-n-triples/syntax | 29 pass, 0 fail (out of 29) |
| `--rdf12` rdf-n-quads/syntax | 27 pass, 0 fail (out of 27) |
| `--rdf12` rdf-turtle/syntax | 67 pass, 0 fail (out of 67) |
| `--rdf12` rdf-turtle/eval | 29 pass, 0 fail (out of 29) |
| `--rdf12` rdf-trig/syntax | 35 pass, 0 fail (out of 35) |
| `--rdf12` rdf-trig/eval | 25 pass, 0 fail (out of 25) |
| `--rdf12` rdf-xml/eval | 30 pass, 0 fail (out of 30) |
| **`--rdf12` total** | **242 pass, 0 fail (out of 242)** |
| `--rdf12c14n` rdf-n-triples/c14n | 41 pass, 0 fail (out of 41) |
| `--rdf12c14n` rdf-n-quads/c14n | 41 pass, 0 fail (out of 41) |
| **`--rdf12c14n` total** | **82 pass, 0 fail (out of 82)** |
| **`--rdf12entail` rdf-semantics** | **41 pass, 3 fail, 3 skip (out of 47)** |
| `--sparql12` codepoint-escapes | 8 pass, 0 fail (out of 8) |
| `--sparql12` eval-triple-terms | 41 pass, 0 fail (out of 41) |
| `--sparql12` expression | 1 pass, 0 fail (out of 1) |
| `--sparql12` grouping | 1 pass, 0 fail (out of 1) |
| `--sparql12` lang-basedir | 11 pass, 0 fail (out of 11) |
| `--sparql12` rdf11 | 3 pass, 0 fail (out of 3) |
| `--sparql12` syntax | 2 pass, 0 fail (out of 2) |
| `--sparql12` syntax-triple-terms-negative | 65 pass, 0 fail (out of 65) |
| `--sparql12` syntax-triple-terms-positive | 113 pass, 0 fail (out of 113) |
| `--sparql12` version | 9 pass, 0 fail (out of 9) |
| **`--sparql12` total** | **254 pass, 0 fail (out of 254)** |

Harness diagnostics report zero escape branches on every suite
(`budget_exceeded:0 gsp_seed:0 no_manifest:0 zero_tests:0`), so no suite
score above is inflated by a silent cap.

The task brief carried older figures (RDF 1.2 212 pass, SPARQL 1.2 248 pass
6 fail, "c14n 1.2 (86 tests) open"). Those are stale: c14n and the SPARQL
1.2 fails had already landed. `rdf-semantics` is the only 1.2 suite in the
F\* tree that is not clean, and it is the semantics suite, which is what the
owner's instruction is about.

### The six non-passing `rdf-semantics` tests, by cause

| Test | Regime | Grading | Cause |
|---|---|---|---|
| `annotation` | simple | FAIL | Upstream fixture defect. Tight case TC-1 below. |
| `annotation-unfolded` | simple | FAIL | Same defect, other direction. TC-1. |
| `triple-terms-propositions` | RDFS | FAIL | Missing semantic condition: a triple term denotes an `rdfs:Proposition`. Engine gap, fixed here. |
| `malformed-literal` | RDF | SKIP | `mf:result false` (an inconsistency test). Harness had no arm for it. Fixed here. |
| `malformed-literal-control` | RDF | SKIP | Same. Fixed here. |
| `literal-type` | RDF | SKIP | Upstream manifest typo makes the entry unreadable. Tight case TC-2 below. |

## 2. Tight test cases

Fixtures and a W3C-shaped manifest are at
`tests/local/rdf12-semantics-tight/`. Run them with:

```
RDF12_TESTS_BASE=tests/local bin/<platform>/w3c_runner \
  --rdf12entail rdf12-semantics-tight
```

`RDF12_TESTS_BASE` is a new runner environment override. The vendored tree
is never edited (third-party vendoring policy,
`docs/designissues/2026-05-07-io-verification-and-third-party.md`).

### TC-1 — the annotation block `{| ... |}`: two readings, one corpus

Two entries in `rdf12/rdf-semantics/manifest.ttl` describe an expansion of
the RDF 1.2 Turtle annotation syntax that contradicts the expansion the
**same upstream commit's** Turtle 1.2 evaluation oracles define.

The action, `rdf-semantics/test007a.ttl`:

```turtle
prefix : <http://example.com/ns#> .
:a :b :c {| :p1 :o1 |}.
```

**Reading A** — RDF 1.2 Turtle, "Reifying Triples and Annotation Syntax". A
`{| ... |}` block with no explicit reifier introduces a fresh blank node
reifier `r`, asserts `r rdf:reifies <<( s p o )>>`, and hangs the block's
predicate-object list on `r`. The base triple stays asserted. Three
triples:

```turtle
:a :b :c .
_:r rdf:reifies <<( :a :b :c )>> .
_:r :p1 :o1 .
```

This reading is not an interpretation on our part. It is written down as an
expected result in the same repository, at the same pinned commit, in
`rdf12/rdf-turtle/eval/turtle12-eval-annotation-01.nt`:

```
<http://example/s> <http://example/p> <http://example/o> .
_:anon <http://example/r> <http://example/z> .
_:anon <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> <<( <http://example/s> <http://example/p> <http://example/o> )>> .
```

Factoidal implements reading A. All 67 RDF 1.2 Turtle syntax tests and all
29 Turtle evaluation tests pass, `turtle12-eval-annotation-01` through
`-05` included.

**Reading B** — the graph the `annotation` entry names as its `mf:result`,
`rdf-semantics/test007r2.ttl`:

```turtle
:a1 :p1 <<( :a :b :c )>>.
```

Reading B cannot be entailed by the action under any RDF 1.2 entailment
regime, for a reason that does not depend on which expansion is right: the
IRI `:a1` does not occur in the action at all, under either reading. An IRI
in the consequent denotes a fixed resource; no instance mapping can
introduce it. The same holds for `annotation-unfolded`, which asks the
2-triple `test007a2.ttl` (`:a :b :c` plus `:a1 :p1 <<( :a :b :c )>>`) to
entail the 3-triple expansion of `test007a.ttl`: the action carries no
`rdf:reifies` triple, so it cannot entail one.

The two entries are consistent with each other only under a third
expansion, in which `{| :p1 :o1 |}` on `:a :b :c` yields `:a1 :p1
<<( :a :b :c )>>` — an expansion that names an IRI appearing nowhere in the
input. No reading of the specification produces that. Note also that
`test007r2.ttl` is byte-identical to `test001a.ttl`, which is what a
copy-paste slip looks like.

Both entries carry `rdft:approval rdft:NotClassified` — the whole
`rdf-semantics` manifest does — so neither has been reviewed by the
working group. Both `rdfs:comment`s say "This is about shorthand
expansion, and is not really a semantics test."

**Decision.** Keep reading A. Do not change the engine to satisfy these two
entries; satisfying them would break the 96 Turtle 1.2 tests that encode
reading A, which is the stronger evidence. `annotation` and
`annotation-unfolded` stay as 2 fails against the vendored suite, recorded
here rather than suppressed. Three entries in the tight-case manifest pin
the decision: `annotation-expansion-entailed` (positive, reading A),
`annotation-cg-reading-not-entailed` and `annotation-unfolded-not-entailed`
(the two vendored entries, graded the other way round).

**Action outstanding:** report to `w3c/rdf-tests` upstream. Not yet filed.

### TC-2 — `literal-type` is unreachable because of a manifest typo

`rdf12/rdf-semantics/manifest.ttl` line 247 writes:

```turtle
  test:approval test:NotClassified .
```

`test:` is never declared in that document; the intended prefix is `rdft:`,
as every other entry in the same file uses. A conforming Turtle parser
rejects the statement, and with it the whole `trs:literal-type` block —
`mf:action`, `mf:result`, `mf:name` and all. The runner's manifest loader
is lenient with a stderr diagnostic (issue #334), so the file's other 46
entries survive; `literal-type` does not, and is reported as a skip with no
name.

The test itself is meaningful and states an RDF 1.2 D-entailment condition:
`:a :b "42"^^xsd:integer` entails `:a :b _:x . _:x rdf:type xsd:integer` —
a literal denotes an instance of its datatype. Re-stated verbatim as
`trs:literal-type` in the tight-case manifest.

**Status: implemented.** The generalized-triple antecedent added in this
landing (section 3) makes the condition expressible — the consequent needs a
blank node to bind to a literal in subject position, which it now can — and
`literal_type_gtriples` emits it. The rule strengthens the antecedent for all
22 RDF-regime tests including nine negative ones, so it was measured before
and after: the vendored `rdf-semantics` suite is unchanged at 44 pass, 2
fail, 1 skip, and `trs:literal-type` in the tight-case suite goes from fail
to pass.

**Action outstanding:** report the typo to `w3c/rdf-tests` upstream.

### TC-3 — malformed literals and D-inconsistency

`malformed-literal` and `malformed-literal-control` are graded
`mf:result false`: the question is not "does the action entail this graph"
but "is the action graph inconsistent". The harness had no arm for that
shape and skipped both.

RDF 1.2 Semantics: a literal whose lexical form is ill-formed for a
recognized datatype has no value, so a graph asserting it has no model.
`malformed-literal-control.ttl` asserts one directly; `malformed-literal.ttl`
puts it inside a triple term, and the entry's own comment states the
intended answer — "Malformed literals are allowed in triple terms, but cause
inconsistency."

Implemented as `RDF.Entailment.Regime.rdf_inconsistent`, a predicate
separate from `entails_rdf`. Deliberately separate: the same manifest grades
`malformed-literal-bnode-neg` and `malformed-literal-no-spurious` as
NegativeEntailmentTests over `malformed-literal.ttl`, and an inconsistent
graph D-entails everything, so folding inconsistency into `entails_rdf`
would make those two entries contradictory with the two above. The suite
asks the inconsistency question only through `mf:result false`, and only
that arm consults the predicate.

The tight-case manifest adds `well-formed-literal-consistent`, a vacuity
guard: a checker that answered "inconsistent" for every graph would
otherwise score two out of two on the vendored pair.

## 3. Engine changes

All in `formal/fstar/RDF.Entailment.Regime.fst`; verified under z3 4.13.3
with no `--lax` (`make verify-RDF.Entailment.Regime`).

### Generalized-RDF antecedent

RDF 1.2 Semantics states its semantic conditions over a term universe in
which a triple term, or a literal, can be the subject of a derived triple.
`RDF.Term.triple` cannot hold that, because `RDF.Term.subject = S_IRI |
S_BNode` — which is correct, since no RDF 1.2 concrete syntax can write such
a triple.

Rather than widen `RDF.Term.subject` (which would reach every parser,
serializer and store in the tree for a condition no syntax can express), the
regime layer closes the **antecedent** into a subject-generalized triple:

```fstar
noeq type gtriple = { gs : rdf_term; gp : wf_iri; go : rdf_term }
```

The **consequent** stays `list triple` — it is always parsed from a concrete
syntax. `match_subj_g` widens only the ground side of subject matching, so a
consequent blank node may bind to a triple term. `try_match_g` / `try_alts_g`
mirror `RDF.Entailment.Simple`'s backtracking search with the same
lexicographic termination measure; `match_term` is reused unchanged.

`RDF.Entailment.Simple` is untouched, so its refinement, model-theory and
boundary proofs are unaffected.

### Triple terms denote propositions

`proposition_gtriples` emits `<<( s p o )>> rdf:type rdfs:Proposition` for
every triple term occurring in the graph, nested ones included.
`entails_rdfs` and `entails_rdfs_plus` now run over
`rdfs_regime_gclosure`, which is the ordinary RDFS closure embedded as
gtriples plus these assertions.

This is the general condition of which the existing `rdf12_reifies_closure`
step (`X rdf:reifies Y` gives `Y rdf:type rdfs:Proposition` for an IRI or
blank-node `Y`) is the corollary for reified objects that a `triple` subject
can hold.

### RDFS rules whose conclusion is about a triple term or a literal

Two residual incompletenesses were found by writing the tests for them
first. Neither is exercised by any vendored fixture; both are tight cases
TC-4 and TC-5 in the local suite, and both failed before the fix.

`RDFS.Closure` works on `triple`, so the two RDFS rules whose conclusion can
be about a triple term or a literal were unreachable to it:

- **rdfs3** — `s p o` with `p rdfs:range D` gives `o rdf:type D`, and `o`
  may be a triple term or a literal. Applied as `rdfs3_over_gtriples`
  against the closed antecedent, for those two object shapes only; IRI and
  blank-node objects are already handled inside the fixed point.
- **rdfs9** — `x rdf:type c` with `c rdfs:subClassOf d` gives
  `x rdf:type d`, and `x` is a triple term for every proposition assertion
  and a literal for every datatype-instance assertion. Applied as
  `rdfs9_over_gtriples`. One pass suffices for the class hierarchy because
  rdfs11 (subClassOf transitivity) has already reached its fixed point
  inside `rdfs_regime_closure`, so the lookup returns transitive
  superclasses. No RDFS rule has a premise that can be a generalized
  triple other than these two, so one pass is complete for the RDFS rule
  set rather than merely enough for the fixtures.

Separately, the RDF 1.2 vocabulary axiom
`rdf:reifies rdfs:range rdfs:Proposition` is now seeded before the RDFS
fixed point, so an `rdf:reifies` triple **derived** inside the loop — by
rdfs7 from a subproperty of `rdf:reifies` — triggers the range condition.
Before, the reifies step ran once before the loop and derived triples were
missed (TC-4). The pre-pass `rdf12_reifies_closure` is kept, because rdfs3
as `RDFS.Closure` implements it reads the object as a subject-capable term.

The axiom seeding was measured against the suites the shared
`RDFS.Closure` reaches: OWL 2 RL is unchanged at 30 pass 0 fail positive
entailment, 6 pass 0 fail negative entailment, 76 pass 0 fail consistency,
14 pass 0 fail inconsistency; RDF 1.1 unchanged at 1030 pass, 0 fail, 1
unsupported (out of 1031).

### D-inconsistency

`rdf_inconsistent : list triple -> bool` is true when any literal in the
graph, including inside a triple term, is ill-formed for its datatype
(via the existing `literal_ill_formed`). Consumed only by the harness's
`mf:result false` arm.

## 4. Harness changes

`bin/w3c-runner/w3c_runner.ml` — a consumer tool, not the verified library;
no semantics were added to it.

1. `test_case` gains `result_false : bool`, set when `mf:result` is the
   literal `false`. It was previously indistinguishable from an absent
   `mf:result`, which is why both inconsistency tests were skipped.
2. The `Positive/NegativeEntailmentTest` arm branches on it and calls the
   extracted `RDF_Entailment_Regime.rdf_inconsistent`.
3. `RDF12_TESTS_BASE` environment override for the RDF 1.2 corpus root, so
   the local tight-case suite runs through the same code path as the
   vendored one.

## 5. Additional open-source 1.2 test suites

Surveyed 2026-09-07 by web inspection of repository trees; nothing cloned or
vendored yet. Recorded here so the Lean tree and the F\* tree vendor the
same things once, in one place.

**Worth vendoring:**

1. `apache/jena`, `jena-arq/testing/RIOT/rrx12/` (and `rrx11-2/`) — about 76
   files, 35 KB, Apache-2.0, W3C `mf:` manifests already using the rdf-tests
   IRI base. RDF 1.2 in RDF/XML: triple terms, reifiers, annotations,
   `rdf:version`, base direction. Its README states it supplements the
   rdf-tests CG suite. Best coverage per byte of anything found, and RDF/XML
   1.2 is where our own corpus is thinnest (30 eval tests).
2. `w3c-cg/rdf-star`, `tests/` — 222 tests, 490 KB, same licence as
   rdf-tests. Archived 2026-05-11. Take it for the 27 semantics tests and
   the 15 SPARQL-star `.ru` update files, which have no RDF 1.2 successor
   (`sparql/sparql12/` has no update directory). It uses the old CG quoted
   triple `<< s p o >>` and CG opacity semantics, so it is a translation
   job, not a drop-in: vendor it as a clearly-labelled legacy suite with its
   own expectation file, and never add its score to the rdf-tests score.

**Only if LATERAL comes into scope** (it is not in the SPARQL 1.2 rdf-tests
set): `apache/jena` `ARQ/Lateral` + `ARQ/Syntax-Lateral` (31 files,
Apache-2.0), `oxigraph/oxigraph` `testsuite/oxigraph-tests/sparql/lateral`
(16 files, MIT or Apache-2.0), `eclipse-rdf4j/rdf4j`
`testcases-sparql-1.2/lateral` (12 files, BSD-3-Clause). Three independent
implementations of one feature is a useful differential check.

**Copies of `w3c/rdf-tests` — do not vendor:** `apache/jena`
`jena-arq/testing/rdf-tests-cg/`; `eclipse-rdf4j/rdf4j`
`testsuites/rio/.../rdf12/` and `testcases-sparql-1.2-w3c/`;
`oxigraph/oxigraph` `testsuite/rdf-tests` and its sibling submodules;
`RDFLib/rdflib` `test/data/suites/w3c/`.

**Nothing to take:** RDFLib (no RDF 1.2 material of its own), N3.js (JS unit
tests with inline strings, not a data-driven corpus), `w3c/rdf-canon`
(RDFC-1.0 over RDF 1.1 N-Quads only — no triple-term dataset
canonicalization corpus exists in any repository found), `w3c/rdf-star-wg`
(documents only), `w3c/sparql-dev` `tests/` (11 files, SEP-0004 only, the
SEP is unsettled).

## 6. Status and open items

### Scores after this landing

Same binary path, `bin/darwin-arm64/w3c_runner`, rebuilt from the changed
`RDF.Entailment.Regime.fst`.

| Suite | Before | After |
|---|---|---|
| `--rdf12entail` rdf-semantics | 41 pass, 3 fail, 3 skip (out of 47) | **44 pass, 2 fail, 1 skip (out of 47)** |
| tight cases (`rdf12-semantics-tight`) | did not exist | **9 pass, 0 fail (out of 9)** |
| `--rdf12` | 242 pass, 0 fail (out of 242) | 242 pass, 0 fail (out of 242) |
| `--rdf12c14n` | 82 pass, 0 fail (out of 82) | 82 pass, 0 fail (out of 82) |
| `--sparql12` | 254 pass, 0 fail (out of 254) | 254 pass, 0 fail (out of 254) |
| `--rdf` (RDF 1.1) | 1030 pass, 0 fail, 1 unsupported (out of 1031) | 1030 pass, 0 fail, 1 unsupported (out of 1031) |
| SPARQL 1.1 (default flag set) | 631 pass, 0 fail (out of 631) | 631 pass, 0 fail (out of 631) |
| `tests/unit/run-all.sh` | 50 files pass, 0 fail (out of 50) | 50 files pass, 0 fail (out of 50) |

The three recovered `rdf-semantics` tests are `triple-terms-propositions`
(was a fail), `malformed-literal` and `malformed-literal-control` (were
skips). The two remaining fails and the one remaining skip are the upstream
fixture defects of TC-1 and TC-2; nothing in the engine is known to be
missing for them.

Every SPARQL 1.2 built-in the specification adds is present in the F\* tree
and exercised by the suites above: `TRIPLE`, `SUBJECT`, `PREDICATE`,
`OBJECT`, `isTRIPLE`, `LANGDIR`, `STRLANGDIR`, `hasLANG`, `hasLANGDIR`
(`SPARQL11.Algebra.fst` constructors `E_IsTriple`, `E_HasLang`,
`E_HasLangDir`, `E_LangDir`; `SPARQL11.Parser.fst` tokens gated on the
`sparql12` flag).

### TC-4 and TC-5 — the two residuals, found by writing the test first

Neither shape appears in any vendored fixture, so neither could have been
found by running the suite. Both are licensed by RDF 1.2 Semantics together
with RDFS, both failed when first written, and both pass now.

- **TC-4 `reifies-subproperty-range`.** `:p rdfs:subPropertyOf rdf:reifies`
  and `:x :p :y` entail `:y rdf:type rdfs:Proposition`. rdfs7 derives
  `:x rdf:reifies :y` inside the fixed point; the range condition has to
  apply to that derived triple.
- **TC-5 `proposition-subclass`.** `rdfs:Proposition rdfs:subClassOf :C`
  and `:a1 :p1 <<( :a :b :c )>>` entail `:a1 :p1 _:t . _:t rdf:type :C`.
  The consequent reaches the triple term through a blank node, which is the
  only way a concrete syntax can name it.

### Open



- **The rebuilt `bin/darwin-arm64/*` binaries and
  `ocaml-output/RDF_Entailment_Regime.ml` are NOT committed by this
  landing.** A complete `build-ocaml.sh extract` could not run (see the
  next item), and anti-pattern #33 forbids committing an `.ml` captured
  from a partial extraction. The scores above come from a targeted
  extraction of the one changed module (`fstar.exe --codegen OCaml
  --cache_checked_modules RDF.Entailment.Regime.fst`, which no patch in
  `experimental_ocaml_glue/` or `ocaml-patches.sh` touches) followed by a
  full `build-ocaml.sh compile`. CI on linux-x86_64 runs the whole
  extraction and produces the shipping binaries.
- **`git checkout -- formal/fstar/ocaml-output/` on darwin restores
  x86-64 ELF objects into `ocaml-output/hacl-obj/`,** which are committed
  for linux and make every native link fail with "unknown file type".
  `rm -f ocaml-output/hacl-obj/*.o` before compiling; the build script
  rebuilds them. Cost here: one failed compile round.
- **`RDF.Store.Columnar.DeltaLog.fst` does not verify on darwin-arm64.**
  Pre-existing, unrelated to this work, and it blocks a full
  `build-ocaml.sh extract` at layer 2. `Error 19 ... Assertion failed` at
  `RDF.Store.Columnar.DeltaLog.fst(766,30-766,42)`, reproducible in 16
  seconds with `make verify-RDF.Store.Columnar.DeltaLog`. The module has no
  entry in the `checked-cache` branch tarball (122 modules), so CI verifies
  it from scratch too and is green — which points at a platform difference
  in z3's search rather than a proof that is simply absent. Needs its own
  issue.
- `literal-type` (TC-2): the D-entailment rule "a literal denotes an
  instance of its datatype" is expressible now but not implemented.
- Upstream reports to `w3c/rdf-tests` for TC-1 and TC-2 are not filed.
- The two suites in section 5 are not vendored.
- Proposition assertions do not re-enter the RDFS fixed point (section 3).

## 7. Per-test outcomes, for the Lean/F\* diff

The list the coordinator needs to find where the two trees disagree. F\*
tree, `bin/darwin-arm64/w3c_runner --rdf12entail`, after this landing. The
47th test, `literal-type`, is not listed because the runner never sees it:
its vendored manifest block is unreadable (TC-2), so it has no name to
report and counts as the one skip.

| Test | F\* |
|---|---|
| `all-identical-triple-terms-are-the-same` | PASS |
| `annotated-asserted` | PASS |
| `annotation` | FAIL |
| `annotation-unfolded` | FAIL |
| `bnodes-in-triple-term-object` | PASS |
| `bnodes-in-triple-term-subject` | PASS |
| `bnodes-in-triple-term-subject-and-object` | PASS |
| `bnodes-in-triple-term-subject-and-object-fail` | PASS |
| `constrained-bnodes-in-triple-term-fail` | PASS |
| `constrained-bnodes-in-triple-term-object` | PASS |
| `constrained-bnodes-in-triple-term-subject` | PASS |
| `constrained-bnodes-on-literal` | PASS |
| `different-bnodes-same-triple-term` | PASS |
| `double-infinity` | PASS |
| `double-round-different` | PASS |
| `double-round-same` | PASS |
| `double-zero` | PASS |
| `float-infinity` | PASS |
| `float-round-different` | PASS |
| `float-round-same` | PASS |
| `float-zero` | PASS |
| `json-array-unordered` | PASS |
| `json-infinity` | PASS |
| `json-object-unordered` | PASS |
| `json-round-different` | PASS |
| `json-round-same` | PASS |
| `json-zero` | PASS |
| `json-zero-array` | PASS |
| `malformed-literal` | PASS |
| `malformed-literal-accepted` | PASS |
| `malformed-literal-bnode-neg` | PASS |
| `malformed-literal-control` | PASS |
| `malformed-literal-no-spurious` | PASS |
| `opaque-dir-language-string` | PASS |
| `opaque-dir-language-string-control` | PASS |
| `opaque-iri` | PASS |
| `opaque-iri-control` | PASS |
| `opaque-language-string` | PASS |
| `opaque-language-string-control` | PASS |
| `opaque-literal` | PASS |
| `opaque-literal-control` | PASS |
| `reifies-range` | PASS |
| `same-bnode-same-quoted-term` | PASS |
| `triple-term-not-asserted` | PASS |
| `triple-terms-no-spurious` | PASS |
| `triple-terms-propositions` | PASS |

Both fails are TC-1, the upstream annotation-expansion defect. Every other
vendored test passes.

The tight-case suite is 9 pass, 0 fail (out of 9); its entries are named in
`.github/test-suites/local-rdf12-semantics-tight.yaml`. Running the same
nine against the Lean tree is the sharper comparison, because five of them
state a decision rather than reproduce a fixture.
