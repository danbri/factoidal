# Lean 4 against F\*: the conformance parity table, measured 2026-09-03

This note extends
[the specification coverage ledger](designissues/2026-08-23-spec-coverage-ledger.md)
into a per-suite parity table. That ledger answers "does an upstream
suite exist, is it vendored, is it wired". This one answers a
different question: **for a suite both engines can run, what does each
score, and what is the difference?**

## Provenance of every number

- **F\* column.** Quoted from `docs/test-results/latest.json`,
  timestamp `2026-09-03 11:26 UTC`, commit `7e1fa377b`. The F\* engine
  was NOT re-run in this session. Where a suite has no row in that
  file, the cell says so and names the other source.
- **Lean column.** Measured in this session by running each runner
  from a worktree of commit `4be43aed7` after
  `tools/ensure-test-env.sh` reported all 18 suite fixtures present.
  Every command is in § "Commands" below.
- **Working directory matters.** `l4w3c`, `l4shacl`, `l4owl-probe` and
  most conformance runners resolve manifest paths relative to the
  REPOSITORY ROOT. `l4rdfc-probe`, `l4turtle-probe` and
  `l4rdfxml-probe` resolve relative to `formal/lean4/`. A runner in
  the wrong directory prints "not found" and still exits 0, so it
  reports no score rather than a wrong one. The commands below state
  the directory for each.
- Every score is written "N pass, M fail (out of T)". A suite not run
  says "not run" with the reason and carries no assumed number.

## 1. Suites both engines run

| Suite | F\* | Lean 4 | Delta | Cause |
|---|---|---|---|---|
| SPARQL 1.1, whole manifest | 631 pass, 0 fail (out of 631) | 631 pass, 0 fail (out of 631) | 0 | — |
| SPARQL 1.2 | 254 pass, 0 fail (out of 254) | 254 pass, 0 fail (out of 254) | 0 | — |
| RDF 1.1, whole manifest | 1,030 pass, 0 fail, 1 unsupported (out of 1,031) | 1,031 pass, 0 fail (out of 1,031) | Lean +1 pass | One `rdf-mt` entailment entry that the F\* runner declares unsupported, the Lean runner answers. Which verdict is right is unresolved — see § "Findings" |
| rdf-turtle (RDF 1.1) | 313 pass, 0 fail (out of 313) | 313 pass, 0 fail (out of 313) | 0 | — |
| rdf-trig (RDF 1.1) | 356 pass, 0 fail (out of 356) | 356 pass, 0 fail (out of 356) | 0 | — |
| rdf-n-triples (RDF 1.1) | 70 pass, 0 fail (out of 70) | 70 pass, 0 fail (out of 70) | 0 | — |
| rdf-n-quads (RDF 1.1) | 87 pass, 0 fail (out of 87) | 87 pass, 0 fail (out of 87) | 0 | — |
| rdf-xml (RDF 1.1) | 166 pass, 0 fail (out of 166) | 166 pass, 0 fail (out of 166) | 0 | `l4rdfxml-probe` separately reports 130 pass, 2 fail (out of 132) on its `eval-isomorphic` group, but those two entries are commented out in the upstream manifest — see § "Findings" |
| rdf-mt (RDF 1.1 semantics) | 38 pass, 0 fail, 1 unsupported (out of 39) | 39 pass, 0 fail (out of 39) | Lean +1 pass | Same entry as the RDF 1.1 row |
| RDF 1.2 syntaxes | 242 pass, 0 fail (out of 242) | 242 pass, 0 fail (out of 242) | 0 | The RDF 1.2 manifests `mf:include` the RDF 1.1 ones, so the RDF 1.2 figure is the sum of the `eval` and `syntax` groups only. See § "What was compared" |
| RDF 1.2 canonical N-Triples/N-Quads | 82 pass, 0 fail (out of 82) | 82 pass, 0 fail (out of 82) | 0 | Sum of the two `c14n` groups |
| **RDF 1.2 Semantics** | 41 pass, 3 fail, 3 skip (out of 47) | **19 pass, 11 fail, 0 skip, 17 unsupported (out of 47)** | **22 passes** | The Lean entailment engine does not answer the RDF 1.2 triple-term and reification entailments. Named failures include `annotation-unfolded` (simple entailment), `triple-terms-propositions` and `reifies-range` (RDFS entailment). The second-largest delta in the tree |
| RDF Dataset Canonicalization (RDFC-1.0) | 86 pass, 0 fail (out of 86) | 86 pass, 0 fail (out of 86): rdfc10 eval 63 of 63, sha384 eval 1 of 1, map eval 21 of 21, negative eval 1 of 1 | 0 | — |
| SHACL 1.0 Core | 98 pass, 0 fail (out of 98) | 98 pass, 0 fail (out of 98) | 0 | — |
| SHACL 1.0 SPARQL constraints | 22 pass, 0 fail (out of 22) | 22 pass, 0 fail (out of 22) | 0 | — |
| **SHACL 1.2 Core** | 138 pass, 0 fail (out of 138) | **103 pass, 30 fail (out of 133)** | **35 passes; the denominators also differ, 133 against 138** | Under investigation by a worker agent this session. The denominator difference means the Lean runner does not see five entries the F\* runner sees |
| SHACL 1.2 SPARQL | 25 pass, 0 fail (out of 25) | 22 pass, 3 fail (out of 25) | 3 | Not yet classified |
| SHACL 1.2 node expressions | 142 pass, 0 fail (out of 142) | 140 pass, 0 fail, 2 unsupported (out of 142) | 2 | Two node-expression forms the Lean evaluator declines |
| SHACL 1.2 rules (eval, syntax, wellformed, stratification) | 88 pass, 0 fail (out of 88) | 88 pass, 0 fail (out of 88) | 0 | F\* reports the four groups separately: 11 + 62 + 7 + 8 |
| ShEx validation | 1,182 pass, 0 fail (out of 1,182) | 1,182 pass, 0 fail (out of 1,182 decided), 0 not read | 0 | — |
| JSON-LD toRdf | 467 pass, 0 fail (out of 467) | 467 pass, 0 fail (out of 467) | 0 | — |
| JSON-LD expand | 385 pass, 0 fail (out of 385) | 385 pass, 0 fail (out of 385) | 0 | — |
| JSON-LD compact | 245 pass, 0 fail, 1 skip (out of 246) | 245 pass, 0 fail, 1 local-override (out of 246) | 0 | — |
| JSON-LD flatten | 58 pass, 0 fail (out of 58) | 58 pass, 0 fail (out of 58) | 0 | — |
| JSON-LD fromRdf | 53 pass, 0 fail, 1 skip (out of 54) | 53 pass, 0 fail, 1 local-override (out of 54) | 0 | — |
| JSON-LD in HTML | no row in `latest.json` | 50 pass, 0 fail (out of 50) | not comparable | Wired on the F\* side (`jsonld-html.yaml`) but never scored; kind (c) in the coverage ledger |
| JSON-LD Framing | 28 pass, 64 fail (out of 92), from `docs/test-results/assurance-inventory.json`, not `latest.json` | 29 pass, 63 fail, 0 unsupported (out of 92) | Lean +1 pass | Both engines are red on the same suite. The framing algorithm is incomplete in both trees |
| CSVW csv2rdf | 270 pass, 0 fail (out of 270) | 270 pass, 0 fail (out of 270): positive 212, negative 58 | 0 | — |
| CSVW csv2json | 270 pass, 0 fail (out of 270) | 270 pass, 0 fail (out of 270) | 0 | — |
| JSON Schema draft-07 | 770 pass, 0 fail (out of 770) | 770 pass, 0 fail (out of 770 decided) | 0 | — |
| RML Core | 76 pass, 0 fail (out of 76) | 60 pass, 0 fail (out of 60 compared); 15 negative cases not attempted, 1 not read (out of 76) | 16 not attempted | The Lean slice has no mapping validator, so it makes no claim about the 15 negative cases. The 1 not-read case is fixture `RMLTC0027b-JSON`, whose expected N-Quads contain an IRIREF with a space |
| **RIF Core** | 46 pass, 0 fail, 4 skip (out of 50) | **24 pass, 2 fail (out of 26 decided)**; 13 undecided, 1 not read, 6 import rejection (out of 46 read) | **22 passes**, and the denominators differ, 46 against 50 | The Lean RIF built-in library is a named subset of RIF-DTB's 197 built-ins; 13 cases stop on a missing built-in or on the chain round bound, and the port has no import profile checker |
| ISO Schematron | 8 pass, 0 fail (out of 8) | 8 pass, 0 fail (out of 8 decided) | 0 | Both run the same 8 self-authored cases; not a conformance claim on either side |
| XSLT 1.0 | 87 pass, 0 fail, 1 skip (out of 88) | 84 pass, 3 fail (out of 87 decided), 1 refused (out of 88) | 3 | Namespace declaration order on one case, the implementation-defined `namespace::` axis order on one, `xsl:copy` of a node from a second document on one. The refusal is `select-59.xml`, a document the vendoring did not capture |
| GRDDL | 18 pass, 50 fail (out of 68) | 19 pass, 22 fail (out of 41 decided); 27 not decided (out of 68) | Lean +1 pass; the fail columns are not comparable | The Lean runner counts a case whose documents the vendored docroot does not mirror as not decided, not as a failure. The F\* runner folds them into `fail`. Both engines are red on this suite |
| XML 1.0 conformance | 1,447 pass, 0 fail, 1,138 skip (out of 2,585) | 1,840 pass, 22 fail (out of 1,862 in profile, out of 2,585) | not comparable | Different profiles: the Lean parser declares XML 1.0 non-validating, non-namespace, UTF-8 and scores 1,862 of the 2,585 cases; the F\* runner scores 1,447 and skips 1,138. The two skip sets were not compared |
| MathML | 81 pass, 0 fail (out of 81) | 56 pass, 0 fail (out of 56) | not comparable | Different test sets. The F\* 81 are a self-authored manifest; the Lean 56 are content-MathML evaluation only |
| HDT container | 6 pass, 0 fail (out of 6) — a backend parity check, not the fixtures | 2 pass, 0 fail (out of 2 vendored `.hdt` containers) | not comparable | The two runners measure different things: F\* compares an HDT-backed store against the in-memory one; Lean reads the two vendored containers and checks their dictionary and triple sections |
| did:key vectors | 8 pass, 0 fail (out of 8) | 8 pass, 0 fail (out of 8) | 0 | The same 8 internal vectors on both sides |
| VC Data Integrity eddsa-rdfc-2022 | 31 pass, 0 fail (out of 31) | 28 pass, 0 fail (out of 28): 8 test-suite cases plus 20 specification vectors | not comparable | Different partitions of the same corpus; the Lean probe also runs 22 ed25519 RFC 8032 vectors and a 13-case sha256 differential, total 71 pass, 0 fail (out of 71) |
| **OWL 2, all catalogs** | see § 2 — five catalogs scored, 681 pass, 4 fail, 2 skip (out of 687) | **1,131 pass, 316 fail, 2 skip, 8 unsupported (out of 1,457)** | **not directly comparable; the largest delta in the tree** | The Lean probe runs every catalog in `third_party/testing/owl/`, including `semantics-direct.rdf` and three `type-*` catalogs that have no row in `latest.json`. Classification in progress — see § 2 |

## 2. OWL: why the totals cannot be subtracted

The Lean `l4owl-probe` walks all ten catalogs under
`third_party/testing/owl/` and scores 1,457 entries. `latest.json`
carries five OWL rows and 687 entries. `semantics-direct.rdf` (1,127
tests) and three of the four `type-*` catalogs are run by
`generate-report.sh` off the dashboard hot path and have no recorded
F\* score — that is item c11 in the coverage ledger, and it is why a
single delta figure cannot be written here.

The five catalogs both engines score:

| Catalog | F\* | Lean 4 |
|---|---|---|
| `profile-RL.rdf` | 30 pass, 0 fail (out of 30) | per-catalog figures pending, see below |
| `profile-QL.rdf` | 87 pass, 0 fail (out of 87) | pending |
| `profile-EL.rdf` | 119 pass, 1 fail (out of 120) | pending |
| `syntax-dl.rdf` | 319 pass, 2 fail, 2 skip (out of 323) | pending |
| `type-inconsistency.rdf` | 126 pass, 1 fail (out of 127) | pending |

A per-catalog classification of the 316 Lean failures is under way in
this session; when it lands, this section is replaced by its table.
The prior measurement (2026-08-23) of `type-inconsistency.rdf` on the
Lean side was 30 pass, 97 fail under RL closure and 67 pass, 60 fail
(out of 127) with `--dl`, against the F\* 126 pass, 1 fail (out of
127).

Running `l4owl-probe --dl` adds the materialisation pass and the
refuter: 1,177 pass, 270 fail, 2 skip, 8 unsupported (out of 1,457),
measured 2026-08-23.

## 3. Suites the F\* engine runs and Lean has no runner for

Each row is "no Lean runner". None of these has a Lean conformance
harness; several have Lean library modules with no runner over them.

| Suite | F\* score | Lean module present? |
|---|---|---|
| SPARQL Protocol, Graph Store, Service Description, Federated Query | folded into the 631 | yes, and folded into the Lean 631 |
| RML I/O | 17 pass, 1 fail, 55 skip (out of 73) | no runner |
| RML containers, functions, RML-star | never run on either side | no |
| CSVW validation (tabular data model) | 281 pass, 1 fail (out of 282) | no standalone runner; `l4csvw-rdf` cross-checks the validator against every positive test and reports 0 wrongly rejected |
| ShEx negative syntax | `present: false`, 0 pass, 0 fail (out of 0) | `l4shexc` runs a different test set: 442 match, 0 mismatch (out of 442) on the ShExC/ShExJ differential |
| GeoSPARQL | 37 pass, 0 fail (out of 37) | `Geo/Wkt` module, no runner |
| XPath 1.0 unit cases | 100 pass, 0 fail (out of 100) | `XPath/Full` and `XPath/Mini`, no runner over the F\* case set |
| XForms 1.1 | 2 pass, 0 fail (out of 2) | `XForms/Bind`, no runner |
| QUDT integrity | 0 pass, 0 fail, 29 skip (out of 29) | no |
| QUDT user shapes | 9 pass, 0 fail (out of 9) | no |
| VC Data Model 2.0 structural | 117 pass, 0 fail (out of 117) | `VC/` modules, no runner over this manifest |
| VC Data Model 2.0 issuer/verifier HTTP | 59 pass, 0 fail (out of 59) | no |
| EECC VC/DID interop fixtures | 4 pass, 0 fail, 51 skip (out of 55) | no |
| TOAN matrix | 11 pass, 0 fail (out of 11) | `Math/Matrix`, no runner |
| F\* native unit regressions | 19 pass, 28 fail (out of 47) | not applicable, F\*-side only |
| npm package tests | 252 pass, 0 fail, 2 skip (out of 254) | not applicable |
| hub browser bundle | 410 pass, 0 fail (out of 410) | not applicable |

## 4. What was compared, where the suite names differ

- **"RDF 1.2 syntaxes"**: the RDF 1.2 manifests carry
  `mf:include (<eval/manifest.ttl> <syntax/manifest.ttl>
  <../../rdf11/rdf-turtle/manifest.ttl>)`, so a run of
  `rdf/rdf12/manifest.ttl` re-runs the whole RDF 1.1 suite. The
  Lean total for that manifest is 1,335 pass, 11 fail, 17 unsupported
  (out of 1,363). The RDF 1.2 figure quoted in the table is the sum of
  the `eval` and `syntax` groups only — 29 + 27 + 29 + 67 + 25 + 35 +
  30 = 242 — which is exactly the F\* `rdf12` denominator, and the
  `c14n` groups are 41 + 41 = 82, exactly the F\* `rdf12c14n`
  denominator. That agreement is the evidence that the two engines
  score the same test set.
- **"SHACL 1.2 rules"**: F\* reports four rows
  (`shacl12_rules` 11, `shacl12_rules_syntax` 62,
  `shacl12_rules_wellformed` 7, `shacl12_rules_stratification` 8);
  `l4shacl-rules` reports the same four groups and a total of 88.
- **"VC Data Integrity"**: the F\* row is the vendored
  `vc-di-eddsa` suite, 31 entries. The Lean probe splits the same
  corpus into 8 test-suite cases and 20 specification vectors and adds
  a 13-case sha256 differential. The partitions were not reconciled
  case by case.
- **"OWL 2"**: see § 2. The denominators are 687 against 1,457.

## 5. Findings worth a GitHub issue

1. **One `rdf-mt` entry: F\* says unsupported, Lean answers it.** The
   F\* engine scores rdf-mt 38 pass, 0 fail, 1 unsupported (out of
   39); the Lean engine scores 39 pass, 0 fail (out of 39). Two
   engines give different verdicts about whether a W3C entailment test
   is answerable. One of them is wrong and neither is failing, so no
   suite is red and nothing would catch it.
2. **`l4rdfxml-probe` scores two tests the upstream manifest has
   withdrawn.** `l4w3c` on `rdf/rdf11/rdf-xml/manifest.ttl` reports
   166 pass, 0 fail (out of 166); `l4rdfxml-probe` reports its
   `eval-isomorphic` group as 130 pass, 2 fail (out of 132). The two
   are `rdfms-xml-literal-namespaces/test001.rdf` and `test002.rdf`.
   They are NOT a runner disagreement: both entries are commented out
   in `manifest.ttl` (lines 1574-1596, every line prefixed `#`), so
   `l4w3c` correctly does not run them and the probe, which walks the
   DIRECTORY rather than the manifest, runs them anyway. This
   corrects the 2026-08-22 parity ledger, which recorded "RDF/XML 130
   pass, 2 fail (of 132)" as a Lean gap against F\*. There is no such
   gap. The probe should either read the manifest or label a
   directory-walked entry as unscored, the way `l4turtle-probe`
   already does with its "walked but not listed" count.
3. **The Lean SHACL 1.2 core runner sees 133 entries where the F\*
   runner sees 138.** A denominator gap is a coverage gap, not a
   scoring gap, and it is invisible in a pass percentage.
4. **`turtle-tests/test-38.ttl` is on disk and in no manifest.**
   `l4turtle-probe` reports 4 files walked but not listed in
   `rdf-turtle/manifest.ttl`, one of which it fails to parse
   (`surrogate or out-of-range codepoint U+d801 in escape`). It is not
   scored by either engine. Worth an upstream question to
   w3c/rdf-tests.
5. **`RMLTC0027b-JSON`'s expected output is not valid N-Quads.** Its
   `output.nq` writes `<http://example.com/Person/Emily Smith>`, and
   an IRIREF may not contain a space (RDF 1.1 N-Quads, §2.3). The
   Lean runner reports it as not read. The F\* runner scores the RML
   Core suite 76 pass, 0 fail (out of 76), so it either parses that
   file or reaches the same triples another way — the two behaviours
   were not reconciled. Worth an upstream issue to kg-construct.
6. **The RDF 1.2 rdf-semantics manifest still carries the undeclared
   `test:` prefix** recorded in the coverage ledger § 4. The F\*
   runner degrades to the well-formed subset; the Lean runner now
   reads 47 entries, so the two harnesses no longer disagree about
   loading it, but they disagree about 22 verdicts.
7. **Four F\*-scored suites are red on the F\* side and have no Lean
   counterpart to compare**: `tests_unit` 19 pass, 28 fail (out of
   47); `grddl_stage1` 18 pass, 50 fail (out of 68); `qudt_integrity`
   0 pass, 0 fail, 29 skip (out of 29); `rml_io` 17 pass, 1 fail, 55
   skip (out of 73).

## 6. Commands

Run every command in this section from the REPOSITORY ROOT unless the
row says `formal/lean4`. `bash tools/ensure-test-env.sh` must exit 0
first; a worktree without test submodules reports 0/0.

### F\* engine

The whole battery, which writes `docs/test-results/latest.json`:

```
eval $(opam env --switch=fstar)
./w3c-tests.sh
```

Per-area flags of `formal/fstar/generate-report.sh`: `--rdf`,
`--rdf12`, `--rdf12c14n`, `--rdf12entail`, `--sparql12`, `--species`,
`--regime`, `--integrity`, `--negative-syntax`. The numbers in this
note were read from `latest.json`, not produced by re-running these.

### Lean 4 engine

```
cd formal/lean4 && lake build          # then run from the repository root
```

| Suite | Command |
|---|---|
| SPARQL 1.1 | `./formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/sparql/sparql11/manifest-all.ttl` |
| SPARQL 1.2 | `./formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/sparql/sparql12/manifest.ttl` |
| RDF 1.1 (all) | `./formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/manifest.ttl` |
| rdf-mt | `./formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/rdf-mt/manifest.ttl` |
| RDF 1.2 (all, includes RDF 1.1) | `./formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl` |
| RDF 1.2 Semantics | `./formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl` |
| RDFC-1.0 | from `formal/lean4`: `.lake/build/bin/l4rdfc-probe` |
| SHACL 1.0 core | `./formal/lean4/.lake/build/bin/l4shacl` (default manifest) |
| SHACL 1.0 SPARQL | `./formal/lean4/.lake/build/bin/l4shacl third_party/testing/shacl/data-shapes-test-suite/tests/sparql/manifest.ttl` |
| SHACL 1.2 core | `./formal/lean4/.lake/build/bin/l4shacl third_party/testing/shacl/shacl12-test-suite/tests/core/manifest.ttl` |
| SHACL 1.2 SPARQL | `./formal/lean4/.lake/build/bin/l4shacl third_party/testing/shacl/shacl12-test-suite/tests/sparql/manifest.ttl` |
| SHACL 1.2 node expressions | `./formal/lean4/.lake/build/bin/l4shacl-nodeexpr` |
| SHACL 1.2 rules | `./formal/lean4/.lake/build/bin/l4shacl-rules` |
| ShEx validation | `./formal/lean4/.lake/build/bin/l4shex` |
| ShExC differential | `./formal/lean4/.lake/build/bin/l4shexc` |
| JSON-LD toRdf | `./formal/lean4/.lake/build/bin/l4jsonld-probe` |
| JSON-LD expand/compact/flatten/fromRdf/html | `./formal/lean4/.lake/build/bin/l4jsonld-api` |
| JSON-LD framing | `./formal/lean4/.lake/build/bin/l4jsonld-frame` |
| CSVW csv2rdf | `./formal/lean4/.lake/build/bin/l4csvw-rdf` |
| CSVW csv2json | `./formal/lean4/.lake/build/bin/l4csvw-json` |
| JSON Schema | `./formal/lean4/.lake/build/bin/l4jsonschema` |
| RML Core | `./formal/lean4/.lake/build/bin/l4rml` |
| RIF Core | `./formal/lean4/.lake/build/bin/l4rif` |
| Schematron | `./formal/lean4/.lake/build/bin/l4schematron` |
| XSLT 1.0 | `./formal/lean4/.lake/build/bin/l4xslt` |
| GRDDL | `./formal/lean4/.lake/build/bin/l4grddl` |
| XML 1.0 conformance | `./formal/lean4/.lake/build/bin/l4xmlconf` |
| MathML content | `./formal/lean4/.lake/build/bin/l4mathml` |
| HDT containers | `./formal/lean4/.lake/build/bin/l4hdt` |
| VC and did:key | `./formal/lean4/.lake/build/bin/l4vc-probe` |
| OWL 2 | `./formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl` (add `--dl` for the refuter) |
| RDF/XML probe | from `formal/lean4`: `.lake/build/bin/l4rdfxml-probe` |
| Turtle and TriG probe | from `formal/lean4`: `.lake/build/bin/l4turtle-probe` |
| SPARQL query-syntax probe | `./formal/lean4/.lake/build/bin/l4sparql-probe` |

`tools/affected-tests.sh` cannot select any of these: it maps F\* yaml
suites only, and no yaml describes the Lean harness
(https://github.com/danbri/factoidal/issues/642, and item c12 in the
coverage ledger). A Lean-only diff must name its runners by hand.

## 7. Reading of the table

- On RDF 1.1, RDF 1.2 syntax and canonicalization, SPARQL 1.1, SPARQL
  1.2, RDFC-1.0, SHACL 1.0, ShEx, JSON-LD, CSVW, JSON Schema and
  Schematron the two engines are level, on the same manifest files,
  with zero failures each.
- Four deltas are large enough to work on, in order: **OWL 2** (316
  Lean failures across 1,457 entries), **RDF 1.2 Semantics** (22
  passes), **RIF Core** (22 passes, mostly built-ins), **SHACL 1.2
  Core** (35 passes and a 5-entry denominator gap).
- Three deltas are small: XSLT (3), SHACL 1.2 SPARQL (3), SHACL 1.2
  node expressions (2).
- Two suites are red on both engines and are a shared gap, not a
  parity gap: JSON-LD Framing and GRDDL.
- Seventeen F\*-scored suites have no Lean runner. Most are periphery;
  the two that carry real conformance weight are VC Data Model 2.0
  (117 + 59 entries) and CSVW validation (282 entries).
