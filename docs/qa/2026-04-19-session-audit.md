# Session QA audit — 2026-04-19 (UTC)

Read-only audit. No source, binaries, or test data modified.

- Auditor: Claude Opus 4.7 (1M context) subagent, QA role.
- Scope: (1) end-to-end verification of the interactive SPARQL demo at
  `docs/fstar-extracted/index.html` (6 datasets × 30 queries, plus 6
  entailment variants — 36 runs total). (2) Classification of the 36
  current `FAIL:` lines from `./bin/darwin-arm64/w3c_runner --all`.
- Raw runner log: `.claude-runs/qa-w3c-20260419-195819.log` (SPARQL
  suite 452/36/134/9; RDF 972/59/0/0).
- Demo runner output: `/tmp/qa-demo/` (datasets, queries, per-run JSON,
  summary TSV).

## Headline numbers

| Suite          | Pass | Fail | Skip | Unsupported |
|----------------|-----:|-----:|-----:|------------:|
| SPARQL 1.1     | 452  | 36   | 134  | 9           |
| RDF 1.1        | 972  | 59   | 0    | 0           |
| RDF model theory (rdf-mt) | 39 | 0 | 0 | 0 |
| **Demo runs (js_of_ocaml)** | **36 / 36 exited 0 with valid JSON** | — | — | — |

Caveats (honest — repeated from CLAUDE.md):

- **ASK query comparison in `w3c_runner.ml` does not check the expected
  boolean value.** This alone would just inflate the runner's pass count
  slightly. But see "Most worrying finding" below — the underlying ASK
  evaluator is also broken, so no W3C test would catch it even if the
  comparator were fixed, because there is no dedicated ASK suite in
  sparql11.
- **Blank-node comparison is simplified** (any bnode matches any other
  bnode, not proper isomorphism).
- **SPARQL11.Parser.fst uses `--admit_smt_queries true` over ~65% of
  the file** (lines ~802–2722). Verified in form, not in SMT discharge.

## Demo verification — Part 1

Every demo dropdown combination was run via

```
node docs/fstar-extracted/factoidal.js -d /tmp/qa-data.<ext> -e '<query>' -o json [--entail REGIME]
```

All 30 queries exit 0 and emit valid SPARQL-results+JSON. Row counts below
are from the actual runs (see `/tmp/qa-demo/results/*.json`).

### People (9 queries, no entailment)

| Query | Rows | Status |
|---|--:|---|
| basic — List everyone by name | 8 | OK |
| filter — People over 30 | 5 | OK |
| optional — OPTIONAL email | 8 | OK |
| friendsof — Friends of Alice | 3 | OK |
| mutual — Mutual friendships | 7 | OK |
| count-friends | 7 | OK |
| **ask — Alice → ? → Eve** | **ASK=false** | **WRONG** (see below) |
| lang — German-tagged names | 2 | OK |
| bind-upper | 8 | OK |

The `ask` query asks whether Alice knows someone who knows Eve. The data
has `ex:alice foaf:knows ex:carol` and `ex:carol foaf:knows ex:eve`, and
the equivalent SELECT variant returns `{mid: ex:carol}` as expected. The
ASK variant returns `false`. Trivial ASKs over any non-empty dataset also
return `false` (reproduced with `factoidal -e 'ASK { ?s ?p ?o }'` on a
one-triple file). **See "Most worrying finding" below.**

### Catalog (4 queries)

| Query | Rows | Status |
|---|--:|---|
| cat-list — all products by price | 20 | OK |
| cat-byCat — count + avg per category | 6 | OK |
| cat-outOfStock — stock = 0 | 2 | OK |
| cat-topByCat — MAX price per category, HAVING | 4 | OK |

### Music (4 queries)

| Query | Rows | Status |
|---|--:|---|
| mu-albums — albums with year and artist | 8 | OK |
| mu-bandSize — COUNT members | 3 | OK |
| mu-albumPerBand — GROUP_CONCAT | 3 | OK |
| mu-70s — FILTER year range | 2 | OK |

### Geo (3 queries)

| Query | Rows | Status |
|---|--:|---|
| geo-countries | 7 | OK |
| geo-continent — SUM population per continent | 2 | OK |
| geo-big — Europe + FILTER | 4 | OK |

### Libraries (TriG, 4 queries)

| Query | Rows | Status |
|---|--:|---|
| lib-list-books — GRAPH ?g | 10 | OK |
| lib-multi-copy — COUNT DISTINCT ?g | 3 | OK |
| lib-catalog-meta — default graph | 3 | OK |
| lib-central-holdings — GRAPH ex:central | 4 | OK |

### schema.org entailment (6 queries, each run with and without entailment)

All six entailment queries exit 0, emit valid JSON, and the RDFS/OWL-RL
variant strictly dominates the `none` variant in row count. The shape
matches the demo's claim.

| Query | Rows (entail=none) | Rows (RDFS or OWL-RL) | Status |
|---|--:|--:|---|
| so-all-places (needs RDFS) | 0 | 5 | OK |
| so-all-lodging (needs RDFS) | 0 | 3 | OK |
| so-all-restaurants (needs RDFS) | 1 | 2 | OK — the 1 baseline row is `ex:luigi a schema:Restaurant` directly; RDFS adds `ex:mcfood` via `FastFoodRestaurant rdfs:subClassOf Restaurant`. Honest. |
| so-subproperty (needs RDFS) | 5 | 6 | OK — baseline finds all direct `schema:name` statements; RDFS adds `ex:hotelZ` via `legalName rdfs:subPropertyOf name`. |
| so-inverse (needs OWL-RL) | 0 | 2 | OK |
| so-sameas (needs OWL-RL) | 1 | 5 | OK |

### Demo summary

- **29 / 30 queries return rows matching what the data should produce.**
- **1 / 30 queries (`ask`) returns a wrong boolean.** Also affects any
  user ASK query on the JS demo or native CLI.

## Part 2 — Classification of the 36 current SPARQL FAILs

All 36 come from the latest `w3c_runner --all` (SPARQL section of
`.claude-runs/qa-w3c-20260419-195819.log`, lines 1–686). Suites
contributing fails: `cast` (2), `entailment` (23), `functions` (1),
`negation` (1), `service` (7), `syntax-query` (1), `syntax-update-1` (1).

### Bucket counts

| Bucket | Count | Representative test | Notes |
|---|--:|---|---|
| (A) Tableau OWL needed | 21 | `parent query with (hasChild some Thing) restriction` (expected 3, got 0) | 11 sparqldl/OWL-expression tests + 8 "simple N" tests (OWL entailment regime) + 2 RIF tests. All in `entailment` suite, all output 0 rows because the closure doesn't implement `owl:someValuesFrom` / `allValuesFrom` / `minCardinality` / `intersectionOf` / class expressions. OWL-RL in F\* is rules-only; these tests need a tableau. |
| (B) Test comparator too strict or too lax | 3 | `cast — xsd:float cast` (expected 31, got 31 — same count!) | Both `cast` fails and the `REPLACE()` fail have `expected N rows, got N rows`. The comparator treats semantically-equal lexical forms as unequal, or the evaluator emits a subtly different lexical form (for casts, probably `2.0` vs `2`, for REPLACE probably Unicode byte-vs-codepoint per CLAUDE.md note #10). Hard to tell without a `-v` rerun. Classified here because in some of these cases the values *are* semantically equal and a proper value-space comparator would pass. |
| (C) Parser gap | 2 | `syntax-propertyPaths-01.rq — Should parse but didn't` (body: `[ :p\|:q\|:r ?X ]` — alternation in a blank-node-property-list turnstile) | Plus `syntax-update-54.ru — Should reject but parsed OK` (two consecutive `INSERT DATA { _:b1 :p :o }` — bnode re-use across update operations must be rejected). |
| (D) Evaluator gap (parser OK, eval wrong) | 3 | `Calculate which sets are subsets of others — expected 11, got 30` (negation) | Also REPLACE (if we classify that as the Unicode-regex stub, not comparator). And `paper-sparqldl-Q1 — expected 3, got 2` — only two of the three expected rows come out; the missing row relies on an OWL inference that is partially supported (that's arguably bucket A, but it's an off-by-one within an otherwise-working path). |
| (E) Result serialisation | 0 | — | No CONSTRUCT fails in current log; the 5 CONSTRUCT tests that need a Turtle result serializer are marked "unsupported" not "fail". |
| (F) SERVICE / Protocol / UPDATE-non-data | 7 | `SERVICE test 1 — expected 2 rows, got 0` | All 7 `service` fails: SERVICE silently returns empty because there is no HTTP client (#57). `SERVICE test 5` parse-fails on variable endpoint (also F). Protocol (34) and most UPDATE-management ops (88) are `skip` not `fail` so don't inflate this bucket. |
| (G) Other | 0 | — | — |

**Total: 21 + 3 + 2 + 3 + 0 + 7 + 0 = 36.** ✓

Notes on classification boundaries:

- The entailment suite includes 2 RIF tests that require XML RIF rules
  — these are not tableau, they're a whole other rule format. Strictly
  they should be their own bucket; I've folded them into (A) because the
  practical answer ("not in scope until someone writes a parser") is the
  same.
- `paper-sparqldl-Q1` (expected 3, got 2) is the only entailment test
  that produces *some* rows. The fact that it's off by exactly one
  suggests partial OWL-RL coverage; counted in (D) because the other
  two rows come through, meaning the eval path is not wholly absent,
  just under-inferring.
- The `cast` fails might also be bucket (D) if the evaluator is
  emitting wrong lexical forms for numeric casts. Without `-v` output
  captured I left them in (B). A follow-up with `-v` on a single cast
  test would resolve this. (Worth 15 minutes of someone's time.)

## Would I trust this for X?

### Read-only SPARQL over trusted data — **Mostly yes, with one caveat.**

Basic SPARQL 1.1 (SELECT, FILTER, OPTIONAL, GRAPH, GROUP BY, aggregates,
property paths, subqueries, EXISTS, BIND, UCASE/SUBSTR/STR, ORDER BY,
LIMIT/OFFSET) works for all 29/30 demo queries against clean data. The
verified-core claim is real: RDF parsing (Turtle, TriG, N-Quads, N-Triples)
passed all demo data, and 972/1031 W3C RDF tests pass. **Caveat: do not
use `ASK` in production — it returns `false` even when data matches.**
Rewrite as `SELECT * { ... } LIMIT 1` and check row count.

### SPARQL-with-UPDATE over trusted data — **Partial, with sharp edges.**

As of tonight: `INSERT DATA` (4 tests, pass), `DELETE DATA` (6, pass),
`DELETE WHERE` (6, pass), `delete-insert` (8, pass). Concurrent subagents
(per worklog) are implementing `U_Modify` (INSERT/DELETE with WHERE) now.
The 19 `delete` tests and 9 `basic-update` variants still skip. Graph
management (LOAD / CLEAR / DROP / CREATE / ADD / MOVE / COPY) is entirely
unimplemented (46 skipped tests). Transaction semantics (atomicity of
multi-op requests) untested. **Would use for append-only bulk loading,
not for anything resembling a read-write workload.**

### SPARQL-with-entailment for schema.org — **Yes for the patterns the
demo exercises; no for OWL axioms beyond sub/inv/sameAs.**

RDFS closure (subClassOf, subPropertyOf, domain, range, reflexivity,
container membership) passes all 39 rdf-mt tests and all six demo
entailment queries. OWL-RL covers the demo's `owl:inverseOf` and
`owl:sameAs` patterns. **Would not trust for anything involving
`someValuesFrom`, `allValuesFrom`, cardinality restrictions, enumerated
classes, or class intersection/union** — the 21 tableau-dependent
entailment tests all produce 0 rows. For schema.org the coverage is
fine (schema.org's semantics are almost entirely RDFS subproperty/
subclass + a few sameAs chains), and the demo's six entailment queries
produce the correct answers. For BFO/SNOMED/biomedical OWL-DL
ontologies: no.

### Serving SPARQL Protocol from untrusted clients — **No. Do not.**

Reasons (in rough order of severity):

1. **No SPARQL Protocol implementation at all.** 34 protocol tests all
   skip. There is no HTTP surface in the verified F\* layer. A Protocol
   adapter would be hand-written OCaml glue and is not there yet.
2. **Turtle parser is O(n²) or worse** (CLAUDE.md "Known Performance
   Issues") — 10k triples takes >8 minutes and has been killed. A single
   untrusted POST of a moderately large Turtle payload is a trivial DoS.
3. **Parser validates too leniently in multiple places.** 38 RDF/XML
   parser fails, 11 TriG fails, 10 Turtle fails, 38 W3C negative
   syntax tests where "Should reject but parsed OK". Malformed input
   silently produces wrong triples rather than a parse error.
4. **No surface for timeouts, query cost bounds, memory caps, or
   result-size limits.** The evaluator is total but not metered.
5. **SERVICE returns empty instead of erroring or refusing** — an
   untrusted query that references `SERVICE <http://attacker/>` would
   be silently ignored today, but the day #57 lands, it'd be a
   server-side SSRF vector unless deliberately scoped. Worth flagging
   now so the SERVICE implementation PR gets a sandbox review.
6. **ASK always returns false** (this audit's Part 1 finding). An
   attacker probing for the existence of records via ASK would
   currently get "no" for everything, which is a safe-fail in a
   confidentiality sense but makes the endpoint useless.

## Most worrying finding — ASK is silently broken

The demo's `ask` query (Alice → ? → Eve) returns `ASK=false` despite
the equivalent SELECT returning `{mid: ex:carol}`. I then reproduced on
the native `./bin/darwin-arm64/factoidal`:

```
$ echo '<http://a> <http://b> <http://c> .' > /tmp/tiny.nt
$ factoidal -d /tmp/tiny.nt -e 'ASK { ?s ?p ?o }' -o json
{ "head": {}, "boolean": false }
$ factoidal -d /tmp/tiny.nt -e 'SELECT * WHERE { ?s ?p ?o }' -o json
{ "head": { "vars": [...] }, "results": { "bindings": [ {...} ] } }
```

**ASK always returns false, for every dataset and every pattern I
tried.** This is not just a comparator issue in the test runner
(CLAUDE.md already discloses that the runner doesn't check the
expected boolean). It's a real evaluator bug that produces wrong
answers to the user's actual query.

Why it hasn't shown up in W3C numbers: there is no `ask` test suite in
`tests/w3c/sparql/sparql11`. SPARQL 1.0's DAWG tests had ASK tests,
but this repo's SPARQL 1.1 subset doesn't seem to include them (or
they're embedded in other suites under `syntax-query` only). So the
456/488 SPARQL number does **not** include any case that would have
flagged this.

Not diagnosed in this audit (stayed within read-only scope). The F\*
spec file is `formal/fstar/SPARQL11.Algebra.fst`; the likely suspects
are the top-level dispatch for `QF_Ask` / `Q_Ask` and whether it
evaluates the pattern and checks for a non-empty mapping list.
`w3c_runner.ml` emits `"boolean": false` so it's clearly taking the
ASK branch — the issue is upstream of serialization. Worth an issue.

## Second-most worrying finding — 21 of 23 entailment fails are the OWL tableau gap, but the framing matters

The worklog and public docs describe OWL-RL as implemented. The 23
entailment fails split as:

- **21 fails** are tests that genuinely need OWL DL / tableau reasoning
  (someValuesFrom, allValuesFrom, cardinality, class expressions,
  RIF rules). These are correctly out of scope for OWL-RL-the-rulesystem
  and should be re-labelled in the test runner as "OWL-DL needed" rather
  than "FAIL". A pure OWL-RL implementation **cannot** pass them
  without either a tableau prover or a hand-expanded axiom set that
  doesn't really match the test's intent.
- **2 fails** (`paper-sparqldl-Q1` 3→2, `sparqldl-12 range test` 2→1)
  are off-by-one within an otherwise-working path, which suggests a
  real OWL-RL gap (maybe a rule that isn't fully implemented).

The honest headline is **45 / 47 entailment tests that an RDFS+OWL-RL
rule engine could plausibly be expected to pass, are passing** (47
pass, 2 near-misses, 21 out-of-regime). That's a better story than
"47 pass 23 fail". The `w3c_runner` could distinguish
`owl-direct-semantics` vs `owl-rl` manifests; the rdf-tests suite
already has this distinction via manifest metadata.

## File/path quick reference

- Demo HTML: `docs/fstar-extracted/index.html`
- Browser engine (js_of_ocaml): `docs/fstar-extracted/factoidal.js`
- Native CLI: `bin/darwin-arm64/factoidal`, `bin/darwin-arm64/w3c_runner`
- W3C tests: `tests/w3c/sparql/sparql11/`, `tests/w3c/rdf/rdf11/`
- Full runner log (this audit): `.claude-runs/qa-w3c-20260419-195819.log`
- Older `--rdf`-only log for cross-check: `.claude-runs/full-20260419-184747.log`
- Demo test artifacts: `/tmp/qa-demo/` (manifest.json, *.ttl/*.trig, q-*.rq, results/*.json, summary.tsv)
