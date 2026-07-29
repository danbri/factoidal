# Differential testing against reference implementations (issue #317)

Review gate 4 (issue #313, sub-issue #317): *"Fuzz RDF parsers and SPARQL
evaluation against reference implementations ... Conformance fixtures
alone are vulnerable to test-directed implementation."*

This doc is the triage ledger. The harness lives at
`tools/difftest/` and is described in its own module docstrings; this
file records what it found, with a disposition per finding
(ours-wrong / theirs-wrong / spec-ambiguous), plus the environment
inventory (what reference implementations were actually reachable in
this container) and the harness's own limitations.

Cross-reference: issue #75 (in-house unit/property/fuzz testing) covers
the SAME general intent (testing beyond the W3C fixture set) but at the
unit-test/OCaml-extraction-boundary level. This issue is specifically
about differential comparison against INDEPENDENT third-party engines on
GENERATED inputs. The two should stay cross-linked, not merged: #75's
scope includes non-RDF-semantic bugs (integer overflow in zarith, parser
crashes) that a differential harness against reference RDF engines would
never see, since those engines don't share Factoidal's OCaml internals.

## Environment inventory (what was actually reachable)

Per the session's environment-reality-check instruction: this container
routes outbound HTTPS through a policy-enforcing proxy
(`/root/.ccr/README.md`). `pypi.org` and `registry.npmjs.org` are on the
proxy's `noProxy` allowlist (direct, no tunnel needed); `crates.io`'s
index host is too. GitHub *release binary downloads* are the thing
historically blocked (per the `session-restore` skill) -- that matters
for Jena/RDF4J, which ship as GitHub release jars or need a Maven
Central resolve.

Probed and confirmed working:

- **rdflib 7.6.0** (`pip install rdflib`) -- pure-Python, independent
  SPARQL 1.1 query engine + RDF parsers (Turtle/N-Triples/N-Quads/TriG/
  RDF-XML) + `rdflib.compare.to_isomorphic` (graph-isomorphism-aware
  comparison, used here as a differential-testing ORACLE, not just a
  data source).
- **pyoxigraph 0.5.9** (`pip install pyoxigraph`) -- Python binding to
  Oxigraph (Rust). Parses all 5 syntaxes we support (`RdfFormat.N_TRIPLES
  /N_QUADS/TURTLE/TRIG/RDF_XML`), runs SPARQL 1.1 query, and --
  significant for this gate -- ships a **native RDFC-1.0 canonicalizer**
  (`Dataset.canonicalize(CanonicalizationAlgorithm.RDFC_1_0)`), so
  canonical-form comparison didn't need to route through a third tool.

Not probed / not attempted this session (JVM + Maven ARE present --
`java 21`, `/opt/maven`, `/opt/gradle` -- so Jena/RDF4J are plausible for
a follow-up; deprioritized here per the "get one working end-to-end
rather than four half-wired" instruction, since rdflib + pyoxigraph
already gave two independent engines, one of them (Oxigraph) with a
native RDFC-1.0 implementation that made canonicalization-based
comparison direct rather than home-grown):

- Apache Jena ARQ / RDF4J -- would need a Maven dependency resolve
  (`org.apache.jena:jena-arq`, likely proxied through Maven Central,
  untested) or a local jar; the EXISTING `tools/jena_arq_*_probe.sh`
  scripts (see `skills/test-suites/SKILL.md`) don't actually invoke Jena
  at all -- see "What the existing Jena probes actually are" below, a
  finding in its own right.

**Net: this gate got TWO independent, currently-reachable reference
implementations working end-to-end (rdflib, pyoxigraph), not zero and
not four half-wired.**

## What the existing "Jena ARQ comparison probes" actually are

`skills/test-suites/SKILL.md` documents `tools/jena_arq_{syntax,basic,
graph,ask}_probe.sh` as "Jena ARQ probes". Reading them (this session):
they compare Factoidal's own output against the **expected `.srx` /
manifest files bundled inside a Jena source checkout's `DAWG-Final`
test directory** -- i.e. the same-ish W3C DAWG SPARQL test suite, just
sourced from Jena's copy of it rather than `w3c/rdf-tests` directly.
**None of these scripts invoke a Jena JAR or the ARQ CLI.** They are
fixture-based comparison against pre-computed expected results, exactly
the pattern issue #317 says is insufficient on its own ("conformance
fixtures alone are vulnerable to test-directed implementation") --
they are not yet a second independent IMPLEMENTATION in the loop.
This doesn't make them worthless (a second corpus of expected-result
fixtures is still useful), but the skill doc's framing as "Jena
comparison" overstates what they check. Filed as an obsolescence-sweep
note; not fixed here (out of this task's scope; the doc-precision fix
belongs with whoever next touches that skill file).

## The harness (`tools/difftest/`)

| File | Role |
|---|---|
| `atoms.py` | Term generators: adversarial IRIs (unicode, percent-encoding, sub-delims), Turtle-legal blank-node label shapes, unusual-case language tags (`EN-US`, `zh-Hans-CN`, `i-klingon`, ...), datatype-boundary literals (int32/int64/bignum boundaries, decimal/double edge values incl. `INF`/`NaN`/subnormals, boolean lexical variants, dateTime edge cases, string-escape edge cases incl. surrogate-pair emoji, combining marks, RTL text). |
| `rdfgen.py` | Builds ONE abstract graph/dataset per seed (bnode-heavy backbone "mini database" + deep bnode chain/tree + symmetric 2/3/5-cycles + a nested RDF collection built as both explicit `rdf:first/rest/nil` triples AND native `( ... )` Turtle/TriG sugar for the SAME semantic content), then renders it into N-Triples, Turtle, RDF/XML (`graph` profile) or N-Quads, TriG (`dataset` profile, multiple named graphs). |
| `sparqlgen.py` | A battery of SPARQL query shapes (BGP join, OPTIONAL, UNION, FILTER incl. `lang()` and integer-boundary comparisons, property path `+`, ASK, `COUNT`+aggregate, CONSTRUCT, VALUES) parameterized against one Doc's backbone entities. |
| `compare.py` | Canonical-N-Quads line-set comparison (the "compare via canonicalisation, never string equality" primitive); a langtag-case auto-classifier; and `isomorphic_after_langtag_fold`, a THIRD-implementation (rdflib) graph-isomorphism oracle used to see through RDFC-1.0's hash-cascade (below). |
| `rdf_diff.py` | RDF parser differential harness: Factoidal `canonicalize` vs pyoxigraph `Dataset.canonicalize(RDFC_1_0)` on the same source bytes, plus a cross-format self-consistency check (all renderings of the SAME abstract graph must canonicalize identically under Factoidal itself). |
| `sparql_diff.py` | SPARQL evaluation differential harness: Factoidal `query -o json` vs rdflib vs pyoxigraph, over N-Triples data (isolating query-evaluation bugs from the parser bugs already tracked in `rdf_diff.py`). |
| `repros/` | Minimal standalone repro files for the two confirmed parser bugs below. |
| `run_differential.sh` | Driver: `tools/difftest/run_differential.sh [N_RDF] [N_SPARQL]`. |

Run it: `tools/difftest/run_differential.sh 400 150` (or any N); reports
land at `.claude-runs/difftest/{rdf,sparql}-corpus/report.json`.

### A methodological note that is itself worth recording

Building this harness surfaced three harness-side bugs before it surfaced
any engine bugs, each instructive:

1. **Locale-dependent subprocess decoding.** This container's locale is
   POSIX/C (`LANG` unset). `subprocess.run(..., text=True)` without an
   explicit `encoding="utf-8"` decodes Factoidal's (correct) UTF-8 stdout
   via `locale.getpreferredencoding()`, silently mangling every
   multi-byte character. The first raw run misattributed ~10 "Factoidal
   disagreements" to this before it was caught by re-decoding the raw
   bytes independently. **Never trust a differential harness's own
   subprocess encoding defaults; pin them.**
2. **Term-key normalization gaps produce false positives.** Comparing
   `datatype: null` (Factoidal's JSON omits the implicit `xsd:string`)
   against `datatype: xsd:string` (pyoxigraph always fills it in) as
   "different" produced dozens of spurious SELECT-row disagreements
   before normalizing both to the same key.
3. **RDFC-1.0's hash cascade defeats naive line-diffing.** One
   differently-cased language tag anywhere in a densely-connected
   blank-node graph changes the Hash N-Degree Quads result for every
   blank node in its transitive neighborhood, so a line-level diff shows
   dozens of "unrelated" disagreements for what is really one
   already-known issue. Catching this needed a THIRD independent
   implementation (rdflib) doing an actual graph-isomorphism check after
   folding case on both sides (`compare.isomorphic_after_langtag_fold`),
   not a smarter string heuristic.

Point 3 specifically is why raw disagreement COUNTS from this class of
harness are not meaningful without this classification step -- a
project that reported "1063 disagreements found" (the first, unclassified
run's raw number) would have been technically true and substantively
misleading (anti-pattern #3/#25 territory even in a brand-new report). ⚠️

## Findings

### 🔴 Finding 1 (ours-wrong, SILENT FAILURE -- highest priority): RDF/XML drops the whole document on a non-ASCII property-element local name

**Repro:** `tools/difftest/repros/rdfxml_unicode_qname_dropped.rdf`

```
bin/linux-x86_64/factoidal count tools/difftest/repros/rdfxml_unicode_qname_dropped.rdf
```

Factoidal prints `... : 0 triples`, **exit code 0**, **no error message**.
The file is well-formed RDF/XML (confirmed independently via Python's
`xml.dom.minidom`) with one property element whose local name is
non-ASCII (`<ex:日本語 rdf:datatype="...#double">1.0E-300</ex:日本語>`).
Both reference implementations parse it correctly:

```python
list(pyoxigraph.parse(path=..., format=RdfFormat.RDF_XML))  # -> 1 quad
rdflib.Graph().parse(..., format='xml')                     # -> 1 triple
```

Bisection (splitting the fuzz corpus's RDF/XML output at `rdf:Description`
block boundaries, not raw lines -- raw-line bisection of XML produces
malformed-XML false leads, a trap hit and corrected during this work)
confirmed: adding any ONE `rdf:Description` block containing a
non-ASCII-named property element drops the ENTIRE document's triple
count to zero from that point on, not just that one triple. So this is
a whole-document parse failure being swallowed somewhere between
`Parser.RDFXML.fst` and the CLI, not a per-triple skip.

**Impact:** any RDF/XML file with a non-ASCII-named property element
(plausible for e.g. multilingual ontologies using native-script property
names) silently produces an EMPTY graph with a SUCCESS exit code. A
caller has no way to detect this from the CLI's own signals.

**Disposition: ours-wrong.** Locus (not fixed here, per this task's
scope discipline -- other agents hold the build locks and a fix without
gate review is how regressions land): `formal/fstar/Parser.RDFXML.fst`
(QName/element-name handling) and whatever underlying XML
tokenizer/Name-production it depends on for element names, PLUS
separately the swallowed-error path between the parser and the CLI
(`count`/`canonicalize`/`dump` should never exit 0 with "0 triples" on a
genuine parse failure of a non-empty file -- that symptom alone is worth
its own defensive fix regardless of the root parser bug).

### 🔴 Finding 2 (ours-wrong, SOUNDNESS-RELEVANT): Turtle/TriG corrupt non-ASCII bytes inside `<IRIREF>`

**Repro:** `tools/difftest/repros/turtle_iriref_unicode_mojibake.ttl`

```
bin/linux-x86_64/factoidal canonicalize tools/difftest/repros/turtle_iriref_unicode_mojibake.ttl
```

Input: `<https://example.org/日本語> ex:p "plain literal café" .`
Factoidal's canonical output: `<https://example.org/æ¥æ¬èª> ...` -- the
IRI is corrupted. The corruption is **valid UTF-8** (so `file`/byte-count
checks alone don't reveal it -- only decoding does), consistent with a
"read UTF-8 bytes as if Latin-1 codepoints, then re-encode as UTF-8"
double-encoding bug. Notably: the **literal** on the same line
(`"plain literal café"`) round-trips CORRECTLY -- the corruption is
specific to `<...>` IRIREF tokens, not to string-literal parsing. Same
file as **N-Triples** (`<https://example.org/日本語> <...> "x" .`)
round-trips correctly; the same file re-saved as **TriG** shows the
identical corruption (shared IRIREF scanner). Confirmed against both
references:

```python
list(pyoxigraph.parse(path=..., format=RdfFormat.TURTLE))  # correct IRI
rdflib.Graph().parse(..., format='turtle')                 # correct IRI
```

**Disposition: ours-wrong, and soundness-relevant per this task's flag
criterion** -- Factoidal produces a triple with a DIFFERENT IRI than
every other implementation for the same input, which is exactly the
"we produce a triple no other implementation produces" case this task
was told to flag loudly. Locus (not fixed here): `formal/fstar/
Parser.TurtleScanner.fst`'s `scan_iri_ref_span`/`scan_iri_ref_end` (spans
only, byte-based scanning looked correct on inspection) or, more likely,
whatever OCaml/F* code turns that byte span into the final IRI string
value -- the corruption pattern points at a byte-vs-codepoint mismatch in
that extraction step, not in the span-finding scanner itself. Root cause
not fully isolated (out of this task's scope per the "report, don't
fix" instruction); the repro file above is the starting point for
whoever picks this up.

### 🟡 Finding 3 (spec-ambiguous): RDFC-1.0 canonical form is not stable across language-tag casing

RDFC-1.0 (`bin/linux-x86_64/factoidal canonicalize`) preserves a literal's
language tag EXACTLY as written (`"x"@EN-US` stays `@EN-US`). Oxigraph's
native RDFC-1.0 implementation (`pyoxigraph`) folds language tags to
lowercase (`@en-us`) during its own processing. Checked against the
actual specs (not assumed) via the W3C TR pages:

- **RDF Dataset Canonicalization (RDFC-1.0)** itself flags this as a
  KNOWN, UNRESOLVED cross-implementation hazard: *"RDF 1.1 Concepts and
  Abstract Syntax lacks clarity on the representation of
  language-tagged strings ... different implementations might represent
  language tags differently ... which could lead to different canonical
  forms and hash values,"* recommending *"user communities ought to
  agree to use lower case language tags."*
- **RDF 1.2 Concepts sec 3.4.1** explicitly permits either choice:
  implementations *"MAY preserve the case from the original
  representation, provided that it processes it in a case-insensitive
  manner,"* or normalize via BCP 47 canonicalization. RDF 1.2 also
  changed the abstract model so that case difference does not even
  propagate into literal identity (`"chat"@fr` and `"chat"@FR` are the
  SAME literal, a change from RDF 1.1 where they were distinct terms an
  implementation MAY normalize).

**Disposition: spec-ambiguous, not a bug on either side.** Both Factoidal
(preserve) and Oxigraph (fold) are compliant choices under RDF 1.2 sec
3.4.1's explicit either/or. This is precisely the class of finding this
task asked to be written up rather than silently conformed away --
conforming Factoidal's behavior to Oxigraph's here would not fix a bug,
it would just pick the other allowed option. Auto-classified in the
harness (`compare.is_only_langtag_case_difference` for direct line
diffs; `compare.isomorphic_after_langtag_fold` for the cascaded case,
see the methodological note above) so it doesn't drown out real
findings in the raw counts.

### 🟢 Finding 4 (theirs-wrong / reference-implementation limitation, positive result for Factoidal): numeric-literal lexical-form preservation

Two independent, reproducible sub-cases where Factoidal preserves a
literal's exact lexical form through simple SPARQL variable projection
(no cast, no arithmetic -- just `SELECT`), per RDF 1.1/1.2 Concepts'
requirement that a literal's lexical form is part of its term identity,
while a reference implementation re-normalizes it:

**4a -- `xsd:decimal` lexical form.** Minimal repro:

```python
import pyoxigraph as ox
d = ox.Dataset()
d.add(ox.Quad(ox.NamedNode('http://e/s'), ox.NamedNode('http://e/p'),
              ox.Literal('0.0', datatype=ox.NamedNode('http://www.w3.org/2001/XMLSchema#decimal'))))
d.canonicalize(ox.CanonicalizationAlgorithm.RDFC_1_0)
print(list(d)[0])  # "0"^^xsd:decimal -- NOT "0.0"
```

rdflib preserves `"0.0"`; Factoidal preserves `"0.0"`; Oxigraph alone
normalizes to `"0"`. 2-vs-1, matching the spec-mandated behavior.

**4b -- `xsd:integer` beyond native word width, in a SPARQL `FILTER`.**
Query `SELECT ?age WHERE { ?s :age ?age . FILTER(?age > 1000000000) }`
over a triple with `?age = "99999999999999999999999999999999999999"^^
xsd:integer` (far beyond int64/i128): Factoidal and rdflib both correctly
match the row (XSD 1.1 `integer` is an UNBOUNDED-precision type; Python
and, per this differential run, Factoidal's numeric evaluation both
honor that). pyoxigraph's `FILTER` **silently drops the row** -- no
error, no match, despite the raw triple being retrievable unfiltered.
Minimal repro (`tools/difftest/sparql_diff.py`'s `filter_integer_boundary`
query against seed 5009 reproduces it; a standalone two-line repro is in
the harness output, not duplicated here).

**Disposition: theirs-wrong (Oxigraph-specific limitation), and a
genuine positive signal for Factoidal** -- both sub-cases show Oxigraph
trading exact XSD semantics for a fixed-width/canonical internal numeric
representation (a defensible engineering trade-off for a
performance-oriented engine, but a real divergence from the RDF/SPARQL
spec's literal-identity and unbounded-integer requirements), while
Factoidal (agreeing with rdflib, a second independent implementation)
gets the spec-mandated behavior. Recorded here per the ledger's own
rule -- disagreements get triaged and reported in both directions, not
just the direction that finds bugs in us.

## Scale of the confirmed run (2026-07-29 baseline)

- **RDF harness:** 200 generated instances (mixed `graph`/`dataset`
  profile, small/medium/large size, all 5 syntaxes where applicable),
  run via `tools/difftest/rdf_diff.py --n 200` (406.6s wall-clock).
  Confirmed disposition breakdown: **424 labelled `disagreement`, 108
  labelled `spec-ambiguous-langtag-case-cascaded`, 2 labelled
  `spec-ambiguous-langtag-case`** (of 200 instances x up to 5 format
  renderings each = up to 1000 canonicalization comparisons). Remaining
  `disagreement` entries by format: `ttl` 134, `rdf` 134, `nq` 66,
  `trig` 66, `nt` 24 -- the `ttl`/`rdf`/`nq`/`trig` counts are Findings
  1+2 (RDF/XML whole-document drop; Turtle/TriG IRIREF mojibake --
  `nq`/`trig` inherit the same Turtle-family IRIREF scanner bug as
  `ttl`). The 24 residual `nt`-format entries (N-Triples has NEITHER
  known parser bug) were spot-checked: re-running
  `compare.isomorphic_after_langtag_fold` with a longer timeout on a
  sample confirmed they are uncaught cascades of Finding 3 (the 3-second
  cap missed them at this instance size, not a fourth new bug class --
  see the harness-limitations note on this cap below). All 134
  `soundness_suspects` in this run are format `rdf` (Finding 1's
  whole-document drop registers as "factoidal DROPPED quads" under the
  one-sided add/drop check `rdf_diff.py` used at run time). **That
  undercounts Finding 2**: the Turtle/TriG mojibake bug is a same-COUNT
  "swap" (a wrong triple in place of a correct one, not a pure drop), a
  shape the soundness checker did not classify as `soundness_suspect`
  until a fix landed later in this session (see `rdf_diff.py`'s comment
  at the swap-detection branch) -- Finding 2 IS soundness-relevant per
  this task's own criterion regardless of that counter, as its writeup
  above states directly from the manual repro, not from this counter.
  Full machine-readable report:
  `.claude-runs/difftest/rdf-corpus/report.json` (not committed --
  `.claude-runs/` is gitignored per repo convention; regenerate with
  `tools/difftest/run_differential.sh`). The run also flagged 334
  cross-format self-inconsistencies (Factoidal's OWN canonical output
  differing between two renderings of the SAME abstract graph) --
  expected, not a fourth finding: this is exactly what Findings 1-2
  predict (an RDF/XML or Turtle/TriG rendering of a graph that also has
  a correct N-Triples rendering WILL self-disagree with N-Triples,
  since Factoidal parses the two renderings differently).
- **SPARQL harness:** 150 generated instances x 9-10 query shapes each
  x 2 reference implementations, run via
  `tools/difftest/sparql_diff.py --n 150`. Confirmed disposition
  breakdown: **667 pass-through labelled `disagreement`, 142 labelled
  `spec-ambiguous-langtag-case`** (out of the comparisons that produced
  any finding at all -- most query/reference/instance combinations
  agreed and produced no finding). Per-query-shape counts: `union_age_note`
  253, `optional_note` 215, `construct_has_name` 104,
  `filter_integer_boundary` 56, `property_path_knows_plus` 39;
  `bgp_typed_name`, `ask_knows_exists`, `count_persons`, `values_clause`
  produced ZERO disagreements at this scale (those query shapes'
  evaluation matches both references exactly).
- **Manual sampling across the SPARQL disagreements (not a full
  automatic classification -- noted as a harness limitation below)
  confirms they reduce to Findings 3 and 4, not new classes:**
  `filter_integer_boundary`'s 56 are ALL `reference=pyoxigraph` with
  `factoidal_rows > reference_rows` (Finding 4b, the bignum-FILTER
  drop); `union_age_note`/`optional_note`/`construct_has_name`/
  `property_path_knows_plus` split roughly evenly between
  `reference=rdflib` and `reference=pyoxigraph` (130/123, 112/103,
  52/52, 20/19 respectively), consistent with Findings 3 (langtag case)
  and 4a (numeric lexical-form re-normalization) affecting comparisons
  against BOTH references, rather than one engine-specific quirk.
- The RDF harness's raw disagreement counts are dominated, once
  properly classified, by Findings 1-3 above (RDF/XML's whole-document
  drop and Turtle/TriG's IRIREF corruption both affect nearly every
  generated instance, since the generator is deliberately unicode-heavy;
  Finding 3's cascade compounds this further before classification --
  see `compare.isomorphic_after_langtag_fold`, which is HARD-CAPPED at
  3 seconds per check per the methodological note above, so it does not
  catch every cascaded case at this instance size; residual
  `disagreement`-labelled entries in the RDF report include some
  uncaught cascades of the SAME Finding 3, confirmed by spot-checking a
  sample with a longer timeout, not exclusively new bugs).
  **Do not quote the raw JSON `len(disagreements)` number in isolation
  -- read the `disposition` field per entry, or this ledger's
  Findings section, instead** (anti-pattern #3/#25: an unlabelled
  count here would be exactly the kind of misleading score this
  project has been burned by before).

## Harness limitations (documented, not hidden)

- **SELECT-result blank-node comparison is an approximation, not a
  soundness-hardened isomorphism check.** `sparql_diff.py`'s
  `_canonical_bnode_labels` does 3 rounds of Weisfeiler-Leman-style
  iterative refinement over each result table's blank-node occurrences.
  This is adequate for the small distinct-blank-node counts these fuzz
  queries produce, but is NOT a general graph-isomorphism-hardness proof
  (pathologically symmetric result tables could in principle confuse it).
  The RDF harness's canonical-form comparison (`rdf_diff.py`) does not
  have this limitation, since it delegates to two independent spec
  implementations of an actual canonicalization algorithm.
- **Only 2 reference implementations, not the review's suggested 4**
  (Jena, RDF4J, Oxigraph, RDFLib). See the environment inventory above
  for why (JVM-based engines need a dependency resolve not attempted
  this session) and what's plausible for a follow-up.
- **No CI scheduling wired yet.** The review's acceptance criteria
  include a scheduled CI job; this session built and ran the harness
  manually. Follow-up: a `.github/workflows/differential-testing.yml`
  cron job (matching the `conformance-rerun.yml` pattern already used
  for the W3C suites) that runs `tools/difftest/run_differential.sh`
  with a fixed seed range and diffs the disposition summary against the
  previous run, surfacing NEW disagreement classes rather than
  re-litigating known ones every run.
- **CONSTRUCT / SELECT comparisons against pyoxigraph use its in-Python
  `Store`/`Dataset` API, not a subprocess** -- so a hang or crash inside
  pyoxigraph's Rust core would hang this harness's Python process too,
  not just fail one comparison. Not observed in this run; worth a
  `timeout`-wrapped subprocess boundary if this harness is hardened for
  unattended CI.
