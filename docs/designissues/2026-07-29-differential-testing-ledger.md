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

### ✅ Finding 1 (was 🔴 ours-wrong, SILENT FAILURE) -- FIXED 2026-07-30 in #325: RDF/XML drops the whole document on a non-ASCII property-element local name

> Resolved. See "Resolution of Findings 1 and 2" below for the root cause,
> the second defect that turned out to be in this finding's own repro
> fixture, and the measured suite deltas. The analysis below is kept as
> written on 2026-07-29, including the parts the fix corrected.

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

### ✅ Finding 2 (was 🔴 ours-wrong, SOUNDNESS-RELEVANT) -- FIXED 2026-07-30 in #325: Turtle/TriG corrupt non-ASCII bytes inside `<IRIREF>`

> Resolved. The locus guess below ("whatever code turns that byte span into
> the final IRI string value") was right; it was
> `Parser.Turtle.decode_iri_escapes_acc`. N-Triples and N-Quads turned out
> to be affected too, on their escaped-IRI slow path. See "Resolution of
> Findings 1 and 2" below.

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

## Resolution of Findings 1 and 2 (2026-07-30, issue #325)

Both are FIXED, and they turned out to be **one** root cause with seven
call sites — plus three more instances of the same defect that this
harness's generator never happened to produce.

### The root cause

`FStar.String.string_of_list` extracts (F\* OCaml runtime,
`ulib/ml/app/FStar_String.ml`) to

```ocaml
let string_of_list l = BatUTF8.init (BatList.length l) (fun i -> BatUChar.chr (BatList.at l i))
```

so it **re-encodes every list element as a UTF-8 codepoint**. Any parser
that walks bytes with `Parser.FastString.fs_byte_index`, accumulates them
into an F\* `list char`, and finishes with `string_of_list` therefore
rewrites all of its non-ASCII input: byte `0xE6` goes in and the two
bytes `0xC3 0xA6` come out. That is exactly UTF-8 read as Latin-1, and it
is silent.

This ledger's Finding 2 guessed the locus correctly: *"whatever OCaml/F\*
code turns that byte span into the final IRI string value"*. It was
`Parser.Turtle.decode_iri_escapes_acc`. The reason the **literal** on the
same source line round-tripped correctly is that literals go through
`scan_short_string_span` + `span_to_string`, i.e. `fs_byte_sub`, which is
byte-transparent. Nothing about file decoding differed between the two
tokens — only the primitive each used to leave the parser. That asymmetry
was the whole bug, and the diagnostic lead in this ledger is what
isolated it.

Escapes are the mirror-image case, and were correct all along: a
`\uXXXX` carries a **codepoint**, and `string_of_list` on a ONE-element
list is precisely "encode this codepoint as UTF-8". Mixing bytes and
codepoints in one accumulator is the defect; the rule that replaces it is
now stated once, at the boundary where the hazard lives, on
`Parser.FastString.fs_utf8_of_codepoint`:

> raw bytes leave through `fs_byte_sub`, codepoints leave through
> `fs_utf8_of_codepoint`, and the two never share an accumulator.

`FStar.String.string_of_char` is the opposite trap and is worth naming
alongside it: it extracts to `BatString.of_char (Char.chr c)`, so it is
byte-oriented (correct for passing a byte through) and **raises** above
U+00FF (never hand it a codepoint).

### Finding 1 was TWO defects, and the fixture had one of them

**Defect A, the reported one.** The XML Name scan was byte-level. Its
non-ASCII arm accepted UTF-8 LEAD bytes (`>= 0xC0`) and rejected
CONTINUATION bytes (`0x80`–`0xBF`), so the scan stopped *inside* the
first non-ASCII codepoint. `<ex:日本語 …>` scanned as the name `ex:` +
`0xE6` and then met `0x97` where the element parser wanted `>` or
whitespace. The element failed, the failure propagated to the document
root, and the lenient RDF/XML entry point returned `[]`. Hence "0
triples, exit 0" on a well-formed file — the whole-document drop the
bisection in Finding 1 observed. Confirmed by direct before/after on a
minimal fixture, not inferred.

Alongside it, the START character was never checked at codepoint level
at all: `parse_xml_name` tested the byte and then hand-special-cased the
single codepoint U+00B7. Every other non-NameStartChar codepoint was
waved through as a name start; the only reason xmlconf never noticed is
that the byte-level body scan then truncated the name and the element
failed anyway — the right verdict for the wrong reason. Fixing the body
scan removed that accident and two xmlconf cases surfaced the hole
immediately (`o-p05fail4`, a Name may not start with a CombiningChar;
`rmt-020`, U+F0000, illegal in BOTH XML 1.0 and 1.1). Both are fixed by
testing the start codepoint against the real NameStartChar table.

**Defect B, in the fixture itself.** `rdfxml_unicode_qname_dropped.rdf`'s
own header comment contained four `--` sequences (`exit code 0 -- no
error is printed`, `(WRONG -- should be 1)`). XML 1.0 §2.5 forbids `--`
anywhere inside a comment, so the fixture was **not well-formed XML** and
Factoidal correctly rejected it for that second, independent reason.
pyoxigraph and rdflib are lenient about it, which is why the fixture
looked like a clean single-variable repro when it was not. With the
comment rewritten (2026-07-30) the fixture isolates Defect A exactly:
the base binary gives `0 triples` with exit code 0, the fixed binary
gives `1 triples`, and pyoxigraph gives the same single quad. Keep that
file free of double hyphens.

The lesson generalises: a differential-testing repro is itself an input
to a parser, and "the reference implementations accept it" is not the
same as "it is valid". Reduce a repro to a MINIMAL fixture and check the
minimal one independently — a repro carrying explanatory prose can carry
a second defect in that prose.

The swallowed-error path this ledger asked for as its own defensive fix
also landed. `bin/factoidal-cli/factoidal_cli.ml` now diagnoses a parse
that yields zero triples from a document that has content, and exits
non-zero. The judgement of "did this document actually parse" stays in
F\*: every format already ships a strict entry point returning `None` on
a syntax error (`parse_rdfxml_with_base_strict`,
`parse_turtle_with_base_strict`, `parse_ntriples_strict`,
`parse_nquads_strict`, `parse_trig_with_base`), and the CLI only ASKS one
of them, only on the zero-triple path — so a healthy parse never pays for
a second pass and no parsing decision moves into the consumer
(anti-pattern #15). A legitimately triple-free document still exits 0.

### Three more instances the harness did not generate

Worth recording, because each hid behind a fast path that made its format
look correct — the generator would have had to produce a specific,
unusual token shape to reach any of them:

- **N-Triples and N-Quads IRIREFs** (`Parser.NTriples.parse_iri_body_acc`).
  `parse_iri_raw` takes a `scan_iri_end` fast path that slices with
  `fs_byte_sub` whenever the IRI contains no backslash, so a plain
  non-ASCII IRIREF is correct and the char accumulator is never entered.
  This ledger's "same file as N-Triples round-trips correctly" observation
  was true — but only of escape-free input. `<http://e.org/日a本b語>`
  parsed to `<http://e.org/æ¥a本bèª>`. Both formats were affected.
- **Turtle PN_LOCAL names** (`Parser.Turtle.unescape_pn_local`), which
  short-circuits to the input string unless `has_backslash_fuel` finds a
  backslash. `ex:日本` was right; `ex:日\-本` resolved to
  `<http://e.org/æ¥-æ¬>`.
- **XML CDATA sections, comments, PI bodies, and DTD internal-entity
  values** (`Parser.XML.parse_cdata_body` / `parse_comment_body` /
  `collect_pi_body` / `read_entity_value_raw`). CDATA is the one whose
  content reaches RDF literals, so `<![CDATA[日本 café]]>` produced the
  literal `"æ¥æ¬ cafÃ©"` — a user-visible corruption that no
  conformance fixture caught.

### xml-conformance moves, and the composition matters 🧭

Measured on identical runner sources, base parser vs fixed parser:
**1429 pass, 0 fail, 1156 skip (of 2585) → 1456 pass, 0 fail, 1129 skip.**
Zero fails before and after. But read the breakdown, because the
composition changes a lot:

| bucket | base | fixed |
|---|---|---|
| valid documents accepted | 399 | **727** |
| not-wf documents correctly rejected | 1030 | **729** |
| skip: valid DTD-boundary (rejected) | 386 | 58 |
| skip: out-of-profile | 37 | **339** |

**+328 valid documents now parse** that were previously rejected — that
is the bug, and it is the whole point.

**302 not-wf tests moved from pass to skip.** They were "passing" only
because the parser rejected every non-ASCII name, so it satisfied
"illegal in XML 1.0 4th edition" by accident while also rejecting every
LEGAL non-ASCII name. They are almost all in
`ibm/ibm_oasis_not-wf.xml` — 312 not-wf entries in the corpus carry
`EDITION="1 2 3 4"`, i.e. they assert the enumerated Appendix B
Letter/CombiningChar/Extender tables that XML 1.0 **5th edition** (2008)
retired in favour of the XML 1.1 NameStartChar/NameChar ranges.
Parser.XML now implements the 5th-edition/1.1 production — the same
table `XML.Wellformedness.fst` already carried, and the one current XML
processors implement — so `bin/xml-runner/xml_runner.ml` gained an
`EDITION`-aware branch that classifies those as out-of-profile, the same
category it already used for the 37 XML-1.1-only and Namespaces-only
cases. Not a fail, not a claimed pass.

🧭 **Decision for the owner.** The alternative is to implement the XML
1.0 **4th**-edition Appendix B tables instead, which would keep those
302 as real passes AND keep the 328 valid documents (日本語 is
Ideographic under both editions). Cost: a several-hundred-line hand
transcription of Appendix B, and Parser.XML would then implement an
older Name production than `XML.Wellformedness.fst` does — an internal
inconsistency. The 5th-edition table was chosen for consistency with
what the tree already had. Say the word if the 4th-edition table is
wanted instead.

### Not fixed, deliberately

`Parser.Combinators`' `ptake_while` / `ptake_while1` / `ptake_while_acc` /
`pquoted_body` carry the same byte-into-`list char` pattern. They were
rewritten byte-transparently and the rewrite was **reverted**: exporting
`ptake_while_scan`'s refined `r:nat{r >= pos}` return type through them
puts enough extra facts into every caller's SMT context to break an
unrelated termination proof in `Parser.WKT.parse_ring_list_rest`
(measured: WKT verifies on the base tree and fails with the rewrite, same
z3 4.13.3; stripping the refinement through a plain `nat` moved the
failure to the next structurally identical recursion rather than removing
it). No reachable caller can hit the defect — every one passes an
ASCII-only predicate and `pquoted_string` has no caller at all — so
destabilising a green module for an unreachable defect was the wrong
trade. The four functions now carry a warning banner naming the hazard,
the safe alternatives (`ptake_while_pos` / `ptake_while1_pos`), and the
condition for redoing the rewrite.

### Why the conformance suites were blind to all of this

Stated in this ledger's own framing, and confirmed: RDF 1.1 scores 1031
pass, 0 fail with every one of these defects present. The W3C parser
tests check **acceptance** — did the file parse, to the right triple
count — not **preservation** of the term strings through to output. This
is the coverage gap issue #92 named. The regression pin added with the
fix (`tests/local/parser_unicode_regressions.sh`, wired as
`.github/test-suites/local-parser-unicode.yaml`) asserts preservation
instead, comparing exact canonical output bytes, and covers both the
defective paths and the already-correct ones so a future change cannot
regress a correct path into a defective one.

### Harness note: the swap classifier earns its keep

The `soundness_suspects` counter now catches same-count "swap" shapes
(a corrupted triple in place of a correct one), not only one-sided
add/drop. The 2026-07-29 baseline quoted below predates that fix and so
undercounts Finding 2 at 134; a re-run of the identical seed range with
the fixed classifier scores the baseline at **422 soundness_suspects**
(288 swap + 134 drop). That is the number the post-fix run is measured
against — see "Post-fix re-run" below.

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
