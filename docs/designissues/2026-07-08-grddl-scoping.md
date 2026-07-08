# 2026-07-08 — GRDDL scoping

## Status

Research + scoping only. No F* code in this PR. Written to answer:
given we already have an F*-verified XSLT 1.0 engine, XML parser, and
RDF/XML parser, does GRDDL fit, and what would a Stage 1 slice cost.

## What GRDDL is

GRDDL ("Gleaning Resource Descriptions from Dialects of Languages") is
a W3C Recommendation (11 Sept 2007):

- Spec: <https://www.w3.org/TR/grddl/>
- Primer: <https://www.w3.org/TR/grddl-primer/>
- Test cases: <https://www.w3.org/TR/grddl-tests/> (manifest data at
  <https://www.w3.org/2001/sw/grddl-wg/td/>)

It extracts RDF from XML/XHTML documents by having the document (or a
namespace/profile document it points to) *reference an XSLT
transformation* that, applied to the source, produces RDF (typically
RDF/XML). A GRDDL-aware agent: fetches the source, discovers the
transformation reference(s), applies the XSLT, parses the result as
RDF, and (if more than one transformation was discovered) merges the
resulting graphs.

## 1. Mechanism

The spec table of contents (confirmed by fetch of the Rec text):

1. Introduction: Data and Documents
2. Adding GRDDL to well-formed XML
3. Using GRDDL with XML Namespace Documents
4. Using GRDDL with valid XHTML
5. GRDDL for HTML Profiles
6. GRDDL Transformations
7. GRDDL-Aware Agents
8. Security considerations
9. The GRDDL Vocabulary
10. References

Four discovery paths, in the spec's own terms:

**(a) `grddl:transformation` attribute (§2, "Adding GRDDL to
well-formed XML").** "The general form of associating a GRDDL
transformation link with a well-formed XML document is adding to the
root element a `grddl` namespace declaration and a
`grddl:transformation` attribute whose value is an IRI reference, or
list of IRI references." — a plain attribute on the document's root
element, resolved against the doc's base IRI. **Pure XML.** No fetch
needed to *discover* the reference (fetching the referenced
transformation itself is a separate step, §c below).

**(b) XHTML `head/@profile` + `link[@rel=transformation]` (§4, "Using
GRDDL with valid XHTML").** "The general form of adding a GRDDL
assertion to a valid XHTML document is by specifying the GRDDL profile
in the `profile` attribute of the `head` element, and `transformation`
as the value of the `rel` attribute of a `link` or `a` element." The
profile URI is the fixed constant `http://www.w3.org/2003/g/data-view`
(also serving as the `grddl` namespace URI, with `#`-suffixed terms
`grddl:transformation`, `grddl:namespaceTransformation`,
`grddl:profileTransformation`). **Pure XML** *if* the document is
well-formed XML (served/parsed as XHTML, not tag-soup HTML) — walk to
`html/head`, read `@profile`, walk `head`'s `link`/`a` children for
`@rel="transformation"`, read `@href`.

**(c) Namespace-document transformation (§3).** A GRDDL-aware agent
"can also retrieve the namespace document of an XML dialect to find a
GRDDL transformation by 'following its nose' from the namespace on the
root element" — i.e., dereference the root element's namespace URI,
parse whatever comes back (commonly RDF or another XHTML-with-profile
doc), and look for a `grddl:namespaceTransformation` statement/link in
it. **Requires an HTTP fetch of a second document** the source doesn't
control the availability of.

**(d) Profile-document transformation (§5, "GRDDL for HTML
Profiles").** Symmetric to (c) but for the `profile` URI instead of
the namespace URI: "add `profile="http://www.w3.org/2003/g/data-view"`
to the `head` element and make a link of type `profileTransformation`
to the transformation" *in the profile document itself* — so an
XHTML doc can point at a shared, third-party profile URI (e.g. the
standard "Embedded RDF" profile from the primer) that carries the
transformation link, rather than embedding the link locally.
**Requires an HTTP fetch.**

§7 ("GRDDL-Aware Agents") states the processing model: find every
transformation associated with the source via (a)-(d), "selectively
apply any or all discovered transformations to obtain GRDDL results,"
then "merge those GRDDL results." It also flags that "discovery by
namespace or profile document is recursive" and that implementations
should detect loops in the profile/namespace structure — a
non-trivial requirement once (c)/(d) are in play (a namespace document
can itself declare a profile that points to another namespace
document).

Output syntax (§6, "GRDDL Transformations"): "XSLT version 1 is the
format most widely supported" but the spec explicitly allows other
output serializations via the `media-type` attribute of
`xsl:output` — RDF/XML is the common case, not the only legal one
(the fetch confirms informative test cases exercise a Turtle/N3
output). A conformant processor in principle needs a
media-type-dispatching RDF parser, not just RDF/XML.

**Which of (a)-(d) is pure-XML, in-scope for our stack today:** (a)
and (b) are pure tree-walks over an already-fetched, already-parsed
`xml_node` — no new I/O. (c) and (d) require fetching and parsing a
*second* resource whose availability, content-type, and shape (RDF?
XHTML-with-profile? both?) aren't controlled by the source document.

## 2. Gap analysis against the current stack

We do have the three pieces GRDDL composes, verified in-repo:

- **XSLT 1.0 engine**: `formal/fstar/XSLT.Transform.fst`, `transform
  (stylesheet:xml_node) (source:xml_node) : string` at line 1124.
  Zero `assume val` in the file (grepped, confirmed) — pure F*, no
  host XSLT library. Extracted and reachable from JS as
  `fn.xsltTransform` (`npm/factoidal/fn.js`, `npm/factoidal/index.js`,
  `npm/factoidal/index.mjs`, plus the mirrored `docs/npm/foafos/`
  copies); demoed live in
  `docs/web/hub/27-transforming-and-checking-xml.md` against
  `tests/hub/post27_test.mjs`, calling
  `abi.xsltTransform(stylesheet, source)` and parsing a
  `{ok, output|error}` JSON envelope.
- **XML parser**: `formal/fstar/Parser.XML.fst`,
  `parse_xml_document` at line 1429. Zero `assume val`.
- **RDF/XML parser**: `formal/fstar/Parser.RDFXML.fst`,
  `parse_rdfxml` (line 1177) / `parse_rdfxml_with_base` (line 1169) /
  strict `option`-returning variants (lines 1184, 1193). Zero
  `assume val`. 166/166 on the W3C RDF/XML suite per
  `docs/claude-rules/current-state.md` (lines 509, 534: "rdf-xml
  166/166 ... RDF/XML 166/166 after the 2026-04-23" fixes).

So "parse XML → discover transform refs → `xsltTransform` → parse
result via RDF/XML → RDF graph" is a real, checkable composition, not
hand-waving: every arrow already has a verified F* function on each
end except "discover transform refs," which doesn't exist yet (§4
below covers it — it's a straightforward tree-walk, not a gap).

Now the parts that do NOT fit cleanly:

**HTML tag-soup is out of scope, plainly.** `Parser.XML.fst` parses
well-formed XML only (`parse_xml_document`, entry point requires
exactly one well-formed root element — see the file's own scope note
carried in
`docs/designissues/2026-05-07-xml-fstar-phase0-audit.md`). Real-world
`text/html` pages that are GRDDL sources in the wild are frequently
*not* well-formed XML (unclosed `<br>`, unquoted attributes, implicit
`<tbody>`, etc.) — that's precisely the case that needs an HTML5
tokenizer with error-recovery rules, which does not exist in this repo
and is a separate, large project (roughly the size of the whole
Parser.XML effort again, per the tag-soup section of the HTML5
parsing spec's state-machine complexity). XHTML served as
`application/xhtml+xml`, or any document that is *actually*
well-formed XML with an `.xhtml`/`.xml` extension, parses fine. GRDDL
test documents and hand-authored microformat pages are commonly
written to be valid XHTML for exactly this reason, so this isn't
fatal to a Stage 1 slice — but it does mean "GRDDL over an arbitrary
URL from the open web" is off the table until an HTML tokenizer
exists.

**Real-world XHTML entity references are a second, sharper gap.**
`Parser.XML.fst` gained DTD "Stage A" — internal-subset entity
declarations (`<!ENTITY foo "bar">` inside a `<!DOCTYPE ... [ ... ]>`
block) — per the DTD entity-table code at lines 318-435 and
`parse_doctype` at line 1327. But **external** `SYSTEM`/`PUBLIC`
entity declarations are explicitly *not* followed: "External entity
(SYSTEM/PUBLIC) or otherwise -- skip" (line 1241; see also line 1201).
The standard XHTML 1.0 `DOCTYPE` line —
`<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">` — has *no*
internal subset at all; every named entity XHTML authors rely on
(`&nbsp;`, `&mdash;`, `&copy;`, …) is declared in that external DTD.
A real-world XHTML document using `&nbsp;` will fail to parse today
with "reference to undeclared entity" unless it sticks to the five
XML-predefined entities (`&amp; &lt; &gt; &quot; &apos;`) and numeric
character references. Hand-authored GRDDL test fixtures can (and
mostly do) avoid the problem; scraped real-world pages will not.

**Discovery logic doesn't exist yet, but is F*-implementable.** Paths
(a) and (b) above are pure attribute/tree lookups over `xml_node` —
same shape as the `element_attrs`/`find_attr`/`child_elements`
accessors `Parser.RDFXML.fst` already uses. No new parser, no I/O.
This is the bulk of "new F* code" for Stage 1.

**Fetching is the real boundary crossing (rule #11).** Paths (c) and
(d), plus fetching the transformation document(s) IRI-referenced by
(a)/(b) once discovered, are network I/O and cannot live inside the
verified core. Two precedents already exist in-tree for exactly this
shape of problem — a single `assume val` "resolve this identifier to
document bytes" hook, realised per-consumer:

- `SPARQL11.Algebra.fst:2413` —
  `assume val service_endpoint_lookup : wf_iri -> option graph_store`
  for SPARQL `SERVICE`. Comment: "the OCaml side patches this to
  consult a global hashtable populated by the test runner; live HTTP
  I/O is a later phase." Realised by
  `formal/fstar/minimal_regrettable_glue_code_each_with_an_open_issue/57_service_client_bind.sh`.
- `JSONLD.Loader.fst:67` —
  `assume val jsonld_load_document : string -> option string` for
  JSON-LD's `documentLoader`. Realised by
  `.../275_jsonld_document_loader.sh`, which installs a **ref-cell +
  per-consumer registration hook**: `bin/jsonld-runner` maps the W3C
  suite's base IRI prefix to local test files on disk; `bin/
  factoidal-cli` / `-http` / `-dump-nq` default to `fun _ -> None`
  (honest failure) until a real HTTP loader is wired per-consumer.

A GRDDL transformation/namespace/profile fetch hook should follow the
same shape: one `assume val grddl_load_document : string -> option
string` (or reuse `jsonld_load_document` directly — same signature,
same "resolve an absolute IRI to document bytes" contract), a test
runner that maps the W3C GRDDL suite's local-test IRIs to
`third_party/testing/grddl/`, and every other consumer defaulting to
`None` (no live network fetch) until that's a deliberate, separately
reviewed decision. This sidesteps needing new I/O plumbing — it reuses
the existing dispatch pattern — but it does NOT remove the "any
consumer that turns this on is running arbitrary third-party XSLT"
problem (§5).

**Output syntax: RDF/XML is covered, others are not.** The spec
permits non-RDF/XML transformation output (§6, `media-type` on
`xsl:output`). We only have an RDF/XML reader
(`Parser.RDFXML.fst`) — no Turtle/N3 output handling on the GRDDL
result side (a Turtle *parser* likely exists elsewhere in the repo for
other purposes, but wiring "detect declared media type → dispatch to
the matching RDF parser" is new glue, not currently present in any
XSLT/GRDDL-adjacent module). For Stage 1, restricting to RDF/XML
output (the overwhelmingly common case, including every primer
example) is a reasonable, explicit scope cut.

**XSLT 1.0 feature coverage: real gaps for real-world GRDDL
transforms.** `XSLT.Transform.fst`'s own scope banner (lines 18-50)
lists what's supported (`xsl:template`, `xsl:apply-templates`,
`xsl:call-template`+`xsl:with-param`, `xsl:param`/`xsl:variable`
[constant `select=` or result-tree-fragment body],
`xsl:value-of`, `xsl:for-each`+`xsl:sort`, `xsl:if`,
`xsl:choose`/`when`/`otherwise`, `xsl:element`, `xsl:attribute`,
`xsl:text`, `xsl:comment`, `xsl:copy`, `xsl:copy-of`, literal result
elements with attribute-value templates) and, explicitly, what's
"deliberately OUT of scope (a mismatch here is expected, not a bug)":
**`xsl:number`, `xsl:key`/`key()`, `document()`, `xsl:import`/
`xsl:include`, `xsl:apply-imports`/`next-match`, `format-number`,
`xsl:sort` case-order/lang collations, namespace-node synthesis,
`disable-output-escaping`, positional pattern predicates (`[1]`-style
tests can be wrong), and the `processing-instruction()` node test.**
This matters concretely: several widely-cited real GRDDL
transformations lean on exactly these features —
`generate-id()`-based blank-node minting (works, it's an XPath
function, not on the excluded list, but combined patterns using
`document()` to pull in a second source or `xsl:key` to index/group
nodes do not work here), and multi-file stylesheets using
`xsl:import`/`xsl:include` to share boilerplate templates across
transforms (common in the hCard/hCalendar microformat-to-RDF
transforms referenced by the primer) fail outright. **Any given
third-party GRDDL transformation has to be checked feature-by-feature
before assuming it'll run**; this isn't a blanket "XSLT 1.0 works" —
it's "the subset of XSLT 1.0 that avoids `document()`, `xsl:key`, and
multi-file includes works."

## 3. Test suite

`https://www.w3.org/TR/grddl-tests/` is the normative test-cases
document. Manifest: "an RDF vocabulary for manifests developed for the
[RDF Test Cases] Recommendation," with a GRDDL-specific extension
vocabulary at
`http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#`
(`exercisesRule`, `alternative`, and a `NetworkedTest` class flagging
tests that require live HTTP). Manifest is published in parallel
RDF/XML and Turtle, both full and "normative-only":

- `https://www.w3.org/2001/sw/grddl-wg/td/grddl-tests.rdf` /
  `.n3` — full set.
- `https://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.rdf` /
  `-normative.n3` — normative subset.

Fetched and counted the normative Turtle manifest directly: **67
distinct test-case entries** (subjects typed `t:Test`, the rdfcore
test-schema vocabulary). First alphabetical names include `base-param`,
`card5n`/`card5na`, `four-transforms`, `glean-profile`,
`grddlProfileBase1/2/3`, `grddlonrdf`, `grddlonrdf-xmlmediatype`,
`hcard`/`hcard1`/`hcarda`, `hl7-to-owl`,
`html-and-transformation-attr` — the naming makes the discovery-path
split visible directly in the test IDs (attribute-based vs
profile-based vs namespace-based vs hCard-microformat-specific).

Rough category split, from the manifest content and the spec's own
`NetworkedTest` flag:

- **Local, no network** — `grddl:transformation` attribute tests,
  XHTML profile+link tests, RDF/XML-as-GRDDL-source tests, base-IRI
  handling. This is the achievable-now bucket: pure XML discovery +
  our XSLT engine + our RDF/XML reader.
- **`NetworkedTest`-flagged** — namespace-document and
  profile-document transformation tests (dereferencing a second URI),
  multi-profile tests, tests turning on `xml:base`/relative-URI
  edge cases against a fetched document.
- **hCard/microformat-family tests** — exercise the real hCard XSLT,
  which per §2's feature-gap analysis is exactly the kind of transform
  likely to use `xsl:key`/`generate-id()`-heavy patterns and possibly
  `document()`; needs a per-test check rather than an assumption.
  (Not confirmed line-by-line here — flagging as "check before
  counting it in the achievable bucket.")
- **Security-adjacent tests** — local-file-access and
  remote-operation attempts, meant to exercise implementation
  hardening rather than correctness.
- **Informative-only tests** — alternative output serializations
  (e.g. Turtle/N3 output), unknown media types — outside "normative"
  by the manifest's own split, and outside our RDF/XML-only Stage 1
  scope per §2.

**Realistic achievable-subset estimate for a Stage 1 (no network, no
HTML tag-soup) runner: roughly the local/non-networked, non-hCard
subset of the 67 normative tests** — a low-to-mid double-digit
fraction, not a number I'll assert precisely without running the
manifest against a real runner (per rule #25/#3, no numerator without
having actually run it). The namespace/profile-document tests and any
transform that hits an out-of-scope XSLT feature move to "needs
Stage 2/3" or "known gap," respectively — the runner should report all
three buckets (`pass`/`fail-known-gap`/`skip-network`) rather than a
single pass/fail number, matching the `pass/fail/skip/total` reporting
discipline already used by the other W3C runners in this repo (per
`docs/designissues/2026-05-07-xml-fstar-phase0-audit.md`'s harness
design and CLAUDE.md rule #25).

A `bin/grddl-runner/` following the existing runner shape is the
natural home — and there's a closer precedent than "similar in spirit"
here: `bin/xslt-runner/xslt_runner.ml` already exists, already runs
"a curated, W3C-sourced XSLT-1.0-expressible subset" through
`XSLT.Transform.transform` + `Parser.XML.parse_xml_document`
end-to-end with the file's own banner stating the I/O-glue-only
discipline (rule #11) and per-category pass/fail bucketing (rule #25).
A `grddl-runner` is structurally "`xslt-runner` plus discovery plus an
RDF/XML-vs-expected-graph diff instead of an XML-vs-expected-XML
diff" — most of the harness shape (manifest traversal via the
F*-extracted JSON/RDF parsers, output normalization, categorized
failure buckets) carries over directly. Differences: read the manifest
(itself parseable by `Parser.RDFXML.fst`/a Turtle parser since it's
plain RDF, not JSON), for each test case fetch/read the input document
(local file for offline tests, `grddl_load_document`-style lookup
table for networked ones, matching the JSONLD-runner precedent), run
discovery + transform + RDF/XML parse, and diff the resulting graph
against the expected output graph (graph-isomorphism-aware comparison
— RDFC-1.0 canonicalization already exists in-repo and is the correct
tool for this comparison, not string diff, unlike `xslt-runner`'s
XML-string comparison).

## 4. Staged implementation plan

**Stage 1 — same-document discovery over XHTML-as-XML, no network.**
New F*: a `GRDDL.Discovery.fst` (or similar) module with pure
functions over `xml_node`: `find_transformation_attr : xml_node ->
list string` (path a, reads `grddl:transformation` off the root),
`find_xhtml_transformation_links : xml_node -> list string` (path b,
walks `head/@profile` + `head`'s `link`/`a` children for
`rel="transformation"`), both resolving relative IRIs against the
document's base per the existing RFC 3986 resolution logic
`Parser.RDFXML.fst` already has (cited in
`docs/claude-rules/current-state.md` line 553, "delegate RDF/XML IRI
resolution to RFC 3986 v2" — reuse, don't reimplement). Then a
`grddl_apply : xml_node (*stylesheet*) -> xml_node (*source*) ->
option (list triple)` composing `XSLT.Transform.transform` +
`Parser.RDFXML.parse_rdfxml_strict`. Everything here composes existing
verified functions plus new pure discovery logic — no `assume val`,
no I/O. Consumer glue: `bin/grddl-runner/` (small, mirrors
`bin/jsonld-runner/`/`bin/xml-runner/` shape) to read stylesheet(s)
from local disk (allowlisted path, not fetched) and drive the
manifest. Rough size: XS-S for the F* discovery module (two small
tree-walks, maybe 100-150 lines with totality proofs), S for the
runner.

**Stage 2 — namespace-document and profile-document transforms
(needs fetch).** Adds the recursive discovery paths (c)/(d): fetch the
namespace/profile URI, parse the result (RDF, or XHTML-with-profile,
or both — the spec allows either shape), extract
`grddl:namespaceTransformation`/`grddl:profileTransformation`. New
`assume val` (or reuse of `jsonld_load_document`'s signature) per §2,
realised via the ref-cell + per-consumer-registration pattern from
issue #275, with loop detection for the recursive namespace/profile
chase (§7's own requirement) implemented as a pure F* visited-set
check over the discovery, not left to the OCaml side. Rough size: S-M
— the fetch glue reuses an existing pattern, but the recursive
discovery-with-loop-detection logic and the "is the fetched thing RDF
or XHTML" dispatch are new proof surface.

**Stage 3 — HTML tag-soup input (needs an HTML tokenizer).** Out of
scope for anything called "GRDDL work" — this is really "build an
HTML5 tokenizer in F*," a project on the scale of the XML-in-F* effort
itself (see
`docs/designissues/2026-05-07-xml-fstar-phase0-audit.md` for the size
of that effort as a comparator), that would also unlock RDFa and
microdata extraction from real-world pages, not just GRDDL. Should be
scoped and tracked as its own issue/design-doc if it's ever prioritized,
not folded into a GRDDL ticket.

## 5. Security note

GRDDL's own §8 ("Security considerations") is explicit that this is
"the execution of general-purpose programming languages as
interpreters for transformations" and "exposes serious security
risks": untrusted transformations "may access URLs which the end-user
has read or write permission" via `document()`, `doc()`,
`unparsed-text()`, `xsl:result-document`; implementors are told to
"completely disable all potentially dangerous URL operations or take
special care not to delegate any special authority to their
operation," to bound "the consumption of only a reasonable amount of
any given system resource," and to "provide appropriate mechanisms to
abort processing after a reasonable amount of time has elapsed." The
spec does not mandate a specific sandbox model — it identifies the
risk and leaves the mitigation to implementations.

For this stack specifically, two of the spec's named attack surfaces
are already structurally closed rather than merely policy-restricted:
`XSLT.Transform.fst` doesn't implement `document()` or
`xsl:result-document` at all (§2 above — "deliberately OUT of scope"),
so the classic "malicious transform reads `file:///etc/passwd` via
`document()`" attack has no code path to exploit here, full stop. What
remains open:

- **Resource exhaustion.** `XSLT.Transform.fst`'s totality proof
  bounds recursion by an explicit `fuel:nat` parameter sized from
  source+stylesheet node counts (file banner, lines 52-57): a
  self-calling template exhausts fuel and returns `[]` rather than
  diverging. That's a termination guarantee, not a *time* or
  *work* bound — a pathological but fuel-bounded transform can still
  do a lot of work before returning `[]`. A GRDDL runner should still
  wrap `transform` calls in the same wall-clock cap discipline as
  every other ad-hoc run in this repo (CLAUDE.md rule #17, `timeout
  600`).
- **Which transformations get run at all.** Stage 1 restricts the
  transformation source to a local allowlisted path (no fetch), which
  is itself the correct default posture — the spec's "disable
  dangerous URL operations" advice, taken to its logical conclusion,
  is "don't fetch and execute arbitrary third-party XSLT by default."
  Stage 2 reopens this the moment it fetches a
  namespace/profile-referenced transformation from an arbitrary IRI;
  that fetch hook should default to `None` (matches the
  `jsonld_load_document` default-`None` posture already adopted for
  every non-test-runner consumer) and any live-fetch mode should be
  opt-in, logged, and probably scoped to a per-request allowlist
  rather than "fetch whatever the document points at."

## 6. Recommendation

Stage 1 is worth doing now. All three engines it needs — XSLT 1.0,
XML, RDF/XML — already exist, verify under z3 with no `assume val` in
any of the three files, and are already extracted and reachable from
JS (`fn.xsltTransform` is already in the npm ABI and demoed live in
the hub). The only genuinely new work is two small pure tree-walks
over `xml_node` (attribute lookup, `head`/`link` scan) plus a
manifest-driven runner in the shape this repo already has three
copies of (`bin/xml-runner/`, `bin/jsonld-runner/`, the W3C RDF/XML
runner) — no new `assume val`, no network dependency, no HTML
tokenizer. The ceiling is real but bounded and stated up front: no
tag-soup HTML, no `document()`/`xsl:key`/multi-file-include
transforms, RDF/XML output only, and a "check before counting it"
caveat on the hCard-family tests specifically. That's a small,
honestly-scoped slice that extends the existing composition
(XML → XSLT → RDF/XML) one hop rather than starting a new subsystem —
the kind of win this project's own standing priorities favor over a
from-scratch feature.
