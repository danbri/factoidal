# 2026-05-07 — XML in F* — Phase 0 audit + scaffold plan

## Status

Phase 0 of issue [#185](https://github.com/danbri/factoidal/issues/185)
("spec: implement XML in F* (intent — stretch goal)"). This document
audits the existing F* XML surface, makes the extend-vs-build-alongside
decision, assesses the EverParse fit, and lays out the W3C test corpus
vendoring plus failure-tolerant runner design. No F* code edits in this
phase. The runner skeleton lands as `bin/xml-runner/` per CLAUDE.md
rule #11 (consumer relocation).

## Existing surface

### Parser.XML.fst

`formal/fstar/Parser.XML.fst`, 680 lines, 43 top-level definitions, zero
`assume val`s, builds on `Parser.Combinators` and `Parser.FastString`.
Verifies under z3 4.13.3 with no `--lax` (it's part of the current
build).

What it covers:

- AST: `xml_attribute`, `xml_node` with four constructors —
  `XText`, `XElement`, `XComment`, `XCDATA`. Note: no `XPI`
  (processing instruction) and no `XDoctype` constructor; PIs are
  parsed-and-skipped, DOCTYPEs aren't recognised at all.
- Name characters: ASCII fast-path plus a coarse non-ASCII rule
  (`code >= 0xC0`). This is **not** the XML 1.0 4th-Edition
  NameStartChar table; it accepts characters the spec rejects and
  vice versa. Adequate for ASCII-only RDF/XML in practice;
  insufficient for W3C conformance.
- Tokens: `parse_xml_name`, `parse_attr_value`,
  `parse_xml_attribute`, `parse_attributes`. Both quote styles
  (`"` and `'`) accepted. Whitespace handling matches XML S
  (space, tab, CR, LF).
- Entity / character references (`parse_reference`):
  - The five predefined entities `&amp; &lt; &gt; &quot; &apos;`.
  - Decimal and hex character references with full UTF-8 byte
    output via `codepoint_to_string` (handles 1/2/3/4-byte UTF-8).
  - **No DTD-defined entity references.** A document declaring
    `<!ENTITY foo "bar">` and using `&foo;` will fail with
    `unknown entity reference`.
- Comment parsing (`<!-- ... -->`) and CDATA section parsing
  (`<![CDATA[...]]>`).
- Processing instructions: `parse_xml_pi` skips `<? ... ?>` payloads
  in content and (separately) `<?xml ... ?>` declarations are parsed
  by `parse_xml_declaration` for their attributes (version, encoding,
  standalone). The PI target name is not validated.
- Element parsing (`parse_xml_element` / `parse_children`,
  fuel-based): self-closing (`<tag/>`), open/close pairs with
  matching tag-name check, nested children including comments,
  CDATA, and PIs in content position.
- Document entry point (`parse_xml_document`): optional whitespace,
  optional `<?xml ... ?>` declaration, prolog comments via
  `skip_misc`, then exactly one root element. The epilog (any
  trailing comments / PIs / whitespace after the root) is **not**
  consumed; the parser returns the root and ignores trailing input.
- Convenience accessors: `element_tag`, `element_attrs`,
  `element_children`, `find_attr`, `text_content`,
  `child_element`, `child_elements`, `all_child_elements`.

What it punts:

- **Namespaces.** Element / attribute names are stored as raw
  `string`s. `xmlns` and `xmlns:prefix` declarations are stored as
  ordinary attributes; QName resolution is the consumer's problem.
  `Parser.RDFXML` rolls its own `extract_namespaces`,
  `split_qname`, `lookup_ns`, `resolve_qname` (20 references
  total) — that logic belongs in an XML-namespace layer.
- **DOCTYPE / DTDs.** No `<!DOCTYPE ...>` recognition. A document
  with an internal subset will fail at the `<!` after the prolog.
- **Custom entity definitions.** As a consequence of no DTD
  parsing, only the five predefined entity names resolve.
- **Parameter entities** (`%name;`) — entirely outside the AST.
- **XML 1.1.** Character class heuristic is XML-1.0-ish; XML 1.1's
  expanded NameStartChar / NameChar tables and the restricted-char
  rules aren't modelled. Defer 1.1 until 1.0 is conformant
  (matches the issue #185 plan).
- **Encoding declaration enforcement.** The `encoding="..."`
  attribute on the XML declaration is stored but not honoured —
  the parser assumes the input string is already a sequence of
  Unicode codepoints (concretely: bytes interpreted as ASCII /
  Latin-1 by `Parser.FastString`'s byte indexing).
- **Epilog consumption.** Trailing `<?xml-stylesheet?>` PIs or
  comments after the root are silently dropped (parser returns
  early on `parse_xml_element` success).
- **Well-formedness as a refinement.** `xml_node` has no refinement
  tying construction to "is well-formed XML". The parser's success
  is the only well-formedness witness; there's no `is_well_formed`
  predicate or lemma (the strawdraft in #185 sketches one but it
  doesn't exist yet).
- **Round-trip lemma.** No `parse (serialize x) == Some x` lemma
  pair. Parser.RDFXML has its own `serialize_xml_node` /
  `serialize_xml_node_c14n` for canonicalising rdf:parseType=Literal
  payloads; a generalised serializer + roundtrip lemma belongs in
  the core, not in the consumer.

What's marked TODO / partial / `assume val`:

- Zero `assume val`s — the file is currently entirely defined.
- No inline `TODO` / `FIXME` / `XXX` markers.
- Implicit gaps documented above (no inline marker means the
  audit doc is the only record).

### Parser.RDFXML.fst (consumer)

`formal/fstar/Parser.RDFXML.fst`, 1133 lines. The only in-tree
consumer of `Parser.XML` today.

Parser.XML entry points it uses:

- `parse_xml_document` — top-level entry from
  `parse_rdfxml` / `parse_rdfxml_to_graph`.
- The `xml_node` AST (`XElement`, `XText`, `XCDATA`, `XComment`)
  — pattern-matched throughout the RDF graph builder
  (`process_node_element`, `process_property_element`,
  `process_property_children`, `serialize_xml_node`,
  `serialize_xml_node_c14n`, `collect_text`, `is_all_text`).
- Attribute helpers: `find_attr`, `element_attrs`,
  `element_children`.

Workarounds for Parser.XML gaps:

- **Namespace resolution lives in Parser.RDFXML, not Parser.XML.**
  Parser.RDFXML defines and threads:
  - `extract_namespaces : list xml_attribute -> list (string * string) -> list (string * string)`
  - `split_qname : string -> string * string`
  - `lookup_ns : string -> list (string * string) -> option string`
  - `resolve_qname : rdfxml_state -> string -> option string`
  - 20+ call sites across element / attribute processing.
- **xml:base and xml:lang inheritance** are managed by
  `update_state_from_attrs` because the XML core doesn't carry
  inherited attributes through the tree.
- **C14N-style XML serialization** for `rdf:parseType="Literal"`
  is reimplemented in Parser.RDFXML
  (`serialize_xml_node_c14n` ≈ 50 lines) because the core has no
  serialiser.

These workarounds are the strongest argument for an XML core
that owns namespaces + serialisation: every future XML consumer
(RSS, Atom, Sitemap, RIF-XML) would otherwise reimplement the
same four functions and the same C14N-ish serialiser.

## Decision: extend or build alongside

**Recommendation: (B) build alongside, then migrate Parser.RDFXML in a
follow-up PR.**

Concrete shape:

- `formal/fstar/XML.Core.fst` — refined AST: namespace-aware
  `qname` type, `xml_node` with `XPI` and `XDoctype` constructors
  (DOCTYPE recognised even when not interpreted), `is_well_formed`
  refinement (predicate now, lemma-carrying type later).
- `formal/fstar/Parser.XMLDoc.fst` — document-level parser layered
  on `Parser.Combinators`, producing `XML.Core` trees. Includes:
  - Namespace binding stack threaded through element parsing.
  - DTD recognition (skip-and-store, not full interpretation; full
    DTD evaluation is its own deferred phase).
  - Epilog consumption.
  - Encoding-declaration sanity check (UTF-8 / US-ASCII only;
    other declared encodings → parse error, since we can't
    transcode without an external decoder).
  - Round-trip-friendly serialiser (`serialize_xml_doc`) with the
    parse/serialise lemma deferred to Phase 2 once the AST is
    stable.
- `formal/fstar/XML.Namespaces.fst` — pure namespace-resolution
  layer (`qname`, prefix → URI environment, default-namespace
  rules, attribute-namespace special case where unprefixed
  attributes have no namespace per Namespaces in XML 1.0 §6.2).

Migration:

1. Phase 1 (this rollout) lands `XML.Core.fst` + `Parser.XMLDoc.fst`
   alongside the existing files; no consumer changes.
2. Phase 3 re-roots `Parser.RDFXML` on the new core in a single PR.
   The diff is large (1133 lines touched) but mechanical; the
   four namespace helpers in `Parser.RDFXML` get deleted and
   their call sites switch to `XML.Namespaces` equivalents. RDF/XML
   W3C pass rate must not regress.
3. Once Parser.RDFXML is migrated, `Parser.XML.fst` becomes an
   orphan and can be removed (or kept as a thin compatibility
   shim if other private consumers surface in the audit).

Why **build alongside** rather than **extend in place**:

- The existing `xml_node` constructor set is too narrow. Adding
  `XPI` and `XDoctype` is a breaking change to every pattern match
  in `Parser.RDFXML`. Doing that breakage *and* adding namespace
  awareness *and* changing the document entry point in one PR is
  large and high-risk. A separate core lets us land the new types
  + parser with verification first, then migrate the consumer
  with a focused PR.
- The new core is intended to grow into the **shared backbone**
  for RSS, Atom, Sitemap XML, and RIF-XML (per issue #185). Those
  formats need namespace-aware QNames as a first-class type, not as
  a string with manual splitting. Designing for that from day one
  is cleaner than retrofitting `Parser.XML.fst` and propagating
  the change.
- Cost of duplication during migration is one extra `.fst` file in
  the tree for the duration of one PR (Phase 1 → Phase 3). That's
  acceptable.

The cons are real but bounded: zero migration cost only happens for
trivial extensions; we already need to add four major capabilities
(namespaces, DOCTYPE, epilog, serialise+roundtrip), at which point
"extend in place" is no longer a small change.

## EverParse fit assessment

EverParse / LowParse / 3D is purpose-built for **binary** formats with
fixed-width fields, length-prefixed buffers, and tag-driven case
selection (TLS, CBOR, Bitcoin blocks, network packets). XML is a
text-based recursive grammar with:

- Variable-length tokens delimited by structural characters
  (`<`, `>`, `&`, `;`, quote chars).
- A nested grammar rather than a flat record / TLV layout.
- Character-encoding-aware lexing (UTF-8 / UTF-16, BOMs).
- DTD and entity references that introduce a second parse pass.
- Whitespace preservation rules that depend on context (CDATA vs
  text vs attribute value).

Investigation of upstream:

- **No EverParse / LowParse / 3D XML parser exists.** Searched the
  Project Everest repo (`project-everest/everparse`,
  `src/lowparse/`, `src/3d/`, `src/qd/`, `src/cbor/`, `src/cddl/`,
  `src/cose/`, `src/ASN1/`) and the format coverage table in the
  PulseParse 2025 paper. Coverage to date: TLS 1.0–1.3, Bitcoin,
  ASN.1 DER PKCS#1, QUIC, Hyper-V network virtualization,
  CBOR / CDDL / COSE, DICE Protection Environment. Nothing
  text-based; nothing recursive in the way XML is.
- **No academic or community F\* XML parser.** The F\* community
  parser corpus (low-level networking + cryptographic protocol
  formats) doesn't include XML.
- LowParse combinators model "byte stream → typed value" with
  validators and serialisers. The combinators handle fixed-width
  ints, length-prefixed buffers, sums, and tagged unions. They
  don't have native support for:
  - Recursive grammars (3D's recursion via `casetype` is
    constrained; XML's "element contains arbitrary mix of
    elements / text / comments / CDATA" is more open).
  - Lookahead beyond the immediate next byte — XML needs lookahead
    for `<!--` vs `<![CDATA[` vs `<!DOCTYPE` vs `<!ENTITY` etc.
  - Backtracking-free disambiguation across the four `<!`-prefixed
    constructs without an explicit tag byte.

**Recommendation: roll our own using the existing `Parser.Combinators.fst`.**

Justification:

- The XML 1.0 token grammar fits the existing combinator model
  (the current `Parser.XML.fst` is the proof-of-concept). What's
  missing is documented above (namespaces, DOCTYPE recognition,
  epilog, serialise+roundtrip, refinement) and is incremental work
  on the same combinator base, not a paradigm shift.
- Adopting EverParse for XML would require either:
  - Vendoring EverParse and contributing an XML format definition
    upstream — months of work for a format outside their declared
    coverage.
  - Or building a one-off LowParse-on-top-of-text shim that pays
    EverParse's dependency cost without using the combinators it
    was designed for.
- Both options are worse than extending `Parser.Combinators` in
  the directions XML needs (namespaced tokens, lookahead, parse
  state for namespace bindings).
- EverParse remains the right answer for **binary** companion-file
  formats per
  [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md)
  (round-trip witness pattern, future SPARQL Protocol over the
  wire). XML is not where it earns its keep.

This decision is consistent with the existing EverParse research
notes in [`docs/designissues/everparse.md`](everparse.md) and the
[`2026-04-25-tav4-everparse-research-scratch.md`](2026-04-25-tav4-everparse-research-scratch.md)
scratch — both call EverParse a binary-format tool.

If, during Phase 2, the pure-F\* combinator route hits a verification
wall (e.g. termination proofs become unwieldy for the recursive
content model), reopen the EverParse question. Until then, no
vendoring; no `formal/third_party/everparse/` directory.

## Test corpus vendoring

W3C XML Test Suite — the comprehensive conformance corpus. Two URLs
are relevant; both should be checked at vendoring time.

- Project page: <https://www.w3.org/XML/Test/>
- Latest release archive: <https://www.w3.org/XML/Test/xmlts20130923.tar.gz>
  (most recent W3C-hosted snapshot at time of writing; verify
  against the project page when vendoring).
- License: W3C document license; permits redistribution with
  attribution and the W3C notice intact. Compatible with the
  factoidal repo.

The suite contains:

- `xmltest/` — James Clark's original conformance suite
  (well-formedness, validity).
- `japanese/` — Fuji Xerox tests for Japanese-language XML.
- `sun/` — Sun Microsystems' tests.
- `oasis/` — OASIS conformance tests.
- `eduni/` — University of Edinburgh tests (XML 1.0 4th edition,
  XML 1.1, namespaces).
- `ibm/` — IBM tests covering 1.0 and 1.1.

Manifest: each subsuite has its own `xmlconf.xml` (or similarly
named) describing each test as a `TEST` element with attributes
including `TYPE` (`valid` / `not-wf` / `invalid` / `error`),
`URI`, `ID`, optionally `ENTITIES` and `OUTPUT`. The top-level
`xmlconf.xml` aggregates them. Reading the manifest is itself an
XML parsing task — chicken-and-egg solved by either:

(a) Bootstrapping the harness with the existing `Parser.XML.fst`,
which is sufficient to read the manifest (it's plain ASCII XML
with no DTDs; the bits the current parser punts don't appear
in the manifest itself).

(b) Hand-converting the manifest to a CSV in a one-time prep
script, committed alongside the harness.

Recommendation: (a). The existing parser handles the manifest;
no extra tooling needed.

Vendoring plan:

```bash
# Phase 0 (this PR): NO vendoring. Plan only.
# Phase 1 (next PR):
mkdir -p third_party/testing/xml
cd third_party/testing
git submodule add https://github.com/w3c/xml-conformance-tests.git xml
# OR — if W3C-hosted tarball is preferred:
curl -O https://www.w3.org/XML/Test/xmlts20130923.tar.gz
tar -xzf xmlts20130923.tar.gz -C xml/ --strip-components=1
# Plus a VERSION file pinning the snapshot date and source URL.
```

Submodule vs tarball — pick at vendoring time based on which has
a stable upstream. The submodule path is preferred (matches
existing `third_party/testing/` patterns); the tarball is a
fallback if no canonical Git mirror exists.

## Failure-tolerant harness — what it looks like

Per anti-pattern #25 (no cryptic score strings; never report
"972/59" without labels), the runner's output uses
`pass / fail / skip / total` for every category. Format spec:

```
=== W3C XML Test Suite ===
Test base: third_party/testing/xml/

Suite Results:
  xmltest/valid                   pass:N1   fail:F1   skip:S1   (out of T1)
  xmltest/not-wf                  pass:N2   fail:F2   skip:S2   (out of T2)
  xmltest/invalid                 pass:N3   fail:F3   skip:S3   (out of T3)
  japanese                        pass:N4   fail:F4   skip:S4   (out of T4)
  sun/valid                       pass:N5   fail:F5   skip:S5   (out of T5)
  sun/not-wf                      pass:N6   fail:F6   skip:S6   (out of T6)
  oasis                           pass:N7   fail:F7   skip:S7   (out of T7)
  eduni/xml-1.0-4e                pass:N8   fail:F8   skip:S8   (out of T8)
  eduni/namespaces-1.0            pass:N9   fail:F9   skip:S9   (out of T9)
  eduni/xml-1.1                   pass:N10  fail:F10  skip:S10  (out of T10) [unsupported]
  eduni/namespaces-1.1            pass:N11  fail:F11  skip:S11  (out of T11) [unsupported]
  ibm/valid                       pass:N12  fail:F12  skip:S12  (out of T12)
  ibm/not-wf                      pass:N13  fail:F13  skip:S13  (out of T13)
  ibm/invalid                     pass:N14  fail:F14  skip:S14  (out of T14)

TOTAL: N pass, F fail, S skip, U unsupported (out of T)
```

Categories:

- **pass** — manifest's expected verdict matches our parser's
  verdict. For `valid` / `not-wf` / `invalid` tests, the verdicts
  are `well-formed` / `not-well-formed` / `well-formed-but-invalid`.
- **fail** — verdict mismatch. The harness logs the test ID and a
  one-line diagnostic to a per-suite log file.
- **skip** — test deliberately excluded, either because the test
  exercises a feature we've explicitly deferred (DTD validation,
  XML 1.1) or because the manifest entry references an external
  resource that's not vendored. Exclusion list lives in a
  `bin/xml-runner/exclusions.txt` style file with a one-line
  reason per test ID, so a reviewer can audit what was hidden.
- **unsupported** — the entire subsuite is not yet attempted (e.g.
  XML 1.1 in Phase 2 / 3). Counts toward total but doesn't run.

CLI shape:

```
xml-runner --suite=all                # run everything
xml-runner --suite=xmltest            # one subsuite
xml-runner --list                     # enumerate subsuites
xml-runner --verbose                  # log every fail to stderr
xml-runner --json                     # machine-readable for the dashboard
```

Initially we expect: small `pass`, large `fail`, with `fail`
dominated by DTD-using tests (current parser doesn't recognise
DOCTYPE) and namespace-using tests (current parser doesn't carry
namespace state). That's the **honest baseline** that lets us
measure progress through Phases 2–3.

Per CLAUDE.md rule #11 the runner is a consumer, not part of the
verified library — it lives in `bin/xml-runner/` and is allowed to
contain hand-written OCaml (`xml_runner.ml`) once the F\* core
exposes a callable entry point in Phase 1.

## Sequenced rollout

| Phase | Deliverable | Effort |
|---|---|---|
| 0 | This audit + scaffold (this PR) | XS |
| 1 | `XML.Core.fst` + `XML.Namespaces.fst` + `Parser.XMLDoc.fst` skeletons (no DTDs yet); W3C suite vendored; `bin/xml-runner/xml_runner.ml` reading the manifest and reporting honest pass/fail/skip/total | S–M |
| 2 | XML 1.0 + namespaces parser passing the W3C XML core conformance subset (`xmltest/`, `japanese/`, `sun/`, `oasis/`, `eduni/xml-1.0-4e`, `eduni/namespaces-1.0`, `ibm/` 1.0 subset). DOCTYPE recognised but not interpreted | M |
| 3 | Re-root `Parser.RDFXML` on the new core; no regression in RDF/XML W3C pass rate. Delete the four namespace helpers from `Parser.RDFXML`. Keep `Parser.XML.fst` only if a non-RDFXML consumer surfaces in the audit | S–M |
| 4 | Migrate RSS / Atom / Sitemap XML / RIF-XML consumers onto the core. One PR each | S each |
| 5 | Surface dashboard panel; honest `pass / fail / skip / total` numbers per anti-pattern #25 | XS |

## Done criteria

(Restated from issue [#185](https://github.com/danbri/factoidal/issues/185).)

- W3C XML Test Suite vendored under `third_party/testing/xml/` with
  upstream pin in `third_party/testing/xml/VERSION` and the W3C
  notice intact in `third_party/testing/xml/LICENSE`.
- F\* XML core verifies under z3 4.13.3 with no `--lax` and no
  `--admit_smt_queries`.
- All RSS / Atom / Sitemap XML / RIF-XML / RDF/XML parsers consume
  the same XML core. No private re-implementations of namespace
  resolution or QName splitting.
- Dashboard panel reports `pass / fail / skip / total` with
  per-subsuite breakdown.
- Per CLAUDE.md rule #4 (parsers belong in F\*), no host XML
  library is allowed inside the verified core. Boundary call-outs
  (e.g. for streaming over very large documents) tagged per the
  I/O verification annex.

## Open questions

1. **DTD scope for Phase 2.** Recognise-and-skip is enough for
   well-formedness checks on documents that *have* a DOCTYPE. Full
   DTD evaluation (entity definitions, default attribute values,
   element content models, `xml:id` validation) is a separate
   project. Where do we draw the line for Phase 2?

2. **XML 1.1 deferral horizon.** The `eduni/xml-1.1` and
   `eduni/namespaces-1.1` subsuites will report `unsupported` at
   the start. Do we commit to a Phase number for adding 1.1, or
   leave it open-ended until a consumer (RIF? XSLT 2?) demands it?

3. **Encoding declaration handling.** The Phase 1 plan rejects
   non-UTF-8 / non-US-ASCII declared encodings rather than
   transcoding. Real-world XML uses UTF-16 and ISO-8859-1
   (especially older RSS feeds). Do we ship a transcoder
   in F\* (months of work), use a host call-out
   (`assume val transcode : declared:string -> bytes:list u8 -> ML (list u8)`,
   per rule #11(a)), or stay UTF-8-only and document the limitation?

4. **`XPI` and `XDoctype` constructor adoption.** Adding two
   constructors to the AST in `XML.Core` means RDF/XML's
   `serialize_xml_node` (used for `rdf:parseType="Literal"` C14N)
   needs cases for both. Are the C14N rules for those constructors
   correctly: PI → output as-is; Doctype → drop (not part of
   parseType="Literal" content)? Worth checking against the
   RDF/XML test suite expected output before committing.

5. **Round-trip lemma scope.** Phase 1 ships parser + serialiser;
   Phase 2 should add `parse (serialize x) == Some x` for
   well-formed `x`. Is that enough, or do we also need the harder
   direction (`serialize ∘ parse` is idempotent on the subset of
   strings that successfully parse)? The harder direction is
   what canonicalisation needs — a downstream concern but worth
   flagging.

6. **Submodule vs tarball for the test corpus.** The W3C-hosted
   tarball is the canonical artefact; the `w3c/xml-conformance-tests`
   GitHub mirror is a third-party convenience. Phase 1's vendoring
   PR has to pick one. Stability of the upstream URL across years
   is the deciding factor — needs a check at vendoring time.
