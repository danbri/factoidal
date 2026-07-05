# bin/xml-runner — W3C XML Conformance Test Suite runner

Assesses `formal/fstar/Parser.XML.fst` (generic XML → AST parser) and
`formal/fstar/XML.Wellformedness.fst` against the real W3C `xmlconf`
corpus, vendored at `third_party/testing/xml/xmlconf/` (see that
directory's `README.md` for provenance). Owner directive 2026-07-05:
"bring in XML test suite to assess our basic XML implementation."

This supersedes the bigger from-scratch rewrite sketched in
[`docs/designissues/2026-05-07-xml-fstar-phase0-audit.md`](../../docs/designissues/2026-05-07-xml-fstar-phase0-audit.md)
(`XML.Core.fst` + `Parser.XMLDoc.fst`) — that plan was never built.
`Parser.XML.fst` is the real, currently-extracted generic XML parser
(it already underlies `Parser.RDFXML` and `Parser.RIFXML`), so it is
what gets assessed here, as-is, with no F\* edits (per the task: this
is an assessment, not a fix — see "Fix candidates" below for what a
follow-up would tackle).

## Build

Standalone `mktemp`-scratch compile, same isolation pattern as
`bin/rif-runner`/`bin/vc-runner` (so this doesn't poison
`formal/fstar/ocaml-output/`'s `.cmi`/`.cmx` for a concurrent
`build-ocaml.sh` run). The dependency closure is small — just the
parser combinator base and the two modules under test, no RDF/OWL/
SPARQL modules needed:

```bash
eval $(opam env --switch=fstar)
SCRATCH=$(mktemp -d)
cp formal/fstar/ocaml-output/Parser_FastString.ml \
   formal/fstar/ocaml-output/Parser_Combinators.ml \
   formal/fstar/ocaml-output/Parser_XML.ml \
   formal/fstar/ocaml-output/XML_Wellformedness.ml \
   bin/xml-runner/xml_runner.ml "$SCRATCH"/
cd "$SCRATCH"
ocamlfind ocamlopt -package fstar.lib,zarith -linkpkg -w -8-14-26 \
  Parser_FastString.ml Parser_Combinators.ml Parser_XML.ml XML_Wellformedness.ml \
  xml_runner.ml -o xml_runner
cp xml_runner <repo>/bin/linux-x86_64/xml_runner
```

`Parser_XML.ml`/`XML_Wellformedness.ml` are already extracted and
committed in `ocaml-output/` — this runner does **not** re-extract or
touch `build-ocaml.sh`/any `.fst` file, per the task constraints.

## Run

```bash
./bin/linux-x86_64/xml_runner                    # default xmlconf dir (repo-root relative)
./bin/linux-x86_64/xml_runner <xmlconf-dir>       # explicit dir
./bin/linux-x86_64/xml_runner -v                  # print every FAIL as it runs
```

## What it does (I/O glue only — no XML logic here, rule #11)

1. Dogfoods `Parser_XML.parse_xml_document` on the master manifest
   `xmlconf.xml` itself. This **always returns `None`**:
   `Parser.XML.fst` has no `<!DOCTYPE ...>` production at all (its
   `skip_misc` only skips whitespace/comments), and `xmlconf.xml`
   opens with exactly such a DOCTYPE (declaring one entity per
   sub-manifest file). The runner reports this honestly, then falls
   back to a targeted textual scan for `<!ENTITY name SYSTEM "path">`
   declarations — file-path discovery, not an XML/DTD parser.
2. Each of the 21 discovered **leaf** manifest files parses cleanly
   via the real extracted parser (none carry a DOCTYPE) — except
   three (`sun/sun-valid.xml`, `sun/sun-invalid.xml`,
   `sun/sun-not-wf.xml`) which are bare, unwrapped sibling `<TEST>`
   lists with no single root element at all (only well-formed in the
   entity-inclusion context they were written for — confirmed
   independently: Python's `xml.etree.ElementTree` also rejects them
   standalone). `Parser.XML.fst` has no "reject trailing content
   after the root" check, so it silently parses only the *first*
   `<TEST>` and stops, which would silently drop 27/73/55 tests from
   those three files — a real bug caught while building this runner.
   Fix: every leaf manifest's post-prolog body is wrapped in a
   synthetic `<TESTCASES>...</TESTCASES>` before the dogfood parse
   (harmless for files that already have their own TESTCASES root,
   since TESTCASES-in-TESTCASES nests fine and the walker already
   recurses). This wrapping is manifest bookkeeping only — the actual
   conformance test **input** documents are always parsed raw.
3. Every `<TEST>` element is walked out of the parsed AST via
   `Parser_XML.element_tag`/`element_attrs`/`element_children`/
   `find_attr`/`text_content` (genuinely dogfooded, not regexed).
4. Each test's input file is read and classified — see "Scoring
   semantics" in `xml_runner.ml`'s header comment for the full
   pass/fail/skip decision tree (mirrors the owner's spec verbatim,
   citing `testcases.dtd`'s own stated exemptions for non-validating,
   non-external-entity-reading processors).
5. `XML_Wellformedness.is_valid_ncname` is called informationally
   only, on every accepted document's element tags — its NCName
   production explicitly excludes `:` from Name-start/continue
   characters (an RDF/XML-domain rule), so applying it as a generic
   XML well-formedness gate would wrongly reject plain XML 1.0
   documents that legally use `:` in Names outside a
   Namespaces-aware reading (several `xmltest/` cases do this on
   purpose). This finding — that the wellformedness module doesn't
   generically apply to plain XML conformance — is one of this
   assessment's results, not a runner bug.

## Score (2026-07-05, wave 1 — full run, log at `.claude-runs/xml-runner-2026-07-05.log`)

**1358 pass, 84 fail, 1143 skip (of 2585 discovered `<TEST>` entries).**

Per TYPE bucket:
- `valid` (labelled "wf-accept" per the task — a clean parse only
  exercises well-formedness, not DTD validity): **0 pass, 0 fail, 812
  skip (of 812)**. Every `valid` test in this suite carries a
  DOCTYPE — expected, since validity is *defined* relative to a DTD —
  so this entire bucket reduces to `Skip "DOCTYPE/DTD not parsed"`. No
  bug: this project's parser has zero DTD support, so the suite's
  entire "does it correctly ACCEPT a well-formed, DTD-bearing
  document" axis is untestable here.
- `invalid`/`error`: **0/0, 242 + 33 = 275 skip**, always
  `Skip "no DTD validation (by design)"` per the task's own rule.
- `not-wf`: **1358 pass, 84 fail, 56 skip (of 1498)**. 1165 of the
  1358 passes are flagged "vacuous" (the document also carries a
  DOCTYPE our parser can never get past, so the reject is
  structurally guaranteed rather than necessarily catching the
  documented violation) — see the tagged summary line in the log.
  The 56 skips are the `ENTITIES != "none"` exemption
  (`testcases.dtd`: "No parser should accept a 'not-wf' testcase
  unless it's a nonvalidating parser and the test contains external
  entities that the parser doesn't read").

Per collection: `jclark` 154/43/168 (365), `sun` 50/1/108 (159),
`ibm` 873/1/262 (1136), `oasis` 194/22/132 (348), `eduni` 87/17/461
(565), `japanese` 0/0/12 (12, all skip — non-UTF-8 Japanese
encodings).

## Fail cluster table (84 total across 30 SECTIONS-keyed clusters — see the log for the full table with example IDs)

The runner's own output groups strictly by `(TYPE, SECTIONS)`; the
table below additionally merges clusters that are clearly the same
underlying construct cited under adjacent SECTIONS numbers (e.g.
`2.5 [15]` + `2.5 [16]`, both "comment must not contain `--`"),
verified to sum to exactly 84 across all 30 raw clusters:

| Construct | Count | Raw SECTIONS clusters | Note |
|---|---|---|---|
| Non-character codepoints accepted (raw content and `&#x...;`/`&#...;` char-refs) | 19 | `2.2[2]`(12), `4.1[66]`(7) | Neither the text-content walk nor `parse_reference`'s digit-to-codepoint conversion checks the result against the XML `Char` production's exclusions (e.g. `U+FFFF`) |
| XML declaration grammar (attribute ordering/repetition, required parts, value casing/charset, encoding-name lexical rules) | 18 | `2.8[23]`(6), `2.8[22]`(3), `2.8[26]`(3), `2.9[32]`(2), `4.3.3[81]`(2), `2.8[24]`(1), `3.1[43]`(1) | `parse_xml_declaration` reuses the generic `parse_attributes` list parser for `version`/`encoding`/`standalone` — no positional grammar (`VersionInfo EncodingDecl? SDDecl?`), no per-attribute value lexical grammar (`VersionNum`, `EncName`, `yes\|no`) |
| Namespace-spec violations (`xmlns`/`xml` (un)binding, reserved-prefix rules, bad QName colon placement, attribute uniqueness across prefixes) | 17 | `SECTIONS 3`(5), `NE05`(5), `SECTIONS 2`(2), `SECTIONS 4`(2), `5.3`(2), `SECTIONS 5`(1) | `Parser.XML.fst` has zero Namespaces-in-XML awareness — **expected**, not a defect in scope: namespace resolution deliberately lives in `Parser.RDFXML`, per the phase-0 audit's own conclusion |
| Content/declarations after the document element accepted (junk epilog, second root, stray CDATA/XML-decl after `</root>`) | 11 | `2.8[27]`(8), `2.1[1]`(2), `SECTIONS 2.1`(1) | `parse_xml_document` ignores everything after the first root element — no "epilog is only S/Comment/PI" check (a known gap, already noted in the phase-0 audit) |
| Comment body containing `--` or ending in `-` accepted | 5 | `2.5[15]`(3), `2.5[16]`(2) | `parse_comment_body` only watches for the closing `-->`, never rejects an internal `--` |
| `]]>` literal sequence in text content accepted | 4 | `2.4[14]`(4) | `parse_text_content` only stops at `<`/`&`, never scans for a literal `]]>` |
| Attribute-value/uniqueness violations accepted (literal `<` in a value, duplicate attribute name) | 4 | `2.3[10]`(2), `SECTIONS 3.1`(1), `3.1[44]`(1) | `parse_attr_value_body` doesn't exclude literal `<`; `parse_attributes` doesn't check for a repeated `attr_name` |
| PI-vs-declaration target-name case confusion (`<?xmL`, `<?xMl`) accepted | 3 | `2.6[16]`(1), `2.6[17]`(1), `2.8+2.6[23,17]`(1) | `parse_xml_pi`'s target-name check (or lack of it) doesn't special-case the reserved, case-insensitive `xml` target name |
| Misc singles: `Name` starting with an Extender, nested `CDATA` sections, malformed end-tag syntax | 3 | `2.3[5]`(1), `2.7[18]`(1), `3.1[42]`(1) | Each a distinct, narrow lexical-grammar gap — see the log for the exact test |

Ordered by cluster size for follow-up prioritization (not fixed here,
per the task): (1) non-character codepoint rejection (19 — a single
shared `is_valid_xml_char` predicate, applied at both the raw-content
and char-ref-decode sites, would close this whole cluster at once),
(2) XML declaration grammar (18 — needs a dedicated ordered-attribute
grammar plus per-attribute value lexers, replacing the generic
`parse_attributes` reuse), (3) namespace-spec awareness (17, but
arguably **out of scope** for `Parser.XML.fst` per the phase-0 audit —
would belong in a namespace layer, likely `Parser.RDFXML`'s domain),
(4) epilog/trailing-content rejection (11 — one check: after parsing
the root, verify only `S`/`Comment`/PI remains), (5) comment `--` and
`]]>`-in-text rejection (9 combined, two small added scans), (6)
attribute-value/uniqueness checks (4), (7) PI/declaration target-name
casing (3), (8) the 3 remaining singleton gaps.

## Known imprecision in this harness (disclosed, not fixed)

The encoding-skip heuristic (`encoding_skip_reason` in
`xml_runner.ml`) treats "declared `encoding=` value is outside
{utf-8, ascii, us-ascii}" as "SKIP — can't decode these bytes." For a
handful of `not-wf` tests (`sun/not-wf/encoding04.xml`
`ibm/not-wf/P81/ibm81n05..09.xml`) the document's actual bytes ARE
plain ASCII and the test's real point is that the encoding-name
*token itself* contains illegal characters (`utf:8`, `UTF~8`, …) —
conflating "unsupported byte encoding" with "syntactically invalid
encoding name" converts a handful of testable not-wf cases into
over-conservative skips. Two of the closely related cases
(`sun/not-wf/encoding01.xml`'s leading-space and jclark's
`not-wf-sa-101`) DID make it through to a real, correctly-diagnosed
FAIL, because `String.trim`-ing the declared value before the
supported-encodings check happened to preserve testability for that
specific sub-case. Not fixed here (assessment task); a fix would
separate "BOM/declared encoding requires a real decoder we don't
have" from "the encoding NAME's own character content is
syntactically invalid," parsing the latter with the real engine
either way.

## Cross-references

- Test corpus + provenance: `third_party/testing/xml/README.md`
- `formal/fstar/Parser.XML.fst`, `formal/fstar/XML.Wellformedness.fst`
- Pattern reference: `bin/rif-runner/README.md`, `bin/vc-runner/vc_runner.ml`
- `skills/test-suites/SKILL.md` — suite table entry
