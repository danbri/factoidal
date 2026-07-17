# XML conformance skip census — categories, conformance-class framing, implementation order

Status: skip census + triage. Written 2026-07-17 per owner directive
("crank toward 100% — xml named explicitly"). Supersedes the one-line
dashboard summary previously carried in the ledger's `xml_conformance`
row.

Score at write time: **1428 pass, 0 fail, 1157 skip (out of 2585)** —
up from 1414/0/1171 (see "What got implemented this pass" below).
`bin/xml-runner/xml_runner.ml` / `bin/linux-x86_64/xml_runner`;
`formal/fstar/Parser.XML.fst` + `XML.Wellformedness.fst` +
`XML.Namespaces.fst` under test, **unchanged this pass** — everything
below is triage against the parser as it exists, not a proposal to
change it here. A concurrent agent is working DTD-ID inside
`Parser.XML.fst`; this pass deliberately avoided that module's core
accepting paths.

## Conformance class we should claim

XML 1.0 §5.1 ("Validating and Non-Validating Processors") names two
processor classes. A **validating processor** MUST enforce every
Validity Constraint (VC) in the DTD — content models, `ATTLIST`
defaulting/enforcement, ID/IDREF uniqueness, NOTATION cross-references.
A **non-validating processor** is required only to enforce
Well-Formedness Constraints (WFCs) — it MAY use DTD information but is
not required to validate against it. `xmlconf`'s own
`testcases.dtd` goes further and names a *sub*-class within
non-validating: a processor that additionally does not read external
general/parameter entities, with its own `ENTITIES` attribute
exemption for exactly that case.

**Factoidal's `Parser.XML.fst` is, and should keep claiming to be, a
non-validating, non-external-entity-reading XML 1.0 well-formedness
processor.** That is not a euphemism for "incomplete" — it is a
conformance class the XML Recommendation itself defines and the test
suite itself scores against (`TYPE="invalid"`/`"error"` and the
`ENTITIES` attribute exist precisely so a corpus consumer can tell
which tests apply to which processor class). Under that claim, two of
the skip buckets below (275 `invalid`/`error` + 57 external-entity
exemption = **332 of 1157, ~29%**) are **not applicable**, not
missing — they test a different processor class. The remaining 825
skips are real, closeable gaps against the claimed class, with one
narrower profile choice inside that count (XML 1.1, 33 tests) worth a
separate owner call before investing there.

This reclassification changes how the score should be *read*, not the
number: 1157 skips out of 2585 stays the accurate figure, but 332 of
those are inapplicable-by-class rather than un-implemented-by-effort.
The dashboard/ledger should carry both the raw count and this class
note side by side — a bare "1157 skipped" without it reads as
uniformly missing coverage, when the honest picture is "well-formedness-
only processor by design, ~825 in-scope gaps remaining, frontloaded by
one family (Name-character-class errata, 305 tests) that is a
Unicode-range table edit, not new grammar."

## Category table (1157 skips, post-fix; see "implemented this pass" below)

| Category | Count | By-design or gap | F\* effort | What it would unlock |
|---|---|---|---|---|
| `invalid`/`error` TYPE (DTD validity: content models, ATTLIST enforcement, ID/IDREF, NOTATION) | 275 | **By-design** — VCs are validating-processor-only per XML 1.0 §5.1; we claim non-validating | L (a real validating XML processor — a different project) | Nothing we've committed to; would need an explicit owner decision to add a validating conformance class |
| External-entity exemption (`ENTITIES` = parameter/both/general ≠ none) | 57 | **By-design** — `testcases.dtd`'s own exemption for a non-external-entity-reading processor | L (external DTD subset + external general/parameter entity fetch — even file-local, a real I/O + resolution feature) | Nothing required by the claimed class; would only matter if the class claim changes |
| `not-wf` DTD-internal-subset WFC-shape gap (malformed `<!ELEMENT>`/`<!ATTLIST>`/`<!NOTATION>`/`<!ENTITY>` declarations — wrong field order, missing required field, wrong keyword) | 332 | **Real gap, in-scope** — these are WFCs (e.g. malformed `NotationDecl`/`PublicID`/`PEDecl`/`NDataDecl` shape), which bind non-validating processors too | M/L — Stage B of `docs/designissues/2026-07-08-xml-dtd-support.md`: tighten the internal-subset declaration grammar from "parse the shape and discard" (Stage A) to actually enforcing the production shape | ~332 real not-wf passes; **touches `Parser.XML.fst` core** — deferred this pass per the DTD-ID coordination note |
| `valid` Stage-A DTD-boundary — Name-character-class errata (5th-edition `BaseChar`/`Digit`/`Extender` ranges, `SECTIONS B.`) | 305 of 386 | **Real gap, in-scope, cheapest large family in the whole census** | S/M — a Unicode range-table update to `is_name_start_char`/`is_name_char`'s `Extender`/`Digit` productions, not new control flow | ~305 real wf-accept passes for a table edit; **touches `Parser.XML.fst` core Name-char classification** — deferred this pass, recommended as the **#1 priority for the next XML pass** once the DTD-ID work lands and this area is clear to touch |
| `valid` Stage-A DTD-boundary — genuine Stage-B remainder (external subset, markup-bearing general-entity replacement content) | 81 of 386 | **Real gap, in-scope**, matches the design doc's stated non-goals verbatim | L — external subset loading + markup-in-replacement-text semantics | ~81 real wf-accept passes; harder tail of Stage B/C |
| UTF-16 decode (36 LE-BOM + 4 BE-BOM sniffed + 1 declared-but-undecoded) | 41 | **Real gap against the MANDATORY baseline** — XML 1.0 §4.3.3 requires every conforming processor, validating or not, to accept both UTF-8 *and* UTF-16 | M — a UTF-16 (LE/BE, BOM and no-BOM) → UTF-8 transcode step ahead of/within the byte-oriented parser | ~41 tests, but more importantly closes the one skip family that isn't excusable by the non-validating class claim at all |
| `not-wf` out-of-profile: XML 1.1 (`version="1.1"`, tighter `Char`/`RestrictedChar` rules) | 33 | **Profile choice** — a different edition of the spec, not a validity/WF distinction; XML 1.1 adoption in the wild is minimal and RDF/XML corpora are practically all 1.0 | M — XML 1.1 has its own `Char`/`RestrictedChar`/`NameChar` productions, would need a version-gated parse path | Recommend parking pending an explicit owner call — see "Open question" below |
| Declared-encoding "iso-8859-1" undecoded (syntactically legal `EncName`, we don't decode it) | 27 | **Real gap, optional** — XML 1.0 permits (does not require) additional encodings beyond UTF-8/UTF-16 | S — ISO-8859-1 is a 1-byte-to-1-codepoint identity-ish map (0xA0–0xFF → U+00A0–U+00FF), a few lines | Cheap future win; still touches `Parser.XML.fst`'s byte-decoding path, deferred this pass |
| `not-wf` out-of-profile: Namespaces-in-XML (PI-target colon check `XML.Namespaces` doesn't model) | 4 | **Real gap, small** | S — extend `XML.Namespaces.fst`'s existing QName/PI checks | Tiny count; noted as a second cheap candidate for a future pass, not implemented here to keep this pass's commit to one deliverable |
| UTF-8 BOM prefix not skipped | 2 | **Real gap, trivial in isolation** — XML 1.0 §4.3.3 permits a BOM; a processor that accepts UTF-8 should tolerate a leading BOM | S — skip a literal `EF BB BF` prefix before the declaration scan | 2 tests; touches `parse_xml_document`'s entry point, so `Parser.XML.fst` core — deferred |

Total: 275 + 57 + 332 + 305 + 81 + 41 + 33 + 27 + 4 + 2 = **1157**, matches the post-fix skip count exactly.

## What got implemented this pass (before/after, labelled)

One category turned out to be a **runner bug, not a parser gap**: the
14 "declared encoding not decoded" skips whose encoding *name* is
syntactically illegal (`UTF#8`, `-UTF-8`, `.UTF-8`, `8-UTF`, `UTF/8`,
`UTF:8`, `UTF;8`, `UTF~8`, `XYZ+999`, `_UTF-8`, `a/b`,
`just&#41;word`, `@import(sys-encoding)`, `utf:8`). `Parser.XML.fst`
already implements XML 1.0 Production 81's `EncName` grammar
(`is_enc_name`, used inside `parse_xml_declaration`) and independently
rejects every one of these — the real parser was never the blocker.
The runner's `encoding_skip_reason` heuristic in
`bin/xml-runner/xml_runner.ml`, however, pre-filtered on a much
cruder test ("is this string one of `utf-8`/`ascii`/`us-ascii`?")
and skipped these 14 *before* the real, already-correct
`Parser_XML.is_enc_name`/`parse_xml_declaration` logic ever ran —
exactly the "tests skipped for runner reasons, not parser reasons"
case this census was asked to look for.

Fix (in `bin/xml-runner/xml_runner.ml` only — zero changes to
`Parser.XML.fst`/`XML.Wellformedness.fst`/`XML.Namespaces.fst`):
`encoding_skip_reason` now calls the already-extracted
`Parser_XML.is_enc_name` on the trimmed declared value; when it's
syntactically invalid, the pre-filter no longer skips and lets the
real dogfooded parser run and reject the document itself. A
syntactically legal but genuinely undecoded value (`UTF-16`,
`iso-8859-1`) still correctly falls through to the skip — this only
stops pre-empting the syntax-invalid subset the real parser was
always going to reject on its own. All 14 affected tests are
`TYPE="not-wf"` (verified per-test before landing this), so the flip
can only ever turn a skip into a real PASS, never manufacture a FAIL.

**Before: 1414 pass, 0 fail, 1171 skip (of 2585).**
**After: 1428 pass, 0 fail, 1157 skip (of 2585).** (+14 pass, −14 skip,
fail held at 0.)

Verified: `rdf-xml` 166 pass, 0 fail (unaffected — different binary,
`Parser.XML.fst` untouched); `grddl` 15 pass (≥15 floor held); XPath
unit 91 pass, 0 fail (unaffected). `formal/fstar/ocaml-output/xml_conformance_results.log`
refreshed to the new run.

## Recommended implementation order (next XML pass, once clear of the concurrent DTD-ID work)

1. **Name-character-class errata table** (305 tests, S/M) — the single
   highest tests-per-line-changed family in the whole census. A pure
   `Extender`/`Digit`/`BaseChar` Unicode-range update to
   `Parser.XML.fst`'s existing Name-char predicates; no new grammar,
   no new control flow.
2. **UTF-16 decode** (41 tests, M) — closes the one family that isn't
   excusable by the non-validating conformance-class claim; XML 1.0
   §4.3.3 makes UTF-16 acceptance mandatory regardless of processor
   class.
3. **DTD-internal-subset WFC-shape enforcement** (332 tests, M/L) —
   Stage B of the existing `2026-07-08-xml-dtd-support.md` plan:
   tighten `<!ELEMENT>`/`<!ATTLIST>`/`<!NOTATION>`/`<!ENTITY>` parsing
   from "shape-and-discard" to real production enforcement. Largest
   single bucket; also the most implementation work per test.
4. **ISO-8859-1 decode** (27 tests, S) — trivial byte-range decode,
   cheap but optional (not spec-mandated).
5. Everything else (Stage-B external-subset remainder, XML 1.1
   profile, Namespaces PI-target edge case, UTF-8 BOM prefix) is
   smaller-count and/or larger-effort; sequence opportunistically.

## Open question for the owner

Two categories are legitimately not-applicable under the
non-validating-processor class this project claims: `invalid`/`error`
TYPE (275) and the external-entity exemption (57), totalling **332
by-design skips** (a numeric coincidence with the separate, in-scope
332-test DTD-internal-subset WFC-shape gap in the table above — the
two are unrelated buckets that happen to share a count). Confirming
that framing explicitly — "Factoidal's XML layer is a non-validating,
non-external-entity-reading well-formedness processor, and scores
accordingly" — would let the dashboard headline for `xml_conformance`
read as a *bounded* remaining-gap count (~825, not 1157) rather than
an undifferentiated skip pile. Per the CLAUDE.md steer-handling rules,
this is being surfaced as a question, not assumed: **should the
dashboard carry this conformance-class framing alongside the raw
score, and is the XML 1.1 profile (33 skips) worth a dedicated slice,
or does it stay parked as a minimally-adopted edition?**

## Cross-references

- `bin/xml-runner/README.md` — the runner's own score history and
  "Known imprecision" section (which named this exact encoding-name
  runner gap in 2026-07-08, unfixed until this pass).
- `docs/designissues/2026-07-08-xml-dtd-support.md` — the Stage A/B/C
  DTD plan this census's items 1 and 3 continue.
- `docs/claude-rules/w3c-completeness-ledger.md` — dispositions table,
  `xml_conformance` row.
