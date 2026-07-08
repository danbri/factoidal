# XML DTD / DOCTYPE support — scope, tractable slice, and the honest-SKIP remainder

Status: design note / follow-up tracker. Written 2026-07-08 alongside
the "honest XML conformance accounting" change (see the commit that
stopped counting vacuous DOCTYPE-forced not-wf rejections as passes).

## Why this exists

`Parser.XML.fst` has no `<!DOCTYPE ...>` production at all. `skip_misc`
skips whitespace / comments / PIs, then hands off to
`parse_xml_element`. Any document whose prolog carries a DOCTYPE is
therefore rejected outright — the parser never reaches the root element.

Before the 2026-07-08 accounting fix, the xmlconf runner counted every
one of those rejections as a `not-wf` PASS. That inflated the score:
1166 of 1442 "passes" were **vacuous** — the document was rejected only
because we cannot parse any DOCTYPE, not because we detected the
not-well-formed construct the test targets. A test that wants "reject"
got "reject" for the wrong reason. Those 1166 are now counted as SKIP,
and the honest headline dropped to a few hundred real passes.

To convert vacuous SKIPs back into real verdicts we need actual DTD /
DOCTYPE handling in `Parser.XML.fst`. This note records what a tractable
first slice looks like and what stays an honest SKIP until it lands.

## What the corpus actually needs

The `valid` bucket (812 tests) is 100% DOCTYPE-bearing: every one is
`Skip "DOCTYPE/DTD not parsed"`. A large fraction are well-formed with
only an *internal* subset and no external entities — those become real
`wf-accept` passes the moment the parser can (a) recognise and step over
`<!DOCTYPE name [ ... ]>` and (b) resolve the general-entity references
the body then makes against the internal subset's `<!ENTITY>`
declarations.

The `not-wf` DOCTYPE tests split two ways:

1. Violation is in the element body / general structure (mismatched
   tags, bad char, `]]>` in text, ...). Once the DOCTYPE is stepped
   over, the existing element parser already rejects these for the right
   reason — vacuous → **real pass**.
2. Violation is in the DTD itself or in a DTD-dependent WF constraint
   (reference to an undeclared entity, recursive/self-referential entity
   definition, PE in an internal subset used where the WFC forbids it,
   an `<!ATTLIST>`/`<!ELEMENT>` the well-formedness — not validity —
   rules still constrain). These require the parser to *understand* the
   internal subset, not just skip it. Skipping the DOCTYPE naively would
   make the parser **accept** these documents → they would flip from
   vacuous SKIP to genuine FAIL, which is strictly worse than a SKIP.

Point 2 is why "just skip the `<!DOCTYPE ...>`" is not an acceptable
slice on its own: it manufactures FAILs.

## Tractable slice (proposed, F*-first, must verify with no `--lax`)

Add to `Parser.XML.fst`, all fuel-bounded `Tot`, no new escape hatches:

1. `parse_doctype_decl` — recognise `<!DOCTYPE` S Name (S ExternalID)?
   S? (`[` intSubset `]` S?)? `>`. Return the declared root Name plus a
   parsed internal-subset declaration list; when an ExternalID
   (SYSTEM/PUBLIC) is present, record that fact but read nothing external
   (this parser is non-validating and reads no external entities — the
   same stance the runner already documents).

2. Internal-subset declarations, enough for well-formedness:
   - `<!ENTITY name "value">` general internal entity — store
     (name → replacement text).
   - `<!ENTITY % name "value">` parameter entity — store; not expanded in
     the internal subset beyond what the WFCs need.
   - `<!ELEMENT ...>` / `<!ATTLIST ...>` / `<!NOTATION ...>` — parse the
     shape and discard (element/attlist *content models* are a validity
     concern, out of scope for a WF-only slice), but their presence must
     parse cleanly so a valid-with-internal-DTD document is accepted.
   - PI / comment / PEReference / whitespace inside the subset.

3. Wire the general-entity table into `parse_reference` /
   `parse_text_content` / `parse_attr_value` so that:
   - a reference to a declared internal general entity expands to its
     replacement text (recursively, with a cycle guard — the WFC "No
     Recursion"), and
   - a reference to an **undeclared** entity is rejected (WFC "Entity
     Declared"), instead of the current fixed five-builtin-only set.

4. `parse_xml_document` calls `parse_doctype_decl` from `skip_misc`'s
   position (DOCTYPE is legal Misc-adjacent in the prolog, at most once,
   before the root element) and threads the entity table into the
   element parse.

Everything above is byte-oriented and fuel-decreasing like the existing
comment/CDATA/PI bodies, so it stays inside the current verification
regime. No change to the on-disk format, no OCaml glue.

## Explicit non-goals (stay SKIP until a later slice)

- DTD **validity** (`invalid` / `error` TYPEs) — element content models,
  attribute-type enforcement, ID/IDREF, `#REQUIRED`/`#FIXED`. The runner
  already SKIPs these "no DTD validation (by design)" and that stays
  correct.
- External DTD subsets and external parsed entities (we read nothing
  external; the runner's `ENTITIES != "none"` exemption already covers
  the not-wf cases that hinge on external entities).
- Conditional sections (`INCLUDE`/`IGNORE`), notation-driven unparsed
  entities.
- Parameter-entity expansion semantics beyond the minimum the WFCs need.

## Accounting contract for the runner

Until the slice lands, DOCTYPE-bearing tests remain honest SKIPs:
`valid` → `Skip "DOCTYPE/DTD not parsed"`, `not-wf` → vacuous SKIP. As
each capability above lands, the corresponding tests move from SKIP to a
real PASS or a real FAIL — never back to a vacuous PASS. The runner must
keep the invariant that a `not-wf` test counts as PASS only when the
rejection is attributable to the tested construct.

## Tracking

File a GitHub issue "XML: internal-subset DTD slice (WF-only)" linking
this note; check off capabilities 1–4 as they land, reporting the
vacuous-SKIP → real-verdict delta on each.
