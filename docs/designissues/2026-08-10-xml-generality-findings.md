# XML stack generality sanity check (task #49)

Owner directive (task #49, 2026-08-10): sanity-check `formal/fstar/Parser.XML.fst`
+ `XML.Namespaces.fst` + `XML.Wellformedness.fst`'s generality **before**
any RDF/XML proof program builds on it. Investigation + tests only — no
engine changes, no proofs.

Method: read the three modules, then exercise the real extracted parser
(`Parser_XML.parse_xml_document` / `parse_xml_document_children`, plus
`XML_Namespaces.is_namespace_wellformed`) two ways:

1. The existing `bin/xml-runner` against the vendored W3C `xmlconf`
   corpus (baseline, already committed — this session only re-ran it,
   did not re-derive its methodology).
2. A new ad-hoc driver, `tests/xml-generality/driver/xml_probe.ml`
   (I/O glue only, not part of the build — rule #11), against a new
   fixture set in `tests/xml-generality/fixtures/` covering the task's
   named categories: namespaces, entities, CDATA/comments/PIs, deep
   nesting, attribute edge cases, encodings, and a generated large
   document.

`bin/linux-x86_64/xml_runner` (already committed) baseline, re-run this
session: **1447 pass, 0 fail, 1138 skip (of 2585 discovered `<TEST>`
entries), 313 not-applicable** (EDITION-gated), in 0.216s wall. Unchanged
from `bin/xml-runner/README.md`'s recorded score — this task did not
touch the parser, so this is a confirmation run, not a new result.

## Table: WORKS / DIVERGES / UNSUPPORTED

Legend: **WORKS** = matches the XML 1.0 (5th ed.) / Namespaces-in-XML
spec on the probed case. **DIVERGES** = accepts/produces something the
spec forbids or requires differently, with a witness. **UNSUPPORTED** =
correctly refuses to handle a case that is out of the parser's declared
scope, with the error shape it produces.

| # | Area | Case | Verdict | Witness / detail |
|---|------|------|---------|-------------------|
| 1 | Namespaces | default namespace decl (`xmlns="..."`) | WORKS | `ns_default.xml` parses, `is_namespace_wellformed` true |
| 2 | Namespaces | prefixed namespace decl + use | WORKS | `ns_prefixed.xml` |
| 3 | Namespaces | prefix redeclared to a different URI in a descendant scope | WORKS | `ns_redeclaration.xml`: inner scope shadows outer, both accepted |
| 4 | Namespaces | prefixed unbind (`xmlns:p=""`) under XML 1.0 | WORKS | `ns_unbind_prefixed_only_10.xml`: `is_namespace_wellformed "1.0"` = **false** (spec: illegal in 1.0) |
| 5 | Namespaces | same prefixed unbind under XML 1.1 | WORKS | same fixture, `is_namespace_wellformed "1.1"` = **true** (spec: legal in 1.1) — version-gating is correctly threaded through, not hardcoded |
| 6 | Namespaces | default-namespace unbind (`xmlns=""`) | WORKS | `ns_unbind_default.xml`, true under both versions (spec allows this in both) |
| 7 | Namespaces | rebinding reserved prefix `xml` to the wrong URI | WORKS | `ns_reserved_xml_prefix_bad.xml` correctly false |
| 8 | Namespaces | binding any prefix to the reserved `xmlns` namespace URI | WORKS | `ns_reserved_xmlns_uri.xml` correctly false |
| 9 | Namespaces | two prefixes bound to the same URI, both used as attribute prefixes with the same local name | WORKS | `ns_attr_collision.xml` correctly false (post-expansion attribute-uniqueness rule) |
| 10 | Namespaces | element/attribute using an undeclared prefix | WORKS | `ns_unbound_prefix_use.xml` correctly false |
| 11 | Namespaces | `xml:` prefix usable without any declaration (pre-bound) | WORKS | `ns_xml_prefix_predeclared.xml`, `xml:lang`/`xml:space` accepted |
| 12 | Namespaces | duplicate `xmlns` attribute on one element | WORKS | `attr_duplicate_xmlns_bad.xml` rejected at the plain-XML duplicate-attribute-name layer, before namespace logic runs |
| 13 | Entities | five predefined (`amp lt gt quot apos`) | WORKS | `entities_predefined.xml` decodes correctly |
| 14 | Entities | decimal numeric char ref | WORKS | `entities_numeric_dec.xml` |
| 15 | Entities | hex numeric char ref | WORKS | `entities_numeric_hex.xml` |
| 16 | Entities | astral-plane numeric refs (`&#x1F600;`, `&#x10FFFF;` — max legal codepoint) | WORKS | `entities_astral.xml`: output bytes are the correct 4-byte UTF-8 for both codepoints (`F0 9F 98 80`, `F4 8F BF BF`) |
| 17 | Entities | undeclared entity reference | WORKS | `entities_undefined.xml` rejected (WFC "Entity Declared") |
| 18 | Entities | DOCTYPE-declared general internal entity | WORKS | `entities_declared_general.xml` expands |
| 19 | Entities | one declared entity's replacement referencing another declared entity | WORKS | `entities_composed_declared.xml`: `&b;` = `&a;, World!` expands recursively to `Hello, World!` |
| 20 | Entities | direct/mutual entity recursion (`&a;` → `&b;` → `&a;`) | WORKS | `entities_recursive.xml` rejected (WFC "No Recursion") |
| 21 | Entities | bare, unescaped `&` in content | WORKS | `entities_bare_amp_bad.xml` rejected |
| 22 | Entities | entity replacement text containing literal markup (`<`) | **UNSUPPORTED** (documented) | `entities_markup_in_replacement.xml` rejected outright. `Parser.XML.fst`'s own comment names this a Stage-A boundary: rejected, never silently wrong-accepted. A conformant processor should re-parse the expansion as content and accept it. |
| 23 | CDATA | basic CDATA carrying literal `<`/`&` | WORKS | `cdata_basic.xml` |
| 24 | Comments/PIs | comment + PI in both prolog and epilog | WORKS | `comment_and_pi_prolog_epilog.xml` |
| 25 | Comments/PIs | PI in content position (mid-element) | WORKS | `pi_in_content.xml`, retained as an `XPI` child node |
| 26 | Comments | `--` inside a comment body | WORKS | `comment_double_dash_bad.xml` rejected |
| 27 | Content | bare `]]>` in ordinary text | WORKS | `text_bare_cdata_close_bad.xml` rejected |
| 28 | Attributes | duplicate attribute name on one element | WORKS | `attr_duplicate_bad.xml` rejected |
| 29 | Attributes | **literal** tab/LF whitespace inside an attribute value | **DIVERGES** | `attr_whitespace_forms.xml`: literal `\t`/`\n` preserved as-is (hex `09`/`0A`). XML 1.0 §3.3.3 attribute-value normalization is a MUST for every processor (validating or not): literal whitespace chars (tab/CR/LF) in an attribute value must be replaced by a single space `0x20`. Not implemented. |
| 30 | Attributes | char-ref whitespace (`&#9;`, `&#10;`, `&#13;`) inside an attribute value | WORKS, but see #29 | `attr_charref_whitespace.xml`: correctly preserved as the literal control byte (spec requires this). Because #29 is unimplemented, right now literal and char-ref whitespace in attributes are **indistinguishable in the output** — both come out as the raw control byte — when the spec requires them to differ (literal → space, char-ref → preserved). |
| 31 | Content | CR / CRLF / LF line-ending normalization (XML 1.0 §2.11) | **DIVERGES** | `line_endings_crlf_cr_lf.xml`: text content came back as `line1\r\nline2\rline3\nline4` (hex shows raw `0D 0A`, `0D`, `0A` all preserved). Spec requires the processor to normalize `\r\n` and bare `\r` to `\n` **before** parsing, for every processor unconditionally. Not implemented anywhere in `Parser.XML.fst` (confirmed by source grep — no line-ending-normalization pass exists). This affects text content, comments, CDATA, and (compounding #29) attribute values, and would produce non-compliant literal content for any RDF/XML document containing raw CR or CRLF in its source. |
| 32 | Encoding | UTF-8 BOM at byte 0 | WORKS | `utf8_bom.xml`: BOM consumed, not treated as content |
| 33 | Encoding | `encoding="ISO-8859-1"` declared, document is plain ASCII | WORKS (vacuously) | `encoding_decl_iso8859.xml` parses — but doesn't exercise the divergence below since the bytes happen to already be valid UTF-8 |
| 34 | Encoding | `encoding="ISO-8859-1"` declared, document's bytes are **actually** ISO-8859-1 (non-UTF-8, e.g. `é` = `0xE9`) | **DIVERGES** (documented) | `encoding_decl_iso8859_raw.xml` rejected outright — a genuinely well-formed ISO-8859-1 document is refused. `parse_xml_declaration` parses and **syntax-validates** the `encoding=` pseudo-attribute (`is_enc_name`), but the caller (`parse_xml_document`) discards the parsed attributes (`ParseOk _attrs pos' -> pos'`) and every downstream byte read (`fs_cp_at`, `fs_byte_index`) unconditionally assumes UTF-8. The encoding declaration is recognized syntactically and then ignored. Matches the already-documented xmlconf skip category "declared encoding X not decoded" (27 iso-8859-1 + 1 UTF-16 cases in the corpus, `bin/xml-runner/README.md`). |
| 35 | Encoding | UTF-16 (with BOM, declared `encoding="UTF-16"`) | UNSUPPORTED (documented) | `utf16le_encoded.xml` rejected — no UTF-16 decode path exists; matches the corpus's 4 UTF-16BE + 1 UTF-16 skip bucket. |
| 36 | Deep nesting | element parent→child nesting depth, native-stack behavior | **DIVERGES from "arbitrary depth"** (structural, not a bug) | See "Deep nesting" section below — the F* `fuel` bound is `document length + 1` (no artificial depth cap in the logic), but `parse_xml_element`/`parse_children` are **mutually recursive, non-tail** (per the module's own #273 comment — the tail-recursion fix there only covered same-depth **siblings**, not parent-child nesting), so each nesting level costs one native OCaml stack frame. Under the default 8 MiB `ulimit -s`, parsing overflows the native stack between depth 55,000 (succeeds) and depth 60,000 (`Fatal error: exception Stack overflow`). With `ulimit -s unlimited`, depth 200,000 parses in 0.50 s / 51 MB peak RSS with no error. |
| 37 | Large documents | ~50 MB, flat/wide (RDF/XML-shaped, 191,167 sibling `rdf:Description` records) | measured, not a correctness finding | See "Large-document / DOM-materialization cost" below. |

## Deep nesting: stack behavior in detail

`parse_xml_document`'s top-level fuel is `fs_byte_length input + 1` — the
F* logic itself imposes no depth ceiling; a document could in principle
nest as deep as its byte length allows. But `parse_xml_element` calls
`parse_children` which calls `parse_xml_element` again for each child
element — this is a **parent→child** recursion, structurally different
from the same-module's `#273` fix (comment at
`formal/fstar/Parser.XML.fst:1144-1153`), which made **sibling**
accumulation tail-recursive but left nesting depth as one native stack
frame per level, by construction (the recursive call's result is wrapped
in `XElement` before the caller returns).

Measured (probe driver, `-bench`, `tests/xml-generality/gen_deep_nesting.py`):

| Depth | Default `ulimit -s` (8192 KB) | `ulimit -s unlimited` |
|---|---|---|
| 1,000 | OK, 0.0013 s, 6.8 MB RSS | OK |
| 10,000 | OK, 0.013 s, 10.0 MB RSS | OK |
| 50,000 | OK, 0.073 s, 18.5 MB RSS | OK |
| 55,000 | OK | — |
| 60,000 | **Stack overflow** | — |
| 100,000 | Stack overflow | OK, — |
| 200,000 | Stack overflow | OK, 0.50 s, 51 MB RSS |
| 2,000,000 | Stack overflow | not run past 200k |

This is a real, reachable limit for a non-adversarial document — 55–60k
levels is well inside what a buggy generator or an adversarial input
could produce, and it fails as an uncaught native OCaml exception
(`Fatal error: exception Stack overflow`, process exit code 2), not a
handled `ParseFail`/`None`. That is a robustness gap worth carrying into
the traversal-interface design (below): a fold-shaped interface with an
externally-bounded frame budget, or one compiled to an explicit
work-list instead of the call stack, removes this class of failure by
construction for a future streaming producer, even though the concrete
`xml_node` instance (this task did not change it) still has it.

## Large-document / DOM-materialization cost

`tests/xml-generality/gen_large_doc.py` generates a flat, wide,
RDF/XML-shaped document (many sibling `rdf:Description` records, matching
the owner's stated concern about DOM materialization cost). Measured with
the probe driver (`-bench`; note this is an un-optimized `ocamlfind
ocamlopt` scratch build — no `-O3`/flambda flags — so these are relative/
scaling numbers, not the production binary's throughput floor):

| Input size | Records | Total AST nodes | Parse time | Peak RSS (`VmHWM`) | RSS : input ratio |
|---|---|---|---|---|---|
| 1 MB | 3,896 | 46,754 | 0.143 s | 12.8 MB | 12.8x |
| 10 MB | 38,531 | 462,374 | 1.318 s | 55.4 MB | 5.5x |
| 50 MB | 191,167 | 2,294,006 | 6.429 s | 250.5 MB | 5.0x |

Throughput is roughly linear and stable at **~7.5–7.8 MB/s** across this
size range (single-threaded, this driver). Peak memory settles toward
**~5x the input byte size** as documents grow past a few MB (the 1 MB
row's higher 12.8x ratio is process/runtime baseline overhead, not
document-proportional). Both are consistent with full DOM
materialization (every text run, attribute, and element becomes boxed
OCaml values with no sharing/interning) — this is the cost the traversal-
interface sketch below is designed to let a future streaming producer
avoid, without changing what the concrete `xml_node` instance does today.

## Fixtures and driver

- `tests/xml-generality/fixtures/*.xml` — 30+ hand-written witness
  documents, one per row above (committed).
- `tests/xml-generality/gen_deep_nesting.py` — generates
  `<a><a>...leaf...</a></a>` at a given depth (committed; the deep
  fixtures actually probed here are regenerated on demand, not
  committed at 50k+ depth to avoid a huge diff — two small ones,
  1,000 and 5,000 levels, are committed as fixtures).
- `tests/xml-generality/gen_large_doc.py` — generates the flat
  RDF/XML-shaped large document at a target byte size (committed; the
  50 MB output itself is not committed).
- `tests/xml-generality/driver/xml_probe.ml` — ad-hoc OCaml driver,
  I/O glue only (rule #11), linking the extracted `Parser_XML` /
  `XML_Namespaces` modules directly. Not wired into `build-ocaml.sh`;
  build recipe is the same scratch-compile pattern
  `bin/xml-runner/README.md` documents, recorded in
  `tests/xml-generality/driver/README.md`.

## Summary for the RDF/XML proof program

Two findings are load-bearing for anyone about to prove the RDF/XML
mapping algorithm against this parser's output:

1. **Line-ending and attribute-value-whitespace normalization (#29, #31)
   are both missing**, unconditionally (not a DTD/validation gap — XML
   1.0 requires both for every processor). Any theorem about literal
   equality between an RDF/XML document's source text and its produced
   RDF literals should either (a) state this as an explicit assumption/
   caveat, or (b) get these two normalization passes landed in
   `Parser.XML.fst` first — they are small, well-founded, and squarely
   inside the existing module's style (a codepoint/byte walk, same shape
   as `scan_chars_valid`).
2. **Declared-encoding is parsed and validated but never honored (#34)**
   — the parser is UTF-8-only by construction. This is already scored
   honestly as a `skip` bucket in `bin/xml-runner`, so it is not a
   silent gap, but it means the RDF/XML proof program's applicability
   claim should be stated as "UTF-8 (or ASCII-compatible) input", not
   "XML 1.0", until a real multi-encoding decode path exists.

Everything else probed — namespaces (all eight sub-cases), the five
predefined + numeric + astral + declared-entity paths, WF rejections
(recursion, undeclared entities, duplicate attributes, `--` in
comments, bare `]]>`), BOM handling, and sibling-heavy large documents —
**WORKS** and matches spec. The deep-nesting native-stack limit (#36) is
real but only reachable at depths (~55–60k) that a proof program is
unlikely to need to reason about directly; it matters for the traversal-
interface design (next document) more than for the mapping proof itself.
