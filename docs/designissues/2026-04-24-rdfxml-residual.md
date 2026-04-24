# RDF/XML residual W3C failures — 2026-04-24

Goal: close out 4 residual `rdf-xml` W3C test failures. All 4 report
"Triples mismatch: expected N, got N" (count-equal, content-different).

## Target tests

| Test | Expected | Got | Hypothesis |
|------|---------:|----:|------------|
| `rdf-containers-syntax-vs-schema-test004` | 15 | 15 | `rdf:li` numbering (sequential) mixed with reification via `rdf:ID` |
| `rdf-containers-syntax-vs-schema-test007` | 4  | 4  | `rdf:li` counter scoping: each node element has its own counter (nested `rdf:Description` inside rdf:li) |
| `xml-canon-test001` | 1 | 1 | `parseType="Literal"` XML canonicalisation |
| `xml-canon-test002` | 5 | 5 | `parseType="Literal"` + reification (`rdf:ID`) |

## Expected N-triples (ground truth summary)

### test004 — `rdf-containers-syntax-vs-schema`
Input: `<foo:Bar>` containing four `<rdf:li>` children with varied forms:
1. `<rdf:li rdf:ID="e1">1</rdf:li>`           — plain literal, reified at `#e1`
2. `<rdf:li rdf:parseType="Literal">2</rdf:li>` — XMLLiteral
3. `<rdf:li rdf:parseType="Resource">…</rdf:li>` — resource bnode
4. `<rdf:li rdf:ID="e4" foo:bar="foobar"/>`    — empty-element form, reified at `#e4`, object is resource bnode with `foo:bar "foobar"`.

Key expected triples (15):
- `_:bar rdf:type foo:Bar`
- `_:bar rdf:_1 "1"`, `_:bar rdf:_2 "2"^^XMLLiteral`, `_:bar rdf:_3 _:res`, `_:bar rdf:_4 _:res2`
- `_:res rdf:type foo:Bar` (from parseType="Resource")
- `_:res2 <http://foo/bar> "foobar"` (empty property element)
- Reification quad for `#e1`: rdf:Statement/subject/predicate/object with object="1"
- Reification quad for `#e4`: rdf:Statement/subject/predicate=rdf:_4/object=_:res2

### test007 — independent `rdf:li` counters
Nested rdf:li: outer `rdf:_1`, `rdf:_2`; inner Description has its own
`rdf:_1`, `rdf:_2`. Counter MUST reset per node-element.

### xml-canon test001 / test002
Input `<eg:prop rdf:parseType="Literal"><br /></eg:prop>`.
Expected literal lex form:
`<br xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:eg="http://example.org/"></br>`
i.e. exclusive XML canonicalisation: `<br />` expands to `<br></br>`, and
the inner element inherits ambient namespace declarations.

test002 adds `rdf:ID="reif"` reification and `xml:base="http://example.com/"`
so the reification statement is anchored at `<http://example.com/#reif>`.

## F* code locations

- Parser: `formal/fstar/Parser.RDFXML.fst`
- Related: `formal/fstar/Parser.XML.fst` (if separate XML tokeniser)

## Plan

1. Diagnose: read parser to see how `rdf:li` counter is threaded + how
   parseType="Literal" reconstructs XML text.
2. Fix narrow bugs; if deeper refactor required, stop and document.
3. Commit per-test; rebuild deferred to main thread.

## Progress

- [x] scratch doc committed
- [ ] test004 root cause
- [ ] test007 root cause
- [ ] xml-canon test001 root cause
- [ ] xml-canon test002 root cause
