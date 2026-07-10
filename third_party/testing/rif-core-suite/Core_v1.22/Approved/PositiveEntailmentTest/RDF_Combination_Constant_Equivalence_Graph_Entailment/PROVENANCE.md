# PROVENANCE — RDF_Combination_Constant_Equivalence_Graph_Entailment-conclusion.ttl

The official `Core_v1.22.zip` distribution ships this test's premise
and imported graph but **no conclusion document** — because this
test's conclusion is an **RDF graph**, not a RIF condition, and the
zip packaging only collected `.rif` conclusions. The repository URL a
`-conclusion.rif` would have had
(`https://www.w3.org/2005/rules/test/repository/tc/RDF_Combination_Constant_Equivalence_Graph_Entailment/RDF_Combination_Constant_Equivalence_Graph_Entailment-conclusion.rif`)
returned 404 in the earliest Wayback Machine captures too (checked
2026-07-10, e.g. the 2017-07-12 snapshot) — the file never existed.

`RDF_Combination_Constant_Equivalence_Graph_Entailment-conclusion.ttl`
here transcribes the **Conclusion** section of the archived
authoritative test-case wiki page:

- Source: <https://www.w3.org/2005/rules/wiki/RDF_Combination_Constant_Equivalence_Graph_Entailment>
  (read-only archive; page last modified 2010-02-02, oldid=12024,
  fetched 2026-07-10)
- Conclusion as published there (Turtle):

  ```
  @prefix ex: <http://example.org/example#> .
  @prefix xs: <http://www.w3.org/2001/XMLSchema#> .
   ex:a ex:p "this is a plain literal"^^xs:string .
  ```

- Test metadata from the same page: PositiveEntailmentTest, Dialect
  Core, Status Approved (F2F12), Contributor Jos de Bruijn, Purpose
  "Test equivalent treatment of RDF constants and RIF symbols in
  simple entailment".

Only whitespace was normalized in the transcription; the triple is
byte-identical in content.

License: W3C Document License, same as the rest of the vendored RIF
Test Cases (see `third_party/testing/rif-core-suite/README.md`).
