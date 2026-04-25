UK Parliament Procedure Browser sample SPARQL queries

Source site:
- `https://api.parliament.uk/procedure-browser/`
- starting point used: `https://api.parliament.uk/procedure-browser/meta/sitemap`

Extraction date:
- 2026-04-24

Scope:
- main landing/sub-pages that visibly expose "SPARQL queries used by this page"
- a small set of representative detail pages that were directly accessible via the
  site and search snippets, including procedure, step, legislature, and house pages

Notes:
- Queries are reformatted for readability; they are not raw HTML copies.
- A few landing pages were visible in search results but could not be fetched
  directly through the available tooling in this session, notably:
  `procedure-browser/routes`, `procedure-browser/clocks`, and
  `procedure-browser/calculation-styles`.
- The extracted queries here are intended as a useful local sample corpus rather
  than a claim of complete exhaustive coverage of every entity page in the site.

Files:
- `main/` contains landing-page queries
- `detail/` contains representative detail-page queries
