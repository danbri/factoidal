# 2026-05-07 — GeoSPARQL 1.1 in F* + backend architecture impact

## Status

Design investigation. Doc-only. No code written, no decisions
ratified. Sequel to the F*-purity recovery plan
([2026-05-07-query-planning-fstar-recovery.md](2026-05-07-query-planning-fstar-recovery.md))
and the I/O verification annex
([2026-05-07-io-verification-and-third-party.md](2026-05-07-io-verification-and-third-party.md)).

## Background

GeoSPARQL is a joint OGC + W3C standard that adds geometric data
types and spatial query primitives to RDF + SPARQL. It is the
canonical way to model and query spatial data in linked-data
systems. Wikidata, OpenStreetMap RDF dumps, Ordnance Survey,
the UK Parliament constituency boundaries dataset, transport
graphs, environmental observation networks, and most government
open-data SPARQL endpoints all carry geometry literals tagged
with `geo:wktLiteral`.

The latest version is GeoSPARQL 1.1 (OGC 22-047r1), published
September 2024. It supersedes 1.0 (OGC 11-052r4, 2012). 1.1 is
backwards compatible: every 1.0 conformant store is also
1.0-conformant when read as 1.1, but 1.1 adds new literal
datatypes, new function families, and clarifies CRS handling.

### 1.0 vs 1.1 deltas (the important ones)

- New geometry literal datatypes: `geo:geoJSONLiteral` (RFC 7946
  GeoJSON, embedded in RDF as a string-typed literal),
  `geo:dggsLiteral` (Discrete Global Grid System cell strings,
  e.g. H3, S2, rHEALPix).
- New aggregate functions in the `geof:` namespace —
  `geof:aggCentroid`, `geof:aggBoundingBox`, `geof:aggUnion`,
  etc. (full set per spec). These are SPARQL aggregate
  functions, not row-level expressions.
- CRS handling clarified: WKT CRS prefix syntax
  (`<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(...)`)
  and explicit `crs84` / `crs:EPSG/0/4326` semantics for
  non-prefixed literals.
- Conformance class restructure: Core / Topology / Geometry
  Extension / Query Rewrite Extension / RDFS Entailment
  Extension. 1.0's "simple features" / "Egenhofer" / "RCC8"
  topological vocabularies are all retained.
- `geo:hasMetricArea`, `geo:hasMetricLength`,
  `geo:hasMetricVolume`, `geo:hasMetricPerimeter` derived
  property predicates in 1.1.

### Why this is in scope

A verified RDF store that cannot answer `?x geo:sfWithin
?bbox` queries cannot serve any of the production datasets
listed above. Wikidata in particular has hundreds of millions
of `wdt:P625` (coordinate-location) statements with
`geo:wktLiteral` values. A store that punts spatial is a toy.

## Scope decision: profile + version

- Aim at GeoSPARQL 1.1 directly (OGC 22-047r1). 1.0 is a strict
  subset of 1.1's vocabulary; conformance to 1.1 implies 1.0.
- First-cut profile: Core + Topology Extension (Simple
  Features family of relations) + a **subset** of the Geometry
  Extension (envelope, distance, intersection on bounding
  boxes — the "cheap" CG functions). The Egenhofer and RCC8
  relation families are deferred but mostly derive from
  Simple Features predicates plus DE-9IM (so cheap to add
  once the DE-9IM matrix evaluator exists).
- Defer: GML literal parser, GeoJSON literal parser, DGGS
  literal parser, full Geometry Extension (buffer,
  convexHull, symmetric difference, boundary as a true
  topological boundary), Query Rewrite Extension, RDFS
  Entailment Extension. Each of these is its own multi-week
  project — punted with rationale below.
- Out of scope entirely for v0: 3D geometries, M-coordinate
  geometries (linear referencing), CRS transformations
  beyond identity (so EPSG:4326 → EPSG:27700 is not
  attempted; queries must use the storage CRS).

Rationale: WKT + 2D + EPSG:4326 (or the literal's stated
CRS, used as-is) covers the dominant real-world workload.
Everything else can be added in subsequent phases without
rearchitecting the literal layer.

## F* surface required

A table mapping GeoSPARQL features to F* modules. "S/M/L/XL"
estimates are LoC: S < 300, M 300-1000, L 1000-3000, XL > 3000.

| GeoSPARQL feature | F* home | Reuse? | Estimate |
|---|---|---|---|
| WKT literal lexer + parser (POINT / LINESTRING / POLYGON / MULTI*) | NEW: `formal/fstar/Parser.WKT.fst` | reuses `Parser.Combinators` | M |
| Geometry ADT (point / linestring / polygon / multi*, plus collection) | NEW: `formal/fstar/RDF.Geo.Types.fst` | new | S |
| Bounding-box ADT + envelope computation | NEW: `formal/fstar/RDF.Geo.BBox.fst` | new | S |
| DE-9IM topological predicates (Simple Features family) | NEW: `formal/fstar/RDF.Geo.Topology.fst` | new | L |
| Cheap non-topological functions (distance, envelope, area, length) | NEW: `formal/fstar/RDF.Geo.Functions.fst` | new | M |
| Hard CG functions (buffer, convexHull, intersection, union, difference) | NEW: `formal/fstar/RDF.Geo.CG.fst` | needs decision | L-XL |
| `geof:` function-call dispatch | extends `SPARQL11.Algebra.evaluate_expr` for `E_FunctionCall iri args` when `iri` is in the `geof:` namespace | extends existing | XS-S |
| `geo:` property predicate handling (e.g. `geo:hasGeometry`, `geo:asWKT`) | dispatch in `SPARQL11.Store` query layer | extends existing | XS |
| CRS registry (well-known EPSG codes, identity transform only for v0) | NEW: `formal/fstar/RDF.Geo.CRS.fst` | new | S |
| GeoJSON literal parser (RFC 7946) | NEW: `formal/fstar/Parser.GeoJSON.fst` | reuses `Parser.JSONResults` JSON tokeniser | M (deferred) |
| GML literal parser | NEW: `formal/fstar/Parser.GML.fst` | reuses `Parser.XML` | M (deferred) |
| DGGS literal handling (H3 / S2 cell-id strings) | NEW: `formal/fstar/RDF.Geo.DGGS.fst` | new | M (deferred) |
| Aggregate `geof:agg*` (centroid, bbox, union over a group) | extends `SPARQL11.Algebra` aggregates | extends existing | M |
| Spatial index over in-mem | NEW: `formal/fstar/RDF.Geo.Index.fst` (R-tree or H3-binned Roaring) | new, see below | L |

The `E_FunctionCall : wf_iri -> list expr -> expr` constructor
already exists in `SPARQL11.Algebra` (line 479). GeoSPARQL
function calls land there; the dispatch table grows. No new
algebra constructor is needed for row-level functions. For
aggregates the existing aggregate dispatch needs a new
constructor or a generic extension hook.

Where a feature is "punt for now" the table says so. The v0
slice is rows 1-9 (WKT + types + bbox + topology + cheap
functions + dispatch + CRS registry + in-mem index), with
the index being the architectural fork.

## Computational geometry in F* — the hard part

DE-9IM topological predicates and especially distance / buffer /
intersection / union / difference are real computational-geometry
algorithms with a long history of subtle numerical bugs. F* in
2026 has:

- `FStar.Real` (axiomatised reals, no extraction, suitable
  only for spec-level reasoning);
- `FStar.Math.Lib`, `FStar.Math.Lemmas` (integer / rational
  reasoning, lemma-heavy);
- `FStar.UInt32` / `FStar.UInt64` / `FStar.Int64` (machine
  integers, fully extractable);
- no built-in IEEE-754 floating-point spec (HACL\* uses
  fixed-point or interval arithmetic where it needs reals).

This is the section that decides whether GeoSPARQL is feasible at
all under the iron rules. There are three honest options.

### Option A: pure exact-arithmetic geometry (rationals)

Represent coordinates as `(int * int)` numerator / denominator
pairs (or arbitrary-precision rationals via a vendored bignum
in F*). All predicates (point-in-polygon, segment intersection,
DE-9IM matrix entries) reduce to comparisons of polynomial
expressions over rationals, which are exact. No floating-point
roundoff bugs.

- Verifiable: yes. The point-in-polygon ray-cast,
  segment-intersection, and DE-9IM evaluator can be specified
  and proved correct against a model in `FStar.Real`.
- Performant: no. Coordinate values blow up under repeated
  intersection (each operation roughly squares the numerator
  / denominator size). Buffer / convex-hull on real-world
  polygons becomes effectively unusable.
- Adequacy: fine for **topological predicates** on raw
  literal coordinates (no derived geometries). The blow-up
  bites only when you compose CG operations.
- Verdict: **acceptable for v0 topology + envelope +
  bounding-box + distance-squared (so the sqrt isn't
  needed)**. Not acceptable for buffer / convexHull / true
  intersection / union output as new geometries.

### Option B: robust floating-point geometry (Shewchuk-style)

Implement Shewchuk's adaptive-precision predicates and
exact-arithmetic constructions in F*. Coordinate values stay
as `double`s; predicates use floating-point filters that fall
back to extended precision only when the filter is inconclusive.
This is what production systems (CGAL, JTS / GEOS, S2) do.

- Verifiable: hard. Without an IEEE-754 spec in F* you cannot
  prove the predicates correct against the real-arithmetic
  model. You can prove the structure (filter then exact path)
  but the exact path needs an exact-arithmetic kernel anyway,
  which is just option A wrapped in a fast path. Without an
  IEEE-754 model, option B reduces in spec to "trust the
  filter".
- Performant: yes — this is the mainstream solution.
- Verdict: **off the critical path under the iron rules**.
  Pursue only if/when an IEEE-754 spec lands in F* core or
  HACL\* gains a verified `double` arithmetic library. We
  should not block GeoSPARQL on this.

### Option C: `assume val` to a host CG library

CGAL (C++), GEOS (C, the JTS port), S2 (C++), or libspatialindex.
Wrapped as F* `assume val` declarations with semantic
specifications and OCaml-side realisations that call the host
library via OCaml bindings (`ocaml-cgal`, `ocaml-geos`).

- Verifiable: only at the boundary. The F* spec describes what
  the function returns; the OCaml realisation is trusted (as
  with regex, file I/O, clock). Per CLAUDE.md rule #11 this is
  acceptable **only** if the call-out is a host-engine primitive
  and not a re-implementation of logic that belongs in F*.
- Boundary status: spatial predicates and CG operations are
  arguably host-engine call-outs in the same sense regex is —
  the algorithms have decades of numerical-stability work behind
  them and re-implementing them in pure F* is a dead end. The
  I/O verification annex's pattern of "F* spec + OCaml realiser
  + round-trip property test" applies cleanly to predicates
  (input geometries → boolean) but less cleanly to constructions
  (input geometries → output geometry, where the output's exact
  form depends on the host library's tolerance settings).
- Risk: importing a 500k-line C++ codebase (CGAL) into the
  trust base is a strictly worse story than vendoring HACL\*
  (which is itself verified). GEOS is smaller (~200k lines)
  and well-tested. S2 is library-quality and used by Google
  internally.
- Verdict: **the pragmatic choice for production**, but it
  inflates the unverified surface significantly. If pursued,
  the boundary-audit must explicitly tag CG call-outs as
  "trusted, non-verified, vendored".

### Recommendation

For the v0 phase 1-3 slice (WKT + topology + in-mem index), use
**option A** (pure-rational topology + bounding-box + distance²).
This delivers `geof:sfIntersects`, `geof:sfWithin`,
`geof:sfContains`, `geof:sfTouches`, `geof:sfDisjoint`,
`geof:sfEquals`, `geof:sfCrosses`, `geof:sfOverlaps`,
`geof:distance` (squared, with a final sqrt that can be lemma'd
out in the planner where possible), and `geof:envelope`. This
is enough to be useful for filtering Wikidata-style point-data
queries.

For phase 6 (the hard CG functions — buffer / convexHull /
true intersection / union / difference output as new
geometries), **option C with GEOS** is the recommended path,
explicitly added to the boundary audit as a vendored host-engine
call-out. Reject this if the user wants a pure-F* implementation
even at the cost of those operations.

## Backend implications

### In-memory (`RDF.CottasInMem`)

Each geometry literal is parsed once on insertion and cached as
the `RDF.Geo.Types.geometry` ADT alongside the original WKT
lexical form (the lexical form must be preserved for round-trip
serialisation; geo literals are not auto-canonicalised, since
WKT has multiple equivalent textual forms). The dictionary
(term-id ↔ term) gains an optional "parsed-geometry" side-table
keyed by term-id. Spatial predicates iterate over candidate
triples; with no index this is O(N) per predicate evaluation.
Adequate for small datasets (< ~10k geometries); quadratic for
spatial joins.

A v0 in-mem spatial index belongs in `RDF.Geo.Index.fst` and
should be a learning-friendly structure: an STR-packed R-tree
over bounding boxes is the textbook choice (build once, query
many). All operations are over `RDF.Geo.BBox.bbox` rationals;
exact and verifiable. R-tree node fanout is a tuning constant.

### COTTAS / Parquet on-disk (`RDF.CottasStore.*`)

The current model is an OPS-sorted columnar store with
presence-bitmap indexes (one bitmap per O for fast S/P lookups).
Adding spatial indexing is the big architectural decision.
Three options ranged from cheapest-to-implement to
most-correct-at-scale:

1. **Naive WKT-lexical column.** Geometry literals are stored
   as their WKT string in the literal column (already supported
   — they are typed literals). Spatial predicates parse on demand.
   Slow. No index. This is the day-1 fallback and requires
   *zero* COTTAS changes.

2. **WKB binary column.** Pre-parse WKT to Well-Known Binary
   (a defined OGC binary serialisation of geometries) and store
   as a variable-length binary side column keyed by literal
   term-id. Faster decode (no re-parsing). Adds one new column
   type to COTTAS. No index; spatial predicates still iterate.

3. **GeoParquet adoption.** Apache Sedona / OGC have defined
   GeoParquet, a Parquet profile for geo data with WKB-encoded
   geometry columns plus standardised file-level metadata
   (`geo` key in Parquet kv-metadata declaring CRS, geometry
   type, bbox per row group). If COTTAS is going Parquet anyway
   per the `ParquetFooter.fst` pilot, adopting GeoParquet means
   the on-disk format interoperates with Sedona, DuckDB-spatial,
   GDAL/OGR, QGIS, and the Python geopandas + pyarrow stack —
   all of which read GeoParquet natively. This is a substantial
   ecosystem win for very little additional spec work.

Plus a **spatial index column** for "give me triples whose
geometry intersects bbox B in O(log n)". Two competing designs:

- **R-tree footer.** Build an STR-packed R-tree over the
  per-row-group bboxes (or per-row bboxes for fine-grained
  queries) and serialise it into the Parquet file footer or
  a sidecar index file. Standard approach; matches GeoParquet's
  row-group bbox metadata at coarse granularity, finer-grained
  via sidecar. Requires implementing a verified R-tree (build
  + query) in F*.
- **H3 / S2 cell-id Roaring index.** Discretise each geometry
  to a set of H3 cells (or S2 cells) at a chosen resolution,
  build a Roaring bitmap per cell ID listing the term-ids
  whose geometry touches that cell. A spatial query
  decomposes the query bbox / geometry into cells, ANDs the
  Roaring bitmaps for those cells, and yields a candidate
  set that is then filtered by exact predicate. This is how
  GeoMesa, Apache Sedona's broadcast-spatial-join, and
  SpatialHadoop work internally.

The Roaring + H3 approach has three things going for it in this
codebase:

- The Roaring infrastructure already exists in
  `formal/roaring/src/`. Adding spatial just adds one new
  bitmap-keying scheme alongside the existing presence
  bitmaps.
- H3 cell IDs are 64-bit integers, which is exactly the
  shape Roaring is built for. S2 cell IDs are also 64-bit.
- The predicate evaluator is already comfortable with
  "Roaring AND → candidate set → row-level filter" — it's
  the same shape as the existing presence-bitmap join path.

Cost: H3 / S2 cell decomposition itself is a CG operation
(rasterising a polygon onto a hierarchical grid). For points
it's trivial (one cell per point). For polygons it's the
hardest geometry-vs-grid intersection problem. **For v0,
restrict the spatial index to point geometries** (Wikidata,
sensor networks, GNAF-style addresses) and fall back to
sequential scan for polygon-typed data. This covers the
dominant real-world case at minimal CG verification cost.

### Roaring bitmaps (`formal/roaring/src/`)

Roaring isn't a spatial index per se — it's a sorted-int-set
representation. But spatial discretisation produces sorted
int sets (cell IDs). The existing `Container.Bitmap` /
`Container.Array` / `Container.Run` containers are the right
shape; the new code is in `RDF.Geo.Index.fst` and lives
*above* the Roaring layer.

Concrete plan: an `H3SpatialIndex` keyed by `(graph_id,
predicate_id, cell_id)` with the value being a Roaring bitmap
of subject term-ids. Query path: bbox → cell list (H3 has a
covering function) → Roaring OR over cells → candidate
subjects → row-level exact predicate filter. Build path:
on insert, geometry → H3 cell set → for each cell, set the
subject's bit in the per-cell Roaring bitmap. Bulk-load is
the same with a sort-then-build optimisation.

## Test viability

The OGC GeoSPARQL 1.1 conformance test suite is at
[opengeospatial/geosparql-tests](https://github.com/opengeospatial/geosparql-tests)
(canonical location at time of writing — verify before
vendoring). The 1.0 test suite is part of the W3C Spatial Data
on the Web archive at
`https://www.w3.org/2015/spatial/wiki/`. The 1.1 suite is the
current target.

Vendoring path: `third_party/testing/geosparql/` as a git
submodule, with manifest entries pointing at `tests/cite/`
or wherever the OGC harness puts the manifests. The runner
reads manifest, loads input dataset (`*.ttl`), runs query
(`*.rq`), compares results (`*.srx` or `*.csv`).

A `bin/geosparql_runner/` consumer (per CLAUDE.md rule #11
this lives outside the verified library, in `bin/`, exactly
like `w3c_runner`) reads the OGC manifest, invokes the
extracted SPARQL evaluator with GeoSPARQL extensions
enabled, and emits a pass / fail report. It must not contain
any semantic logic — manifest parsing, dataset loading,
query dispatch only.

A panel on the dashboard (per the existing dashboard
infrastructure) shows GeoSPARQL pass / fail counts with
labelled numerators and denominators (per anti-pattern #25:
"X pass, Y fail (out of Z)" — never bare `X/Z`).

## Sequenced rollout

| Phase | Deliverable | Backend impact | Effort |
|---|---|---|---|
| 1 | `Parser.WKT.fst` + `RDF.Geo.Types.fst` + `RDF.Geo.BBox.fst` | none — enables literal parsing only | M |
| 2 | DE-9IM Simple-Features predicates over in-mem (option A pure-rational); `geof:` dispatch in algebra evaluator; OGC test suite vendored; runner scaffolding | in-mem only; no index | L |
| 3 | In-mem spatial index (R-tree over bboxes, pure F\*); cheap functions (envelope, distance², area, length) | in-mem index module; no on-disk impact | L |
| 4 | GeoParquet read / emit on COTTAS path; geometry as WKB column | COTTAS gains a geometry column type and per-row-group bbox metadata | L |
| 5 | Spatial index on COTTAS: H3-keyed Roaring per (graph, predicate) for point geometries; sequential-scan fallback for polygon | COTTAS gains H3-Roaring index sidecar; index lives in F\*-verified module | L-XL |
| 6 | Hard CG functions (buffer / convexHull / true intersection-as-new-geometry / union / difference). Requires the option-A-vs-option-C decision. If option C: vendored GEOS via `assume val` boundary | adds a new vendored unverified surface; CRS still identity | XL |
| 7 | GeoJSON literal parser; CRS registry (EPSG codes, identity transform only); `geo:hasMetricArea` etc. derived properties | parser + dispatch only | M |
| 8 | DGGS literals (H3 / S2 cell-id strings as first-class geometry literals) | reuses phase-5 H3 path | M |
| 9 | Aggregate `geof:agg*` functions (centroid, bbox, union over a group) | extends algebra aggregates | M |
| 10 | GML literal parser; full Geometry profile conformance | parser only | M |

Aggregate effort: phases 1-3 (the v0 useful slice) are roughly
M + L + L = ~3000-5000 LoC of F\* plus tests, call it
3-6 weeks of focused F\* work. Phases 4-5 (COTTAS integration)
are L + L-XL = ~3000-6000 LoC, another 4-8 weeks. Phase 6 is
the wildcard: a few weeks if option C, multiple months if
option A pushed beyond its comfort zone.

## Done criteria (v0)

- OGC GeoSPARQL 1.1 test suite vendored under
  `third_party/testing/geosparql/`.
- `Parser.WKT.fst`, `RDF.Geo.Types.fst`, `RDF.Geo.BBox.fst`,
  `RDF.Geo.Topology.fst`, `RDF.Geo.Functions.fst` (cheap
  subset), `RDF.Geo.CRS.fst` (identity-only), `RDF.Geo.Index.fst`
  (R-tree) on `claude/main`, all verifying with no `--lax`
  per iron rule #10.
- `geof:` function-call dispatch wired into
  `SPARQL11.Algebra.evaluate_expr` via the existing
  `E_FunctionCall` constructor.
- `bin/geosparql_runner/` consumer reading OGC manifests;
  Core + Topology profile tests pass.
- Dashboard has a GeoSPARQL panel with labelled
  numerator/denominator score strings.

## What this does NOT do

- Doesn't write any code. This is a planning document.
- Doesn't commit to a CG verification strategy for phase 6 —
  the option A / B / C choice is an open question.
- Doesn't ratify GeoParquet adoption — that's a question for
  the COTTAS-Parquet plan owner.
- Doesn't address CRS transformations beyond identity. Real
  reprojection (EPSG:4326 → EPSG:27700 etc.) requires a CRS
  database and Helmert / projection math, which is an entire
  separate project (PROJ-equivalent in F\* is not on the
  table).

## Open questions

1. **CG verification strategy for phase 6.** Pure-rational
   F\* (option A, slow), assume-val to GEOS (option C,
   pragmatic but adds vendored unverified surface), or
   defer phase 6 indefinitely?
2. **Roaring + H3 vs R-tree footer for spatial indexing in
   COTTAS.** Roaring + H3 reuses existing infrastructure
   and aligns with the cell-id grain that GeoSPARQL 1.1's
   DGGS support will need anyway. R-tree is more textbook
   and slightly more selective on non-point geometries.
3. **GeoParquet adoption now (interop with Sedona / DuckDB /
   GDAL) vs custom geometry column?** GeoParquet means
   adopting the OGC-defined kv-metadata schema on Parquet
   files; this constrains future column-format choices
   somewhat but unlocks instant interop with the Python
   geo stack.
4. **WKT-only first? GeoJSON later? GML deferred indefinitely?**
   GML is the legacy serialisation; almost no production
   data uses GML literals in SPARQL, but it's required for
   1.0 conformance. GeoJSON is increasingly common
   (web-native).
5. **1.1 conformance level: Core only, Core + Topology,
   or Core + Topology + Geometry?** The recommendation here
   is Core + Topology + cheap Geometry subset; Geometry
   profile completeness depends on phase-6 outcome.
6. **Polygon support in the spatial index from day 1, or
   point-only?** Point-only covers Wikidata-style data and
   sidesteps polygon-vs-cell rasterisation. Polygon support
   needs a polygon-rasterise-to-cells routine, which is
   itself a CG operation.
7. **Index sharding by predicate?** Most spatial queries
   filter on `geo:hasGeometry`, but if multiple predicates
   carry geometries (e.g. `wdt:P625` for points,
   `wdt:P3896` for boundaries on Wikidata), a per-predicate
   index avoids cross-predicate noise.
8. **Should `geo:wktLiteral` literals be canonicalised at
   ingest** (`POINT(1.0 2.0)` → `POINT(1 2)`, whitespace
   normalised) or preserved bit-exact? Bit-exact is safer
   for round-trip but means duplicate literals can leak in.

## Rough effort estimate

Per module (using S/M/L/XL bands defined above):

- `Parser.WKT.fst` — M
- `RDF.Geo.Types.fst` — S
- `RDF.Geo.BBox.fst` — S
- `RDF.Geo.Topology.fst` — L
- `RDF.Geo.Functions.fst` (cheap subset) — M
- `RDF.Geo.CG.fst` (hard CG, phase 6) — L-XL
- `RDF.Geo.CRS.fst` (identity-only) — S
- `RDF.Geo.Index.fst` (R-tree over bboxes) — L
- `RDF.Geo.Index.fst` extension (H3-Roaring on COTTAS) — L
- `bin/geosparql_runner/` (manifest reader + dispatch) — S
- Test infrastructure + vendoring + dashboard panel — S

Aggregate by phase:

- Phases 1-3 (v0 useful slice): ~3-6 weeks F\* work.
- Phases 4-5 (COTTAS integration): ~4-8 weeks.
- Phase 6 (hard CG): few weeks (option C) to 6+ months (option A pushed hard).
- Phases 7-10 (parser breadth + aggregates + GML): ~6-10 weeks combined.

Total to "fully GeoSPARQL 1.1 conformant store, all profiles":
~6-12 months focused work, dominated by phase 6. Total to "useful
GeoSPARQL store covering Wikidata-style point data":
~2-3.5 months focused work (phases 1-5).

## Recommendation

Pursue, but at v0 depth (phases 1-5) only. The v0 slice is
tractable in F\* with option A pure-rational arithmetic, reuses
the existing `Parser.Combinators`, `SPARQL11.Algebra`
(`E_FunctionCall` already extensible), and Roaring containers,
and unlocks every production point-data SPARQL workload we care
about (Wikidata coordinates, sensor networks, transport graphs,
parliamentary boundaries reduced to centroid-points). Phase 6
should remain an open question pending a decision on host-CG
vendoring; phases 7-10 are pure spec breadth and can be
scheduled per-customer-demand.

Do not pursue if the user requires fully verified hard CG
operations (true polygon intersection / buffer / convexHull
constructed as new geometries) without a vendored host-CG
library — that path is multi-year and depends on F\* gaining
an IEEE-754 spec or a verified rational-bignum kernel that
doesn't blow up under composition.

## References

- OGC GeoSPARQL 1.1 (22-047r1, Sept 2024): see
  https://docs.ogc.org/is/22-047r1/22-047r1.html
- OGC GeoSPARQL test suite repo: see
  https://github.com/opengeospatial/geosparql-tests (verify
  current location before vendoring)
- GeoParquet specification: see https://geoparquet.org/
- Apache Sedona (reference Spark + Flink + Snowflake spatial
  engine, GeoParquet reader): see https://sedona.apache.org/
- GEOS (C port of JTS, candidate for option-C vendoring):
  see https://libgeos.org/
- S2 geometry library (Google, candidate for option-C
  vendoring): see http://s2geometry.io/
- H3 hierarchical hexagonal indexing (Uber, candidate for
  spatial discretisation): see https://h3geo.org/
- Shewchuk, "Adaptive Precision Floating-Point Arithmetic
  and Fast Robust Geometric Predicates" (1996) — the
  reference for option B robust floating-point CG.
- F\* rules + recovery context:
  [`docs/designissues/2026-05-07-query-planning-fstar-recovery.md`](2026-05-07-query-planning-fstar-recovery.md),
  [`docs/designissues/2026-05-07-io-verification-and-third-party.md`](2026-05-07-io-verification-and-third-party.md),
  [`docs/designissues/2026-05-07-c-build-and-roaring-plan.md`](2026-05-07-c-build-and-roaring-plan.md).
