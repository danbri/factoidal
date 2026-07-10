# docs/web/hub/assets/geo/ — vendored vector basemap

Two small GeoJSON files, vendored for the GeoSPARQL hub post
(`docs/web/hub/21-geosparql-geometry-and-topology.md`) to give its
Leaflet map a real, same-origin basemap. Task #105: the strict hub's
Content-Security-Policy is `self`-only by design (no CDN, no external
tile hosts), so the map has no raster tile layer — this vector data is
what makes the strict page "read as a real place" without any network
request.

## Files

| File | Content | Size |
|---|---|---|
| `london-boroughs.geojson` | 33 features — the 32 London boroughs + the City of London, as `Polygon`/`MultiPolygon` | 67,632 bytes |
| `thames.geojson` | 1 feature — the River Thames through Greater London, as a `LineString` | 1,187 bytes |

Total: **68,819 bytes** (~67 KB), under the ~300 KB target.

## Sources

### `london-boroughs.geojson`

- **Source**: ONS Open Geography Portal — *Local Authority Districts
  (May 2024) Boundaries UK BGC* (Boundary Generalised, Clipped),
  `LAD_MAY_2024_UK_BGC` feature layer.
  Service: `https://services1.arcgis.com/ESMARspQHYMw9BZ9/arcgis/rest/services/Local_Authority_Districts_May_2024_Boundaries_UK_BGC/FeatureServer/0`
- **Filter applied at query time**: `LAD24CD LIKE 'E09%'` — the ONS
  code prefix reserved for the 33 London boroughs (32 boroughs + the
  City of London), via the service's own `query` endpoint
  (`outFields=LAD24CD,LAD24NM&outSR=4326&geometryPrecision=4&f=geojson`).
- **Licence**: Open Government Licence v3.0 (OGL v3). Contains OS
  data © Crown copyright and database right 2024; contains ONS data
  © Crown copyright and database right 2024. See
  <https://www.ons.gov.uk/methodology/geography/licences> and
  <https://www.nationalarchives.gov.uk/doc/open-government-licence/version/3/>.
- **Retrieved**: 2026-07-10.
- **Simplification applied**: the ONS BGC layer is already generalised
  (20 m tolerance) for the whole UK. It was additionally simplified
  here with a pure-Python Douglas-Peucker pass (no `mapshaper`/`ogr2ogr`/
  `shapely` available in this environment; a one-shot script, not
  shipped) at ε = 0.0005° (~40–55 m at London's latitude), then
  coordinates rounded to 5 decimal places (~1.1 m). Point count:
  12,670 → 7,242 across the 33 features. Each ring was simplified
  independently, so a shared administrative border between two
  neighbouring boroughs is **not guaranteed to coincide exactly**
  after simplification (small gaps/slivers are possible along shared
  edges) — acceptable for this post's schematic, illustrative map;
  not suitable for any boundary-precision use.
- **Properties kept**: `code` (ONS `LAD24CD`), `name` (ONS `LAD24NM`).
  All other ONS fields (`Shape__Area`, `Shape__Length`, etc.) were
  dropped as unused.

### `thames.geojson`

- **Source**: Natural Earth, `ne_10m_rivers_lake_centerlines`
  (1:10m vector data set), the `Thames` feature
  (`name` = `"Thames"`, `rivernum` = 302).
  Mirror used: `https://github.com/nvkelso/natural-earth-vector`
  (`geojson/ne_10m_rivers_lake_centerlines.geojson`), which republishes
  the same public-domain Natural Earth data as plain GeoJSON.
- **Licence**: Public domain (Natural Earth places no restrictions on
  use — see <https://www.naturalearthdata.com/about/terms-of-use/>).
  No attribution required; a courtesy credit is enough:
  "Made with Natural Earth."
- **Retrieved**: 2026-07-10.
- **Simplification applied**: the source `MultiLineString` (152
  vertices, England-wide) was clipped to the points falling inside the
  bounding box `lon ∈ [-0.55, 0.40], lat ∈ [51.25, 51.72]` (Greater
  London plus a small margin so the line still reaches the map edge
  cleanly), producing a single `LineString` of 54 vertices. Coordinates
  rounded to 5 decimal places. No further Douglas-Peucker pass was
  needed at that vertex count.
- Because Natural Earth's 1:10m scale is a coarse cartographic
  generalisation to begin with, this line traces the Thames's overall
  course through London (its meanders past Westminster, the Isle of
  Dogs, Greenwich, etc. are all still visible) but is **not** a
  survey-accurate centerline — it is drawn for the same schematic,
  "this map reads as a real place" purpose as the borough polygons,
  not for any measurement.

## Why two sources for one basemap

ONS/OS Open Geography (administrative boundaries) does not publish
hydrology; Natural Earth (global cartographic reference data) does not
publish UK sub-national administrative boundaries at a useful scale.
Both sources are open (OGL v3 / public domain respectively), both
are used here read-only and unmodified beyond simplification and a
bounding-box clip — no derived-data relicensing question arises for
either.

## Integrity

Recompute and compare before trusting a checkout:

```sh
sha256sum docs/web/hub/assets/geo/london-boroughs.geojson \
          docs/web/hub/assets/geo/thames.geojson
```

| File | sha256 |
|---|---|
| `london-boroughs.geojson` | `a0f3e434e41d6f3590699954bf14c3ab9f84b4071a428d02f371bcd22a827b70` |
| `thames.geojson` | `b0d798b779d26772652164421141a6f21fa0e8f510375532d8d456e02d260cc9` |

## Serving

`docs/.eleventy.js` passthrough-copies this directory (see the
`web/hub/assets/geo` entry) so the post's map cell can `fetch()` both
files same-origin at `./assets/geo/london-boroughs.geojson` and
`./assets/geo/thames.geojson` relative to the post's own URL — no CDN,
consistent with `third_party/leaflet/PROVENANCE.md` and
`third_party/observable/README.md`'s no-CDN policy.
