# third_party/leaflet/

Vendored copy of [Leaflet](https://leafletjs.com/), the JS mapping
library, for rendering a live map on the documentation hub's
GeoSPARQL post (`docs/web/hub/21-geosparql-geometry-and-topology.md`)
— served same-origin from GitHub Pages, no CDN. Same constraint that
already governs `third_party/observable/` (see its README) and
`npm/factoidal/browser.js`: fetching code from `unpkg.com` or any
other CDN at page-load time is not acceptable here.

## What's vendored

| File | Source | Version | Notes |
|---|---|---|---|
| `leaflet.js` | `leaflet` npm package, `dist/leaflet.js` | 1.9.4 | Upstream's own prebuilt UMD bundle (unmodified) — sets `window.L` when loaded as a classic `<script>`. Not re-bundled here; Leaflet's own dist build is already a single self-contained file. |
| `leaflet.css` | `leaflet` npm package, `dist/leaflet.css` | 1.9.4 | Upstream's own prebuilt stylesheet (unmodified). |

Fetched via `npm pack leaflet@1.9.4` and extracted; both files are
copied byte-for-byte from the package's `dist/` directory.

**Deliberately NOT vendored:** `dist/images/*.png` (the default
marker icon, its 2x variant, the shadow, and the layers-control
icons). The hub's map cell uses vector-only markers
(`L.circleMarker` / `L.geoJSON` with a `style`) and no layers
control, so nothing on the page ever requests those images — see
the "No marker-image dependencies" note in the hub post's map cell
for why (Leaflet's default marker PNGs 404 unless `L.Icon.Default`'s
`imagePath` is configured, and configuring it just to serve
unused images was judged not worth it for an image-free, offline-
clean page).

## Versions and integrity

| File | sha256 |
|---|---|
| `leaflet.js` | `db49d009c841f5ca34a888c96511ae936fd9f5533e90d8b2c4d57596f4e5641a` |
| `leaflet.css` | `a7837102824184820dfa198d1ebcd109ff6d0ff9a2672a074b9a1b4d147d04c6` |

Recompute with `sha256sum third_party/leaflet/leaflet.js
third_party/leaflet/leaflet.css` and compare against this table
before trusting a checkout.

## License

BSD 2-Clause. Full text in `LICENSE` (copied verbatim from the
upstream package): Copyright (c) 2010-2023 Volodymyr Agafonkin,
Copyright (c) 2010-2011 CloudMade.

## Serving

`docs/.eleventy.js` passthrough-copies this directory to
`/vendor/leaflet/` (same pattern as the `third_party/observable/`
passthrough to `/vendor/observable/`), so the hub layout
(`docs/_includes/hub.njk`) loads `leaflet.css` via a same-origin
`<link>` and `leaflet.js` via a same-origin classic `<script>` in
the page head.
