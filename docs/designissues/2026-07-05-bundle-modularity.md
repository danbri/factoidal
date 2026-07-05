# 2026-07-05 — Bundle modularity: per-capability entry points for JS/wasm

## Status

Design proposal with a measured pilot. The pilot entry source is
parked at [`bin/npm-entry-core/entry_core_jsoo.ml`](../../bin/npm-entry-core/entry_core_jsoo.ml)
(compiles clean, smoke-tested under Node; not yet wired into
`build-ocaml.sh` — wiring lands with this design's implementation
wave). Owner directive: implemented standards must not force
consumers to load huge libraries for modest tasks.

## 1. The problem

Every JS/wasm consumer today downloads every capability. The npm
package's engine bundle `factoidal-npm-entry.js` links the full
extraction set — SPARQL parser + algebra + store, SHACL, ShEx, OWL,
RIF, JSON-LD, RDF/XML, RDFC-1.0, the COTTAS/Parquet storage layer —
even when the consumer only wants to parse a Turtle file.

Baselines as of this writing (all sizes from `wc -c`; gzip is
`gzip -9 | wc -c`):

| artifact | raw | gzip -9 |
|---|---|---|
| `docs/fstar-extracted/factoidal.js` (CLI bundle) | 622,428 B | 188,924 B |
| `docs/fstar-extracted/factoidal-npm-entry.js` (npm engine) | 476,558 B | 144,265 B |
| `factoidal-npm-entry.wasm.js` + `.wasm` asset | 43,629 + 503,790 B | 14,757 + 141,316 B |
| `factoidal.wasm.assets/*.wasm` | 706,125 B | 183,506 B |

## 2. The lever, measured

js_of_ocaml performs whole-program dead-code elimination per entry
point: what survives in the bundle is what the entry's `Js.export`
surface transitively reaches, at function granularity. So one
`.byte` per capability, each linking the same extracted `.ml` set,
yields bundles sized to their capability — no F\* or extraction
changes required.

Pilot: `bin/npm-entry-core/entry_core_jsoo.ml` exposes only
parse (Turtle/N-Triples/N-Quads/TriG) + serialize (sorted N-Quads,
pretty Turtle), reusing the exact export patterns of
`bin/npm-entry/entry_jsoo.ml`. Compiled 2026-07-05 in a scratch dir
with the same `ocamlfind ocamlc` + `js_of_ocaml` invocations as
build-ocaml.sh's `js` step (same package list, same stub files,
minus the fzstd/parquet shims since `Parquet_Footer` is not linked;
no `-custom` stub needed for the same reason).

| bundle | raw | gzip -9 | vs full entry (raw) |
|---|---|---|---|
| runtime floor (hello-world, same stubs) | 86,431 B | 27,190 B | 18% |
| **core pilot** `factoidal-npm-entry-core.js` | **190,367 B** | **59,318 B** | **40%** |
| full `factoidal-npm-entry.js` | 476,558 B | 144,265 B | 100% |

wasm_of_ocaml, same pilot bytecode (loader + single `.wasm` asset):

| bundle | raw | gzip -9 |
|---|---|---|
| core loader `.wasm.js` | 42,497 B | 14,218 B |
| core `.wasm` asset | 162,521 B | 50,541 B |
| full-entry loader `.wasm.js` | 43,629 B | 14,757 B |
| full-entry `.wasm` asset | 503,790 B | 141,316 B |

The core `.wasm` asset is 32% of the full entry's. (Pilot wasm was
not run through `wasm_stub_shims.py` and is a size measurement only;
the JS pilot is the one smoke-tested end to end.)

Summary: a parse/serialize consumer drops from 144 KB to 59 KB
gzipped over the wire, and evaluates 40% as much JS. The 86 KB
(27 KB gzipped) runtime floor — jsoo runtime + zarith bigint stubs —
is the irreducible per-entry cost and the argument for keeping the
number of entries modest rather than one-export-per-entry.

## 3. Per-capability entry matrix

Estimation model: `raw ≈ 86 KB floor + k × (linked extracted .ml
bytes reachable from the entry)`, with k ≈ 0.17 measured from the
pilot (104 KB of JS above floor from 621 KB of `.ml`) and k ≈ 0.13
from the full entry — DCE inside partially-used modules pulls the
effective k down as entries grow. Estimates below use k = 0.15 ± and
are stated to the nearest 10 KB; gzip ≈ 0.31 × raw (both measured
pairs agree). Module-group weights measured from
`ocaml-output/*.ml`: query stack 788 KB, SHACL+ShEx 298 KB,
OWL+RIF 205 KB, JSON-LD 209 KB, XML stack 109 KB, COTTAS 534 KB.

| entry | exports (ABI subset) | extra modules beyond core | est. raw | est. gzip |
|---|---|---|---|---|
| `core-parse` | parseToDatasetJson, serializeNQuads, serializeTurtle | — | **190 KB (measured)** | **59 KB (measured)** |
| `canonicalize` | core + canonicalizeToNQuads | RDFC-1.0 labelling half of RDF_Canonical + hash paths (already linked, DCE'd out of core) | ~220 KB | ~70 KB |
| `jsonld` | core + JSON-LD parse | Parser_JSON, JSONLD_{Loader,Context,Expand}, Parser_JSONLD (209 KB) | ~230 KB | ~70 KB |
| `query` | core + queryDataset, askDataset, updateDataset | SPARQL11_{Parser,Algebra,Store}, XSD_Datatypes, plan modules, results serializers (~850 KB) | ~320 KB | ~100 KB |
| `validate` | core + SHACL validate, ShEx validate | SHACL_Validation, ShEx_{Schema,Validation} (298 KB) + reachable slices of SPARQL11_{Parser,Algebra} (SPARQL-based constraints) | ~330 KB | ~100 KB |
| `reason` | core + RDFS/OWL closure, RIF eval | OWL_* + RIF_* (205 KB) + reachable slice of SPARQL11_Algebra | ~290 KB | ~90 KB |
| `full` | everything (today's ABI) | all of the above + RDF/XML + COTTAS | **477 KB (measured)** | **144 KB (measured)** |

Dependency notes (grepped from extracted `.ml`): SHACL_Validation
references SPARQL11_Parser + SPARQL11_Algebra; ShEx_Validation and
OWL_QueryRewrite/QueryEval reference SPARQL11_Algebra only; the
JSON-LD stack reaches only SPARQL11_IRI_Resolve, which is already in
core. Function-granular DCE means "references SPARQL11_Algebra" does
not cost the whole 340 KB module — only reachable functions — which
is why `validate` and `reason` estimates sit well under
core + their group + the full query stack. RDF/XML stays out of
every entry except `full` because Parser_RDFXML drags the XML
well-formedness stack (109 KB of `.ml`) for a format npm consumers
rarely feed us; revisit if telemetry disagrees.

The estimates are for planning; each entry gets measured when built
(§7 makes the measurement a CI artifact).

## 4. npm subpath exports

`npm/factoidal/package.json` already has an `exports` map (`.`,
`./wasm`, `./rdfjs`, `./fn`, `./browser`, `./browser-wasm`, plus
raw-asset passthroughs). Add per-capability subpaths, preserving the
default export exactly as it is:

```json
"./parse":        { "types": "./parse.d.ts",       "default": "./parse.js" },
"./query":        { "types": "./query.d.ts",       "default": "./query.js" },
"./validate":     { "types": "./validate.d.ts",    "default": "./validate.js" },
"./reason":       { "types": "./reason.d.ts",      "default": "./reason.js" },
"./canonicalize": { "types": "./canonicalize.d.ts","default": "./canonicalize.js" },
"./jsonld":       { "types": "./jsonld.d.ts",      "default": "./jsonld.js" }
```

Each wrapper (`parse.js`, …) is a thin `lib/api.js`-style adapter
over its engine bundle (`factoidal-npm-entry-core.js`, …), exposing
the same envelope-JSON ABI subset and the same rich rdfjs.js types.
`.` keeps loading the full bundle — zero breakage for existing
consumers; the subpaths are opt-in slimming. Every per-capability
ABI is a strict subset of the full ABI with identical envelope
shapes (the pilot already returns a routable
"use the full bundle" error for formats it excludes), so a consumer
can be moved between bundles without code changes.

## 5. wasm splitting

`wasm_of_ocaml` already emits one loader `.wasm.js` + hashed
`.wasm` asset(s) per entry, and the loader fetches its assets
lazily. Per-entry wasm therefore falls out of the same
one-byte-per-capability scheme: compile each `.byte` with
`wasm_of_ocaml compile` and ship each loader + asset dir as its own
subpath (`./parse-wasm`, mirroring today's `./browser-wasm`).
Measured above: the core entry's asset is 162 KB vs 504 KB —
same lever, slightly stronger (32% vs 40%). Assets are
content-hashed, so a CDN/service-worker caches shared bytes only if
identical — they will not be (different DCE per entry). Accept the
duplication; entries are small enough that it is cheaper than a
shared-chunk scheme jsoo does not support.

## 6. Browser incremental loading

`browser.js` today injects one script for the full bundle. Change to
dynamic import per capability: each capability accessor
(`factoidal.query(...)` etc.) lazily `import()`s its bundle on first
use and caches the module handle. First parse costs 59 KB gzipped;
SPARQL arrives only when a query is first issued. A
`preload(["query", "validate"])` hint covers latency-sensitive
apps. Same pattern for `browser-wasm.js`, where lazy asset fetch
already exists — the loader JS just becomes per-capability too.

## 7. What the foundational-core refactor contributes

[`2026-07-05-foundational-core-refactor.md`](2026-07-05-foundational-core-refactor.md)
splits `RDF.Graph.Executable` and `SPARQL11.Algebra` into
term/triple/graph vs evaluator vs closure modules. For bundling this
means: (a) `validate`/`reason` entries stop linking the evaluator
module at all instead of relying on function-level DCE inside a
340 KB module — module-level exclusion is verifiable in the link
line, DCE reachability is not; (b) the axiomatic-triple tables
(`RDF.Vocabulary.Axioms`) become data reachable only from closure
entries; (c) k drops toward the pilot's 0.17-on-clean-modules
figure for every entry. The refactor is not a prerequisite — the
pilot proves the win without it — but each landed slice tightens
the matrix above.

## 8. build-ocaml.sh additions (describe only, not implemented here)

Inside the existing `js` step, after the current `npm_entry.byte`
block: a loop over an `ENTRY_POINTS` array
(`core:bin/npm-entry-core/entry_core_jsoo.ml`, `query:…`, …) that
(1) runs the same `ocamlfind ocamlc -package …,js_of_ocaml -linkpkg`
invocation per entry — `-custom parquet_zstd_stubs_jsoo.c` and the
fzstd shims only for entries whose module set reaches
`Parquet_Footer`; (2) runs the same `js_of_ocaml` invocation to
`docs/fstar-extracted/factoidal-npm-entry-<name>.js`; (3) appends
each artifact to `JS_TARGETS`/`JS_SOURCES` so the freshness check
covers it. The `wasm-factoidal` step gets the mirror loop. The
npm-copy step copies each bundle + wasm asset dir into
`npm/factoidal/`. One `.byte` per entry adds roughly a minute each
to the js step; acceptable, and the freshness check skips them when
sources are unchanged.

## 9. CI size-budget gate

Extend the js step (or a separate `tools/bundle-sizes.sh`) to emit
`docs/test-results/bundle-sizes.json`: per entry, raw and gzip -9
bytes. CI compares against the committed previous values and fails
if any entry grows more than 10% without a
`bundle-size-note:` trailer in the commit message explaining the
growth. Shrinkage and sub-10% drift update the committed file
silently. This is the same measured-not-asserted discipline the
test suites use, applied to bytes on the wire.

## 10. Open decisions

1. Entry granularity: the six-entry matrix above, or fewer
   (core / query / everything-else)? Each entry re-pays the 27 KB
   gzipped runtime floor; six entries means ~160 KB of duplicated
   floor across a consumer that eventually loads everything.
2. Should `validate` split into `shacl` and `shex`? Grep says ShEx
   avoids SPARQL11_Parser entirely, so a shex-only entry would be
   noticeably smaller — but two more entries is two more floors.
3. Does `canonicalize` merit its own entry, or fold into
   `core-parse` (+~30 KB raw estimate) since RDFC-1.0 is a natural
   companion of serialization?
4. RDF/XML placement: full-bundle-only (as proposed), or its own
   `./rdfxml` subpath?
5. Per-entry ABI naming: keep one global `factoidalNpmEntry` name
   with per-bundle subsets (simplest for lib/api.js reuse), or
   per-entry names like the pilot's `factoidalNpmEntryCore`
   (collision-safe if two bundles load in one page)? Pilot chose
   the latter; the wrapper layer hides either.
6. Does the default `.` export ever flip to lazy per-capability
   loading (a breaking timing change for synchronous consumers), or
   stay eager-full forever?
7. Gate mechanics: 10%-per-entry as proposed, or also an absolute
   ceiling per entry (e.g. core-parse must stay under 256 KB raw)?
