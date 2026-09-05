# A geometry bounding-box index for block storage (GBI1)

Date: 2026-09-05.

Companion record: `docs/designissues/2026-09-04-literal-token-index.md`. GBI1
follows LGI1 exactly — a per-block sidecar, a candidate filter that never
decides a row, a superset theorem, and encoder admission equal to decoder
admission. Read that record first; this one states only what is different
because the data is geometry.

## 1. The problem

Six GeoSPARQL topology functions work today over a persisted store —
`geof:sfEquals`, `sfDisjoint`, `sfIntersects`, `sfTouches`, `sfWithin`,
`sfContains`, in `L4Factoidal/Geo/Functions.lean` over the WKT parser. A geo
`FILTER` is a full scan: every row is decoded, every `geo:wktLiteral` lexical
form is parsed into a `Geometry`, and the topology algorithm runs on it.

The parse is the expensive part. A polygon of 200 vertices costs 200 decimal
parses before any predicate is evaluated, and the scan pays that for every row
whether or not the row can possibly answer.

## 2. What is indexed

**The axis-aligned bounding box of every `geo:wktLiteral` term in the block
dictionary, plus that term's CRS.**

* The box is `L4Factoidal.Geo.BBox`, computed from the parsed geometry's
  vertices. `BBox.lean` is not restated here; the index calls it.
* Coordinates stay EXACT. A box is four `Scaled` decimals, not four floats.
  A float box would need an outward rounding rule to stay conservative, and a
  wrong rounding direction is exactly the silent-row-loss failure.
* A term whose geometry is outside the PROVED FRAGMENT has no box. It is
  recorded as OPAQUE and is always a candidate — the index never excludes a
  row whose geometry its proof does not reach. The fragment is a point, and a
  polygon whose exterior ring and holes are all closed; section 5 says why a
  linestring is not in it yet.
* A term that is not a `geo:wktLiteral`, or whose lexical form does not parse,
  is in neither list and is never a candidate. `Geo.geoPredicate` answers
  `none` for it, a `none` is a §17.6 type error, and an error drops the row.
* The CRS is stored as an index into a per-sidecar string table, with 0
  meaning the default CRS84. `Geo.geoPredicate` refuses a cross-CRS pair with
  `none`, and a `none` is a §17.6 type error, so such a row is never accepted
  by the filter. Excluding it up front is therefore sound and free.

The unit is the dictionary term, not the row, so a repeated geometry is
parsed and boxed once. Local term IDs are the PTD1 dictionary positions TLI1
and LGI1 use, so a candidate reaches rows through the existing OLI2 object
index with no second identity scheme.

## 3. The asymmetry, and it is the whole design

A bounding box is a CONSERVATIVE approximation of a geometry: every point of
the geometry is in the box, and the box holds points the geometry does not.

    boxes do not overlap  =>  the geometries cannot share a point
    boxes overlap         =>  nothing follows

**A box can exclude. A box can never confirm.** Reading that backwards
returns rows the query does not license, silently. The index is therefore a
candidate filter: it returns a superset of the terms the `FILTER` accepts and
the planner re-evaluates the original, unmodified expression on the
candidates. Rows are the scan's rows by construction.

## 4. Which of the six a box can filter, one at a time

The query shape is `geof:sfX(?geo, Q)` with `Q` a constant `geo:wktLiteral`
and `?geo` bound in object position by one triple pattern. `B(g)` is the box
of `g`.

| function | box test | why |
|---|---|---|
| `sfIntersects(?geo, Q)` | `overlaps B(?geo) B(Q)` | `some true` means the two share a point; that point is in both boxes, so the boxes overlap. Non-overlapping boxes cannot be accepted. |
| `sfWithin(?geo, Q)` | `overlaps B(?geo) B(Q)` | within implies intersecting for a non-empty row geometry, so the same exclusion holds. The stronger test `B(?geo)` inside `B(Q)` is NOT used: it is not implied, because a box corner of the row need not lie in `Q`. |
| `sfContains(?geo, Q)` | `overlaps B(?geo) B(Q)` | `sfContains g Q` is `sfWithin Q g`; the same shared-point argument, with the roles swapped. |
| `sfTouches(?geo, Q)` | `overlaps B(?geo) B(Q)` | touching is meeting at a boundary point, which is still a shared point. |
| `sfEquals(?geo, Q)` | `overlaps B(?geo) B(Q)` | equal non-empty geometries share every point. The boxes are in fact equal, but `overlaps` is what the one theorem gives and a weaker test cannot be unsound. |
| `sfDisjoint(?geo, Q)` | **none — falls back to the scan** | see below. |

### 4.1 `sfDisjoint`, and why a box does not help

`sfDisjoint g Q` is `some true` exactly when `sfIntersects g Q` is
`some false`. The rows it accepts are the rows that do NOT share a point with
`Q`, and non-overlapping boxes are the strongest evidence of that.

So the box test is not merely unhelpful, it is inverted. The set of rows a
box can exclude for `sfIntersects` — the non-overlapping ones — is a subset
of the rows `sfDisjoint` ACCEPTS. Filtering on `overlaps` would drop
answers. Filtering on `!overlaps` would drop the answers among the
overlapping boxes, which are also real: two geometries with overlapping boxes
are usually still disjoint.

There is a sound use of the box here, and it is not a candidate filter: a
non-overlapping box pair PROVES `sfDisjoint` is `some true`, so the topology
test can be skipped and the row admitted directly. That is a per-row cost
saving inside a scan that still visits every row — it does not reduce the
candidate set, it does not make a miss cheap, and it needs its own theorem in
the opposite direction (`¬overlaps → sfDisjoint = some true`, a completeness
claim about the topology algorithm rather than the soundness claim this
record proves). It is out of scope here, and GBI1 declines to serve
`sfDisjoint` at all.

The general rule the table follows: **a box serves a predicate whose truth
requires a shared point, and no other.** Five of the six require one.
`sfDisjoint` requires the absence of one.

### 4.2 What else falls back to the scan

| case | why |
|---|---|
| `Q` not a constant `geo:wktLiteral`, or it does not parse | no query box at plan time |
| `Q` empty, or the row term unboxed | `BBox.ofGeometry` is `none`; nothing to compare |
| `!geof:sfX(...)` | the complement of a superset is not a superset |
| `geof:sfX(...)` under `\|\|` | one disjunct being false does not exclude the row |
| a variable the pattern does not bind in object position | no entry applies |
| the query geometry is a linestring, a `Multi*`, a `GeometryCollection`, an empty, or a polygon with an open ring | outside the proved fragment; `fragmentBox` is `none` |
| the block has no `.gbi1` sidecar | old generations keep answering |
| `geof:sfDisjoint` | section 4.1 |

Every rejection is load-bearing in the `StoreFastPath` sense: matching a shape
the index cannot serve is the only failure mode, and each row above is a shape
that would be mis-served.

## 5. The superset theorem

`Storage/GeoBBoxIndex.lean`, in the shape of `LiteralGramIndex`'s
`mem_candidatesSpec`:

    theorem mem_candidatesSpec
      (dict : Array Term) (op : GeoOp) (query : WktValue)
      (i : Nat) (t : Term) (ids : List Nat)
      (hop    : op ≠ GeoOp.disjoint)
      (hget   : dict.toList[i]? = some t)
      (hmatch : evalTerm op t query = some true)
      (hc     : candidatesSpec dict op query = some ids)
      : i ∈ ids

Read: a dictionary term the exact predicate accepts is always a candidate.
`evalTerm` reaches the SAME `Geo.sfIntersects` / `sfWithin` / … the evaluator
calls, through the same datatype gate and the same `Geo.sameCrs` guard, and
does not restate any of them. `#guard`s in the module compare it against
`Geo.extFns` on six pairs, so a change to `Geo.geoPredicate` breaks the build
rather than the index.

The geometric step under it is `exists_common_point`: two fragment geometries
a served predicate accepts have a point BOTH boxes contain. `sfDisjoint` is
excluded there by hypothesis, and the polygon-to-polygon case is discharged
because every base predicate REFUSES that pair — `Geo.Topology` answers
`none`, never `some true`.

The geometric content is in `Geo/BBoxSound.lean`. Two facts carry it.

1. **`ofPoints_mem`** — the box of a point list contains every point of the
   list. A `foldl` monotonicity argument.
2. **`polygonClass_interior_contains`** — a point the ray-casting
   point-in-polygon test calls INTERIOR lies in the polygon's box.

The second is the one that is not obvious, and it is proved rather than
assumed, because the whole `sfWithin`-against-a-polygon case rests on it:

* An interior point has an odd crossing count, so at least one edge crosses.
  A crossing edge straddles the horizontal line `y = p.y`, which puts one
  endpoint above `p.y` and the other at or below it. Both `y` bounds follow
  from that alone.
* If `p.x` were strictly greater than every vertex `x`, then for every
  straddling edge the orientation determinant takes the sign the crossing
  test rejects, so the count would be ZERO — even, not odd.
* If `p.x` were strictly less than every vertex `x`, then every straddling
  edge crosses, so the count equals the number of straddling edges. On a
  CLOSED ring that number is even, because the predicate `y > p.y` returns to
  its starting value. Even, not odd.

Both sign steps are one signed-area identity evaluated at a common decimal
scale: with `p` strictly left of the edge, `orient a b p = v*A + u*(b.y-p.y)`
with `u, v > 0`; with `p` strictly right, `orient a b p = u*(p.y-b.y) - v*A`.
`Scaled.at'` carries `sub` and `mul` to integers at a shared scale so the
signs are ordinary integer arithmetic.

The closed-ring hypothesis is discharged, not assumed: `inFragment` checks
`isClosedLine` on the query polygon's rings at plan time, which is a WKT
convention every conforming polygon literal satisfies and costs one pass.

`fragmentBox` names what the proof does NOT yet cover, so those geometries
are opaque instead of being filtered wrongly. The open obligation is the
four-orientation proper-crossing rule (`segmentsIntersect` returning true
through `o1 != o2 && o3 != o4`, which carries no `inSegBBox` conjunct) and
the linestring cases built on it. They are true and they need the
separating-axis argument; until that is proved, a linestring carries no box.
Compound geometries are opaque for a second reason: `Geo.Topology.components`
is a `partial def`, so no proof can see through it.

## 6. The wire format

A sidecar beside `.lgi1`, `.tli1`, `.sri2` and `.oli2`, in the same framing:
fixed prefix, payload, CRC-32C.

    file  <block>.gbi1
    magic "GBI1", 0x31494247 little endian
    version 1

    prefix (fixed, 61 bytes)
      u32   magic
      u8    version
      [32]  targetIBKSha256
      u32   dictCount        -- the bound every ID is below
      u32   entryCount       -- boxed dictionary terms
      u32   opaqueCount      -- parseable terms outside the fragment
      u32   crsCount         -- CRS table entries
      u32   crsBytes
      u32   entriesBytes

    crs table (crsCount entries, in table order; index 0 is NOT stored and
               always means the default CRS84)
      u32   byteLength
      [..]  the CRS IRI, UTF-8

    entries (entryCount, strictly ascending by local term ID)
      u32   localTermId
      u32   crsIndex          -- 0 = default CRS84
      4 x { u64 mantissa two's complement, u8 scale }   -- xmin ymin xmax ymax

    opaque ids (opaqueCount, strictly ascending u32)

    u32   crc32c(payload)

An entry is 4 + 4 + 4*9 = 44 bytes, fixed. Fixed width is deliberate: the
lookup is a linear pass over the entry array comparing four decimals, and a
variable-length entry would make that pass parse before it can compare. A
term with no box is absent from the entry array and present in the opaque-ID
array, which is where "always a candidate" is recorded. A term in NEITHER
array is not a geometry at all and is never a candidate.

`supported` is the encoder gate; `decode?` re-runs every one of its
conditions — both ID lists strictly ascending and below `dictCount`, every
scale below 256, every mantissa inside the signed 64-bit range, every CRS
index at most `crsCount`, `xmin <= xmax`, `ymin <= ymax`, and the extents
covering the payload exactly. There are TWO readers, so unlike LGI1 the equality IS
claimed: `decodeSpec?` over `List UInt8` states what GBI1 admits, `decode?`
reads the artifact by byte-array index, and `decode_eq_spec` proves they
agree on every input.

## 7. Size and speed, measured

`l4block-geo-bbox` (`Harness/GeoBBoxProbe.lean`) on a generated IBK4 block of
40,000 `geo:asWKT` triples — points and small square polygons scattered over a
1000 by 1000 square. The fixture and its generator are deleted after the
measurement; the probe reprints every number on any regenerated fixture.

| part | measured |
|---|---|
| block | 5,871,740 bytes, 40,000 rows |
| dictionary | 80,001 terms |
| boxed terms | 40,000 |
| opaque terms | 0 |
| GBI1 bytes | 1,760,065, **30% of the block**, 44 bytes per row |
| index build | 173 ms, at pack time only |
| GBI1 round trip | the decoded index equals the built one |

Answering the filter through the DECODED artifact, not only through `build`.
Best of five.

| query | rows | scan | index | ratio |
|---|---|---|---|---|
| `sfWithin` a 20x20 polygon | 14 | 304,296 us | 5,903 us | 51x |
| **`sfWithin` a polygon over empty space (MISS)** | **0** | **311,693 us** | **7,762 us** | **40x** |
| `sfIntersects` the same 20x20 polygon | 14 | 305,822 us | 5,585 us | 55x |
| `sfDisjoint` the same polygon | 31,986 | 316,013 us | index not used, falls back | 1x |
| `sfWithin` a LINESTRING query | 0 | 178,310 us | index not used, falls back | 1x |

The rows returned through the index equal the rows returned by the scan for
every query, compared as row lists.

The MISS costs 40x less than the scan and NOT more, because the entry array is
flat: the lookup still compares the query box against all 40,000 entry boxes,
it only stops paying the WKT parse and the topology test. A single hull box
over the whole index would make a miss constant-time, and it needs one
monotonicity lemma (`e.box` inside the hull implies `overlaps e.box q` implies
`overlaps hull q`) plus a wire field. That is the named next step; it is not
landed here.

The 30% is the price of exact decimals at a fixed width. A `Scaled` costs 9
bytes whatever its magnitude, and a box costs four of them.

## 8. Manifest, packer, planner — landed 2026-09-05

GBI1 is a fifth sidecar role. It reached the shipped query path the way LGI1
did, in the same four files.

### 8.1 SBM9

Manifest wire version 9, layout label `quad-ibk4-ptd1-lgi1-gbi1-merkle-v0`.
The entry gains `geoIndex : Option ArtifactRef`, carrying the sidecar's key,
extent, SHA-256 and its own Merkle chunk commitment, written immediately
after the LGI1 sidecar and before the quad tail.

The version bump was unavoidable for the reason SBM8's was: a new per-entry
field changes the byte sequence whether it is mandatory or optional, so
encoder admission equals decoder admission only at a new version. The role is
MANDATORY at 9 and ABSENT below it. A block whose dictionary holds no
geometry carries a GBI1 with no entry rather than no sidecar, so an SBM9
reader never asks whether the role is present; it asks whether the manifest
is SBM9.

`ShardManifestTheorems.decodeEntry_encodeEntry_quadGeo` proves the SBM9 entry
round trip and `decode?_encode?` covers version 9, with the same statement and
the same three axioms: `propext`, `Classical.choice`, `Quot.sound`.

One structural note for whoever adds a sixth role. The literal and geometry
sidecars are ONE conjunct of `entryValid` and of `encodableEntry`, not two.
Every proof in `ShardManifestTheorems` reaches a conjunct through a chain of
`andL`/`andR`, so a new conjunct renumbers every proof that reads an earlier
one. Pairing the two roles kept those proofs unchanged.

### 8.2 The packer and activation

`l4block-shard-pack` writes `.gbi1` beside every IBK4 block and commits its
SHA-256 and Merkle root. The IBK4 block bytes are unchanged: the five blocks
of the section 8.4 fixture compare equal with `cmp` against the same corpus
packed as SBM8.

`GenerationVerify.geoIndexAgrees` checks the sidecar's own framing and CRC,
that it names THIS block by `targetIBKSha256`, and that its `dictCount` is
this block's dictionary size. It does NOT recompute the boxes, for the reason
`literalIndexAgrees` does not recompute the postings: rebuilding parses every
`geo:wktLiteral` again, which is the whole cost the index removes. What that
leaves uncaught is a PACKER fault that wrote a self-consistent index of the
wrong content; tampering after the pack is caught by the digest, and the
consequence of such a fault is bounded because the index is a candidate
filter and the planner re-evaluates the original expression, so a wrong index
can only DROP rows, never add them. Recomputing the boxes is open work.

### 8.3 The planner

`Storage/GeoIndexPlan.lean` decides which shapes the index may serve. It is
`LiteralIndexPlan` with a geometry in place of a needle, and it admits the
section 4 shape and nothing else.

Two decisions the literal planner did not have to make.

* **The argument order is read, not assumed.** `geof:sfWithin(?geo, Q)` and
  `geof:sfWithin(Q, ?geo)` are different predicates. The index judges a term
  by `evalTerm op t query`, which is `op.fn t Q` with the ROW geometry first,
  so a query that writes the constant first is served by the CONVERSE
  operation: `sfWithin` and `sfContains` swap, the other three are symmetric
  in Simple Features. The converse table is pinned against `Geo.extFns` on
  six pairs rather than asserted.
* **A wrapped object argument is refused.** `LiteralIndexPlan` admits `STR`
  and `LCASE` around the object variable; `GeoIndexPlan` admits neither.
  `Geo.wktArg` accepts only a `geo:wktLiteral` TERM, so a wrapped argument is
  a §17.6 type error and the row is excluded either way.

`Wasm/Ops/StoreHandles.lean` uses the answer. `storeOpen` retains the decoded
sidecar; `RetainedLiteralIndex` became `RetainedIndexes` with both roles
optional, so the two indexes share one copy of the row array, the
object-ID-to-row map and the non-literal row list — they index the SAME local
dictionary IDs. `storeHandleQuery` tries the literal plan and then the
geometry plan, materialises the candidate rows, and evaluates the ORIGINAL
query text over them. The geometry path keeps no non-literal row, because the
type error above already excludes it.

### 8.4 Measured through the shipped path

`l4block-geo-gate` (`Harness/GeoGate.lean`) opens one generation twice — one
handle with the sidecars, one without — answers the same query text on both,
and compares the two envelopes byte for byte.

The fixture is 40,000 `geo:asWKT` quads in one named graph, alternating
points and 0.5 by 0.5 squares over a 1000 by 1000 square, packed as SBM9:
5 blocks, 6,165,390 block bytes. The fixture and its generator are deleted
after the measurement.

    SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s geo:asWKT ?o
      FILTER(geof:sfX(?o, "<query>"^^geo:wktLiteral)) } } ORDER BY ?g ?s ?o

Best of five, through `storeHandleQuery`.

| query | rows | scan | index | ratio |
|---|---|---|---|---|
| `sfWithin` a 20x20 polygon | 5 | 1,088,925 us | 14,811 us | 74x |
| **`sfWithin` a polygon over empty space (MISS)** | **0** | **1,129,317 us** | **13,791 us** | **82x** |
| `sfIntersects` the same 20x20 polygon | 5 | 1,116,485 us | 11,911 us | 94x |
| `sfDisjoint` the same polygon | 19,995 | 6,612,149 us | 6,726,590 us | 1x, falls back |
| `sfWithin` a LINESTRING query | 0 | 824,067 us | 765,988 us | 1x, falls back |

Row identity: 5 pass, 0 fail (out of 5), compared as whole answer envelopes.

`sfDisjoint` answers 19,995 rows through the scan on both handles, which is
the section 4.1 refusal working: the index declines and the answer is
unchanged.

Old generations are unaffected. `factoidal-skoscross` and
`factoidal-skosgraphs` are SBM7 generations that declare no sidecar at all;
both answer through `storeHandleQuery` with the index path falling back
silently, 5 pass, 0 fail (out of 5) between them. The same fixture packed as
SBM8 — LGI1 present, no GBI1 — answers the same `sfWithin` by scanning, with
the same 5 rows: 1 pass, 0 fail (out of 1).

`tests/store-host/cli.mjs` compares the wasm command against the native tool
over a natively packed generation, so it fails until the wasm module is
rebuilt: the committed module answers `bytes do not decode as an admitted
SBM0 to SBM7 manifest`. That message names the whole cause. The native path
is the evidence until the rebuild lands.

### 8.5 Pack time and generation size

Same 40,000-quad input, same 5 blocks, packed twice.

| | SBM8 (before) | SBM9 (after) |
|---|---|---|
| pack time | 15.6 s | 17.5 s |
| block bytes | 6,165,390 | 6,165,390 |
| LGI1 bytes | 3,948,582 | 3,948,582 |
| GBI1 bytes | 0 | 1,760,281 |
| GBI1 Merkle bytes | 0 | 992 |
| generation on disk | 9,944 KiB | 11,696 KiB |

The GBI1 sidecar is 28.6% of the block bytes and the generation grows by
17.6%. The 44-byte fixed-width entry of section 6 is the whole cost.

### 8.6 The planner widening that limits this today

A `geof:` FILTER selects EVERY block of a generation, not the block of the
bound predicate. `Expr.backendLocal` excludes every `functionCall`, so
`ShardManifest.quadNativeConstantPredicates?` answers `none` for such a
filter and `quadEntriesForQuery` then keeps every entry. Measured on the
`factoidal-skosgraphs` manifest, 119 entries: a `geof:sfWithin` FILTER over
`skos:prefLabel` selects **119 blocks**; the same query with a `CONTAINS`
FILTER selects **1**. This is
<https://github.com/danbri/factoidal/issues/656>.

The consequence for GBI1 is exact. `storeHandleQuery` restricts rows only
when EVERY planned block carries the plan's predicate, so on a
multi-predicate generation the widening makes the geometry path fall back to
the scan every time. The section 8.4 numbers are real because that fixture
holds ONE predicate, so the widened selection is still that predicate's five
blocks. GBI1 needs issue 656 fixed before it can help a mixed store. Nothing
here works around it.

## 9. What this is NOT

* **Not an R-tree.** There is no tree, no split heuristic, no node fanout.
  The entry array is flat and the lookup is a linear pass over 44-byte
  entries. That is far cheaper per row than decode-plus-parse-plus-topology,
  and it is what makes the miss fast; it is not asymptotically better than
  the scan and does not claim to be. A tree, a Hilbert or Z-order curve over
  the entries, or a grid, are each a later decision with their own theorem.
* **Not a spatial ordering.** Entries are sorted by local term ID, the order
  the other sidecars use, so a candidate list is already ascending for the
  OLI2 join.
* **Not CRS handling.** No coordinate transform is performed, here or
  anywhere in the Lean geo tree. The index stores the CRS the WKT literal
  declared and uses it only to exclude rows the evaluator would refuse
  anyway. Two boxes in different CRSes are never compared.
* **Not a distance or nearest-neighbour index.** `geof:distance` and the
  buffer and relate families are not in the tree, and a box does not bound a
  distance without a metric on the CRS.
