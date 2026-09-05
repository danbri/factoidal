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
* A term whose lexical form does not parse, or whose geometry is empty, has
  NO box. It is absent from the index and is always a candidate — the index
  never excludes a row it failed to understand.
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
| the block has no `.gbi1` sidecar | old generations keep answering |
| `geof:sfDisjoint` | section 4.1 |

Every rejection is load-bearing in the `StoreFastPath` sense: matching a shape
the index cannot serve is the only failure mode, and each row above is a shape
that would be mis-served.

## 5. The superset theorem

`Storage/GeoBBoxIndex.lean`, in the shape of `LiteralGramIndex`'s
`mem_candidatesSpec`:

    theorem mem_candidatesSpec
      (dict : Array Term) (op : GeoOp) (query : WktValue) (i : Nat) (t : Term)
      (hget   : dict.toList[i]? = some t)
      (hfrag  : inFragment op query = true)
      (hmatch : evalOp op t query = some true)
      (hc     : candidatesSpec dict op query = some ids)
      : i ∈ ids

Read: a dictionary term the exact predicate accepts is always a candidate.
`evalOp` reaches the SAME `Geo.sfIntersects` / `sfWithin` / … the evaluator
calls, through the same `Geo.wktArg` and the same `Geo.sameCrs` guard, and
does not restate any of them.

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

`inFragment` also names what the proof does NOT yet cover, so those shapes
scan instead of being served wrongly. The open obligation is the
four-orientation proper-crossing rule (`segmentsIntersect` returning true
through `o1 != o2 && o3 != o4`, which carries no `inSegBBox` conjunct) and
the linestring-to-linestring and linestring-to-polygon cases built on it.
They are true and they need the separating-axis argument; until that is
proved, `inFragment` admits only query geometries whose components are
points and polygons.

## 6. The wire format

A sidecar beside `.lgi1`, `.tli1`, `.sri2` and `.oli2`, in the same framing:
fixed prefix, payload, CRC-32C.

    file  <block>.gbi1
    magic "GBI1", 0x31494247 little endian
    version 1

    prefix (fixed, 57 bytes)
      u32   magic
      u8    version
      [32]  targetIBKSha256
      u32   dictCount        -- the bound every entry ID is below
      u32   entryCount       -- boxed dictionary terms
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

    u32   crc32c(payload)

An entry is 4 + 4 + 4*9 = 44 bytes, fixed. Fixed width is deliberate: the
lookup is a linear pass over the entry array comparing four decimals, and a
variable-length entry would make that pass parse before it can compare. A
term with no box is absent from the array, and absence means "always a
candidate", so the array holds only the terms the index can use.

`supported` is the encoder gate; `decode?` re-runs every one of its
conditions — IDs strictly ascending and below `dictCount`, every scale below
256, every mantissa inside the signed 64-bit range, every CRS index at most
`crsCount`, `xmin <= xmax`, `ymin <= ymax`, and the extents covering the
payload exactly. There are TWO readers, so unlike LGI1 the equality IS
claimed: `decodeSpec?` over `List UInt8` states what GBI1 admits, `decode?`
reads the artifact by byte-array index, and `decode_eq_spec` proves they
agree on every input.

## 7. Size and speed

Measured by `l4block-geo-bbox` (`Harness/GeoBBoxProbe.lean`) on a generated
IBK4 block of `geo:wktLiteral` objects. The fixture and its generator are
deleted after the measurement; the numbers are in the landing report and the
probe reprints them on any regenerated fixture.

The probe reports block bytes and rows, distinct boxed terms, GBI1 bytes and
the percentage of the block, index build time, and per query the scan time,
the index time and the ratio — for a `geof:sfWithin` against a small query
polygon that matches a few rows and for one that matches NOTHING. The MISS is
the reading that matters: an index that does not make a query over empty
space fast has not indexed anything.

## 8. Manifest, packer, planner — all open

GBI1 is a fifth sidecar role and needs the same manifest work LGI1 needs: a
role in the manifest wire version, the sidecar's SHA-256, its own Merkle
commitment, and the rule that a generation WITHOUT it still activates and
answers. The packer writing `.gbi1` and the planner detecting the shapes of
section 4 are both open and deliberately not landed here, because the same
four files carry LGI1's packer and planner work.

Until they land, the shipped query path still scans and the section 7 numbers
are the mechanism measured through the probe, not through `storeHandleQuery`.

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
