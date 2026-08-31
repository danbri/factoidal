# Delta-log proof port: first Lean framing primitive

Status: in progress, 2026-08-31.

The reference implementation remains
`formal/fstar/RDF.Store.Columnar.DeltaLog.fst`.  It already proves the
per-layer inverse chain for DLE1/DLB1/DLOG and CEP1, plus the epoch-filter
used after compaction.  Lean's executable implementation is in
`formal/lean4/L4Factoidal/Storage/DeltaLog.lean`; it now mirrors the CEP1
framing and replay placement, but most format-wide inverse theorems remain to
be ported.

This increment establishes reusable Lean theorems in
`L4Factoidal/Storage/Bytes.lean`:

* `readU32LE_writeU32LE_append`: a u32 field round-trips in front of an
  arbitrary suffix.
* `readU32LE_append_writeU32LE`: the same field remains readable at a known
  offset after arbitrary preceding framing.
* `drop_append_length_add`: consuming a fixed prefix plus an offset from an
  appended byte stream is equivalent to consuming the offset from its suffix.
* `writeU32LE_length` and `u32_toNat_ofNat_of_lt`: fixed field width and the
  no-truncation fact needed for bounded length fields.

They are universal theorems, not sampled `#guard` checks.  Lean's simplifier
reduces the byte assembly to a 32-bit reconstruction identity; the final
identity is discharged by `Std.Tactic.BVDecide`, giving a checked bit-vector
proof rather than an axiom or `sorry`.

The first DLE1 theorem is now landed in
`L4Factoidal/Storage/DeltaLog.lean`:

```lean
payload.length < UInt32.size →
  parseEntry (frameEntry payload ++ rest) = some (payload, rest)
```

That premise is necessary because `frameEntry` presently writes
`UInt32.ofNat payload.length`; an unrestricted Lean list can exceed a u32
length field. Its proof checks magic, version, length, payload extent,
checksum and suffix cursor movement. It deliberately uses the `UInt32.size`
bound rather than hiding truncation behind a cast.

The later proof chain should make public writer refusal explicit for all u32
length fields, then port string, RDF term, triple, typed entry, batch,
whole-log, and compaction-filter refinement results in that order.

Validation for this increment:

```sh
cd formal/lean4
lake build L4Factoidal.Storage.Bytes
lake build L4Factoidal.Storage.DeltaLog
```
