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

The durable writer boundary now uses explicit admission APIs:

* `serializeDeltaBatch? : DeltaBatch → Option (List UInt8)`;
* `serializeLog? : List DeltaBatch → Option (List UInt8)`.

They reject out-of-range sequence/epoch/count/body values. The legacy
list-returning functions remain only for compatibility with pure existing
callers; `Harness/DeltaLogTool.lean`, the path that appends a real durable log,
uses only the option-returning functions and reports wire-limit refusal rather
than silently dropping a batch. Regression guards cover u64 overflow refusal.

The admission chain now continues through `serializeLString?`, subject, term,
triple, graph-name and delta-payload encoders. This ensures a nested u32 string
length cannot silently truncate, and that the currently unsupported RDF-star
triple-term encoding is refused before it can create a DLOG record whose reader
would reject during replay.

The executable delta and compaction smokes were also rerun: two updates are
read through the Merkle-verified SPARQL path, compaction publishes and
activates a new base, and a post-compaction update is written at epoch 2 and
visible through base-plus-delta evaluation.

Replay of both raw DLE1 frames and DLB1 batches now uses a reverse accumulator
and one final `reverse`, rather than repeated `acc ++ [item]`. This keeps
recovery linear in the number of committed frames/batches while preserving
physical log order; a two-batch regression guards the order at the DLOG API.

The CEP1 companion marker now also has a landed Lean theorem:

```lean
natFitsU64 n = true →
  parseEpoch (frameEpoch ⟨n⟩) = some ⟨n⟩
```

The proof composes the new `readU64LE_writeU64LE_append` theorem with the
existing u32 framing inverses, verifies the fixed 24-byte CEP1 shape and uses
the representability premise to prove that `Nat → UInt64 → Nat` preserves the
epoch. This is a **landed Lean theorem** corresponding to F*'s
`lemma_compacted_epoch_roundtrip`; it does not yet prove complete DLB1/DLOG
decode/encode inversion or full RDF-term payload round trips.

Validation for this increment:

```sh
cd formal/lean4
lake build L4Factoidal.Storage.Bytes
lake build L4Factoidal.Storage.DeltaLog
lake build L4Factoidal.Storage.DeltaLogTests
```
