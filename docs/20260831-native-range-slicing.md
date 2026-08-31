# Native verified-range slicing

Status: landed Lean executable optimization, 2026-08-31.

`formal/lean4/Harness/PosixRangeIO.lean` implements the native `pread` and
Merkle-verification boundary used by the disk-backed Shardborough query tools.
It previously converted complete `ByteArray` chunks (and `.merkle` sidecars)
to linked `List UInt8` values merely to extract a short requested range. The
same conversion occurred after concatenating the verified chunks for both cold
and cache-assisted reads.

Those slice operations now use `ByteArray.extract` directly:

* Merkle leaf extraction takes each 32-byte digest without converting the
  full sidecar for every leaf;
* single-chunk verified reads return the requested interior range directly;
* multi-chunk and cached multi-chunk readers do the same after verifying the
  constituent chunks.

This is a **landed Lean executable optimization**, not a new theorem: the
native `pread` edge remains a harness/host realization outside the pure block
semantics. It preserves the existing length checks and Merkle proof admission;
the selective SPARQL smoke is the integration evidence.

The same smoke had become stale by invoking `l4block-shard-query`, whose
legacy SBM0/SBM1 manifest reader cannot open the current packer's SBM2 output.
`tools/blockengine-shard-selective-smoke.sh` now uses the proof-carrying
`l4block-shard-merkle-query` and verifies the intended current behavior:
a two-predicate query opens two artifacts, while a limited one-predicate query
opens one artifact through the range-prefix path.

Validation:

```sh
cd formal/lean4
lake build Harness.PosixRangeIO Harness.ShardMerkleScan Harness.ShardMerkleMaterialize \
  l4block-shard-merkle-query
cd ../..
bash tools/blockengine-shard-selective-smoke.sh
```

Remaining work: `concatChunks` and several storage decoders still use
`ByteArray → List UInt8`; the broader offset-based decoder refactor remains
open and must carry its own decode/denotation proof plan.
