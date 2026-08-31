# IBK2 native byte slicing

Status: landed Lean implementation, 2026-08-31.

`L4Factoidal/Storage/IndexedBlockWireV2.lean` previously implemented the
private `sliceBytes` helper by converting the whole `ByteArray` to a `List`,
then applying `drop` and `take`, and converting the result back to an array.
This happened on every opened-block range scan, including the planning prefix,
dictionary, directory and selected predicate segment.

The helper now uses `ByteArray.extract offset (offset + length)`. The public
meaning is unchanged: it still returns the same clamped half-open byte range.
The compiled implementation can use Lean's byte-array copy primitive directly,
and no longer allocates or traverses an unrelated whole-artifact list merely
to select a range.

This does not yet remove the other list-based parsers in IBK2; those remain a
separate, larger refactor requiring offset-based byte readers and preservation
theorems. It is nevertheless relevant to persistent selective SPARQL because
`OpenBlock.scanBoundRange` invokes this helper for each selected physical
range.

Validation:

```sh
cd formal/lean4
lake build L4Factoidal.Storage.IndexedBlockWireV2 \
  L4Factoidal.Storage.IndexedBlockWireV2Tests \
  l4block-shard-pack l4block-shard-merkle-query
bash ../../tools/blockengine-w3c-disk-query-smoke.sh
```

The disk gate packed the W3C fixtures and evaluated two unmodified parsed
SPARQL queries through predicate-selective, Merkle-verified IBK2 storage:
one returned its expected binding and one returned zero rows.
