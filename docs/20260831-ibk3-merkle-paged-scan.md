# IBK3 Merkle-verified paged scan

`l4block-id-v3-merkle-scan` is the first native reference host for the IBK3
range layout. It admits the SBM2 manifest and artifact's chunk commitment,
then supplies the pure Lean range executor only after native `pread` has
verified each requested file chunk to that commitment.

For a predicate-local artifact it reads, in order:

1. the 13-byte IBK3 header;
2. the PTD1 prefix and page directory;
3. a caller-bounded row prefix; and
4. exactly the PTD1 term pages referenced by that row prefix.

Missing, malformed, or mismatched pages reject the operation. They cannot be
silently reported as an empty SPARQL result. The executable is deliberately a
narrow push-worker reference: it currently receives a predicate and row limit,
not a general network protocol or replacement SPARQL evaluator.

## Real-corpus check

After conversion of the 36,056-row Wikidata P684 gene artifact, a bounded
native scan of ten rows reported:

```text
rows=10
logical-read-bytes=12732
fetched-bytes=131072
verified-chunks=2
range-requests=5
artifact-bytes=2061235
```

`logical-read-bytes` counts the exact requested ranges; `fetched-bytes` counts
the complete 64 KiB Merkle chunks newly admitted by that process. Thus the
small-result read avoids the former multi-megabyte IBK2 dictionary fetch while
remaining explicit about the physical read amplification caused by fixed chunk
integrity units.

The first implementation exposed a large-result problem: it decoded a
referenced PTD1 page again for every subject, predicate, and object lookup.
The pure executor now decodes each supplied page once, then resolves all row
terms from that validated in-memory page. Re-running the same real artifact
for all 36,056 rows completes in under one second on the development laptop
and reports:

```text
logical-read-bytes=2061227
fetched-bytes=2061235
verified-chunks=32
range-requests=132
```

That is expected for a complete scan: it needs essentially the whole 2.06 MiB
artifact. The useful contrast is therefore bounded result retrieval versus
complete predicate retrieval, not a claim that paging makes a full scan
smaller.

## Multi-artifact predicate scans

SBM2 permits bounded publication batches, so one predicate can have several
immutable artifacts. The host now uses manifest-order `selectAll`, applies one
global limit across those artifacts, and totals its integrity/I/O evidence.
On direct `gene.ttl` publication, P684 spans five artifacts (759,263 rows):

```text
LIMIT 50000: rows=50000, artifacts=2/5,
             logical=2703715, fetched=2782131, chunks=43, requests=172
all rows:    rows=759263, artifacts=5/5,
             logical=16428933, fetched=16428973, chunks=253, requests=391
```

`LIMIT 0` opens no artifacts and reports zero I/O. This is a deterministic
predicate scan suitable for lowering from a bounded physical fragment; it is
not yet the general parsed-SPARQL host, which must still compose this fragment
with joins, expressions, projection, ordering, and updates through the
existing SPARQL evaluator.
