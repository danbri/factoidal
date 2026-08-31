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
