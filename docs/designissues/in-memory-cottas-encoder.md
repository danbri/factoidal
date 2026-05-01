# In-memory COTTAS encoder: F*-verified indexing for in-memory RDF

**Status:** design note, 2026-05-01
**Origin:** user idea ("ramdisk" / fake disk space from RAM)
**Motivation:** the streaming-count fast path (PR #131) is correct but
delivers no wall-time win on the lifesci demo because
`bucket_replace_acc`'s O(N²) assoc-list inserts during
`indexed_dataset_backend` construction dominate the cost. Replacing
`bucket_map` is a structural F\* change touching the whole graph layer.
A cheaper unlock: serialise the in-memory graph to COTTAS bytes in RAM
and re-use the F\*-verified COTTAS read path that already has
presence-bitmap prune, compound (p,o) index, page cache, etc.

## What this is

A new constructor `cottas_inmem_store : rdf_graph -> cottas_ondisk_store`
that produces a COTTAS-shaped byte buffer in memory, then hands it to
the existing F\* search/estimate/page-cache code unchanged. The byte
source is a `Bytes.t` reference instead of an `mmap`'d file, but the
F\* side already works against an abstract `parquet_byte_range` API —
the only OCaml-side change is the byte source.

## What it isn't

- Not a full RDF→Parquet writer. We don't need DeltaLengthByteArray
  encoding; a simpler layout is fine since we control the bytes.
- Not portable to other COTTAS readers. The on-disk format is the
  product; this is a private "instance the same reader against a
  different byte source" optimisation.
- Not a replacement for the existing `indexed_graph_backend`. It's a
  parallel option, used when the graph is small enough that COTTAS
  overhead amortises (parquet footer, dictionary pages, etc.).

## Architecture

```
         +-----------------------------+
         |  rdf_graph (list triple)    |
         +-------------+---------------+
                       |
                       v  cottas_inmem_encode
         +-----------------------------+
         |  cottas_bytes : Bytes.t     |
         |  - footer (num_rows, etc.)  |
         |  - 4 string columns (S P O G)|
         |  - presence bitmaps         |
         |  - compound (p,o) bitmap    |
         +-------------+---------------+
                       |
                       v  Bytes.t-backed parquet_byte_range
         +-----------------------------+
         |  cottas_ondisk_store        |
         |  (existing F* type)         |
         +-------------+---------------+
                       |
                       v  same path as on-disk
         +-----------------------------+
         |  F* search / estimate       |
         |  page cache, presence prune |
         +-----------------------------+
```

## Where the work happens

### F\* side (small)

The F\* code is **already** abstract over the byte source. The only
thing that needs touching is the `assume val parquet_byte_range`
realisation in `experimental_ocaml_glue/parquet_footer_runtime.sh` —
add a "buffer" variant that reads from a `Bytes.t` ref instead of
`mmap`'d file bytes. Or better: define the abstraction as a
`byte_range` module the F\* side requires, and let OCaml have two
realisations (file-mmap vs in-RAM-buffer) selected at handle-open
time.

The path constructor `cottas_ondisk_store` currently embeds a `path`
string. We'd extend it to be a sum:

```fstar
type cottas_byte_source =
  | CBS_File of string        (* path, mmap-backed *)
  | CBS_Buffer of opaque_id   (* in-RAM buffer, looked up via assume val *)
```

### OCaml side (larger but bounded)

Write the encoder in OCaml glue (it's pure I/O against the Bytes.t,
not semantic logic — rule-#11 allowed). Roughly:

```ocaml
(* experimental_ocaml_glue/cottas_inmem_runtime.sh *)
let encode_to_buffer (g : rdf_graph) : Bytes.t =
  let buf = Buffer.create (16 * 1024) in
  (* footer *)
  write_footer buf ~num_rows:(List.length g);
  (* four string columns: subj/pred/obj/graph *)
  write_column buf (List.map (fun t -> subject_to_str t.s) g);
  write_column buf (List.map (fun t -> t.p) g);
  write_column buf (List.map (fun t -> term_to_str t.o) g);
  write_column buf (List.map (fun _ -> "") g); (* default graph *)
  (* presence bitmaps + compound (p,o) — same shape as the on-disk
     companion writers (Yod6 / Tet3 / compound_po) *)
  write_companions buf g;
  Buffer.to_bytes buf
```

The "row group" model can be trivial: one row group containing all
triples. The page cache becomes irrelevant (everything is in RAM
already) but stays a no-op. Presence-bitmap prune still works because
it's a separate companion file → in-mem becomes a separate region of
the same buffer.

## Expected payoff

For lifesci-demo Q01 (`SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g
{ ?s ?p ?o } } GROUP BY ?g`):

- `backend_estimate` per named graph reads `num_rows` from the
  in-memory footer. **O(1) per graph, not O(N²)**.
- The streaming-count detector (PR #131) already dispatches
  `count_group_by_graph_solutions` → `backend_estimate`. So Q01
  drops from ~137s to **milliseconds**.

For bound queries (e.g. `?s rdf:type owl:Class`):
- Predicate presence-bitmap prune skips graphs that don't contain the
  predicate — *for free*, because the bitmap is in the in-memory buffer.
- Compound (p,o) prune likewise.
- Net: F\*-verified indexing on data the user gave us as Turtle.

## Cost

- F\* abstraction tweak: ~50 LoC, mostly type tweaks. Verifies in F\*.
- OCaml encoder: ~300 LoC of pure-bytes plumbing. No new `assume val`s
  beyond the buffer-source realisation.
- Tests: re-run W3C, plus a perf re-bench of Q01.

Estimate: 1-2 agent runs (encoder + wiring), then a third for the
verification claim update.

## Why this beats fixing `bucket_map`

- `bucket_map` is an F\* assoc-list type used pervasively in
  `RDF.Graph.Executable.fst`. Replacing it with a hash-keyed structure
  needs a whole-file refactor + proof updates for everything that
  reasons about it (RDFS closure, OWL-RL closure, model-theory
  equivalence). High blast radius.
- The in-memory COTTAS encoder is **additive**. Old paths unchanged;
  new path constructed from the same `rdf_graph`. If it doesn't work
  out we delete one OCaml file and one F\* type case.

## Why this beats a literal ramdisk

A literal ramdisk (`/dev/shm` on Linux, `diskutil erasevolume` macOS
RAM volume) would work today with `--data-cottas` pointing at the
RAM-backed file. But it requires:
- A separate import step (Turtle → COTTAS file write → mount).
- Filesystem indirection for every byte read (mmap of tmpfs ≠ direct
  Bytes.t access).
- Doesn't help the JS demo at all (no fs mount in browser).

The encoder option works in-process and works in JS, because Bytes.t
is just a string in OCaml-extracted JS.

## Phasing

1. **Phase A** — bytes-only encoder (1 row group, no compound bitmaps).
   Just enough for the streaming-count detector to win.
2. **Phase B** — add presence bitmaps for predicate-bound queries.
3. **Phase C** — add compound (p,o) bitmap.

Phase A is the unlock for the demo. B and C scale to bigger queries.

## Open questions

- **Memory overhead.** A 43k-triple lifesci graph in COTTAS bytes is
  probably ~2-3 MB. Compared to the existing `indexed_graph` (with 6
  bucket maps × N entries each, plus the triple list itself), it
  could be smaller, equal, or larger depending on string interning.
  Worth measuring before committing.
- **Bnode handling.** COTTAS encodes everything as strings; bnodes
  become `_:label`. Round-trip identity is preserved by the parser,
  but we should double-check that BGP joins on bnodes still work the
  same as in `indexed_graph`.
- **Default graph.** COTTAS has a graph column. For the in-memory
  case, we'd write the empty string for default-graph triples and the
  graph IRI for named-graph triples. The existing dispatcher already
  handles this on the on-disk path.

## Decision needed

Whether to (a) ship Phase A as the next PR after #131 merges, or
(b) wait for the bucket_map structural fix and skip this entirely.

(a) is the higher-value path: lifesci demo gets the F\*-verified
indexing **today**, demonstrates the "F\* spec is the product, runtime
targets are interchangeable" play, and unlocks the COTTAS-class
optimiser work for in-memory data without breaking anyone's existing
code. The bucket_map structural fix can still happen later for the
non-COTTAS path.
