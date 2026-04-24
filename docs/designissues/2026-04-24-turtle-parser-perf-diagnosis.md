# Turtle/TriG parser perf diagnosis — 331 MB UK Parliament file

Static analysis by Agent Delta, 2026-04-24. Reference:
[`2026-04-19-turtle-parser-speed.md`](2026-04-19-turtle-parser-speed.md) already
identified three structural bottlenecks for Turtle. This doc focuses on the
**TriG** path, where a new dominant bottleneck exists that the 2026-04-19
audit missed.

No files were edited. No parser was run. Agent Alpha owns the benchmark.

## Scope

`factoidal_cli.ml:157-158` and `factoidal_http.ml:95-96` both call
`Parser_TriG.parse_trig_with_base_lenient`. Our 331 MB file therefore goes
through `Parser.TriG.parse_trig_doc` → `trig_dataset_add_triples` →
`trig_dataset_add` → `graph_add` and `trig_find_named_graph`.

## Finding 1 — Dataset accumulator is O(N²) per named graph (DOMINANT)

**Location:** `RDF.Graph.Executable.fst:248-249` (`graph_add`) and
`RDF.Graph.Executable.fst:243-246` (`mem_triple`), called from
`Parser.TriG.fst:52`, `:56`, `:60`.

```fstar
let rec mem_triple (t:triple) (g:rdf_graph) : bool = ...  (* O(|g|) linear scan *)
let graph_add (t:triple) (g:rdf_graph) : rdf_graph =
  if mem_triple t g then g else g @ [t]                   (* O(|g|) append *)
```

For each triple we (a) walk the whole graph to dedupe and (b) append to the
tail of an OCaml list — an `O(|g|)` copy allocating `|g|` fresh cons cells.
Inserting N triples into one named graph is **Θ(N²) time and Θ(N²) total
allocation**. A typical UK Parliament TriG carries most of its payload in a
handful of named graphs. At N ≈ 1 M triples per graph this is 10¹² list-cell
operations — consistent with "runs for minutes, 1.8 GB RAM, never finishes".

This is the single biggest bottleneck and it is **not in Parser.Turtle at
all**; it lives in the graph-construction layer. The 2026-04-19 speed plan
never examined it because that plan targeted the syntactic parser.

## Finding 2 — `trig_find_named_graph` rebuilds the named-graph list per triple

**Location:** `Parser.TriG.fst:36-46` and `Parser.TriG.fst:58,61`
(also `Parser.NQuads.fst:146-174` for the N-Quads path).

```fstar
match trig_find_named_graph name ds.ds_named with
| Some (before, existing_g, after) ->
    ...
    { ds with ds_named = List.Tot.append before (List.Tot.append [updated_ng] after) }
```

Every quad (a) linearly scans `ds.ds_named` to locate its graph and (b)
rebuilds the named-graph spine via two `List.Tot.append`s. If the file has K
named graphs and N total triples, this adds **Θ(N · K)** on top of Finding 1.
K is typically small (tens) so the absolute cost is smaller than Finding 1,
but the allocation rate is high and contributes to the 1.8 GB RSS figure.

## Finding 3 — Fuel & positions are bignums (`Z.t`) in hot loops

**Location:** Extracted in `ocaml-output/Parser_Turtle.ml:2817`,
`Parser_TriG.ml`, etc. All `Prims.nat` extracts to `Z.t`.

```ocaml
let fuel = (len + Prims.int_one) * (Prims.of_int (2)) in  (* ≈ 6·10^8 for 331 MB *)
```

Every `pos + 1`, `fuel - 1`, `pos >= len` goes through Zarith. OCaml's
small-int fast path keeps this to ~1 word per op, but there are still
allocations for intermediate results and the dispatch cost compounds over
~10⁹ loop iterations. This is the bottleneck the 2026-04-19 plan (Phase B)
attacks. It matters, but **Finding 1 will dominate it at 331 MB scale by an
order of magnitude**.

## Finding 4 — Per-statement `append_list` in Turtle grammar (pre-existing, smaller)

**Location:** `Parser.Turtle.fst:1469, 1497, 1567, 1634, 1775` — already
documented in `2026-04-19-turtle-parser-speed.md` §3.

Intra-statement `append_list` (O(k) per merge where k = objects in one
statement) is O(k²) per long predicate-object list. Irrelevant at 331 MB
unless the file has unusually long collections; Parliament data tends
toward small per-subject grouping.

## Finding 5 — `lookup_prefix` is O(|prefixes|) but prefixes are small

**Location:** `Parser.Turtle.fst:61-64`, called from `:113`.

Linear scan of the prefix list. Parliament files typically declare <20
prefixes, so this is a constant-factor concern at most. Mentioned for
completeness — not a priority.

## What's *not* broken

- **`Parser.FastString`** is wired: `fs_byte_length`/`fs_byte_index`/`fs_byte_sub`
  are used throughout the Turtle scanner and grammar. The O(n²) byte-walk
  problem from issue #70 is fixed.
- **NTriples/NQuads line loops** use `t :: acc` (O(1) per triple) and do
  **not** call `append_list` — see `Parser.NTriples.fst:709, 761` and
  `Parser.NQuads.fst:186-238`. They're fine for the streaming case.
- **TurtleScanner** does not materialize substrings until `span_to_string`
  — the allocation is deferred correctly.

## Ranked mitigation table

| # | Fix | Where | Expected speedup @ 331 MB | Risk |
|---|-----|-------|---------------------------|------|
| 1 | **Drop dedup + tail-append in bulk-parser graph construction.** Change `graph_add` to `t :: g` (no `mem_triple`, no `g @ [t]`) during parsing. Move the set-semantics dedup to an explicit `graph_canonicalise : rdf_graph -> rdf_graph` called once post-load, or skip it entirely for the "lenient" entry points. | `RDF.Graph.Executable.fst:248-249` plus a new `graph_add_unchecked`, callers `Parser.TriG.fst:52,56` and `Parser.NQuads.fst:164,169`. | **10⁴–10⁶×** — drops parse from O(N²) to O(N). Without this, nothing else matters at 331 MB. | Low on the extraction side (one function). Some on the spec side: any downstream code that *assumes* graphs are dedup'd now gets duplicates. Audit `graph_union`, `mem_triple` consumers. Two-tier API (`graph_add` vs `graph_add_unchecked`) keeps verified properties for callers who need them. |
| 2 | **Accumulate named graphs reverse-prepended, finalise once.** Replace `trig_dataset_add`'s linear scan + 2-append spine with an association-list prepend during parsing; materialise the final `ds_named` order after `parse_trig_doc` returns. Use an immutable hash-trie / `FStar.Map` if we need dedup. | `Parser.TriG.fst:49-61`, `Parser.NQuads.fst:160-174`, `parse_trig_doc:446-459`. | **3–20×** on top of fix #1, dominated by K (graph count). | Moderate — requires an insertion-ordered accumulator type and changes the API surface that TriG/N-Quads callers see. |
| 3 | **Move fuel/position to machine-int.** Already scoped in Phase B of `2026-04-19-turtle-parser-speed.md`. Introduce `Parser.Position` with `pos_t` extracting to OCaml `int`. | `Parser.TurtleScanner`, `Parser.Turtle`, combinator hot path. | **3–10×** on top of #1+#2 at 331 MB (bignum overhead over 10⁹ positions is real; effect grows with file size). | High — broad edit, weeks of SMT re-proving. Do *after* #1+#2 prove they're not enough. |
| 4 | **Streaming parse → consumer callback.** Replace `parse_trig_doc : rdf_dataset → rdf_dataset` with a `fold_trig : (triple → graph_name → acc → acc) → acc → acc` so callers choose their own accumulator (list, DB writer, tokio sink). Lets the HTTP server build an indexed store directly. | New entry in `Parser.TriG.fst`; `factoidal_cli.ml`/`factoidal_http.ml` callsites adapt. | **Makes the RAM cliff disappear.** Constant-memory streaming regardless of file size. Time stays at whatever #1+#2+#3 deliver. | Moderate — API change; `rdf_dataset` consumers need a migration path. |
| 5 | Finish Turtle Phase A.2 — eliminate intra-statement `append_list` (`Parser.Turtle.fst:1469/1497/1567/1634/1775`) in favour of reversed accumulators. | Same file, same lines as the 2026-04-19 plan. | **1.1–1.5×** at 331 MB (only matters per-statement; Parliament statements are short). | Low. Already scoped. |

## Bottom-line verdict

The 331 MB UK Parliament TriG load is currently **Θ(N²) in time and
Θ(N²) in allocation**, where N is the number of triples per named graph.
That's because `graph_add` in `RDF.Graph.Executable.fst:248-249` dedup-checks
and tail-appends a list for every quad. Replacing the bulk-parser path with
an unchecked `t :: g` prepend (mitigation #1) drops the load to **Θ(N) time
and Θ(N) memory** — the file should finish in minutes with hundreds of MB
RSS, not fail to finish at multi-GB RSS. The Phase B machine-int work from
the 2026-04-19 plan is still worth doing but is a 3–10× constant-factor
improvement, not the orders-of-magnitude fix the 331 MB case needs.
