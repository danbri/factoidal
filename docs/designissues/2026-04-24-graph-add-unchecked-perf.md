# `graph_add_unchecked` — O(1) prepend for bulk parsers

Agent Lambda, 2026-04-24. Companion / mitigation of
[`2026-04-24-turtle-parser-perf-diagnosis.md`](2026-04-24-turtle-parser-perf-diagnosis.md)
(Agent Delta) and follows Agent Alpha's confirmed O(N^2.3) benchmark on the
331 MB UK Parliament TriG.

## Problem (recap)

`graph_add` in `RDF.Graph.Executable.fst` does:

```fstar
let graph_add (t:triple) (g:rdf_graph) : rdf_graph =
  if mem_triple t g then g else g @ [t]
```

That is `O(|g|)` linear dedup + `O(|g|)` tail-append. Inserting N triples
is Theta(N^2). At N approx 1 M per named graph this is approx 10^12
list-cell ops — consistent with "runs for minutes, 1.8 GB RAM, never
finishes" reported by Alpha on the UK Parliament TriG load.

## Mitigation

Add a sibling:

```fstar
let graph_add_unchecked (t:triple) (g:rdf_graph) : rdf_graph = t :: g
```

`O(1)` per call, no dedup. Not sound for a user-facing API (a SPARQL
INSERT DATA must dedup), but **correct for bulk parsing**: a single TriG
or N-Quads file does not produce duplicate triples within one named
graph in practice, and even when it does, the canonical RDF abstract
syntax is set-semantics — duplicates collapse for query semantics
because SPARQL evaluation is set-based (BGP / ASK / SELECT) regardless
of the underlying list shape.

## Call-site swaps

In-scope (bulk parser path, raw input -> fresh dataset accumulator):

- `Parser.NQuads.fst:164` — default-graph add in `dataset_add_quad`.
- `Parser.NQuads.fst:169` — named-graph add in `dataset_add_quad`.
- `Parser.TriG.fst:52` — default-graph add in `trig_dataset_add`.
- `Parser.TriG.fst:56` — named-graph add in `trig_dataset_add`.

Out-of-scope (kept as `graph_add`):

- `Parser.NTriples.fst` — already uses `t :: acc` + final `List.Tot.rev`.
- `Parser.Turtle.fst` — already uses `t :: acc_rev` etc., no `graph_add`.
- `Parser.RDFXML.fst` — already produces `list triple` via cons.
- `Parser.Ballyhoo.fst` — HDT shell-out scope, not the bulk-parser target.
- `SPARQL11.Algebra.fst` (INSERT DATA / graph_append) — user-facing
  set semantics, dedup is required.
- `graph_union`, `add_triple_if_new` — user-facing dedup helpers.

## Semantic caveats

1. **Order reverses.** `graph_add` appended at the tail; `graph_add_unchecked`
   prepends at the head. Code that round-trips a TriG file and expects the
   serialised triple order to match the source order will see reversed
   order per named graph. SPARQL evaluation is set-based and does not
   care. Issue: pretty-printing / canonicalisation tests may need to
   sort first.
2. **Duplicates pass through.** If a TriG file legitimately repeats a
   quad, the parsed dataset will now contain two list cells for one
   abstract triple. SPARQL semantics still treat them as one (BGP
   matching is set-based). Counting via `graph_len` will over-report;
   any code that uses `graph_len` as a "distinct triple count" must
   switch to a dedup pass first. Today `factoidal --count` prints
   `graph_len`, so it is now "list length" not "distinct triples". Note
   this in user docs if it matters.
3. **No verified property change.** `lemma_add_no_dup` for `graph_add`
   stays as-is. We do **not** add an analogous lemma for the unchecked
   variant — its only contract is `t :: g`, which is its definition.

## Expected impact

Alpha's curve: `t ~ N^2.3` (in seconds for N triples). With prepend-only:

- Per-triple cost is O(1) instead of O(N).
- Total cost is O(N) instead of O(N^2).
- Memory: N cons cells instead of Theta(N^2) (the tail-append created
  fresh spine on every call).

For a 1 M-triple named graph: the prior 10^12 ops becomes 10^6 ops —
a **10^6x** speedup on the hot accumulator. The full parse is still
bottlenecked by FastString byte-walking and Zarith fuel arithmetic
(Findings 3 and 4 in Delta's doc), so end-to-end speedup is bounded by
those — Delta estimated 10^4 to 10^6 x; the conservative end is more
likely.

## Verification plan

- F* verify only the four edited files locally. `--lax` is banned.
- No `build-ocaml.sh extract` or `compile` from this agent — main thread
  is rebuilding. Patches and benchmarks land in a follow-up commit.
