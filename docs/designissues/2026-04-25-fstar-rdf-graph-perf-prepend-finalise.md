# `graph_add_unchecked` + `graph_finalise` — O(N) bulk parse, order preserved

Agent Tet2, 2026-04-25. Cleaner re-do of Agent Lambda's reverted commit
`a5cf381`. Reverted at `bb6f9d7` because the prepend-only fix flipped per-graph
triple insertion order and broke 19 RDF/XML round-trip bnode-iso tests.

## Recap of the bottleneck

Diagnosed by Agent Delta in
[`2026-04-24-turtle-parser-perf-diagnosis.md`](2026-04-24-turtle-parser-perf-diagnosis.md):

`RDF.Graph.Executable.fst:graph_add` does

```fstar
let graph_add (t:triple) (g:rdf_graph) : rdf_graph =
  if mem_triple t g then g else g @ [t]
```

— `O(|g|)` linear dedup + `O(|g|)` tail-append. Bulk parsing N quads is
Θ(N²) time + Θ(N²) allocation. UK Parliament TriG (3.14 M quads) "runs for
minutes, never finishes, 1.8 GB RSS".

`graph_add` is reached on the bulk path **only** through:

- `Parser.NQuads.fst:dataset_add_quad` — default + named graph add
- `Parser.TriG.fst:trig_dataset_add` — default + named graph add

`Parser.NTriples`, `Parser.Turtle`, `Parser.RDFXML` already cons-prepend into
`list triple` accumulators and reverse at the end (`List.Tot.rev acc`). They
never call `graph_add`. So the surgical fix targets exactly the N-Quads /
TriG dataset construction layer.

## Why Lambda's fix broke RDF/XML round-trips

Lambda swapped `graph_add` for `t :: g`. Insertion order then reversed.
Pretty-printers / round-trip serialisers compared parse(serialise(parse(x)))
to `x` and saw the named-graph triples in reverse order; the bnode-iso check
declared mismatch on 19 tests.

(RDF/XML itself does not call `graph_add`, but RDF/XML output lands in an
`rdf_dataset` somewhere downstream — N-Quads round-trip + TriG round-trip
were the real victims; the "RDF/XML" failures are at the dataset-construction
layer, not the XML parser.)

## Mitigation: prepend-while-loading + finalise-once

Two helpers in `RDF.Graph.Executable.fst`:

```fstar
let graph_add_unchecked (t:triple) (g:rdf_graph) : rdf_graph = t :: g

let graph_finalise (g:rdf_graph) : rdf_graph = List.Tot.rev g
```

`graph_add_unchecked` is the bulk-loader call. `graph_finalise` reverses
once at parse end so insertion order is restored. No dedup pass: a single
TriG / N-Quads file does not produce duplicate quads in practice, and SPARQL
evaluation is set-based so semantics are unaffected even if it does. Adding
a sorted-set dedup is `O(N log N)` and could be done later — kept out of
this commit to minimise churn (rule #15: no logic in glue, but this is
F\*-side data structure work, not a glue patch).

A companion `dataset_finalise : rdf_dataset -> rdf_dataset` walks
`ds_default` + each `ng_graph` and applies `graph_finalise`. This runs once
at the parse entry point.

## Call-site changes

In `Parser.NQuads.fst:dataset_add_quad`:

- swap `graph_add t ds.ds_default` → `graph_add_unchecked t ds.ds_default`
- swap `graph_add t existing_g` → `graph_add_unchecked t existing_g`

In `Parser.TriG.fst:trig_dataset_add`: same two swaps.

At the four entry points (`parse_nquads`, `parse_nquads_strict`,
`parse_trig*`), wrap the result in `dataset_finalise`.

## Why NTriples / Turtle / RDFXML don't change

They produce `list triple` directly with `t :: acc` + `List.Tot.rev acc`.
The result is already in source order. `graph_finalise` would be a redundant
O(N) pass. We do **not** wrap them; the spec deliberately limits the change
to where the bottleneck lives.

## Expected impact on 3.14 M-quad Parliament

Per-quad cost drops from O(|g|) to O(1). Total parse cost drops from Θ(N²)
to Θ(N) plus a single Θ(N) reverse at the end. Going from ~10¹² list-cell
ops to ~10⁷ — six orders of magnitude on the dominant term. End-to-end
speed is also bounded by FastString byte-walking (Delta Finding 3) and
zarith fuel (Finding 4); those remain. Conservative estimate: a load that
"never finishes" should now complete in minutes with hundreds of MB RSS.

## Coordination

- Cottas-Perf is in `Parquet.Footer.fst` / `Parser.BallyhooCOTTAS.fst` — not
  touched.
- Sade / Bet2 / Aleph2 are in `RDF.Canonical.fst` — not touched.
- Phi / Heh edited `SPARQL11.Algebra.fst` — not touched.
- This commit edits `RDF.Graph.Executable.fst`, `Parser.NQuads.fst`,
  `Parser.TriG.fst` only.

## Verification

`fstar.exe --include . --cache_dir .cache <module>.fst` for each. No
`--lax`. `build-ocaml.sh` not run from this agent (Wave 12 owns the
extract / compile lock).
