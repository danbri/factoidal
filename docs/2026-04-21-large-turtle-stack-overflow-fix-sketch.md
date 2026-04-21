# Large Turtle Stack Overflow Fix Sketch

Date: 2026-04-21

## Symptom

This command fails in the native CLI:

```sh
factoidal -d tmp/wikidata-lifesci-kgx/gene.ttl -e 'select distinct ?t ?p where { ?s ?p ?o ; a ?t . }'
```

The narrower parse/count path also fails:

```sh
./bin/darwin-arm64/factoidal --count tmp/wikidata-lifesci-kgx/gene.ttl
```

with:

```text
Error parsing tmp/wikidata-lifesci-kgx/gene.ttl: Stack overflow
```

The file is about 17 MB and contains 888,949 triples.

## What The Bytecode Probe Showed

The existing bytecode executable:

```sh
eval $(opam env --switch=fstar)
OCAMLRUNPARAM=b formal/fstar/ocaml-output/factoidal.byte --count tmp/wikidata-lifesci-kgx/gene.ttl
```

also reports `Stack overflow`, but this is because the CLI catches the exception
and prints it, which suppresses a useful OCaml backtrace.

Temporary uncaught harnesses in `tmp/` showed something more useful:

```ocaml
Parser_Turtle.count_turtle_triples input
Parser_Turtle.parse_turtle_with_base input base
```

both succeed on the same file and return `888949`.

So the Turtle parser is not simply unable to scan this input. The immediate
failure is in the CLI/materialization path around the parser result.

## Likely Immediate Cause

`formal/fstar/ocaml-output/factoidal_cli.ml` has stack-unsafe list operations on
very large triple lists.

The sharpest one is:

```ocaml
let load_triples ?(format=None) ?(base=None) path =
  let ds = load_dataset ~format ~base path in
  ds.ds_default @ List.concat_map (fun ng -> ng.ng_graph) ds.ds_named
```

For a plain Turtle file, `ds.ds_named = []`, so this becomes effectively:

```ocaml
ds.ds_default @ []
```

`(@)` recursively walks the left operand. With roughly 889k triples this can
overflow the native stack even though the parsed list itself was produced.

Query mode has the same class of risk:

```ocaml
let graph = List.concat_map (fun ds -> ds.ds_default) datasets
let file_named_graphs = List.concat_map (fun ds -> ds.ds_named) datasets
let all_named = file_named_graphs @ cli_named_graphs
```

For one large dataset, `List.concat_map (fun ds -> ds.ds_default) [ds]` can
still require appending the large `ds_default` list to `[]`.

## Minimal CLI Fix

Add stack-safe list helpers in the CLI glue, then replace `@` and
`List.concat_map` on potentially large triple lists.

Sketch:

```ocaml
let concat_preserve_order lists =
  List.rev (
    List.fold_left
      (fun acc xs -> List.rev_append xs acc)
      []
      lists
  )

let concat_map_preserve_order f xs =
  concat_preserve_order (List.map f xs)
```

Then:

```ocaml
let load_triples ?(format=None) ?(base=None) path =
  let ds = load_dataset ~format ~base path in
  match ds.ds_named with
  | [] -> ds.ds_default
  | named ->
      concat_preserve_order
        (ds.ds_default :: List.map (fun ng -> ng.ng_graph) named)
```

And in query mode:

```ocaml
let graph = concat_map_preserve_order (fun ds -> ds.ds_default) datasets
```

For named graph metadata lists, ordinary `@` is probably fine when the lists are
small, but it is cleaner to use the same helpers anywhere list size can be
data-dependent.

## Better `--count` Fix

`--count` should not materialize triples just to count them.

For Turtle, route directly to:

```ocaml
Parser_Turtle.count_turtle_triples input
```

or:

```ocaml
Parser_Turtle.count_turtle_triples_with_base input base
```

This path succeeded on `gene.ttl` and returned `888949`.

Equivalent count-only entry points would be useful for N-Triples, N-Quads, and
TriG if large-file counting matters across formats.

## F* Streaming Direction

Yes, this points toward a streaming-ish Turtle parser API in F*, but the first
step does not need to be a full SAX/event parser.

Useful stages:

1. `count` API: already exists for Turtle and avoids list materialization.
2. `fold` API: parse triples and update an accumulator without returning a giant list.
3. `emit/chunk` API: parse into bounded chunks or invoke a callback-like sink.
4. storage-aware API: populate a table/index/dataset store directly instead of building `triple list` and then re-walking it.

The query engine still needs an in-memory graph today, so a streaming parser
alone will not make large query workloads memory-small. But it will remove
avoidable stack hazards and let the CLI count/dump/index paths operate without
large recursive list concatenations.

## Suggested Next Patch

1. Patch `factoidal_cli.ml` to use stack-safe concat helpers.
2. Special-case `--count` for Turtle to use `count_turtle_triples(_with_base)`.
3. Add a local regression using `tmp/wikidata-lifesci-kgx/gene.ttl` when present,
   or generate a synthetic Turtle file with more than 500k simple triples.
4. Add a design issue for an F* parser fold API:

```fstar
val fold_turtle_triples :
  input:string ->
  base:option string ->
  init:'acc ->
  step:('acc -> triple -> Tot 'acc) ->
  Tot 'acc
```

Exact effect annotations may need adjustment, especially if the eventual sink is
stateful or external.
