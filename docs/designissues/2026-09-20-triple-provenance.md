# Triple provenance: annotating emitted triples with their origin

Status: first stage landed in the Lean tree on 2026-09-20 for the Turtle
reference parser. Owner's ask (2026-09-20): improve the RDF parsers so each
emitted triple can be annotated, by named graph or in RDF 1.2 style, with an
id to which parsing and validation information can be attached.

## Decision

The identity is kept OUT of the graph and produced BESIDE it. A graph is a
set of triples; a document can state the same triple twice, and two
documents can state it once each, so a per-triple identity cannot live in
the triple. The parser therefore emits, for every triple, a provenance
record, and a separate step turns records into RDF when a consumer wants
them as RDF.

The record for the Turtle parser (`Syntax.TurtleProvenance`):

| Field | Meaning |
| --- | --- |
| `span.index` | 0-based ordinal of the statement in the document, directives counted |
| `span.startPos` | character offset of the statement's first character |
| `span.endPos` | character offset just past its terminating `.` |
| `ordinal` | 0-based position of the triple among those the statement emitted |

Offsets are the same character offsets the parser reports in `ParseError`,
so an error position and a provenance position are comparable directly.
Byte offsets are a later addition once the byte-streaming path
(`TurtleChunkFold`) carries the same records; the chunk scanner already
keeps statement boundaries, so the ordinal comes for free there.

## Why not a fourth column or a named graph per triple

- A named graph per triple would be a quad store with one graph per row.
  The store then needs a graph-name generator, and every query has to know
  to ignore or join the generated names. RDF 1.2 reifiers say the same
  thing inside one graph, with standard vocabulary.
- A named graph per SOURCE remains a good fit for source-level facts
  (retrieval IRI, time, parser version) and composes with reifiers for
  triple-level facts. Nothing here prevents it.

## RDF form

`reifyProvenance source annotated` produces, per annotated triple, six
triples:

    _:prov/<statement>/<ordinal> rdf:reifies <<( s p o )>> ;
        prov:source "<source>" ;
        prov:statement <statement> ;
        prov:ordinal <ordinal> ;
        prov:start <startPos> ;
        prov:end <endPos> .

Reifier labels contain `/`, which `BLANK_NODE_LABEL` cannot produce, and
the parser's generated labels are `anon` plus underscores, so the three
label populations are disjoint. The `prov:` namespace is the placeholder
`https://factoidal.example/ns/provenance#` behind five constants; changing
it is a one-line edit.

The reified graph does not repeat the annotated triples; append it to the
parsed graph when both are wanted.

## Proved

- `parseStatementsFoldProv_forget`: a step that ignores the span is the
  existing `parseStatementsFold`.
- `parseTurtleProv_triples`: projecting the provenance away from
  `parseTurtleProv` is exactly `parseTurtle`, errors included. The
  annotated parse is the reference parse plus data, not a second parser.
- `reifyProvenance_length`: six triples per annotated triple.

Build-time guards in `Syntax.TurtleProvenanceTests` pin spans and ordinals
on a document with a directive, a predicateObjectList and a comment, error
agreement with `parseTurtle`, and the reified graph's shape.

## What validation attaches

- A SHACL validation result names a focus node, a path and a value; with
  provenance it can also name the reifier of the triple that carried the
  value, which is what a report consumer needs to point back into a file.
- A ShEx result carries an arc labelling: which triple constraint of which
  shape consumed each triple. That is a per-triple annotation already, and
  the ShapesCore certificate design keeps it. Both attach to the reifier.

## Not done

1. TriG and N-Quads: same records, plus the graph name the statement sat
   in. The TriG parser reuses `readStatement`, so the fold change is the
   same shape.
2. The F* Turtle parser: iron rule 4 says parsers are F* first. This
   landed in Lean because the Lean fold and its agreement theorem are
   where the proof of "reference parse plus data" is cheap to state. The
   F* `fold_turtle_triples_acc` takes the same change; until it lands, the
   F* engine does not emit provenance.
3. Byte offsets and the streaming path (above).
4. A CLI or wasm surface. `parseTurtleProv` and `reifyProvenance` are
   library functions only.
