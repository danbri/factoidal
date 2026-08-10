# A fold-shaped XML document interface for the RDF/XML mapping proof (task #49)

Owner decision (2026-08-10, task #49): the RDF/XML mapping should be
proved against a **traversal-shaped** abstract document interface, not a
random-access one (no `get_child(i)`, no `parent()` pointer, no
materialize-then-index). Reason: a random-access interface can only ever
be satisfied by something that already holds the whole document in
memory — exactly the DOM-materialization cost the large-document
measurement in the companion findings doc quantifies (~5x input size in
peak RSS, `docs/designissues/2026-08-10-xml-generality-findings.md`).
A fold/traversal interface can be satisfied by *either* the concrete
`Parser.XML.xml_node` tree (trivially — see below) *or* a future
streaming producer that never materializes more than the current node's
siblings-so-far in memory. Proving the mapping against the interface,
not against `xml_node` directly, means that future producer inherits the
proof for free.

This is a sketch: the shape of the record and its laws, how `xml_node`
satisfies it, and what a streaming producer's proof obligation would
look like. **No proofs are attempted here.**

## The interface: a one-level unfold (coalgebra), not a full walk

The RDF/XML mapping (and any XML consumer) never needs "give me the
whole subtree" — it needs "what kind of node is this, and what are its
immediate children" repeated. That is exactly a coalgebra: a function
that exposes one layer of structure and hands back more opaque nodes to
recurse into, never a pre-built list/tree the caller can index.

```fstar
module XML.Traversal

(* One layer of XML structure, generic over the opaque node type the
   producer uses to represent "a child, not yet looked at". Mirrors
   Parser.XML.xml_node's five constructors exactly -- this is meant to
   be the same shape, not a redesign. *)
noeq type xml_view (node:Type) =
  | VText    : text:string -> xml_view node
  | VElement : tag:string -> attrs:list xml_attribute ->
               children:list node -> xml_view node
  | VComment : text:string -> xml_view node
  | VCDATA   : text:string -> xml_view node
  | VPI      : target:string -> data:string -> xml_view node

(* The interface itself: a node type, a way to look at one layer of it
   (`expose`), and a well-founded measure that shrinks strictly from a
   VElement to each of its children -- this is what lets a fold over it
   be proved Tot without ever demanding the whole tree exist at once. *)
noeq type xml_document = {
  node    : Type;
  root    : node;
  measure : node -> nat;
  expose  : node -> xml_view node;
  descent_law :
    n:node -> squash (
      match expose n with
      | VElement _ _ children ->
        forall (c:node). List.Tot.memP c children ==> measure c < measure n
      | _ -> True)
}
```

`expose` is the entire interface surface. Everything else the RDF/XML
mapping wants — "does this element have exactly one child and is it
text" (parseType Literal detection), "walk the attribute list looking
for `rdf:about`", "recurse into each child in document order" — is
expressible by calling `expose` and pattern-matching the `xml_view`,
never by indexing into a pre-existing structure.

## The fold combinator the mapping is proved against

```fstar
let rec fold_xml (#acc:Type) (doc:xml_document)
                  (f: acc -> xml_view doc.node -> acc)
                  (n:doc.node) (a:acc)
    : Tot acc (decreases (doc.measure n)) =
  let v = doc.expose n in
  let a' = f a v in
  match v with
  | VElement _ _ children -> fold_children doc f children a'
  | _ -> a'

and fold_children (#acc:Type) (doc:xml_document)
                   (f: acc -> xml_view doc.node -> acc)
                   (children:list doc.node) (a:acc)
    : Tot acc (decreases children) =
  match children with
  | [] -> a
  | c :: rest -> fold_children doc f rest (fold_xml doc f c a)
```

The RDF/XML mapping algorithm (node-element / property-element grammar,
`rdf:parseType` handling, blank-node minting) gets specified as an
instance of `f` threading an accumulator of `(triples, blank-node
counter, xml:base/xml:lang stack)` through `fold_xml`. That
specification never mentions `xml_node`, `Parser.XML`, or any concrete
representation — only `xml_document` and `xml_view`. That is the point:
the proof obligation "the mapping is correct" is stated once, against
the interface, and every producer that implements `xml_document`
inherits it.

## Laws (informal — no proofs here, just what would need proving)

1. **Well-founded descent** (`descent_law` above, stated as a field so
   it is available wherever `xml_document` is): every child `expose`
   hands back is strictly smaller under `measure` than its parent. This
   is what makes `fold_xml` extractable as `Tot` and is the one law any
   instance — tree or streaming — must actually discharge, not just
   assert.
2. **Determinism / no observable effect**: `expose n` called twice on
   the same `n` produces the same `xml_view` both times. For the tree
   instance this is definitional (pattern match, pure). For a streaming
   instance backed by mutable I/O state (a file handle, a socket
   buffer), this is the property that has to be *engineered*, not
   proved in the usual sense — the node type has to be a cursor/token
   (e.g. "byte offset + a handle to the already-decoded prefix") whose
   `expose` re-derives the view from that cursor rather than mutating
   shared state, so two calls with the same cursor value agree. This is
   the same discipline `Parser.Combinators`' `parser` type already uses
   (a pure function of `input * pos`, not a stateful reader) — a
   streaming `xml_document` is that same shape lifted from bytes to
   nodes.
3. **Faithfulness to a reference parse**: for a streaming producer to be
   an acceptable substitute for the concrete tree, `fold_xml` applied to
   it must produce the same accumulator, for every `f`, as `fold_xml`
   applied to the tree instance built from the same input bytes by
   `Parser.XML.parse_xml_document`. That is a simulation/round-trip
   obligation, not a from-scratch proof of XML well-formedness — the
   same shape as the hash-witness pattern rule #11(b) already uses for
   Option-B perf realizations (byte-format spec lives in F*, the OCaml
   side is checked against it by a witness test, not reproved). A
   streaming producer's F* obligation is therefore: implement `expose`
   in terms of a **verified single-node-header parser** (a `Tot`
   function `bytes -> pos -> (xml_view_header & list child_cursor)`,
   living in F* next to `Parser.XML.fst`'s existing per-construct
   parsers), with only the "read more bytes from the wire" step as an
   `assume val` I/O realization (rule #11(a): pure I/O). The byte-layout
   logic — how a `<tag attr="v">` header decodes — stays specified and
   verified in F*; the OCaml glue reduces to `read_bytes`, exactly the
   companion-file discipline rule #11 already requires elsewhere.

## `xml_node` as the first (trivial) instance

```fstar
let measure_node (n:Parser.XML.xml_node) : nat = ... (* structural size *)

let expose_node (n:Parser.XML.xml_node) : xml_view Parser.XML.xml_node =
  match n with
  | Parser.XML.XText t         -> VText t
  | Parser.XML.XElement t a c  -> VElement t a c
  | Parser.XML.XComment t      -> VComment t
  | Parser.XML.XCDATA t        -> VCDATA t
  | Parser.XML.XPI tgt d       -> VPI tgt d

let xml_node_document (root:Parser.XML.xml_node) : xml_document = {
  node = Parser.XML.xml_node;
  root = root;
  measure = measure_node;
  expose = expose_node;
  descent_law = (fun n -> () (* structural size strictly decreases into
                                 each child by construction of xml_node
                                 as an inductive type -- provable, not
                                 sketched here *))
}
```

`expose_node` is a one-line unwrap; the whole tree already exists in
memory (that is exactly the DOM-materialization cost measured in the
findings doc), so this instance pays that cost up front and `expose`
does no further work. It is the reference instance the RDF/XML mapping
proof ships against first — nothing about the interface design changes
what gets built for it now.

## What a streaming producer's obligation looks like (sketch only)

A producer reading, say, a chunked HTTP body or a large file without
holding it all in memory would represent `node` as a cursor — position
plus enough decoded lookahead to answer one `expose` call — and
implement `expose` by calling into the same per-construct parsers
`Parser.XML.fst` already has (`parse_xml_element`'s header portion,
`parse_xml_comment`, `parse_xml_cdata`, `parse_xml_pi`, `parse_xml_text`)
rather than reimplementing byte-level XML grammar in OCaml (rule #4: new
parsers belong in F* first). The `children` list `VElement` returns
would be cursors pointing at "the next unread child", not parsed
subtrees — so a `fold_xml` walk over it advances the stream one node at
a time and never holds more than the current path's siblings-so-far.
Concretely, this needs:

- A `Tot`, F*-specified "parse one node's header and the cursor for its
  first child (if any) and next sibling (if any)" function, alongside
  the existing per-construct parsers.
- An `assume val` (rule #11(a), pure I/O) for "block for more bytes if
  the cursor has run past what is buffered" — the only place OCaml is
  allowed to exist in this path.
- A round-trip test (rule #11(b) style, a hash-witness or direct
  structural-equality test over `fold_xml` accumulators) comparing the
  streaming instance against the tree instance on the W3C `xmlconf`
  corpus, before any claim that the streaming producer is a legitimate
  substitute.

None of this is built. This document is the shape the recovery-plan-style
follow-up work would target — recorded here so the RDF/XML mapping proof
that comes next is written against `xml_document`/`fold_xml`, not against
`Parser.XML.xml_node`'s constructors directly, and so a streaming
producer slots in later without reopening the mapping proof.

## Relationship to the findings doc

The deep-nesting native-stack limit
(`docs/designissues/2026-08-10-xml-generality-findings.md`, row #36) is
a property of the *tree-building* parser, not of this interface: a
`fold_xml` walk driven by a streaming producer's cursor-based `expose`
does not need to hold `depth`-many stack frames of *already-built*
`XElement` values the way `parse_xml_element`/`parse_children` do today
— an explicit work-list-driven fold (rather than the native call stack)
removes that failure mode by construction. That is a reason to prefer
this interface for any future adversarial-input hardening, independent
of the DOM-materialization motivation above.
