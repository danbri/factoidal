"""
RDF fuzz-corpus generator (issue #317, gate 4: independent differential testing).

Design: build ONE abstract graph model per generated instance (subject/
predicate/object triples using internal blank-node keys, optionally split
across named graphs), then render that SAME abstract graph into every
concrete syntax Factoidal supports (N-Triples, N-Quads, Turtle, TriG,
RDF/XML). This buys two checks for the price of one generation step:

  1. cross-format self-consistency: our own parser's canonical output for
     the N-Triples rendering of a graph must equal its canonical output for
     the Turtle/TriG/RDF-XML rendering of the SAME graph.
  2. cross-implementation agreement: our canonical output must equal an
     independent implementation's (pyoxigraph / Oxigraph, Rust) canonical
     output for the same source bytes -- this is the actual differential
     test, see rdf_diff.py.

Two profiles:
  - "graph"   -- single (default) graph, rendered in all 5 syntaxes.
  - "dataset" -- multiple named graphs, rendered in N-Quads + TriG only
                 (the two syntaxes with dataset/named-graph support).

Bias, per the issue brief: blank-node-heavy graphs, unicode/escaping edge
cases, datatype boundary literals, deeply nested structures, unusual-case
language tags -- see atoms.py for the underlying term generators.
"""
from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Optional

import atoms

IRI = tuple  # ('I', iri_string)
BNODE = tuple  # ('B', internal_key)
LIT = tuple  # ('L', lexical, datatype_or_None, lang_or_None)


def T_iri(s: str):
    return ("I", s)


def T_bnode(key):
    return ("B", key)


def T_lit(lexical: str, datatype: Optional[str], lang: Optional[str]):
    return ("L", lexical, datatype, lang)


@dataclass
class Doc:
    """One abstract RDF graph/dataset instance plus bookkeeping for the
    SPARQL query generator (sparqlgen.py)."""

    triples: list = field(default_factory=list)          # default graph: (s,p,o)
    named: dict = field(default_factory=dict)             # iri_string -> [(s,p,o), ...]
    collections: list = field(default_factory=list)        # (s, p, nested_list) rendered as Turtle/TriG sugar
    bnode_labels: dict = field(default_factory=dict)       # internal key -> lexical label (Turtle-legal)
    backbone_predicates: dict = field(default_factory=dict)  # name -> iri, for query generation
    backbone_subjects: list = field(default_factory=list)  # terms used as backbone subjects
    seed: int = 0
    profile: str = "graph"


def _new_bnode_factory():
    counter = {"n": 0}

    def make(rng, doc: Doc):
        key = counter["n"]
        counter["n"] += 1
        doc.bnode_labels[key] = atoms.bnode_label(rng, key)
        return T_bnode(key)

    return make


def _rand_object(rng, doc, bnode_factory, bnode_bias: float):
    r = rng.random()
    if r < bnode_bias:
        return bnode_factory(rng, doc)
    if r < bnode_bias + 0.30:
        return T_iri(atoms.iri(rng))
    lex, dt, lang = atoms.literal(rng)
    return T_lit(lex, dt, lang)


def _rand_subject(rng, doc, bnode_factory, bnode_bias: float):
    if rng.random() < bnode_bias:
        return bnode_factory(rng, doc)
    return T_iri(atoms.iri(rng))


def _backbone(rng, doc: Doc, n_entities: int, bnode_bias: float, bnode_factory):
    """A small connected 'mini database' so SPARQL queries reliably have
    non-trivial results: n_entities each with :name, :age, :knows (links to
    other entities), :lang (a language-tagged literal), :note (boundary
    literal)."""
    vocab = {
        "name": "http://example.org/onto#name",
        "age": "http://example.org/onto#age",
        "knows": "http://example.org/onto#knows",
        "note": "http://example.org/onto#note",
        "typeOf": "http://example.org/onto#typeOf",
    }
    doc.backbone_predicates = vocab

    entities = []
    for i in range(n_entities):
        subj = bnode_factory(rng, doc) if rng.random() < bnode_bias else T_iri(f"http://example.org/entity/e{i}")
        entities.append(subj)
    doc.backbone_subjects = entities

    for i, subj in enumerate(entities):
        name_lex, _, name_lang = ("Entity " + str(i) + " " + rng.choice(["café", "日本語", "naïve"]), None,
                                   atoms.lang_tag(rng) if rng.random() < 0.5 else None)
        doc.triples.append((subj, T_iri(vocab["name"]), T_lit(name_lex, None, name_lang)))

        age_lex, age_dt, _ = rng.choice(atoms.INTEGER_BOUNDARIES), atoms.XSD + "integer", None
        doc.triples.append((subj, T_iri(vocab["age"]), T_lit(age_lex, age_dt, None)))

        note_lex, note_dt, note_lang = atoms.literal(rng)
        doc.triples.append((subj, T_iri(vocab["note"]), T_lit(note_lex, note_dt, note_lang)))

        doc.triples.append((subj, T_iri(vocab["typeOf"]), T_iri("http://example.org/onto#Person")))

        # a couple of :knows edges to build joinable structure (including
        # self-loops and mutual pairs -- deliberately adversarial)
        for _ in range(rng.randint(0, 2)):
            target = rng.choice(entities)
            doc.triples.append((subj, T_iri(vocab["knows"]), target))


def _bnode_chain(rng, doc: Doc, depth: int, bnode_factory):
    pred = T_iri("http://example.org/onto#next")
    head = bnode_factory(rng, doc)
    cur = head
    for _ in range(depth):
        nxt = bnode_factory(rng, doc)
        doc.triples.append((cur, pred, nxt))
        cur = nxt
    lex, dt, lang = atoms.literal(rng)
    doc.triples.append((cur, T_iri("http://example.org/onto#leaf"), T_lit(lex, dt, lang)))
    return head


def _bnode_tree(rng, doc: Doc, depth: int, branching: int, bnode_factory):
    pred = T_iri("http://example.org/onto#child")

    def build(d):
        node = bnode_factory(rng, doc)
        if d <= 0:
            lex, dt, lang = atoms.literal(rng)
            doc.triples.append((node, T_iri("http://example.org/onto#leafval"), T_lit(lex, dt, lang)))
            return node
        for _ in range(branching):
            child = build(d - 1)
            doc.triples.append((node, pred, child))
        return node

    return build(depth)


def _symmetric_cycle(rng, doc: Doc, k: int, bnode_factory):
    """A k-cycle of otherwise-indistinguishable blank nodes connected by the
    SAME predicate -- a known hard case for naive canonicalization (the
    Hash First-Degree Quads step alone cannot break the symmetry; the
    algorithm must fall through to Hash N-Degree Quads)."""
    pred = T_iri("http://example.org/onto#cyc")
    nodes = [bnode_factory(rng, doc) for _ in range(k)]
    for i in range(k):
        doc.triples.append((nodes[i], pred, nodes[(i + 1) % k]))
    return nodes


def _collection(rng, doc: Doc, depth: int, width: int, bnode_factory):
    """Build a nested list value both as explicit rdf:first/rdf:rest/rdf:nil
    triples (for N-Triples/N-Quads/RDF-XML) AND record the nested Python
    structure so the Turtle/TriG serializer can render native '( ... )'
    collection sugar for the SAME semantic content."""
    RDF_FIRST = T_iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#first")
    RDF_REST = T_iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#rest")
    RDF_NIL = T_iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#nil")

    def leaf_item():
        if rng.random() < 0.5:
            v = atoms.iri(rng)
            return T_iri(v), ("iri", v)
        lex, dt, lang = atoms.literal(rng)
        return T_lit(lex, dt, lang), ("lit", lex, dt, lang)

    def build(d):
        """Returns (head_term_or_RDF_NIL, nested_python_repr_list). Each
        entry of the returned repr list is one of:
          ("nested", <nested_repr_list>)
          ("lit", lex, dt, lang)
          ("iri", iri_string)
        """
        items = []  # list of (value_term, repr_entry)
        n = rng.randint(1, width)
        for _ in range(n):
            if d > 0 and rng.random() < 0.4:
                sub_head, sub_repr = build(d - 1)
                items.append((sub_head, ("nested", sub_repr)))
            else:
                term, repr_entry = leaf_item()
                items.append((term, repr_entry))

        # materialize as explicit rdf:first/rest/nil chain
        cells = [bnode_factory(rng, doc) for _ in items]
        for idx, (value_term, _repr_entry) in enumerate(items):
            cell = cells[idx]
            doc.triples.append((cell, RDF_FIRST, value_term))
            nxt = cells[idx + 1] if idx + 1 < len(cells) else RDF_NIL
            doc.triples.append((cell, RDF_REST, nxt))
        head = cells[0] if cells else RDF_NIL
        nested_repr = [repr_entry for _term, repr_entry in items]
        return head, nested_repr

    head, nested_repr = build(depth)
    return head, nested_repr


def generate_graph(seed: int, profile: str = "graph", size: str = "medium") -> Doc:
    rng = random.Random(seed)
    doc = Doc(seed=seed, profile=profile)
    bnode_factory = _new_bnode_factory()

    bnode_bias = rng.choice([0.35, 0.55, 0.75])  # "blank-node-heavy" bias, varies per instance
    n_entities = {"small": 3, "medium": 6, "large": 12}[size]

    _backbone(rng, doc, n_entities, bnode_bias, bnode_factory)

    # deep nesting: chain + tree, depth scaled by size
    depth = {"small": 4, "medium": 9, "large": 18}[size]
    _bnode_chain(rng, doc, depth, bnode_factory)
    _bnode_tree(rng, doc, depth=min(depth, 5), branching=2, bnode_factory=bnode_factory)

    # symmetric cycles: classic RDFC-1.0 stress case
    for k in (2, 3, 5):
        _symmetric_cycle(rng, doc, k, bnode_factory)

    # nested collection, rendered as native sugar in Turtle/TriG, explicit
    # rdf:first/rest/nil triples elsewhere
    coll_subj = bnode_factory(rng, doc) if rng.random() < bnode_bias else T_iri("http://example.org/entity/collection-holder")
    coll_pred = T_iri("http://example.org/onto#items")
    coll_head, coll_repr = _collection(rng, doc, depth=2, width=3, bnode_factory=bnode_factory)
    doc.triples.append((coll_subj, coll_pred, coll_head))
    doc.collections.append((coll_subj, coll_pred, coll_repr))

    # extra flat noise triples for general parser stress (unicode IRIs,
    # boundary literals, unusual lang tags all mixed in)
    n_noise = {"small": 10, "medium": 25, "large": 60}[size]
    for _ in range(n_noise):
        s = _rand_subject(rng, doc, bnode_factory, bnode_bias)
        p = T_iri(atoms.iri(rng, ontology_safe=True))
        o = _rand_object(rng, doc, bnode_factory, bnode_bias)
        doc.triples.append((s, p, o))

    if profile == "dataset":
        # split some of the triples into 2-3 named graphs; keep the rest default
        graph_names = [f"http://example.org/graph/g{i}" for i in range(rng.randint(2, 3))]
        all_triples = doc.triples
        doc.triples = []
        doc.named = {g: [] for g in graph_names}
        for t in all_triples:
            if rng.random() < 0.6:
                g = rng.choice(graph_names)
                doc.named[g].append(t)
            else:
                doc.triples.append(t)
        # ensure no named graph is empty (drop empties -- an empty named
        # graph is a valid but uninteresting edge case we don't need here)
        doc.named = {g: ts for g, ts in doc.named.items() if ts}

    return doc


# ---------------------------------------------------------------------------
# Escaping helpers shared by the text-based serializers
# ---------------------------------------------------------------------------

def escape_literal(s: str, rng: random.Random, raw_newlines_ok: bool = False, unicode_escape_prob: float = 0.15) -> str:
    out = []
    for ch in s:
        cp = ord(ch)
        if ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\n" and not raw_newlines_ok:
            out.append("\\n")
        elif ch == "\r" and not raw_newlines_ok:
            out.append("\\r")
        elif ch == "\t":
            out.append("\\t")
        elif cp < 0x20 and ch not in ("\n", "\r"):
            out.append("\\u%04X" % cp)
        elif cp > 0x7F and rng.random() < unicode_escape_prob:
            if cp > 0xFFFF:
                out.append("\\U%08X" % cp)
            else:
                out.append("\\u%04X" % cp)
        else:
            out.append(ch)
    return "".join(out)


def xml_escape_text(s: str) -> str:
    # &#13; / &#10; as character references (not raw CR/LF) so XML's
    # mandatory end-of-line normalization (XML 1.0 sec 2.11) can't silently
    # change the RDF literal's exact lexical value on a round trip.
    s = s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    s = s.replace("\r\n", "&#13;&#10;").replace("\r", "&#13;").replace("\n", "&#10;")
    return s


def xml_escape_attr(s: str) -> str:
    return xml_escape_text(s).replace('"', "&quot;")


def render_term_nt(term, doc: Doc, rng: random.Random) -> str:
    tag = term[0]
    if tag == "I":
        return f"<{term[1]}>"
    if tag == "B":
        return f"_:{doc.bnode_labels[term[1]]}"
    _, lex, dt, lang = term
    body = f'"{escape_literal(lex, rng)}"'
    if lang:
        body += f"@{lang}"
    elif dt:
        body += f"^^<{dt}>"
    return body


def render_triples_block_nt(triples, doc: Doc, rng: random.Random, graph: Optional[str] = None) -> str:
    lines = []
    for s, p, o in triples:
        s_r = render_term_nt(s, doc, rng)
        p_r = render_term_nt(p, doc, rng)
        o_r = render_term_nt(o, doc, rng)
        if graph is None:
            lines.append(f"{s_r} {p_r} {o_r} .")
        else:
            lines.append(f"{s_r} {p_r} {o_r} <{graph}> .")
    return "\n".join(lines)


def serialize_ntriples(doc: Doc, rng: random.Random) -> str:
    assert doc.profile == "graph"
    return render_triples_block_nt(doc.triples, doc, rng) + "\n"


def serialize_nquads(doc: Doc, rng: random.Random) -> str:
    parts = [render_triples_block_nt(doc.triples, doc, rng)]
    for g, ts in doc.named.items():
        parts.append(render_triples_block_nt(ts, doc, rng, graph=g))
    return "\n".join(p for p in parts if p) + "\n"


def _render_collection_sugar_v2(nested_repr, rng: random.Random) -> str:
    parts = []
    for item in nested_repr:
        kind = item[0]
        if kind == "nested":
            parts.append(_render_collection_sugar_v2(item[1], rng))
        elif kind == "lit":
            _, lex, dt, lang = item
            body = f'"{escape_literal(lex, rng)}"'
            if lang:
                body += f"@{lang}"
            elif dt:
                body += f"^^<{dt}>"
            parts.append(body)
        else:  # "iri"
            parts.append(f"<{item[1]}>")
    return "( " + " ".join(parts) + " )"


def render_term_ttl(term, doc: Doc, rng: random.Random) -> str:
    return render_term_nt(term, doc, rng)


def serialize_turtle_like(triples, doc: Doc, rng: random.Random, collections_here) -> str:
    lines = ["@prefix ex: <http://example.org/onto#> ."]
    coll_subjects = {(s, p): repr_ for (s, p, repr_) in collections_here}
    for s, p, o in triples:
        key = (s, p)
        if key in coll_subjects:
            o_r = _render_collection_sugar_v2(coll_subjects[key], rng)
        else:
            o_r = render_term_ttl(o, doc, rng)
        s_r = render_term_ttl(s, doc, rng)
        p_r = render_term_ttl(p, doc, rng)
        lines.append(f"{s_r} {p_r} {o_r} .")
    return "\n".join(lines) + "\n"


def serialize_turtle(doc: Doc, rng: random.Random) -> str:
    assert doc.profile == "graph"
    return serialize_turtle_like(doc.triples, doc, rng, doc.collections)


def serialize_trig(doc: Doc, rng: random.Random) -> str:
    parts = ["@prefix ex: <http://example.org/onto#> ."]
    coll_subjects = {(s, p): repr_ for (s, p, repr_) in doc.collections}
    for s, p, o in doc.triples:
        key = (s, p)
        o_r = _render_collection_sugar_v2(coll_subjects[key], rng) if key in coll_subjects else render_term_ttl(o, doc, rng)
        parts.append(f"{render_term_ttl(s, doc, rng)} {render_term_ttl(p, doc, rng)} {o_r} .")
    for g, ts in doc.named.items():
        parts.append(f"GRAPH <{g}> {{")
        for s, p, o in ts:
            key = (s, p)
            o_r = _render_collection_sugar_v2(coll_subjects[key], rng) if key in coll_subjects else render_term_ttl(o, doc, rng)
            parts.append(f"  {render_term_ttl(s, doc, rng)} {render_term_ttl(p, doc, rng)} {o_r} .")
        parts.append("}")
    return "\n".join(parts) + "\n"


def _local_name(iri_str: str) -> str:
    if "#" in iri_str:
        return iri_str.rsplit("#", 1)[1]
    return iri_str.rsplit("/", 1)[1]


def serialize_rdfxml(doc: Doc, rng: random.Random) -> str:
    assert doc.profile == "graph"
    lines = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        '<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"',
        '         xmlns:ex="http://example.org/onto#">',
    ]

    # group by subject for valid rdf:Description blocks
    by_subject = {}
    for s, p, o in doc.triples:
        by_subject.setdefault(s, []).append((p, o))

    for s, preds in by_subject.items():
        if s[0] == "I":
            open_tag = f'  <rdf:Description rdf:about="{xml_escape_attr(s[1])}">'
        else:
            open_tag = f'  <rdf:Description rdf:nodeID="{doc.bnode_labels[s[1]]}">'
        lines.append(open_tag)
        for p, o in preds:
            local = _local_name(p[1])
            if o[0] == "I":
                lines.append(f'    <ex:{local} rdf:resource="{xml_escape_attr(o[1])}"/>')
            elif o[0] == "B":
                lines.append(f'    <ex:{local} rdf:nodeID="{doc.bnode_labels[o[1]]}"/>')
            else:
                _, lex, dt, lang = o
                attrs = ""
                if lang:
                    attrs = f' xml:lang="{xml_escape_attr(lang)}"'
                elif dt:
                    attrs = f' rdf:datatype="{xml_escape_attr(dt)}"'
                lines.append(f"    <ex:{local}{attrs}>{xml_escape_text(lex)}</ex:{local}>")
        lines.append("  </rdf:Description>")
    lines.append("</rdf:RDF>")
    return "\n".join(lines) + "\n"


SERIALIZERS_GRAPH = {
    "nt": serialize_ntriples,
    "ttl": serialize_turtle,
    "rdf": serialize_rdfxml,
}
SERIALIZERS_DATASET = {
    "nq": serialize_nquads,
    "trig": serialize_trig,
}
