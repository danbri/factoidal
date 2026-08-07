"""
SPARQL query generator for the differential harness (issue #317).

Generates a fixed battery of query SHAPES (BGP join, OPTIONAL, UNION,
FILTER incl. lang()/datatype boundaries, property path, ASK, aggregate,
CONSTRUCT, VALUES) parameterized against ONE rdfgen.Doc's backbone --
so results are non-trivial (the backbone is a small connected "mini
database", see rdfgen._backbone) while the surrounding graph is still the
full adversarial fuzz content (unicode, boundary literals, deep bnode
nesting) that the query has to evaluate correctly around/through.
"""
from __future__ import annotations

PREFIX = "PREFIX ex: <http://example.org/onto#>\n"


def entity_iris(doc) -> list:
    return [t[1] for t in doc.backbone_subjects if t[0] == "I"]


def queries_for(doc) -> list:
    """Returns a list of (name, query_text, expected_form) tuples.
    expected_form is one of 'select', 'ask', 'construct'."""
    qs = []
    iris = entity_iris(doc)

    qs.append((
        "bgp_typed_name",
        PREFIX + "SELECT ?s ?name WHERE { ?s ex:typeOf ex:Person . ?s ex:name ?name }",
        "select",
    ))
    qs.append((
        "optional_note",
        PREFIX + "SELECT ?s ?name ?note WHERE { ?s ex:name ?name . OPTIONAL { ?s ex:note ?note } }",
        "select",
    ))
    qs.append((
        "union_age_note",
        PREFIX + "SELECT ?s ?v WHERE { { ?s ex:age ?v } UNION { ?s ex:note ?v } }",
        "select",
    ))
    qs.append((
        "filter_has_lang",
        PREFIX + 'SELECT ?s ?name WHERE { ?s ex:name ?name . FILTER(lang(?name) != "") }',
        "select",
    ))
    qs.append((
        "filter_integer_boundary",
        PREFIX + "SELECT ?s ?age WHERE { ?s ex:age ?age . FILTER(?age > 1000000000) }",
        "select",
    ))
    qs.append((
        "ask_knows_exists",
        PREFIX + "ASK { ?s ex:knows ?o }",
        "ask",
    ))
    qs.append((
        "count_persons",
        PREFIX + "SELECT (COUNT(?s) AS ?c) WHERE { ?s ex:typeOf ex:Person }",
        "select",
    ))
    qs.append((
        "property_path_knows_plus",
        PREFIX + "SELECT ?s ?o WHERE { ?s ex:knows+ ?o }",
        "select",
    ))
    qs.append((
        "construct_has_name",
        PREFIX + "CONSTRUCT { ?s ex:hasName ?name } WHERE { ?s ex:name ?name }",
        "construct",
    ))
    if iris:
        first = iris[0]
        qs.append((
            "values_clause",
            PREFIX + f"SELECT ?name WHERE {{ VALUES ?s {{ <{first}> }} ?s ex:name ?name }}",
            "select",
        ))
    return qs
