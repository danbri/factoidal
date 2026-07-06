"""Shared SPARQL query text for tools/bench_competitive.py.

One module so the exact same query STRING (not just the same logical
query) is sent to every engine -- byte-identical SPARQL text is the
whole point of a same-workload comparison. Every query here was
validated against the reference corpus
(examples/wikidata/subsets/lifesci-kgx/data/gene.ttl, 888,949 triples)
with pyoxigraph before being locked in; the row counts in each
description are the pyoxigraph-measured ground truth used only to
pick informative queries -- the actual benchmark run re-derives and
cross-checks every answer independently per engine (a benchmark row
where engines disagree is VOID, not reported as a timing; see
bench_competitive.py's `compare_answers`).

Predicate frequencies on gene.ttl (SPARQL GROUP BY, not text-grepped):
  wdt:P684  759,263  (gene-gene relation; dominates, 85% of triples)
  rdf:type   91,871  (bio:Gene for every subject)
  wdt:P1057  25,058
  wdt:P688   10,422
  wdt:P527    2,331
  wdt:P682        4  (rarest -- used for the join query)
"""

QUERIES = {
    "q1_count_star": {
        "sparql": "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }",
        "description": "COUNT(*) over the whole default graph.",
        "category": "aggregate-full-scan",
    },
    "q2_bound_predicate_count": {
        "sparql": (
            "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\n"
            "SELECT (COUNT(*) AS ?c) WHERE { ?s wdt:P684 ?o }"
        ),
        "description": (
            "Bound-predicate COUNT on wdt:P684, the dominant predicate "
            "(759,263 of 888,949 triples on gene.ttl)."
        ),
        "category": "aggregate-bound-predicate",
    },
    "q3_subject_point_lookup": {
        "sparql": (
            "PREFIX wd: <http://www.wikidata.org/entity/>\n"
            "SELECT ?p ?o WHERE { wd:Q100085837 ?p ?o }"
        ),
        "description": (
            "Subject point lookup: all (p, o) for one fixed subject "
            "IRI present in gene.ttl (3 triples: 1 rdf:type + 2 "
            "wdt:P684 edges)."
        ),
        "category": "point-lookup",
    },
    "q4_two_pattern_join": {
        "sparql": (
            "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\n"
            "SELECT ?s ?o1 ?o2 WHERE { ?s wdt:P684 ?o1 . ?s wdt:P682 ?o2 }"
        ),
        "description": (
            "Same-subject 2-pattern join between the dominant predicate "
            "(wdt:P684) and the rarest one (wdt:P682, 4 triples total); "
            "14 result rows on gene.ttl."
        ),
        "category": "join",
    },
    "q5_group_by": {
        "sparql": (
            "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\n"
            "SELECT ?p (COUNT(*) AS ?c) WHERE { ?s ?p ?o } GROUP BY ?p"
        ),
        "description": (
            "GROUP BY predicate over the whole default graph; 6 groups "
            "on gene.ttl."
        ),
        "category": "group-by",
    },
    "q6_optional_filter": {
        "sparql": (
            "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\n"
            "SELECT ?s ?o1 ?o2 WHERE {\n"
            "  ?s wdt:P1057 ?o1 .\n"
            "  OPTIONAL { ?s wdt:P688 ?o2 }\n"
            "  FILTER(isIRI(?o1))\n"
            "}"
        ),
        "description": (
            "Required wdt:P1057 pattern + OPTIONAL wdt:P688 + a FILTER; "
            "25,083 rows on gene.ttl, 9,117 with the optional var bound."
        ),
        "category": "optional-filter",
    },
}
