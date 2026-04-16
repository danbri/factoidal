#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
HDT="${1:-/tmp/Corpus3/berlin-dbpedia-page/v1/data.hdt}"
GRAPH_IRI="${2:-https://factoidaldb.com/id/graph/berlin}"

"${BIN}" \
  --named-hdt "${GRAPH_IRI}=${HDT}" \
  -e 'PREFIX dbr: <http://dbpedia.org/resource/>
      PREFIX dbo: <http://dbpedia.org/ontology/>
      SELECT ?g ?o WHERE {
        GRAPH ?g {
          dbr:Berlin dbo:country ?o .
        }
      }'
