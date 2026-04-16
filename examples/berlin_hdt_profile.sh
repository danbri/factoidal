#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
HDT="${1:-/tmp/Corpus3/berlin-dbpedia-page/v1/data.hdt}"

"${BIN}" \
  --data-hdt "${HDT}" \
  -e '
    SELECT ?country ?thumb ?type WHERE {
      <http://dbpedia.org/resource/Berlin>
        <http://dbpedia.org/ontology/country> ?country .
      <http://dbpedia.org/resource/Berlin>
        <http://dbpedia.org/ontology/thumbnail> ?thumb .
      <http://dbpedia.org/resource/Berlin>
        <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> ?type .
    }'
