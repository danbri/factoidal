#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
HDT="${1:-/tmp/Corpus3/berlin-dbpedia-page/v1/data.hdt}"

"${BIN}" \
  --data-hdt "${HDT}" \
  -e '
    SELECT ?o WHERE {
      <http://dbpedia.org/resource/Berlin>
        <http://dbpedia.org/ontology/country> ?o .
    }'
