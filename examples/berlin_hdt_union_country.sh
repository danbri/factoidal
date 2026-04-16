#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
HDT1="${1:-/tmp/Corpus3/berlin-dbpedia-page/v1/data.hdt}"
HDT2="${2:-/tmp/Corpus3/berlin-dbpedia-page/v1/data-copy.hdt}"

"${BIN}" \
  --data-hdt "${HDT1}" \
  --data-hdt "${HDT2}" \
  -e 'SELECT ?o WHERE {
        <http://dbpedia.org/resource/Berlin>
          <http://dbpedia.org/ontology/country> ?o
      }'
