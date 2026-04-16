#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
HDT="${1:-/tmp/Corpus3/berlin-dbpedia-page/v1/data.hdt}"

"${BIN}" \
  --data-hdt "${HDT}" \
  -e 'PREFIX d: <http://dbpedia.org/>
      SELECT ?country ?thumb ?type WHERE { d:resource/Berlin a ?type ; d:ontology/country ?country ; d:ontology/thumbnail ?thumb . }'
