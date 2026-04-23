#!/usr/bin/env bash
# serve-lifesci-demo.sh — launch a SPARQL endpoint populated with the
# same three Wikidata life-sciences graphs as the browser demo.
#
#   chromosome.ttl        → <urn:kgx:chromosome>
#   sequence_variant.ttl  → <urn:kgx:sequence_variant>
#   disease.ttl           → <urn:kgx:disease>
#
# Usage:
#   ./serve-lifesci-demo.sh              # port 3030, loopback only
#   ./serve-lifesci-demo.sh --port 4040  # custom port
#   ./serve-lifesci-demo.sh --host 0.0.0.0 --read-only
#                                        # bind all interfaces, block UPDATE
#   ./serve-lifesci-demo.sh --union-default
#                                        # ALSO load every triple into the
#                                        # default graph, so bare
#                                        # `SELECT ?s ?p ?o WHERE{?s ?p ?o}`
#                                        # queries return data without
#                                        # needing a GRAPH wrapper. Default
#                                        # is off (pure named-graph shape).
#
# Once running:
#   - Every triple lives in one of the three named graphs
#     <urn:kgx:chromosome>, <urn:kgx:sequence_variant>, <urn:kgx:disease>.
#   - A bare SPARQL `WHERE { ?s ?p ?o }` therefore returns zero rows —
#     you must wrap with `GRAPH ?g { … }` to read a named graph. That's
#     SPARQL 1.1's default-vs-named-graph distinction, not a bug.
#   - Pass `--union-default` if you want a query-it-like-one-big-graph
#     shape where triples also show up in the default graph.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  BIN="bin/darwin-arm64/factoidal-http" ;;
  Linux-x86_64)  BIN="bin/linux-x86_64/factoidal-http" ;;
  *) echo "Unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 2 ;;
esac
[ -x "$BIN" ] || { echo "Missing binary: $BIN — run 'cd formal/fstar && ./build-ocaml.sh compile' first" >&2; exit 2; }

# Scan args for our own --union-default flag; everything else passes
# straight through to factoidal-http.
UNION_DEFAULT=0
FORWARD_ARGS=()
for arg in "$@"; do
  if [ "$arg" = "--union-default" ]; then UNION_DEFAULT=1
  else FORWARD_ARGS+=("$arg")
  fi
done

LIFESCI="docs/fstar-extracted/lifesci"
for f in chromosome.ttl sequence_variant.ttl disease.ttl; do
  [ -f "$LIFESCI/$f" ] || { echo "Missing data file: $LIFESCI/$f" >&2; exit 2; }
done

# Assemble an N-Quads file — one line per triple, last column is the
# graph IRI. factoidal-http loads this via --load-rw-graphs (the
# canonical multi-named-graph ingress for the server). We use
# factoidal --dump to convert each TTL to N-Triples, then append the
# graph IRI to each line.
SCRATCH="$(mktemp -d)"
NQ="$SCRATCH/lifesci.nq"
DEFAULT_NT="$SCRATCH/lifesci.nt"
trap 'rm -rf "$SCRATCH"' EXIT

echo "Building combined N-Quads dataset at $NQ …"
for pair in \
  chromosome.ttl=urn:kgx:chromosome \
  sequence_variant.ttl=urn:kgx:sequence_variant \
  disease.ttl=urn:kgx:disease
do
  TTL="${pair%=*}"
  GRAPH="${pair#*=}"
  echo "  ${TTL}  →  <${GRAPH}>"
  NT="${BIN%factoidal-http}factoidal"
  "$NT" --dump --format turtle "$LIFESCI/$TTL" | tee -a "$DEFAULT_NT" | \
    awk -v g="<${GRAPH}>" '{sub(/ \.$/, " " g " ."); print}' >> "$NQ"
done

TRIPLE_COUNT=$(wc -l < "$NQ" | tr -d ' ')
echo ""
echo "Loaded ${TRIPLE_COUNT} triples across 3 named graphs."
if [ $UNION_DEFAULT -eq 1 ]; then
  echo "Also duplicating every triple into the DEFAULT graph (--union-default)."
fi
echo ""

# Default port — can be overridden by passing args straight through.
HAVE_PORT=0
for a in "${FORWARD_ARGS[@]}"; do
  case "$a" in -p|-p=*|--port|--port=*) HAVE_PORT=1 ;; esac
done
if [ $HAVE_PORT -eq 0 ]; then FORWARD_ARGS=(--port 3030 "${FORWARD_ARGS[@]}"); fi

cat <<'USAGE'
Starting factoidal-http …
Data is in three NAMED GRAPHS. Queries that don't wrap with GRAPH { … }
will read the (empty) default graph and return zero rows. Try:

  curl -H 'Accept: application/sparql-results+json' \
    --data-urlencode 'query=SELECT * WHERE { GRAPH ?g { ?s ?p ?o } } LIMIT 5' \
    http://127.0.0.1:3030/query

  curl -H 'Accept: application/sparql-results+json' \
    --data-urlencode 'query=SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g' \
    http://127.0.0.1:3030/query

Re-run with --union-default if you want every triple in the default
graph too, so bare `WHERE { ?s ?p ?o }` queries return data.

Stop with Ctrl-C.
USAGE

if [ $UNION_DEFAULT -eq 1 ]; then
  exec "$BIN" --dataset "$DEFAULT_NT" --format ntriples --load-rw-graphs "$NQ" "${FORWARD_ARGS[@]}"
else
  exec "$BIN" --load-rw-graphs "$NQ" "${FORWARD_ARGS[@]}"
fi
