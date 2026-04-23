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
#
# Once running, query it:
#   curl "http://127.0.0.1:3030/sparql?query=SELECT+(COUNT(*)+AS+?n)+WHERE+%7B%7Bgraph+%3Fg+%7B?s+?p+?o%7D%7D%7D"
# Or via factoidal-http's browsable UI at http://127.0.0.1:3030/

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$REPO_ROOT"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64)  BIN="bin/darwin-arm64/factoidal-http" ;;
  Linux-x86_64)  BIN="bin/linux-x86_64/factoidal-http" ;;
  *) echo "Unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 2 ;;
esac
[ -x "$BIN" ] || { echo "Missing binary: $BIN — run 'cd formal/fstar && ./build-ocaml.sh compile' first" >&2; exit 2; }

LIFESCI="docs/fstar-extracted/lifesci"
for f in chromosome.ttl sequence_variant.ttl disease.ttl; do
  [ -f "$LIFESCI/$f" ] || { echo "Missing data file: $LIFESCI/$f" >&2; exit 2; }
done

# Assemble an N-Quads file — one line per triple, last column is the
# graph IRI. factoidal-http loads this via --load-rw-graphs (the
# canonical multi-named-graph ingress for the server). We use
# factoidal --dump to convert each TTL to N-Triples, then append the
# graph IRI to each line.
NQ="$(mktemp -d)/lifesci.nq"
trap 'rm -rf "$(dirname "$NQ")"' EXIT

echo "Building combined N-Quads dataset at $NQ …"
for pair in \
  chromosome.ttl=urn:kgx:chromosome \
  sequence_variant.ttl=urn:kgx:sequence_variant \
  disease.ttl=urn:kgx:disease
do
  TTL="${pair%=*}"
  GRAPH="${pair#*=}"
  echo "  ${TTL}  →  <${GRAPH}>"
  "${BIN%factoidal-http}factoidal" --dump --format turtle "$LIFESCI/$TTL" | \
    awk -v g="<${GRAPH}>" '{sub(/ \.$/, " " g " ."); print}' >> "$NQ"
done

TRIPLE_COUNT=$(wc -l < "$NQ" | tr -d ' ')
echo ""
echo "Loaded ${TRIPLE_COUNT} triples across 3 named graphs."
echo ""

# Default port / host — can be overridden by passing args straight
# through to factoidal-http.
if [[ "$*" != *"--port"* && "$*" != *"-p "* ]]; then
  set -- "$@" --port 3030
fi

echo "Starting factoidal-http …"
echo "  Health check: curl http://127.0.0.1:3030/"
echo "  SPARQL GET:   curl 'http://127.0.0.1:3030/sparql?query=SELECT+*+WHERE+%7BGRAPH+%3Fg+%7B%3Fs+%3Fp+%3Fo%7D%7D+LIMIT+5'"
echo "  Stop with Ctrl-C."
echo ""
exec "$BIN" --load-rw-graphs "$NQ" "$@"
