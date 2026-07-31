#!/bin/bash
# Fetch a JSON-LD @context into the URL-keyed offline cache.
#
#   tools/jsonld-context-cache.sh add URL...     fetch + store (idempotent)
#   tools/jsonld-context-cache.sh verify         re-hash every snapshot
#   tools/jsonld-context-cache.sh list           print the index
#
# Layout (see third_party/jsonld-context-cache/README.md):
#   <cache>/<domain-of-requested-url>/<sha256(url)>.v<N>.jsonld
#
# The key is the REQUESTED url — what documents actually reference —
# never the redirect target. w3id.org URLs redirect to w3c.github.io;
# a document citing the w3id.org IRI must resolve under that IRI.
#
# A new vN is minted only when the fetched bytes differ from the newest
# stored version, so re-running is cheap and history is preserved.

set -euo pipefail
ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
CACHE="$ROOT/third_party/jsonld-context-cache"
INDEX="$CACHE/index.json"
CMD="${1:-list}"; shift || true

[ -f "$INDEX" ] || echo '{"contexts":{}}' > "$INDEX"

case "$CMD" in
add)
  for url in "$@"; do
    domain="$(python3 -c "import sys,urllib.parse;print(urllib.parse.urlparse(sys.argv[1]).netloc)" "$url")"
    urlsha="$(printf '%s' "$url" | sha256sum | cut -d' ' -f1)"
    mkdir -p "$CACHE/$domain"
    tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
    # Capture rc explicitly (anti-pattern #14) — never swallow a failed fetch.
    RC=0
    hdr="$(curl -sS -L --max-time 30 \
            -H 'Accept: application/ld+json, application/json;q=0.9' \
            -w '%{http_code}\t%{content_type}\t%{url_effective}' \
            -o "$tmp" "$url")" || RC=$?
    if [ "$RC" -ne 0 ]; then echo "FETCH FAILED rc=$RC $url" >&2; exit "$RC"; fi
    code="$(printf '%s' "$hdr" | cut -f1)"
    if [ "$code" != "200" ]; then echo "HTTP $code for $url" >&2; exit 1; fi
    python3 "$ROOT/tools/jsonld_context_cache.py" store \
      --cache "$CACHE" --url "$url" --domain "$domain" --url-sha "$urlsha" \
      --body "$tmp" --content-type "$(printf '%s' "$hdr" | cut -f2)" \
      --final-url "$(printf '%s' "$hdr" | cut -f3)"
    rm -f "$tmp"; trap - EXIT
  done
  ;;
verify) python3 "$ROOT/tools/jsonld_context_cache.py" verify --cache "$CACHE" ;;
list)   python3 "$ROOT/tools/jsonld_context_cache.py" list   --cache "$CACHE" ;;
*) echo "usage: $0 {add URL...|verify|list}" >&2; exit 2 ;;
esac
