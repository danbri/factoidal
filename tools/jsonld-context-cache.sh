#!/bin/bash
# Thin front door to tools/jsonld_context_cache.py — the offline,
# URL-keyed JSON-LD @context cache under third_party/jsonld-context-cache/.
#
#   tools/jsonld-context-cache.sh add URL...      fetch + store (idempotent)
#   tools/jsonld-context-cache.sh resolve URL     print cached body, no network
#   tools/jsonld-context-cache.sh refresh         re-fetch every known URL
#   tools/jsonld-context-cache.sh verify          re-hash every snapshot
#   tools/jsonld-context-cache.sh list            print the index
#
# All logic lives in the Python module so there is ONE implementation to
# reason about: retries, URL normalization, atomic writes, index locking
# and digest checks are not duplicated here. A consumer that wants the
# read path in-process should import `resolve_body` rather than shell out.
#
# Docs: skills/jsonld-context-cache/SKILL.md

set -euo pipefail
ROOT="$(git -C "$(dirname "${BASH_SOURCE[0]}")" rev-parse --show-toplevel)"
exec python3 "$ROOT/tools/jsonld_context_cache.py" \
  --cache "$ROOT/third_party/jsonld-context-cache" "$@"
