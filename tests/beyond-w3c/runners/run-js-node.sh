#!/usr/bin/env bash
# tests/beyond-w3c/runners/run-js-node.sh
#
# Phase 2a (#243): run a SPARQL query through the js_of_ocaml bundle
# under Node. Prints SPARQL Results JSON to stdout, same surface as
# run-native.sh, so run-parity.py can compare bundle output against
# native uniformly.
#
# Usage:
#   run-js-node.sh --query QUERY.rq --data FILE[:FORMAT[:GRAPH]] [--data ...]
#
# Why this is the same surface as run-native.sh:
# the bundle's CLI is the F*-extracted `factoidal_cli` driver —
# `node docs/fstar-extracted/factoidal.js -d X.ttl --query Q.rq -o json`
# accepts exactly the same flag set the native binary does. File I/O
# under Node goes through MlNodeFd → require('node:fs'), reading raw
# UTF-8 bytes; no jsoo_fs_tmp transcode is involved. The browser path
# (factoidal-sparql-client.js) DOES transcode at the JS↔OCaml boundary
# (see #240) — different concern, different runner (Phase 3 #245).

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$REPO_ROOT"

JS_BUNDLE="docs/fstar-extracted/factoidal.js"
[[ -f "$JS_BUNDLE" ]] || { echo "missing: $JS_BUNDLE (run ./formal/fstar/build-ocaml.sh js)" >&2; exit 2; }

command -v node >/dev/null || { echo "node not found on PATH" >&2; exit 2; }

QUERY=""
ARGS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --query) QUERY="$2"; shift 2 ;;
    --data)
      # Accept FILE[:FORMAT[:GRAPH]]
      spec="$2"; shift 2
      file="${spec%%:*}"
      rest="${spec#*:}"
      if [[ "$rest" == "$spec" ]]; then
        ARGS+=( --data "$file" )
      else
        format="${rest%%:*}"
        graph="${rest#*:}"
        if [[ "$graph" == "$rest" ]]; then
          ARGS+=( --data "$file" --format "$format" )
        else
          ARGS+=( --named "$graph=$file" --format "$format" )
        fi
      fi
      ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

[[ -n "$QUERY" ]] || { echo "missing --query" >&2; exit 2; }

exec node "$JS_BUNDLE" --query "$QUERY" -o json "${ARGS[@]}"
