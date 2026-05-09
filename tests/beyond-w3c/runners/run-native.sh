#!/usr/bin/env bash
# tests/beyond-w3c/runners/run-native.sh
#
# Phase 2 reference runner: run a SPARQL query against a set of TTL/TriG
# files using the native binary. Prints SPARQL Results JSON to stdout.
#
# Usage:
#   run-native.sh --query QUERY.rq --data FILE[:FORMAT[:GRAPH]] [--data ...]
#
# Sub-issue #243 (JS) and #244 (Wasm) provide siblings with the same
# CLI shape so run-parity.py (Phase 2 orchestrator) can call any of them
# uniformly.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd)"
cd "$REPO_ROOT"

case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) NATIVE_BIN="bin/darwin-arm64/factoidal" ;;
  Linux-x86_64) NATIVE_BIN="bin/linux-x86_64/factoidal" ;;
  *) echo "Unsupported platform: $(uname -s)-$(uname -m)" >&2; exit 2 ;;
esac

[[ -x "$NATIVE_BIN" ]] || { echo "missing: $NATIVE_BIN" >&2; exit 2; }

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

exec "$NATIVE_BIN" --query "$QUERY" -o json "${ARGS[@]}"
