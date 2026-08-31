#!/usr/bin/env bash
# Run two approved W3C SPARQL 1.0 basic-evaluation fixtures through the
# persistent Shardborough path:
#
#   W3C Turtle input -> predicate-local IBK2 + SBM2/Merkle files
#                    -> parsed W3C .rq -> selective disk-backed evaluation
#
# This is intentionally a regression gate, not a claim that the current
# predicate-selective backend implements every W3C SPARQL feature.  The two
# selected manifest entries exercise a matching basic graph pattern (including
# Turtle/SPARQL numeric-literal compatibility) and a non-matching BGP.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
fixture_dir="$repo_root/third_party/testing/w3c/sparql/sparql10/basic"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-w3c-disk-query.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

for fixture in data-6.ttl spoo-1.rq spoo-1.srx data-7.ttl bgp-no-match.rq bgp-no-match.srx; do
  test -f "$fixture_dir/$fixture"
done

matching_store="$run_dir/spoo-1"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-6.ttl" "$matching_store" >/dev/null
matching=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$matching_store" --query \
  "$(<"$fixture_dir/spoo-1.rq")")

empty_store="$run_dir/bgp-no-match"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-7.ttl" "$empty_store" >/dev/null
empty=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$empty_store" --query \
  "$(<"$fixture_dir/bgp-no-match.rq")")

printf '%s\n' "$matching"
printf '%s\n' "$empty"

# spoo-1.srx has exactly one binding: ?s = http://example.org/ns#x.
grep -q 'open-mode=predicate-selective-merkle(2)' <<<"$matching"
grep -q 'rows=1 ' <<<"$matching"
grep -q 'Term.iri "http://example.org/ns#x"' <<<"$matching"

# bgp-no-match.srx has an empty <results/> element.
grep -q 'open-mode=predicate-selective-merkle(2)' <<<"$empty"
grep -q 'rows=0 ' <<<"$empty"

echo 'blockengine-w3c-disk-query-smoke=pass'
