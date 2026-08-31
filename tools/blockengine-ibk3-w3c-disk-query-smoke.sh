#!/usr/bin/env bash
# Run two approved W3C SPARQL basic-evaluation fixtures through the paged
# persistent path: W3C Turtle -> IBK3/PTD1 + SBM2/Merkle -> parsed W3C query.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
fixture_dir="$repo_root/third_party/testing/w3c/sparql/sparql10/basic"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-ibk3-w3c-disk-query.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

for fixture in data-6.ttl spoo-1.rq spoo-1.srx data-7.ttl bgp-no-match.rq bgp-no-match.srx; do
  test -f "$fixture_dir/$fixture"
done

matching_root="$run_dir/spoo-1"
matching_store="$matching_root/first"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-6.ttl" "$matching_store" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$matching_root" first >/dev/null
matching=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$matching_root" --query \
  "$(<"$fixture_dir/spoo-1.rq")")

empty_root="$run_dir/bgp-no-match"
empty_store="$empty_root/first"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-7.ttl" "$empty_store" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$empty_root" first >/dev/null
empty=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$empty_root" --query \
  "$(<"$fixture_dir/bgp-no-match.rq")")

printf '%s\n' "$matching"
printf '%s\n' "$empty"

# spoo-1.srx has exactly one ?s binding, http://example.org/ns#x.
grep -q 'open-mode=ibk3-paged-merkle(2)' <<<"$matching"
grep -q 'rows=1 ' <<<"$matching"
grep -q 'Term.iri "http://example.org/ns#x"' <<<"$matching"

# bgp-no-match.srx has an empty results element. Its distinct predicates also
# exercise the SRI2/TLI1 shared-subject join admission before the ordinary
# parsed evaluator confirms that no bindings survive.
grep -q 'open-mode=ibk3-sri2-tli1-subject-join(2)' <<<"$empty"
grep -q 'rows=0 ' <<<"$empty"

echo 'blockengine-ibk3-w3c-disk-query-smoke=pass'
