#!/usr/bin/env bash
# Exercise the native IBK3 persistence route without an in-memory substitute:
# streamed Turtle publication, Merkle-paged parsed SELECT, then DLOG INSERT and
# DELETE replay against the same immutable store.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d /private/tmp/factoidal-ibk3-persistent.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT
store="$run_dir/store"
predicate='http://www.wikidata.org/prop/direct/P31'

pack=$("$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$store" ibk3)
printf '%s\n' "$pack"
grep -q 'format=predicate-ibk3-ptd1-merkle-v0' <<<"$pack"
grep -q 'triples=368 blocks=2' <<<"$pack"

base=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$store" --query \
  "SELECT ?x ?type WHERE { ?x <$predicate> ?type . } LIMIT 2")
printf '%s\n' "$base"
grep -q 'shards=1 open-mode=ibk3-paged-merkle(1) delta=base' <<<"$base"
grep -q 'rows=2' <<<"$base"

insert=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$store" --update \
  "INSERT DATA { <http://example.org/ibk3-smoke> <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$insert"
grep -q 'committed.*seq=1.*ops=1' <<<"$insert"

present=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$store" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$present"
grep -q 'delta=base-plus-delta' <<<"$present"
grep -q 'rows=1' <<<"$present"
grep -q 'ibk3-smoke' <<<"$present"

delete=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$store" --update \
  "DELETE DATA { <http://example.org/ibk3-smoke> <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$delete"
grep -q 'committed.*seq=2.*ops=1' <<<"$delete"

absent=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$store" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$absent"
grep -q 'delta=base-plus-delta' <<<"$absent"
grep -q 'rows=0' <<<"$absent"

inspect=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$store" --inspect)
printf '%s\n' "$inspect"
grep -q 'committed-batches=2 committed-ops=2 clean-tail=true' <<<"$inspect"
echo 'blockengine-ibk3-persistent-smoke=pass'
