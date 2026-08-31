#!/usr/bin/env bash
# Exercise the native IBK3 persistence route without an in-memory substitute:
# streamed Turtle publication, Merkle-paged parsed SELECT, then DLOG INSERT and
# DELETE replay against the same immutable store.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d /private/tmp/factoidal-ibk3-persistent.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT
root="$run_dir/collection"
generation='first'
store="$root/$generation"
predicate='http://www.wikidata.org/prop/direct/P31'

pack=$("$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$store" ibk3)
printf '%s\n' "$pack"
grep -q 'format=predicate-ibk3-ptd1-merkle-v0' <<<"$pack"
grep -q 'triples=368 blocks=2' <<<"$pack"

activate=$("$lean_dir/.lake/build/bin/l4block-shard-activate" "$root" "$generation")
printf '%s\n' "$activate"
grep -q 'generation=first.*pointer=CURRENT' <<<"$activate"
test "$(<"$root/CURRENT")" = "$generation"

base=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x ?type WHERE { ?x <$predicate> ?type . } LIMIT 2")
printf '%s\n' "$base"
grep -q 'shards=1 open-mode=ibk3-paged-merkle(1) delta=base' <<<"$base"
grep -q 'rows=2' <<<"$base"

ask=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "ASK { ?x <$predicate> ?type . }")
printf '%s\n' "$ask"
grep -q 'open-mode=ibk3-paged-merkle-ask(1) delta=base' <<<"$ask"
grep -q 'boolean=true' <<<"$ask"

ask_empty=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  'ASK { ?x <http://example.org/no-such-predicate> ?type . }')
printf '%s\n' "$ask_empty"
grep -q 'open-mode=ibk3-paged-merkle-ask(1) delta=base' <<<"$ask_empty"
grep -q 'boolean=false' <<<"$ask_empty"

count=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT (COUNT(*) AS ?count) WHERE { ?x <$predicate> ?type . }")
printf '%s\n' "$count"
grep -q 'open-mode=ibk3-paged-merkle-count(1) delta=base' <<<"$count"
grep -q 'rows=1' <<<"$count"
grep -q '"78"' <<<"$count"

count_zero=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT (COUNT(*) AS ?count) WHERE { ?x <$predicate> ?type . } LIMIT 0")
printf '%s\n' "$count_zero"
grep -q 'open-mode=ibk3-paged-merkle-count(1) delta=base' <<<"$count_zero"
grep -q 'rows=0' <<<"$count_zero"

group_count=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  'SELECT ?p (COUNT(*) AS ?count) WHERE { ?x ?p ?type . } GROUP BY ?p ORDER BY ?p')
printf '%s\n' "$group_count"
grep -q 'open-mode=ibk3-paged-merkle-predicate-group-count(2) delta=base' <<<"$group_count"
grep -q 'rows=2' <<<"$group_count"
grep -q '"78"' <<<"$group_count"
grep -q '"290"' <<<"$group_count"

insert=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$root" --update \
  "INSERT DATA { <http://example.org/ibk3-smoke> <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$insert"
grep -q 'committed.*seq=1.*ops=1' <<<"$insert"

present=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$present"
grep -q 'delta=base-plus-delta' <<<"$present"
grep -q 'rows=1' <<<"$present"
grep -q 'ibk3-smoke' <<<"$present"

count_with_delta=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT (COUNT(*) AS ?count) WHERE { ?x <$predicate> ?type . }")
printf '%s\n' "$count_with_delta"
grep -q 'open-mode=ibk3-paged-merkle(1) delta=base-plus-delta' <<<"$count_with_delta"
grep -q 'rows=1' <<<"$count_with_delta"
grep -q '"79"' <<<"$count_with_delta"

delete=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$root" --update \
  "DELETE DATA { <http://example.org/ibk3-smoke> <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$delete"
grep -q 'committed.*seq=2.*ops=1' <<<"$delete"

absent=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$absent"
grep -q 'delta=base-plus-delta' <<<"$absent"
grep -q 'rows=0' <<<"$absent"

inspect=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$root" --inspect)
printf '%s\n' "$inspect"
grep -q 'committed-batches=2 committed-ops=2 clean-tail=true' <<<"$inspect"
echo 'blockengine-ibk3-persistent-smoke=pass'
