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
grep -q 'format=predicate-ibk3-ptd1-sri1-tli1-merkle-v0.*wire-version=4' <<<"$pack"
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

# The smaller P31 side drives a two-pattern subject join. The executor must
# announce the SRI1 path; result construction remains the parsed evaluator.
join=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  'SELECT ?x ?type ?whole WHERE { ?x <http://www.wikidata.org/prop/direct/P31> ?type . ?x <http://www.wikidata.org/prop/direct/P361> ?whole . }')
printf '%s\n' "$join"
grep -q 'open-mode=ibk3-sri1-subject-join(2) delta=base' <<<"$join"
grep -q 'rows=290' <<<"$join"

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

construct=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "CONSTRUCT { ?x <http://example.org/hasType> ?type . } WHERE { ?x <$predicate> ?type . } LIMIT 2")
printf '%s\n' "$construct"
grep -q 'open-mode=ibk3-paged-merkle(1) delta=base' <<<"$construct"
grep -q 'triples=2' <<<"$construct"
grep -q 'hasType' <<<"$construct"

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

# An SBM4 subject index is a committed generation artifact.  Corrupting its
# bytes while retaining the old manifest and Merkle leaves must prevent
# activation, rather than merely disabling a future selective scan.
bad_generation='bad-subject-index'
bad_store="$root/$bad_generation"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$bad_store" ibk3 >/dev/null
printf '\377' | dd of="$bad_store/predicate-0.ibk3.sri1" bs=1 seek=16 conv=notrunc status=none
if "$lean_dir/.lake/build/bin/l4block-shard-activate" "$root" "$bad_generation" >/dev/null 2>&1; then
  echo 'activation accepted a corrupted SBM4 subject-index sidecar' >&2
  exit 1
fi
# TLI1 is equally committed and bound to its own IBK3 digest.  Its checksum
# must be checked before CURRENT can name the generation.
bad_generation='bad-term-index'
bad_store="$root/$bad_generation"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$bad_store" ibk3 >/dev/null
printf '\377' | dd of="$bad_store/predicate-0.ibk3.tli1" bs=1 seek=16 conv=notrunc status=none
if "$lean_dir/.lake/build/bin/l4block-shard-activate" "$root" "$bad_generation" >/dev/null 2>&1; then
  echo 'activation accepted a corrupted SBM4 term-index sidecar' >&2
  exit 1
fi
echo 'blockengine-ibk3-persistent-smoke=pass'
