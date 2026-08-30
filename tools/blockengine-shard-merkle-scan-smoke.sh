#!/usr/bin/env bash
# Exercise an SBM1-root-verified, cross-chunk positioned read and then feed
# verified IBK2 ranges into a predicate-local physical scan.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-shard-merkle-scan.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/docs/fstar-extracted/lifesci/sequence_variant.ttl" "$run_dir/store" >/dev/null

pread=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-pread" "$run_dir/store" \
  http://www.wikidata.org/prop/direct/P31 65000 1000)
p31=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-scan" "$run_dir/store" \
  http://www.wikidata.org/prop/direct/P31)
p1057=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-scan" "$run_dir/store" \
  http://www.wikidata.org/prop/direct/P1057)
query=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --query \
  'PREFIX wdt: <http://www.wikidata.org/prop/direct/> PREFIX wd: <http://www.wikidata.org/entity/> SELECT ?variant ?chrom WHERE { ?variant wdt:P31 wd:Q15304597 . ?variant wdt:P1057 ?chrom . } LIMIT 5')
explain=$("$lean_dir/.lake/build/bin/l4block-shard-merkle-query" "$run_dir/store" --explain \
  'PREFIX wdt: <http://www.wikidata.org/prop/direct/> PREFIX wd: <http://www.wikidata.org/entity/> SELECT ?variant ?chrom WHERE { ?variant wdt:P31 wd:Q15304597 . ?variant wdt:P1057 ?chrom . } LIMIT 5')
session=$(printf '%s\n' \
  'PREFIX wdt: <http://www.wikidata.org/prop/direct/> PREFIX wd: <http://www.wikidata.org/entity/> SELECT ?variant ?chrom WHERE { ?variant wdt:P31 wd:Q15304597 . ?variant wdt:P1057 ?chrom . } LIMIT 5' \
  'PREFIX wdt: <http://www.wikidata.org/prop/direct/> PREFIX wd: <http://www.wikidata.org/entity/> SELECT ?variant WHERE { ?variant wdt:P31 wd:Q15304597 . } LIMIT 3' |
  "$lean_dir/.lake/build/bin/l4block-shard-merkle-session" "$run_dir/store")

printf '%s\n' "$pread"
printf '%s\n' "$p31"
printf '%s\n' "$p1057"
printf '%s\n' "$query"
printf '%s\n' "$explain"
printf '%s\n' "$session"
grep -q 'verified-bytes=1000 offset=65000 chunks=0-1' <<<"$pread"
grep -q 'rows=1800 predicate=http://www.wikidata.org/prop/direct/P31' <<<"$p31"
grep -q 'rows=1357 predicate=http://www.wikidata.org/prop/direct/P1057' <<<"$p1057"
grep -q 'open-mode=predicate-selective-merkle(2)' <<<"$query"
grep -q 'rows=5' <<<"$query"
grep -q 'explain format=sexp .* executes=false' <<<"$explain"
grep -q '(node scan-0' <<<"$explain"
grep -q '(node scan-4' <<<"$explain"
grep -q '(node sparql-eval' <<<"$explain"
grep -q 'query=1 shards=2 open-mode=predicate-selective-merkle(2) cache-hit=0 cache-miss=2' <<<"$session"
grep -q '^l4block-shard-merkle-session rows=5 ' <<<"$session"
grep -q 'query=1 shards=2 open-mode=predicate-selective-merkle(2) cache-hit=0 cache-miss=2 logical-bytes=192847 requested-range-bytes=192889 fetched-chunk-bytes=192855 verified-chunks=4 range-requests=6' <<<"$session"
grep -q 'profile format=sexp query=1' <<<"$session"
grep -q '(node scan-0' <<<"$session"
grep -q '(node scan-4' <<<"$session"
grep -q ':physical-bytes 110020 :chunks 2 :range-requests 3 :cache miss' <<<"$session"
grep -q ':physical-bytes 82835 :chunks 2 :range-requests 3 :cache miss' <<<"$session"
grep -q '(node sparql-eval' <<<"$session"
grep -q 'query=2 shards=1 open-mode=predicate-selective-merkle(1) cache-hit=1 cache-miss=0 logical-bytes=0 requested-range-bytes=0 fetched-chunk-bytes=0 verified-chunks=0 range-requests=0' <<<"$session"
grep -q ':physical-bytes 0 :chunks 0 :range-requests 0 :cache hit' <<<"$session"
grep -q '^l4block-shard-merkle-session rows=3 ' <<<"$session"
grep -q 'summary queries=2 succeeded=2 failed=0' <<<"$session"
echo 'blockengine-shard-merkle-scan-smoke=pass'
