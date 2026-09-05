#!/usr/bin/env bash
# IBK4 quad generation: pack, activate, refuse an IBK3 query, and refuse a
# manifest whose graph-set summary does not match the block header.
#
# The fixture has the default graph and two named graphs, one triple present in
# BOTH named graphs (two quads, two rows), and one labelled blank node. The
# N-Quads twin must pack to byte-identical blocks.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
bin="$lean_dir/.lake/build/bin"
run_dir=$(mktemp -d /private/tmp/factoidal-ibk4-quad.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT

trig="$repo_root/tests/local/data/quad_sample.trig"
nq="$repo_root/tests/local/data/quad_sample.nq"

"$bin/l4block-shard-pack" "$trig" "$run_dir/trig" ibk4 >"$run_dir/pack-trig.txt"
"$bin/l4block-shard-pack" "$nq" "$run_dir/nq" ibk4 >"$run_dir/pack-nq.txt"
cat "$run_dir/pack-trig.txt"
grep -q 'format=quad-ibk4-ptd1-merkle-v0 syntax=trig' "$run_dir/pack-trig.txt"
grep -q 'quads=6 blocks=4 graphs=3' "$run_dir/pack-trig.txt"
grep -q 'wire-version=7' "$run_dir/pack-trig.txt"
grep -q 'syntax=nquads' "$run_dir/pack-nq.txt"
grep -q 'quads=6 blocks=4 graphs=3' "$run_dir/pack-nq.txt"

# The manifest table: one row per BLOCK, and a block holds one predicate in one
# graph (docs/designissues/2026-09-04-blocks-per-predicate.md). `ex:name` has
# rows in three graphs, so it publishes three blocks, and each carries the
# single-graph set a planner reads for GRAPH <iri> selection without opening
# the block.
cat "$run_dir/trig/manifest.tsv"
awk -F'\t' '$1=="0" && $2=="http://example.org/name" && $3=="predicate-0.ibk4" && $4=="1" \
  && $8=="1" && $9=="default" { found=1 } END { exit found?0:1 }' "$run_dir/trig/manifest.tsv"
awk -F'\t' '$1=="1" && $2=="http://example.org/name" && $3=="predicate-1.ibk4" && $4=="2" \
  && $8=="1" && $9=="http://example.org/g1" { found=1 } END { exit found?0:1 }' "$run_dir/trig/manifest.tsv"
awk -F'\t' '$1=="2" && $2=="http://example.org/name" && $3=="predicate-2.ibk4" && $4=="2" \
  && $8=="1" && $9=="http://example.org/g2" { found=1 } END { exit found?0:1 }' "$run_dir/trig/manifest.tsv"
awk -F'\t' '$1=="3" && $2=="http://example.org/knows" && $3=="predicate-3.ibk4" && $4=="1" \
  && $8=="1" && $9=="default" { found=1 } END { exit found?0:1 }' "$run_dir/trig/manifest.tsv"

# Same quads in the same order from either syntax, so the same block bytes.
cmp "$run_dir/trig/predicate-0.ibk4" "$run_dir/nq/predicate-0.ibk4"
cmp "$run_dir/trig/predicate-1.ibk4" "$run_dir/nq/predicate-1.ibk4"
cmp "$run_dir/trig/predicate-2.ibk4" "$run_dir/nq/predicate-2.ibk4"
cmp "$run_dir/trig/predicate-3.ibk4" "$run_dir/nq/predicate-3.ibk4"

# Activation: full SHA-256, Merkle roots, and an IBK4 decode of every artifact.
mkdir -p "$run_dir/store"
cp -R "$run_dir/trig" "$run_dir/store/gen-1"
"$bin/l4block-shard-activate" "$run_dir/store" gen-1 | tee "$run_dir/activate.txt"
grep -q 'pointer=CURRENT' "$run_dir/activate.txt"

# The IBK3 query path refuses an IBK4 generation by layout, rather than
# misreading its rows.
set +e
"$bin/l4block-id-v3-query" "$run_dir/store" --query \
  'SELECT * WHERE { ?s <http://example.org/name> ?o }' >"$run_dir/query.txt" 2>&1
query_rc=$?
set -e
cat "$run_dir/query.txt"
test "$query_rc" -eq 1
grep -q 'rejected: this generation is SBM7 with IBK4 quad blocks' "$run_dir/query.txt"

# ---------------------------------------------------------------------------
# SPARQL over the activated SBM7 generation (l4block-quad-query).
#
# Each case checks the row count AND the number of blocks the planner opened.
# Block selection is `ShardManifest.quadEntriesForQuery`: the manifest graph
# set skips a block a constant-IRI GRAPH clause cannot reach, and the constant
# predicates of the pattern skip a block the query never names.
# ---------------------------------------------------------------------------
quad_query() {
  "$bin/l4block-quad-query" "$run_dir/store" --query "$1"
}

# GRAPH <g1>: two rows, and only the `name` block carries g1, so one shard.
quad_query 'SELECT * WHERE { GRAPH <http://example.org/g1> { ?s ?p ?o } }' \
  >"$run_dir/q-graph-g1.txt"
cat "$run_dir/q-graph-g1.txt"
grep -q '^l4block-quad-query shards=1 open-mode=ibk4-full-manifest(1) ' "$run_dir/q-graph-g1.txt"
grep -q '^l4block-quad-query rows=2 ' "$run_dir/q-graph-g1.txt"

# GRAPH ?g: four rows over both named graphs, and every row carries ?g. A
# variable graph establishes no restriction, so every block is opened.
quad_query 'SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }' >"$run_dir/q-graph-var.txt"
cat "$run_dir/q-graph-var.txt"
grep -q '^l4block-quad-query shards=4 open-mode=ibk4-full-manifest(4) ' "$run_dir/q-graph-var.txt"
grep -q '^l4block-quad-query rows=4 ' "$run_dir/q-graph-var.txt"
grep -q 'http://example.org/g1' "$run_dir/q-graph-var.txt"
grep -q 'http://example.org/g2' "$run_dir/q-graph-var.txt"
grep -q '("g", ' "$run_dir/q-graph-var.txt"

# A default-graph pattern sees the two default-graph quads and neither named
# graph.
quad_query 'SELECT * WHERE { ?s ?p ?o }' >"$run_dir/q-default.txt"
cat "$run_dir/q-default.txt"
grep -q '^l4block-quad-query rows=2 ' "$run_dir/q-default.txt"
grep -q 'http://example.org/alice' "$run_dir/q-default.txt"
grep -vq 'http://example.org/shared' "$run_dir/q-default.txt" || \
  { echo 'default-graph query leaked a named-graph row'; exit 1; }

# FROM NAMED restricts the dataset to g1, so GRAPH ?g answers two rows.
quad_query 'SELECT * FROM NAMED <http://example.org/g1> WHERE { GRAPH ?g { ?s ?p ?o } }' \
  >"$run_dir/q-from-named.txt"
cat "$run_dir/q-from-named.txt"
grep -q '^l4block-quad-query rows=2 ' "$run_dir/q-from-named.txt"
grep -q 'http://example.org/g1' "$run_dir/q-from-named.txt"
grep -vq 'http://example.org/g2' "$run_dir/q-from-named.txt" || \
  { echo 'FROM NAMED query leaked a graph the dataset does not name'; exit 1; }

# `ex:knows` is in the default graph only, so exactly one block is opened.
quad_query 'SELECT * WHERE { ?s <http://example.org/knows> ?o }' \
  >"$run_dir/q-one-block.txt"
cat "$run_dir/q-one-block.txt"
grep -q '^l4block-quad-query shards=1 open-mode=ibk4-full-manifest(1) ' "$run_dir/q-one-block.txt"
grep -q '^l4block-quad-query rows=1 ' "$run_dir/q-one-block.txt"

# `GRAPH <g1> { }` reads no row but still asks whether the dataset names g1,
# so the block that carries g1 must not be skipped.
quad_query 'SELECT * WHERE { GRAPH <http://example.org/g1> { } }' \
  >"$run_dir/q-graph-empty.txt"
cat "$run_dir/q-graph-empty.txt"
grep -q '^l4block-quad-query shards=1 ' "$run_dir/q-graph-empty.txt"
grep -q '^l4block-quad-query rows=1 ' "$run_dir/q-graph-empty.txt"

# FILTER NOT EXISTS is decided by the reference semantics against
# `env.dataset`, which is the same generation the backend answers from
# (anti-pattern 34).
quad_query 'SELECT * WHERE { ?s ?p ?o FILTER NOT EXISTS { ?s <http://example.org/knows> ?x } }' \
  >"$run_dir/q-not-exists.txt"
cat "$run_dir/q-not-exists.txt"
grep -q '^l4block-quad-query shards=4 ' "$run_dir/q-not-exists.txt"
grep -q '^l4block-quad-query rows=0 ' "$run_dir/q-not-exists.txt"

# An unnamed graph is not a graph of the dataset.
quad_query 'ASK WHERE { GRAPH <http://example.org/g9> { } }' >"$run_dir/q-absent.txt"
cat "$run_dir/q-absent.txt"
grep -q '^l4block-quad-query boolean=false' "$run_dir/q-absent.txt"

# A manifest graph-set summary that the block header does not have is refused.
# The block bytes, their digests and their Merkle roots are untouched: only the
# manifest's copy of the graph name changes.
mkdir -p "$run_dir/tampered/gen-1"
cp "$run_dir"/trig/predicate-*.ibk4 "$run_dir"/trig/predicate-*.ibk4.merkle \
   "$run_dir/tampered/gen-1/"
python3 - "$run_dir/trig/manifest.sbm2" "$run_dir/tampered/gen-1/manifest.sbm2" <<'PY'
import sys
source, target = sys.argv[1], sys.argv[2]
data = bytearray(open(source, 'rb').read())
offset = data.find(b'http://example.org/g2')
assert offset > 0, 'graph-set name not found in manifest'
data[offset + len(b'http://example.org/g')] = ord('3')
open(target, 'wb').write(bytes(data))
PY
set +e
"$bin/l4block-shard-activate" "$run_dir/tampered" gen-1 >"$run_dir/tamper.txt" 2>&1
tamper_rc=$?
set -e
cat "$run_dir/tamper.txt"
test "$tamper_rc" -eq 1
grep -q 'graph set differs from the manifest entry' "$run_dir/tamper.txt"

echo 'blockengine-ibk4-quad-smoke=pass'
