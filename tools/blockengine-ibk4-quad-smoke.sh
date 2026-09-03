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
grep -q 'quads=6 blocks=2 graphs=3' "$run_dir/pack-trig.txt"
grep -q 'wire-version=7' "$run_dir/pack-trig.txt"
grep -q 'syntax=nquads' "$run_dir/pack-nq.txt"
grep -q 'quads=6 blocks=2 graphs=3' "$run_dir/pack-nq.txt"

# The manifest table: one row per predicate, with the graph set a planner reads
# for GRAPH <iri> selection without opening the block.
cat "$run_dir/trig/manifest.tsv"
awk -F'\t' '$1=="0" && $2=="http://example.org/name" && $3=="predicate-0.ibk4" && $4=="5" \
  && $8=="3" && $9=="default,http://example.org/g1,http://example.org/g2" { found=1 } \
  END { exit found?0:1 }' "$run_dir/trig/manifest.tsv"
awk -F'\t' '$1=="1" && $2=="http://example.org/knows" && $3=="predicate-1.ibk4" && $4=="1" \
  && $8=="1" && $9=="default" { found=1 } END { exit found?0:1 }' "$run_dir/trig/manifest.tsv"

# Same quads in the same order from either syntax, so the same block bytes.
cmp "$run_dir/trig/predicate-0.ibk4" "$run_dir/nq/predicate-0.ibk4"
cmp "$run_dir/trig/predicate-1.ibk4" "$run_dir/nq/predicate-1.ibk4"

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

# A manifest graph-set summary that the block header does not have is refused.
# The block bytes, their digests and their Merkle roots are untouched: only the
# manifest's copy of the graph name changes.
mkdir -p "$run_dir/tampered/gen-1"
cp "$run_dir/trig/predicate-0.ibk4" "$run_dir/trig/predicate-1.ibk4" \
   "$run_dir/trig/predicate-0.ibk4.merkle" "$run_dir/trig/predicate-1.ibk4.merkle" \
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
