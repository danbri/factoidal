#!/usr/bin/env bash
# IBK5 quad generation (wire version 10): pack, activate, query, and refuse a
# tampered manifest. The sibling script tools/blockengine-ibk4-quad-smoke.sh
# does the same for wire version 9, which the packer still writes.
#
# Two fixtures:
#   quad_sample     — the six-quad fixture of the version-9 script, used here
#                     for the block set, the tamper test and the zone maps;
#   rdf12_sample    — the wire-version-10 fixture: a triple term, a
#                     directional literal, a 70,000-byte literal and a
#                     68,226-byte geometry, the last two out of line.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
bin="$lean_dir/.lake/build/bin"
run_dir=$(mktemp -d /private/tmp/factoidal-ibk5-quad.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT

trig="$repo_root/tests/local/data/quad_sample.trig"
nq="$repo_root/tests/local/data/quad_sample.nq"

"$bin/l4block-shard-pack" "$trig" "$run_dir/trig" ibk5 >"$run_dir/pack-trig.txt"
"$bin/l4block-shard-pack" "$nq" "$run_dir/nq" ibk5 >"$run_dir/pack-nq.txt"
cat "$run_dir/pack-trig.txt"
grep -q 'format=quad-ibk5-ptd2-lgi2-gbi1-merkle-v0 syntax=trig' "$run_dir/pack-trig.txt"
grep -q 'quads=6 blocks=4 graphs=3' "$run_dir/pack-trig.txt"
grep -q 'wire-version=10' "$run_dir/pack-trig.txt"
grep -q 'syntax=nquads' "$run_dir/pack-nq.txt"
grep -q 'quads=6 blocks=4 graphs=3' "$run_dir/pack-nq.txt"

# Since 2026-09-05 the packer buckets by the pair (predicate, graph) and
# publishes in first-seen KEY order. This fixture's graphs are not interleaved,
# so its block SET is the one this script has always asserted; only the ORDER
# of the four blocks can move, and no assertion below names an ordinal.
# The block files carry the version in their name, and each has an LGI2 and a
# GBI1 sidecar.
for b in 0 1 2 3; do
  test -f "$run_dir/trig/predicate-$b.ibk5"
  test -f "$run_dir/trig/predicate-$b.ibk5.lgi2"
  test -f "$run_dir/trig/predicate-$b.ibk5.gbi1"
  cmp "$run_dir/trig/predicate-$b.ibk5" "$run_dir/nq/predicate-$b.ibk5"
done

# The SBM10 TSV columns: the two zone-map prefixes and the blob count.
cat "$run_dir/trig/manifest.tsv"
head -1 "$run_dir/trig/manifest.tsv" | grep -q 'subject-zone	object-zone	blobs'
awk -F'\t' '$1 ~ /^[0-9]+$/ && ($12=="" || $13=="" || $14!="0") { bad=1 } END { exit bad?1:0 }' \
  "$run_dir/trig/manifest.tsv"

# Activation: full SHA-256, Merkle roots, an IBK5 decode of every artifact, and
# the recomputed zone maps and index sidecars.
mkdir -p "$run_dir/store"
cp -R "$run_dir/trig" "$run_dir/store/gen-1"
"$bin/l4block-shard-activate" "$run_dir/store" gen-1 | tee "$run_dir/activate.txt"
grep -q 'pointer=CURRENT' "$run_dir/activate.txt"

quad_query() { "$bin/l4block-quad-query" "$run_dir/store" --query "$1"; }

quad_query 'SELECT * WHERE { GRAPH ?g { ?s <http://example.org/name> ?o } }' \
  >"$run_dir/q-graph-var.txt"
cat "$run_dir/q-graph-var.txt"
grep -q '^l4block-quad-query shards=3 open-mode=ibk5-full-manifest(3) ' "$run_dir/q-graph-var.txt"
grep -q '^l4block-quad-query rows=4 ' "$run_dir/q-graph-var.txt"

# ---------------------------------------------------------------------------
# The zone maps. The same query with a CONSTANT subject opens fewer blocks:
# the manifest holds the smallest and the largest subject key of each block,
# and a key outside those bounds cannot be in the block. `zone-excluded` is
# how many entries the predicate and graph collectors kept and the zone maps
# then dropped.
# ---------------------------------------------------------------------------
quad_query 'SELECT * WHERE { GRAPH ?g { <http://example.org/shalini> <http://example.org/name> ?o } }' \
  >"$run_dir/q-zone.txt"
cat "$run_dir/q-zone.txt"
grep -q '^l4block-quad-query shards=1 ' "$run_dir/q-zone.txt"
grep -q ' zone-excluded=2$' "$run_dir/q-zone.txt"
# A subject that IS in the corpus still answers, and the block it is in is the
# one that is opened.
quad_query 'SELECT * WHERE { GRAPH ?g { <http://example.org/bob> <http://example.org/name> ?o } }' \
  >"$run_dir/q-zone-hit.txt"
cat "$run_dir/q-zone-hit.txt"
grep -q '^l4block-quad-query rows=1 ' "$run_dir/q-zone-hit.txt"
# The unbound query opens every block of the predicate; the bound one does not.
grep -q '^l4block-quad-query shards=3 ' "$run_dir/q-graph-var.txt"

# A manifest graph-set summary that the block header does not have is refused.
mkdir -p "$run_dir/tampered/gen-1"
for f in "$run_dir"/trig/*; do
  case "$(basename "$f")" in
    manifest.sbm2|manifest.tsv) ;;
    *) cp "$f" "$run_dir/tampered/gen-1/" ;;
  esac
done
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
grep -q 'candidate IBK5 artifact' "$run_dir/tamper.txt"

# ---------------------------------------------------------------------------
# The wire-version-10 fixture: the four term shapes version 9 cannot store.
# ---------------------------------------------------------------------------
r12_trig="$repo_root/tests/local/data/rdf12_sample.trig"
r12_nq="$repo_root/tests/local/data/rdf12_sample.nq"
"$bin/l4block-shard-pack" "$r12_trig" "$run_dir/r12" ibk5 >"$run_dir/pack-r12.txt"
"$bin/l4block-shard-pack" "$r12_nq" "$run_dir/r12nq" ibk5 >"$run_dir/pack-r12nq.txt"
cat "$run_dir/pack-r12.txt"
grep -q 'quads=5 blocks=5 graphs=2' "$run_dir/pack-r12.txt"
grep -q 'quads=5 blocks=5 graphs=2' "$run_dir/pack-r12nq.txt"

# Two out-of-line literals, one file each, named by their own digest.
blobs=$(ls "$run_dir/r12" | grep -c '^blob-.*\.lit$')
test "$blobs" -eq 2
python3 - "$run_dir/r12" <<'PY'
import glob, hashlib, os, sys
directory = sys.argv[1]
for path in glob.glob(os.path.join(directory, 'blob-*.lit')):
    digest = hashlib.sha256(open(path, 'rb').read()).hexdigest()
    assert os.path.basename(path) == 'blob-%s.lit' % digest, path
PY

mkdir -p "$run_dir/r12store"
cp -R "$run_dir/r12" "$run_dir/r12store/gen-1"
"$bin/l4block-shard-activate" "$run_dir/r12store" gen-1 | tee "$run_dir/r12-activate.txt"
grep -q 'pointer=CURRENT' "$run_dir/r12-activate.txt"

r12_query() { "$bin/l4block-quad-query" "$run_dir/r12store" --query "$1"; }

# The RDF 1.2 triple term.
r12_query 'SELECT ?o WHERE { <http://example.org/s1> <http://example.org/says> ?o }' \
  >"$run_dir/q-tt.txt"
cat "$run_dir/q-tt.txt"
grep -q 'rows=1 ' "$run_dir/q-tt.txt"
grep -q 'tripleTerm' "$run_dir/q-tt.txt"

# The base direction, read back through SPARQL 1.2 LANGDIR.
r12_query 'SELECT ?d WHERE { <http://example.org/s2> <http://example.org/label> ?o BIND(LANGDIR(?o) AS ?d) }' \
  >"$run_dir/q-dir.txt"
cat "$run_dir/q-dir.txt"
grep -q '"rtl"' "$run_dir/q-dir.txt"

# The 70,000-byte literal: its length, through the blob file.
r12_query 'SELECT ?n WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } BIND(STRLEN(?o) AS ?n) }' \
  >"$run_dir/q-len.txt"
cat "$run_dir/q-len.txt"
grep -q '"70000"' "$run_dir/q-len.txt"

# A needle INSIDE the out-of-line literal. The scan resolves the blob, so this
# is the row an opaque-candidate index path must also answer.
r12_query 'SELECT ?s WHERE { GRAPH ?g { ?s <http://example.org/big> ?o } FILTER(CONTAINS(?o, "needle")) }' \
  >"$run_dir/q-needle.txt"
cat "$run_dir/q-needle.txt"
grep -q 'rows=1 ' "$run_dir/q-needle.txt"

# A geometry above the inline ceiling is a blob and is therefore absent from
# GBI1. It must still answer a simple-features filter.
r12_query 'SELECT ?s WHERE { GRAPH ?g { ?s <http://www.opengis.net/ont/geosparql#asWKT> ?o } FILTER(<http://www.opengis.net/def/function/geosparql/sfIntersects>(?o, "POINT(5 5)"^^<http://www.opengis.net/ont/geosparql#wktLiteral>)) }' \
  >"$run_dir/q-geo.txt"
cat "$run_dir/q-geo.txt"
grep -q 'rows=1 ' "$run_dir/q-geo.txt"

# The generation dumps back to N-Quads, blobs resolved, and the dump packs
# again: a format change can therefore be tested on the same data.
"$bin/l4block-quad-dump" "$run_dir/r12store" "$run_dir/r12-dump.nq" \
  >"$run_dir/dump.txt"
cat "$run_dir/dump.txt"
grep -q 'blocks=5 quads=5' "$run_dir/dump.txt"
grep -q '<<( ' "$run_dir/r12-dump.nq"
grep -q '@ar--rtl' "$run_dir/r12-dump.nq"
"$bin/l4block-shard-pack" "$run_dir/r12-dump.nq" "$run_dir/r12repack" ibk5 \
  >"$run_dir/repack.txt"
grep -q 'quads=5 blocks=5' "$run_dir/repack.txt"

# A blob file whose bytes changed is refused rather than answered.
cp -R "$run_dir/r12store/gen-1" "$run_dir/r12bad"
blob=$(ls "$run_dir/r12bad"/blob-*.lit | head -1)
printf 'x' | dd of="$blob" bs=1 seek=0 conv=notrunc status=none
set +e
"$bin/l4block-shard-activate" "$run_dir/r12store" gen-bad >"$run_dir/blob-tamper.txt" 2>&1
set -e
mkdir -p "$run_dir/r12badstore" && cp -R "$run_dir/r12bad" "$run_dir/r12badstore/gen-1"
set +e
"$bin/l4block-shard-activate" "$run_dir/r12badstore" gen-1 >"$run_dir/blob-tamper.txt" 2>&1
blob_rc=$?
set -e
cat "$run_dir/blob-tamper.txt"
test "$blob_rc" -eq 1

echo 'blockengine-ibk5-quad-smoke=pass'
