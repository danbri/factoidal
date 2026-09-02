#!/usr/bin/env bash
# Profile one RDF file for the Shardborough corpus ladder
# (docs/20260901-corpus-ladder-catalogue.md): bytes, SHA-256,
# parser-measured statement count, predicate histogram, object-kind
# histogram, and literal datatype/language histograms.
#
# Parsing is done by the Lean engine (l4factoidal parse --out nquads);
# awk below only counts fields of engine-emitted N-Quads lines, it never
# parses RDF text itself.
set -euo pipefail

if [ $# -ne 1 ] || [ ! -f "$1" ]; then
  echo "usage: corpus-profile.sh FILE.ttl" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cli="$repo_root/formal/lean4/.lake/build/bin/l4factoidal"
file=$1

case $file in
  *.nt) fmt=ntriples ;;
  *.nq) fmt=nquads ;;
  *.trig) fmt=trig ;;
  *.rdf|*.rdfxml) fmt=rdfxml ;;
  *) fmt=turtle ;;
esac

bytes=$(wc -c <"$file" | tr -d ' ')
digest=$(shasum -a 256 "$file" | awk '{print $1}')
nquads=$("$cli" parse "$file" --format "$fmt" --out nquads)
count=$(printf '%s\n' "$nquads" | grep -c '\.$' || true)

echo "file: $file"
echo "bytes: $bytes"
echo "sha256: $digest"
echo "parser-measured statements: $count (l4factoidal parse, N-Quads lines)"
echo "predicate histogram:"
printf '%s\n' "$nquads" | awk '{print $2}' | sort | uniq -c | sort -rn | sed 's/^/  /'
echo "object kinds:"
printf '%s\n' "$nquads" | awk '{
  o=$3
  if (o ~ /^</) kind="iri"; else if (o ~ /^_:/) kind="bnode"; else kind="literal"
  print kind }' | sort | uniq -c | sort -rn | sed 's/^/  /'
echo "literal datatypes:"
printf '%s\n' "$nquads" | grep -o '\^\^<[^>]*>' | sort | uniq -c | sort -rn | sed 's/^/  /'
echo "literal language tags:"
printf '%s\n' "$nquads" | grep -o '"@[A-Za-z-]*' | sed 's/"//' | sort | uniq -c | sort -rn | sed 's/^/  /'
echo "graphs (statements per graph term; 'default' = no graph field):"
printf '%s\n' "$nquads" | awk '{
  if ($NF == "." && NF >= 5 && ($(NF-1) ~ /^<[^"<>]*>$/ || $(NF-1) ~ /^_:[A-Za-z0-9._-]+$/)) g=$(NF-1); else g="default"
  print g }' | sort | uniq -c | sort -rn | sed 's/^/  /'
