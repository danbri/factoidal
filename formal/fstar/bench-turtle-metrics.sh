#!/bin/bash
set -euo pipefail

cd "$(dirname "$0")"

OUT_ROOT="${TMPDIR:-/tmp}/factoidal-metrics"
OUT_BIN="factoidal"
RUNS="${RUNS:-3}"

python3 - <<'PY'
from pathlib import Path

root = Path("/tmp/factoidal-metrics")
root.mkdir(exist_ok=True)
n = 1000

with (root / "prefixed-1000.ttl").open("w", encoding="utf-8") as f:
    f.write("@prefix ex: <http://example.org/> .\n")
    for i in range(n):
        f.write(f"ex:s{i} ex:p ex:o{i} .\n")

with (root / "fulliri-1000.ttl").open("w", encoding="utf-8") as f:
    for i in range(n):
        f.write(f"<http://example.org/s{i}> <http://example.org/p> <http://example.org/o{i}> .\n")

words = ["東京", "München", "Київ", "القاهرة", "서울", "Αθήνα", "SãoPaulo", "北京"]
with (root / "unicode-1000.ttl").open("w", encoding="utf-8") as f:
    f.write("@prefix ex: <http://example.org/> .\n")
    for i in range(n):
        w = words[i % len(words)]
        f.write(f'ex:s{i} ex:label "{w}-{i}"@en .\n')

src = Path.cwd().parent.parent / "examples" / "data" / "third_party" / "Berlin.ttl"
if src.exists():
    lines = src.read_text(encoding="utf-8").splitlines()
    with (root / "berlin-1000.ttl").open("w", encoding="utf-8") as f:
        for line in lines[:1000]:
            f.write(line + "\n")
PY

eval "$(opam env --switch=fstar --set-switch)"

cd ocaml-output

ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c -linkpkg -w -8-14-26 -ccopt -static \
  RDF_Graph_Executable.ml \
  Parser_Combinators.ml Parser_TurtleScanner.ml \
  Parser_NTriples.ml Parser_Turtle.ml \
  Parser_NQuads.ml Parser_TriG.ml \
  Parser_XML.ml Parser_RDFXML.ml \
  Parser_SRX.ml Parser_CSVResults.ml \
  Parser_JSONResults.ml \
  SPARQL11_Algebra.ml SPARQL11_Parser.ml \
  factoidal_cli.ml \
  -o "$OUT_BIN"

for f in \
  "$OUT_ROOT/prefixed-1000.ttl" \
  "$OUT_ROOT/fulliri-1000.ttl" \
  "$OUT_ROOT/unicode-1000.ttl" \
  "$OUT_ROOT/berlin-1000.ttl"
do
  if [ -f "$f" ]; then
    printf 'FILE %s\n' "$(basename "$f")"
    times_file="$(mktemp)"
    for i in $(seq 1 "$RUNS"); do
      output_file="$(mktemp)"
      err_file="$(mktemp)"
      /usr/bin/time -f '%e %M' "./$OUT_BIN" --count "$f" >"$output_file" 2>"$err_file"
      cat "$output_file"
      read -r secs rss <"$err_file"
      printf 'RUN %s %s %s\n' "$i" "$secs" "$rss"
      printf '%s\n' "$secs" >>"$times_file"
      rm -f "$output_file" "$err_file"
    done
    python3 - "$times_file" <<'PY'
import statistics
import sys

vals = [float(x.strip()) for x in open(sys.argv[1], encoding="utf-8") if x.strip()]
if vals:
    print(f"MEDIAN {statistics.median(vals):.2f}")
    print(f"MIN {min(vals):.2f}")
    print(f"MAX {max(vals):.2f}")
PY
    rm -f "$times_file"
  fi
done
