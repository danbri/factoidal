#!/usr/bin/env bash
# Differential check of the two N-Quads parsers on one file:
#   reference  L4Factoidal.Syntax.parseNQuads      (l4factoidal parse)
#   fast       L4Factoidal.Syntax.parseNQuadsFast  (l4wasm-cli datasetOpen,
#              the path the browser and npm entry use)
# Both results are serialised to canonical N-Quads by the engine, sorted in
# the C locale, and compared byte for byte. Exit 0 only when identical.
# Also prints wall time for each side, so the quadratic reference and the
# indexed accumulator can be compared on the same input.
set -euo pipefail

if [ $# -ne 1 ] || [ ! -f "$1" ]; then
  echo "usage: nquads-parser-differential.sh FILE.nq" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
bin="$repo_root/formal/lean4/.lake/build/bin"
file=$1
mkdir -p "$repo_root/tmp"
work=$(mktemp -d "$repo_root/tmp/nquads-differential.XXXXXX")
trap 'rm -rf "$work"' EXIT

ref_started=$(date +%s.%N)
"$bin/l4factoidal" parse "$file" --format nquads --out nquads \
  | LC_ALL=C sort | grep -v '^$' >"$work/reference.nq"
ref_elapsed=$(echo "$(date +%s.%N) - $ref_started" | bc)

python3 - "$file" "$work/seq.json" <<'EOF'
import json, sys
text = open(sys.argv[1]).read()
json.dump([["datasetOpen", [text, "nquads", ""]], ["datasetSerialize", ["h1", "nquads"]]],
          open(sys.argv[2], "w"))
EOF
fast_started=$(date +%s.%N)
"$bin/l4wasm-cli" callseq "$work/seq.json" >"$work/fast.out"
fast_elapsed=$(echo "$(date +%s.%N) - $fast_started" | bc)
python3 - "$work/fast.out" "$work/fast-raw.nq" <<'EOF'
import json, sys
raw = open(sys.argv[1]).read()
try: results = json.loads(raw)
except Exception: results = [json.loads(l) for l in raw.splitlines() if l.strip()]
if not results[0].get("ok"): sys.exit("datasetOpen failed: " + str(results[0]))
open(sys.argv[2], "w").write(results[1]["nquads"])
EOF
LC_ALL=C sort "$work/fast-raw.nq" | grep -v '^$' >"$work/fast.nq"

lines=$(wc -l <"$work/reference.nq" | tr -d ' ')
if cmp -s "$work/reference.nq" "$work/fast.nq"; then
  echo "nquads-parser-differential: identical ($lines statements); reference ${ref_elapsed}s, fast ${fast_elapsed}s (open+serialize)"
else
  echo "nquads-parser-differential: DIFFERENT" >&2
  diff "$work/reference.nq" "$work/fast.nq" | head -20 >&2
  exit 1
fi
