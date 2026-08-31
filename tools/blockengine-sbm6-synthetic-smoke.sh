#!/usr/bin/env bash
# Controlled-cardinality regression for the Lean SBM6 object and join paths.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d /private/tmp/factoidal-sbm6-synthetic.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT

"$repo_root/tools/generate_blockengine_turtle.py" \
  --output "$run_dir/data.ttl" --subjects 128 --types 8 --parents 16 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-pack" "$run_dir/data.ttl" "$run_dir/store/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$run_dir/store" first >/dev/null

join=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$run_dir/store" --query \
  'PREFIX ex: <urn:factoidal:synthetic:> SELECT ?s ?parent WHERE { ?s ex:type ex:type3 . ?s ex:parent ?parent . }')
label=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$run_dir/store" --query \
  'PREFIX ex: <urn:factoidal:synthetic:> SELECT ?s WHERE { ?s ex:label "record 3"@en . }')
printf '%s\n' "$join"
printf '%s\n' "$label"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-subject-join(2) delta=base' <<<"$join"
grep -q 'rows=16' <<<"$join"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-scan(1) delta=base' <<<"$label"
grep -q 'rows=1' <<<"$label"
grep -q 'urn:factoidal:synthetic:s3' <<<"$label"
echo 'blockengine-sbm6-synthetic-smoke=pass'
