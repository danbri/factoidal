#!/usr/bin/env bash
# Two writers race from an empty DLOG. The conditional append edge must retain
# both whole batches with distinct sequence numbers; one process may retry.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-delta-race.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'INSERT DATA { <http://example.org/a> <http://example.org/p> "one" . }' \
  >"$run_dir/one.out" &
pid_one=$!
"$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --update \
  'INSERT DATA { <http://example.org/b> <http://example.org/p> "two" . }' \
  >"$run_dir/two.out" &
pid_two=$!

wait "$pid_one"
wait "$pid_two"

one=$(<"$run_dir/one.out")
two=$(<"$run_dir/two.out")
inspect=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$run_dir" --inspect)

printf '%s\n' "$one"
printf '%s\n' "$two"
printf '%s\n' "$inspect"
grep -q 'seq=1' <<<"$one$two"
grep -q 'seq=2' <<<"$one$two"
grep -q 'committed-batches=2 committed-ops=2 clean-tail=true' <<<"$inspect"
echo 'blockengine-delta-log-race-smoke=pass'
