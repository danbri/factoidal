#!/usr/bin/env bash
# Pack and activate every positive W3C TriG 1.1 test file as an IBK5
# generation. Positive means `rdft:TestTrigPositiveSyntax` or
# `rdft:TestTrigEval`; the negative-syntax and negative-eval tests are for the
# parser, not for the storage layer, and are not run here.
#
# Wire version 10 reads its source as RDF 1.2, so the TriG 1.1 suite is the
# same input under a wider grammar: a 1.1 document is a 1.2 document.
#
# Reports pass and fail counts and the first three failures with their message.
set -uo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
bin="$lean_dir/.lake/build/bin"
# A git worktree inherits no test submodule. TRIG_SUITE lets this script run
# from a worktree against the main checkout's suite, with the worktree's own
# binaries (hazard 15, skills/workflow-gotchas-debugging).
suite="${TRIG_SUITE:-$repo_root/third_party/testing/w3c/rdf/rdf11/rdf-trig}"
run_dir=$(mktemp -d /private/tmp/factoidal-ibk5-trig.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT

python3 - "$suite/manifest.ttl" >"$run_dir/actions.txt" <<'PY'
import re, sys
text = open(sys.argv[1], encoding='utf-8').read()
# One entry per `<#name> rdf:type rdft:TestX ; ... mf:action <file> ;`
for block in text.split('\n<#'):
    if 'rdft:Test' not in block:
        continue
    kind = re.search(r'rdft:(Test\w+)', block)
    action = re.search(r'mf:action\s+<([^>]+)>', block)
    if not kind or not action:
        continue
    if kind.group(1) in ('TestTrigPositiveSyntax', 'TestTrigEval'):
        print(action.group(1))
PY

total=0
pass_count=0
fail_count=0
failures=0
while read -r action; do
  [ -n "$action" ] || continue
  total=$((total + 1))
  out="$run_dir/out/$total"
  mkdir -p "$out"
  message=""
  if ! pack_out=$("$bin/l4block-shard-pack" "$suite/$action" "$out/gen-1" ibk5 2>&1); then
    message="pack: $(printf '%s' "$pack_out" | tail -1)"
  elif ! activate_out=$("$bin/l4block-shard-activate" "$out" gen-1 2>&1); then
    message="activate: $(printf '%s' "$activate_out" | tail -1)"
  fi
  if [ -z "$message" ]; then
    pass_count=$((pass_count + 1))
  else
    fail_count=$((fail_count + 1))
    if [ "$failures" -lt 3 ]; then
      failures=$((failures + 1))
      echo "FAIL $action -- $message"
    fi
  fi
  rm -rf "$out"
done <"$run_dir/actions.txt"

echo "blockengine-ibk5-w3c-trig: $pass_count pass, $fail_count fail (out of $total)"
test "$fail_count" -eq 0
