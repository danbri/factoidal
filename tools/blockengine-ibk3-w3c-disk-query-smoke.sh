#!/usr/bin/env bash
# Run approved W3C SPARQL basic-evaluation fixtures through the paged
# persistent path: W3C Turtle -> IBK3/PTD1 + SBM6/Merkle -> parsed W3C query.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
fixture_dir="$repo_root/third_party/testing/w3c/sparql/sparql10/basic"
expr_fixture_dir="$repo_root/third_party/testing/w3c/sparql/sparql10/expr-builtin"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-ibk3-w3c-disk-query.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

for fixture in data-6.ttl spoo-1.rq spoo-1.srx data-7.ttl bgp-no-match.rq bgp-no-match.srx; do
  test -f "$fixture_dir/$fixture"
done
for fixture in data-2.ttl list-1.rq list-1.srx list-2.rq list-2.srx list-3.rq list-3.srx list-4.rq list-4.srx; do
  test -f "$fixture_dir/$fixture"
done
for fixture in data-builtin-2.ttl q-lang-3.rq result-lang-3.srx lang-case-sensitivity.ttl lang-case-sensitivity-eq.rq lang-case-sensitivity-ne.rq lang-case-insensitive-eq.srx lang-case-insensitive-ne.srx; do
  test -f "$expr_fixture_dir/$fixture"
done

matching_root="$run_dir/spoo-1"
matching_store="$matching_root/first"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-6.ttl" "$matching_store" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$matching_root" first >/dev/null
matching=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$matching_root" --query \
  "$(<"$fixture_dir/spoo-1.rq")")

empty_root="$run_dir/bgp-no-match"
empty_store="$empty_root/first"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-7.ttl" "$empty_store" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$empty_root" first >/dev/null
empty=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$empty_root" --query \
  "$(<"$fixture_dir/bgp-no-match.rq")")

# The approved base/prefix cases deliberately include both predicate-bound
# and unbound-predicate patterns.  The latter use explicit full-manifest mode
# rather than being rejected merely because no selective physical path exists.
base_root="$run_dir/base-prefix"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-1.ttl" "$base_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$base_root" first >/dev/null
for number in 1 2 3 4 5; do
  value=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$base_root" --query \
    "$(<"$fixture_dir/base-prefix-$number.rq")")
  printf '%s\n' "$value"
  case "$number" in
    1)
      grep -q 'open-mode=ibk3-paged-merkle-full-manifest(3)' <<<"$value"
      grep -q 'rows=2 ' <<<"$value"
      ;;
    2)
      grep -q 'open-mode=ibk3-paged-merkle-full-manifest(3)' <<<"$value"
      grep -q 'rows=1 ' <<<"$value"
      grep -q 'z:x z:p' <<<"$value"
      ;;
    3)
      grep -q 'open-mode=ibk3-paged-merkle(1)' <<<"$value"
      grep -q 'd:x ns:p' <<<"$value"
      ;;
    4)
      grep -q 'open-mode=ibk3-paged-merkle(1)' <<<"$value"
      grep -q 'x:x x:p' <<<"$value"
      ;;
    5)
      grep -q 'open-mode=ibk3-paged-merkle(1)' <<<"$value"
      grep -q 'z:x z:p' <<<"$value"
      ;;
  esac
done

# SPARQL matches language tags case-insensitively.  TLI1's first encoding is
# byte-keyed, so a language-tagged object deliberately falls back to the
# ordinary constant-predicate materialization instead of falsely reporting it
# absent from OLI2.  W3C q-lang-3 asks for @EN against a stored @en value.
lang_root="$run_dir/language-tag-case"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$expr_fixture_dir/data-builtin-2.ttl" "$lang_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$lang_root" first >/dev/null
lang_case=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$lang_root" --query \
  "$(<"$expr_fixture_dir/q-lang-3.rq")")
printf '%s\n' "$lang_case"
grep -q 'open-mode=ibk3-paged-merkle(1)' <<<"$lang_case"
grep -q 'rows=1 ' <<<"$lang_case"
grep -q 'http://example/x3' <<<"$lang_case"

# The same W3C fixture distinguishes expression-level `=` from exact term
# spelling: @en and @EN form four equal pairs and no unequal pairs. This
# checks the parsed evaluator after persisted materialisation, not OLI2.
lang_compare_root="$run_dir/language-tag-compare"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$expr_fixture_dir/lang-case-sensitivity.ttl" "$lang_compare_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$lang_compare_root" first >/dev/null
lang_eq=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$lang_compare_root" --query \
  "$(<"$expr_fixture_dir/lang-case-sensitivity-eq.rq")")
lang_ne=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$lang_compare_root" --query \
  "$(<"$expr_fixture_dir/lang-case-sensitivity-ne.rq")")
printf '%s\n' "$lang_eq"
printf '%s\n' "$lang_ne"
grep -q 'open-mode=ibk3-paged-merkle(2)' <<<"$lang_eq"
grep -q 'rows=4 ' <<<"$lang_eq"
grep -q 'open-mode=ibk3-paged-merkle(2)' <<<"$lang_ne"
grep -q 'rows=0 ' <<<"$lang_ne"

# RDF collection cases introduce Turtle blank nodes and multi-predicate list
# traversal. They deliberately take the safe full-manifest path and confirm
# that the stored RDF terms retain the typed xsd:integer list values.
list_root="$run_dir/lists"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-2.ttl" "$list_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$list_root" first >/dev/null
for number in 1 2 3 4; do
  value=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$list_root" --query \
    "$(<"$fixture_dir/list-$number.rq")")
  printf '%s\n' "$value"
  grep -q 'open-mode=ibk3-paged-merkle-full-manifest(6)' <<<"$value"
  grep -q 'rows=1 ' <<<"$value"
  case "$number" in
    1) grep -q 'http://example.org/ns#list0' <<<"$value" ;;
    2) grep -q 'http://example.org/ns#list1' <<<"$value" ;;
    3) grep -q 'literal ("1", "http://www.w3.org/2001/XMLSchema#integer"' <<<"$value" ;;
    4) grep -q 'literal ("11", "http://www.w3.org/2001/XMLSchema#integer"' <<<"$value" ;;
  esac
done

# W3C term cases pin canonical RDF literal identity after Turtle -> IBK3
# publication.  Unbound predicate patterns intentionally exercise the full
# manifest path; rdf:type remains predicate-selective.
term_root="$run_dir/terms"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$fixture_dir/data-4.ttl" "$term_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$term_root" first >/dev/null
for number in 1 2 3 4 6 8 9; do
  value=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$term_root" --query \
    "$(<"$fixture_dir/term-$number.rq")")
  printf '%s\n' "$value"
  grep -q 'rows=1 ' <<<"$value"
  if [[ "$number" == 3 ]]; then
    grep -q 'open-mode=ibk3-paged-merkle(1)' <<<"$value"
    grep -q 'http://example.org/ns#C' <<<"$value"
  else
    grep -q 'open-mode=ibk3-paged-merkle-full-manifest(7)' <<<"$value"
    case "$number" in
      1) grep -q 'http://example.org/ns#p1' <<<"$value" ;;
      2) grep -q 'http://example.org/ns#p2' <<<"$value" ;;
      4) grep -q 'http://example.org/ns#n1' <<<"$value" ;;
      6) grep -q 'http://example.org/ns#n2' <<<"$value" ;;
      8) grep -q 'http://example.org/ns#n3' <<<"$value" ;;
      9) grep -q 'http://example.org/ns#n4' <<<"$value" ;;
    esac
  fi
done

printf '%s\n' "$matching"
printf '%s\n' "$empty"

# spoo-1.srx has exactly one ?s binding, http://example.org/ns#x.
grep -q 'open-mode=ibk3-paged-merkle(2)' <<<"$matching"
grep -q 'rows=1 ' <<<"$matching"
grep -q 'Term.iri "http://example.org/ns#x"' <<<"$matching"

# bgp-no-match.srx has an empty results element. Its distinct predicates also
# exercise the SRI2/TLI1 shared-subject join admission before the ordinary
# parsed evaluator confirms that no bindings survive.
grep -q 'open-mode=ibk3-sri2-tli1-subject-join(2)' <<<"$empty"
grep -q 'rows=0 ' <<<"$empty"

echo 'blockengine-ibk3-w3c-disk-query-smoke=pass'
