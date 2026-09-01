#!/usr/bin/env bash
# Exercise the native IBK3 persistence route without an in-memory substitute:
# streamed Turtle publication, Merkle-paged parsed SELECT, then DLOG INSERT and
# DELETE replay against the same immutable store.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
run_dir=$(mktemp -d /private/tmp/factoidal-ibk3-persistent.XXXXXX)
trap 'rm -rf "$run_dir"' EXIT
root="$run_dir/collection"
generation='first'
store="$root/$generation"
predicate='http://www.wikidata.org/prop/direct/P31'

pack=$("$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$store" ibk3)
printf '%s\n' "$pack"
grep -q 'format=predicate-ibk3-ptd1-sri2-tli1-oli2-merkle-v0.*wire-version=6' <<<"$pack"
grep -q 'triples=368 blocks=2' <<<"$pack"

# SRI2's selective pages are admitted as a complete subject index only by the
# activation pass. A bare generation directory must not be treated as an
# activated SBM6 collection.
if "$lean_dir/.lake/build/bin/l4block-id-v3-query" "$store" --query \
  "SELECT ?x WHERE { ?x <$predicate> ?type . }" >/dev/null 2>&1; then
  echo 'SBM6 query accepted an unactivated direct generation directory' >&2
  exit 1
fi

activate=$("$lean_dir/.lake/build/bin/l4block-shard-activate" "$root" "$generation")
printf '%s\n' "$activate"
grep -q 'generation=first.*pointer=CURRENT' <<<"$activate"
test "$(<"$root/CURRENT")" = "$generation"

base=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x ?type WHERE { ?x <$predicate> ?type . } LIMIT 2")
printf '%s\n' "$base"
grep -q 'shards=1 open-mode=ibk3-paged-merkle(1) delta=base' <<<"$base"
grep -q 'rows=2' <<<"$base"

# A constant object uses the separately role-labelled OLI2 sidecar, maps the
# RDF object through TLI1, and verifies every returned fixed row has that
# object local ID before normal parsed SPARQL produces bindings.
object_scan=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://www.wikidata.org/entity/Q616005> . }")
printf '%s\n' "$object_scan"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-scan(1) delta=base' <<<"$object_scan"
grep -q 'rows=78' <<<"$object_scan"

object_absent=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://example.org/not-in-binding-site> . }")
printf '%s\n' "$object_absent"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-scan(1) delta=base' <<<"$object_absent"
grep -q 'rows=0' <<<"$object_absent"

# The OLI2-selected P31 rows can also drive the existing SRI2 subject path
# for a second predicate.  The ordinary parsed evaluator receives both exact
# fragments and retains the final join/project semantics.
object_join=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x ?whole WHERE { ?x <$predicate> <http://www.wikidata.org/entity/Q616005> . ?x <http://www.wikidata.org/prop/direct/P361> ?whole . }")
printf '%s\n' "$object_join"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-subject-direct-select(2) delta=base' <<<"$object_join"
grep -q 'rows=290' <<<"$object_join"

# Three present predicate artifacts sharing one subject are narrowed from the
# smallest driver through SRI2.  The fixture includes a two-name × two-team
# subject, so this also checks that direct binding construction keeps BGP
# Cartesian-product/bag behavior (six result mappings total).
three_root="$run_dir/three-way-collection"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$lean_dir/Harness/TestData/three-way-subject.ttl" "$three_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$three_root" first >/dev/null
three_way=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$three_root" --query \
  'SELECT ?x ?name ?team WHERE { ?x <http://example.org/type> ?type . ?x <http://example.org/name> ?name . ?x <http://example.org/member> ?team . }')
printf '%s\n' "$three_way"
grep -q 'open-mode=ibk3-sri2-tli1-subject-triple-direct-select(3) delta=base' <<<"$three_way"
grep -q 'rows=6' <<<"$three_way"
grep -q 'http://example.org/dana' <<<"$three_way"
# A semantically redundant FILTER forces the general persisted evaluator.
# It must retain the same six mappings, including Dana's four-value product;
# this is a compact differential guard for the specialised direct path.
three_way_generic=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$three_root" --query \
  'SELECT ?x ?name ?team WHERE { ?x <http://example.org/type> ?type . ?x <http://example.org/name> ?name . ?x <http://example.org/member> ?team . FILTER(?x = ?x) }')
printf '%s\n' "$three_way_generic"
grep -q 'open-mode=ibk3-paged-merkle(3) delta=base' <<<"$three_way_generic"
grep -q 'rows=6' <<<"$three_way_generic"
grep -q 'http://example.org/team4' <<<"$three_way_generic"
# The direct path must refuse sequence-observing modifiers until a separate
# refinement proves them.  This ordered query remains correct on the ordinary
# BGP evaluator rather than inheriting the physical driver's incidental order.
three_way_ordered=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$three_root" --query \
  'SELECT ?x ?name ?team WHERE { ?x <http://example.org/type> ?type . ?x <http://example.org/name> ?name . ?x <http://example.org/member> ?team . } ORDER BY ?x')
printf '%s\n' "$three_way_ordered"
grep -q 'open-mode=ibk3-sri2-tli1-subject-triple-join(3) delta=base' <<<"$three_way_ordered"
grep -q 'rows=6' <<<"$three_way_ordered"

# A very narrow physical finishing optimisation may deduplicate before the
# standard post-WHERE pipeline only when the selected subject is also the sole
# ORDER BY key.  Exercise both direction forms: they must retain the ordered
# three-row result while advertising the narrower path.
object_join_distinct_asc=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT DISTINCT ?x WHERE { ?x <$predicate> <http://www.wikidata.org/entity/Q616005> . ?x <http://www.wikidata.org/prop/direct/P361> ?whole . } ORDER BY ?x LIMIT 3")
printf '%s\n' "$object_join_distinct_asc"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-subject-direct-select-distinct-subject(2) delta=base' <<<"$object_join_distinct_asc"
grep -q 'rows=3' <<<"$object_join_distinct_asc"

object_join_distinct_desc=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT DISTINCT ?x WHERE { ?x <$predicate> <http://www.wikidata.org/entity/Q616005> . ?x <http://www.wikidata.org/prop/direct/P361> ?whole . } ORDER BY DESC(?x) LIMIT 3")
printf '%s\n' "$object_join_distinct_desc"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-subject-direct-select-distinct-subject(2) delta=base' <<<"$object_join_distinct_desc"
grep -q 'rows=3' <<<"$object_join_distinct_desc"

# The smaller P31 side drives a two-pattern subject join. The executor must
# announce the SRI2 path; result construction remains the parsed evaluator.
join=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  'SELECT ?x ?type ?whole WHERE { ?x <http://www.wikidata.org/prop/direct/P31> ?type . ?x <http://www.wikidata.org/prop/direct/P361> ?whole . }')
printf '%s\n' "$join"
grep -q 'open-mode=ibk3-sri2-tli1-subject-join(2) delta=base' <<<"$join"
grep -q 'rows=290' <<<"$join"

ask=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "ASK { ?x <$predicate> ?type . }")
printf '%s\n' "$ask"
grep -q 'open-mode=ibk3-paged-merkle-ask(1) delta=base' <<<"$ask"
grep -q 'boolean=true' <<<"$ask"

ask_empty=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  'ASK { ?x <http://example.org/no-such-predicate> ?type . }')
printf '%s\n' "$ask_empty"
grep -q 'open-mode=ibk3-paged-merkle-ask(1) delta=base' <<<"$ask_empty"
grep -q 'boolean=false' <<<"$ask_empty"

construct=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "CONSTRUCT { ?x <http://example.org/hasType> ?type . } WHERE { ?x <$predicate> ?type . } LIMIT 2")
printf '%s\n' "$construct"
grep -q 'open-mode=ibk3-paged-merkle(1) delta=base' <<<"$construct"
grep -q 'triples=2' <<<"$construct"
grep -q 'hasType' <<<"$construct"

count=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT (COUNT(*) AS ?count) WHERE { ?x <$predicate> ?type . }")
printf '%s\n' "$count"
grep -q 'open-mode=ibk3-paged-merkle-count(1) delta=base' <<<"$count"
grep -q 'rows=1' <<<"$count"
grep -q '"78"' <<<"$count"

count_zero=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT (COUNT(*) AS ?count) WHERE { ?x <$predicate> ?type . } LIMIT 0")
printf '%s\n' "$count_zero"
grep -q 'open-mode=ibk3-paged-merkle-count(1) delta=base' <<<"$count_zero"
grep -q 'rows=0' <<<"$count_zero"

group_count=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  'SELECT ?p (COUNT(*) AS ?count) WHERE { ?x ?p ?type . } GROUP BY ?p ORDER BY ?p')
printf '%s\n' "$group_count"
grep -q 'open-mode=ibk3-paged-merkle-predicate-group-count(2) delta=base' <<<"$group_count"
grep -q 'rows=2' <<<"$group_count"
grep -q '"78"' <<<"$group_count"
grep -q '"290"' <<<"$group_count"

insert=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$root" --update \
  "INSERT DATA { <http://example.org/ibk3-smoke> <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$insert"
grep -q 'committed.*seq=1.*ops=1' <<<"$insert"

present=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$present"
grep -q 'delta=base-plus-delta' <<<"$present"
grep -q 'rows=1' <<<"$present"
grep -q 'ibk3-smoke' <<<"$present"

count_with_delta=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT (COUNT(*) AS ?count) WHERE { ?x <$predicate> ?type . }")
printf '%s\n' "$count_with_delta"
grep -q 'open-mode=ibk3-paged-merkle(1) delta=base-plus-delta' <<<"$count_with_delta"
grep -q 'rows=1' <<<"$count_with_delta"
grep -q '"79"' <<<"$count_with_delta"

delete=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$root" --update \
  "DELETE DATA { <http://example.org/ibk3-smoke> <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$delete"
grep -q 'committed.*seq=2.*ops=1' <<<"$delete"

absent=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$root" --query \
  "SELECT ?x WHERE { ?x <$predicate> <http://example.org/SmokeType> . }")
printf '%s\n' "$absent"
grep -q 'delta=base-plus-delta' <<<"$absent"
grep -q 'rows=0' <<<"$absent"

inspect=$("$lean_dir/.lake/build/bin/l4block-delta-log" "$root" --inspect)
printf '%s\n' "$inspect"
grep -q 'committed-batches=2 committed-ops=2 clean-tail=true' <<<"$inspect"

# An SBM6 subject index is a committed generation artifact.  Corrupting its
# bytes while retaining the old manifest and Merkle leaves must prevent
# activation, rather than merely disabling a future selective scan.
bad_generation='bad-subject-index'
bad_store="$root/$bad_generation"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$bad_store" ibk3 >/dev/null
printf '\377' | dd of="$bad_store/predicate-0.ibk3.sri2" bs=1 seek=16 conv=notrunc status=none
if "$lean_dir/.lake/build/bin/l4block-shard-activate" "$root" "$bad_generation" >/dev/null 2>&1; then
  echo 'activation accepted a corrupted SBM6 subject-index sidecar' >&2
  exit 1
fi
# TLI1 is equally committed and bound to its own IBK3 digest.  Its checksum
# must be checked before CURRENT can name the generation.
bad_generation='bad-term-index'
bad_store="$root/$bad_generation"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$bad_store" ibk3 >/dev/null
printf '\377' | dd of="$bad_store/predicate-0.ibk3.tli1" bs=1 seek=16 conv=notrunc status=none
if "$lean_dir/.lake/build/bin/l4block-shard-activate" "$root" "$bad_generation" >/dev/null 2>&1; then
  echo 'activation accepted a corrupted SBM6 term-index sidecar' >&2
  exit 1
fi
# OLI2 has a separately typed manifest role and is recomputed from `row.o`.
bad_generation='bad-object-index'
bad_store="$root/$bad_generation"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$repo_root/examples/wikidata/subsets/lifesci-kgx/data/binding_site.ttl" \
  "$bad_store" ibk3 >/dev/null
printf '\377' | dd of="$bad_store/predicate-0.ibk3.oli2" bs=1 seek=16 conv=notrunc status=none
if "$lean_dir/.lake/build/bin/l4block-shard-activate" "$root" "$bad_generation" >/dev/null 2>&1; then
  echo 'activation accepted a corrupted SBM6 object-index sidecar' >&2
  exit 1
fi

# Literal terms use the same TLI1/OLI2 path as IRI terms.  Keep this separate
# tiny fixture because the Wikidata binding-site graph intentionally contains
# only IRI objects.
literal_root="$run_dir/literal-collection"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$lean_dir/Harness/TestData/delta-overlay.ttl" "$literal_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$literal_root" first >/dev/null
literal_object=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$literal_root" --query \
  'SELECT ?person WHERE { ?person <http://example.org/name> "Alice" . }')
printf '%s\n' "$literal_object"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-scan(1) delta=base' <<<"$literal_object"
grep -q 'rows=1' <<<"$literal_object"
grep -q 'http://example.org/alice' <<<"$literal_object"

typed_root="$run_dir/typed-literal-collection"
"$lean_dir/.lake/build/bin/l4block-shard-pack" \
  "$lean_dir/Harness/TestData/object-index-literals.ttl" "$typed_root/first" ibk3 >/dev/null
"$lean_dir/.lake/build/bin/l4block-shard-activate" "$typed_root" first >/dev/null
language_object=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$typed_root" --query \
  'SELECT ?person WHERE { ?person <http://example.org/label> "Alice"@en . }')
typed_object=$("$lean_dir/.lake/build/bin/l4block-id-v3-query" "$typed_root" --query \
  'SELECT ?person WHERE { ?person <http://example.org/score> "42"^^<http://www.w3.org/2001/XMLSchema#integer> . }')
printf '%s\n' "$language_object"
printf '%s\n' "$typed_object"
# TLI1 is byte-keyed while SPARQL language tags match case-insensitively, so
# language-tagged literals retain correctness through the predicate route until
# a multi-ID canonical-equivalence index supersedes this first sidecar.
grep -q 'open-mode=ibk3-paged-merkle(1) delta=base' <<<"$language_object"
grep -q 'rows=1' <<<"$language_object"
grep -q 'http://example.org/alice' <<<"$language_object"
grep -q 'open-mode=ibk3-sri2-tli1-oli2-object-scan(1) delta=base' <<<"$typed_object"
grep -q 'rows=1' <<<"$typed_object"
grep -q 'http://example.org/bob' <<<"$typed_object"
echo 'blockengine-ibk3-persistent-smoke=pass'
