#!/usr/bin/env bash
# Pack the deterministic heterogeneous fixture into an SBM6 generation and
# check, end to end: predicate skew counts, language-tagged and typed object
# lookups, the "1"/"01" xsd:integer term-identity sentinel, a shared-term
# two-pattern join, absent lookups, then update -> compaction -> activation ->
# re-query. Every expectation is asserted; a silent regression fails the
# script, not just a number in a doc.
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$repo_root/formal/lean4"
bin="$lean_dir/.lake/build/bin"
fixture="$lean_dir/Harness/TestData/heterogeneous-fixture.ttl"
mkdir -p "$repo_root/tmp"
run_dir=$(mktemp -d "$repo_root/tmp/blockengine-hetero.XXXXXX")
trap 'rm -rf "$run_dir"' EXIT

EX='http://example.org/'
XSDINT='http://www.w3.org/2001/XMLSchema#integer'

profile=$("$repo_root/tools/corpus-profile.sh" "$fixture")
grep -q 'parser-measured statements: 44' <<<"$profile"

pack=$("$bin/l4block-shard-pack" "$fixture" "$run_dir/source" ibk3)
grep -q 'triples=44' <<<"$pack"
activate=$("$bin/l4block-shard-activate" "$run_dir" source)
grep -q 'pointer=CURRENT' <<<"$activate"

q() { "$bin/l4block-id-v3-query" "$run_dir" --query "$1"; }

# Predicate skew: the dominant and the rare predicate.
notes=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?s <${EX}note> ?o }")
grep -q 'rows=1' <<<"$notes"; grep -q '"17"' <<<"$notes"
rare=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?s <${EX}rare/seenAt> ?o }")
grep -q '"1"' <<<"$rare"

# Language-tagged object lookups; en vs en-GB are distinct terms.
alicia=$(q "SELECT ?s WHERE { ?s <${EX}name> \"Alicia\"@es }")
grep -q 'rows=1' <<<"$alicia"; grep -q 'alice' <<<"$alicia"
boben=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?s <${EX}name> \"Bob\"@en }")
grep -q '"1"' <<<"$boben"
bobgb=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?s <${EX}name> \"Bob\"@en-GB }")
grep -q '"1"' <<<"$bobgb"

# Term-identity sentinel: "1" and "01" as xsd:integer are equal VALUES but
# distinct TERMS; BGP object matching is term equality, so each selects
# exactly its own subject.
one=$(q "SELECT ?s WHERE { ?s <${EX}age> \"1\"^^<${XSDINT}> }")
grep -q 'rows=1' <<<"$one"; grep -q 'alice' <<<"$one"; ! grep -q 'bob' <<<"$one"
zeroone=$(q "SELECT ?s WHERE { ?s <${EX}age> \"01\"^^<${XSDINT}> }")
grep -q 'rows=1' <<<"$zeroone"; grep -q 'bob' <<<"$zeroone"

# Shared-term two-pattern join over ex:knows: six 2-step paths exist.
paths=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?a <${EX}knows> ?b . ?b <${EX}knows> ?c }")
grep -q '"6"' <<<"$paths"

# Object-bound IRI lookup through a shared term.
hubnote=$(q "SELECT ?s WHERE { ?s <${EX}note> <${EX}hub> }")
grep -q 'rows=1' <<<"$hubnote"; grep -q 'eve' <<<"$hubnote"

# Absent lookups: unknown subject, unknown literal, unknown predicate.
if q "ASK { <${EX}absent> ?p ?o }" | grep -q 'boolean=true'; then exit 1; fi
ghost=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?s <${EX}note> \"nothing here\"@tlh }")
grep -q '"0"' <<<"$ghost"
if q "ASK { ?s <${EX}missingPredicate> ?o }" | grep -q 'boolean=true'; then exit 1; fi

# Durable update: add Grace, retract Carol's name; visible pre-compaction.
"$bin/l4block-delta-log" "$run_dir" --update \
  "INSERT DATA { <${EX}grace> <${EX}name> \"Grace\"@en . }" >/dev/null
"$bin/l4block-delta-log" "$run_dir" --update \
  "DELETE DATA { <${EX}carol> <${EX}name> \"Carol\" . }" >/dev/null
names=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?s <${EX}name> ?o }")
grep -q '"12"' <<<"$names"
q "ASK { <${EX}grace> <${EX}name> \"Grace\"@en }" | grep -q 'boolean=true'
if q "ASK { <${EX}carol> <${EX}name> \"Carol\" }" | grep -q 'boolean=true'; then exit 1; fi

# Compact, activate, and re-query the same answers through CURRENT.
compact=$("$bin/l4block-shard-compact" "$run_dir" "$run_dir/compacted")
grep -q 'base-triples=44 delta-batches=2 compacted-triples=44' <<<"$compact"
activate2=$("$bin/l4block-shard-activate" "$run_dir" compacted)
grep -q 'pointer=CURRENT' <<<"$activate2"
test "$(<"$run_dir/CURRENT")" = 'compacted'
names2=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?s <${EX}name> ?o }")
grep -q '"12"' <<<"$names2"
one2=$(q "SELECT ?s WHERE { ?s <${EX}age> \"1\"^^<${XSDINT}> }")
grep -q 'rows=1' <<<"$one2"; grep -q 'alice' <<<"$one2"
paths2=$(q "SELECT (COUNT(*) AS ?n) WHERE { ?a <${EX}knows> ?b . ?b <${EX}knows> ?c }")
grep -q '"6"' <<<"$paths2"

# Post-compaction update lands in the fresh epoch and is visible.
"$bin/l4block-delta-log" "$run_dir" --update \
  "INSERT DATA { <${EX}heidi> <${EX}name> \"Heidi\" . }" >/dev/null
q "ASK { <${EX}heidi> <${EX}name> \"Heidi\" }" | grep -q 'boolean=true'

echo 'blockengine-heterogeneous-fixture-smoke=pass'
