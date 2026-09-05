#!/usr/bin/env bash
# Caller-registered SPARQL 1.1 section 17.6 extension functions, checked
# NATIVELY through the same dispatch entries the wasm module serves
# (`l4wasm-cli callseq`, one process, so the registry and the handles live
# across the sequence).
#
#   tests/store-host/ext-native.sh
#
# Design: docs/designissues/2026-09-04-lean-extension-functions.md
#
# WHAT THIS CAN AND CANNOT SEE
# The native build has NO host: `ffi/l4_ext.c` compiles its no-host arm, so
# `l4_ext_call` answers the empty string and every registered IRI is the
# section 17.6 error. So this script checks the registry, the threading of
# the snapshot into all four query paths, and the section 17.6 error rules,
# on an in-memory dataset handle AND on a store handle. It CANNOT check that
# a JavaScript function answers — that needs a wasm module built from this
# tree, and `tests/store-host/ext-functions.mjs` is the check for it.
#
# Scores are printed as "N pass, M fail (out of T)".
set -u

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
LEAN="$REPO/formal/lean4"
CLI="$LEAN/.lake/build/bin/l4wasm-cli"
PACK="$LEAN/.lake/build/bin/l4block-shard-pack"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

if [ ! -x "$CLI" ]; then
  echo "ext-native: $CLI is missing; run 'lake build' in formal/lean4 first" >&2
  exit 1
fi

PASS=0
FAIL=0
check () { # check NAME EXPECTED ACTUAL
  if [ "$2" = "$3" ]; then
    PASS=$((PASS + 1)); printf '  pass  %s\n' "$1"
  else
    FAIL=$((FAIL + 1)); printf '  FAIL  %s\n        expected %s\n        got      %s\n' "$1" "$2" "$3"
  fi
}

EX='http://example.org/fn/'
NOSUCH='http://example.org/nosuch/'
GEOF='http://www.opengis.net/def/function/geosparql/'
XSD='http://www.w3.org/2001/XMLSchema#'
GEO='http://www.opengis.net/ont/geosparql#'
SKOS='http://www.w3.org/2004/02/skos/core#'

# ------------------------------------------------- in-memory dataset handle
cat > "$WORK/mk1.py" <<PYEOF
import json
TTL = ('@prefix : <http://example.org/> .\n'
       ':a :label "alpha" .\n:b :label "beta" .\n:c :label "apple" .\n'
       ':a :footprint "POINT(1 1)"^^<${GEO}wktLiteral> .\n'
       ':b :footprint "POINT(9 9)"^^<${GEO}wktLiteral> .\n'
       ':c :footprint "POINT(0.5 0.5)"^^<${GEO}wktLiteral> .\n')
json.dump([
  ["extList", []],
  ["extRegister", ["${EX}startsWithA"]],
  ["extRegister", ["${XSD}integer"]],
  ["extRegister", ["${GEOF}sfWithin"]],
  ["extList", []],
  ["datasetOpen", [TTL, "turtle", "http://example.org/"]],
  ["datasetQuery", ["h1", 'PREFIX ex: <${EX}> SELECT ?s WHERE { ?s <http://example.org/label> ?l FILTER(ex:startsWithA(?l)) }']],
  ["datasetQuery", ["h1", 'PREFIX ex: <${NOSUCH}> SELECT ?s WHERE { ?s <http://example.org/label> ?l FILTER(ex:nope(?l)) }']],
  ["datasetQuery", ["h1", 'PREFIX ex: <${NOSUCH}> SELECT ?s (ex:nope(?s) AS ?v) WHERE { ?s <http://example.org/label> ?l } ORDER BY ?s']],
  ["datasetQuery", ["h1", 'PREFIX xsd: <${XSD}> SELECT (xsd:integer("42") AS ?n) WHERE { }']],
  ["datasetQuery", ["h1", 'PREFIX geof: <${GEOF}> PREFIX geo: <${GEO}> SELECT ?s WHERE { ?s <http://example.org/footprint> ?w FILTER(geof:sfWithin(?w, "POLYGON((0 0,0 2,2 2,2 0,0 0))"^^geo:wktLiteral)) } ORDER BY ?s']],
  ["datasetQuery", ["h1", 'SELECT ?s WHERE { ?s <http://example.org/label> ?l FILTER(STRSTARTS(?l, "a")) } ORDER BY ?s']],
  ["extClear", []],
  ["extList", []],
  ["datasetClose", ["h1"]],
], open("$WORK/seq1.json", "w"))
PYEOF
python3 "$WORK/mk1.py"
"$CLI" callseq "$WORK/seq1.json" > "$WORK/out1.txt" 2>&1
line () { sed -n "$1p" "$2"; }

echo 'extension functions - in-memory dataset handle (native, no host)'
check 'the registry starts empty' \
  '{"ok":true,"count":0,"iris":[]}' "$(line 1 "$WORK/out1.txt")"
check 'extList reports the three registrations, in registration order' \
  "{\"ok\":true,\"count\":3,\"iris\":[\"${EX}startsWithA\",\"${XSD}integer\",\"${GEOF}sfWithin\"]}" \
  "$(line 5 "$WORK/out1.txt")"
check 'a registered IRI with no host is the section 17.6 error: FILTER drops every row' \
  '0' "$(python3 -c "import json,sys;print(len(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 7 "$WORK/out1.txt"))"
check 'section 17.6 unregistered IRI in FILTER drops every row' \
  '0' "$(python3 -c "import json,sys;print(len(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 8 "$WORK/out1.txt"))"
check 'section 17.6 unregistered IRI in SELECT keeps every row' \
  '3' "$(python3 -c "import json,sys;print(len(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 9 "$WORK/out1.txt"))"
check 'section 17.6 unregistered IRI in SELECT leaves the variable unbound' \
  'True' "$(python3 -c "import json,sys;print(all('v' not in r for r in json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 9 "$WORK/out1.txt"))"
check 'a registration does not override the xsd: cast family' \
  '42' "$(python3 -c "import json,sys;print(json.loads(sys.stdin.readline())['srj']['results']['bindings'][0]['n']['value'])" < <(line 10 "$WORK/out1.txt"))"
check 'geof:sfWithin answers from the built-in table despite a registration on that IRI' \
  '2' "$(python3 -c "import json,sys;print(len(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 11 "$WORK/out1.txt"))"
check 'and those are the rows the reference STRSTARTS query answers' \
  "$(python3 -c "import json,sys;print(json.dumps(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 12 "$WORK/out1.txt"))" \
  "$(python3 -c "import json,sys;print(json.dumps(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 11 "$WORK/out1.txt"))"
check 'extClear returns the engine to the built-in table' \
  '{"ok":true,"count":0,"iris":[]}' "$(line 14 "$WORK/out1.txt")"

# ------------------------------------------------------------ store handle
echo 'extension functions - persisted store handle (native, no host)'
if [ ! -x "$PACK" ]; then
  echo '  skip  store handle checks - no l4block-shard-pack'
else
  cat > "$WORK/small.ttl" <<TTLEOF
@prefix skos: <${SKOS}> .
@prefix : <http://example.org/c/> .
:1 skos:prefLabel "quartz" .
:2 skos:prefLabel "topaz" .
:3 skos:prefLabel "granite" .
:4 skos:prefLabel "basalt" .
:5 skos:prefLabel "gneiss" .
TTLEOF
  "$PACK" "$WORK/small.ttl" "$WORK/gen" ibk4 > "$WORK/pack.log" 2>&1
  cat > "$WORK/mk2.py" <<PYEOF
import json, os
gen = "$WORK/gen"
arts = [{'key': n, 'bytes': open(os.path.join(gen, n), 'rb').read().hex()}
        for n in sorted(os.listdir(gen)) if n.endswith('.ibk4')]
mh = open(os.path.join(gen, 'manifest.sbm2'), 'rb').read().hex()
Q_EXT = 'PREFIX ex: <${EX}> PREFIX skos: <${SKOS}> SELECT ?c ?l WHERE { ?c skos:prefLabel ?l FILTER(ex:endsWithZed(?l)) } ORDER BY ?c'
Q_REF = 'PREFIX skos: <${SKOS}> SELECT ?c ?l WHERE { ?c skos:prefLabel ?l FILTER(STRENDS(STR(?l), "z")) } ORDER BY ?c'
Q_CNT = 'PREFIX ex: <${NOSUCH}> PREFIX skos: <${SKOS}> SELECT (COUNT(*) AS ?n) WHERE { ?c skos:prefLabel ?l FILTER(ex:nope(?l)) }'
Q_SEL = 'PREFIX ex: <${NOSUCH}> PREFIX skos: <${SKOS}> SELECT ?c (ex:nope(?c) AS ?v) WHERE { ?c skos:prefLabel ?l } ORDER BY ?c'
json.dump([
  ["storeOpen", [mh, json.dumps(arts)]],
  ["storeHandleQuery", ["s1", Q_REF]],
  ["extRegister", ["${EX}endsWithZed"]],
  ["storeHandleQuery", ["s1", Q_EXT]],
  ["storeHandleQuery", ["s1", Q_CNT]],
  ["storeHandleQuery", ["s1", Q_SEL]],
  ["extClear", []],
  ["storeHandleClose", ["s1"]],
], open("$WORK/seq2.json", "w"))
PYEOF
  python3 "$WORK/mk2.py"
  "$CLI" callseq "$WORK/seq2.json" > "$WORK/out2.txt" 2>&1
  check 'storeOpen retains the generation' \
    'True' "$(python3 -c "import json,sys;print(json.loads(sys.stdin.readline())['rows']==5)" < <(line 1 "$WORK/out2.txt"))"
  check 'the reference STRENDS query answers two rows off disk' \
    '2' "$(python3 -c "import json,sys;print(len(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 2 "$WORK/out2.txt"))"
  check 'the registration is accepted while a store handle is open' \
    "{\"ok\":true,\"count\":1,\"iris\":[\"${EX}endsWithZed\"]}" "$(line 3 "$WORK/out2.txt")"
  check 'store handle: a registered IRI with no host is the section 17.6 error' \
    '0' "$(python3 -c "import json,sys;print(len(json.loads(sys.stdin.readline())['srj']['results']['bindings']))" < <(line 4 "$WORK/out2.txt"))"
  check 'store handle: section 17.6 unregistered IRI in FILTER drops every row' \
    '0' "$(python3 -c "import json,sys;print(json.loads(sys.stdin.readline())['srj']['results']['bindings'][0]['n']['value'])" < <(line 5 "$WORK/out2.txt"))"
  check 'store handle: section 17.6 unregistered IRI in SELECT keeps every row, unbound' \
    'True' "$(python3 -c "import json,sys;b=json.loads(sys.stdin.readline())['srj']['results']['bindings'];print(len(b)==5 and all('v' not in r for r in b))" < <(line 6 "$WORK/out2.txt"))"
fi

TOTAL=$((PASS + FAIL))
echo
echo "=== ext-native: $PASS pass, $FAIL fail (out of $TOTAL)"
[ "$FAIL" -eq 0 ]
