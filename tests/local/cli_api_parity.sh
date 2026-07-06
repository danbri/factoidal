#!/usr/bin/env bash
# CLI <-> npm API parity ("owner directive": ensure the full npm FP API
# surface is usable via CLI tools, 2026-07-06). For each factoidal CLI
# subcommand this script drives the SAME input through the npm
# (`npm/factoidal`, js_of_ocaml engine) API and diffs the *essence* of
# the answer -- not necessarily byte-identical (JSON-vs-N-Quads
# formatting differs), but the same RDF content / same verdict.
#
# The parity IS the point: both surfaces call the SAME F*-extracted
# functions (bin/factoidal-cli/factoidal_cli.ml and
# bin/npm-entry/entry_jsoo.ml are two thin consumers of one verified
# library, rule #11), so a real divergence here is a bug in one of the
# two consumer wrappers, never "expected."
#
# Comparison method: canonical N-Quads (RDFC-1.0) isomorphism for
# dataset-shaped results (same technique tests/local/jsonld_regressions.sh
# and the RML/CSVW/JSON-LD W3C runners already use), exact string/bool
# match for scalar verdicts (ShEx boolean, SHACL conforms).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
NPM_DIR="${ROOT}/npm/factoidal"
TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-cli-api-parity-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

if [[ ! -x "${BIN}" ]]; then
  echo "ERROR: factoidal binary not found or not executable: ${BIN}" >&2
  echo "       (build it, or set FACTOIDAL_BIN=/path/to/factoidal)" >&2
  exit 2
fi
if ! command -v node >/dev/null 2>&1; then
  echo "ERROR: node not found on PATH (needed to drive the npm API side)" >&2
  exit 2
fi

pass_count=0
fail_count=0
case_count=0

fail() {
  fail_count=$((fail_count + 1))
  echo "FAIL: $1"
}
pass() {
  pass_count=$((pass_count + 1))
  echo "PASS: $1"
}

canon_nq() {
  # $1 = N-Quads text (stdin) -> RDFC-1.0 canonical N-Quads via the CLI's
  # own --canonicalize, so both sides of every dataset-shaped comparison
  # below go through the exact same canonicalization step.
  "${BIN}" --canonicalize -d - -f nquads
}

# ---------------------------------------------------------------------
# Fixtures (inline, same literals tests/api.test.js already exercises
# against the npm API -- iron rule #6's "real, not synthetic" bar is
# satisfied by these being the SAME strings the npm unit suite treats
# as ground truth, not new made-up examples).
# ---------------------------------------------------------------------

TTL_DATA="${WORKDIR}/data.ttl"
cat > "${TTL_DATA}" <<'EOF'
@prefix ex:   <http://example.org/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
ex:alice a foaf:Person ; foaf:name "Alice" ; foaf:age 30 ; foaf:knows ex:bob .
ex:bob   a foaf:Person ; foaf:name "Bob" .
ex:carol foaf:name "Carol"@en .
EOF

SHACL_SHAPES="${WORKDIR}/shapes.ttl"
cat > "${SHACL_SHAPES}" <<'EOF'
@prefix sh:   <http://www.w3.org/ns/shacl#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex:   <http://example.org/> .
ex:PersonShape a sh:NodeShape ;
  sh:targetClass foaf:Person ;
  sh:property [ sh:path foaf:name ; sh:minCount 1 ] .
EOF

SHEX_SCHEMA="${WORKDIR}/schema.json"
cat > "${SHEX_SCHEMA}" <<'EOF'
{
  "type": "Schema",
  "shapes": [{
    "type": "ShapeDecl", "id": "http://example.org/PersonShape",
    "shapeExpr": {
      "type": "Shape",
      "expression": {
        "type": "TripleConstraint",
        "predicate": "http://xmlns.com/foaf/0.1/name",
        "valueExpr": { "type": "NodeConstraint", "nodeKind": "literal" }
      }
    }
  }]
}
EOF

RML_MAPPING="${WORKDIR}/mapping.ttl"
cat > "${RML_MAPPING}" <<'EOF'
@prefix rml: <http://w3id.org/rml/> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex:   <http://example.org/> .
ex:TM a rml:TriplesMap ;
  rml:logicalSource [ a rml:LogicalSource ;
    rml:iterator "$.people[*]" ;
    rml:referenceFormulation rml:JSONPath ;
    rml:source [ a rml:RelativePathSource ; rml:root rml:MappingDirectory ; rml:path "x" ] ] ;
  rml:subjectMap [ rml:template "http://example.org/person/{$.id}" ] ;
  rml:predicateObjectMap [ rml:predicate foaf:name ; rml:objectMap [ rml:reference "$.name" ] ] .
EOF

RML_SOURCE="${WORKDIR}/people.json"
cat > "${RML_SOURCE}" <<'EOF'
{"people": [{"id": "1", "name": "Alice"}, {"id": "2", "name": "Bob"}]}
EOF

RIF_DATA="${WORKDIR}/rif-data.ttl"
cat > "${RIF_DATA}" <<'EOF'
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex: <http://example.org/> .
ex:alice foaf:knows ex:bob .
EOF

RIF_RULES="${WORKDIR}/rules.rif"
cat > "${RIF_RULES}" <<'EOF'
<?xml version="1.0" encoding="UTF-8"?>
<Document xmlns="http://www.w3.org/2007/rif#">
  <payload>
    <Group>
      <sentence>
        <Forall>
          <declare><Var>x</Var></declare>
          <declare><Var>y</Var></declare>
          <formula>
            <Implies>
              <if>
                <Frame>
                  <object><Var>x</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const>
                    <Var>y</Var>
                  </slot>
                </Frame>
              </if>
              <then>
                <Frame>
                  <object><Var>y</Var></object>
                  <slot ordered="yes">
                    <Const type="http://www.w3.org/2007/rif#iri">http://xmlns.com/foaf/0.1/knows</Const>
                    <Var>x</Var>
                  </slot>
                </Frame>
              </then>
            </Implies>
          </formula>
        </Forall>
      </sentence>
    </Group>
  </payload>
</Document>
EOF

ENTAIL_DATA="${WORKDIR}/entail-data.ttl"
cat > "${ENTAIL_DATA}" <<'EOF'
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix ex:   <http://example.org/> .
ex:Hotel rdfs:subClassOf ex:Place .
ex:motel6 a ex:Hotel .
EOF

JSONLD_DOC="${WORKDIR}/doc.jsonld"
cat > "${JSONLD_DOC}" <<'EOF'
{
  "@context": { "foaf": "http://xmlns.com/foaf/0.1/", "name": "foaf:name" },
  "@id": "alice",
  "name": "Alice"
}
EOF

CSVW_DIR="${ROOT}/third_party/testing/csvw/tests"
CSVW_CSV="${CSVW_DIR}/tree-ops.csv"
CSVW_META="${CSVW_DIR}/test027-user-metadata.json"

# node helper: run a one-shot expression against npm/factoidal, print
# its result (already reduced to a comparable string by the caller).
node_eval() {
  node -e "$1" 2>&1
}

# =======================================================================
# shacl / validate — SHACL Core validation
# =======================================================================
case_count=$((case_count + 1))
cli_out="$("${BIN}" shacl --data "${TTL_DATA}" --shapes "${SHACL_SHAPES}" --json)"
cli_conforms="$(node -e "console.log(JSON.parse(require('fs').readFileSync(0,'utf8')).conforms)" <<<"${cli_out}")"
npm_conforms="$(node_eval "
const { shaclValidate } = require('${NPM_DIR}');
const fs = require('fs');
shaclValidate(fs.readFileSync('${TTL_DATA}','utf8'), fs.readFileSync('${SHACL_SHAPES}','utf8'))
  .then((r) => console.log(r.conforms))
  .catch((e) => { console.error(e); process.exit(1); });
")"
if [[ "${cli_conforms}" == "${npm_conforms}" && "${cli_conforms}" == "true" ]]; then
  pass "shacl: conforms matches npm shaclValidate() (${cli_conforms})"
else
  fail "shacl: CLI conforms=${cli_conforms} vs npm conforms=${npm_conforms}"
fi

# =======================================================================
# shex — ShEx validation of one focus node
# =======================================================================
case_count=$((case_count + 1))
cli_verdict="$("${BIN}" shex --data "${TTL_DATA}" --schema "${SHEX_SCHEMA}" \
  --node "http://example.org/alice" --shape "http://example.org/PersonShape")"
npm_verdict="$(node_eval "
const { shexValidate } = require('${NPM_DIR}');
const fs = require('fs');
shexValidate(fs.readFileSync('${TTL_DATA}','utf8'), fs.readFileSync('${SHEX_SCHEMA}','utf8'),
  'http://example.org/alice', 'http://example.org/PersonShape')
  .then((v) => console.log(v))
  .catch((e) => { console.error(e); process.exit(1); });
")"
if [[ "${cli_verdict}" == "${npm_verdict}" && "${cli_verdict}" == "true" ]]; then
  pass "shex: verdict matches npm shexValidate() (${cli_verdict})"
else
  fail "shex: CLI verdict=${cli_verdict} vs npm verdict=${npm_verdict}"
fi

# =======================================================================
# rml — RML mapping evaluation (JSON source)
# =======================================================================
case_count=$((case_count + 1))
cli_nq="$("${BIN}" rml --mapping "${RML_MAPPING}" --source "${RML_SOURCE}" --kind json)"
npm_nq="$(node_eval "
const { rmlMap, serialize } = require('${NPM_DIR}');
const fs = require('fs');
rmlMap(fs.readFileSync('${RML_MAPPING}','utf8'), fs.readFileSync('${RML_SOURCE}','utf8'), 'json')
  .then((ds) => serialize(ds, { format: 'nquads' }))
  .then((nq) => process.stdout.write(nq))
  .catch((e) => { console.error(e); process.exit(1); });
")"
cli_canon="$(printf '%s' "${cli_nq}" | canon_nq)"
npm_canon="$(printf '%s' "${npm_nq}" | canon_nq)"
if [[ "${cli_canon}" == "${npm_canon}" ]]; then
  pass "rml: canonical N-Quads match npm rmlMap()"
else
  fail "rml: canonical N-Quads differ"
  diff <(echo "${cli_canon}") <(echo "${npm_canon}") || true
fi

# =======================================================================
# csvw — CSVW csv2rdf conversion (minimal mode, real W3C fixture)
# =======================================================================
if [[ -f "${CSVW_CSV}" && -f "${CSVW_META}" ]]; then
  case_count=$((case_count + 1))
  cli_nq="$("${BIN}" csvw --csv "${CSVW_CSV}" --metadata "${CSVW_META}" --minimal --base "http://example.org/")"
  npm_nq="$(node_eval "
const { csvwToRdf, serialize } = require('${NPM_DIR}');
const fs = require('fs');
csvwToRdf(fs.readFileSync('${CSVW_CSV}','utf8'), fs.readFileSync('${CSVW_META}','utf8'),
  { mode: 'minimal', base: 'http://example.org/' })
  .then((ds) => serialize(ds, { format: 'nquads' }))
  .then((nq) => process.stdout.write(nq))
  .catch((e) => { console.error(e); process.exit(1); });
")"
  cli_canon="$(printf '%s' "${cli_nq}" | canon_nq)"
  npm_canon="$(printf '%s' "${npm_nq}" | canon_nq)"
  if [[ "${cli_canon}" == "${npm_canon}" ]]; then
    pass "csvw: canonical N-Quads match npm csvwToRdf() (test027 fixture)"
  else
    fail "csvw: canonical N-Quads differ"
    diff <(echo "${cli_canon}") <(echo "${npm_canon}") || true
  fi
else
  echo "SKIP csvw: vendored fixture missing (${CSVW_CSV})"
fi

# =======================================================================
# jsonld — JSON-LD -> RDF
# =======================================================================
case_count=$((case_count + 1))
cli_nq="$("${BIN}" jsonld --in "${JSONLD_DOC}" --base "http://example.org/")"
npm_nq="$(node_eval "
const { jsonldToRdf, serialize } = require('${NPM_DIR}');
const fs = require('fs');
jsonldToRdf(fs.readFileSync('${JSONLD_DOC}','utf8'), { base: 'http://example.org/' })
  .then((ds) => serialize(ds, { format: 'nquads' }))
  .then((nq) => process.stdout.write(nq))
  .catch((e) => { console.error(e); process.exit(1); });
")"
cli_canon="$(printf '%s' "${cli_nq}" | canon_nq)"
npm_canon="$(printf '%s' "${npm_nq}" | canon_nq)"
if [[ "${cli_canon}" == "${npm_canon}" ]]; then
  pass "jsonld: canonical N-Quads match npm jsonldToRdf()"
else
  fail "jsonld: canonical N-Quads differ"
  diff <(echo "${cli_canon}") <(echo "${npm_canon}") || true
fi

# =======================================================================
# rif — RIF Core forward-chaining saturation
# =======================================================================
case_count=$((case_count + 1))
cli_nq="$("${BIN}" rif --rules "${RIF_RULES}" --data "${RIF_DATA}")"
npm_nq="$(node_eval "
const { rifEval, serialize } = require('${NPM_DIR}');
const fs = require('fs');
rifEval(fs.readFileSync('${RIF_DATA}','utf8'), fs.readFileSync('${RIF_RULES}','utf8'))
  .then((ds) => serialize(ds, { format: 'nquads' }))
  .then((nq) => process.stdout.write(nq))
  .catch((e) => { console.error(e); process.exit(1); });
")"
cli_canon="$(printf '%s' "${cli_nq}" | canon_nq)"
npm_canon="$(printf '%s' "${npm_nq}" | canon_nq)"
if [[ "${cli_canon}" == "${npm_canon}" ]]; then
  pass "rif: canonical N-Quads match npm rifEval()"
else
  fail "rif: canonical N-Quads differ"
  diff <(echo "${cli_canon}") <(echo "${npm_canon}") || true
fi

# =======================================================================
# entail — RDFS/OWL-RL closure dump (owlClosure equivalent)
# =======================================================================
case_count=$((case_count + 1))
cli_nq="$("${BIN}" entail --data "${ENTAIL_DATA}" --regime RDFS)"
npm_nq="$(node_eval "
const { owlClosure, serialize } = require('${NPM_DIR}');
const fs = require('fs');
owlClosure(fs.readFileSync('${ENTAIL_DATA}','utf8'), 'RDFS')
  .then((ds) => serialize(ds, { format: 'nquads' }))
  .then((nq) => process.stdout.write(nq))
  .catch((e) => { console.error(e); process.exit(1); });
")"
cli_canon="$(printf '%s' "${cli_nq}" | canon_nq)"
npm_canon="$(printf '%s' "${npm_nq}" | canon_nq)"
if [[ "${cli_canon}" == "${npm_canon}" ]]; then
  pass "entail: canonical N-Quads match npm owlClosure('RDFS')"
else
  fail "entail: canonical N-Quads differ"
  diff <(echo "${cli_canon}") <(echo "${npm_canon}") || true
fi

# =======================================================================
# update — in-memory SPARQL 1.1 Update apply + dump
# =======================================================================
case_count=$((case_count + 1))
cli_nq="$("${BIN}" update --data "${TTL_DATA}" \
  -e 'PREFIX ex: <http://example.org/> INSERT DATA { ex:dave ex:says "hi" }')"
npm_nq="$(node_eval "
const { update, serialize } = require('${NPM_DIR}');
const fs = require('fs');
update(fs.readFileSync('${TTL_DATA}','utf8'),
  'PREFIX ex: <http://example.org/> INSERT DATA { ex:dave ex:says \"hi\" }')
  .then((ds) => serialize(ds, { format: 'nquads' }))
  .then((nq) => process.stdout.write(nq))
  .catch((e) => { console.error(e); process.exit(1); });
")"
cli_canon="$(printf '%s' "${cli_nq}" | canon_nq)"
npm_canon="$(printf '%s' "${npm_nq}" | canon_nq)"
if [[ "${cli_canon}" == "${npm_canon}" ]]; then
  pass "update: canonical N-Quads match npm update()"
else
  fail "update: canonical N-Quads differ"
  diff <(echo "${cli_canon}") <(echo "${npm_canon}") || true
fi

# =======================================================================
echo ""
echo "cli_api_parity: ${pass_count} pass, ${fail_count} fail (out of ${case_count})"
[[ "${fail_count}" -eq 0 ]]
