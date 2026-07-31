#!/usr/bin/env bash
# Known-defect regression suite — XFAIL semantics.
#
# Every case here reproduces a defect we have FOUND, PROVED and FILED but
# not yet fixed. The point is not to hide them behind a green number: it
# is to make each one a standing, executable claim that can only change
# state deliberately.
#
#   XFAIL  the defect still reproduces      — expected, suite stays green
#   XPASS  the defect did NOT reproduce     — 🔴 SUITE FAILS ON PURPOSE
#   ERROR  the probe itself broke           — 🔴 suite fails
#
# An XPASS is not good news to be silently absorbed. It means either
# somebody fixed the defect (delete the case, close the issue, and say so
# in the same commit) or the probe has drifted and stopped measuring what
# it claims to. Both need a human. A suite that quietly turned green
# would be exactly the "green means we did not do the work" failure mode
# these tests exist to prevent (anti-pattern #3).
#
# Output: human table on stdout, machine-readable JSON to
# docs/test-results/by-suite/known-defects.json.
#
# Usage:  tests/known-defects/run.sh [--json-only]

set -uo pipefail   # NOT -e: a failing probe is data, not a crash.

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/bin/linux-x86_64/factoidal}"
JSON_OUT="${ROOT}/docs/test-results/by-suite/known-defects.json"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/factoidal-known-defects-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

JSON_ONLY=0
[ "${1:-}" = "--json-only" ] && JSON_ONLY=1

XFAIL=0; XPASS=0; ERRORS=0
ROWS=()

# record ID ISSUE TITLE STATE DETAIL
record () {
  local id="$1" issue="$2" title="$3" state="$4" detail="$5"
  case "$state" in
    XFAIL) XFAIL=$((XFAIL+1)) ;;
    XPASS) XPASS=$((XPASS+1)) ;;
    *)     ERRORS=$((ERRORS+1)) ;;
  esac
  ROWS+=("$(printf '{"id":"%s","issue":"%s","title":"%s","state":"%s","detail":"%s"}' \
            "$id" "$issue" "$title" "$state" "${detail//\"/\\\"}")")
  [ "$JSON_ONLY" = "1" ] && return 0
  local mark="  "
  [ "$state" = "XPASS" ] && mark="🔴"
  [ "$state" = "ERROR" ] && mark="🔴"
  printf '%s %-6s  %-7s  %-52s  %s\n' "$mark" "$state" "#$issue" "$title" "$detail"
}

if [ ! -x "$BIN" ]; then
  echo "known-defects: no binary at $BIN" >&2
  exit 2
fi

[ "$JSON_ONLY" = "1" ] || {
  printf '\n=== Known defects — XFAIL suite ===\n'
  printf '   XFAIL = defect still present (expected).  XPASS = defect gone, UPDATE THIS TEST.\n\n'
}

# ---------------------------------------------------------------------
# SR-1 (#336) — SELECT DISTINCT returns duplicate rows.
# distinct_solutions compares solution mappings position-by-position via
# sm_equal; SPARQL 1.1 s18.3 makes a solution mapping a partial function,
# in which binding ORDER carries no meaning. Two UNION arms that build
# the list in different orders therefore survive DISTINCT.
# ---------------------------------------------------------------------
# Both arms must be able to yield the SAME {?x,?y} pair, or nothing can
# duplicate and the probe measures nothing. :s :p :o fires arm 1 with
# x=:s,y=:o; :o :q :s fires arm 2 with the same pair, built in the other
# order. (A first draft of this probe omitted the :q triple and reported
# a false XPASS -- the suite caught its own bug, which is the point.)
cat > "${WORKDIR}/sr1.ttl" <<'EOF'
@prefix : <http://ex.org/> .
:s :p :o .
:o :q :s .
EOF
cat > "${WORKDIR}/sr1.rq" <<'EOF'
PREFIX : <http://ex.org/>
SELECT DISTINCT * WHERE { { ?x :p ?y } UNION { ?y :q ?x } }
EOF
SR1_N=$("$BIN" query --data "${WORKDIR}/sr1.ttl" --query "${WORKDIR}/sr1.rq" 2>/dev/null \
        | grep -c 'http://ex.org/o')
if [ "${SR1_N:-0}" -gt 1 ]; then
  record SR-1 336 "SELECT DISTINCT returns duplicate rows" XFAIL \
    "same row returned ${SR1_N} times under DISTINCT"
elif [ "${SR1_N:-0}" = "1" ]; then
  record SR-1 336 "SELECT DISTINCT returns duplicate rows" XPASS \
    "DISTINCT now returns 1 row — defect appears FIXED"
else
  record SR-1 336 "SELECT DISTINCT returns duplicate rows" ERROR \
    "probe produced no rows at all; query or binary changed"
fi

# ---------------------------------------------------------------------
# SR-2 (#337) — the hash-join key is FINER than the compatibility test it
# narrows, so left_join's candidate set is not a superset of the matching
# pairs. Decisive form: the SAME two patterns joined as a BGP match, and
# as an OPTIONAL do not. The engine contradicts itself on one graph.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/sr2.ttl" <<'EOF'
@prefix : <http://ex.org/> .
:a :p "x"@en .
:b :q "x"@EN .
EOF
cat > "${WORKDIR}/sr2-bgp.rq" <<'EOF'
PREFIX : <http://ex.org/>
SELECT * WHERE { ?s :p ?v . ?t :q ?v }
EOF
cat > "${WORKDIR}/sr2-opt.rq" <<'EOF'
PREFIX : <http://ex.org/>
SELECT * WHERE { ?s :p ?v OPTIONAL { ?t :q ?v } }
EOF
SR2_BGP=$("$BIN" query --data "${WORKDIR}/sr2.ttl" --query "${WORKDIR}/sr2-bgp.rq" 2>/dev/null | grep -c 'ex.org/b')
SR2_OPT=$("$BIN" query --data "${WORKDIR}/sr2.ttl" --query "${WORKDIR}/sr2-opt.rq" 2>/dev/null | grep -c 'ex.org/b')
if [ "${SR2_BGP:-0}" -ge 1 ] && [ "${SR2_OPT:-0}" = "0" ]; then
  record SR-2 337 "OPTIONAL misses a match the BGP finds (lang-tag case)" XFAIL \
    "BGP binds ?t, OPTIONAL leaves it unbound — engine self-contradiction"
elif [ "${SR2_BGP:-0}" -ge 1 ] && [ "${SR2_OPT:-0}" -ge 1 ]; then
  record SR-2 337 "OPTIONAL misses a match the BGP finds (lang-tag case)" XPASS \
    "BGP and OPTIONAL now agree — defect appears FIXED"
else
  record SR-2 337 "OPTIONAL misses a match the BGP finds (lang-tag case)" ERROR \
    "BGP itself did not match (bgp=${SR2_BGP} opt=${SR2_OPT}); probe invalid"
fi

# ---------------------------------------------------------------------
# SE-1 (#324) -- rdf_term_eq case-folds language tags where the spec says
# TERM IDENTITY. The entailment surface is not reachable from the CLI (the
# `entail` verb materializes a closure, it does not check a conclusion), so
# probe the SAME root cause where it IS reachable: sameTerm. SPARQL 1.1
# s17.4.1.1 defines sameTerm as RDF term identity, and RDF 1.1 Concepts
# s3.3 makes two literals identical only if their language tags are the
# same string -- BCP47 case-insensitivity governs matching, not identity.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/se1.ttl" <<'EOF'
@prefix : <http://ex.org/> .
:a :p "x"@en .
:b :p "x"@EN .
EOF
cat > "${WORKDIR}/se1.rq" <<'EOF'
PREFIX : <http://ex.org/>
SELECT * WHERE { ?a :p ?v1 . ?b :p ?v2 FILTER(?a != ?b && sameTerm(?v1,?v2)) }
EOF
SE1_N=$("$BIN" query --data "${WORKDIR}/se1.ttl" --query "${WORKDIR}/se1.rq" 2>/dev/null \
        | grep -c '"x"@' )
if [ "${SE1_N:-0}" -gt 0 ]; then
  record SE-1 324 "sameTerm case-folds language tags (term identity)" XFAIL \
    "sameTerm(\"x\"@en,\"x\"@EN) is TRUE; identity says they differ"
else
  record SE-1 324 "sameTerm case-folds language tags (term identity)" XPASS \
    "sameTerm now distinguishes tag case -- defect appears FIXED"
fi

# ---------------------------------------------------------------------
# RS-1 (#335) -- rdfs_reflexivity_axioms harvests reflexive subClassOf
# more widely than any RDFS rule licenses. rdfs10 licenses `?c rdfs:subClassOf
# ?c` only for ?c typed rdfs:Class. Here :C is typed nothing -- it appears
# only as the SUBJECT of a subClassOf triple -- so emitting :C rdfs:subClassOf
# :C is underivable. The F* witness reflexivity_axioms_not_rdfs_sound is
# hypothesis-free; this is the same unsoundness seen from the CLI.
#
# NOTE ON RS-4: the sibling finding (the rdf12 manifests' RDFS regime runs
# none of rdfs1-13, because RDF.Entailment.Regime shadows the real driver)
# is NOT probeable here -- the CLI `entail --regime RDFS` calls the real
# RDFS.Closure driver and derives rdfs9 correctly. RS-4 lives on the
# w3c_runner's rdf12entail path and is measured by the negative-test
# vacuity checker instead. Do not add a CLI probe for it that appears to
# pass; it would measure the wrong code path.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/rs1.nt" <<'EOF'
<http://ex.org/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://ex.org/D> .
EOF
RS1_N=$("$BIN" entail --data "${WORKDIR}/rs1.nt" --regime RDFS 2>/dev/null \
        | grep -c 'ex.org/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://ex.org/C>')
RS1_RC=$?
if [ "${RS1_N:-0}" -ge 1 ]; then
  record RS-1 335 "reflexive subClassOf emitted for an untyped class" XFAIL \
    "derived :C rdfs:subClassOf :C though :C is not typed rdfs:Class"
elif [ "$RS1_RC" -ne 0 ]; then
  record RS-1 335 "reflexive subClassOf emitted for an untyped class" ERROR \
    "entail --regime RDFS did not run"
else
  record RS-1 335 "reflexive subClassOf emitted for an untyped class" XPASS \
    "no unlicensed reflexive axiom -- defect appears FIXED"
fi

# ---------------------------------------------------------------------
# #334 — Turtle silently DROPS statements using an undeclared prefix
# instead of rejecting the document. Silent data loss beats a parse error
# only if you never find out.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/undeclared.ttl" <<'EOF'
@prefix known: <http://ex.org/> .
known:s known:p known:o .
missing:s missing:p missing:o .
EOF
U_OUT=$("$BIN" dump "${WORKDIR}/undeclared.ttl" 2>&1); U_RC=$?
U_N=$(printf '%s' "$U_OUT" | grep -c '^<' || true)
if [ "$U_RC" -eq 0 ] && [ "${U_N:-0}" = "1" ]; then
  record TTL-PFX 334 "Turtle drops undeclared-prefix statements silently" XFAIL \
    "parsed 1 of 2 statements, exit 0, no diagnostic"
elif [ "$U_RC" -ne 0 ]; then
  record TTL-PFX 334 "Turtle drops undeclared-prefix statements silently" XPASS \
    "document now rejected (exit ${U_RC}) — defect appears FIXED"
else
  record TTL-PFX 334 "Turtle drops undeclared-prefix statements silently" ERROR \
    "unexpected: exit 0 with ${U_N} statements"
fi

# ---------------------------------------------------------------------
# JSONLD-MSG — one disjunctive error string covers BOTH a JSON syntax
# error and an unresolvable remote @context, so a user cannot tell a typo
# from an unimplemented feature. Recorded in tests/did-local/README.md.
# Probe: a document with an INLINE context and a syntax error must not
# mention remote contexts.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/badsyntax.jsonld" <<'EOF'
{"@context":{"name":"http://schema.org/name"},"@id":"http://ex.org/1",
 "vm":[{"a":1},{"b":2},
 "name":"Alice"}
EOF
J_OUT=$("$BIN" jsonld --in "${WORKDIR}/badsyntax.jsonld" 2>&1)
if echo "$J_OUT" | grep -q "remote context"; then
  record JSONLD-MSG 275 "syntax error and missing loader share one message" XFAIL \
    "inline-context syntax error still blamed on remote contexts"
elif [ -n "$J_OUT" ]; then
  record JSONLD-MSG 275 "syntax error and missing loader share one message" XPASS \
    "message no longer mentions remote contexts — appears FIXED"
else
  record JSONLD-MSG 275 "syntax error and missing loader share one message" ERROR \
    "malformed JSON-LD produced no error at all"
fi

# ---------------------------------------------------------------------
# NT-ESC (#339) -- RDF.Pretty.term_to_ntriples escapes NOTHING, so the
# `dump` verb emits invalid N-Triples for any literal containing a quote,
# backslash, newline, CR or tab. Decisive form: our own parser cannot read
# our own output back. dump-nq and dump-turtle are correct; this is one
# function carrying a second, weaker notion of how a literal is written.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/nt.ttl" <<'EOF'
@prefix : <http://ex.org/> .
:s :p "q\"z\nw" .
EOF
"$BIN" dump "${WORKDIR}/nt.ttl" > "${WORKDIR}/nt.out" 2>/dev/null
NT_LINES=$(grep -c . "${WORKDIR}/nt.out" 2>/dev/null || echo 0)
NT_RT=$("$BIN" count "${WORKDIR}/nt.out" 2>&1)
if [ "${NT_LINES:-0}" -gt 1 ] || echo "$NT_RT" | grep -q "zero triples"; then
  record NT-ESC 339 "dump emits unescaped literals (invalid N-Triples)" XFAIL \
    "one triple written as ${NT_LINES} lines; own parser rejects the output"
elif [ "${NT_LINES:-0}" = "1" ]; then
  record NT-ESC 339 "dump emits unescaped literals (invalid N-Triples)" XPASS \
    "one line and it round-trips -- defect appears FIXED"
else
  record NT-ESC 339 "dump emits unescaped literals (invalid N-Triples)" ERROR \
    "dump produced no output"
fi

# ---------------------------------------------------------------------
# Summary + JSON
# ---------------------------------------------------------------------
TOTAL=$((XFAIL + XPASS + ERRORS))
mkdir -p "$(dirname "$JSON_OUT")"
{
  printf '{\n  "suite": "known-defects",\n'
  printf '  "description": "Defects found, proved and filed but not yet fixed. XFAIL = still reproduces (expected). XPASS = gone, update the test.",\n'
  printf '  "xfail": %d,\n  "xpass": %d,\n  "errors": %d,\n  "total": %d,\n' \
    "$XFAIL" "$XPASS" "$ERRORS" "$TOTAL"
  printf '  "cases": [\n'
  for i in "${!ROWS[@]}"; do
    printf '    %s' "${ROWS[$i]}"
    [ "$i" -lt $((${#ROWS[@]} - 1)) ] && printf ','
    printf '\n'
  done
  printf '  ]\n}\n'
} > "$JSON_OUT"

[ "$JSON_ONLY" = "1" ] || {
  printf '\nknown-defects: %d still present (XFAIL, expected), %d unexpectedly gone (XPASS), %d probe errors (out of %d)\n' \
    "$XFAIL" "$XPASS" "$ERRORS" "$TOTAL"
  printf 'wrote %s\n' "${JSON_OUT#"$ROOT"/}"
  if [ "$XPASS" -gt 0 ]; then
    printf '\n🔴 %d defect(s) no longer reproduce. That is not automatically good news:\n' "$XPASS"
    printf '   either somebody fixed it (delete the case + close the issue in the same\n'
    printf '   commit) or the probe drifted and has stopped measuring what it claims.\n'
  fi
}

# XPASS and ERROR both fail the suite. XFAIL alone is green.
[ "$XPASS" -eq 0 ] && [ "$ERRORS" -eq 0 ]
