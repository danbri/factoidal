#!/usr/bin/env bash
# tests/local/cli_ex_align_regressions.sh -- regression pins for issue #365
# (EX-1 / EX-2, owner decision 2026-08-11 "Align"):
#
#   EX-1: `ebv` (SPARQL 1.1 section 17.2.2's Effective Boolean Value)
#   treated a non-empty rdf:langString literal as truthy. The table
#   covers only xsd:boolean, the numeric types, and xsd:string/simple
#   literals -- a language-tagged literal is "any other argument", a
#   Type Error.
#
#   EX-2: `E_And`/`E_Or`/`E_Not` could never signal an error because the
#   old boolean layer (`ebv`) returned a bare `bool`. Section 17.3's
#   error-tolerant, error-PRESERVING tables need a determinate operand
#   to dominate an erroring co-operand (True&&Error=Error, False||Error
#   =Error, !Error=Error) while still letting a genuinely dominant
#   operand win (False&&Error=False, True||Error=True).
#
# These are machine-checked in SPARQL11.Expression.Refinement.fst
# (`lemma_ebv_langstring_agrees`, `lemma_eval_and_true_error_agrees` +
# Or/Not variants -- retired from the pre-landing FINDING/divergence
# lemmas of the same names minus "_agrees"). This script is the
# binary-level end of the same statements, run through the CLI's real
# BIND / SELECT-expression evaluation path (SPARQL11.Store's
# `fx_bind_rows` / `eval_select_item_group`, both of which drop a
# variable's binding entirely -- no key in the row at all -- on
# `ER_Error`, exactly as SPARQL 1.1 requires: "if the ... expression
# ... raises an error, then the variable remains unbound").
#
# FILTER/HAVING are explicitly NOT expected to change here (Type Error
# drops a row exactly like `false`, before and after #365) except for
# the one case EX-1 itself moves -- a FILTER condition that is a bare
# non-empty langString literal, which used to keep the row (truthy)
# and now drops it (Type Error). Both are pinned below, labelled.
#
# Rule anchors: #14 (retired-lemma discipline), #16, #25.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="${ROOT}/formal/fstar/ocaml-output/factoidal"
if [ ! -x "${BIN}" ]; then BIN="${ROOT}/bin/linux-x86_64/factoidal"; fi
if [ ! -x "${BIN}" ]; then
  echo "cli_ex_align_regressions: no factoidal binary found" >&2
  exit 2
fi

TMPDIR="${TMPDIR:-/tmp}"
WORKDIR="$(mktemp -d "${TMPDIR}/factoidal-exalign-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

PASS=0
FAIL=0
note() {
  if [ "$1" -eq 0 ]; then echo "PASS $2"; PASS=$((PASS+1));
  else echo "FAIL $2"; shift 2; printf '%s\n' "$@"; FAIL=$((FAIL+1)); fi
}

cat > "${WORKDIR}/data.ttl" <<'EOF'
@prefix : <http://example.org/> .
:s :iri :o .
:s :lang "hello"@en .
EOF

# has_key JSON VAR -- true (rc 0) iff the SPARQL JSON results' first
# binding row has a key named VAR (i.e. the variable is BOUND in that
# row). Absence of the key is SPARQL's "remains unbound" outcome.
has_key() {
  local json="$1" var="$2"
  printf '%s' "${json}" | grep -q "\"${var}\":"
}

# ran_ok JSON -- true (rc 0) iff the CLI actually ran the query and
# emitted SPARQL JSON results (not a CLI usage/parse error). Guards
# against a false PASS from has_key/row_count silently matching "0
# results" against CLI stderr text instead of real query output --
# exactly the failure mode a bad --output/--format flag produced
# during this script's own development (query never ran, output was
# "Error: unknown format 'json'", and has_key's absence-of-key check
# on that string "passed" every unbound-variable assertion for the
# wrong reason).
ran_ok() {
  local json="$1"
  printf '%s' "${json}" | grep -q '"head"' && \
    ! printf '%s' "${json}" | grep -qi '^Error:'
}

# row_count JSON -- number of binding rows in the SPARQL JSON results.
# print_results_json (bin/factoidal-cli/factoidal_cli.ml) always emits
# exactly 3 fixed '{' characters (the outer object, "head", "results")
# plus one '{' per binding row -- counted this way, not by a "bindings":
# [...] regex, because the pretty-printed output spans multiple lines
# and a line-based grep -o '\[[^]]*\]' cannot see across them.
row_count() {
  local json="$1"
  local braces
  braces="$(printf '%s' "${json}" | grep -o '{' | wc -l)"
  echo $((braces - 3))
}

# ---- EX-2: E_And, True AND Error = Error (BIND context) ------------------
# ?i is bound to a bare IRI -- a Type-Error EBV class. Pre-#365 the
# engine's E_And arm could only ever return a definite ER_Bool, so
# `true && ?i` bound ?z to `false`. Post-#365 it signals ER_Error, and
# BIND leaves ?z unbound.
OUT="$("${BIN}" query --data "${WORKDIR}/data.ttl" --output json \
  -e 'PREFIX : <http://example.org/> SELECT ?z WHERE { :s :iri ?i . BIND( (true && ?i) AS ?z ) }' 2>&1)"
ran_ok "${OUT}"; note $? "ex2-and-true-error-bind-ran" "${OUT}"
if has_key "${OUT}" "z"; then R=1; else R=0; fi
[ "${R}" -eq 0 ]; note $? "ex2-and-true-error-bind-unbound (?z should be UNBOUND, was bound false pre-#365)" "${OUT}"

# ---- EX-2: E_Or, False OR Error = Error (BIND context) --------------------
OUT="$("${BIN}" query --data "${WORKDIR}/data.ttl" --output json \
  -e 'PREFIX : <http://example.org/> SELECT ?z WHERE { :s :iri ?i . BIND( (false || ?i) AS ?z ) }' 2>&1)"
ran_ok "${OUT}"; note $? "ex2-or-false-error-bind-ran" "${OUT}"
if has_key "${OUT}" "z"; then R=1; else R=0; fi
[ "${R}" -eq 0 ]; note $? "ex2-or-false-error-bind-unbound (?z should be UNBOUND, was bound false pre-#365)" "${OUT}"

# ---- EX-2: E_Not, Not(Error) = Error (BIND context) -----------------------
OUT="$("${BIN}" query --data "${WORKDIR}/data.ttl" --output json \
  -e 'PREFIX : <http://example.org/> SELECT ?z WHERE { :s :iri ?i . BIND( (!?i) AS ?z ) }' 2>&1)"
ran_ok "${OUT}"; note $? "ex2-not-error-bind-ran" "${OUT}"
if has_key "${OUT}" "z"; then R=1; else R=0; fi
[ "${R}" -eq 0 ]; note $? "ex2-not-error-bind-unbound (?z should be UNBOUND, was bound true pre-#365)" "${OUT}"

# ---- EX-1 + EX-2 combined: langString operand (BIND context) -------------
# ?l is bound to a non-empty rdf:langString literal. Pre-#365 the old
# EBV treated it as truthy ("hello"@en -> true), so `?l && true` bound
# ?z2 to `true`. Post-#365 EBV signals Type Error for it (EX-1), so
# `Type-Error && true` = Error (EX-2), and ?z2 is unbound.
OUT="$("${BIN}" query --data "${WORKDIR}/data.ttl" --output json \
  -e 'PREFIX : <http://example.org/> SELECT ?z2 WHERE { :s :lang ?l . BIND( (?l && true) AS ?z2 ) }' 2>&1)"
ran_ok "${OUT}"; note $? "ex1-langstring-and-bind-ran" "${OUT}"
if has_key "${OUT}" "z2"; then R=1; else R=0; fi
[ "${R}" -eq 0 ]; note $? "ex1-langstring-and-bind-unbound (?z2 should be UNBOUND, was bound true pre-#365)" "${OUT}"

# ---- Same case, SELECT-expression context (no BIND) -----------------------
OUT="$("${BIN}" query --data "${WORKDIR}/data.ttl" --output json \
  -e 'PREFIX : <http://example.org/> SELECT (?l && true AS ?z3) WHERE { :s :lang ?l }' 2>&1)"
ran_ok "${OUT}"; note $? "ex1-langstring-and-select-expr-ran" "${OUT}"
if has_key "${OUT}" "z3"; then R=1; else R=0; fi
[ "${R}" -eq 0 ]; note $? "ex1-langstring-and-select-expr-unbound (?z3 should be UNBOUND, was bound true pre-#365)" "${OUT}"

# ---- FILTER mechanism UNCHANGED: Type Error still drops the row like
# false, both before and after #365 (E_And with an IRI operand) --------
OUT="$("${BIN}" query --data "${WORKDIR}/data.ttl" --output json \
  -e 'PREFIX : <http://example.org/> SELECT ?i WHERE { :s :iri ?i . FILTER(true && ?i) }' 2>&1)"
ran_ok "${OUT}"; note $? "filter-and-iri-ran" "${OUT}"
N="$(row_count "${OUT}")"
[ "${N}" = "0" ]; note $? "filter-and-iri-still-drops-row (rows=${N:-?}, unchanged by #365)" "${OUT}"

# ---- FILTER, EX-1's one expected FILTER-visible flip: a bare langString
# literal used to keep the row (truthy-by-length); it now Type-Errors and
# drops, exactly as a definite `false` would (same FILTER contract, new
# EBV table). This IS the approved, intended behaviour post-#365. -------
OUT="$("${BIN}" query --data "${WORKDIR}/data.ttl" --output json \
  -e 'PREFIX : <http://example.org/> SELECT ?l WHERE { :s :lang ?l . FILTER(?l) }' 2>&1)"
ran_ok "${OUT}"; note $? "filter-langstring-ran" "${OUT}"
N="$(row_count "${OUT}")"
[ "${N}" = "0" ]; note $? "filter-langstring-now-drops-row (rows=${N:-?}, kept the row pre-#365 -- intended EX-1 flip)" "${OUT}"

echo
echo "cli_ex_align_regressions: ${PASS} pass, ${FAIL} fail (out of $((PASS+FAIL)))"
if [ "${FAIL}" -ne 0 ]; then exit 1; fi
