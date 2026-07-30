#!/usr/bin/env bash
# Issue #325 (found by the #317 differential harness): two parser
# soundness bugs on non-ASCII input, plus a third found while fixing
# them. All three are the SAME root cause — the split-brained string
# primitives trap (skills/fstar-module-style, "Extraction-semantics
# traps" #2): raw BYTES read with Parser.FastString.fs_byte_index are
# accumulated into an F* `list char` and emitted with
# FStar.String.string_of_list, whose extracted realisation is
#   string_of_list l = BatUTF8.init (length l) (fun i -> BatUChar.chr (at l i))
# i.e. it RE-ENCODES every list element as a UTF-8 codepoint. A byte
# 0xE6 therefore becomes codepoint U+00E6 and is written back as the
# two bytes 0xC3 0xA6 — UTF-8 reinterpreted as Latin-1 ("mojibake").
#
# 1. Turtle/TriG IRIREF: <https://example.org/日本語> parsed to
#    <https://example.org/æ¥æ¬èª>. The literal on the same line was
#    correct because the literal path slices with fs_byte_sub.
#    Bug in Parser.Turtle.decode_iri_escapes_acc.
# 2. RDF/XML: a property element whose local name is non-ASCII made the
#    WHOLE document parse to zero triples with exit code 0 and no
#    diagnostic. Parser.XML.is_name_char rejected UTF-8 continuation
#    bytes (0x80-0xBF), so the Name scan stopped mid-codepoint.
#    A non-empty document that yields zero triples must also REPORT.
# 3. XML CDATA (and comment / PI) bodies: same byte-into-char-list bug
#    in Parser.XML.parse_cdata_body / parse_comment_body /
#    collect_pi_body.
#
# Every check below asserts round-trip PRESERVATION, not mere
# acceptance — that is the coverage gap issue #92 identified.
set -u

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/formal/fstar/ocaml-output/factoidal}"
REPROS="${ROOT}/tools/difftest/repros"

pass_count=0
fail_count=0
check() {
  local name="$1" expected="$2" actual="$3"
  if [[ "${actual}" == "${expected}" ]]; then
    echo "PASS ${name}"
    pass_count=$((pass_count + 1))
  else
    echo "FAIL ${name}: expected [${expected}] got [${actual}]"
    fail_count=$((fail_count + 1))
  fi
}

WORKDIR="$(mktemp -d)"
trap 'rm -rf "${WORKDIR}"' EXIT

# ---------------------------------------------------------------------
# Bug 2 — Turtle / TriG IRIREF must be byte-transparent.
# ---------------------------------------------------------------------
EXPECTED_TTL='<https://example.org/日本語> <http://example.org/onto#p> "plain literal café" .'
ttl_out="$("${BIN}" canonicalize "${REPROS}/turtle_iriref_unicode_mojibake.ttl" 2>&1)"
check "turtle-iriref-utf8-repro" "${EXPECTED_TTL}" "${ttl_out}"

# Same bytes as N-Triples: this path was already correct; pin it so a
# future "fix" cannot regress it into the Turtle behaviour.
printf '<https://example.org/\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e> <http://example.org/onto#p> "plain literal caf\xc3\xa9" .\n' \
  > "${WORKDIR}/iri.nt"
check "ntriples-iriref-utf8" "${EXPECTED_TTL}" \
  "$("${BIN}" canonicalize "${WORKDIR}/iri.nt" 2>&1)"
cp "${WORKDIR}/iri.nt" "${WORKDIR}/iri.nq"
check "nquads-iriref-utf8" "${EXPECTED_TTL}" \
  "$("${BIN}" canonicalize "${WORKDIR}/iri.nq" 2>&1)"

# TriG shares the Turtle IRIREF scanner, in the graph name as well as
# in the triple terms.
printf '@prefix ex: <http://example.org/onto#> .\n<https://example.org/\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e> { <https://example.org/\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e> ex:p "caf\xc3\xa9" . }\n' \
  > "${WORKDIR}/g.trig"
check "trig-iriref-utf8-graph-and-subject" \
  '<https://example.org/日本語> <http://example.org/onto#p> "café" <https://example.org/日本語> .' \
  "$("${BIN}" canonicalize "${WORKDIR}/g.trig" 2>&1)"

# @prefix / PREFIX namespace IRIs are IRIREFs too, and the local name
# after them is a PN_LOCAL (a separate, already-correct path).
printf '@prefix ex: <http://example.org/\xe6\x97\xa5\xe6\x9c\xac/> .\nex:\xe8\xaa\x9e ex:p "x" .\n' \
  > "${WORKDIR}/pfx.ttl"
check "turtle-prefix-iri-and-pn-local-utf8" \
  '<http://example.org/日本/語> <http://example.org/日本/p> "x" .' \
  "$("${BIN}" canonicalize "${WORKDIR}/pfx.ttl" 2>&1)"

# A UCHAR escape in an IRIREF must still produce one codepoint, not the
# raw escape text and not a double encoding. This path was correct
# before the fix; the fix must not break it.
printf '<http://e.org/\\u65E5\\U0001F600> <http://e.org/p> "x" .\n' > "${WORKDIR}/esc.ttl"
check "turtle-iriref-uchar-escape" \
  '<http://e.org/日😀> <http://e.org/p> "x" .' \
  "$("${BIN}" canonicalize "${WORKDIR}/esc.ttl" 2>&1)"

# Mixed raw UTF-8 and escapes in one IRIREF exercises the run-slicing
# boundary between the byte-transparent runs and the escape decodes.
printf '<http://e.org/\xe6\x97\xa5a\\u672Cb\xe8\xaa\x9e> <http://e.org/p> "x" .\n' \
  > "${WORKDIR}/mix.ttl"
check "turtle-iriref-mixed-raw-and-escape" \
  '<http://e.org/日a本b語> <http://e.org/p> "x" .' \
  "$("${BIN}" canonicalize "${WORKDIR}/mix.ttl" 2>&1)"

# ---------------------------------------------------------------------
# Bug 1 — RDF/XML non-ASCII QName local name.
# ---------------------------------------------------------------------
EXPECTED_RDFXML='<http://example.org/s> <http://example.org/onto#日本語> "1.0E-300"^^<http://www.w3.org/2001/XMLSchema#double> .'
check "rdfxml-unicode-qname-repro" "${EXPECTED_RDFXML}" \
  "$("${BIN}" canonicalize "${REPROS}/rdfxml_unicode_qname_dropped.rdf" 2>&1)"
check "rdfxml-unicode-qname-repro-count" \
  "${REPROS}/rdfxml_unicode_qname_dropped.rdf: 1 triples" \
  "$("${BIN}" count "${REPROS}/rdfxml_unicode_qname_dropped.rdf" 2>&1)"

# Non-ASCII in the namespace PREFIX part of the QName, in an attribute
# name, and in an rdf:ID — all go through the same XML Name scanner.
cat > "${WORKDIR}/name.rdf" <<'RDFXML'
<?xml version="1.0" encoding="UTF-8"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:日本="http://example.org/onto#">
  <rdf:Description rdf:about="http://example.org/s">
    <日本:述語>値</日本:述語>
  </rdf:Description>
</rdf:RDF>
RDFXML
check "rdfxml-unicode-prefix-and-localname" \
  '<http://example.org/s> <http://example.org/onto#述語> "値" .' \
  "$("${BIN}" canonicalize "${WORKDIR}/name.rdf" 2>&1)"

# ---------------------------------------------------------------------
# Bug 3 — XML CDATA body must be byte-transparent.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/cdata.rdf" <<'RDFXML'
<?xml version="1.0" encoding="UTF-8"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:ex="http://example.org/onto#">
  <rdf:Description rdf:about="http://example.org/s">
    <ex:p><![CDATA[日本 café ☕]]></ex:p>
  </rdf:Description>
</rdf:RDF>
RDFXML
check "rdfxml-cdata-utf8" \
  '<http://example.org/s> <http://example.org/onto#p> "日本 café ☕" .' \
  "$("${BIN}" canonicalize "${WORKDIR}/cdata.rdf" 2>&1)"

# Raw UTF-8 in text content, attribute values and numeric character
# references were already correct — pin them.
cat > "${WORKDIR}/text.rdf" <<'RDFXML'
<?xml version="1.0" encoding="UTF-8"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:ex="http://example.org/onto#">
  <rdf:Description rdf:about="http://example.org/日本">
    <ex:p>日本 café</ex:p>
    <ex:q>&#x65E5;&#x672C; caf&#xE9;</ex:q>
  </rdf:Description>
</rdf:RDF>
RDFXML
check "rdfxml-text-attr-charref-utf8" \
  '<http://example.org/日本> <http://example.org/onto#p> "日本 café" .
<http://example.org/日本> <http://example.org/onto#q> "日本 café" .' \
  "$("${BIN}" canonicalize "${WORKDIR}/text.rdf" 2>&1)"

# ---------------------------------------------------------------------
# Bug 1b — a non-empty document that parses to zero triples must be
# REPORTED, not returned as success. Silent data loss is worse than a
# crash: an unreadable Japanese-vocabulary ontology produced an empty
# graph and exit code 0.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/broken.rdf" <<'RDFXML'
<?xml version="1.0" encoding="UTF-8"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:ex="http://example.org/onto#">
  <rdf:Description rdf:about="http://example.org/s">
    <ex:p>unterminated
</rdf:RDF>
RDFXML
broken_out="$("${BIN}" count "${WORKDIR}/broken.rdf" 2>&1)"
broken_rc=$?
if [[ "${broken_rc}" -ne 0 ]]; then
  echo "PASS zero-triple-nonempty-input-exit-nonzero"
  pass_count=$((pass_count + 1))
else
  echo "FAIL zero-triple-nonempty-input-exit-nonzero: rc=0 out=[${broken_out}]"
  fail_count=$((fail_count + 1))
fi
if [[ "${broken_out}" == *rror* ]] || [[ "${broken_out}" == *ARN* ]]; then
  echo "PASS zero-triple-nonempty-input-diagnosed"
  pass_count=$((pass_count + 1))
else
  echo "FAIL zero-triple-nonempty-input-diagnosed: no diagnostic in [${broken_out}]"
  fail_count=$((fail_count + 1))
fi

# A genuinely empty graph from a document that carries no triples must
# still succeed — the diagnosis must key on "input had content we could
# not turn into triples", not on "the count is zero".
cat > "${WORKDIR}/empty.rdf" <<'RDFXML'
<?xml version="1.0" encoding="UTF-8"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"/>
RDFXML
empty_out="$("${BIN}" count "${WORKDIR}/empty.rdf" 2>&1)"
empty_rc=$?
check "legitimately-empty-document-rc" "0" "${empty_rc}"
check "legitimately-empty-document-count" \
  "${WORKDIR}/empty.rdf: 0 triples" "${empty_out}"

# An empty Turtle file (comments only) is legitimately zero triples.
printf '# just a comment\n' > "${WORKDIR}/empty.ttl"
empty_ttl_out="$("${BIN}" count "${WORKDIR}/empty.ttl" 2>&1)"
empty_ttl_rc=$?
check "comment-only-turtle-rc" "0" "${empty_ttl_rc}"
check "comment-only-turtle-count" \
  "${WORKDIR}/empty.ttl: 0 triples" "${empty_ttl_out}"

echo "pass=${pass_count} fail=${fail_count}"
if [[ "${fail_count}" -ne 0 ]]; then
  exit 1
fi
