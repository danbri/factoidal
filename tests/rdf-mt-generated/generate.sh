#!/usr/bin/env bash
# tests/rdf-mt-generated/generate.sh — writes the fixture .ttl files that
# run.sh exercises through the committed factoidal binary's `entail`
# subcommand. See README.md for what each fixture pins and which
# docs/theorem-registry.md row it belongs to.
#
# Idempotent: re-running overwrites fixtures/ with the same content.
# Rule anchors: #12 (no `(*`/backslash traps — plain Turtle only, no
# escapes), #16 (no output truncation elsewhere in this suite).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FIX="${ROOT}/fixtures"
mkdir -p "${FIX}"

# ---------------------------------------------------------------------
# rdfs2 (domain): p rdfs:domain C, x p y  |=  x rdf:type C
# ---------------------------------------------------------------------

cat > "${FIX}/rdfs2_base.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs2/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:p rdfs:domain ex:C .
ex:x ex:p ex:y .
EOF

cat > "${FIX}/rdfs2_reordered.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs2/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:x ex:p ex:y .
ex:p rdfs:domain ex:C .
EOF

cat > "${FIX}/rdfs2_duplicate.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs2/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:p rdfs:domain ex:C .
ex:x ex:p ex:y .
ex:x ex:p ex:y .
EOF

# ---------------------------------------------------------------------
# rdfs3 (range): p rdfs:range C, x p y  |=  y rdf:type C
# Mixed fixture also carries the soundness-boundary case: a literal
# object can never become a subject, so the second premise must not
# derive any rdf:type-C conclusion (registry finding RS-3).
# ---------------------------------------------------------------------

cat > "${FIX}/rdfs3_base.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs3/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:p rdfs:range ex:C .
ex:x ex:p ex:y .
EOF

cat > "${FIX}/rdfs3_reordered.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs3/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:x ex:p ex:y .
ex:p rdfs:range ex:C .
EOF

cat > "${FIX}/rdfs3_literal_boundary.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs3/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:p rdfs:range ex:C .
ex:x1 ex:p ex:y1 .
ex:x2 ex:p "literal value" .
EOF

# ---------------------------------------------------------------------
# rdfs7 (subPropertyOf): p rdfs:subPropertyOf q, x p y  |=  x q y
# ---------------------------------------------------------------------

cat > "${FIX}/rdfs7_base.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs7/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:p rdfs:subPropertyOf ex:q .
ex:x ex:p ex:y .
EOF

cat > "${FIX}/rdfs7_reordered.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs7/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:x ex:p ex:y .
ex:p rdfs:subPropertyOf ex:q .
EOF

cat > "${FIX}/rdfs7_duplicate.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs7/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:p rdfs:subPropertyOf ex:q .
ex:x ex:p ex:y .
ex:x ex:p ex:y .
EOF

# ---------------------------------------------------------------------
# rdfs9 (subClassOf): C rdfs:subClassOf D, x rdf:type C  |=  x rdf:type D
# ---------------------------------------------------------------------

cat > "${FIX}/rdfs9_base.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs9/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:C rdfs:subClassOf ex:D .
ex:x a ex:C .
EOF

cat > "${FIX}/rdfs9_reordered.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs9/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:x a ex:C .
ex:C rdfs:subClassOf ex:D .
EOF

cat > "${FIX}/rdfs9_duplicate.ttl" <<'EOF'
@prefix ex: <http://example.org/rdfs9/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:C rdfs:subClassOf ex:D .
ex:x a ex:C .
ex:x a ex:C .
EOF

# ---------------------------------------------------------------------
# prp-fp (functional property): p a owl:FunctionalProperty, x p y1,
# x p y2  |=  y1 owl:sameAs y2 (both directions, via eq-sym)
# ---------------------------------------------------------------------

cat > "${FIX}/prpfp_base.ttl" <<'EOF'
@prefix ex: <http://example.org/prpfp/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
ex:hasMother a owl:FunctionalProperty .
ex:alice ex:hasMother ex:mom1 .
ex:alice ex:hasMother ex:mom2 .
EOF

cat > "${FIX}/prpfp_duplicate.ttl" <<'EOF'
@prefix ex: <http://example.org/prpfp/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
ex:hasMother a owl:FunctionalProperty .
ex:alice ex:hasMother ex:mom1 .
ex:alice ex:hasMother ex:mom1 .
ex:alice ex:hasMother ex:mom2 .
EOF

# ---------------------------------------------------------------------
# prp-ifp (inverse-functional property): p a owl:InverseFunctionalProperty,
# x1 p y, x2 p y  |=  x1 owl:sameAs x2
# ---------------------------------------------------------------------

cat > "${FIX}/prpifp_base.ttl" <<'EOF'
@prefix ex: <http://example.org/prpifp/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
ex:ssn a owl:InverseFunctionalProperty .
ex:alice ex:ssn "123" .
ex:bob ex:ssn "123" .
EOF

# ---------------------------------------------------------------------
# prp-key: Person owl:hasKey (name), p1/p2 a Person with name values
# "Alice"@en / "Alice"@EN  |=  p1 owl:sameAs p2 -- this is the WEAKENED
# ROW behavior documented at docs/theorem-registry.md line ~140
# (prp-key row): the engine's agree_on_property uses rdf_term_eq
# (RDF-1.1 value equality, case-insensitive lang tags), which is
# STRICTLY MORE permissive than the row's shares_key_values (plain ==).
# This test PINS that the engine unifies case-differing lang tags —
# it is documented shipping behavior, not a regression to fix.
# ---------------------------------------------------------------------

cat > "${FIX}/prpkey_base.ttl" <<'EOF'
@prefix ex: <http://example.org/prpkey/> .
@prefix owl: <http://www.w3.org/2002/07/owl#> .
ex:Person a owl:Class ;
  owl:hasKey ( ex:name ) .
ex:p1 a ex:Person ;
  ex:name "Alice"@en .
ex:p2 a ex:Person ;
  ex:name "Alice"@EN .
EOF

echo "generate.sh: wrote fixtures to ${FIX}"
