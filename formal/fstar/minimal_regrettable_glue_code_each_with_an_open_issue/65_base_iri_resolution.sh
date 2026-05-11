#!/bin/bash
# Issue #65: BASE IRI resolution — RETIRED 2026-05-11.
# https://github.com/danbri/factoidal/issues/65
#
# Steps 2a/2b/2c (commits e1ffba4, 8b7d9f6, dff3bdc) threaded
# `option wf_iri` through every eval_* and eval_pattern_* function in
# SPARQL11.Algebra.fst and SPARQL11.Store.fst. eval_select_query now
# reads `q.q_base` directly and passes it to the post-WHERE pipeline
# AND the WHERE evaluator AND the FILTER / OPTIONAL paths.
#
# The parser side (SPARQL11.Parser.fst) was already pure F*: it
# pre-rewrites the token stream against BASE via
# `resolve_relative_iri_tokens base ts'` (Parser.fst:2561, 3959, 4024)
# before parsing the body. The OCaml-injected `resolve_tok_iri` and
# `current_base_iri_ref` were defensive belt-and-suspenders; they
# carried no information that the F* pre-pass didn't already supply.
#
# This script intentionally does nothing now. Kept in place as the
# audit trail showing #65 is closed: rule-#11 wormhole removed.
# After CI confirms parity (full SPARQL 1.1 + RDF 1.1 W3C suites at
# 631 and 1031 pass with this patch as a no-op), the file can be
# removed entirely.

set -euo pipefail

OUTDIR="$1"

# Backward compatibility: if $1 is a .ml file, use its directory
if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

echo "  #65 base IRI patch retired — F*-side threading covers all paths."
