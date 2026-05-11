#!/bin/bash
# Issue #64: SPARQL parser escape processing stubs — RETIRED 2026-05-11.
# https://github.com/danbri/factoidal/issues/64
#
# All three escape-processing functions are now implemented in pure F*
# in `SPARQL11.Parser.fst`:
#   - utf8_of_codepoint     (commit 1d2b669, 2026-05-10)
#   - process_iri_escapes   (commit e79c387, 2026-05-10)
#   - process_string_escapes_opt + Tok_INVALID + first_invalid_token_msg
#                           (commits d92311d / Step-2/Step-3, 2026-05-11)
#
# The `process_string_escapes` `assume val` is gone from F* sources;
# `scan_string` consumes `process_string_escapes_opt : string -> option string`
# directly, the tokenizer emits `Tok_INVALID msg` on None, and
# `parse_sparql_with_base` / `parse_sparql_update_with_base` short-circuit
# to `ParseErr msg` if any `Tok_INVALID` is in the token stream — replacing
# the OCaml `failwith "invalid Unicode codepoint: surrogate"` path.
#
# Kept as a no-op shell stub for the audit trail. Can be deleted entirely
# after a few CI cycles confirm the W3C syntax-query suite still rejects
# `syn-invalid-codepoint-escaped-bad-01.rq` correctly.

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

echo "  #64 escape-processing patch retired — F*-side covers all paths."
