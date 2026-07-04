#!/bin/bash
# Issue #TBD: documentLoader realisation for JSONLD.Loader.jsonld_load_document
# (orchestrator: file the issue, then rename this file <issue>_jsonld_document_loader.sh
#  and update this header + JSONLD.Loader.fst's banner with the number)
#
# Background
# ----------
# JSONLD.Loader.fst declares the JSON-LD remote-document loading
# boundary (JSON-LD 1.1 API "documentLoader"):
#
#   assume val jsonld_load_document : string -> option string
#
# Per docs/designissues/2026-07-04-jsonld-program-lessons.md ("remote
# contexts are suite-local files") and CLAUDE.md Iron Rule #11
# (ASSUME-IO), the realisation belongs in each CONSUMER binary, not in
# a library-level .ml patch:
#
#   - bin/jsonld-runner/jsonld_runner.ml: map the W3C suite's base IRI
#     prefix (https://w3c.github.io/json-ld-api/tests/) to
#     third_party/testing/json-ld/tests/ on disk and read the file.
#   - bin/factoidal + other CLIs: fun _ -> None (honest failure) until
#     a real HTTP loader is wired for that consumer.
#
# STATUS 2026-07-04 (JSON-LD Phase 5): DECLARATION ONLY. The module is
# not yet in build-ocaml.sh's extraction lists because nothing calls
# the assume val yet — JSONLD.Context's JString-context branch and
# @import support (the two consumers) are the next Phase 5 slice. When
# that slice lands: add JSONLD.Loader to the three build-ocaml.sh
# module lists, realise the val in each consumer per the plan above,
# and make this script verify the consumer realisations exist (it must
# fail loudly if a consumer binary links the extracted JSONLD_Loader.ml
# without providing the val).
#
# This placeholder is a no-op patch so the Iron Rule #3 inventory
# (every assume val has a stub patch + open issue) stays complete from
# the moment the assume val exists in the tree.

set -euo pipefail

OUT_DIR="${1:-ocaml-output}"

if [[ ! -f "$OUT_DIR/JSONLD_Loader.ml" ]]; then
  echo "[jsonld_document_loader] JSONLD.Loader not extracted yet (declaration-only phase); nothing to do."
  exit 0
fi

# Once JSONLD.Loader is extracted, the val must be realised by the
# consumer, not here — fail loudly so the build cannot silently link a
# missing primitive.
if ! grep -q "jsonld_load_document" "$OUT_DIR/JSONLD_Loader.ml"; then
  echo "[jsonld_document_loader] extracted JSONLD_Loader.ml lacks jsonld_load_document; check extraction." >&2
  exit 1
fi
echo "[jsonld_document_loader] JSONLD_Loader.ml present: ensure each consumer binary realises jsonld_load_document (see header)." >&2
exit 1
