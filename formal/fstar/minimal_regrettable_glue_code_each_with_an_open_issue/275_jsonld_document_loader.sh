#!/bin/bash
# Issue #275: documentLoader realisation for JSONLD.Loader.jsonld_load_document
# https://github.com/danbri/factoidal/issues/275
#
# Background
# ----------
# JSONLD.Loader.fst declares the JSON-LD remote-document loading
# boundary (JSON-LD 1.1 API "documentLoader"):
#
#   assume val jsonld_load_document : string -> option string
#
# JSONLD.Context's context_process now CALLS this directly (a JString
# context value, or an "@import" context-object member — see that
# module's banner). Different CONSUMER BINARIES need different real
# behavior for the SAME extracted symbol:
#   - bin/jsonld-runner/jsonld_runner.ml: map the W3C suite's base IRI
#     prefix (https://w3c.github.io/json-ld-api/tests/) to
#     third_party/testing/json-ld/tests/ on disk and read the file.
#   - bin/factoidal-cli, bin/factoidal-dump-nq, bin/factoidal-http:
#     fun _ -> None (honest failure) until a real HTTP loader is wired
#     for that consumer specifically.
#
# Since all consumers link the SAME ocaml-output/JSONLD_Loader.ml, this
# patch installs ONE shared dispatch shape — a mutable ref cell holding
# the current loader closure, defaulting to `fun _ -> None`, plus a
# `jsonld_loader_register` setter — and each CONSUMER binary's own
# main() calls the setter with its own closure before parsing. This is
# the same "one global assume-val, per-consumer realisation via a
# registration hook" shape as 57_service_client_bind.sh's
# service_endpoint_table/_register (SPARQL SERVICE endpoint resolution)
# — see that patch for the precedent this one follows.
#
# Per CLAUDE.md rule #11 (ASSUME-IO): the ref cell + setter are pure
# dispatch glue, zero RDF/JSON-LD semantic logic. The DECISION of which
# bytes come back for which IRI is each consumer's own business logic,
# in bin/<consumer>/, not here.

set -euo pipefail

OUT_DIR="${1:-ocaml-output}"

# Backward compatibility: if $1 is a .ml file, use its directory.
if [[ -f "$OUT_DIR" && "$OUT_DIR" == *.ml ]]; then
  OUT_DIR="$(dirname "$OUT_DIR")"
fi

FILE="$OUT_DIR/JSONLD_Loader.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  [275_jsonld_document_loader] $FILE not found (JSONLD.Loader not extracted yet); skipping."
  exit 0
fi

# Idempotency: marker is the ref-cell declaration.
if grep -q 'jsonld_loader_ref' "$FILE"; then
  echo "  [275_jsonld_document_loader] already applied; skipping."
  exit 0
fi

echo "  Patching $FILE (jsonld_load_document -> ref-cell dispatch)..."

python3 - "$FILE" <<'PYEOF'
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# F* 2025.12.15 emits two distinct surface forms for `assume val`
# (see 202_now_ms.sh's precedent comment for the same split):
#   form A:  let jsonld_load_document (uu___ : Prims.string) :
#              Prims.string FStar_Pervasives_Native.option=
#              failwith "Not yet implemented: JSONLD.Loader.jsonld_load_document"
#   form B:  let (jsonld_load_document : Prims.string -> Prims.string FStar_Pervasives_Native.option) =
#              fun uu___ -> failwith "Not yet implemented: ..."
old_patterns = [
    # form A
    'let jsonld_load_document (uu___ : Prims.string) :\n'
    '  Prims.string FStar_Pervasives_Native.option=\n'
    '  failwith "Not yet implemented: JSONLD.Loader.jsonld_load_document"',
    # form B
    'let (jsonld_load_document : Prims.string -> Prims.string FStar_Pervasives_Native.option) =\n'
    '  fun uu___ -> failwith "Not yet implemented: JSONLD.Loader.jsonld_load_document"',
]

new_body = (
    '(* Issue #275: rule-#11 ASSUME-IO realisation -- one shared dispatch\n'
    '   shape for every consumer binary (precedent:\n'
    '   57_service_client_bind.sh\'s service_endpoint_table/_register).\n'
    '   Default (nothing registered) is an honest None: a consumer that\n'
    '   never calls jsonld_loader_register gets the same "no remote\n'
    '   loading" behavior it had before this patch existed. *)\n'
    'let jsonld_loader_ref\n'
    '  : (Prims.string -> Prims.string FStar_Pervasives_Native.option) ref =\n'
    '  ref (fun (uu___ : Prims.string) -> FStar_Pervasives_Native.None)\n'
    'let jsonld_loader_register\n'
    '    (f : Prims.string -> Prims.string FStar_Pervasives_Native.option) : unit =\n'
    '  jsonld_loader_ref := f\n'
    'let jsonld_load_document (iri : Prims.string) :\n'
    '  Prims.string FStar_Pervasives_Native.option=\n'
    '  (!jsonld_loader_ref) iri'
)

replaced = False
for old in old_patterns:
    if old in content:
        content = content.replace(old, new_body, 1)
        replaced = True
        break

if not replaced:
    sys.stderr.write(
        "  ERROR: 275_jsonld_document_loader could not find the failwith stub "
        "for jsonld_load_document in " + path +
        "\n         Has the extraction shape changed?\n"
    )
    sys.exit(1)

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  [275_jsonld_document_loader] applied: jsonld_load_document -> ref-cell dispatch (jsonld_loader_register)."
