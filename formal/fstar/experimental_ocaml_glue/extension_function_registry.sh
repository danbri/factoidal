#!/bin/bash
# Issue #463: SPARQL 1.1 §17.6 extension-function registry.
# https://github.com/danbri/factoidal/issues/463
#
# Replaces the F*-extracted failwith stub for
#
#   assume val extension_function_call : string -> list eval_result -> option eval_result
#
# with an OCaml implementation backed by a global mutable hashtable of
# host-supplied closures, keyed by the function's absolute IRI string.
#
# This is a rule-#11 host-engine call-out (same family as issue #57's
# service_endpoint_lookup): zero RDF/SPARQL semantic logic lives here.
# WHICH IRIs dispatch to the registry at all, and that an unregistered
# IRI is an error, is decided in F* (SPARQL11.Algebra.fst's
# E_FunctionCall arm — the registry is consulted LAST, after every
# natively-implemented function family, and None maps to ER_Error).
# This patch only stores and retrieves the host's closures.
#
# Registrants:
#   - bin/npm-entry/entry_jsoo.ml bridges caller-supplied JS functions
#     (Comunica-style extensionFunctions) into closures here;
#   - tests/unit/extension_function_unit.ml registers plain OCaml
#     closures to pin the F* dispatch semantics natively.
#
# The F*-side purity assumption (each (iri, args) call sees one stable
# answer within a query evaluation) is the REGISTRANT's contract to
# honor — the JS bridge memoises per (iri, serialised args); a native
# registrant must supply a deterministic closure.

set -euo pipefail

OUTDIR="$1"

if [[ -f "$OUTDIR" && "$OUTDIR" == *.ml ]]; then
  OUTDIR="$(dirname "$OUTDIR")"
fi

if [[ ! -d "$OUTDIR" ]]; then
  echo "Error: $OUTDIR is not a directory" >&2
  exit 1
fi

FILE="$OUTDIR/SPARQL11_Algebra.ml"
if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE (extension-function registry, #463)..."

# Idempotency: if the global table is already declared, skip.
if grep -q 'extension_function_table' "$FILE"; then
  echo "  Already patched; skipping."
  exit 0
fi

python3 - "$FILE" <<'PYEOF'
import re
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# Replace the extracted failwith stub. Tolerant of argument-name and
# line-break drift (the uu___ numbering and wrapping are extraction
# artifacts), and of the eval_result qualifier: anchored on the
# function name and its own failwith message only.
old_re = re.compile(
    r"let extension_function_call [^=]*=\s*\n?"
    r'\s*failwith "Not yet implemented: SPARQL11\.Algebra\.extension_function_call"'
)

new = '''(* Extension-function registry -- issue #463 (SPARQL 1.1 s17.6).
   Global table of host-supplied closures keyed by absolute function
   IRI. Populated by the npm-entry JS bridge (Comunica-style
   extensionFunctions) or by native registrants (unit tests, future
   CLI plug-ins). All dispatch DECISIONS live in F*: the E_FunctionCall
   arm consults this hook last and maps None to ER_Error, the
   spec-required unsupported-function error. The closure type uses
   stdlib option for registrant ergonomics; conversion to the
   extracted FStar_Pervasives_Native.option happens here. *)
let extension_function_table : (string, eval_result list -> eval_result option) Hashtbl.t =
  Hashtbl.create 16
let extension_function_register (iri : string) (f : eval_result list -> eval_result option) : unit =
  Hashtbl.replace extension_function_table iri f
let extension_function_unregister (iri : string) : unit =
  Hashtbl.remove extension_function_table iri
let extension_function_clear () : unit =
  Hashtbl.clear extension_function_table
let extension_function_call (iri : Prims.string) (args : eval_result Prims.list)
  : eval_result FStar_Pervasives_Native.option =
  match Hashtbl.find_opt extension_function_table iri with
  | None -> FStar_Pervasives_Native.None
  | Some f ->
    (match f args with
     | Some r -> FStar_Pervasives_Native.Some r
     | None -> FStar_Pervasives_Native.None)'''

m = old_re.search(content)
if not m:
    sys.stderr.write(
        "  ERROR: patch (#463) did not find the expected extension_function_call "
        f"stub in {path}\n"
        "         Has the extraction shape changed?\n"
    )
    sys.exit(1)

content = content[:m.start()] + new + content[m.end():]

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  Extension-function registry patched."
