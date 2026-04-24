#!/bin/bash
# Issue #57: SPARQL SERVICE endpoint resolver for federated query.
# https://github.com/danbri/factoidal/issues/57
#
# Replaces the F*-extracted failwith stub for
#
#   assume val service_endpoint_lookup : wf_iri -> option graph_store
#
# with an OCaml implementation backed by a global mutable hashtable. The
# test runner (w3c_runner.ml) populates this hashtable from
# qt:serviceData declarations in W3C SPARQL service-suite manifests:
# each <qt:endpoint> IRI maps to a graph_store loaded from the
# associated <qt:data> Turtle file.
#
# This is glue (rule #15-compliant): zero RDF/SPARQL semantic logic.
# The decision of which IRIs map to which stores is data, populated
# from manifests by the runner. The decision of HOW to dispatch a
# SERVICE request lives in F* (SPARQL11.Algebra.eval_pattern_store).
#
# Live HTTP federation is a future phase: would require Dv-effecting
# evaluator (or a snapshot-based bulk fetch up-front).

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

FILE="$OUTDIR/SPARQL11_Algebra.ml"
if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE (SERVICE endpoint resolver)..."

# Idempotency: if the global table is already declared, skip.
if grep -q 'service_endpoint_table' "$FILE"; then
  echo "  Already patched; skipping."
  exit 0
fi

python3 -c "
with open('$FILE', 'r') as f:
    content = f.read()

# Replace the extracted failwith stub. The F* function returns
# 'graph_store FStar_Pervasives_Native.option', and graph_store is
# extracted as a record with a single field [gs_graph]. We construct
# Some/None purely; the hashtable holds rdf_graph values keyed by IRI
# string and we wrap them on lookup.
old = '''let service_endpoint_lookup (uu___ : Prims.string) : graph_store FStar_Pervasives_Native.option=
  failwith \"Not yet implemented: SPARQL11.Algebra.service_endpoint_lookup\"'''

new = '''(* SERVICE endpoint resolver — issue #57.
   Global table populated by the test runner from qt:serviceData
   manifest declarations. Lookup is keyed on the absolute IRI string
   of the endpoint. *)
let service_endpoint_table : (Prims.string, RDF_Graph_Executable.rdf_graph) Hashtbl.t =
  Hashtbl.create 16
let service_endpoint_register (iri : Prims.string) (g : RDF_Graph_Executable.rdf_graph) : unit =
  Hashtbl.replace service_endpoint_table iri g
let service_endpoint_clear () : unit =
  Hashtbl.clear service_endpoint_table
let service_endpoint_lookup (iri : Prims.string) : graph_store FStar_Pervasives_Native.option=
  match Hashtbl.find_opt service_endpoint_table iri with
  | Some g -> FStar_Pervasives_Native.Some { gs_graph = g }
  | None -> FStar_Pervasives_Native.None'''

if old not in content:
    raise SystemExit('patch 57: did not find expected service_endpoint_lookup stub in ' + '$FILE')

content = content.replace(old, new)

with open('$FILE', 'w') as f:
    f.write(content)
"

echo "  SERVICE resolver patched."
