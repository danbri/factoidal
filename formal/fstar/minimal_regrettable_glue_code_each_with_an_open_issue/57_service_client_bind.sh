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

# 2026-07-05 follow-up (same class of hazard fixed for issue #261 in
# experimental_ocaml_glue/cottas_ondisk_runtime.sh): F* extraction's
# choice of module qualifier for `wf_iri` is NOT stable — the ongoing
# RDF.Graph.Executable -> RDF.Term/RDF.Triple/RDF.Graph split means a
# fresh extraction can emit `RDF_Graph_Executable.wf_iri`,
# `RDF_Term.wf_iri`, or (for other types touched by this same split)
# other new qualifiers. This patch used to hardcode
# `RDF_Graph_Executable.wf_iri` in the OLD-stub match, so a fresh
# extraction that emitted `RDF_Term.wf_iri` instead made the whole
# replacement silently miss (only a non-fatal WARNING from
# ocaml-patches.sh), leaving `service_endpoint_lookup` as
# `failwith "Not yet implemented"` -- every SPARQL SERVICE clause
# query would then crash at runtime instead of resolving.  Fixed by
# matching the qualifier with a regex alternation, and by writing the
# NEW code with no explicit type annotation on the `rdf_graph` value
# at all -- it's pinned by unification with `graph_to_store`'s
# existing parameter type instead, so this patch never needs to know
# which qualifier module owns `rdf_graph` this run either.
python3 - "$FILE" <<'PYEOF'
import re
import sys

path = sys.argv[1]
with open(path, "r") as f:
    content = f.read()

# Replace the extracted failwith stub. The F* function returns
# 'graph_store FStar_Pervasives_Native.option', and graph_store is
# extracted as a record with a single field [gs_graph]. We construct
# Some/None purely; the hashtable holds rdf_graph values keyed by IRI
# string and we wrap them on lookup.
old_re = re.compile(
    r"let service_endpoint_lookup \(uu___ : (RDF_Graph_Executable|RDF_Term)\.wf_iri\) :\n"
    r"  graph_store FStar_Pervasives_Native\.option=\n"
    r'  failwith "Not yet implemented: SPARQL11\.Algebra\.service_endpoint_lookup"'
)

new = '''(* SERVICE endpoint resolver -- issue #57.
   Global table populated by the test runner from qt:serviceData
   manifest declarations. Lookup is keyed on the absolute IRI string
   of the endpoint. The value type is deliberately left unannotated:
   `graph_to_store g` below pins it to whatever module currently
   owns `rdf_graph` (RDF.Graph.Executable is being split into
   RDF.Term/RDF.Triple/RDF.Graph; the qualifier has already moved
   once) without this patch needing to track the split. *)
let service_endpoint_table = Hashtbl.create 16
let service_endpoint_register (iri : Prims.string) g : unit =
  Hashtbl.replace service_endpoint_table iri g
let service_endpoint_clear () : unit =
  Hashtbl.clear service_endpoint_table
let service_endpoint_lookup (iri : Prims.string) : graph_store FStar_Pervasives_Native.option=
  match Hashtbl.find_opt service_endpoint_table iri with
  | Some g -> FStar_Pervasives_Native.Some (graph_to_store g)
  | None -> FStar_Pervasives_Native.None'''

m = old_re.search(content)
if not m:
    sys.stderr.write(
        "  ERROR: patch 57 did not find the expected service_endpoint_lookup "
        f"stub in {path}\n"
        "         Has the extraction shape changed beyond the qualifier?\n"
    )
    sys.exit(1)

content = content[:m.start()] + new + content[m.end():]

with open(path, "w") as f:
    f.write(content)
PYEOF

echo "  SERVICE resolver patched."
