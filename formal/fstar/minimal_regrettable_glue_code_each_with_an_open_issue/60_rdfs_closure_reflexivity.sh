#!/bin/bash
# Post-extraction patch: RDFS closure and reflexivity axioms in w3c_runner.ml
# Issue: https://github.com/danbri/factoidal/issues/60
#
# KNOWN VIOLATION: This logic belongs in F* (tracked in issue #60).
#
# Patches w3c_runner.ml with:
#   - RDFS closure application to default and named graphs under entailment
#   - Reflexivity axiom generation (subClassOf/subPropertyOf self)
#   - Re-closure after reflexivity

set -euo pipefail

OUTDIR="$1"

FILE="$OUTDIR/w3c_runner.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Skipping 60_rdfs_closure_reflexivity.sh: $FILE not found" >&2
  exit 0
fi

echo "  Applying 60_rdfs_closure_reflexivity.sh to $FILE..."

if ! grep -q 'Apply entailment regime closure if needed' "$FILE"; then
  python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

content = content.replace(
    '''  (* Load named graph data *)
  let named_graphs = List.map (fun (iri, path) ->
    let triples = load_triples path in
    RDF_Graph_Executable.({ ng_name = iri; ng_graph = triples })
  ) tc.named_data_files in''',
    '''  (* Apply entailment regime closure if needed (for SPARQL entailment tests) *)
  let graph = match tc.test_type_detail with
    | "RDFS" | "RDF" ->
      let closed = (try RDF_Graph_Executable.rdfs_closure graph (Z.of_int 100)
                    with _ -> graph) in
      (* Add RDFS reflexivity axioms: every class C gets C rdfs:subClassOf C,
         and every property P gets P rdfs:subPropertyOf P.
         These are entailed by RDFS but not yet in the F* closure. *)
      let rdfs_subClassOf = "http://www.w3.org/2000/01/rdf-schema#subClassOf" in
      let rdfs_subPropertyOf = "http://www.w3.org/2000/01/rdf-schema#subPropertyOf" in
      let rdf_type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" in
      let rdfs_class = "http://www.w3.org/2000/01/rdf-schema#Class" in
      let rdf_property = "http://www.w3.org/1999/02/22-rdf-syntax-ns#Property" in
      let owl_class = "http://www.w3.org/2002/07/owl#Class" in
      let owl_objprop = "http://www.w3.org/2002/07/owl#ObjectProperty" in
      let owl_dataprop = "http://www.w3.org/2002/07/owl#DatatypeProperty" in
      (* Collect all classes: anything that appears as object of rdf:type that is itself
         typed as rdfs:Class/owl:Class, or anything that appears as subject/object of rdfs:subClassOf *)
      let classes = List.fold_left (fun acc t ->
        let acc = if t.p = rdfs_subClassOf then
          let acc = (match t.s with S_IRI i -> if List.mem i acc then acc else i :: acc | _ -> acc) in
          (match t.o with T_IRI i -> if List.mem i acc then acc else i :: acc | _ -> acc)
        else acc in
        if t.p = rdf_type then
          match t.o with
          | T_IRI c when c = rdfs_class || c = owl_class ->
            (match t.s with S_IRI i -> if List.mem i acc then acc else i :: acc | _ -> acc)
          | _ -> acc
        else acc
      ) [] closed in
      (* Collect all properties *)
      let properties = List.fold_left (fun acc t ->
        let acc = if t.p = rdfs_subPropertyOf then
          let acc = (match t.s with S_IRI i -> if List.mem i acc then acc else i :: acc | _ -> acc) in
          (match t.o with T_IRI i -> if List.mem i acc then acc else i :: acc | _ -> acc)
        else acc in
        if t.p = rdf_type then
          match t.o with
          | T_IRI c when c = rdf_property || c = owl_objprop || c = owl_dataprop ->
            (match t.s with S_IRI i -> if List.mem i acc then acc else i :: acc | _ -> acc)
          | _ -> acc
        else acc
      ) [] closed in
      (* Add reflexivity triples *)
      let open RDF_Graph_Executable in
      let reflexive = List.map (fun c ->
        { s = S_IRI c; p = rdfs_subClassOf; o = T_IRI c }
      ) classes @ List.map (fun p ->
        { s = S_IRI p; p = rdfs_subPropertyOf; o = T_IRI p }
      ) properties in
      let closed = List.fold_left (fun g t ->
        if List.exists (fun t2 -> t2.s = t.s && t2.p = t.p && t2.o = t.o) g then g
        else t :: g
      ) closed reflexive in
      (* Re-run closure to propagate reflexivity effects *)
      (try RDF_Graph_Executable.rdfs_closure closed (Z.of_int 100)
       with _ -> closed)
    | _ -> graph in

  (* Load named graph data *)
  let named_graphs = List.map (fun (iri, path) ->
    let triples = load_triples path in
    let triples = match tc.test_type_detail with
      | "RDFS" | "RDF" ->
        (try RDF_Graph_Executable.rdfs_closure triples (Z.of_int 100)
         with _ -> triples)
      | _ -> triples in
    RDF_Graph_Executable.({ ng_name = iri; ng_graph = triples })
  ) tc.named_data_files in'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF
fi

echo "  60_rdfs_closure_reflexivity.sh applied."
