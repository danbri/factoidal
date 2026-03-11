#!/bin/bash
# Post-extraction patch: w3c_runner.ml I/O glue fixes
# Issue: https://github.com/danbri/factoidal/issues/69
#
# Patches w3c_runner.ml with:
#   - Namespace constants (sd_ns, ent_ns)
#   - Expanded entailment regime detection (sd:entailmentRegime on action blank nodes)
#   - file_to_base_uri helper
#   - Pass query_file as base in eval tests
#   - Pass query_file as base in positive syntax tests
#   - Catch Failure in negative syntax tests

set -euo pipefail

OUTDIR="$1"

FILE="$OUTDIR/w3c_runner.ml"
if [[ ! -f "$FILE" ]]; then
  echo "  Skipping 69_runner_io_glue.sh: $FILE not found" >&2
  exit 0
fi

echo "  Applying 69_runner_io_glue.sh to $FILE..."

python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

# 1. Add sd_ns and ent_ns namespace constants
if 'let sd_ns =' not in content:
    content = content.replace(
        '''let rdft_ns = "http://www.w3.org/ns/rdftest#"

let find_objects graph subj pred =''',
        '''let rdft_ns = "http://www.w3.org/ns/rdftest#"
let sd_ns = "http://www.w3.org/ns/sparql-service-description#"
let ent_ns = "http://www.w3.org/ns/entailment/"

let find_objects graph subj pred ='''
    )

# 2. Expand entailment regime detection to handle sd:entailmentRegime on action blank nodes
if 'sd:entailmentRegime is on the action blank node' not in content:
    content = content.replace(
        '''    (* Get entailment regime (for rdf-mt tests) *)
    let regime_objs = find_objects graph entry_subj (mf_ns ^ "entailmentRegime") in
    let test_type_detail = match regime_objs with
      | r :: _ -> term_to_str r
      | [] -> "" in''',
        '''    (* Get entailment regime (for rdf-mt tests and SPARQL entailment tests) *)
    let regime_objs = find_objects graph entry_subj (mf_ns ^ "entailmentRegime") in
    let test_type_detail = match regime_objs with
      | r :: _ -> term_to_str r
      | [] ->
        (* For SPARQL entailment tests, sd:entailmentRegime is on the action blank node *)
        (match action_objs with
         | action :: _ ->
           let action_subj = match action with
             | T_IRI i -> S_IRI i | T_BNode b -> S_BNode b | _ -> S_IRI (term_to_str action) in
           let sd_regime_objs = find_objects graph action_subj (sd_ns ^ "entailmentRegime") in
           (* sd:entailmentRegime can be a single value or an RDF list *)
           let regime_iris = List.concat_map (fun obj ->
             match obj with
             | T_IRI i -> [i]
             | T_BNode _ ->
               (* It's an RDF list -- walk it *)
               let rec walk_list node acc =
                 let firsts = find_objects graph node rdf_first in
                 let rests = find_objects graph node rdf_rest in
                 let acc = match firsts with
                   | T_IRI i :: _ -> i :: acc
                   | _ -> acc in
                 match rests with
                 | T_IRI i :: _ when i = rdf_nil -> List.rev acc
                 | (T_BNode _ as next) :: _ ->
                   let next_subj = match next with T_BNode b -> S_BNode b | T_IRI i -> S_IRI i | _ -> S_IRI "" in
                   walk_list next_subj acc
                 | _ -> List.rev acc
               in
               walk_list (S_BNode (match obj with T_BNode b -> b | _ -> "")) []
             | _ -> []
           ) sd_regime_objs in
           (* Pick the best regime we can handle: prefer RDFS > RDF > D *)
           if List.exists (fun i -> i = ent_ns ^ "RDFS") regime_iris then "RDFS"
           else if List.exists (fun i -> i = ent_ns ^ "RDF") regime_iris then "RDF"
           else if List.exists (fun i -> i = ent_ns ^ "D") regime_iris then "D"
           else if List.exists (fun i -> i = ent_ns ^ "OWL-Direct") regime_iris then "OWL-Direct"
           else if List.exists (fun i -> i = ent_ns ^ "OWL-RDF-Based") regime_iris then "OWL-RDF-Based"
           else ""
         | [] -> "") in'''
    )

# 3. Add file_to_base_uri helper and modify parse_sparql_query to accept optional base
if 'let file_to_base_uri' not in content:
    content = content.replace(
        '''let parse_sparql_query content =
  match SPARQL11_Parser.parse_sparql content with
  | SPARQL11_Parser.ParseOk (q, _remaining) -> hoist_query_filters q
  | SPARQL11_Parser.ParseErr msg -> raise (Sparql_parse_error msg)''',
        '''let file_to_base_uri path =
  let abs = if Filename.is_relative path then Filename.concat (Sys.getcwd ()) path else path in
  "file://" ^ abs

let parse_sparql_query ?(base_file=None) content =
  (match base_file with
   | Some path -> SPARQL11_Algebra.current_base_iri_ref := Some (file_to_base_uri path)
   | None -> ());
  let result =
    match SPARQL11_Parser.parse_sparql content with
    | SPARQL11_Parser.ParseOk (q, _remaining) -> hoist_query_filters q
    | SPARQL11_Parser.ParseErr msg -> raise (Sparql_parse_error msg) in
  result'''
    )

# 4. Pass query_file as base to parse_sparql_query in eval test
if '~base_file:(Some tc.query_file)' not in content:
    content = content.replace(
        '''    | Some content -> parse_sparql_query content
  in

  (* Execute query against extracted evaluator *)''',
        '''    | Some content -> parse_sparql_query ~base_file:(Some tc.query_file) content
  in

  (* Execute query against extracted evaluator *)'''
    )

# 5. Pass query_file as base in positive syntax tests
if 'parse_sparql_query ~base_file:(Some tc.query_file) content); Pass' not in content:
    content = content.replace(
        '''     | Some content ->
       (try ignore (parse_sparql_query content); Pass
        with
        | Sparql_parse_error _ -> Fail "Should parse but didn't"
        | Sparql_unsupported msg -> Unsupported_feature msg))''',
        '''     | Some content ->
       (try ignore (parse_sparql_query ~base_file:(Some tc.query_file) content); Pass
        with
        | Sparql_parse_error _ -> Fail "Should parse but didn't"
        | Failure _ -> Fail "Should parse but didn't"
        | Sparql_unsupported msg -> Unsupported_feature msg))'''
    )

# 6. Catch Failure in negative syntax tests (e.g., surrogate codepoints)
if '| Failure _ -> Pass' not in content:
    content = content.replace(
        '''        | Sparql_parse_error _ -> Pass
        | Sparql_unsupported _ -> Unsupported_feature "Can't test rejection"))''',
        '''        | Sparql_parse_error _ -> Pass
        | Failure _ -> Pass
        | Sparql_unsupported _ -> Unsupported_feature "Can't test rejection"))'''
    )

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF

echo "  69_runner_io_glue.sh applied."
