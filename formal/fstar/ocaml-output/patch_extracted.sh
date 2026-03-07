#!/bin/bash
# Post-extraction patches for SPARQL11_Algebra.ml
# Applied after fstar.exe --codegen OCaml extraction

FILE="SPARQL11_Algebra.ml"

# 1. Patch regex_match
sed -i '/^let regex_match/,/^let [a-z]/{
  /^let regex_match/,/failwith.*regex_match/c\
let regex_match (text : Prims.string) (pattern : Prims.string)\
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=\
  try\
    let case_insensitive = match flags with\
      | FStar_Pervasives_Native.Some f -> String.contains f '\''i'\''\
      | FStar_Pervasives_Native.None -> false in\
    let re = if case_insensitive\
      then Str.regexp_case_fold pattern\
      else Str.regexp pattern in\
    (try let _ = Str.search_forward re text 0 in true\
     with Not_found -> false)\
  with _ -> false
}' "$FILE"

# 2. Patch hash functions
sed -i 's/^let hash_md5 (uu___ : Prims.string) : Prims.string=$/let hash_md5 (s : Prims.string) : Prims.string=/' "$FILE"
sed -i 's/failwith "Not yet implemented: SPARQL11.Algebra.hash_md5"/Digestif.MD5.digest_string s |> Digestif.MD5.to_hex/' "$FILE"
sed -i 's/^let hash_sha1 (uu___ : Prims.string) : Prims.string=$/let hash_sha1 (s : Prims.string) : Prims.string=/' "$FILE"
sed -i 's/failwith "Not yet implemented: SPARQL11.Algebra.hash_sha1"/Digestif.SHA1.digest_string s |> Digestif.SHA1.to_hex/' "$FILE"
sed -i 's/^let hash_sha256 (uu___ : Prims.string) : Prims.string=$/let hash_sha256 (s : Prims.string) : Prims.string=/' "$FILE"
sed -i 's/failwith "Not yet implemented: SPARQL11.Algebra.hash_sha256"/Digestif.SHA256.digest_string s |> Digestif.SHA256.to_hex/' "$FILE"
sed -i 's/^let hash_sha384 (uu___ : Prims.string) : Prims.string=$/let hash_sha384 (s : Prims.string) : Prims.string=/' "$FILE"
sed -i 's/failwith "Not yet implemented: SPARQL11.Algebra.hash_sha384"/Digestif.SHA384.digest_string s |> Digestif.SHA384.to_hex/' "$FILE"
sed -i 's/^let hash_sha512 (uu___ : Prims.string) : Prims.string=$/let hash_sha512 (s : Prims.string) : Prims.string=/' "$FILE"
sed -i 's/failwith "Not yet implemented: SPARQL11.Algebra.hash_sha512"/Digestif.SHA512.digest_string s |> Digestif.SHA512.to_hex/' "$FILE"

# 3. Patch eval_expr_ebv, eval_expr_fwd, eval_exists_fwd, eval_select_query_fwd with ref cells
python3 -c "
import re
with open('$FILE', 'r') as f:
    content = f.read()

# Replace the assume val stubs with ref cell pattern
old = '''let eval_expr_ebv (uu___ : expr)
  (uu___1 : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  failwith \"Not yet implemented: SPARQL11.Algebra.eval_expr_ebv\"
let eval_expr_fwd (uu___ : expr)
  (uu___1 : RDF_Graph_Executable.solution_mapping) : eval_result=
  failwith \"Not yet implemented: SPARQL11.Algebra.eval_expr_fwd\"
type named_graph_dataset =
  (Prims.string * RDF_Graph_Executable.rdf_graph) Prims.list
let eval_exists_fwd (uu___ : group_graph_pattern)
  (uu___1 : RDF_Graph_Executable.solution_mapping)
  (uu___2 : RDF_Graph_Executable.rdf_graph) (uu___3 : named_graph_dataset) :
  Prims.bool=
  failwith \"Not yet implemented: SPARQL11.Algebra.eval_exists_fwd\"
let eval_select_query_fwd (uu___ : query)
  (uu___1 : RDF_Graph_Executable.rdf_graph) (uu___2 : named_graph_dataset) :
  solution_sequence=
  failwith \"Not yet implemented: SPARQL11.Algebra.eval_select_query_fwd\"
let eval_property_path_fwd (uu___ : property_path)
  (uu___1 : RDF_Graph_Executable.rdf_graph) :
  (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term) Prims.list=
  failwith \"Not yet implemented: SPARQL11.Algebra.eval_property_path_fwd\"'''

new = '''type named_graph_dataset =
  (Prims.string * RDF_Graph_Executable.rdf_graph) Prims.list
let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =
  ref (fun _ _ -> failwith \"eval_expr_ebv not yet wired\")
let eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =
  ref (fun _ _ -> failwith \"eval_expr_fwd not yet wired\")
let eval_exists_fwd_ref : (group_graph_pattern -> RDF_Graph_Executable.solution_mapping -> RDF_Graph_Executable.rdf_graph -> named_graph_dataset -> Prims.bool) ref =
  ref (fun _ _ _ _ -> failwith \"eval_exists_fwd not yet wired\")
let eval_select_query_fwd_ref : (query -> RDF_Graph_Executable.rdf_graph -> named_graph_dataset -> solution_sequence) ref =
  ref (fun _ _ _ -> failwith \"eval_select_query_fwd not yet wired\")
let eval_property_path_fwd_ref : (property_path -> RDF_Graph_Executable.rdf_graph -> (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term) Prims.list) ref =
  ref (fun _ _ -> failwith \"eval_property_path_fwd not yet wired\")
let eval_expr_ebv (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=
  !eval_expr_ebv_ref e mu
let eval_expr_fwd (e : expr)
  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=
  !eval_expr_fwd_ref e mu
let eval_exists_fwd (p : group_graph_pattern)
  (mu : RDF_Graph_Executable.solution_mapping)
  (g : RDF_Graph_Executable.rdf_graph) (ds : named_graph_dataset) : Prims.bool=
  !eval_exists_fwd_ref p mu g ds
let eval_select_query_fwd (q : query)
  (g : RDF_Graph_Executable.rdf_graph) (ds : named_graph_dataset) : solution_sequence=
  !eval_select_query_fwd_ref q g ds
let eval_property_path_fwd (p : property_path)
  (g : RDF_Graph_Executable.rdf_graph) : (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term) Prims.list=
  !eval_property_path_fwd_ref p g'''

content = content.replace(old, new)

# Wire up eval_expr_ebv_ref and eval_expr_fwd_ref after eval_expr definition
# Find 'type group = {' and insert wiring before it
wire1 = '''let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)
type group = {'''
content = content.replace('type group = {', wire1)

# Wire up eval_exists_fwd_ref after eval_not_exists
target = 'Prims.op_Negation (eval_exists pattern mu graph ds)\n'
content = content.replace(target, target + 'let () = eval_exists_fwd_ref := (fun p mu g ds -> eval_exists p mu g ds)\n', 1)

# Wire up eval_select_query_fwd_ref after eval_select_query definition
target2 = 'let is_not_literal (t : RDF_Graph_Executable.rdf_term)'
wire2 = 'let () = eval_select_query_fwd_ref := (fun q g ds -> eval_select_query q g ds)\n' + target2
content = content.replace(target2, wire2, 1)

# Wire up eval_property_path_fwd_ref after eval_property_path definition
target3 = 'type numeric_precision ='
wire3 = 'let () = eval_property_path_fwd_ref := (fun p g -> eval_property_path p g)\n' + target3
content = content.replace(target3, wire3, 1)

with open('$FILE', 'w') as f:
    f.write(content)
print('Patches applied successfully')
"
