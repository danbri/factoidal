#!/bin/bash
# Post-extraction patches for SPARQL11_Algebra.ml
# These fix assume-val stubs that F* extraction generates as failwith placeholders.
#
# Applied automatically by build-ocaml.sh after F* extraction.

set -euo pipefail

FILE="$1"

if [[ ! -f "$FILE" ]]; then
  echo "Error: $FILE not found" >&2
  exit 1
fi

echo "  Patching $FILE..."

# 1. Replace eval_expr_ebv stub with mutable ref dispatch
sed -i 's/^let eval_expr_ebv (uu___ : expr)/let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =\n  ref (fun _ _ -> failwith "eval_expr_ebv not yet wired")\nlet eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =\n  ref (fun _ _ -> failwith "eval_expr_fwd not yet wired")\nlet eval_expr_ebv (e : expr)/' "$FILE"

sed -i 's/  (uu___1 : RDF_Graph_Executable.solution_mapping) : Prims.bool=$/  (mu : RDF_Graph_Executable.solution_mapping) : Prims.bool=/' "$FILE"

sed -i 's/  failwith "Not yet implemented: SPARQL11.Algebra.eval_expr_ebv"/  !eval_expr_ebv_ref e mu/' "$FILE"

sed -i 's/^let eval_expr_fwd (uu___ : expr)/let eval_expr_fwd (e : expr)/' "$FILE"

# Fix the eval_expr_fwd parameter name and body
python3 -c "
import re
with open('$FILE', 'r') as f:
    content = f.read()

# Fix eval_expr_fwd stub
content = content.replace(
    '  (uu___1 : RDF_Graph_Executable.solution_mapping) : eval_result=\n  failwith \"Not yet implemented: SPARQL11.Algebra.eval_expr_fwd\"',
    '  (mu : RDF_Graph_Executable.solution_mapping) : eval_result=\n  !eval_expr_fwd_ref e mu'
)

# 2. Replace regex_match stub with OCaml Str implementation
# Includes XPath/Perl regex -> OCaml Str regex conversion (handles {n}, (), |, etc.)
content = content.replace(
    '''let regex_match (uu___ : Prims.string) (uu___1 : Prims.string)
  (uu___2 : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  failwith \"Not yet implemented: SPARQL11.Algebra.regex_match\"''',
    '''let xpath_to_str_regex (p : string) : string =
  let open Stdlib in
  let len = String.length p in
  let buf = Buffer.create (len * 2) in
  let i = ref 0 in
  let last_atom = ref \"\" in
  let set_atom s = last_atom := s; Buffer.add_string buf s in
  while !i < len do
    let c = p.[!i] in
    if c = '\\\\\\\\' && !i + 1 < len then begin
      let next = p.[!i + 1] in
      if next = '(' || next = ')' || next = '|' || next = '?' ||
         next = '{' || next = '}' || next = '+' || next = '*' then
        (set_atom (String.make 1 next); i := !i + 2)
      else if next = 'd' then (set_atom \"[0-9]\"; i := !i + 2)
      else if next = 'D' then (set_atom \"[^0-9]\"; i := !i + 2)
      else if next = 'w' then (set_atom \"[a-zA-Z0-9_]\"; i := !i + 2)
      else if next = 'W' then (set_atom \"[^a-zA-Z0-9_]\"; i := !i + 2)
      else if next = 's' then (set_atom \"[ \\\\t\\\\n\\\\r]\"; i := !i + 2)
      else if next = 'S' then (set_atom \"[^ \\\\t\\\\n\\\\r]\"; i := !i + 2)
      else (let s = String.sub p !i 2 in set_atom s; i := !i + 2)
    end else if c = '(' then
      (Buffer.add_string buf \"\\\\(\"; last_atom := \"\"; i := !i + 1)
    else if c = ')' then
      (Buffer.add_string buf \"\\\\)\"; last_atom := \"\\\\)\"; i := !i + 1)
    else if c = '|' then
      (Buffer.add_string buf \"\\\\|\"; last_atom := \"\"; i := !i + 1)
    else if c = '?' then
      (Buffer.add_string buf \"\\\\?\"; i := !i + 1)
    else if c = '{' then begin
      i := !i + 1;
      let nb = Buffer.create 8 in
      while !i < len && p.[!i] <> '}' && p.[!i] <> ',' do
        Buffer.add_char nb p.[!i]; i := !i + 1 done;
      let n = try int_of_string (Buffer.contents nb) with _ -> 1 in
      if !i < len && p.[!i] = ',' then begin
        i := !i + 1;
        let mb = Buffer.create 8 in
        while !i < len && p.[!i] <> '}' do
          Buffer.add_char mb p.[!i]; i := !i + 1 done;
        if !i < len then i := !i + 1;
        let ms = Buffer.contents mb in
        if ms = \"\" then begin
          for _ = 2 to n do Buffer.add_string buf !last_atom done;
          Buffer.add_string buf !last_atom; Buffer.add_char buf '*'
        end else begin
          let m = try int_of_string ms with _ -> n in
          for _ = 2 to n do Buffer.add_string buf !last_atom done;
          for _ = n + 1 to m do
            Buffer.add_string buf !last_atom;
            Buffer.add_string buf \"\\\\?\" done
        end
      end else begin
        if !i < len then i := !i + 1;
        for _ = 2 to n do Buffer.add_string buf !last_atom done
      end
    end else if c = '[' then begin
      let start = !i in
      i := !i + 1;
      if !i < len && p.[!i] = '^' then i := !i + 1;
      if !i < len && p.[!i] = ']' then i := !i + 1;
      while !i < len && p.[!i] <> ']' do i := !i + 1 done;
      if !i < len then i := !i + 1;
      let cls = String.sub p start (!i - start) in
      set_atom cls
    end else (set_atom (String.make 1 c); i := !i + 1)
  done;
  Buffer.contents buf
let regex_match (text : Prims.string) (pattern : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  try
    let case_insensitive = match flags with
      | FStar_Pervasives_Native.Some f -> String.contains f 'i'
      | FStar_Pervasives_Native.None -> false in
    let converted = xpath_to_str_regex pattern in
    let re = if case_insensitive
      then Str.regexp_case_fold converted
      else Str.regexp converted in
    (try let _ = Str.search_forward re text 0 in true
     with Not_found -> false)
  with _ -> false'''
)

# 2b. Replace hash function stubs with OCaml Digest implementations
content = content.replace(
    '''let hash_md5 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_md5\"''',
    '''let hash_md5 (s : Prims.string) : Prims.string=
  Digest.to_hex (Digest.string s)'''
)
content = content.replace(
    '''let hash_sha1 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha1\"''',
    '''let hash_sha1 (s : Prims.string) : Prims.string=
  Sha1.to_hex (Sha1.string s)'''
)
content = content.replace(
    '''let hash_sha256 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha256\"''',
    '''let hash_sha256 (s : Prims.string) : Prims.string=
  Sha256.to_hex (Sha256.string s)'''
)
content = content.replace(
    '''let hash_sha384 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha384\"''',
    '''let hash_sha384 (s : Prims.string) : Prims.string=
  Digestif.SHA384.(to_hex (digest_string s))'''
)
content = content.replace(
    '''let hash_sha512 (uu___ : Prims.string) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.hash_sha512\"''',
    '''let hash_sha512 (s : Prims.string) : Prims.string=
  Sha512.to_hex (Sha512.string s)'''
)

# 2b2. Replace UUID/STRUUID hardcoded stubs with random UUID v4 generation.
# The F* spec returns all-zeros placeholder; we replace with real random UUIDs
# so W3C tests that REGEX-check the format will pass.
content = content.replace(
    '''          if iri_s = "http://www.w3.org/2005/xpath-functions#uuid"
          then
            ER_Term
              (RDF_Graph_Executable.T_IRI
                 "urn:uuid:00000000-0000-0000-0000-000000000000")
          else
            if iri_s = "http://www.w3.org/2005/xpath-functions#struuid"
            then er_string "00000000-0000-0000-0000-000000000000"''',
    '''          if iri_s = "http://www.w3.org/2005/xpath-functions#uuid"
          then
            let () = Random.self_init () in
            let hex () = Printf.sprintf "%04x" (Random.int 0x10000) in
            let s = Printf.sprintf "%s%s-%s-%s-%s-%s%s%s"
              (hex ()) (hex ()) (hex ())
              (Printf.sprintf "4%03x" (Random.int 0x1000))
              (Printf.sprintf "%04x" (0x8000 lor (Random.int 0x4000)))
              (hex ()) (hex ()) (hex ()) in
            ER_Term
              (RDF_Graph_Executable.T_IRI
                 (Prims.strcat "urn:uuid:" s))
          else
            if iri_s = "http://www.w3.org/2005/xpath-functions#struuid"
            then
              let () = Random.self_init () in
              let hex () = Printf.sprintf "%04x" (Random.int 0x10000) in
              let s = Printf.sprintf "%s%s-%s-%s-%s-%s%s%s"
                (hex ()) (hex ()) (hex ())
                (Printf.sprintf "4%03x" (Random.int 0x1000))
                (Printf.sprintf "%04x" (0x8000 lor (Random.int 0x4000)))
                (hex ()) (hex ()) (hex ()) in
              er_string s'''
)

# 2c. Wire eval_exists_fwd assume val stub.
# eval_exists_fwd is declared as assume val in F* and extracted as failwith.
# We need a forward ref because eval_exists is defined after eval_pattern.

# Add forward ref declarations alongside the existing eval_expr refs
content = content.replace(
    '''let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =
  ref (fun _ _ -> failwith \"eval_expr_ebv not yet wired\")
let eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =
  ref (fun _ _ -> failwith \"eval_expr_fwd not yet wired\")''',
    '''let eval_expr_ebv_ref : (expr -> RDF_Graph_Executable.solution_mapping -> Prims.bool) ref =
  ref (fun _ _ -> failwith \"eval_expr_ebv not yet wired\")
let eval_expr_fwd_ref : (expr -> RDF_Graph_Executable.solution_mapping -> eval_result) ref =
  ref (fun _ _ -> failwith \"eval_expr_fwd not yet wired\")
let eval_exists_fwd_ref : (group_graph_pattern -> RDF_Graph_Executable.solution_mapping -> RDF_Graph_Executable.rdf_graph -> RDF_Graph_Executable.rdf_dataset -> Prims.bool) ref =
  ref (fun _ _ _ _ -> false)
let eval_property_path_fwd_ref : (property_path -> RDF_Graph_Executable.rdf_graph -> (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.rdf_term) Prims.list) ref =
  ref (fun _ _ -> [])
let eval_subselect_fwd_ref : (query -> RDF_Graph_Executable.rdf_graph -> RDF_Graph_Executable.rdf_dataset -> solution_sequence) ref =
  ref (fun _ _ _ -> [])'''
)

# Replace eval_exists_fwd failwith body with forward ref dispatch
content = content.replace(
    '''  failwith \"Not yet implemented: SPARQL11.Algebra.eval_exists_fwd\"''',
    '''  !eval_exists_fwd_ref uu___ uu___1 uu___2 uu___3'''
)

# 2e. Wire eval_subselect_fwd to the concrete eval_select_query.
content = content.replace(
    '''  failwith \"Not yet implemented: SPARQL11.Algebra.eval_subselect_fwd\"''',
    '''  !eval_subselect_fwd_ref uu___ uu___1 uu___2'''
)

# 2d. Wire eval_property_path_fwd to the concrete eval_property_path.
# Same forward-ref pattern: declare ref, replace failwith, wire after definition.
content = content.replace(
    '''  failwith \"Not yet implemented: SPARQL11.Algebra.eval_property_path_fwd\"''',
    '''  !eval_property_path_fwd_ref uu___ uu___1'''
)

# 3. Add wiring after eval_expr definition (before 'type group')
content = content.replace(
    'type group = {',
    '''(* Wire up the forward-declared eval_expr_ebv/fwd to the real implementations *)
let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)

type group = {'''
)

# 4. Wire eval_exists_fwd_ref after eval_exists is defined
content = content.replace(
    'let filter_solutions (e : expr) (omega : solution_sequence) :',
    '''(* Wire up eval_exists_fwd to the real eval_exists *)
let () = eval_exists_fwd_ref := eval_exists

let filter_solutions (e : expr) (omega : solution_sequence) :'''
)

# 5. Wire eval_property_path_fwd_ref after eval_property_path is defined
content = content.replace(
    'type numeric_precision =',
    '''(* Wire up eval_property_path_fwd to the real eval_property_path *)
let () = eval_property_path_fwd_ref := eval_property_path

type numeric_precision ='''
)

# 5b. Fix zero-length property path matching on empty graphs.
# SPARQL semantics: ZeroOrMore/ZeroOrOne paths must include zero-length matches
# for constant IRIs/BNodes from the query pattern, even when the graph is empty.
# eval_property_path only generates reflexive pairs for nodes already in the graph,
# so we augment GP_PropertyPath handling to add reflexive pairs for pattern constants.
content = content.replace(
    '''  | GP_PropertyPath (ps, pp, pt) ->
      let pairs = eval_property_path_fwd pp g in
      path_result_to_solutions ps pt pairs''',
    '''  | GP_PropertyPath (ps, pp, pt) ->
      let pairs = eval_property_path_fwd pp g in
      (* SPARQL semantics: ZeroOrMore/ZeroOrOne paths must include zero-length
         matches for any constant IRI/BNode in the pattern, even on empty graphs.
         eval_property_path only generates reflexive pairs for nodes in the graph,
         so we add reflexive pairs for constants from the query pattern here,
         but only if they are not already present (to avoid duplicates). *)
      let pairs = match pp with
        | PP_ZeroOrMore _ | PP_ZeroOrOne _ ->
            let constant_terms =
              (match ps with
               | PS_IRI i -> [RDF_Graph_Executable.T_IRI i]
               | PS_BNode b -> [RDF_Graph_Executable.T_BNode b]
               | PS_Var _ -> [])
              @
              (match pt with
               | PT_IRI i -> [RDF_Graph_Executable.T_IRI i]
               | PT_BNode b -> [RDF_Graph_Executable.T_BNode b]
               | PT_Literal l -> [RDF_Graph_Executable.T_Literal l]
               | PT_Var _ -> []) in
            let has_reflexive t =
              FStar_List_Tot_Base.existsb
                (fun pair -> match pair with (s, o) ->
                   RDF_Graph_Executable.rdf_term_eq s t &&
                   RDF_Graph_Executable.rdf_term_eq o t) pairs in
            let new_terms = FStar_List_Tot_Base.filter
              (fun t -> not (has_reflexive t)) constant_terms in
            let reflexive = FStar_List_Tot_Base.map (fun n -> (n, n)) new_terms in
            FStar_List_Tot_Base.op_At pairs reflexive
        | _ -> pairs in
      path_result_to_solutions ps pt pairs'''
)

# 6. Wire eval_subselect_fwd_ref after eval_select_query is defined
content = content.replace(
    'let is_not_literal',
    '''(* Wire up eval_subselect_fwd to the real eval_select_query *)
let () = eval_subselect_fwd_ref := eval_select_query

let is_not_literal'''
)

with open('$FILE', 'w') as f:
    f.write(content)
"

echo "  Patches applied successfully."

# ======================================================================
# SPARQL11_Parser.ml — no patches needed
# All assume vals (char_at, substring, string_upper, parse_expr, etc.)
# are now implemented directly in F* and extracted. No stubs required.
# ======================================================================
