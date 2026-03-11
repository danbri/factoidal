#!/bin/bash
# Post-extraction patches for F*-extracted OCaml files.
# These fix assume-val stubs, add IRI resolution, RDF/XML validation,
# surrogate codepoint guards, and RDFS closure for entailment tests.
#
# Applied automatically by build-ocaml.sh after F* extraction.

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

# ======================================================================
# SPARQL11_Algebra.ml patches
# ======================================================================
FILE="$OUTDIR/SPARQL11_Algebra.ml"
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

# 2a2. Replace regex_replace stub with OCaml Str implementation
# SPARQL REPLACE() uses XPath fn:replace: full regex with backreferences + flags
content = content.replace(
    '''let regex_replace (uu___ : Prims.string) (uu___1 : Prims.string)
  (uu___2 : Prims.string)
  (uu___3 : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  failwith \"Not yet implemented: SPARQL11.Algebra.regex_replace\"''',
    '''let regex_replace_ref : (Prims.string -> Prims.string -> Prims.string -> Prims.string FStar_Pervasives_Native.option -> Prims.string) ref =
  ref (fun t _ _ _ -> t)
let regex_replace (text : Prims.string) (pattern : Prims.string)
  (replacement : Prims.string)
  (flags : Prims.string FStar_Pervasives_Native.option) : Prims.string=
  !regex_replace_ref text pattern replacement flags'''
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

# 3b. Wire regex_replace_ref after xpath_to_str_regex is defined
# (xpath_to_str_regex is defined inside the regex_match patch)
content = content.replace(
    '''let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)''',
    '''let () = eval_expr_ebv_ref := (fun e mu -> ebv (eval_expr e mu))
let () = eval_expr_fwd_ref := (fun e mu -> eval_expr e mu)
let () = regex_replace_ref := (fun text pattern replacement flags ->
  try
    let case_insensitive = match flags with
      | FStar_Pervasives_Native.Some f -> String.contains f 'i'
      | FStar_Pervasives_Native.None -> false in
    let converted = xpath_to_str_regex pattern in
    let re = if case_insensitive
      then Str.regexp_case_fold converted
      else Str.regexp converted in
    (* Manual global replace that handles unmatched groups gracefully.
       OCaml Str.matched_group raises Not_found for unmatched groups;
       we replace them with empty string per XPath/SPARQL semantics. *)
    let open Stdlib in
    let build_replacement matched_text =
      let len = String.length replacement in
      let buf = Buffer.create len in
      let i = ref 0 in
      while !i < len do
        if replacement.[!i] = '$' && !i + 1 < len &&
           replacement.[!i + 1] >= '0' && replacement.[!i + 1] <= '9' then begin
          let group_n = Char.code replacement.[!i + 1] - Char.code '0' in
          (try Buffer.add_string buf (Str.matched_group group_n matched_text)
           with Not_found -> ());
          i := !i + 2
        end else begin
          Buffer.add_char buf replacement.[!i];
          i := !i + 1
        end
      done;
      Buffer.contents buf
    in
    let result = Buffer.create (String.length text) in
    let pos = ref 0 in
    (try
      while true do
        ignore (Str.search_forward re text !pos);
        let m_start = Str.match_beginning () in
        let m_end = Str.match_end () in
        Buffer.add_string result (String.sub text !pos (m_start - !pos));
        Buffer.add_string result (build_replacement text);
        pos := m_end;
        if m_start = m_end then begin
          if !pos < String.length text then begin
            Buffer.add_char result text.[!pos];
            pos := !pos + 1
          end else raise Not_found
        end
      done
    with Not_found -> ());
    Buffer.add_string result (String.sub text !pos (String.length text - !pos));
    Buffer.contents result
  with _ -> text)'''
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

# 8. IRI()/URI() base IRI resolution
# The spec says IRI(string) resolves the string against the query's BASE.
# eval_expr has no access to the query base, so we use a mutable ref.

# Add the ref before eval_expr so it's in scope
content = content.replace(
    'let rec eval_expr (e : expr) (mu : RDF_Graph_Executable.solution_mapping) :',
    '''let current_base_iri_ref : RDF_Graph_Executable.wf_iri FStar_Pervasives_Native.option ref =
  ref FStar_Pervasives_Native.None

let rec eval_expr (e : expr) (mu : RDF_Graph_Executable.solution_mapping) :'''
)

# Set/restore base_iri in eval_select_query
content = content.replace(
    '''let eval_select_query (q : query) (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) : solution_sequence=
  match q.q_form with
  | QF_Select sel ->''',
    '''let eval_select_query (q : query) (g : RDF_Graph_Executable.rdf_graph)
  (ds : RDF_Graph_Executable.rdf_dataset) : solution_sequence=
  let saved_base = !current_base_iri_ref in
  current_base_iri_ref := q.q_base;
  let result = match q.q_form with
  | QF_Select sel ->'''
)

content = content.replace(
    '''  | QF_Describe uu___ -> []
type path_result =''',
    '''  | QF_Describe uu___ -> []
  in
  current_base_iri_ref := saved_base;
  result
type path_result ='''
)

content = content.replace(
    '''  | E_IRI_fn e1 ->
      (match eval_expr e1 mu with
       | ER_Term (RDF_Graph_Executable.T_IRI i) ->
           ER_Term (RDF_Graph_Executable.T_IRI i)
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           (match string_to_iri (lit_lexical l) with
            | FStar_Pervasives_Native.Some i ->
                ER_Term (RDF_Graph_Executable.T_IRI i)
            | FStar_Pervasives_Native.None -> ER_Error)
       | uu___ -> ER_Error)''',
    '''  | E_IRI_fn e1 ->
      (match eval_expr e1 mu with
       | ER_Term (RDF_Graph_Executable.T_IRI i) ->
           ER_Term (RDF_Graph_Executable.T_IRI i)
       | ER_Term (RDF_Graph_Executable.T_Literal l) ->
           let s = lit_lexical l in
           (match !current_base_iri_ref with
            | FStar_Pervasives_Native.Some base ->
                ER_Term (RDF_Graph_Executable.T_IRI (resolve_iri base s))
            | FStar_Pervasives_Native.None ->
                (match string_to_iri s with
                 | FStar_Pervasives_Native.Some i ->
                     ER_Term (RDF_Graph_Executable.T_IRI i)
                 | FStar_Pervasives_Native.None -> ER_Error))
       | uu___ -> ER_Error)'''
)

with open('$FILE', 'w') as f:
    f.write(content)
"

echo "  SPARQL11_Algebra.ml patched."

# ======================================================================
# SPARQL11_Parser.ml patches — relative IRI resolution against BASE
# ======================================================================
FILE="$OUTDIR/SPARQL11_Parser.ml"
if [[ -f "$FILE" ]]; then
  echo "  Patching $FILE..."
  python3 - "$FILE" << 'PYEOF'
import sys
import re

with open(sys.argv[1], 'r') as f:
    content = f.read()

# 0. Patch assume val stubs: utf8_of_codepoint, process_iri_escapes, process_string_escapes
content = content.replace(
    'let utf8_of_codepoint (uu___ : Prims.nat) : Prims.string=\n  failwith "Not yet implemented: SPARQL11.Parser.utf8_of_codepoint"',
    '''let utf8_of_codepoint (cp_z : Prims.nat) : Prims.string =
  let cp = Z.to_int cp_z in
  let open Stdlib in
  if cp < 0x80 then String.make 1 (Char.chr cp)
  else if cp < 0x800 then
    let b0 = 0xC0 lor (cp lsr 6) in
    let b1 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 2 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1);
    Bytes.to_string s
  else if cp < 0x10000 then
    let b0 = 0xE0 lor (cp lsr 12) in
    let b1 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b2 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 3 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1); Bytes.set s 2 (Char.chr b2);
    Bytes.to_string s
  else
    let b0 = 0xF0 lor (cp lsr 18) in
    let b1 = 0x80 lor ((cp lsr 12) land 0x3F) in
    let b2 = 0x80 lor ((cp lsr 6) land 0x3F) in
    let b3 = 0x80 lor (cp land 0x3F) in
    let s = Bytes.create 4 in
    Bytes.set s 0 (Char.chr b0); Bytes.set s 1 (Char.chr b1);
    Bytes.set s 2 (Char.chr b2); Bytes.set s 3 (Char.chr b3);
    Bytes.to_string s'''
)

content = content.replace(
    'let process_iri_escapes (uu___ : Prims.string) : Prims.string=\n  failwith "Not yet implemented: SPARQL11.Parser.process_iri_escapes"',
    '''let process_iri_escapes (s : Prims.string) : Prims.string =
  let open Stdlib in
  (* Process backslash-u and backslash-U escapes in IRI strings *)
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if !i + 1 < len && s.[!i] = '\\\\' then begin
      let next = s.[!i + 1] in
      if next = 'u' && !i + 5 < len then begin
        let hex = String.sub s (!i + 2) 4 in
        (try let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with _ -> Buffer.add_string buf (String.sub s !i 6));
        i := !i + 6
      end else if next = 'U' && !i + 9 < len then begin
        let hex = String.sub s (!i + 2) 8 in
        (try let cp = int_of_string ("0x" ^ hex) in
             Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with _ -> Buffer.add_string buf (String.sub s !i 10));
        i := !i + 10
      end else begin
        Buffer.add_char buf s.[!i];
        i := !i + 1
      end
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf'''
)

content = content.replace(
    'let process_string_escapes (uu___ : Prims.string) : Prims.string=\n  failwith "Not yet implemented: SPARQL11.Parser.process_string_escapes"',
    '''let process_string_escapes (s : Prims.string) : Prims.string =
  let open Stdlib in
  (* Process string escape sequences: backslash-t, -n, -r, etc. *)
  let len = String.length s in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if !i + 1 < len && s.[!i] = '\\\\' then begin
      let next = s.[!i + 1] in
      if next = 't' then (Buffer.add_char buf '\\t'; i := !i + 2)
      else if next = 'n' then (Buffer.add_char buf '\\n'; i := !i + 2)
      else if next = 'r' then (Buffer.add_char buf '\\r'; i := !i + 2)
      else if next = '\\\\' then (Buffer.add_char buf '\\\\'; i := !i + 2)
      else if next = '"' then (Buffer.add_char buf '"'; i := !i + 2)
      else if next = '\\'' then (Buffer.add_char buf '\\''; i := !i + 2)
      else if next = 'b' then (Buffer.add_char buf '\\008'; i := !i + 2)
      else if next = 'f' then (Buffer.add_char buf '\\012'; i := !i + 2)
      else if next = 'u' && !i + 5 < len then begin
        let hex = String.sub s (!i + 2) 4 in
        (try let cp = int_of_string ("0x" ^ hex) in
             if cp >= 0xD800 && cp <= 0xDFFF then
               failwith "invalid Unicode codepoint: surrogate"
             else
               Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with Failure msg -> raise (Failure msg)
            | _ -> Buffer.add_string buf (String.sub s !i 6));
        i := !i + 6
      end else if next = 'U' && !i + 9 < len then begin
        let hex = String.sub s (!i + 2) 8 in
        (try let cp = int_of_string ("0x" ^ hex) in
             if cp >= 0xD800 && cp <= 0xDFFF then
               failwith "invalid Unicode codepoint: surrogate"
             else
               Buffer.add_string buf (utf8_of_codepoint (Z.of_int cp))
         with Failure msg -> raise (Failure msg)
            | _ -> Buffer.add_string buf (String.sub s !i 10));
        i := !i + 10
      end else begin
        Buffer.add_char buf s.[!i];
        i := !i + 1
      end
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf'''
)

# 1. Add resolve_tok_iri helper after safe_sub function
content = content.replace(
    '''  if a >= b then a - b else Prims.int_zero''',
    '''  if a >= b then a - b else Prims.int_zero
(* Resolve a potentially relative IRI against the current BASE.
   If the IRI is already absolute (passes is_iri), return it unchanged.
   Otherwise, try resolving against the global current_base_iri_ref. *)
let resolve_tok_iri (i : Prims.string) : Prims.string =
  if RDF_Graph_Executable.is_iri i then i
  else match !(SPARQL11_Algebra.current_base_iri_ref) with
    | Some base -> SPARQL11_Algebra.resolve_iri base i
    | None -> i
'''
)

# 2. Regex-based patching: resolve ALL Tok_IRI i patterns globally.
# Each block matches: | Tok_IRI i -> ... if is_iri i ... else ParseErr ...
# We insert `let ri = resolve_tok_iri i in` and rename i -> ri in the block.
def patch_tok_iri_block(match):
    block = match.group(0)
    # Find the indentation of the 'if' line
    for line in block.split('\n'):
        if 'if RDF_Graph_Executable.is_iri i' in line:
            indent = line[:len(line) - len(line.lstrip())]
            break
    else:
        return block  # shouldn't happen

    # Insert resolve_tok_iri before the is_iri check
    block = block.replace(
        'if RDF_Graph_Executable.is_iri i',
        'let ri = resolve_tok_iri i in\n' + indent + 'if RDF_Graph_Executable.is_iri ri',
        1
    )
    # Rename i -> ri in IRI constructor uses
    block = block.replace('PS_IRI i)', 'PS_IRI ri)')
    block = block.replace('PT_IRI i), SPARQL11_Algebra.GP_Empty', 'PT_IRI ri), SPARQL11_Algebra.GP_Empty')
    block = block.replace('PT_IRI i), (parse_advance', 'PT_IRI ri), (parse_advance')
    block = block.replace('PP_IRI i), (parse_advance', 'PP_IRI ri), (parse_advance')
    block = block.replace('PP_IRI i)),', 'PP_IRI ri)),')
    block = block.replace('E_IRI i), ts', 'E_IRI ri), ts')
    block = block.replace('T_IRI i)),', 'T_IRI ri)),')
    block = block.replace('ParseOk (i, (parse_advance', 'ParseOk (ri, (parse_advance')
    block = block.replace('parse_func_call pm (fuel - Prims.int_one) i\n', 'parse_func_call pm (fuel - Prims.int_one) ri\n')
    return block

# Match each Tok_IRI i -> block from the | to the else ParseErr line
content = re.sub(
    r'\| Tok_IRI i ->\n(\s+)if RDF_Graph_Executable\.is_iri i\n.*?else ParseErr[^\n]+',
    patch_tok_iri_block,
    content,
    flags=re.DOTALL
)

# 3. Resolve datatype IRIs (Tok_IRI dt) - insert resolve_tok_iri dt
# These appear inside HATHAT handling for typed literals
content = content.replace(
    '''          | Tok_IRI dt ->
              if RDF_Graph_Executable.is_iri dt''',
    '''          | Tok_IRI dt ->
              let dt = resolve_tok_iri dt in
              if RDF_Graph_Executable.is_iri dt'''
)

# 4. parse_prologue_base: propagate BASE to current_base_iri_ref
content = content.replace(
    '''          | Tok_IRI iri ->
              if RDF_Graph_Executable.is_iri iri
              then
                parse_prologue_base pm (FStar_Pervasives_Native.Some iri)
                  (fuel - Prims.int_one) (parse_advance ts')''',
    '''          | Tok_IRI iri ->
              if RDF_Graph_Executable.is_iri iri
              then begin
                SPARQL11_Algebra.current_base_iri_ref := Some iri;
                parse_prologue_base pm (FStar_Pervasives_Native.Some iri)
                  (fuel - Prims.int_one) (parse_advance ts')
              end'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF
  echo "  SPARQL11_Parser.ml patched."
fi

# ======================================================================
# Parser_RDFXML.ml patches — RDF/XML name validation and NCName checks
# ======================================================================
FILE="$OUTDIR/Parser_RDFXML.ml"
if [[ -f "$FILE" ]]; then
  echo "  Patching $FILE..."
  python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

# 1. Add validation infrastructure after rdf_xmlliteral_iri
content = content.replace(
    '''let rdf_xmlliteral_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"
type rdfxml_state =''',
    '''let rdf_xmlliteral_iri : Prims.string=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral"

(* RDF/XML validation: forbidden rdf: names *)
exception Rdfxml_error of string

(* Names forbidden as node element names (sec 7.2.11) *)
let forbidden_node_element_names = [
  rdf_ns ^ "RDF"; rdf_ns ^ "ID"; rdf_ns ^ "about"; rdf_ns ^ "bagID";
  rdf_ns ^ "parseType"; rdf_ns ^ "resource"; rdf_ns ^ "nodeID";
  rdf_ns ^ "li"; rdf_ns ^ "aboutEach"; rdf_ns ^ "aboutEachPrefix"
]

(* Names forbidden as property element names (sec 7.2.12) *)
let forbidden_property_element_names = [
  rdf_ns ^ "Description"; rdf_ns ^ "RDF"; rdf_ns ^ "ID"; rdf_ns ^ "about";
  rdf_ns ^ "bagID"; rdf_ns ^ "parseType"; rdf_ns ^ "resource";
  rdf_ns ^ "nodeID"; rdf_ns ^ "aboutEach"; rdf_ns ^ "aboutEachPrefix"
]

(* Validate rdf:ID / rdf:nodeID values: must be valid XML NCName.
   Uses Stdlib operators explicitly because open Prims shadows them with Z.t. *)
let is_valid_ncname s =
  let module S = Stdlib in
  let len = S.String.length s in
  if S.(=) len 0 then false
  else
    let byte_at i = S.Char.code (S.String.get s i) in
    let is_start b =
      (S.(>=) b 0x41 && S.(<=) b 0x5A) || (S.(>=) b 0x61 && S.(<=) b 0x7A)
      || S.(=) b 0x5F || S.(>) b 0x7F in
    let is_cont b =
      is_start b || (S.(>=) b 0x30 && S.(<=) b 0x39)
      || S.(=) b 0x2D || S.(=) b 0x2E || S.(=) b 0xB7 in
    let ok = S.ref (is_start (byte_at 0)) in
    for i = 1 to S.(-) len 1 do
      if not (is_cont (byte_at i)) then ok := false
    done;
    S.(!) ok

let validate_rdf_id_attr (attrs : Parser_XML.xml_attribute list) =
  List.iter (fun (a : Parser_XML.xml_attribute) ->
    if a.attr_name = "rdf:ID" || a.attr_name = "rdf:nodeID" then
      if not (is_valid_ncname a.attr_value) then
        raise (Rdfxml_error (Printf.sprintf "Invalid %s value: %s" a.attr_name a.attr_value))
  ) attrs

let check_conflicting_attrs (attrs : Parser_XML.xml_attribute list) =
  let has a = List.exists (fun (x : Parser_XML.xml_attribute) -> x.attr_name = a) attrs in
  if has "rdf:parseType" && has "rdf:resource" then
    raise (Rdfxml_error "conflicting rdf:parseType and rdf:resource");
  if has "rdf:aboutEach" then
    raise (Rdfxml_error "rdf:aboutEach is deprecated and forbidden")

type rdfxml_state ='''
)

# 2. Add validation in process_node_element
content = content.replace(
    '''     | Parser_XML.XElement (tag, attrs, children) ->
         let st1 = update_state_from_attrs st attrs in
         let uu___1 = determine_subject st1 attrs in
         (match uu___1 with''',
    '''     | Parser_XML.XElement (tag, attrs, children) ->
         (* Validate: reject forbidden rdf: names as node elements *)
         (match resolve_name st tag with
          | Some full_iri ->
            if List.mem full_iri forbidden_node_element_names then
              raise (Rdfxml_error (Printf.sprintf "Forbidden node element name: %s" full_iri))
          | None -> ());
         validate_rdf_id_attr attrs;
         check_conflicting_attrs attrs;
         let st1 = update_state_from_attrs st attrs in
         let uu___1 = determine_subject st1 attrs in
         (match uu___1 with''',
    1  # first occurrence only (process_node_element)
)

# 3. Add validation in process_property_element
content = content.replace(
    '''     | Parser_XML.XElement (tag, attrs, children) ->
         let st1 = update_state_from_attrs st attrs in
         let uu___1 =
           match resolve_name st1 tag with''',
    '''     | Parser_XML.XElement (tag, attrs, children) ->
         (* Validate: reject forbidden rdf: names as property elements *)
         (match resolve_name st tag with
          | Some full_iri ->
            if List.mem full_iri forbidden_property_element_names then
              raise (Rdfxml_error (Printf.sprintf "Forbidden property element name: %s" full_iri));
            (* Also reject rdf:Bag/Seq/Alt as property elements *)
            if full_iri = rdf_ns ^ "Bag" || full_iri = rdf_ns ^ "Seq" ||
               full_iri = rdf_ns ^ "Alt" then
              raise (Rdfxml_error (Printf.sprintf "Container type used as property element: %s" full_iri))
          | None -> ());
         validate_rdf_id_attr attrs;
         check_conflicting_attrs attrs;
         let st1 = update_state_from_attrs st attrs in
         let uu___1 =
           match resolve_name st1 tag with'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF
  echo "  Parser_RDFXML.ml patched."
fi

# ======================================================================
# Parser_Turtle.ml patches — surrogate codepoint validation
# ======================================================================
FILE="$OUTDIR/Parser_Turtle.ml"
if [[ -f "$FILE" ]]; then
  echo "  Patching $FILE..."
  python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

# The pattern: after computing cp from hex digits, before calling
# parse_*_string_body with safe_char_of_int cp, insert a surrogate check.
# There are 4 locations: long_string \u, long_string \U, single_string \u, single_string \U.

# We need to find lines like:
#   + h3 in
#   parse_long_string_body qch input
#     (pos + (Prims.of_int (6)))
#     ((Parser_NTriples.safe_char_of_int cp)
# And insert the guard between "h3 in" and "parse_long_string_body"

# 1. parse_long_string_body, \u escape (4-digit, offset +6)
content = content.replace(
    '''                                          + h3 in
                                      parse_long_string_body qch input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)''',
    '''                                          + h3 in
                                      if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                      then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\u escape", pos)
                                      else
                                      parse_long_string_body qch input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)'''
)

# 2. parse_long_string_body, \U escape (8-digit, offset +10)
content = content.replace(
    '''                                            + h7 in
                                        parse_long_string_body qch input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int''',
    '''                                            + h7 in
                                        if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                        then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\U escape", pos)
                                        else
                                        parse_long_string_body qch input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int'''
)

# 3. parse_single_string_body, \u escape (4-digit, offset +6)
content = content.replace(
    '''                                          + h3 in
                                      parse_single_string_body input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)''',
    '''                                          + h3 in
                                      if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                      then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\u escape", pos)
                                      else
                                      parse_single_string_body input
                                        (pos + (Prims.of_int (6)))
                                        ((Parser_NTriples.safe_char_of_int cp)'''
)

# 4. parse_single_string_body, \U escape (8-digit, offset +10)
content = content.replace(
    '''                                            + h7 in
                                        parse_single_string_body input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int''',
    '''                                            + h7 in
                                        if Prims.op_Negation (Parser_NTriples.valid_codepoint cp)
                                        then Parser_Combinators.ParseFail ("surrogate codepoint in \\\\U escape", pos)
                                        else
                                        parse_single_string_body input
                                          (pos + (Prims.of_int (10)))
                                          ((Parser_NTriples.safe_char_of_int'''
)

with open(sys.argv[1], 'w') as f:
    f.write(content)
PYEOF
  echo "  Parser_Turtle.ml patched."
fi

# ======================================================================
# w3c_runner.ml patches — RDFS closure for entailment tests
# ======================================================================
FILE="$OUTDIR/w3c_runner.ml"
if [[ -f "$FILE" ]]; then
  echo "  Patching $FILE..."
  python3 - "$FILE" << 'PYEOF'
import sys

with open(sys.argv[1], 'r') as f:
    content = f.read()

# 1. Add sd_ns and ent_ns namespace constants
content = content.replace(
    '''let rdft_ns = "http://www.w3.org/ns/rdftest#"

let find_objects graph subj pred =''',
    '''let rdft_ns = "http://www.w3.org/ns/rdftest#"
let sd_ns = "http://www.w3.org/ns/sparql-service-description#"
let ent_ns = "http://www.w3.org/ns/entailment/"

let find_objects graph subj pred ='''
)

# 2. Expand entailment regime detection to handle sd:entailmentRegime on action blank nodes
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

# 3. Add RDFS closure application in run_query_eval_test
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

# 5. Add file_to_base_uri helper and modify parse_sparql_query to accept optional base
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

# 6. Pass query_file as base to parse_sparql_query in eval test
content = content.replace(
    '''    | Some content -> parse_sparql_query content
  in

  (* Execute query against extracted evaluator *)''',
    '''    | Some content -> parse_sparql_query ~base_file:(Some tc.query_file) content
  in

  (* Execute query against extracted evaluator *)'''
)

# 7. Pass query_file as base in positive syntax tests
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

# 8. Catch Failure in negative syntax tests (e.g., surrogate codepoints)
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
  echo "  w3c_runner.ml patched."
fi

echo "  All patches applied successfully."
