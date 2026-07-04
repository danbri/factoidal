open Prims
let escape_char (c : FStar_Char.char) : Prims.string=
  let n = FStar_Char.int_of_char c in
  if n = (Prims.of_int (0x5C))
  then "\\\\"
  else
    if n = (Prims.of_int (0x22))
    then "\\\""
    else
      if n = (Prims.of_int (0x0A))
      then "\\n"
      else
        if n = (Prims.of_int (0x0D))
        then "\\r"
        else
          if n = (Prims.of_int (0x09))
          then "\\t"
          else FStar_String.string_of_list [c]
let rec escape_chars_aux (cs : FStar_Char.char Prims.list) : Prims.string=
  match cs with
  | [] -> ""
  | c::rest -> Prims.strcat (escape_char c) (escape_chars_aux rest)
let nq_escape_literal (s : Prims.string) : Prims.string=
  escape_chars_aux (FStar_String.list_of_string s)
let nq_term_to_string (t : RDF_Graph_Executable.rdf_term) : Prims.string=
  match t with
  | RDF_Graph_Executable.T_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Graph_Executable.T_BNode b -> Prims.strcat "_:" b
  | RDF_Graph_Executable.T_Literal l ->
      let esc = nq_escape_literal l.RDF_Graph_Executable.lexical_form in
      (match l.RDF_Graph_Executable.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           Prims.strcat "\"" (Prims.strcat esc (Prims.strcat "\"@" tag))
       | FStar_Pervasives_Native.None ->
           if
             l.RDF_Graph_Executable.datatype =
               RDF_Graph_Executable.xsd_string
           then Prims.strcat "\"" (Prims.strcat esc "\"")
           else
             Prims.strcat "\""
               (Prims.strcat esc
                  (Prims.strcat "\"^^<"
                     (Prims.strcat l.RDF_Graph_Executable.datatype ">"))))
let nq_subject_to_string (s : RDF_Graph_Executable.subject) : Prims.string=
  match s with
  | RDF_Graph_Executable.S_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Graph_Executable.S_BNode b -> Prims.strcat "_:" b
let nq_line_for_triple (graph_iri : Prims.string)
  (t : RDF_Graph_Executable.triple) : Prims.string=
  Prims.strcat (nq_subject_to_string t.RDF_Graph_Executable.s)
    (Prims.strcat " <"
       (Prims.strcat t.RDF_Graph_Executable.p
          (Prims.strcat "> "
             (Prims.strcat (nq_term_to_string t.RDF_Graph_Executable.o)
                (Prims.strcat " <" (Prims.strcat graph_iri "> .\n"))))))
let nq_line_for_triple_default_graph (t : RDF_Graph_Executable.triple) :
  Prims.string=
  Prims.strcat (nq_subject_to_string t.RDF_Graph_Executable.s)
    (Prims.strcat " <"
       (Prims.strcat t.RDF_Graph_Executable.p
          (Prims.strcat "> "
             (Prims.strcat (nq_term_to_string t.RDF_Graph_Executable.o)
                " .\n"))))
