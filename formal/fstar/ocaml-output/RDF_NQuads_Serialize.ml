open Prims
let nq_special_byte (b : Prims.nat) : Prims.bool=
  ((((b = (Prims.of_int (0x5C))) || (b = (Prims.of_int (0x22)))) ||
      (b = (Prims.of_int (0x0A))))
     || (b = (Prims.of_int (0x0D))))
    || (b = (Prims.of_int (0x09)))
let nq_escape_byte (b : Prims.nat) : Prims.string=
  if b = (Prims.of_int (0x5C))
  then "\\\\"
  else
    if b = (Prims.of_int (0x22))
    then "\\\""
    else
      if b = (Prims.of_int (0x0A))
      then "\\n"
      else if b = (Prims.of_int (0x0D)) then "\\r" else "\\t"
let rec nq_escape_walk (s : Prims.string) (len : Prims.nat)
  (run_start : Prims.nat) (pos : Prims.nat) (acc : Prims.string) :
  Prims.string=
  if pos >= len
  then
    (if pos > run_start
     then
       Prims.strcat acc
         (Parser_FastString.fs_byte_sub s run_start (pos - run_start))
     else acc)
  else
    (let b = Parser_FastString.fs_byte_at s pos in
     if nq_special_byte b
     then
       let run =
         if pos > run_start
         then Parser_FastString.fs_byte_sub s run_start (pos - run_start)
         else "" in
       nq_escape_walk s len (pos + Prims.int_one) (pos + Prims.int_one)
         (Prims.strcat acc (Prims.strcat run (nq_escape_byte b)))
     else nq_escape_walk s len run_start (pos + Prims.int_one) acc)
let nq_escape_literal (s : Prims.string) : Prims.string=
  nq_escape_walk s (Parser_FastString.fs_byte_length s) Prims.int_zero
    Prims.int_zero ""
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
