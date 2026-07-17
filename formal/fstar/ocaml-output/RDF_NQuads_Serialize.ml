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
let rec nq_term_to_string (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Term.T_BNode b -> Prims.strcat "_:" b
  | RDF_Term.T_Literal l ->
      let esc = nq_escape_literal l.RDF_Term.lexical_form in
      (match l.RDF_Term.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           let dir_suffix =
             match l.RDF_Term.direction with
             | FStar_Pervasives_Native.Some (RDF_Term.Dir_LTR) -> "--ltr"
             | FStar_Pervasives_Native.Some (RDF_Term.Dir_RTL) -> "--rtl"
             | FStar_Pervasives_Native.None -> "" in
           Prims.strcat "\""
             (Prims.strcat esc
                (Prims.strcat "\"@" (Prims.strcat tag dir_suffix)))
       | FStar_Pervasives_Native.None ->
           if l.RDF_Term.datatype = RDF_Term.xsd_string
           then Prims.strcat "\"" (Prims.strcat esc "\"")
           else
             Prims.strcat "\""
               (Prims.strcat esc
                  (Prims.strcat "\"^^<"
                     (Prims.strcat l.RDF_Term.datatype ">"))))
  | RDF_Term.T_TripleTerm (s, p, o) ->
      let subj_str =
        match s with
        | RDF_Term.S_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
        | RDF_Term.S_BNode b -> Prims.strcat "_:" b in
      Prims.strcat "<<( "
        (Prims.strcat subj_str
           (Prims.strcat " <"
              (Prims.strcat p
                 (Prims.strcat "> "
                    (Prims.strcat (nq_term_to_string o) " )>>")))))
let term_requires_rdf12 (t : RDF_Term.rdf_term) : Prims.bool=
  match t with
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> true
  | RDF_Term.T_Literal l ->
      FStar_Pervasives_Native.uu___is_Some l.RDF_Term.direction
  | uu___ -> false
let nq_term_to_string_mode (mode : Parser_NTriples.rdf_syntax_mode)
  (t : RDF_Term.rdf_term) : Prims.string FStar_Pervasives_Native.option=
  match mode with
  | Parser_NTriples.Mode_12 ->
      FStar_Pervasives_Native.Some (nq_term_to_string t)
  | Parser_NTriples.Mode_11 ->
      if term_requires_rdf12 t
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some (nq_term_to_string t)
let nq_subject_to_string (s : RDF_Term.subject) : Prims.string=
  match s with
  | RDF_Term.S_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Term.S_BNode b -> Prims.strcat "_:" b
let nq_line_for_triple (graph_iri : Prims.string) (t : RDF_Triple.triple) :
  Prims.string=
  Prims.strcat (nq_subject_to_string t.RDF_Triple.s)
    (Prims.strcat " <"
       (Prims.strcat t.RDF_Triple.p
          (Prims.strcat "> "
             (Prims.strcat (nq_term_to_string t.RDF_Triple.o)
                (Prims.strcat " <" (Prims.strcat graph_iri "> .\n"))))))
let nq_line_for_triple_default_graph (t : RDF_Triple.triple) : Prims.string=
  Prims.strcat (nq_subject_to_string t.RDF_Triple.s)
    (Prims.strcat " <"
       (Prims.strcat t.RDF_Triple.p
          (Prims.strcat "> "
             (Prims.strcat (nq_term_to_string t.RDF_Triple.o) " .\n"))))
