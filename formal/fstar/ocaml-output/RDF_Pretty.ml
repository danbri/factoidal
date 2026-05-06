open Prims
let (term_to_ntriples : RDF_Graph_Executable.rdf_term -> Prims.string) =
  fun t ->
    match t with
    | RDF_Graph_Executable.T_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
    | RDF_Graph_Executable.T_BNode b -> Prims.strcat "_:" b
    | RDF_Graph_Executable.T_Literal l ->
        (match l.RDF_Graph_Executable.lang_tag with
         | FStar_Pervasives_Native.Some tag ->
             Prims.strcat "\""
               (Prims.strcat l.RDF_Graph_Executable.lexical_form
                  (Prims.strcat "\"@" tag))
         | FStar_Pervasives_Native.None ->
             if
               l.RDF_Graph_Executable.datatype =
                 RDF_Graph_Executable.xsd_string
             then
               Prims.strcat "\""
                 (Prims.strcat l.RDF_Graph_Executable.lexical_form "\"")
             else
               Prims.strcat "\""
                 (Prims.strcat l.RDF_Graph_Executable.lexical_form
                    (Prims.strcat "\"^^<"
                       (Prims.strcat l.RDF_Graph_Executable.datatype ">"))))
type prefix_table = (Prims.string * Prims.string) Prims.list
let (starts_with_strict : Prims.string -> Prims.string -> Prims.bool) =
  fun s ->
    fun pfx ->
      let pl = FStar_String.strlen pfx in
      let sl = FStar_String.strlen s in
      if sl > pl then (FStar_String.sub s Prims.int_zero pl) = pfx else false
let rec (find_prefix :
  prefix_table ->
    Prims.string ->
      (Prims.string * Prims.string) FStar_Pervasives_Native.option)
  =
  fun table ->
    fun iri ->
      match table with
      | [] -> FStar_Pervasives_Native.None
      | (ns, abbr)::rest ->
          if starts_with_strict iri ns
          then FStar_Pervasives_Native.Some (ns, abbr)
          else find_prefix rest iri
let (abbreviate_iri : prefix_table -> Prims.string -> Prims.string) =
  fun table ->
    fun iri ->
      match find_prefix table iri with
      | FStar_Pervasives_Native.Some (ns, abbr) ->
          let nsl = FStar_String.strlen ns in
          let il = FStar_String.strlen iri in
          if nsl < il
          then Prims.strcat abbr (FStar_String.sub iri nsl (il - nsl))
          else Prims.strcat "<" (Prims.strcat iri ">")
      | FStar_Pervasives_Native.None ->
          Prims.strcat "<" (Prims.strcat iri ">")
let (term_with_prefixes :
  prefix_table -> RDF_Graph_Executable.rdf_term -> Prims.string) =
  fun table ->
    fun t ->
      match t with
      | RDF_Graph_Executable.T_IRI i -> abbreviate_iri table i
      | RDF_Graph_Executable.T_BNode b -> Prims.strcat "_:" b
      | RDF_Graph_Executable.T_Literal l ->
          (match l.RDF_Graph_Executable.lang_tag with
           | FStar_Pervasives_Native.Some tag ->
               Prims.strcat "\""
                 (Prims.strcat l.RDF_Graph_Executable.lexical_form
                    (Prims.strcat "\"@" tag))
           | FStar_Pervasives_Native.None ->
               if
                 l.RDF_Graph_Executable.datatype =
                   RDF_Graph_Executable.xsd_string
               then
                 Prims.strcat "\""
                   (Prims.strcat l.RDF_Graph_Executable.lexical_form "\"")
               else
                 Prims.strcat "\""
                   (Prims.strcat l.RDF_Graph_Executable.lexical_form
                      (Prims.strcat "\"^^<"
                         (Prims.strcat l.RDF_Graph_Executable.datatype ">"))))
let (subject_with_prefixes :
  prefix_table -> RDF_Graph_Executable.subject -> Prims.string) =
  fun table ->
    fun s ->
      match s with
      | RDF_Graph_Executable.S_IRI i -> abbreviate_iri table i
      | RDF_Graph_Executable.S_BNode b -> Prims.strcat "_:" b
let (cli_turtle_prefixes : prefix_table) =
  [("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#", "xsd:");
  ("http://www.w3.org/2002/07/owl#", "owl:");
  ("http://xmlns.com/foaf/0.1/", "foaf:");
  ("http://purl.org/dc/terms/", "dcterms:");
  ("http://purl.org/dc/elements/1.1/", "dc:");
  ("http://schema.org/", "schema:")]
let (explain_prefixes : prefix_table) =
  [("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#", "xsd:");
  ("http://www.w3.org/2002/07/owl#", "owl:");
  ("http://www.opengis.net/ont/geosparql#", "geo:");
  ("https://id.parliament.uk/schema/", ":")]
let (term_to_turtle : RDF_Graph_Executable.rdf_term -> Prims.string) =
  fun t -> term_with_prefixes cli_turtle_prefixes t
let (subject_to_turtle : RDF_Graph_Executable.subject -> Prims.string) =
  fun s -> subject_with_prefixes cli_turtle_prefixes s
let (term_short_explain : RDF_Graph_Executable.rdf_term -> Prims.string) =
  fun t -> term_with_prefixes explain_prefixes t
let (pattern_term_short :
  prefix_table -> SPARQL11_Algebra.pattern_term -> Prims.string) =
  fun table ->
    fun pt ->
      match pt with
      | SPARQL11_Algebra.PT_Var v -> Prims.strcat "?" v
      | SPARQL11_Algebra.PT_IRI i -> abbreviate_iri table i
      | SPARQL11_Algebra.PT_BNode b -> Prims.strcat "_:" b
      | SPARQL11_Algebra.PT_Literal l ->
          term_with_prefixes table (RDF_Graph_Executable.T_Literal l)
let (pattern_subject_short :
  prefix_table -> SPARQL11_Algebra.pattern_subject -> Prims.string) =
  fun table ->
    fun ps ->
      match ps with
      | SPARQL11_Algebra.PS_Var v -> Prims.strcat "?" v
      | SPARQL11_Algebra.PS_IRI i -> abbreviate_iri table i
      | SPARQL11_Algebra.PS_BNode b -> Prims.strcat "_:" b
let (triple_pattern_short :
  prefix_table -> SPARQL11_Algebra.triple_pattern -> Prims.string) =
  fun table ->
    fun tp ->
      Prims.strcat (pattern_subject_short table tp.SPARQL11_Algebra.tp_s)
        (Prims.strcat " "
           (Prims.strcat (pattern_term_short table tp.SPARQL11_Algebra.tp_p)
              (Prims.strcat " "
                 (pattern_term_short table tp.SPARQL11_Algebra.tp_o))))
let (pattern_term_short_explain :
  SPARQL11_Algebra.pattern_term -> Prims.string) =
  fun pt -> pattern_term_short explain_prefixes pt
let (pattern_subject_short_explain :
  SPARQL11_Algebra.pattern_subject -> Prims.string) =
  fun ps -> pattern_subject_short explain_prefixes ps
let (triple_pattern_short_explain :
  SPARQL11_Algebra.triple_pattern -> Prims.string) =
  fun tp -> triple_pattern_short explain_prefixes tp
