open Prims
let dir_suffix (d : RDF_Term.text_direction FStar_Pervasives_Native.option) :
  Prims.string=
  match d with
  | FStar_Pervasives_Native.Some (RDF_Term.Dir_LTR) -> "--ltr"
  | FStar_Pervasives_Native.Some (RDF_Term.Dir_RTL) -> "--rtl"
  | FStar_Pervasives_Native.None -> ""
let rec term_to_ntriples (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> Prims.strcat "<" (Prims.strcat i ">")
  | RDF_Term.T_BNode b -> Prims.strcat "_:" b
  | RDF_Term.T_Literal l ->
      (match l.RDF_Term.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           Prims.strcat "\""
             (Prims.strcat l.RDF_Term.lexical_form
                (Prims.strcat "\"@"
                   (Prims.strcat tag (dir_suffix l.RDF_Term.direction))))
       | FStar_Pervasives_Native.None ->
           if l.RDF_Term.datatype = RDF_Term.xsd_string
           then Prims.strcat "\"" (Prims.strcat l.RDF_Term.lexical_form "\"")
           else
             Prims.strcat "\""
               (Prims.strcat l.RDF_Term.lexical_form
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
                    (Prims.strcat (term_to_ntriples o) " )>>")))))
type prefix_table = (Prims.string * Prims.string) Prims.list
let starts_with_strict (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  let pl = FStar_String.strlen pfx in
  let sl = FStar_String.strlen s in
  if sl > pl then (FStar_String.sub s Prims.int_zero pl) = pfx else false
let rec find_prefix (table : prefix_table) (iri : Prims.string) :
  (Prims.string * Prims.string) FStar_Pervasives_Native.option=
  match table with
  | [] -> FStar_Pervasives_Native.None
  | (ns, abbr)::rest ->
      if starts_with_strict iri ns
      then FStar_Pervasives_Native.Some (ns, abbr)
      else find_prefix rest iri
let abbreviate_iri (table : prefix_table) (iri : Prims.string) :
  Prims.string=
  match find_prefix table iri with
  | FStar_Pervasives_Native.Some (ns, abbr) ->
      let nsl = FStar_String.strlen ns in
      let il = FStar_String.strlen iri in
      if nsl < il
      then Prims.strcat abbr (FStar_String.sub iri nsl (il - nsl))
      else Prims.strcat "<" (Prims.strcat iri ">")
  | FStar_Pervasives_Native.None -> Prims.strcat "<" (Prims.strcat iri ">")
let rec term_with_prefixes (table : prefix_table) (t : RDF_Term.rdf_term) :
  Prims.string=
  match t with
  | RDF_Term.T_IRI i -> abbreviate_iri table i
  | RDF_Term.T_BNode b -> Prims.strcat "_:" b
  | RDF_Term.T_Literal l ->
      (match l.RDF_Term.lang_tag with
       | FStar_Pervasives_Native.Some tag ->
           Prims.strcat "\""
             (Prims.strcat l.RDF_Term.lexical_form
                (Prims.strcat "\"@"
                   (Prims.strcat tag (dir_suffix l.RDF_Term.direction))))
       | FStar_Pervasives_Native.None ->
           if l.RDF_Term.datatype = RDF_Term.xsd_string
           then Prims.strcat "\"" (Prims.strcat l.RDF_Term.lexical_form "\"")
           else
             Prims.strcat "\""
               (Prims.strcat l.RDF_Term.lexical_form
                  (Prims.strcat "\"^^<"
                     (Prims.strcat l.RDF_Term.datatype ">"))))
  | RDF_Term.T_TripleTerm (s, p, o) ->
      let subj_str =
        match s with
        | RDF_Term.S_IRI i -> abbreviate_iri table i
        | RDF_Term.S_BNode b -> Prims.strcat "_:" b in
      Prims.strcat "<<( "
        (Prims.strcat subj_str
           (Prims.strcat " <"
              (Prims.strcat p
                 (Prims.strcat "> "
                    (Prims.strcat (term_with_prefixes table o) " )>>")))))
let subject_with_prefixes (table : prefix_table) (s : RDF_Term.subject) :
  Prims.string=
  match s with
  | RDF_Term.S_IRI i -> abbreviate_iri table i
  | RDF_Term.S_BNode b -> Prims.strcat "_:" b
let cli_turtle_prefixes : prefix_table=
  [("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#", "xsd:");
  ("http://www.w3.org/2002/07/owl#", "owl:");
  ("http://xmlns.com/foaf/0.1/", "foaf:");
  ("http://purl.org/dc/terms/", "dcterms:");
  ("http://purl.org/dc/elements/1.1/", "dc:");
  ("http://schema.org/", "schema:")]
let explain_prefixes : prefix_table=
  [("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:");
  ("http://www.w3.org/2000/01/rdf-schema#", "rdfs:");
  ("http://www.w3.org/2001/XMLSchema#", "xsd:");
  ("http://www.w3.org/2002/07/owl#", "owl:");
  ("http://www.opengis.net/ont/geosparql#", "geo:");
  ("https://id.parliament.uk/schema/", ":")]
let term_to_turtle (t : RDF_Term.rdf_term) : Prims.string=
  term_with_prefixes cli_turtle_prefixes t
let subject_to_turtle (s : RDF_Term.subject) : Prims.string=
  subject_with_prefixes cli_turtle_prefixes s
let term_short_explain (t : RDF_Term.rdf_term) : Prims.string=
  term_with_prefixes explain_prefixes t
let pattern_term_short (table : prefix_table)
  (pt : SPARQL11_Algebra.pattern_term) : Prims.string=
  match pt with
  | SPARQL11_Algebra.PT_Var v -> Prims.strcat "?" v
  | SPARQL11_Algebra.PT_IRI i -> abbreviate_iri table i
  | SPARQL11_Algebra.PT_BNode b -> Prims.strcat "_:" b
  | SPARQL11_Algebra.PT_Literal l ->
      term_with_prefixes table (RDF_Term.T_Literal l)
let pattern_subject_short (table : prefix_table)
  (ps : SPARQL11_Algebra.pattern_subject) : Prims.string=
  match ps with
  | SPARQL11_Algebra.PS_Var v -> Prims.strcat "?" v
  | SPARQL11_Algebra.PS_IRI i -> abbreviate_iri table i
  | SPARQL11_Algebra.PS_BNode b -> Prims.strcat "_:" b
let triple_pattern_short (table : prefix_table)
  (tp : SPARQL11_Algebra.triple_pattern) : Prims.string=
  Prims.strcat (pattern_subject_short table tp.SPARQL11_Algebra.tp_s)
    (Prims.strcat " "
       (Prims.strcat (pattern_term_short table tp.SPARQL11_Algebra.tp_p)
          (Prims.strcat " "
             (pattern_term_short table tp.SPARQL11_Algebra.tp_o))))
let pattern_term_short_explain (pt : SPARQL11_Algebra.pattern_term) :
  Prims.string= pattern_term_short explain_prefixes pt
let pattern_subject_short_explain (ps : SPARQL11_Algebra.pattern_subject) :
  Prims.string= pattern_subject_short explain_prefixes ps
let triple_pattern_short_explain (tp : SPARQL11_Algebra.triple_pattern) :
  Prims.string= triple_pattern_short explain_prefixes tp
