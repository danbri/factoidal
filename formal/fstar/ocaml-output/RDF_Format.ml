open Prims
type rdf_format =
  | NT 
  | Turtle 
  | NQuads 
  | TriG 
  | RDFXML 
  | JSONLD 
let uu___is_NT (projectee : rdf_format) : Prims.bool=
  match projectee with | NT -> true | uu___ -> false
let uu___is_Turtle (projectee : rdf_format) : Prims.bool=
  match projectee with | Turtle -> true | uu___ -> false
let uu___is_NQuads (projectee : rdf_format) : Prims.bool=
  match projectee with | NQuads -> true | uu___ -> false
let uu___is_TriG (projectee : rdf_format) : Prims.bool=
  match projectee with | TriG -> true | uu___ -> false
let uu___is_RDFXML (projectee : rdf_format) : Prims.bool=
  match projectee with | RDFXML -> true | uu___ -> false
let uu___is_JSONLD (projectee : rdf_format) : Prims.bool=
  match projectee with | JSONLD -> true | uu___ -> false
let rdf_format_default : rdf_format= Turtle
let format_of_extension (ext : Prims.string) :
  rdf_format FStar_Pervasives_Native.option=
  let lo = FStar_String.lowercase ext in
  if lo = ".nt"
  then FStar_Pervasives_Native.Some NT
  else
    if lo = ".ntriples"
    then FStar_Pervasives_Native.Some NT
    else
      if lo = ".ttl"
      then FStar_Pervasives_Native.Some Turtle
      else
        if lo = ".turtle"
        then FStar_Pervasives_Native.Some Turtle
        else
          if lo = ".nq"
          then FStar_Pervasives_Native.Some NQuads
          else
            if lo = ".nquads"
            then FStar_Pervasives_Native.Some NQuads
            else
              if lo = ".trig"
              then FStar_Pervasives_Native.Some TriG
              else
                if lo = ".rdf"
                then FStar_Pervasives_Native.Some RDFXML
                else
                  if lo = ".xml"
                  then FStar_Pervasives_Native.Some RDFXML
                  else
                    if lo = ".rdfxml"
                    then FStar_Pervasives_Native.Some RDFXML
                    else
                      if lo = ".owl"
                      then FStar_Pervasives_Native.Some RDFXML
                      else
                        if lo = ".jsonld"
                        then FStar_Pervasives_Native.Some JSONLD
                        else
                          if lo = ".json-ld"
                          then FStar_Pervasives_Native.Some JSONLD
                          else FStar_Pervasives_Native.None
let format_of_string (s : Prims.string) :
  rdf_format FStar_Pervasives_Native.option=
  let lo = FStar_String.lowercase s in
  if lo = "ntriples"
  then FStar_Pervasives_Native.Some NT
  else
    if lo = "nt"
    then FStar_Pervasives_Native.Some NT
    else
      if lo = "n-triples"
      then FStar_Pervasives_Native.Some NT
      else
        if lo = "turtle"
        then FStar_Pervasives_Native.Some Turtle
        else
          if lo = "ttl"
          then FStar_Pervasives_Native.Some Turtle
          else
            if lo = "nquads"
            then FStar_Pervasives_Native.Some NQuads
            else
              if lo = "nq"
              then FStar_Pervasives_Native.Some NQuads
              else
                if lo = "n-quads"
                then FStar_Pervasives_Native.Some NQuads
                else
                  if lo = "trig"
                  then FStar_Pervasives_Native.Some TriG
                  else
                    if lo = "rdfxml"
                    then FStar_Pervasives_Native.Some RDFXML
                    else
                      if lo = "rdf/xml"
                      then FStar_Pervasives_Native.Some RDFXML
                      else
                        if lo = "rdf"
                        then FStar_Pervasives_Native.Some RDFXML
                        else
                          if lo = "xml"
                          then FStar_Pervasives_Native.Some RDFXML
                          else
                            if lo = "jsonld"
                            then FStar_Pervasives_Native.Some JSONLD
                            else
                              if lo = "json-ld"
                              then FStar_Pervasives_Native.Some JSONLD
                              else
                                if lo = "application/ld+json"
                                then FStar_Pervasives_Native.Some JSONLD
                                else FStar_Pervasives_Native.None
let format_name (f : rdf_format) : Prims.string=
  match f with
  | NT -> "N-Triples"
  | Turtle -> "Turtle"
  | NQuads -> "N-Quads"
  | TriG -> "TriG"
  | RDFXML -> "RDF/XML"
  | JSONLD -> "JSON-LD (expanded form)"
let detect_format_or_default (extension : Prims.string) : rdf_format=
  match format_of_extension extension with
  | FStar_Pervasives_Native.Some f -> f
  | FStar_Pervasives_Native.None -> rdf_format_default
