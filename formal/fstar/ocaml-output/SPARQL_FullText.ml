open Prims
let fulltext_query_pred : RDF_Term.wf_iri=
  "http://jena.apache.org/text#query"
let fulltext_args_datatype : RDF_Term.wf_iri=
  "http://jena.apache.org/text#query-args"
type fulltext_query =
  {
  ftq_field: RDF_Term.wf_iri FStar_Pervasives_Native.option ;
  ftq_terms: Prims.string ;
  ftq_limit: Prims.nat FStar_Pervasives_Native.option }
let __proj__Mkfulltext_query__item__ftq_field (projectee : fulltext_query) :
  RDF_Term.wf_iri FStar_Pervasives_Native.option=
  match projectee with | { ftq_field; ftq_terms; ftq_limit;_} -> ftq_field
let __proj__Mkfulltext_query__item__ftq_terms (projectee : fulltext_query) :
  Prims.string=
  match projectee with | { ftq_field; ftq_terms; ftq_limit;_} -> ftq_terms
let __proj__Mkfulltext_query__item__ftq_limit (projectee : fulltext_query) :
  Prims.nat FStar_Pervasives_Native.option=
  match projectee with | { ftq_field; ftq_terms; ftq_limit;_} -> ftq_limit
let is_ascii_digit (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (0x30))) && (n <= (Prims.of_int (0x39)))
let is_ascii_upper (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (0x41))) && (n <= (Prims.of_int (0x5A)))
let is_ascii_lower_char (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (0x61))) && (n <= (Prims.of_int (0x7A)))
let is_ascii_alnum (c : FStar_Char.char) : Prims.bool=
  ((is_ascii_digit c) || (is_ascii_upper c)) || (is_ascii_lower_char c)
let ascii_fold_char (c : FStar_Char.char) : FStar_Char.char=
  if is_ascii_upper c
  then
    FStar_Char.char_of_int ((FStar_Char.int_of_char c) + (Prims.of_int (32)))
  else c
let rec ascii_fold_chars (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with
  | [] -> []
  | c::rest -> (ascii_fold_char c) :: (ascii_fold_chars rest)
let ascii_lowercase (s : Prims.string) : Prims.string=
  FStar_String.string_of_list
    (ascii_fold_chars (FStar_String.list_of_string s))
let rec split_words_acc (cs : FStar_Char.char Prims.list)
  (cur : FStar_Char.char Prims.list) (acc : Prims.string Prims.list) :
  Prims.string Prims.list=
  match cs with
  | [] ->
      if (FStar_List_Tot_Base.length cur) = Prims.int_zero
      then FStar_List_Tot_Base.rev acc
      else
        FStar_List_Tot_Base.rev
          ((FStar_String.string_of_list (FStar_List_Tot_Base.rev cur)) ::
          acc)
  | c::rest ->
      if is_ascii_alnum c
      then split_words_acc rest (c :: cur) acc
      else
        if (FStar_List_Tot_Base.length cur) = Prims.int_zero
        then split_words_acc rest [] acc
        else
          split_words_acc rest []
            ((FStar_String.string_of_list (FStar_List_Tot_Base.rev cur)) ::
            acc)
let default_tokenizer (s : Prims.string) : Prims.string Prims.list=
  split_words_acc (FStar_String.list_of_string (ascii_lowercase s)) [] []
let match_tokens (query_tokens : Prims.string Prims.list)
  (candidate_tokens : Prims.string Prims.list) : Prims.bool=
  FStar_List_Tot_Base.for_all
    (fun qt -> FStar_List_Tot_Base.mem qt candidate_tokens) query_tokens
let literal_matches_query (ftq : fulltext_query) (l : RDF_Term.wf_literal) :
  Prims.bool=
  match_tokens (default_tokenizer ftq.ftq_terms)
    (default_tokenizer l.RDF_Term.lexical_form)
let unit_sep : FStar_Char.char= FStar_Char.char_of_int (Prims.of_int (31))
let unit_sep_str : Prims.string= FStar_String.string_of_list [unit_sep]
let rec split_on_char_acc (delim : FStar_Char.char)
  (cur : FStar_Char.char Prims.list) (cs : FStar_Char.char Prims.list)
  (acc : Prims.string Prims.list) : Prims.string Prims.list=
  match cs with
  | [] ->
      FStar_List_Tot_Base.rev
        ((FStar_String.string_of_list (FStar_List_Tot_Base.rev cur)) :: acc)
  | c::rest ->
      if c = delim
      then
        split_on_char_acc delim [] rest
          ((FStar_String.string_of_list (FStar_List_Tot_Base.rev cur)) ::
          acc)
      else split_on_char_acc delim (c :: cur) rest acc
let split_on_char (delim : FStar_Char.char) (s : Prims.string) :
  Prims.string Prims.list=
  split_on_char_acc delim [] (FStar_String.list_of_string s) []
let rec chars_to_int_digits (cs : FStar_Char.char Prims.list)
  (acc : Prims.int) : Prims.int=
  match cs with
  | [] -> acc
  | c::rest ->
      chars_to_int_digits rest
        ((acc * (Prims.of_int (10))) +
           ((FStar_Char.int_of_char c) - (Prims.of_int (0x30))))
let string_to_nat (s : Prims.string) :
  Prims.nat FStar_Pervasives_Native.option=
  let cs = FStar_String.list_of_string s in
  if (FStar_List_Tot_Base.length cs) = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    if FStar_List_Tot_Base.for_all is_ascii_digit cs
    then
      (let v = chars_to_int_digits cs Prims.int_zero in
       if v >= Prims.int_zero
       then FStar_Pervasives_Native.Some v
       else FStar_Pervasives_Native.None)
    else FStar_Pervasives_Native.None
let encode_fulltext_literal (ftq : fulltext_query) : RDF_Term.wf_literal=
  let field_part =
    match ftq.ftq_field with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some f -> f in
  let limit_part =
    match ftq.ftq_limit with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some n -> Prims.string_of_int n in
  let lex =
    Prims.strcat field_part
      (Prims.strcat unit_sep_str
         (Prims.strcat ftq.ftq_terms (Prims.strcat unit_sep_str limit_part))) in
  {
    RDF_Term.lexical_form = lex;
    RDF_Term.datatype = fulltext_args_datatype;
    RDF_Term.lang_tag = FStar_Pervasives_Native.None
  }
let decode_fulltext_literal (l : RDF_Term.wf_literal) :
  fulltext_query FStar_Pervasives_Native.option=
  if l.RDF_Term.datatype <> fulltext_args_datatype
  then FStar_Pervasives_Native.None
  else
    (match split_on_char unit_sep l.RDF_Term.lexical_form with
     | field_part::term::limit_part::[] ->
         let field =
           if (FStar_String.strlen field_part) = Prims.int_zero
           then FStar_Pervasives_Native.None
           else
             if RDF_Term.is_iri field_part
             then FStar_Pervasives_Native.Some field_part
             else FStar_Pervasives_Native.None in
         let limit =
           if (FStar_String.strlen limit_part) = Prims.int_zero
           then FStar_Pervasives_Native.None
           else string_to_nat limit_part in
         FStar_Pervasives_Native.Some
           { ftq_field = field; ftq_terms = term; ftq_limit = limit }
     | uu___1 -> FStar_Pervasives_Native.None)
let object_matches_query (ftq : fulltext_query) (o : RDF_Term.rdf_term) :
  Prims.bool=
  match o with
  | RDF_Term.T_Literal l -> literal_matches_query ftq l
  | uu___ -> false
