open Prims
let rdf_type_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
let rdf_first_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
let rdf_rest_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
let rdf_nil_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
let rdf_json_iri : RDF_Graph_Executable.wf_iri=
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"
let rec jcanon_mantissa_all_zero (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then true
     else
       (let b = Parser_JSON.jbyte_at s pos in
        if
          (((((b = (Prims.of_int (0x2E))) || (b = (Prims.of_int (0x65)))) ||
               (b = (Prims.of_int (0x45))))
              || (b = (Prims.of_int (0x2B))))
             || (b = (Prims.of_int (0x2D))))
            || (b = (Prims.of_int (0x30)))
        then
          jcanon_mantissa_all_zero s (pos + Prims.int_one)
            (fuel - Prims.int_one)
        else false))
let rec jcanon_has_exp_marker (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then false
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then false
     else
       (let b = Parser_JSON.jbyte_at s pos in
        if (b = (Prims.of_int (0x65))) || (b = (Prims.of_int (0x45)))
        then true
        else
          jcanon_has_exp_marker s (pos + Prims.int_one)
            (fuel - Prims.int_one)))
let rec jcanon_find_dot (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then FStar_Pervasives_Native.None
     else
       if (Parser_JSON.jbyte_at s pos) = (Prims.of_int (0x2E))
       then FStar_Pervasives_Native.Some pos
       else jcanon_find_dot s (pos + Prims.int_one) (fuel - Prims.int_one))
let rec jcanon_all_zero_from (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then true
     else
       if (Parser_JSON.jbyte_at s pos) = (Prims.of_int (0x30))
       then
         jcanon_all_zero_from s (pos + Prims.int_one) (fuel - Prims.int_one)
       else false)
let jcanon_number (lexeme : Prims.string) : Prims.string=
  let n = Parser_FastString.fs_byte_length lexeme in
  if jcanon_mantissa_all_zero lexeme Prims.int_zero (n + Prims.int_one)
  then "0"
  else
    if jcanon_has_exp_marker lexeme Prims.int_zero (n + Prims.int_one)
    then lexeme
    else
      (match jcanon_find_dot lexeme Prims.int_zero (n + Prims.int_one) with
       | FStar_Pervasives_Native.None -> lexeme
       | FStar_Pervasives_Native.Some dot ->
           if jcanon_all_zero_from lexeme (dot + Prims.int_one) (n - dot)
           then Parser_FastString.fs_byte_sub lexeme Prims.int_zero dot
           else lexeme)
let jcanon_string (s : Prims.string) : Prims.string=
  FStar_String.concat "" ["\""; SPARQL_JSON_Escape.json_escape s; "\""]
let rec jcanon_insert_sorted (kv : (Prims.string * Parser_JSON.json_val))
  (xs : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match xs with
  | [] -> [kv]
  | (k2, v2)::rest ->
      if RDF_Graph_Executable.string_lt (FStar_Pervasives_Native.fst kv) k2
      then kv :: xs
      else (k2, v2) :: (jcanon_insert_sorted kv rest)
let rec jcanon_sort_fields
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) :
  (Prims.string * Parser_JSON.json_val) Prims.list=
  match fields with
  | [] -> []
  | kv::rest -> jcanon_insert_sorted kv (jcanon_sort_fields rest)
let rec jcanon_serialize (v : Parser_JSON.json_val) (fuel : Prims.nat) :
  Prims.string=
  if fuel = Prims.int_zero
  then "null"
  else
    (match v with
     | Parser_JSON.JNull -> "null"
     | Parser_JSON.JBool b -> if b then "true" else "false"
     | Parser_JSON.JNumber lex -> jcanon_number lex
     | Parser_JSON.JString s -> jcanon_string s
     | Parser_JSON.JArray items ->
         FStar_String.concat ""
           ["["; jcanon_serialize_items items (fuel - Prims.int_one); "]"]
     | Parser_JSON.JObject fields ->
         FStar_String.concat ""
           ["{";
           jcanon_serialize_fields (jcanon_sort_fields fields)
             (fuel - Prims.int_one);
           "}"])
and jcanon_serialize_items (items : Parser_JSON.json_val Prims.list)
  (fuel : Prims.nat) : Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    (match items with
     | [] -> ""
     | x::[] -> jcanon_serialize x (fuel - Prims.int_one)
     | x::rest ->
         FStar_String.concat ""
           [jcanon_serialize x (fuel - Prims.int_one);
           ",";
           jcanon_serialize_items rest (fuel - Prims.int_one)])
and jcanon_serialize_fields
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (fuel : Prims.nat) : Prims.string=
  if fuel = Prims.int_zero
  then ""
  else
    (match fields with
     | [] -> ""
     | (k, v)::[] ->
         FStar_String.concat ""
           [jcanon_string k; ":"; jcanon_serialize v (fuel - Prims.int_one)]
     | (k, v)::rest ->
         FStar_String.concat ""
           [jcanon_string k;
           ":";
           jcanon_serialize v (fuel - Prims.int_one);
           ",";
           jcanon_serialize_fields rest (fuel - Prims.int_one)])
let jcanon_document (v : Parser_JSON.json_val) : Prims.string=
  jcanon_serialize v
    (((Prims.of_int (10)) * (Parser_JSON.json_size v)) + (Prims.of_int (32)))
let jld_is_digit_byte (b : Prims.int) : Prims.bool=
  (b >= (Prims.of_int (0x30))) && (b <= (Prims.of_int (0x39)))
let jld_digit_val (b : Prims.int) : Prims.nat=
  if jld_is_digit_byte b then b - (Prims.of_int (0x30)) else Prims.int_zero
let rec jld_find_exp_pos (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat FStar_Pervasives_Native.option=
  if fuel = Prims.int_zero
  then FStar_Pervasives_Native.None
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then FStar_Pervasives_Native.None
     else
       if
         ((Parser_JSON.jbyte_at s pos) = (Prims.of_int (0x65))) ||
           ((Parser_JSON.jbyte_at s pos) = (Prims.of_int (0x45)))
       then FStar_Pervasives_Native.Some pos
       else jld_find_exp_pos s (pos + Prims.int_one) (fuel - Prims.int_one))
let rec jld_digits_to_nat (s : Prims.string) (pos : Prims.nat)
  (endpos : Prims.nat) (acc : Prims.nat) (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then acc
  else
    if pos >= endpos
    then acc
    else
      jld_digits_to_nat s (pos + Prims.int_one) endpos
        ((acc * (Prims.of_int (10))) +
           (jld_digit_val (Parser_JSON.jbyte_at s pos)))
        (fuel - Prims.int_one)
let jld_parse_exponent (s : Prims.string) (start : Prims.nat) : Prims.int=
  let n = Parser_FastString.fs_byte_length s in
  if start >= n
  then Prims.int_zero
  else
    (let b0 = Parser_JSON.jbyte_at s start in
     if b0 = (Prims.of_int (0x2B))
     then
       jld_digits_to_nat s (start + Prims.int_one) n Prims.int_zero
         ((n - start) + Prims.int_one)
     else
       if b0 = (Prims.of_int (0x2D))
       then
         -
           (jld_digits_to_nat s (start + Prims.int_one) n Prims.int_zero
              ((n - start) + Prims.int_one))
       else
         jld_digits_to_nat s start n Prims.int_zero
           ((n - start) + Prims.int_one))
let jld_number_parts (lexeme : Prims.string) :
  (Prims.bool * Prims.nat * Prims.nat * Prims.nat * Prims.nat * Prims.int)=
  let n = Parser_FastString.fs_byte_length lexeme in
  let neg =
    (n > Prims.int_zero) &&
      ((Parser_JSON.jbyte_at lexeme Prims.int_zero) = (Prims.of_int (0x2D))) in
  let start0 = if neg then Prims.int_one else Prims.int_zero in
  let dotpos = jcanon_find_dot lexeme start0 ((n - start0) + Prims.int_one) in
  let exppos = jld_find_exp_pos lexeme start0 ((n - start0) + Prims.int_one) in
  let int_end =
    match dotpos with
    | FStar_Pervasives_Native.Some d -> d
    | FStar_Pervasives_Native.None ->
        (match exppos with
         | FStar_Pervasives_Native.Some e -> e
         | FStar_Pervasives_Native.None -> n) in
  let int_len = if int_end > start0 then int_end - start0 else Prims.int_zero in
  let uu___ =
    match dotpos with
    | FStar_Pervasives_Native.Some d ->
        let fend =
          match exppos with
          | FStar_Pervasives_Native.Some e -> e
          | FStar_Pervasives_Native.None -> n in
        let flen =
          if fend > (d + Prims.int_one)
          then (fend - d) - Prims.int_one
          else Prims.int_zero in
        ((d + Prims.int_one), flen)
    | FStar_Pervasives_Native.None -> (Prims.int_zero, Prims.int_zero) in
  match uu___ with
  | (frac_start, frac_len) ->
      let exp =
        match exppos with
        | FStar_Pervasives_Native.Some e ->
            jld_parse_exponent lexeme (e + Prims.int_one)
        | FStar_Pervasives_Native.None -> Prims.int_zero in
      (neg, start0, int_len, frac_start, frac_len, exp)
let rec jld_last_nonzero_len (s : Prims.string) (pos : Prims.nat)
  (best : Prims.nat) (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then best
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then best
     else
       jld_last_nonzero_len s (pos + Prims.int_one)
         (if (Parser_JSON.jbyte_at s pos) <> (Prims.of_int (0x30))
          then pos + Prims.int_one
          else best) (fuel - Prims.int_one))
let rec jld_first_nonzero_pos (s : Prims.string) (pos : Prims.nat)
  (fuel : Prims.nat) : Prims.nat=
  if fuel = Prims.int_zero
  then pos
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then pos
     else
       if (Parser_JSON.jbyte_at s pos) <> (Prims.of_int (0x30))
       then pos
       else
         jld_first_nonzero_pos s (pos + Prims.int_one) (fuel - Prims.int_one))
let rec jld_zeros (k : Prims.nat) : Prims.string=
  if k = Prims.int_zero
  then ""
  else FStar_String.concat "" ["0"; jld_zeros (k - Prims.int_one)]
let jld_number_canonicalize (lexeme : Prims.string)
  (force_double : Prims.bool) : (Prims.string * Prims.bool)=
  let uu___ = jld_number_parts lexeme in
  match uu___ with
  | (neg, int_start, int_len, frac_start, frac_len, exp) ->
      let combined =
        FStar_String.concat ""
          [Parser_FastString.fs_byte_sub lexeme int_start int_len;
          Parser_FastString.fs_byte_sub lexeme frac_start frac_len] in
      let clen = Parser_FastString.fs_byte_length combined in
      let lead =
        jld_first_nonzero_pos combined Prims.int_zero (clen + Prims.int_one) in
      if lead >= clen
      then (if force_double then ("0.0E0", true) else ("0", false))
      else
        (let after_lead =
           Parser_FastString.fs_byte_sub combined lead (clen - lead) in
         let exp_total = exp - frac_len in
         let keep =
           jld_last_nonzero_len after_lead Prims.int_zero Prims.int_zero
             ((Parser_FastString.fs_byte_length after_lead) + Prims.int_one) in
         let digits =
           Parser_FastString.fs_byte_sub after_lead Prims.int_zero keep in
         let tz = (Parser_FastString.fs_byte_length after_lead) - keep in
         let exp_total1 = exp_total + tz in
         let ndigits = Parser_FastString.fs_byte_length digits in
         let sci_exp = (exp_total1 + ndigits) - Prims.int_one in
         let is_integral = exp_total1 >= Prims.int_zero in
         let magnitude_ge_1e21 = sci_exp >= (Prims.of_int (21)) in
         let use_double =
           (force_double || (Prims.op_Negation is_integral)) ||
             magnitude_ge_1e21 in
         let sign_str = if neg then "-" else "" in
         if use_double
         then
           let mantissa_first =
             Parser_FastString.fs_byte_sub digits Prims.int_zero
               Prims.int_one in
           let mantissa_rest =
             if ndigits > Prims.int_one
             then
               Parser_FastString.fs_byte_sub digits Prims.int_one
                 (ndigits - Prims.int_one)
             else "0" in
           let lexical =
             FStar_String.concat ""
               [sign_str;
               mantissa_first;
               ".";
               mantissa_rest;
               "E";
               Prims.string_of_int sci_exp] in
           (lexical, true)
         else
           (let lexical =
              FStar_String.concat "" [sign_str; digits; jld_zeros exp_total1] in
            (lexical, false)))
type rdf_direction_mode =
  | RDM_Drop 
  | RDM_I18nDatatype 
  | RDM_CompoundLiteral 
let uu___is_RDM_Drop (projectee : rdf_direction_mode) : Prims.bool=
  match projectee with | RDM_Drop -> true | uu___ -> false
let uu___is_RDM_I18nDatatype (projectee : rdf_direction_mode) : Prims.bool=
  match projectee with | RDM_I18nDatatype -> true | uu___ -> false
let uu___is_RDM_CompoundLiteral (projectee : rdf_direction_mode) :
  Prims.bool=
  match projectee with | RDM_CompoundLiteral -> true | uu___ -> false
let jld_fresh_bnode (ctr : Prims.nat) :
  (RDF_Graph_Executable.bnode_id * Prims.nat)=
  ((FStar_String.concat "" ["_jld_anon"; Prims.string_of_int ctr]),
    (ctr + Prims.int_one))
let jld_is_bnode_label (s : Prims.string) : Prims.bool=
  ((Parser_JSON.jbyte_at s Prims.int_zero) = (Prims.of_int (0x5F))) &&
    ((Parser_JSON.jbyte_at s Prims.int_one) = (Prims.of_int (0x3A)))
let jld_strip_bnode_prefix (s : Prims.string) : Prims.string=
  let n = Parser_FastString.fs_byte_length s in
  if n >= (Prims.of_int (2))
  then
    Parser_FastString.fs_byte_sub s (Prims.of_int (2))
      (n - (Prims.of_int (2)))
  else s
let jld_forbidden_byte (b : Prims.int) : Prims.bool=
  ((((((((((b >= Prims.int_zero) && (b <= (Prims.of_int (0x20)))) ||
            (b = (Prims.of_int (0x3C))))
           || (b = (Prims.of_int (0x3E))))
          || (b = (Prims.of_int (0x22))))
         || (b = (Prims.of_int (0x7B))))
        || (b = (Prims.of_int (0x7D))))
       || (b = (Prims.of_int (0x7C))))
      || (b = (Prims.of_int (0x5C))))
     || (b = (Prims.of_int (0x5E))))
    || (b = (Prims.of_int (0x60)))
let rec jld_scan_wf (s : Prims.string) (pos : Prims.nat) (fuel : Prims.nat) :
  Prims.bool=
  if fuel = Prims.int_zero
  then true
  else
    (let n = Parser_FastString.fs_byte_length s in
     if pos >= n
     then true
     else
       if jld_forbidden_byte (Parser_JSON.jbyte_at s pos)
       then false
       else jld_scan_wf s (pos + Prims.int_one) (fuel - Prims.int_one))
let jld_iri_wf (s : Prims.string) : Prims.bool=
  (RDF_Graph_Executable.is_iri s) &&
    (jld_scan_wf s Prims.int_zero
       ((Parser_FastString.fs_byte_length s) + Prims.int_one))
let jld_lang_tag_wf (s : Prims.string) : Prims.bool=
  jld_scan_wf s Prims.int_zero
    ((Parser_FastString.fs_byte_length s) + Prims.int_one)
let jld_id_to_subject (s : Prims.string) :
  RDF_Graph_Executable.subject FStar_Pervasives_Native.option=
  if jld_is_bnode_label s
  then
    FStar_Pervasives_Native.Some
      (RDF_Graph_Executable.S_BNode (jld_strip_bnode_prefix s))
  else
    if jld_iri_wf s
    then FStar_Pervasives_Native.Some (RDF_Graph_Executable.S_IRI s)
    else FStar_Pervasives_Native.None
let jld_is_keyword (k : Prims.string) : Prims.bool=
  (Parser_JSON.jbyte_at k Prims.int_zero) = (Prims.of_int (0x40))
let jld_as_array (v : Parser_JSON.json_val) :
  Parser_JSON.json_val Prims.list=
  match v with | Parser_JSON.JArray items -> items | uu___ -> [v]
let jld_make_literal (lexical : Prims.string) (dt : Prims.string)
  (lang : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if
    (jld_iri_wf dt) &&
      (match lang with
       | FStar_Pervasives_Native.Some l -> jld_lang_tag_wf l
       | FStar_Pervasives_Native.None -> true)
  then
    let lit =
      {
        RDF_Graph_Executable.lexical_form = lexical;
        RDF_Graph_Executable.datatype = dt;
        RDF_Graph_Executable.lang_tag = lang
      } in
    (if RDF_Graph_Executable.literal_wf lit
     then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_Literal lit)
     else FStar_Pervasives_Native.None)
  else FStar_Pervasives_Native.None
let jld_scalar_to_term (v : Parser_JSON.json_val) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match v with
  | Parser_JSON.JString str ->
      jld_make_literal str RDF_Graph_Executable.xsd_string
        FStar_Pervasives_Native.None
  | Parser_JSON.JBool b ->
      jld_make_literal (if b then "true" else "false")
        RDF_Graph_Executable.xsd_boolean FStar_Pervasives_Native.None
  | Parser_JSON.JNumber n ->
      let uu___ = jld_number_canonicalize n false in
      (match uu___ with
       | (lex, is_double) ->
           jld_make_literal lex
             (if is_double
              then RDF_Graph_Executable.xsd_double
              else RDF_Graph_Executable.xsd_integer)
             FStar_Pervasives_Native.None)
  | uu___ -> FStar_Pervasives_Native.None
let jld_i18n_direction_iri
  (lang : Prims.string FStar_Pervasives_Native.option) (dir : Prims.string) :
  Prims.string=
  let langpart =
    match lang with
    | FStar_Pervasives_Native.Some lg -> FStar_String.lowercase lg
    | FStar_Pervasives_Native.None -> "" in
  FStar_String.concat "" ["https://www.w3.org/ns/i18n#"; langpart; "_"; dir]
let jld_value_object_to_term (rdir : rdf_direction_mode)
  (obj : Parser_JSON.json_val) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  match Parser_JSON.json_get_field "@value" obj with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some v ->
      let lang = Parser_JSON.json_get_string "@language" obj in
      let dt = Parser_JSON.json_get_string "@type" obj in
      let dir = Parser_JSON.json_get_string "@direction" obj in
      (match (dir, dt) with
       | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.Some
          uu___1) -> FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.Some d, FStar_Pervasives_Native.None) ->
           (match rdir with
            | RDM_Drop ->
                (match v with
                 | Parser_JSON.JString s ->
                     (match lang with
                      | FStar_Pervasives_Native.Some lg ->
                          jld_make_literal s
                            RDF_Graph_Executable.rdf_lang_string
                            (FStar_Pervasives_Native.Some lg)
                      | FStar_Pervasives_Native.None ->
                          jld_make_literal s RDF_Graph_Executable.xsd_string
                            FStar_Pervasives_Native.None)
                 | uu___ -> FStar_Pervasives_Native.None)
            | RDM_I18nDatatype ->
                (match v with
                 | Parser_JSON.JString s ->
                     jld_make_literal s (jld_i18n_direction_iri lang d)
                       FStar_Pervasives_Native.None
                 | uu___ -> FStar_Pervasives_Native.None)
            | RDM_CompoundLiteral -> FStar_Pervasives_Native.None)
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some d) ->
           if d = "@json"
           then
             jld_make_literal (jcanon_document v) rdf_json_iri
               FStar_Pervasives_Native.None
           else
             (match v with
              | Parser_JSON.JString s ->
                  jld_make_literal s d FStar_Pervasives_Native.None
              | Parser_JSON.JBool b ->
                  jld_make_literal (if b then "true" else "false") d
                    FStar_Pervasives_Native.None
              | Parser_JSON.JNumber n ->
                  let uu___1 =
                    jld_number_canonicalize n
                      (d = RDF_Graph_Executable.xsd_double) in
                  (match uu___1 with
                   | (lex, uu___2) ->
                       jld_make_literal lex d FStar_Pervasives_Native.None)
              | uu___1 -> FStar_Pervasives_Native.None)
       | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
           (match lang with
            | FStar_Pervasives_Native.Some lg ->
                (match v with
                 | Parser_JSON.JString s ->
                     jld_make_literal s RDF_Graph_Executable.rdf_lang_string
                       (FStar_Pervasives_Native.Some lg)
                 | uu___ -> FStar_Pervasives_Native.None)
            | FStar_Pervasives_Native.None -> jld_scalar_to_term v))
let jld_type_term (t : Prims.string) :
  RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option=
  if jld_is_bnode_label t
  then
    FStar_Pervasives_Native.Some
      (RDF_Graph_Executable.T_BNode (jld_strip_bnode_prefix t))
  else
    if jld_iri_wf t
    then FStar_Pervasives_Native.Some (RDF_Graph_Executable.T_IRI t)
    else FStar_Pervasives_Native.None
let rec jld_type_prepend_items (subj : RDF_Graph_Executable.subject)
  (items : Parser_JSON.json_val Prims.list)
  (acc : RDF_Graph_Executable.triple Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  match items with
  | [] -> acc
  | (Parser_JSON.JString t)::rest ->
      (match jld_type_term t with
       | FStar_Pervasives_Native.Some tm ->
           jld_type_prepend_items subj rest
             ({
                RDF_Graph_Executable.s = subj;
                RDF_Graph_Executable.p = rdf_type_iri;
                RDF_Graph_Executable.o = tm
              } :: acc)
       | FStar_Pervasives_Native.None -> jld_type_prepend_items subj rest acc)
  | uu___::rest -> jld_type_prepend_items subj rest acc
let jld_type_prepend (subj : RDF_Graph_Executable.subject)
  (v : Parser_JSON.json_val) (acc : RDF_Graph_Executable.triple Prims.list) :
  RDF_Graph_Executable.triple Prims.list=
  jld_type_prepend_items subj (jld_as_array v) acc
let jld_graph_name_of_subject (s : RDF_Graph_Executable.subject) :
  RDF_Graph_Executable.iri=
  match s with
  | RDF_Graph_Executable.S_IRI i -> i
  | RDF_Graph_Executable.S_BNode b -> FStar_String.concat "" ["_:"; b]
let rec jld_expand_value (rdir : rdf_direction_mode)
  (v : Parser_JSON.json_val) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.rdf_term FStar_Pervasives_Native.option *
    RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (FStar_Pervasives_Native.None, acc, named, ctr)
  else
    (match v with
     | Parser_JSON.JObject uu___1 ->
         (match Parser_JSON.json_get_field "@value" v with
          | FStar_Pervasives_Native.Some uu___2 ->
              ((jld_value_object_to_term rdir v), acc, named, ctr)
          | FStar_Pervasives_Native.None ->
              (match Parser_JSON.json_get_field "@list" v with
               | FStar_Pervasives_Native.Some lst ->
                   let uu___2 =
                     jld_expand_list rdir (jld_as_array lst) ctr acc named
                       (fuel - Prims.int_one) in
                   (match uu___2 with
                    | (t, acc1, named1, ctr1) ->
                        ((FStar_Pervasives_Native.Some t), acc1, named1,
                          ctr1))
               | FStar_Pervasives_Native.None ->
                   let uu___2 =
                     jld_expand_node rdir v ctr acc named
                       (fuel - Prims.int_one) in
                   (match uu___2 with
                    | (osubj, acc1, named1, ctr1) ->
                        (match osubj with
                         | FStar_Pervasives_Native.Some subj ->
                             ((FStar_Pervasives_Native.Some
                                 (RDF_Graph_Executable.subject_to_term subj)),
                               acc1, named1, ctr1)
                         | FStar_Pervasives_Native.None ->
                             (FStar_Pervasives_Native.None, acc1, named1,
                               ctr1)))))
     | uu___1 -> ((jld_scalar_to_term v), acc, named, ctr))
and jld_expand_list (rdir : rdf_direction_mode)
  (items : Parser_JSON.json_val Prims.list) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.rdf_term * RDF_Graph_Executable.triple Prims.list *
    RDF_Graph_Executable.named_graph Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then ((RDF_Graph_Executable.T_IRI rdf_nil_iri), acc, named, ctr)
  else
    (match items with
     | [] -> ((RDF_Graph_Executable.T_IRI rdf_nil_iri), acc, named, ctr)
     | item::rest ->
         let uu___1 =
           jld_expand_value rdir item ctr acc named (fuel - Prims.int_one) in
         (match uu___1 with
          | (oterm, acc1, named1, ctr1) ->
              (match oterm with
               | FStar_Pervasives_Native.None ->
                   jld_expand_list rdir rest ctr1 acc1 named1
                     (fuel - Prims.int_one)
               | FStar_Pervasives_Native.Some t ->
                   let uu___2 = jld_fresh_bnode ctr1 in
                   (match uu___2 with
                    | (cell, ctr2) ->
                        let uu___3 =
                          jld_expand_list rdir rest ctr2 acc1 named1
                            (fuel - Prims.int_one) in
                        (match uu___3 with
                         | (rest_term, acc2, named2, ctr3) ->
                             let cell_subj =
                               RDF_Graph_Executable.S_BNode cell in
                             ((RDF_Graph_Executable.T_BNode cell),
                               ({
                                  RDF_Graph_Executable.s = cell_subj;
                                  RDF_Graph_Executable.p = rdf_rest_iri;
                                  RDF_Graph_Executable.o = rest_term
                                } ::
                               {
                                 RDF_Graph_Executable.s = cell_subj;
                                 RDF_Graph_Executable.p = rdf_first_iri;
                                 RDF_Graph_Executable.o = t
                               } :: acc2), named2, ctr3))))))
and jld_expand_node (rdir : rdf_direction_mode) (v : Parser_JSON.json_val)
  (ctr : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.subject FStar_Pervasives_Native.option *
    RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (FStar_Pervasives_Native.None, acc, named, ctr)
  else
    (match v with
     | Parser_JSON.JObject fields ->
         let uu___1 =
           match Parser_JSON.json_get_field "@id" v with
           | FStar_Pervasives_Native.Some (Parser_JSON.JString id_str) ->
               ((jld_id_to_subject id_str), ctr)
           | FStar_Pervasives_Native.Some uu___2 ->
               (FStar_Pervasives_Native.None, ctr)
           | FStar_Pervasives_Native.None ->
               let uu___2 = jld_fresh_bnode ctr in
               (match uu___2 with
                | (b, ctr') ->
                    ((FStar_Pervasives_Native.Some
                        (RDF_Graph_Executable.S_BNode b)), ctr')) in
         (match uu___1 with
          | (subj_opt, ctr1) ->
              (match subj_opt with
               | FStar_Pervasives_Native.None ->
                   (FStar_Pervasives_Native.None, acc, named, ctr1)
               | FStar_Pervasives_Native.Some subj ->
                   (match Parser_JSON.json_get_field "@graph" v with
                    | FStar_Pervasives_Native.Some g ->
                        let uu___2 =
                          jld_expand_graph_nodes rdir (jld_as_array g) ctr1
                            [] named (fuel - Prims.int_one) in
                        (match uu___2 with
                         | (gtris, named1, ctr2) ->
                             let ng =
                               {
                                 RDF_Graph_Executable.ng_name =
                                   (jld_graph_name_of_subject subj);
                                 RDF_Graph_Executable.ng_graph = gtris
                               } in
                             let uu___3 =
                               jld_expand_fields rdir subj fields ctr2 acc
                                 (ng :: named1) (fuel - Prims.int_one) in
                             (match uu___3 with
                              | (acc1, named2, ctr3) ->
                                  ((FStar_Pervasives_Native.Some subj), acc1,
                                    named2, ctr3)))
                    | FStar_Pervasives_Native.None ->
                        let uu___2 =
                          jld_expand_fields rdir subj fields ctr1 acc named
                            (fuel - Prims.int_one) in
                        (match uu___2 with
                         | (acc1, named1, ctr2) ->
                             ((FStar_Pervasives_Native.Some subj), acc1,
                               named1, ctr2)))))
     | uu___1 -> (FStar_Pervasives_Native.None, acc, named, ctr))
and jld_expand_fields (rdir : rdf_direction_mode)
  (subj : RDF_Graph_Executable.subject)
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list)
  (ctr : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, named, ctr)
  else
    (match fields with
     | [] -> (acc, named, ctr)
     | (key, value)::rest ->
         let uu___1 =
           if key = "@type"
           then ((jld_type_prepend subj value acc), named, ctr)
           else
             if key = "@reverse"
             then
               jld_expand_reverse_map rdir subj value ctr acc named
                 (fuel - Prims.int_one)
             else
               if key = "@included"
               then
                 jld_expand_graph_nodes rdir (jld_as_array value) ctr acc
                   named (fuel - Prims.int_one)
               else
                 if jld_is_keyword key
                 then (acc, named, ctr)
                 else
                   if jld_iri_wf key
                   then
                     jld_expand_property rdir subj key (jld_as_array value)
                       ctr acc named (fuel - Prims.int_one)
                   else (acc, named, ctr) in
         (match uu___1 with
          | (acc1, named1, ctr1) ->
              jld_expand_fields rdir subj rest ctr1 acc1 named1
                (fuel - Prims.int_one)))
and jld_expand_reverse_map (rdir : rdf_direction_mode)
  (subj : RDF_Graph_Executable.subject) (v : Parser_JSON.json_val)
  (ctr : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, named, ctr)
  else
    (match v with
     | Parser_JSON.JObject entries ->
         jld_expand_reverse_entries rdir subj entries ctr acc named
           (fuel - Prims.int_one)
     | uu___1 -> (acc, named, ctr))
and jld_expand_reverse_entries (rdir : rdf_direction_mode)
  (subj : RDF_Graph_Executable.subject)
  (entries : (Prims.string * Parser_JSON.json_val) Prims.list)
  (ctr : Prims.nat) (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, named, ctr)
  else
    (match entries with
     | [] -> (acc, named, ctr)
     | (prop, value)::rest ->
         let uu___1 =
           if jld_iri_wf prop
           then
             jld_expand_reverse_prop rdir subj prop (jld_as_array value) ctr
               acc named (fuel - Prims.int_one)
           else (acc, named, ctr) in
         (match uu___1 with
          | (acc1, named1, ctr1) ->
              jld_expand_reverse_entries rdir subj rest ctr1 acc1 named1
                (fuel - Prims.int_one)))
and jld_expand_reverse_prop (rdir : rdf_direction_mode)
  (subj : RDF_Graph_Executable.subject) (prop : RDF_Graph_Executable.wf_iri)
  (vals : Parser_JSON.json_val Prims.list) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, named, ctr)
  else
    (match vals with
     | [] -> (acc, named, ctr)
     | v::rest ->
         let uu___1 =
           jld_expand_node rdir v ctr acc named (fuel - Prims.int_one) in
         (match uu___1 with
          | (osubj, acc1, named1, ctr1) ->
              let acc2 =
                match osubj with
                | FStar_Pervasives_Native.Some vsubj ->
                    {
                      RDF_Graph_Executable.s = vsubj;
                      RDF_Graph_Executable.p = prop;
                      RDF_Graph_Executable.o =
                        (RDF_Graph_Executable.subject_to_term subj)
                    } :: acc1
                | FStar_Pervasives_Native.None -> acc1 in
              jld_expand_reverse_prop rdir subj prop rest ctr1 acc2 named1
                (fuel - Prims.int_one)))
and jld_expand_property (rdir : rdf_direction_mode)
  (subj : RDF_Graph_Executable.subject) (prop : RDF_Graph_Executable.wf_iri)
  (vals : Parser_JSON.json_val Prims.list) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, named, ctr)
  else
    (match vals with
     | [] -> (acc, named, ctr)
     | v::rest ->
         let uu___1 =
           jld_expand_value rdir v ctr acc named (fuel - Prims.int_one) in
         (match uu___1 with
          | (oterm, acc1, named1, ctr1) ->
              let acc2 =
                match oterm with
                | FStar_Pervasives_Native.Some t ->
                    {
                      RDF_Graph_Executable.s = subj;
                      RDF_Graph_Executable.p = prop;
                      RDF_Graph_Executable.o = t
                    } :: acc1
                | FStar_Pervasives_Native.None -> acc1 in
              jld_expand_property rdir subj prop rest ctr1 acc2 named1
                (fuel - Prims.int_one)))
and jld_expand_graph_nodes (rdir : rdf_direction_mode)
  (nodes : Parser_JSON.json_val Prims.list) (ctr : Prims.nat)
  (acc : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (acc, named, ctr)
  else
    (match nodes with
     | [] -> (acc, named, ctr)
     | n::rest ->
         let uu___1 =
           jld_expand_node rdir n ctr acc named (fuel - Prims.int_one) in
         (match uu___1 with
          | (uu___2, acc1, named1, ctr1) ->
              jld_expand_graph_nodes rdir rest ctr1 acc1 named1
                (fuel - Prims.int_one)))
let jld_expand_top (rdir : rdf_direction_mode) (v : Parser_JSON.json_val)
  (dflt : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (ctr : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  match v with
  | Parser_JSON.JObject fields ->
      (match Parser_JSON.json_get_field "@graph" v with
       | FStar_Pervasives_Native.Some g ->
           let uu___ =
             match Parser_JSON.json_get_field "@id" v with
             | FStar_Pervasives_Native.Some (Parser_JSON.JString id_str) ->
                 ((jld_id_to_subject id_str), ctr)
             | FStar_Pervasives_Native.Some uu___1 ->
                 (FStar_Pervasives_Native.None, ctr)
             | FStar_Pervasives_Native.None ->
                 let uu___1 = jld_fresh_bnode ctr in
                 (match uu___1 with
                  | (b, ctr') ->
                      ((FStar_Pervasives_Native.Some
                          (RDF_Graph_Executable.S_BNode b)), ctr')) in
           (match uu___ with
            | (subj_opt, ctr1) ->
                (match subj_opt with
                 | FStar_Pervasives_Native.None -> (dflt, named, ctr1)
                 | FStar_Pervasives_Native.Some gsubj ->
                     let uu___1 =
                       jld_expand_graph_nodes rdir (jld_as_array g) ctr1 []
                         named fuel in
                     (match uu___1 with
                      | (gtris, named1, ctr2) ->
                          let uu___2 =
                            jld_expand_fields rdir gsubj fields ctr2 dflt
                              named1 fuel in
                          (match uu___2 with
                           | (dflt1, named2, ctr3) ->
                               let ng =
                                 {
                                   RDF_Graph_Executable.ng_name =
                                     (jld_graph_name_of_subject gsubj);
                                   RDF_Graph_Executable.ng_graph = gtris
                                 } in
                               (dflt1, (ng :: named2), ctr3)))))
       | FStar_Pervasives_Native.None ->
           let uu___ = jld_expand_node rdir v ctr dflt named fuel in
           (match uu___ with
            | (uu___1, dflt1, named1, ctr1) -> (dflt1, named1, ctr1)))
  | uu___ -> (dflt, named, ctr)
let rec jld_expand_tops (rdir : rdf_direction_mode)
  (vs : Parser_JSON.json_val Prims.list)
  (dflt : RDF_Graph_Executable.triple Prims.list)
  (named : RDF_Graph_Executable.named_graph Prims.list) (ctr : Prims.nat)
  (fuel : Prims.nat) :
  (RDF_Graph_Executable.triple Prims.list * RDF_Graph_Executable.named_graph
    Prims.list * Prims.nat)=
  if fuel = Prims.int_zero
  then (dflt, named, ctr)
  else
    (match vs with
     | [] -> (dflt, named, ctr)
     | v::rest ->
         let uu___1 = jld_expand_top rdir v dflt named ctr fuel in
         (match uu___1 with
          | (d1, n1, c1) ->
              jld_expand_tops rdir rest d1 n1 c1 (fuel - Prims.int_one)))
let rec jld_only_graph_keys
  (fields : (Prims.string * Parser_JSON.json_val) Prims.list) : Prims.bool=
  match fields with
  | [] -> true
  | (k, uu___)::rest -> (k = "@graph") && (jld_only_graph_keys rest)
let jld_dataset_of_json (rdir : rdf_direction_mode)
  (root : Parser_JSON.json_val) :
  RDF_Graph_Executable.rdf_dataset FStar_Pervasives_Native.option=
  let fuel = (Parser_JSON.json_size root) + Prims.int_one in
  match root with
  | Parser_JSON.JArray tops ->
      let uu___ = jld_expand_tops rdir tops [] [] Prims.int_zero fuel in
      (match uu___ with
       | (d, n, uu___1) ->
           FStar_Pervasives_Native.Some
             (RDF_Graph_Executable.dataset_finalise
                {
                  RDF_Graph_Executable.ds_default = d;
                  RDF_Graph_Executable.ds_named = (FStar_List_Tot_Base.rev n)
                }))
  | Parser_JSON.JObject fields ->
      let tops =
        if jld_only_graph_keys fields
        then
          match Parser_JSON.json_get_field "@graph" root with
          | FStar_Pervasives_Native.Some g -> jld_as_array g
          | FStar_Pervasives_Native.None -> [root]
        else [root] in
      let uu___ = jld_expand_tops rdir tops [] [] Prims.int_zero fuel in
      (match uu___ with
       | (d, n, uu___1) ->
           FStar_Pervasives_Native.Some
             (RDF_Graph_Executable.dataset_finalise
                {
                  RDF_Graph_Executable.ds_default = d;
                  RDF_Graph_Executable.ds_named = (FStar_List_Tot_Base.rev n)
                }))
  | uu___ -> FStar_Pervasives_Native.None
let jld_has_inline_context (root : Parser_JSON.json_val) : Prims.bool=
  match root with
  | Parser_JSON.JObject fields ->
      FStar_List_Tot_Base.existsb
        (fun kv -> (FStar_Pervasives_Native.fst kv) = "@context") fields
  | uu___ -> false
let rdf_direction_mode_of_option
  (rdf_direction : Prims.string FStar_Pervasives_Native.option) :
  rdf_direction_mode=
  match rdf_direction with
  | FStar_Pervasives_Native.Some "i18n-datatype" -> RDM_I18nDatatype
  | FStar_Pervasives_Native.Some "compound-literal" -> RDM_CompoundLiteral
  | uu___ -> RDM_Drop
let parse_jsonld (input : Prims.string)
  (base : Prims.string FStar_Pervasives_Native.option)
  (rdf_direction : Prims.string FStar_Pervasives_Native.option)
  (expand_context : Prims.string FStar_Pervasives_Native.option) :
  RDF_Graph_Executable.rdf_dataset FStar_Pervasives_Native.option=
  let rdir = rdf_direction_mode_of_option rdf_direction in
  match Parser_JSON.parse_json input with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some root ->
      if
        ((jld_has_inline_context root) ||
           (FStar_Pervasives_Native.uu___is_Some base))
          || (FStar_Pervasives_Native.uu___is_Some expand_context)
      then
        let ac_seed =
          {
            JSONLD_Context.ac_terms =
              (JSONLD_Context.empty_active_context.JSONLD_Context.ac_terms);
            JSONLD_Context.ac_vocab =
              (JSONLD_Context.empty_active_context.JSONLD_Context.ac_vocab);
            JSONLD_Context.ac_base = base;
            JSONLD_Context.ac_language =
              (JSONLD_Context.empty_active_context.JSONLD_Context.ac_language);
            JSONLD_Context.ac_direction =
              (JSONLD_Context.empty_active_context.JSONLD_Context.ac_direction);
            JSONLD_Context.ac_previous =
              (JSONLD_Context.empty_active_context.JSONLD_Context.ac_previous)
          } in
        let ac0_opt =
          match expand_context with
          | FStar_Pervasives_Native.None ->
              FStar_Pervasives_Native.Some ac_seed
          | FStar_Pervasives_Native.Some ctxref ->
              JSONLD_Context.context_process ac_seed
                (Parser_JSON.JString ctxref) false
                JSONLD_Context.jld_remote_context_fuel [] in
        (match ac0_opt with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some ac0 ->
             (match JSONLD_Expand.expand ac0 root with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some expanded ->
                  jld_dataset_of_json rdir expanded))
      else jld_dataset_of_json rdir root
