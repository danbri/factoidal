open Prims
let shnex_ns : Prims.string= "http://www.w3.org/ns/shacl-node-expr#"
let shnex_focusNode : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#focusNode"
let shnex_pathValues : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#pathValues"
let shnex_nodes : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#nodes"
let shnex_concat : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#concat"
let shnex_count : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#count"
let shnex_distinct : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#distinct"
let shnex_exists : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#exists"
let shnex_if : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#if"
let shnex_then : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#then"
let shnex_else : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#else"
let shnex_var : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#var"
let shnex_instancesOf : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#instancesOf"
let shnex_sum : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#sum"
let shnex_min : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#min"
let shnex_max : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#max"
let shnex_intersection : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#intersection"
let shnex_remove : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#remove"
let shnex_flatMap : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#flatMap"
let shnex_orderBy : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#orderBy"
let shnex_desc : RDF_Term.wf_iri= "http://www.w3.org/ns/shacl-node-expr#desc"
let shnex_filterShape : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#filterShape"
let shnex_matchAll : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#matchAll"
let shnex_findFirst : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#findFirst"
let shnex_nodesMatching : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#nodesMatching"
let shnex_limit : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#limit"
let shnex_offset : RDF_Term.wf_iri=
  "http://www.w3.org/ns/shacl-node-expr#offset"
let mk_int_lit (n : Prims.int) : RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = (Prims.string_of_int n);
      RDF_Term.datatype = RDF_Term.xsd_integer;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    }
let mk_bool_lit (b : Prims.bool) : RDF_Term.rdf_term=
  RDF_Term.T_Literal
    {
      RDF_Term.lexical_form = (if b then "true" else "false");
      RDF_Term.datatype = RDF_Term.xsd_boolean;
      RDF_Term.lang_tag = FStar_Pervasives_Native.None;
      RDF_Term.direction = FStar_Pervasives_Native.None
    }
let ne_ebv (l : RDF_Term.rdf_term Prims.list) : Prims.bool=
  match l with
  | (RDF_Term.T_Literal lit)::uu___ ->
      if lit.RDF_Term.datatype = RDF_Term.xsd_boolean
      then lit.RDF_Term.lexical_form = "true"
      else true
  | [] -> false
  | uu___ -> true
let rec list_drop (n : Prims.nat) (l : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match (n, l) with
  | (uu___, uu___1) when uu___ = Prims.int_zero -> l
  | (uu___, []) -> []
  | (uu___, uu___1::tl) -> list_drop (n - Prims.int_one) tl
let rec list_take (n : Prims.nat) (l : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match (n, l) with
  | (uu___, uu___1) when uu___ = Prims.int_zero -> []
  | (uu___, []) -> []
  | (uu___, hd::tl) -> hd :: (list_take (n - Prims.int_one) tl)
let instances_of (g : RDF_Graph.rdf_graph) (c : RDF_Term.wf_iri) :
  RDF_Term.rdf_term Prims.list=
  let closed =
    SHACL_Validation.shacl_class_closure g
      ((RDF_Graph.graph_len g) + (Prims.of_int (20))) in
  SHACL_Validation.dedup_terms
    (FStar_List_Tot_Base.map RDF_Graph.subject_to_term
       (RDF_Graph_Executable.find_subjects closed RDFS_Closure.rdf_type
          (RDF_Term.T_IRI c)))
let node_conforms (g : RDF_Graph.rdf_graph) (shape_term : RDF_Term.rdf_term)
  (v : RDF_Term.rdf_term) : Prims.bool=
  match SHACL_Validation.term_to_shape_ref shape_term with
  | FStar_Pervasives_Native.None -> true
  | FStar_Pervasives_Native.Some r ->
      let sg =
        (SHACL_Validation.parse_shape_from_graph_pure g).SHACL_Validation.shapes in
      (match SHACL_Validation.lookup_shape r sg with
       | FStar_Pervasives_Native.None -> true
       | FStar_Pervasives_Native.Some sh ->
           let closed_cls =
             SHACL_Validation.shacl_class_closure g
               ((RDF_Graph.graph_len g) + (Prims.of_int (20))) in
           Prims.uu___is_Nil
             (SHACL_Validation.collect_shape_violations g sg closed_cls v sh
                ((RDF_Graph.graph_len g) + (Prims.of_int (100)))))
let parse_int_term (t : RDF_Term.rdf_term) :
  Prims.int FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if l.RDF_Term.datatype = RDF_Term.xsd_integer
      then SPARQL11_Algebra.parse_int_string l.RDF_Term.lexical_form
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let rec ints_of (l : RDF_Term.rdf_term Prims.list) :
  Prims.int Prims.list FStar_Pervasives_Native.option=
  match l with
  | [] -> FStar_Pervasives_Native.Some []
  | h::r ->
      (match ((parse_int_term h), (ints_of r)) with
       | (FStar_Pervasives_Native.Some n, FStar_Pervasives_Native.Some ns) ->
           FStar_Pervasives_Native.Some (n :: ns)
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
let rec pow10 (n : Prims.nat) : Prims.int=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int (10)) * (pow10 (n - Prims.int_one))
let rec split_dot (cs : FStar_Char.char Prims.list)
  (acc : FStar_Char.char Prims.list) :
  (FStar_Char.char Prims.list * FStar_Char.char Prims.list
    FStar_Pervasives_Native.option)=
  match cs with
  | [] -> ((FStar_List_Tot_Base.rev acc), FStar_Pervasives_Native.None)
  | 46::rest ->
      ((FStar_List_Tot_Base.rev acc), (FStar_Pervasives_Native.Some rest))
  | c::rest -> split_dot rest (c :: acc)
let parse_dec_lexical (s : Prims.string) :
  (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  let uu___ = split_dot (FStar_String.list_of_string s) [] in
  match uu___ with
  | (before, after_opt) ->
      (match after_opt with
       | FStar_Pervasives_Native.None ->
           (match SPARQL11_Algebra.parse_int_string s with
            | FStar_Pervasives_Native.Some n ->
                FStar_Pervasives_Native.Some (n, Prims.int_zero)
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
       | FStar_Pervasives_Native.Some after ->
           (match SPARQL11_Algebra.parse_int_string
                    (FStar_String.string_of_list
                       (FStar_List_Tot_Base.op_At before after))
            with
            | FStar_Pervasives_Native.Some n ->
                FStar_Pervasives_Native.Some
                  (n, (FStar_List_Tot_Base.length after))
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None))
let parse_num_term (t : RDF_Term.rdf_term) :
  (Prims.int * Prims.nat) FStar_Pervasives_Native.option=
  match t with
  | RDF_Term.T_Literal l ->
      if
        (l.RDF_Term.datatype = RDF_Term.xsd_integer) ||
          (l.RDF_Term.datatype = RDF_Term.xsd_decimal)
      then parse_dec_lexical l.RDF_Term.lexical_form
      else FStar_Pervasives_Native.None
  | uu___ -> FStar_Pervasives_Native.None
let rec nums_of (l : RDF_Term.rdf_term Prims.list) :
  (Prims.int * Prims.nat) Prims.list FStar_Pervasives_Native.option=
  match l with
  | [] -> FStar_Pervasives_Native.Some []
  | h::r ->
      (match ((parse_num_term h), (nums_of r)) with
       | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.Some ps) ->
           FStar_Pervasives_Native.Some (p :: ps)
       | (uu___, uu___1) -> FStar_Pervasives_Native.None)
let rec max_scale (ps : (Prims.int * Prims.nat) Prims.list) (acc : Prims.nat)
  : Prims.nat=
  match ps with
  | [] -> acc
  | (uu___, sc)::r -> max_scale r (if sc > acc then sc else acc)
let rec sum_scaled (ps : (Prims.int * Prims.nat) Prims.list) (ms : Prims.nat)
  : Prims.int=
  match ps with
  | [] -> Prims.int_zero
  | (n, sc)::r ->
      (n * (pow10 (if ms >= sc then ms - sc else Prims.int_zero))) +
        (sum_scaled r ms)
let rec repeat0 (n : Prims.nat) : FStar_Char.char Prims.list=
  if n = Prims.int_zero then [] else 48 :: (repeat0 (n - Prims.int_one))
let mk_decimal_lit (scaled_val : Prims.int) (scale : Prims.nat) :
  RDF_Term.rdf_term=
  if scale = Prims.int_zero
  then mk_int_lit scaled_val
  else
    (let neg = scaled_val < Prims.int_zero in
     let a = if neg then Prims.int_zero - scaled_val else scaled_val in
     let digits = FStar_String.list_of_string (Prims.string_of_int a) in
     let dlen = FStar_List_Tot_Base.length digits in
     let padded =
       FStar_List_Tot_Base.op_At
         (if dlen >= (scale + Prims.int_one)
          then []
          else repeat0 ((scale + Prims.int_one) - dlen)) digits in
     let n = FStar_List_Tot_Base.length padded in
     let k = if n >= scale then n - scale else Prims.int_zero in
     let uu___1 = FStar_List_Tot_Base.splitAt k padded in
     match uu___1 with
     | (intp, fracp) ->
         let body =
           FStar_String.string_of_list
             (FStar_List_Tot_Base.op_At intp
                (FStar_List_Tot_Base.op_At [46] fracp)) in
         let lex = if neg then FStar_String.concat "" ["-"; body] else body in
         RDF_Term.T_Literal
           {
             RDF_Term.lexical_form = lex;
             RDF_Term.datatype = RDF_Term.xsd_decimal;
             RDF_Term.lang_tag = FStar_Pervasives_Native.None;
             RDF_Term.direction = FStar_Pervasives_Native.None
           })
let sum_expr (vals : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match nums_of vals with
  | FStar_Pervasives_Native.Some ps ->
      let ms = max_scale ps Prims.int_zero in
      [mk_decimal_lit (sum_scaled ps ms) ms]
  | FStar_Pervasives_Native.None -> []
let rec max_int (ns : Prims.int Prims.list) (acc : Prims.int) : Prims.int=
  match ns with | [] -> acc | h::r -> max_int r (if h > acc then h else acc)
let rec min_int (ns : Prims.int Prims.list) (acc : Prims.int) : Prims.int=
  match ns with | [] -> acc | h::r -> min_int r (if h < acc then h else acc)
let max_expr (vals : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match ints_of vals with
  | FStar_Pervasives_Native.Some (h::t) -> [mk_int_lit (max_int t h)]
  | uu___ -> []
let min_expr (vals : RDF_Term.rdf_term Prims.list) :
  RDF_Term.rdf_term Prims.list=
  match ints_of vals with
  | FStar_Pervasives_Native.Some (h::t) -> [mk_int_lit (min_int t h)]
  | uu___ -> []
let rec term_mem (t : RDF_Term.rdf_term) (l : RDF_Term.rdf_term Prims.list) :
  Prims.bool=
  match l with
  | [] -> false
  | h::r -> (RDF_Term.rdf_term_eq t h) || (term_mem t r)
let rec clist_cmp (a : FStar_Char.char Prims.list)
  (b : FStar_Char.char Prims.list) : Prims.int=
  match (a, b) with
  | ([], []) -> Prims.int_zero
  | ([], uu___) -> (Prims.of_int (-1))
  | (uu___, []) -> Prims.int_one
  | (x::xs, y::ys) ->
      let cx = FStar_Char.int_of_char x in
      let cy = FStar_Char.int_of_char y in
      if cx < cy
      then (Prims.of_int (-1))
      else if cx > cy then Prims.int_one else clist_cmp xs ys
let str_cmp (a : Prims.string) (b : Prims.string) : Prims.int=
  clist_cmp (FStar_String.list_of_string a) (FStar_String.list_of_string b)
let term_render (t : RDF_Term.rdf_term) : Prims.string=
  match t with
  | RDF_Term.T_IRI i -> i
  | RDF_Term.T_Literal l -> l.RDF_Term.lexical_form
  | RDF_Term.T_BNode b -> b
  | RDF_Term.T_TripleTerm (uu___, uu___1, uu___2) -> ""
let term_cmp (a : RDF_Term.rdf_term) (b : RDF_Term.rdf_term) : Prims.int=
  match ((parse_int_term a), (parse_int_term b)) with
  | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
      if x < y
      then (Prims.of_int (-1))
      else if x > y then Prims.int_one else Prims.int_zero
  | (uu___, uu___1) -> str_cmp (term_render a) (term_render b)
let sparql_ns : Prims.string= "http://www.w3.org/ns/sparql#"
let sparql_localname (p : RDF_Term.wf_iri) :
  Prims.string FStar_Pervasives_Native.option=
  let n = FStar_String.strlen sparql_ns in
  if
    ((FStar_String.strlen p) > n) &&
      ((FStar_String.sub p Prims.int_zero n) = sparql_ns)
  then
    FStar_Pervasives_Native.Some
      (FStar_String.sub p n ((FStar_String.strlen p) - n))
  else FStar_Pervasives_Native.None
let sparql_call_of (g : RDF_Graph.rdf_graph) (es : RDF_Term.subject) :
  (Prims.string * RDF_Term.rdf_term) FStar_Pervasives_Native.option=
  match FStar_List_Tot_Base.filter
          (fun tr ->
             (RDF_Term.subject_eq tr.RDF_Triple.s es) &&
               (FStar_Pervasives_Native.uu___is_Some
                  (sparql_localname tr.RDF_Triple.p))) g
  with
  | tr::uu___ ->
      (match sparql_localname tr.RDF_Triple.p with
       | FStar_Pervasives_Native.Some ln ->
           FStar_Pervasives_Native.Some (ln, (tr.RDF_Triple.o))
       | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
  | [] -> FStar_Pervasives_Native.None
let subj_to_expr (s : RDF_Term.subject) : SPARQL11_Algebra.expr=
  match s with
  | RDF_Term.S_IRI i -> SPARQL11_Algebra.E_IRI i
  | RDF_Term.S_BNode uu___ ->
      SPARQL11_Algebra.E_Literal (SPARQL11_Algebra.mk_plain_literal "")
let rec term_to_expr (t : RDF_Term.rdf_term) : SPARQL11_Algebra.expr=
  match t with
  | RDF_Term.T_IRI i -> SPARQL11_Algebra.E_IRI i
  | RDF_Term.T_Literal l ->
      if l.RDF_Term.datatype = RDF_Term.xsd_integer
      then
        (match SPARQL11_Algebra.parse_int_string l.RDF_Term.lexical_form with
         | FStar_Pervasives_Native.Some n -> SPARQL11_Algebra.E_NumericLit n
         | FStar_Pervasives_Native.None -> SPARQL11_Algebra.E_Literal l)
      else
        if l.RDF_Term.datatype = RDF_Term.xsd_decimal
        then SPARQL11_Algebra.E_DecimalLit (l.RDF_Term.lexical_form)
        else
          if l.RDF_Term.datatype = RDF_Term.xsd_double
          then SPARQL11_Algebra.E_DoubleLit (l.RDF_Term.lexical_form)
          else
            if l.RDF_Term.datatype = RDF_Term.xsd_boolean
            then
              SPARQL11_Algebra.E_BoolLit (l.RDF_Term.lexical_form = "true")
            else SPARQL11_Algebra.E_Literal l
  | RDF_Term.T_TripleTerm (s, p, o) ->
      SPARQL11_Algebra.E_TripleTerm
        ((subj_to_expr s), (SPARQL11_Algebra.E_IRI p), (term_to_expr o))
  | RDF_Term.T_BNode uu___ ->
      SPARQL11_Algebra.E_Literal (SPARQL11_Algebra.mk_plain_literal "")
let sparql_fn_expr (ln : Prims.string)
  (args : SPARQL11_Algebra.expr Prims.list) :
  SPARQL11_Algebra.expr FStar_Pervasives_Native.option=
  match (ln, args) with
  | ("abs", a::[]) -> FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Abs a)
  | ("ceil", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Ceil a)
  | ("floor", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Floor a)
  | ("round", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Round a)
  | ("str", a::[]) -> FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Str a)
  | ("strlen", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrLen a)
  | ("ucase", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_UCase a)
  | ("lcase", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_LCase a)
  | ("lang", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Lang a)
  | ("langdir", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_LangDir a)
  | ("hasLang", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_HasLang a)
  | ("hasLang", a::uu___::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_HasLang a)
  | ("hasLangdir", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_HasLangDir a)
  | ("hasLangdir", a::uu___::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_HasLangDir a)
  | ("datatype", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Datatype a)
  | ("iri", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IRI_fn a)
  | ("uri", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IRI_fn a)
  | ("encode-for-uri", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_EncodeForUri a)
  | ("encode", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_EncodeForUri a)
  | ("isIRI", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IsIRI a)
  | ("isURI", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IsIRI a)
  | ("isBlank", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IsBlank a)
  | ("isLiteral", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IsLiteral a)
  | ("isNumeric", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IsNumeric a)
  | ("isTriple", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_IsTriple a)
  | ("triple", a::b::c::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_TripleTerm (a, b, c))
  | ("subject", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_TTSubject a)
  | ("predicate", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_TTPredicate a)
  | ("object", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_TTObject a)
  | ("contains", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Contains (a, b))
  | ("strstarts", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrStarts (a, b))
  | ("strends", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrEnds (a, b))
  | ("strbefore", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrBefore (a, b))
  | ("strafter", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrAfter (a, b))
  | ("strdt", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrDt (a, b))
  | ("strlang", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrLang (a, b))
  | ("strlangdir", a::b::c::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_StrLangDir (a, b, c))
  | ("concat", uu___) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Concat args)
  | ("coalesce", uu___) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Coalesce args)
  | ("sameTerm", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_SameTerm (a, b))
  | ("if", a::b::c::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_If (a, b, c))
  | ("substr", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Substr (a, b, FStar_Pervasives_Native.None))
  | ("substr", a::b::c::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Substr (a, b, (FStar_Pervasives_Native.Some c)))
  | ("replace", a::b::c::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Replace (a, b, c, FStar_Pervasives_Native.None))
  | ("replace", a::b::c::d::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Replace
           (a, b, c, (FStar_Pervasives_Native.Some d)))
  | ("regex", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Regex (a, b, FStar_Pervasives_Native.None))
  | ("regex", a::b::c::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Regex (a, b, (FStar_Pervasives_Native.Some c)))
  | ("year", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Year a)
  | ("month", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Month a)
  | ("day", a::[]) -> FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Day a)
  | ("hours", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Hours a)
  | ("minutes", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Minutes a)
  | ("seconds", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Seconds a)
  | ("timezone", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Timezone a)
  | ("tz", a::[]) -> FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Tz a)
  | ("md5", a::[]) -> FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_MD5 a)
  | ("sha1", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_SHA1 a)
  | ("sha256", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_SHA256 a)
  | ("sha384", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_SHA384 a)
  | ("sha512", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_SHA512 a)
  | ("logical-not", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Not a)
  | ("unary-minus", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_UnaryMinus a)
  | ("unary-plus", a::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_UnaryPlus a)
  | ("logical-and", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_And (a, b))
  | ("logical-or", a::b::[]) ->
      FStar_Pervasives_Native.Some (SPARQL11_Algebra.E_Or (a, b))
  | ("divide", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Div, a, b))
  | ("multiply", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Mul, a, b))
  | ("plus", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Add, a, b))
  | ("subtract", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Arith (SPARQL11_Algebra.Sub, a, b))
  | ("equals", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Compare (SPARQL11_Algebra.CmpEq, a, b))
  | ("sameValue", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Compare (SPARQL11_Algebra.CmpEq, a, b))
  | ("not-equals", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Compare (SPARQL11_Algebra.CmpNe, a, b))
  | ("greater-than", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Compare (SPARQL11_Algebra.CmpGt, a, b))
  | ("greater-than-or-equal", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Compare (SPARQL11_Algebra.CmpGe, a, b))
  | ("less-than", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Compare (SPARQL11_Algebra.CmpLt, a, b))
  | ("less-than-or-equal", a::b::[]) ->
      FStar_Pervasives_Native.Some
        (SPARQL11_Algebra.E_Compare (SPARQL11_Algebra.CmpLe, a, b))
  | (uu___, uu___1) -> FStar_Pervasives_Native.None
let canon_decimal (t : RDF_Term.rdf_term) : RDF_Term.rdf_term=
  match t with
  | RDF_Term.T_Literal l ->
      if
        (l.RDF_Term.datatype = RDF_Term.xsd_decimal) &&
          (Prims.op_Negation
             (FStar_List_Tot_Base.mem 46
                (FStar_String.list_of_string l.RDF_Term.lexical_form)))
      then
        RDF_Term.T_Literal
          {
            RDF_Term.lexical_form =
              (FStar_String.concat "" [l.RDF_Term.lexical_form; ".0"]);
            RDF_Term.datatype = (l.RDF_Term.datatype);
            RDF_Term.lang_tag = (l.RDF_Term.lang_tag);
            RDF_Term.direction = (l.RDF_Term.direction)
          }
      else t
  | uu___ -> t
let ne_uuid_iri : RDF_Term.wf_iri=
  "urn:uuid:00000000-0000-0000-0000-000000000000"
let is_digit (c : FStar_Char.char) : Prims.bool=
  let n = FStar_Char.int_of_char c in
  (n >= (Prims.of_int (48))) && (n <= (Prims.of_int (57)))
let rec after_char (c : FStar_Char.char) (cs : FStar_Char.char Prims.list) :
  FStar_Char.char Prims.list=
  match cs with | [] -> [] | x::r -> if x = c then r else after_char c r
let rec take_while_lc (p : FStar_Char.char -> Prims.bool)
  (cs : FStar_Char.char Prims.list) : FStar_Char.char Prims.list=
  match cs with
  | c::r -> if p c then c :: (take_while_lc p r) else []
  | [] -> []
let extract_seconds_field (s : Prims.string) : Prims.string=
  let cs = FStar_String.list_of_string s in
  let secs =
    take_while_lc is_digit (after_char 58 (after_char 58 (after_char 84 cs))) in
  match secs with | [] -> "0" | uu___ -> FStar_String.string_of_list secs
let str_starts_with (s : Prims.string) (pfx : Prims.string) : Prims.bool=
  let n = FStar_String.strlen pfx in
  ((FStar_String.strlen s) >= n) &&
    ((FStar_String.sub s Prims.int_zero n) = pfx)
let lang_matches (tag : Prims.string) (range : Prims.string) : Prims.bool=
  if range = "*"
  then (FStar_String.strlen tag) > Prims.int_zero
  else
    (tag = range) ||
      (str_starts_with tag (FStar_String.concat "" [range; "-"]))
let sparql_apply (ln : Prims.string) (argvals : RDF_Term.rdf_term Prims.list)
  : RDF_Term.rdf_term Prims.list=
  match (ln, argvals) with
  | ("isBlank", t::[]) -> [mk_bool_lit (RDF_Term.uu___is_T_BNode t)]
  | ("bnode", uu___) -> [RDF_Term.T_BNode "ne_bnode0"]
  | ("uuid", uu___) -> [RDF_Term.T_IRI ne_uuid_iri]
  | ("struuid", uu___) ->
      [RDF_Term.T_Literal
         (SPARQL11_Algebra.mk_plain_literal
            "00000000-0000-0000-0000-000000000000")]
  | ("langMatches", a::b::[]) ->
      [mk_bool_lit (lang_matches (term_render a) (term_render b))]
  | ("seconds", (RDF_Term.T_Literal l)::[]) ->
      [RDF_Term.T_Literal
         {
           RDF_Term.lexical_form =
             (extract_seconds_field l.RDF_Term.lexical_form);
           RDF_Term.datatype = RDF_Term.xsd_decimal;
           RDF_Term.lang_tag = FStar_Pervasives_Native.None;
           RDF_Term.direction = FStar_Pervasives_Native.None
         }]
  | ("bound", uu___) -> [mk_bool_lit (Prims.uu___is_Cons argvals)]
  | (uu___, uu___1) ->
      (match sparql_fn_expr ln (FStar_List_Tot_Base.map term_to_expr argvals)
       with
       | FStar_Pervasives_Native.Some e ->
           (match SPARQL11_Algebra.er_to_term
                    (SPARQL11_Algebra.eval_expr_with_base
                       FStar_Pervasives_Native.None e
                       SPARQL11_Algebra.sm_empty)
            with
            | FStar_Pervasives_Native.Some t -> [canon_decimal t]
            | FStar_Pervasives_Native.None -> [])
       | FStar_Pervasives_Native.None -> [])
let rec eval_ne (g : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term FStar_Pervasives_Native.option)
  (scope : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (expr : RDF_Term.rdf_term) (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  if fuel = Prims.int_zero
  then []
  else
    (let fuel' = fuel - Prims.int_one in
     match RDF_Graph.term_to_subject expr with
     | FStar_Pervasives_Native.None -> [expr]
     | FStar_Pervasives_Native.Some es ->
         let start_nodes =
           match RDF_Graph_Executable.find_objects g es shnex_focusNode with
           | fe::uu___1 -> eval_ne g focus scope fe fuel'
           | [] ->
               (match focus with
                | FStar_Pervasives_Native.Some f -> [f]
                | FStar_Pervasives_Native.None -> []) in
         let base =
           match RDF_Graph_Executable.find_objects g es shnex_var with
           | (RDF_Term.T_Literal l)::uu___1 ->
               if l.RDF_Term.lexical_form = "focusNode"
               then
                 (match focus with
                  | FStar_Pervasives_Native.Some f -> [f]
                  | FStar_Pervasives_Native.None -> [])
               else
                 (match FStar_List_Tot_Base.find
                          (fun uu___3 ->
                             match uu___3 with
                             | (n, uu___4) -> n = l.RDF_Term.lexical_form)
                          scope
                  with
                  | FStar_Pervasives_Native.Some (uu___3, t) -> [t]
                  | FStar_Pervasives_Native.None -> [])
           | uu___1 ->
               (match RDF_Graph_Executable.find_objects g es shnex_pathValues
                with
                | p::uu___2 ->
                    FStar_List_Tot_Base.concatMap
                      (fun st ->
                         SHACL_Validation.eval_path g st
                           (SHACL_Validation.parse_path g p fuel'))
                      start_nodes
                | [] ->
                    (match RDF_Graph_Executable.find_objects g es shnex_nodes
                     with
                     | l::uu___2 -> eval_ne g focus scope l fuel'
                     | [] ->
                         (match RDF_Graph_Executable.find_objects g es
                                  shnex_concat
                          with
                          | l::uu___2 ->
                              eval_ne_list g focus scope
                                (SHACL_Validation.rdf_list_terms g l fuel')
                                fuel'
                          | [] ->
                              (match RDF_Graph_Executable.find_objects g es
                                       shnex_distinct
                               with
                               | e::uu___2 ->
                                   SHACL_Validation.dedup_terms
                                     (eval_ne g focus scope e fuel')
                               | [] ->
                                   (match RDF_Graph_Executable.find_objects g
                                            es shnex_count
                                    with
                                    | e::uu___2 ->
                                        [mk_int_lit
                                           (FStar_List_Tot_Base.length
                                              (eval_ne g focus scope e fuel'))]
                                    | [] ->
                                        (match RDF_Graph_Executable.find_objects
                                                 g es shnex_exists
                                         with
                                         | e::uu___2 ->
                                             [mk_bool_lit
                                                (Prims.uu___is_Cons
                                                   (eval_ne g focus scope e
                                                      fuel'))]
                                         | [] ->
                                             (match RDF_Graph_Executable.find_objects
                                                      g es shnex_if
                                              with
                                              | c::uu___2 ->
                                                  if
                                                    ne_ebv
                                                      (eval_ne g focus scope
                                                         c fuel')
                                                  then
                                                    (match RDF_Graph_Executable.find_objects
                                                             g es shnex_then
                                                     with
                                                     | t::uu___3 ->
                                                         eval_ne g focus
                                                           scope t fuel'
                                                     | [] -> [])
                                                  else
                                                    (match RDF_Graph_Executable.find_objects
                                                             g es shnex_else
                                                     with
                                                     | e::uu___4 ->
                                                         eval_ne g focus
                                                           scope e fuel'
                                                     | [] -> [])
                                              | [] ->
                                                  (match RDF_Graph_Executable.find_objects
                                                           g es shnex_sum
                                                   with
                                                   | e::uu___2 ->
                                                       sum_expr
                                                         (eval_ne g focus
                                                            scope e fuel')
                                                   | [] ->
                                                       (match RDF_Graph_Executable.find_objects
                                                                g es
                                                                shnex_min
                                                        with
                                                        | e::uu___2 ->
                                                            min_expr
                                                              (eval_ne g
                                                                 focus scope
                                                                 e fuel')
                                                        | [] ->
                                                            (match RDF_Graph_Executable.find_objects
                                                                    g es
                                                                    shnex_max
                                                             with
                                                             | e::uu___2 ->
                                                                 max_expr
                                                                   (eval_ne g
                                                                    focus
                                                                    scope e
                                                                    fuel')
                                                             | [] ->
                                                                 (match 
                                                                    RDF_Graph_Executable.find_objects
                                                                    g es
                                                                    shnex_intersection
                                                                  with
                                                                  | l::uu___2
                                                                    ->
                                                                    SHACL_Validation.dedup_terms
                                                                    (eval_ne_intersect
                                                                    g focus
                                                                    scope
                                                                    (SHACL_Validation.rdf_list_terms
                                                                    g l fuel')
                                                                    fuel')
                                                                  | [] ->
                                                                    (match 
                                                                    RDF_Graph_Executable.find_objects
                                                                    g es
                                                                    shnex_nodesMatching
                                                                    with
                                                                    | 
                                                                    s::uu___2
                                                                    ->
                                                                    SHACL_Validation.dedup_terms
                                                                    (FStar_List_Tot_Base.filter
                                                                    (fun v ->
                                                                    node_conforms
                                                                    g s v)
                                                                    (FStar_List_Tot_Base.map
                                                                    RDF_Graph.subject_to_term
                                                                    (SHACL_Validation.distinct_subjects
                                                                    g)))
                                                                    | 
                                                                    [] ->
                                                                    (match 
                                                                    sparql_call_of
                                                                    g es
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (ln,
                                                                    arglist)
                                                                    ->
                                                                    sparql_apply
                                                                    ln
                                                                    (eval_ne_argvals
                                                                    g focus
                                                                    scope
                                                                    (SHACL_Validation.rdf_list_terms
                                                                    g arglist
                                                                    fuel')
                                                                    fuel')
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (match 
                                                                    RDF_Graph_Executable.find_objects
                                                                    g es
                                                                    shnex_instancesOf
                                                                    with
                                                                    | 
                                                                    (RDF_Term.T_IRI
                                                                    c)::uu___2
                                                                    ->
                                                                    instances_of
                                                                    g c
                                                                    | 
                                                                    uu___2 ->
                                                                    (match 
                                                                    RDF_Graph_Executable.find_objects
                                                                    g es
                                                                    OWL_Closure.rdf_first
                                                                    with
                                                                    | 
                                                                    uu___3::uu___4
                                                                    ->
                                                                    eval_ne_list
                                                                    g focus
                                                                    scope
                                                                    (SHACL_Validation.rdf_list_terms
                                                                    g expr
                                                                    fuel')
                                                                    fuel'
                                                                    | 
                                                                    [] ->
                                                                    (match expr
                                                                    with
                                                                    | 
                                                                    RDF_Term.T_BNode
                                                                    uu___3 ->
                                                                    []
                                                                    | 
                                                                    uu___3 ->
                                                                    [expr])))))))))))))))) in
         let after_flatmap =
           match RDF_Graph_Executable.find_objects g es shnex_flatMap with
           | m::uu___1 -> eval_ne_flatmap g scope m base fuel'
           | [] -> base in
         let after_remove =
           match RDF_Graph_Executable.find_objects g es shnex_remove with
           | r::uu___1 ->
               let rm = eval_ne g focus scope r fuel' in
               FStar_List_Tot_Base.filter
                 (fun x -> Prims.op_Negation (term_mem x rm)) after_flatmap
           | [] -> after_flatmap in
         let after_orderby =
           match RDF_Graph_Executable.find_objects g es shnex_orderBy with
           | k::uu___1 ->
               let desc =
                 match SHACL_Validation.first_bool
                         (RDF_Graph_Executable.find_objects g es shnex_desc)
                 with
                 | FStar_Pervasives_Native.Some true -> true
                 | uu___2 -> false in
               let keyed = eval_ne_keyed g scope k after_remove fuel' in
               let sorted =
                 FStar_List_Tot_Base.sortWith
                   (fun p1 p2 ->
                      term_cmp (FStar_Pervasives_Native.snd p1)
                        (FStar_Pervasives_Native.snd p2)) keyed in
               let ordered =
                 FStar_List_Tot_Base.map
                   (fun p -> FStar_Pervasives_Native.fst p) sorted in
               if desc then FStar_List_Tot_Base.rev ordered else ordered
           | [] -> after_remove in
         let after_filter =
           match RDF_Graph_Executable.find_objects g es shnex_filterShape
           with
           | s::uu___1 ->
               FStar_List_Tot_Base.filter (fun v -> node_conforms g s v)
                 after_orderby
           | [] -> after_orderby in
         let after_matchall =
           match RDF_Graph_Executable.find_objects g es shnex_matchAll with
           | s::uu___1 ->
               [mk_bool_lit
                  (FStar_List_Tot_Base.for_all (fun v -> node_conforms g s v)
                     after_filter)]
           | [] -> after_filter in
         let after_findfirst =
           match RDF_Graph_Executable.find_objects g es shnex_findFirst with
           | s::uu___1 ->
               (match FStar_List_Tot_Base.find (fun v -> node_conforms g s v)
                        after_matchall
                with
                | FStar_Pervasives_Native.Some v -> [v]
                | FStar_Pervasives_Native.None -> [])
           | [] -> after_matchall in
         let after_offset =
           match SHACL_Validation.first_int
                   (RDF_Graph_Executable.find_objects g es shnex_offset)
           with
           | FStar_Pervasives_Native.Some n -> list_drop n after_findfirst
           | FStar_Pervasives_Native.None -> after_findfirst in
         (match SHACL_Validation.first_int
                  (RDF_Graph_Executable.find_objects g es shnex_limit)
          with
          | FStar_Pervasives_Native.Some n -> list_take n after_offset
          | FStar_Pervasives_Native.None -> after_offset))
and eval_ne_list (g : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term FStar_Pervasives_Native.option)
  (scope : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (es : RDF_Term.rdf_term Prims.list) (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  match es with
  | [] -> []
  | e::rest ->
      FStar_List_Tot_Base.op_At (eval_ne g focus scope e fuel)
        (eval_ne_list g focus scope rest fuel)
and eval_ne_intersect (g : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term FStar_Pervasives_Native.option)
  (scope : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (members : RDF_Term.rdf_term Prims.list) (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  match members with
  | [] -> []
  | m::[] -> eval_ne g focus scope m fuel
  | m::rest ->
      let hd = eval_ne g focus scope m fuel in
      let tl = eval_ne_intersect g focus scope rest fuel in
      FStar_List_Tot_Base.filter (fun x -> term_mem x tl) hd
and eval_ne_flatmap (g : RDF_Graph.rdf_graph)
  (scope : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (mapper : RDF_Term.rdf_term) (elems : RDF_Term.rdf_term Prims.list)
  (fuel : Prims.nat) : RDF_Term.rdf_term Prims.list=
  match elems with
  | [] -> []
  | el::rest ->
      FStar_List_Tot_Base.op_At
        (eval_ne g (FStar_Pervasives_Native.Some el) scope mapper fuel)
        (eval_ne_flatmap g scope mapper rest fuel)
and eval_ne_keyed (g : RDF_Graph.rdf_graph)
  (scope : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (keyexpr : RDF_Term.rdf_term) (elems : RDF_Term.rdf_term Prims.list)
  (fuel : Prims.nat) : (RDF_Term.rdf_term * RDF_Term.rdf_term) Prims.list=
  match elems with
  | [] -> []
  | el::rest ->
      let k =
        match eval_ne g (FStar_Pervasives_Native.Some el) scope keyexpr fuel
        with
        | kk::uu___ -> kk
        | [] ->
            RDF_Term.T_Literal
              {
                RDF_Term.lexical_form = "";
                RDF_Term.datatype = RDF_Term.xsd_string;
                RDF_Term.lang_tag = FStar_Pervasives_Native.None;
                RDF_Term.direction = FStar_Pervasives_Native.None
              } in
      (el, k) :: (eval_ne_keyed g scope keyexpr rest fuel)
and eval_ne_argvals (g : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term FStar_Pervasives_Native.option)
  (scope : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (argexprs : RDF_Term.rdf_term Prims.list) (fuel : Prims.nat) :
  RDF_Term.rdf_term Prims.list=
  match argexprs with
  | [] -> []
  | a::rest ->
      FStar_List_Tot_Base.op_At
        (match eval_ne g focus scope a fuel with | v::uu___ -> [v] | [] -> [])
        (eval_ne_argvals g focus scope rest fuel)
let eval_node_expr_top (g : RDF_Graph.rdf_graph)
  (focus : RDF_Term.rdf_term FStar_Pervasives_Native.option)
  (scope : (Prims.string * RDF_Term.rdf_term) Prims.list)
  (expr : RDF_Term.rdf_term) : RDF_Term.rdf_term Prims.list=
  eval_ne g focus scope expr ((RDF_Graph.graph_len g) + (Prims.of_int (100)))
