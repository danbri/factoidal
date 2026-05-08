open Prims
type rif_var = {
  var_name: Prims.string }
let __proj__Mkrif_var__item__var_name (projectee : rif_var) : Prims.string=
  match projectee with | { var_name;_} -> var_name
type rif_term =
  | RIF_Var of rif_var 
  | RIF_Const of RDF_Graph_Executable.rdf_term 
let uu___is_RIF_Var (projectee : rif_term) : Prims.bool=
  match projectee with | RIF_Var _0 -> true | uu___ -> false
let __proj__RIF_Var__item___0 (projectee : rif_term) : rif_var=
  match projectee with | RIF_Var _0 -> _0
let uu___is_RIF_Const (projectee : rif_term) : Prims.bool=
  match projectee with | RIF_Const _0 -> true | uu___ -> false
let __proj__RIF_Const__item___0 (projectee : rif_term) :
  RDF_Graph_Executable.rdf_term= match projectee with | RIF_Const _0 -> _0
type rif_atom =
  | RIF_Triple of rif_term * rif_term * rif_term 
  | RIF_Frame of rif_term * rif_term * rif_term 
  | RIF_Member of rif_term * rif_term 
  | RIF_Sub of rif_term * rif_term 
let uu___is_RIF_Triple (projectee : rif_atom) : Prims.bool=
  match projectee with | RIF_Triple (_0, _1, _2) -> true | uu___ -> false
let __proj__RIF_Triple__item___0 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Triple (_0, _1, _2) -> _0
let __proj__RIF_Triple__item___1 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Triple (_0, _1, _2) -> _1
let __proj__RIF_Triple__item___2 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Triple (_0, _1, _2) -> _2
let uu___is_RIF_Frame (projectee : rif_atom) : Prims.bool=
  match projectee with | RIF_Frame (_0, _1, _2) -> true | uu___ -> false
let __proj__RIF_Frame__item___0 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Frame (_0, _1, _2) -> _0
let __proj__RIF_Frame__item___1 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Frame (_0, _1, _2) -> _1
let __proj__RIF_Frame__item___2 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Frame (_0, _1, _2) -> _2
let uu___is_RIF_Member (projectee : rif_atom) : Prims.bool=
  match projectee with | RIF_Member (_0, _1) -> true | uu___ -> false
let __proj__RIF_Member__item___0 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Member (_0, _1) -> _0
let __proj__RIF_Member__item___1 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Member (_0, _1) -> _1
let uu___is_RIF_Sub (projectee : rif_atom) : Prims.bool=
  match projectee with | RIF_Sub (_0, _1) -> true | uu___ -> false
let __proj__RIF_Sub__item___0 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Sub (_0, _1) -> _0
let __proj__RIF_Sub__item___1 (projectee : rif_atom) : rif_term=
  match projectee with | RIF_Sub (_0, _1) -> _1
type rif_body =
  | RIF_BodyAtom of rif_atom 
  | RIF_BodyAnd of rif_body Prims.list 
let uu___is_RIF_BodyAtom (projectee : rif_body) : Prims.bool=
  match projectee with | RIF_BodyAtom _0 -> true | uu___ -> false
let __proj__RIF_BodyAtom__item___0 (projectee : rif_body) : rif_atom=
  match projectee with | RIF_BodyAtom _0 -> _0
let uu___is_RIF_BodyAnd (projectee : rif_body) : Prims.bool=
  match projectee with | RIF_BodyAnd _0 -> true | uu___ -> false
let __proj__RIF_BodyAnd__item___0 (projectee : rif_body) :
  rif_body Prims.list= match projectee with | RIF_BodyAnd _0 -> _0
type rif_rule =
  {
  rule_name: Prims.string FStar_Pervasives_Native.option ;
  head: rif_atom ;
  body: rif_body }
let __proj__Mkrif_rule__item__rule_name (projectee : rif_rule) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { rule_name; head; body;_} -> rule_name
let __proj__Mkrif_rule__item__head (projectee : rif_rule) : rif_atom=
  match projectee with | { rule_name; head; body;_} -> head
let __proj__Mkrif_rule__item__body (projectee : rif_rule) : rif_body=
  match projectee with | { rule_name; head; body;_} -> body
type rif_program = {
  rules: rif_rule Prims.list }
let __proj__Mkrif_program__item__rules (projectee : rif_program) :
  rif_rule Prims.list= match projectee with | { rules;_} -> rules
let mk_var (n : Prims.string) : rif_term= RIF_Var { var_name = n }
let mk_const (t : RDF_Graph_Executable.rdf_term) : rif_term= RIF_Const t
let mk_const_iri (i : RDF_Graph_Executable.wf_iri) : rif_term=
  RIF_Const (RDF_Graph_Executable.T_IRI i)
let mk_atom_triple (s : rif_term) (p : rif_term) (o : rif_term) : rif_atom=
  RIF_Triple (s, p, o)
let mk_atom_frame (o : rif_term) (p : rif_term) (v : rif_term) : rif_atom=
  RIF_Frame (o, p, v)
let mk_atom_member (o : rif_term) (c : rif_term) : rif_atom=
  RIF_Member (o, c)
let mk_atom_sub (sub : rif_term) (sup_ : rif_term) : rif_atom=
  RIF_Sub (sub, sup_)
let mk_body_atom (a : rif_atom) : rif_body= RIF_BodyAtom a
let mk_body_and (bs : rif_body Prims.list) : rif_body= RIF_BodyAnd bs
let mk_rule (head_ : rif_atom) (body_ : rif_body) : rif_rule=
  { rule_name = FStar_Pervasives_Native.None; head = head_; body = body_ }
let mk_named_rule (n : Prims.string) (head_ : rif_atom) (body_ : rif_body) :
  rif_rule=
  { rule_name = (FStar_Pervasives_Native.Some n); head = head_; body = body_
  }
let empty_program : rif_program= { rules = [] }
let program_of_rules (rs : rif_rule Prims.list) : rif_program= { rules = rs }
let rif_var_eq (a : rif_var) (b : rif_var) : Prims.bool=
  a.var_name = b.var_name
let rif_term_eq (a : rif_term) (b : rif_term) : Prims.bool=
  match (a, b) with
  | (RIF_Var v1, RIF_Var v2) -> rif_var_eq v1 v2
  | (RIF_Const c1, RIF_Const c2) -> RDF_Graph_Executable.rdf_term_eq c1 c2
  | (uu___, uu___1) -> false
let rif_atom_eq (a : rif_atom) (b : rif_atom) : Prims.bool=
  match (a, b) with
  | (RIF_Triple (s1, p1, o1), RIF_Triple (s2, p2, o2)) ->
      ((rif_term_eq s1 s2) && (rif_term_eq p1 p2)) && (rif_term_eq o1 o2)
  | (RIF_Frame (o1, p1, v1), RIF_Frame (o2, p2, v2)) ->
      ((rif_term_eq o1 o2) && (rif_term_eq p1 p2)) && (rif_term_eq v1 v2)
  | (RIF_Member (o1, c1), RIF_Member (o2, c2)) ->
      (rif_term_eq o1 o2) && (rif_term_eq c1 c2)
  | (RIF_Sub (sub1, sup1), RIF_Sub (sub2, sup2)) ->
      (rif_term_eq sub1 sub2) && (rif_term_eq sup1 sup2)
  | (uu___, uu___1) -> false
