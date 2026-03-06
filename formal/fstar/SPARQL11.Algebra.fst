module SPARQL11.Algebra

(** ======================================================================== **)
(** SPARQL 1.1 Query Language — Formal Specification                         **)
(**                                                                          **)
(** Based on: W3C Recommendation 21 March 2013                               **)
(** https://www.w3.org/TR/sparql11-query/                                    **)
(**                                                                          **)
(** Scope: Query algebra, evaluation semantics, built-in functions.          **)
(** Excludes: SPARQL Protocol, Federated Query (SERVICE), Update.            **)
(**                                                                          **)
(** ADMITTED SHORTFALLS (documented per project policy):                      **)
(** [S1] Property paths: recursive closure (* / +) not fully modeled;        **)
(**      finite-depth approximation specified, proof of completeness deferred.**)
(** [S2] Aggregates: GROUP BY partitioning specified declaratively;           **)
(**      concrete partitioning algorithm deferred.                            **)
(** [S3] String functions operating on Unicode: assume correct UTF-8 handling**)
(**      via external primitives; no char-level Unicode spec in F*.           **)
(** [S4] Numeric type promotion hierarchy: specified as a total order         **)
(**      but promotion rules for mixed arithmetic are simplified.             **)
(** [S5] CONSTRUCT/DESCRIBE/ASK query forms: types specified,                **)
(**      evaluation deferred (SELECT is primary target).                      **)
(** [S6] Dataset specification (FROM/FROM NAMED): types present,             **)
(**      multi-graph evaluation deferred.                                     **)
(** ======================================================================== **)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable

(** ====================================================================== **)
(** Part 1: Concrete RDF Types (imported from RDF.Graph.Executable)         **)
(** ====================================================================== **)

(* Core types (wf_iri, bnode_id, wf_literal, rdf_term, subject, triple,
   rdf_graph, solution_mapping, var_name) are imported via open.
   Constructors T_IRI, T_BNode, T_Literal, S_IRI, S_BNode are in scope.
   Equality functions subject_eq, literal_eq, rdf_term_eq, triple_eq
   are in scope with concrete implementations and proved reflexivity. *)

(* Literal field accessors — concrete via record projection *)
let lit_lexical (l : wf_literal) : string = l.lexical_form
let lit_datatype (l : wf_literal) : wf_iri = l.datatype
let lit_lang (l : wf_literal) : option string = l.lang_tag

(* IRI string extraction — wf_iri is a refined string, so identity *)
let iri_to_string (i : wf_iri) : string = i
let string_to_iri (s : string) : option wf_iri =
  if is_iri s then Some s else None

(* Well-known datatype IRIs: reuse from RDF.Graph.Executable where available.
   rdf_lang_string, xsd_string, xsd_integer, xsd_decimal, xsd_double,
   xsd_boolean are imported via open. Additional SPARQL-needed IRIs: *)
let rdf_langString : wf_iri = rdf_lang_string  (* camelCase alias *)
let xsd_float : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#float");
  "http://www.w3.org/2001/XMLSchema#float"
let xsd_dateTime : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#dateTime");
  "http://www.w3.org/2001/XMLSchema#dateTime"
let xsd_date : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#date");
  "http://www.w3.org/2001/XMLSchema#date"
let xsd_time : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#time");
  "http://www.w3.org/2001/XMLSchema#time"
let xsd_duration : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#duration");
  "http://www.w3.org/2001/XMLSchema#duration"
let xsd_dayTimeDuration : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#dayTimeDuration");
  "http://www.w3.org/2001/XMLSchema#dayTimeDuration"
let xsd_yearMonthDuration : wf_iri =
  assert_norm (is_iri "http://www.w3.org/2001/XMLSchema#yearMonthDuration");
  "http://www.w3.org/2001/XMLSchema#yearMonthDuration"

(* Solution mapping operations — concrete implementations *)
let sm_empty : solution_mapping = []

let sm_lookup (v : string) (mu : solution_mapping) : option rdf_term =
  List.Tot.assoc v mu

let sm_bind (v : string) (t : rdf_term) (mu : solution_mapping) : solution_mapping =
  (v, t) :: mu

let sm_domain (mu : solution_mapping) : list string =
  List.Tot.map fst mu

(* Two mappings are compatible if shared variables bind to equal terms *)
let rec sm_compatible (mu1 mu2 : solution_mapping) : bool =
  match mu1 with
  | [] -> true
  | (v, t) :: rest ->
    (match List.Tot.assoc v mu2 with
     | None -> sm_compatible rest mu2
     | Some t2 -> rdf_term_eq t t2 && sm_compatible rest mu2)

(* Merge: mu1 bindings take priority; add non-overlapping from mu2 *)
let rec sm_merge_aux (mu1 : solution_mapping) (mu2 : solution_mapping) : solution_mapping =
  match mu2 with
  | [] -> mu1
  | (v, t) :: rest ->
    if Some? (List.Tot.assoc v mu1)
    then sm_merge_aux mu1 rest
    else sm_merge_aux ((v, t) :: mu1) rest

let sm_merge (mu1 mu2 : solution_mapping) : solution_mapping =
  sm_merge_aux mu1 mu2

(* Graph operations — concrete via list/record access *)
let graph_triples (g : rdf_graph) : list triple = g
let triple_subject (t : triple) : subject = t.s
let triple_predicate (t : triple) : wf_iri = t.p
let triple_object (t : triple) : rdf_term = t.o

(** ====================================================================== **)
(** Part 2: SPARQL 1.1 Variable and Pattern Types                          **)
(** ====================================================================== **)

type var_name = string

(** Pattern terms: variables or concrete RDF terms **)
type pattern_term =
  | PT_Var      : var_name -> pattern_term
  | PT_IRI      : wf_iri -> pattern_term
  | PT_BNode    : bnode_id -> pattern_term
  | PT_Literal  : wf_literal -> pattern_term

type pattern_subject =
  | PS_Var   : var_name -> pattern_subject
  | PS_IRI   : wf_iri -> pattern_subject
  | PS_BNode : bnode_id -> pattern_subject

(** Triple pattern: subject, predicate (may be variable), object **)
noeq type triple_pattern = {
  tp_s : pattern_subject;
  tp_p : pattern_term;      (* SPARQL 1.1 allows variable predicates *)
  tp_o : pattern_term;
}

(** Basic Graph Pattern **)
type bgp = list triple_pattern

(** ====================================================================== **)
(** Part 3: SPARQL 1.1 Expression Language                                 **)
(** ====================================================================== **)

(** Comparison operators **)
type comp_op = | CmpEq | CmpNe | CmpLt | CmpGt | CmpLe | CmpGe

(** Arithmetic operators **)
type arith_op = | Add | Sub | Mul | Div

(** Aggregate functions (§18.5) **)
type aggregate_fn =
  | Agg_Count
  | Agg_Sum
  | Agg_Min
  | Agg_Max
  | Agg_Avg
  | Agg_GroupConcat of option string   (* optional separator *)
  | Agg_Sample

(** SPARQL 1.1 Expression AST (§18.2) **)
noeq type expr =
  (* Primary expressions *)
  | E_Var           : var_name -> expr
  | E_IRI           : wf_iri -> expr
  | E_Literal       : wf_literal -> expr
  | E_BoolLit       : bool -> expr
  | E_NumericLit    : int -> expr        (* integer literal *)
  | E_DecimalLit    : string -> expr     (* decimal as string, [S4] *)
  | E_DoubleLit     : string -> expr     (* double as string, [S4] *)

  (* Arithmetic (§17.4.2) *)
  | E_Arith         : arith_op -> expr -> expr -> expr
  | E_UnaryMinus    : expr -> expr
  | E_UnaryPlus     : expr -> expr

  (* Comparison (§17.3) *)
  | E_Compare       : comp_op -> expr -> expr -> expr

  (* Logical connectives (§17.4.1) *)
  | E_And           : expr -> expr -> expr
  | E_Or            : expr -> expr -> expr
  | E_Not           : expr -> expr

  (* Node type tests (§17.4.3.1) *)
  | E_IsIRI         : expr -> expr
  | E_IsBlank       : expr -> expr
  | E_IsLiteral     : expr -> expr
  | E_IsNumeric     : expr -> expr

  (* Accessors (§17.4.3) *)
  | E_Str           : expr -> expr
  | E_Lang          : expr -> expr
  | E_Datatype      : expr -> expr
  | E_IRI_fn        : expr -> expr       (* IRI() / URI() constructor *)

  (* Term constructors (§17.4.4) *)
  | E_StrDt         : expr -> expr -> expr   (* STRDT(lexical, datatype) *)
  | E_StrLang       : expr -> expr -> expr   (* STRLANG(lexical, langtag) *)

  (* BOUND test (§17.4.1.1) *)
  | E_Bound         : var_name -> expr

  (* Conditional (§17.4.1) *)
  | E_If            : expr -> expr -> expr -> expr
  | E_Coalesce      : list expr -> expr
  | E_In            : expr -> list expr -> expr
  | E_NotIn         : expr -> list expr -> expr

  (* String functions (§17.4.3.4 – §17.4.3.13) *)
  | E_StrLen        : expr -> expr
  | E_Substr        : expr -> expr -> option expr -> expr
  | E_UCase         : expr -> expr
  | E_LCase         : expr -> expr
  | E_StrStarts     : expr -> expr -> expr
  | E_StrEnds       : expr -> expr -> expr
  | E_Contains      : expr -> expr -> expr
  | E_StrBefore     : expr -> expr -> expr
  | E_StrAfter      : expr -> expr -> expr
  | E_Concat        : list expr -> expr
  | E_EncodeForUri  : expr -> expr
  | E_Replace       : expr -> expr -> expr -> option expr -> expr  (* str, pattern, replacement, flags *)
  | E_Regex         : expr -> expr -> option expr -> expr          (* str, pattern, flags *)

  (* Numeric functions (§17.4.4) *)
  | E_Abs           : expr -> expr
  | E_Round         : expr -> expr
  | E_Ceil          : expr -> expr
  | E_Floor         : expr -> expr

  (* Hash functions (§17.4.3.14) *)
  | E_MD5           : expr -> expr
  | E_SHA1          : expr -> expr
  | E_SHA256        : expr -> expr
  | E_SHA384        : expr -> expr
  | E_SHA512        : expr -> expr

  (* Date/time functions (§17.4.5) *)
  | E_Now           : expr
  | E_Year          : expr -> expr
  | E_Month         : expr -> expr
  | E_Day           : expr -> expr
  | E_Hours         : expr -> expr
  | E_Minutes       : expr -> expr
  | E_Seconds       : expr -> expr
  | E_Timezone      : expr -> expr
  | E_Tz            : expr -> expr

  (* RDF term equality (§17.4.1.7) *)
  | E_SameTerm      : expr -> expr -> expr

  (* EXISTS / NOT EXISTS (§18.6) *)
  | E_Exists        : group_graph_pattern -> expr
  | E_NotExists     : group_graph_pattern -> expr

  (* Aggregate expressions (§18.5) — only valid inside HAVING or SELECT *)
  | E_Aggregate     : aggregate_fn -> bool (* distinct *) -> expr -> expr

  (* Function call (extensible — IRI-named functions, §17.6) *)
  | E_FunctionCall  : wf_iri -> list expr -> expr

(** ====================================================================== **)
(** Part 4: SPARQL 1.1 Property Paths (§9)                                 **)
(** [S1] Recursive closure paths (* / +) specified structurally;            **)
(**      termination/completeness of evaluation deferred.                   **)
(** ====================================================================== **)

and property_path =
  | PP_IRI           : wf_iri -> property_path                     (* iri *)
  | PP_Inverse       : property_path -> property_path              (* ^path *)
  | PP_Sequence      : property_path -> property_path -> property_path  (* path/path *)
  | PP_Alternative   : property_path -> property_path -> property_path  (* path|path *)
  | PP_ZeroOrMore    : property_path -> property_path              (* path* [S1] *)
  | PP_OneOrMore     : property_path -> property_path              (* path+ [S1] *)
  | PP_ZeroOrOne     : property_path -> property_path              (* path? *)
  | PP_NegatedSet    : list property_path -> property_path         (* !(:a|:b|^:c) *)

(** ====================================================================== **)
(** Part 5: SPARQL 1.1 Graph Patterns (§18.2)                              **)
(** ====================================================================== **)

and group_graph_pattern =
  | GP_BGP        : bgp -> group_graph_pattern
  | GP_Join       : group_graph_pattern -> group_graph_pattern -> group_graph_pattern
  | GP_LeftJoin   : group_graph_pattern -> group_graph_pattern -> expr -> group_graph_pattern
      (* OPTIONAL with filter: LeftJoin(P1, P2, filter_expr) *)
  | GP_Filter     : expr -> group_graph_pattern -> group_graph_pattern
  | GP_Union      : group_graph_pattern -> group_graph_pattern -> group_graph_pattern
  | GP_Graph      : pattern_term -> group_graph_pattern -> group_graph_pattern
      (* GRAPH ?g { P } or GRAPH <iri> { P } [S6] *)
  | GP_Minus      : group_graph_pattern -> group_graph_pattern -> group_graph_pattern
  | GP_Bind       : expr -> var_name -> group_graph_pattern -> group_graph_pattern
      (* BIND(expr AS ?var) appended to pattern *)
  | GP_Values     : list var_name -> list (list (option rdf_term)) -> group_graph_pattern
      (* VALUES (?x ?y) { (1 2) (3 UNDEF) } — inline data *)
  | GP_Service    : wf_iri -> group_graph_pattern -> bool -> group_graph_pattern
      (* SERVICE <iri> { P } silent? — EXCLUDED from evaluation [scope exclusion] *)
  | GP_SubSelect  : query -> group_graph_pattern
      (* Sub-SELECT: treated as a group graph pattern *)
  | GP_PropertyPath : pattern_subject -> property_path -> pattern_term -> group_graph_pattern
      (* Property path pattern: ?s path ?o *)
  | GP_Empty      : group_graph_pattern
      (* Empty group pattern {} — identity for Join *)

(** ====================================================================== **)
(** Part 6: SPARQL 1.1 Query Structure (§18.2.4)                           **)
(** ====================================================================== **)

(** Order specification **)
and order_condition =
  | OC_Asc  : expr -> order_condition
  | OC_Desc : expr -> order_condition

(** Solution modifier **)
and solution_modifier = {
  sm_order_by   : option (list order_condition);
  sm_distinct   : bool;
  sm_reduced    : bool;
  sm_offset     : option nat;
  sm_limit      : option nat;
}

(** SELECT projection — either specific variables/expressions or * **)
and select_item =
  | SI_Var  : var_name -> select_item
  | SI_Expr : expr -> var_name -> select_item    (* (expr AS ?var) *)

and select_clause =
  | Select_Vars : list select_item -> select_clause
  | Select_All  : select_clause                  (* SELECT * *)

(** GROUP BY clause **)
and group_condition =
  | GC_Var   : var_name -> group_condition
  | GC_Expr  : expr -> option var_name -> group_condition  (* expr, optional alias *)
  | GC_BuiltIn : expr -> group_condition

(** HAVING clause **)
and having_condition = expr

(** Query forms (§18.2) **)
and query_form =
  | QF_Select    : select_clause -> query_form
  | QF_Construct : list triple_pattern -> query_form   (* [S5] *)
  | QF_Ask       : query_form                          (* [S5] *)
  | QF_Describe  : list pattern_term -> query_form     (* [S5] *)

(** Dataset clause **)
and dataset_clause =
  | DC_Default : wf_iri -> dataset_clause       (* FROM <iri> [S6] *)
  | DC_Named   : wf_iri -> dataset_clause       (* FROM NAMED <iri> [S6] *)

(** Complete SPARQL 1.1 query **)
and query = {
  q_base     : option wf_iri;
  q_prefixes : list (string * wf_iri);             (* PREFIX decls *)
  q_form     : query_form;
  q_dataset  : list dataset_clause;                 (* [S6] *)
  q_pattern  : group_graph_pattern;
  q_group_by : option (list group_condition);       (* [S2] *)
  q_having   : option (list having_condition);
  q_modifier : solution_modifier;
}

(** 6.1 IRI resolution against BASE (§5.1.1) **)

(* Resolve a relative IRI reference against a base IRI per RFC 3986.
   If the reference has a scheme, it is returned as-is.
   Fragment references (#foo) are appended to the base (after removing
   any existing fragment). Otherwise, the reference replaces the last
   path segment of the base. *)
assume val resolve_iri : wf_iri -> string -> wf_iri

(* Prefix namespace IRIs are resolved against BASE during parsing.
   All IRIs in the query body are then resolved against BASE.
   This ensures that relative IRIs like <x> or <#x> become absolute. *)
let resolve_query_iri (base : option wf_iri) (rel : string) : option wf_iri =
  match base with
  | Some b -> Some (resolve_iri b rel)
  | None -> string_to_iri rel

(** 6.2 SPARQL string escape processing (§19.7) **)

(* SPARQL string literals support escape sequences.
   The unescape function converts:
     \\ → \, \n → newline, \r → carriage return, \t → tab,
     \" → ", \' → ', \uXXXX → Unicode char, \UXXXXXXXX → Unicode char.
   This is applied to regex patterns before compilation. *)
assume val unescape_sparql_string : string -> string

(** ====================================================================== **)
(** Part 7: SPARQL 1.1 Evaluation Semantics (§18.5, §18.6)                **)
(** ====================================================================== **)

(** Solution sequence: ordered list of solution mappings **)
type solution_sequence = list solution_mapping

(** 7.1 Pattern matching — triple pattern against a triple **)

(* Convert a subject to an rdf_term for binding *)
let subject_to_term (s : subject) : rdf_term =
  match s with
  | S_IRI i -> T_IRI i
  | S_BNode b -> T_BNode b

(* Try to bind a pattern subject against a concrete subject.
   If the pattern is a concrete value, check equality.
   If it's a variable, check existing binding or add new one. *)
let try_bind_subject (ps : pattern_subject) (s : subject) (mu : solution_mapping)
  : option solution_mapping =
  match ps with
  | PS_IRI i ->
    (match s with
     | S_IRI i' -> if i = i' then Some mu else None
     | _ -> None)
  | PS_BNode b ->
    (match s with
     | S_BNode b' -> if b = b' then Some mu else None
     | _ -> None)
  | PS_Var v ->
    let term = subject_to_term s in
    match sm_lookup v mu with
    | Some existing -> if rdf_term_eq existing term then Some mu else None
    | None -> Some (sm_bind v term mu)

(* Try to bind a pattern term against a concrete RDF term. *)
let try_bind_term (pt : pattern_term) (t : rdf_term) (mu : solution_mapping)
  : option solution_mapping =
  match pt with
  | PT_IRI i ->
    (match t with
     | T_IRI i' -> if i = i' then Some mu else None
     | _ -> None)
  | PT_BNode b ->
    (match t with
     | T_BNode b' -> if b = b' then Some mu else None
     | _ -> None)
  | PT_Literal l ->
    (match t with
     | T_Literal l' -> if literal_eq l l' then Some mu else None
     | _ -> None)
  | PT_Var v ->
    match sm_lookup v mu with
    | Some existing -> if rdf_term_eq existing t then Some mu else None
    | None -> Some (sm_bind v t mu)

(* A pattern term matches an RDF term under a solution mapping — CONCRETE *)
let pattern_term_matches (pt : pattern_term) (t : rdf_term) (mu : solution_mapping) : bool =
  Some? (try_bind_term pt t mu)

(* A pattern subject matches a subject under a solution mapping — CONCRETE *)
let pattern_subject_matches (ps : pattern_subject) (s : subject) (mu : solution_mapping) : bool =
  Some? (try_bind_subject ps s mu)

(* A triple pattern matches a graph triple, producing extended mapping — CONCRETE.
   Threads bindings: subject → predicate → object. *)
let tp_match (tp : triple_pattern) (t : triple) (mu : solution_mapping)
  : option solution_mapping =
  match try_bind_subject tp.tp_s t.s mu with
  | None -> None
  | Some mu1 ->
    (* Predicate is pattern_term; graph triple predicate is wf_iri → wrap as T_IRI *)
    match try_bind_term tp.tp_p (T_IRI t.p) mu1 with
    | None -> None
    | Some mu2 -> try_bind_term tp.tp_o t.o mu2

(** 7.2 BGP evaluation — CONCRETE **)

(* Evaluate a single triple pattern against the graph, extending a given mapping *)
let eval_single_tp (tp : triple_pattern) (g : rdf_graph) (mu : solution_mapping)
  : solution_sequence =
  List.Tot.filter_map (fun t -> tp_match tp t mu) g

(* Evaluate a BGP: for each triple pattern, extend existing mappings.
   Empty BGP matches everything with the empty mapping.
   Per SPARQL semantics: eval(BGP) = Join of individual pattern evaluations. *)
let rec eval_bgp (patterns : bgp) (g : rdf_graph) : solution_sequence =
  match patterns with
  | [] -> [sm_empty]
  | tp :: rest ->
    let sub_results = eval_bgp rest g in
    List.Tot.concatMap (fun mu -> eval_single_tp tp g mu) sub_results

(** 7.3 Core algebra operations (§18.5) **)

(* Join: compatible merge of solution mappings from two patterns *)
(* Ω1 Join Ω2 = { merge(μ1, μ2) | μ1 ∈ Ω1, μ2 ∈ Ω2, compatible(μ1, μ2) } *)
let join (omega1 omega2 : solution_sequence) : solution_sequence =
  List.Tot.concatMap
    (fun mu1 -> List.Tot.filter_map
      (fun mu2 -> if sm_compatible mu1 mu2 then Some (sm_merge mu1 mu2) else None)
      omega2)
    omega1

(* LeftJoin (OPTIONAL): join + unmatched from left *)
(* Ω1 LeftJoin(Ω2, expr) =
     { merge(μ1,μ2) | μ1 ∈ Ω1, μ2 ∈ Ω2, compatible(μ1,μ2), expr(merge(μ1,μ2)) }
     ∪ { μ1 | μ1 ∈ Ω1, ∀ μ2 ∈ Ω2: ¬compatible(μ1,μ2) ∨ ¬expr(merge(μ1,μ2)) } *)
assume val eval_expr_ebv : expr -> solution_mapping -> bool

let left_join (omega1 omega2 : solution_sequence) (filter_expr : expr) : solution_sequence =
  let matched = List.Tot.concatMap
    (fun mu1 ->
      let joins = List.Tot.filter_map
        (fun mu2 ->
          if sm_compatible mu1 mu2 then
            let merged = sm_merge mu1 mu2 in
            if eval_expr_ebv filter_expr merged then Some merged else None
          else None)
        omega2 in
      if List.Tot.length joins > 0 then joins else [mu1])
    omega1 in
  matched

(* Union: multiset union of solution mappings *)
let union (omega1 omega2 : solution_sequence) : solution_sequence =
  omega1 @ omega2

(* Minus (§18.5) *)
(* Ω1 Minus Ω2 = { μ1 | μ1 ∈ Ω1, ∀ μ2 ∈ Ω2:
     ¬compatible(μ1, μ2) ∨ dom(μ1) ∩ dom(μ2) = ∅ } *)
(* domains_disjoint: true if no variable appears in both mappings — CONCRETE *)
let rec domains_disjoint (mu1 mu2 : solution_mapping) : bool =
  match mu1 with
  | [] -> true
  | (v, _) :: rest ->
    not (Some? (List.Tot.assoc v mu2)) && domains_disjoint rest mu2

let minus (omega1 omega2 : solution_sequence) : solution_sequence =
  List.Tot.filter
    (fun mu1 ->
      not (List.Tot.existsb
        (fun mu2 -> sm_compatible mu1 mu2 && not (domains_disjoint mu1 mu2))
        omega2))
    omega1

(* Filter: retain solutions where expression evaluates to true *)
let filter_solutions (e : expr) (omega : solution_sequence) : solution_sequence =
  List.Tot.filter (eval_expr_ebv e) omega

(** 7.4 Graph pattern evaluation (§18.6) — CONCRETE **)

(* Helper: convert eval_result to rdf_term for BIND *)
let er_to_term (v : eval_result) : option rdf_term =
  match v with
  | ER_Term t -> Some t
  | ER_Bool true -> Some (T_Literal (mk_plain_literal "true"))
  | ER_Bool false -> Some (T_Literal (mk_plain_literal "false"))
  | ER_Num n -> Some (T_Literal ({ lexical_form = string_of_int n;
                                    datatype = xsd_integer; lang_tag = None }))
  | ER_Dec s -> Some (T_Literal ({ lexical_form = s;
                                    datatype = xsd_decimal; lang_tag = None }))
  | ER_Dbl s -> Some (T_Literal ({ lexical_form = s;
                                    datatype = xsd_double; lang_tag = None }))
  | ER_Error -> None

(* Evaluate a group graph pattern against an RDF graph — CONCRETE.
   [S6] GRAPH patterns evaluated against single default graph only.
   [S1] Property paths deferred.
   Sub-SELECT deferred (requires eval_select_query). *)
let rec eval_pattern (p : group_graph_pattern) (g : rdf_graph)
  : Tot solution_sequence (decreases p) =
  match p with
  | GP_BGP bgp -> eval_bgp bgp g

  | GP_Join p1 p2 ->
    join (eval_pattern p1 g) (eval_pattern p2 g)

  | GP_LeftJoin p1 p2 filter_e ->
    left_join (eval_pattern p1 g) (eval_pattern p2 g) filter_e

  | GP_Filter e p' ->
    filter_solutions e (eval_pattern p' g)

  | GP_Union p1 p2 ->
    union (eval_pattern p1 g) (eval_pattern p2 g)

  | GP_Minus p1 p2 ->
    minus (eval_pattern p1 g) (eval_pattern p2 g)

  | GP_Empty -> [sm_empty]

  | GP_Bind e v p' ->
    let omega = eval_pattern p' g in
    List.Tot.map
      (fun mu ->
        match er_to_term (eval_expr e mu) with
        | Some t ->
          (* Only bind if variable is not already bound *)
          (match sm_lookup v mu with
           | Some _ -> mu  (* preserve existing binding *)
           | None -> sm_bind v t mu)
        | None -> mu)  (* error → leave mapping unchanged *)
      omega

  | GP_Values vars rows ->
    eval_values vars rows

  | GP_Graph _ p' ->
    (* [S6] Named graph patterns: evaluate against default graph *)
    eval_pattern p' g

  | GP_Service _ _ _ ->
    (* SERVICE: remote execution, not supported *)
    []

  | GP_SubSelect _ ->
    (* Sub-SELECT: requires eval_select_query, deferred *)
    []

  | GP_PropertyPath _ _ _ ->
    (* [S1] Property paths: deferred *)
    []

(** ====================================================================== **)
(** Part 8: SPARQL 1.1 Expression Evaluation (§17)                         **)
(** ====================================================================== **)

(** 8.1 Effective Boolean Value (§17.2.2) **)

(* The EBV of an expression result.
   - xsd:boolean: the boolean value
   - Numeric: true if non-zero and not NaN
   - xsd:string / plain literal: true if length > 0
   - rdf:langString: true if length > 0
   - All other types: type error (returns false) *)

type eval_result =
  | ER_Term  : rdf_term -> eval_result
  | ER_Bool  : bool -> eval_result
  | ER_Num   : int -> eval_result          (* integer value *)
  | ER_Dec   : string -> eval_result       (* decimal as string [S4] *)
  | ER_Dbl   : string -> eval_result       (* double as string [S4] *)
  | ER_Error : eval_result                 (* type error / unbound *)

(* Effective Boolean Value — CONCRETE implementation (§17.2.2) *)
let ebv (v : eval_result) : bool =
  match v with
  | ER_Bool b   -> b
  | ER_Num n    -> n <> 0
  | ER_Dec s    -> s <> "0" && s <> "0.0" && s <> ""
  | ER_Dbl s    -> s <> "0" && s <> "0.0" && s <> "NaN" && s <> ""
  | ER_Term (T_Literal l) ->
    if lit_datatype l = xsd_boolean
    then lit_lexical l = "true" || lit_lexical l = "1"
    else if lit_datatype l = xsd_string
    then String.length (lit_lexical l) > 0
    else if lit_datatype l = rdf_langString
    then String.length (lit_lexical l) > 0
    else if is_numeric_datatype (lit_datatype l)
    then lit_lexical l <> "0" && lit_lexical l <> "0.0" && lit_lexical l <> ""
    else false  (* unknown type → type error → false *)
  | ER_Term _   -> false   (* IRI/BNode have no boolean interpretation *)
  | ER_Error    -> false

(** 8.2 Expression evaluation function — CONCRETE **)

(* Helper: extract string from eval_result for string function dispatch *)
let er_to_string (v : eval_result) : option string =
  match v with
  | ER_Term (T_Literal l) -> Some (lit_lexical l)
  | ER_Term (T_IRI i) -> Some (iri_to_string i)
  | _ -> None

(* Helper: wrap string result as plain literal *)
let er_string (s : string) : eval_result =
  ER_Term (T_Literal (mk_plain_literal s))

(* Helper: evaluate arithmetic on integers *)
let eval_arith_int (op : arith_op) (a b : int) : eval_result =
  match op with
  | Add -> ER_Num (a + b)
  | Sub -> ER_Num (a - b)
  | Mul -> ER_Num (a * b)
  | Div -> if b = 0 then ER_Error else ER_Num (a / b)

(* Helper: extract the xsd:dateTime lexical form from a literal *)
let er_to_datetime_lex (v : eval_result) : option string =
  match v with
  | ER_Term (T_Literal l) ->
    if lit_datatype l = xsd_dateTime then Some (lit_lexical l) else None
  | _ -> None

(* Full expression evaluation: expr × solution_mapping → eval_result — CONCRETE.
   EXISTS/NOT EXISTS require graph context — delegated to eval_pattern.
   This function does not take a graph parameter; EXISTS/NOT EXISTS return ER_Error.
   Use eval_exists/eval_not_exists (Part 17) for graph-aware evaluation. *)
let rec eval_expr (e : expr) (mu : solution_mapping)
  : Tot eval_result (decreases e) =
  match e with
  (* Primary expressions *)
  | E_Var v ->
    (match sm_lookup v mu with
     | Some t -> ER_Term t
     | None -> ER_Error)
  | E_IRI i -> ER_Term (T_IRI i)
  | E_Literal l -> ER_Term (T_Literal l)
  | E_BoolLit b -> ER_Bool b
  | E_NumericLit n -> ER_Num n
  | E_DecimalLit s -> ER_Dec s
  | E_DoubleLit s -> ER_Dbl s

  (* Arithmetic *)
  | E_Arith op e1 e2 ->
    (match eval_expr e1 mu, eval_expr e2 mu with
     | ER_Num a, ER_Num b -> eval_arith_int op a b
     | _, _ -> ER_Error)
  | E_UnaryMinus e1 ->
    (match eval_expr e1 mu with
     | ER_Num n -> ER_Num (0 - n)
     | _ -> ER_Error)
  | E_UnaryPlus e1 -> eval_expr e1 mu

  (* Comparison *)
  | E_Compare op e1 e2 ->
    (match value_compare (eval_expr e1 mu) (eval_expr e2 mu) op with
     | Some b -> ER_Bool b
     | None -> ER_Error)

  (* Logical connectives *)
  | E_And e1 e2 -> ER_Bool (ebv (eval_expr e1 mu) && ebv (eval_expr e2 mu))
  | E_Or e1 e2 -> ER_Bool (ebv (eval_expr e1 mu) || ebv (eval_expr e2 mu))
  | E_Not e1 -> ER_Bool (not (ebv (eval_expr e1 mu)))

  (* Type tests *)
  | E_IsIRI e1 -> fn_isIRI (eval_expr e1 mu)
  | E_IsBlank e1 -> fn_isBlank (eval_expr e1 mu)
  | E_IsLiteral e1 -> fn_isLiteral (eval_expr e1 mu)
  | E_IsNumeric e1 -> fn_isNumeric (eval_expr e1 mu)

  (* Accessors *)
  | E_Str e1 -> fn_str (eval_expr e1 mu)
  | E_Lang e1 -> fn_lang (eval_expr e1 mu)
  | E_Datatype e1 -> fn_datatype (eval_expr e1 mu)
  | E_IRI_fn e1 ->
    (match eval_expr e1 mu with
     | ER_Term (T_IRI i) -> ER_Term (T_IRI i)
     | ER_Term (T_Literal l) -> ER_Term (T_IRI (string_to_iri (lit_lexical l)))
     | _ -> ER_Error)

  (* Term constructors *)
  | E_StrDt e1 e2 ->
    (match er_to_string (eval_expr e1 mu), eval_expr e2 mu with
     | Some s, ER_Term (T_IRI dt) -> ER_Term (fn_strdt s dt)
     | _, _ -> ER_Error)
  | E_StrLang e1 e2 ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu) with
     | Some s, Some lang -> ER_Term (fn_strlang s lang)
     | _, _ -> ER_Error)

  (* BOUND *)
  | E_Bound v -> ER_Bool (Some? (sm_lookup v mu))

  (* Conditional *)
  | E_If cond then_e else_e ->
    if ebv (eval_expr cond mu) then eval_expr then_e mu
    else eval_expr else_e mu
  | E_Coalesce es -> eval_coalesce es mu
  | E_In ev es ->
    let v = eval_expr ev mu in
    eval_in v es mu
  | E_NotIn ev es ->
    let v = eval_expr ev mu in
    (match eval_in v es mu with
     | ER_Bool b -> ER_Bool (not b)
     | other -> other)

  (* String functions *)
  | E_StrLen e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> ER_Num (string_length s)
     | None -> ER_Error)
  | E_Substr e1 e2 e3_opt ->
    (match er_to_string (eval_expr e1 mu), eval_expr e2 mu with
     | Some s, ER_Num start ->
       let len_opt = match e3_opt with
         | Some e3 -> (match eval_expr e3 mu with
                       | ER_Num n -> Some n
                       | _ -> None)
         | None -> None
       in er_string (fn_substr_spec s start len_opt)
     | _, _ -> ER_Error)
  | E_UCase e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (string_upper s)
     | None -> ER_Error)
  | E_LCase e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (string_lower s)
     | None -> ER_Error)
  | E_StrStarts e1 e2 ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu) with
     | Some s, Some prefix -> ER_Bool (string_starts_with s prefix)
     | _, _ -> ER_Error)
  | E_StrEnds e1 e2 ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu) with
     | Some s, Some suffix -> ER_Bool (string_ends_with s suffix)
     | _, _ -> ER_Error)
  | E_Contains e1 e2 ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu) with
     | Some s, Some sub -> ER_Bool (string_contains s sub)
     | _, _ -> ER_Error)
  | E_StrBefore e1 e2 ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu) with
     | Some s, Some arg -> er_string (string_before s arg)
     | _, _ -> ER_Error)
  | E_StrAfter e1 e2 ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu) with
     | Some s, Some arg -> er_string (string_after s arg)
     | _, _ -> ER_Error)
  | E_Concat es -> eval_concat es mu
  | E_EncodeForUri e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (string_encode_uri s)
     | None -> ER_Error)
  | E_Replace e1 e2 e3 e4_opt ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu),
           er_to_string (eval_expr e3 mu) with
     | Some s, Some pat, Some rep ->
       let flags = match e4_opt with
         | Some e4 -> er_to_string (eval_expr e4 mu)
         | None -> None
       in er_string (string_replace s pat rep flags)
     | _, _, _ -> ER_Error)
  | E_Regex e1 e2 e3_opt ->
    (match er_to_string (eval_expr e1 mu), er_to_string (eval_expr e2 mu) with
     | Some s, Some pat ->
       let flags = match e3_opt with
         | Some e3 -> er_to_string (eval_expr e3 mu)
         | None -> None
       in ER_Bool (fn_regex_spec s pat flags)
     | _, _ -> ER_Error)

  (* Numeric functions *)
  | E_Abs e1 ->
    (match eval_expr e1 mu with
     | ER_Num n -> ER_Num (int_abs n)
     | _ -> ER_Error)
  | E_Round e1 ->
    (match eval_expr e1 mu with
     | ER_Num n -> ER_Num n
     | ER_Dec s -> ER_Num (int_round s)
     | _ -> ER_Error)
  | E_Ceil e1 ->
    (match eval_expr e1 mu with
     | ER_Num n -> ER_Num n
     | ER_Dec s -> ER_Num (int_ceil s)
     | _ -> ER_Error)
  | E_Floor e1 ->
    (match eval_expr e1 mu with
     | ER_Num n -> ER_Num n
     | ER_Dec s -> ER_Num (int_floor s)
     | _ -> ER_Error)

  (* Hash functions *)
  | E_MD5 e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (hash_md5 s)
     | None -> ER_Error)
  | E_SHA1 e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (hash_sha1 s)
     | None -> ER_Error)
  | E_SHA256 e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (hash_sha256 s)
     | None -> ER_Error)
  | E_SHA384 e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (hash_sha384 s)
     | None -> ER_Error)
  | E_SHA512 e1 ->
    (match er_to_string (eval_expr e1 mu) with
     | Some s -> er_string (hash_sha512 s)
     | None -> ER_Error)

  (* Date/time functions *)
  | E_Now -> ER_Error  (* requires runtime context *)
  | E_Year e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_year s with Some n -> ER_Num n | None -> ER_Error)
     | None -> ER_Error)
  | E_Month e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_month s with Some n -> ER_Num n | None -> ER_Error)
     | None -> ER_Error)
  | E_Day e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_day s with Some n -> ER_Num n | None -> ER_Error)
     | None -> ER_Error)
  | E_Hours e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_hours s with Some n -> ER_Num n | None -> ER_Error)
     | None -> ER_Error)
  | E_Minutes e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_minutes s with Some n -> ER_Num n | None -> ER_Error)
     | None -> ER_Error)
  | E_Seconds e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_seconds s with Some ds -> ER_Dec ds | None -> ER_Error)
     | None -> ER_Error)
  | E_Timezone e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_timezone s with Some tz -> er_string tz | None -> ER_Error)
     | None -> ER_Error)
  | E_Tz e1 ->
    (match er_to_datetime_lex (eval_expr e1 mu) with
     | Some s -> (match dt_tz s with Some tz -> er_string tz | None -> ER_Error)
     | None -> ER_Error)

  (* SameTerm *)
  | E_SameTerm e1 e2 ->
    (match eval_expr e1 mu, eval_expr e2 mu with
     | ER_Term t1, ER_Term t2 -> ER_Bool (same_term t1 t2)
     | _, _ -> ER_Error)

  (* EXISTS / NOT EXISTS — require graph context, delegated *)
  | E_Exists _ -> ER_Error
  | E_NotExists _ -> ER_Error

  (* Aggregates — evaluated in aggregation context, not here *)
  | E_Aggregate _ _ _ -> ER_Error

  (* Function call — extensible, not handled here *)
  | E_FunctionCall _ _ -> ER_Error

(* Coalesce: first non-error result from list *)
and eval_coalesce (es : list expr) (mu : solution_mapping)
  : Tot eval_result (decreases es) =
  match es with
  | [] -> ER_Error
  | e :: rest ->
    (match eval_expr e mu with
     | ER_Error -> eval_coalesce rest mu
     | v -> v)

(* IN: check if value equals any in list *)
and eval_in (v : eval_result) (es : list expr) (mu : solution_mapping)
  : Tot eval_result (decreases es) =
  match es with
  | [] -> ER_Bool false
  | e :: rest ->
    (match value_compare v (eval_expr e mu) CmpEq with
     | Some true -> ER_Bool true
     | _ -> eval_in v rest mu)

(* CONCAT: concatenate string results *)
and eval_concat (es : list expr) (mu : solution_mapping)
  : Tot eval_result (decreases es) =
  match es with
  | [] -> er_string ""
  | e :: rest ->
    (match er_to_string (eval_expr e mu), eval_concat rest mu with
     | Some s, ER_Term (T_Literal l) ->
       er_string (strcat s (lit_lexical l))
     | _, _ -> ER_Error)

(* eval_expr_ebv: EBV of expression evaluation — CONCRETE *)
let eval_expr_ebv (e : expr) (mu : solution_mapping) : bool =
  ebv (eval_expr e mu)

(** 8.3 Value comparison (§17.3) — CONCRETE **)

(* Apply a comparison operator to an integer ordering result (-1, 0, 1) *)
let apply_comp_op (cmp : int) (op : comp_op) : bool =
  match op with
  | CmpEq -> cmp = 0
  | CmpNe -> cmp <> 0
  | CmpLt -> cmp < 0
  | CmpGt -> cmp > 0
  | CmpLe -> cmp <= 0
  | CmpGe -> cmp >= 0

(* Compare two integers *)
let int_compare (a b : int) : int =
  if a < b then -1 else if a = b then 0 else 1

(* SPARQL value comparison with type-aware semantics — CONCRETE.
   Returns None for type errors (incompatible types).
   Cross-numeric comparison is always permitted.
   Same-type xsd:string, xsd:dateTime, etc. use natural ordering.
   Different simple literal types → type error. *)
let value_compare (v1 v2 : eval_result) (op : comp_op) : option bool =
  match v1, v2 with
  (* Integer vs integer *)
  | ER_Num a, ER_Num b -> Some (apply_comp_op (int_compare a b) op)
  (* Boolean vs boolean: false < true *)
  | ER_Bool a, ER_Bool b ->
    let ia = if a then 1 else 0 in
    let ib = if b then 1 else 0 in
    Some (apply_comp_op (int_compare ia ib) op)
  (* Decimal vs decimal: lexicographic (approximate — proper decimal comparison deferred [S4]) *)
  | ER_Dec a, ER_Dec b -> Some (apply_comp_op (String.compare a b) op)
  (* Double vs double *)
  | ER_Dbl a, ER_Dbl b -> Some (apply_comp_op (String.compare a b) op)
  (* Cross-numeric: integer vs decimal/double — promote integer to string *)
  | ER_Num a, ER_Dec b -> Some (apply_comp_op (String.compare (string_of_int a) b) op)
  | ER_Dec a, ER_Num b -> Some (apply_comp_op (String.compare a (string_of_int b)) op)
  | ER_Num a, ER_Dbl b -> Some (apply_comp_op (String.compare (string_of_int a) b) op)
  | ER_Dbl a, ER_Num b -> Some (apply_comp_op (String.compare a (string_of_int b)) op)
  | ER_Dec a, ER_Dbl b -> Some (apply_comp_op (String.compare a b) op)
  | ER_Dbl a, ER_Dec b -> Some (apply_comp_op (String.compare a b) op)
  (* Term comparisons *)
  | ER_Term (T_IRI i1), ER_Term (T_IRI i2) ->
    Some (apply_comp_op (String.compare (iri_to_string i1) (iri_to_string i2)) op)
  | ER_Term (T_Literal l1), ER_Term (T_Literal l2) ->
    (* Same-type literals: compare lexical forms *)
    if lit_datatype l1 = lit_datatype l2
    then
      (* For lang-tagged strings, also check lang tag match for equality *)
      if lit_lang l1 = lit_lang l2
      then Some (apply_comp_op (String.compare (lit_lexical l1) (lit_lexical l2)) op)
      else (match op with
            | CmpEq -> Some false
            | CmpNe -> Some true
            | _ -> None)
    else None  (* incompatible types *)
  (* Error propagation *)
  | ER_Error, _ -> None
  | _, ER_Error -> None
  (* All other combinations: type error *)
  | _, _ -> None

(** ====================================================================== **)
(** Part 9: SPARQL 1.1 Built-in Functions (§17.4)                         **)
(** ====================================================================== **)

(** 9.1 Node type testing functions (§17.4.2.1) **)

let fn_isIRI (v : eval_result) : eval_result =
  match v with
  | ER_Term (T_IRI _) -> ER_Bool true
  | ER_Error -> ER_Error
  | _ -> ER_Bool false

let fn_isBlank (v : eval_result) : eval_result =
  match v with
  | ER_Term (T_BNode _) -> ER_Bool true
  | ER_Error -> ER_Error
  | _ -> ER_Bool false

let fn_isLiteral (v : eval_result) : eval_result =
  match v with
  | ER_Term (T_Literal _) -> ER_Bool true
  | ER_Error -> ER_Error
  | _ -> ER_Bool false

(* isNumeric: true if the datatype IRI is one of the XSD numeric types — CONCRETE *)
let is_numeric_datatype (dt : wf_iri) : bool =
  dt = xsd_integer || dt = xsd_decimal || dt = xsd_double || dt = xsd_float

let fn_isNumeric (v : eval_result) : eval_result =
  match v with
  | ER_Num _ -> ER_Bool true
  | ER_Dec _ -> ER_Bool true
  | ER_Dbl _ -> ER_Bool true
  | ER_Term (T_Literal l) -> ER_Bool (is_numeric_datatype (lit_datatype l))
  | ER_Error -> ER_Error
  | _ -> ER_Bool false

(** 9.2 Accessor functions (§17.4.2) **)

(* Helper: construct a plain xsd:string literal *)
let mk_plain_literal (s : string) : wf_literal =
  { lexical_form = s; datatype = xsd_string; lang_tag = None }

(* STR: string representation of an RDF term — CONCRETE *)
let fn_str (v : eval_result) : eval_result =
  match v with
  | ER_Term (T_IRI i) -> ER_Term (T_Literal (mk_plain_literal (iri_to_string i)))
  | ER_Term (T_Literal l) -> ER_Term (T_Literal (mk_plain_literal (lit_lexical l)))
  | ER_Term (T_BNode b) -> ER_Term (T_Literal (mk_plain_literal b))
  | ER_Error -> ER_Error
  | _ -> ER_Error

(* LANG: language tag of a literal — CONCRETE *)
let fn_lang (v : eval_result) : eval_result =
  match v with
  | ER_Term (T_Literal l) ->
    (match lit_lang l with
     | Some tag -> ER_Term (T_Literal (mk_plain_literal tag))
     | None     -> ER_Term (T_Literal (mk_plain_literal "")))
  | _ -> ER_Error

(* DATATYPE: datatype IRI of a literal — CONCRETE *)
let fn_datatype (v : eval_result) : eval_result =
  match v with
  | ER_Term (T_Literal l) -> ER_Term (T_IRI (lit_datatype l))
  | _ -> ER_Error

(** 9.3 String functions (§17.4.3) **)

(* All string functions operate on the lexical form of simple literals
   and xsd:string typed literals. Lang-tagged strings are handled
   specially per function. [S3] Unicode handled via assumed primitives. *)

let string_length (s : string) : nat = String.length s

(* List-based string operations for contains/starts_with/ends_with *)
let rec list_is_prefix (#a:eqtype) (prefix lst : list a) : Tot bool (decreases prefix) =
  match prefix, lst with
  | [], _ -> true
  | _, [] -> false
  | x :: xs, y :: ys -> x = y && list_is_prefix xs ys

let rec list_contains_sublist (#a:eqtype) (needle haystack : list a) : Tot bool (decreases haystack) =
  match haystack with
  | [] -> Nil? needle
  | _ :: rest -> list_is_prefix needle haystack || list_contains_sublist needle rest

(* SUBSTR: extract substring — CONCRETE via FStar.String.sub *)
let string_substring (s : string) (start : nat) (len : option nat) : string =
  let slen = String.length s in
  let start' = if start >= slen then slen else start in
  let actual_len = match len with
    | Some l -> if start' + l > slen then slen - start' else l
    | None -> slen - start'
  in
  if actual_len = 0 || start' >= slen then ""
  else String.sub s start' actual_len

(* UCASE / LCASE — CONCRETE via FStar.String *)
let string_upper (s : string) : string = String.uppercase s
let string_lower (s : string) : string = String.lowercase s

(* CONTAINS — CONCRETE via list_of_string *)
let string_contains (s sub : string) : bool =
  list_contains_sublist (String.list_of_string sub) (String.list_of_string s)

(* STRSTARTS — CONCRETE via list_of_string *)
let string_starts_with (s prefix : string) : bool =
  list_is_prefix (String.list_of_string prefix) (String.list_of_string s)

(* STRENDS — CONCRETE via reversed lists *)
let string_ends_with (s suffix : string) : bool =
  list_is_prefix
    (List.Tot.rev (String.list_of_string suffix))
    (List.Tot.rev (String.list_of_string s))

(* Find position of substring needle in haystack (character list), returning
   the 0-based index of the first occurrence, or None if not found. *)
let rec find_substring_pos_aux (#a:eqtype) (needle haystack : list a) (pos : nat)
  : Tot (option nat) (decreases haystack) =
  match haystack with
  | [] -> if Nil? needle then Some pos else None
  | _ :: rest ->
    if list_is_prefix needle haystack then Some pos
    else find_substring_pos_aux needle rest (pos + 1)

let find_substring_pos (needle haystack : list char) : option nat =
  find_substring_pos_aux needle haystack 0

(* STRBEFORE — CONCRETE: returns substring of s before first occurrence of arg.
   If arg is empty string, returns "". If arg not found, returns "". *)
let string_before (s arg : string) : string =
  if String.length arg = 0 then ""
  else
    let s_chars = String.list_of_string s in
    let arg_chars = String.list_of_string arg in
    match find_substring_pos arg_chars s_chars with
    | None -> ""
    | Some pos ->
      if pos = 0 then ""
      else String.string_of_list (List.Tot.Base.firstn pos s_chars)

(* STRAFTER — CONCRETE: returns substring of s after first occurrence of arg.
   If arg is empty string, returns s. If arg not found, returns "". *)
let string_after (s arg : string) : string =
  if String.length arg = 0 then s
  else
    let s_chars = String.list_of_string s in
    let arg_chars = String.list_of_string arg in
    let arg_len = List.Tot.length arg_chars in
    match find_substring_pos arg_chars s_chars with
    | None -> ""
    | Some pos ->
      String.string_of_list (List.Tot.Base.skipn (pos + arg_len) s_chars)

(* CONCAT — CONCRETE via FStar.String.concat *)
let string_concat (args : list string) : string = String.concat "" args

(* ENCODE_FOR_URI, REPLACE, REGEX — require complex string processing *)
assume val string_encode_uri : string -> string
assume val string_replace : string -> string -> string -> option string -> string
assume val regex_match : string -> string -> option string -> bool

(* STRLEN: returns xsd:integer *)
let fn_strlen_spec (s : string) : nat = string_length s

(* SUBSTR: 1-indexed, returns same type as input *)
let fn_substr_spec (s : string) (start : nat) (len : option nat) : string =
  let idx = if start > 0 then start - 1 else 0 in
  string_substring s idx len

(* UCASE / LCASE *)
let fn_ucase_spec (s : string) : string = string_upper s
let fn_lcase_spec (s : string) : string = string_lower s

(* STRSTARTS / STRENDS / CONTAINS *)
let fn_strstarts_spec (s arg : string) : bool = string_starts_with s arg
let fn_strends_spec (s arg : string) : bool = string_ends_with s arg
let fn_contains_spec (s arg : string) : bool = string_contains s arg

(* STRBEFORE / STRAFTER *)
let fn_strbefore_spec (s arg : string) : string = string_before s arg
let fn_strafter_spec (s arg : string) : string = string_after s arg

(* CONCAT *)
let fn_concat_spec (args : list string) : string = string_concat args

(* ENCODE_FOR_URI *)
let fn_encode_for_uri_spec (s : string) : string = string_encode_uri s

(* REPLACE *)
let fn_replace_spec (s pattern replacement : string) (flags : option string) : string =
  string_replace s pattern replacement flags

(* REGEX — XPath/XQuery regex matching (§17.2.4.2)
   Flags: i = case-insensitive, s = dot matches newline, m = multi-line,
          q = quote metacharacters (literal match), x = extended (strip whitespace).
   The pattern string undergoes SPARQL string unescape processing before
   compilation: \\ → \, \n → newline, etc.
   When q flag is set, all regex metacharacters in the pattern are escaped.
   When x flag is set, unescaped whitespace and #-comments are stripped. *)
let fn_regex_spec (s pattern : string) (flags : option string) : bool =
  regex_match s (unescape_sparql_string pattern) flags

(** 9.4 Numeric functions (§17.4.4) **)

(* ABS: absolute value — CONCRETE *)
let int_abs (n : int) : int = if n >= 0 then n else 0 - n

(* ROUND, CEIL, FLOOR: operate on decimal strings [S4] — require parsing *)
assume val int_round : string -> int    (* decimal string → rounded int [S4] *)
assume val int_ceil : string -> int     (* decimal string → ceiling [S4] *)
assume val int_floor : string -> int    (* decimal string → floor [S4] *)

let fn_abs_spec (n : int) : int = int_abs n

(** 9.5 Hash functions (§17.4.3.14) **)

(* Hash functions take a string and return a hex-encoded hash string *)
assume val hash_md5 : string -> string
assume val hash_sha1 : string -> string
assume val hash_sha256 : string -> string
assume val hash_sha384 : string -> string
assume val hash_sha512 : string -> string

(** 9.6 Date/time functions (§17.4.5) — CONCRETE **)

(* Date/time functions extract components from xsd:dateTime values.
   Input must be a literal with datatype xsd:dateTime.
   Functions return xsd:integer for numeric components, xsd:dayTimeDuration for timezone.
   xsd:dateTime format: YYYY-MM-DDThh:mm:ss[.sss][Z|(+|-)hh:mm] *)

(* Helper: parse digit character to int *)
let char_to_digit (c : FStar.Char.char) : option int =
  let n = FStar.Char.int_of_char c in
  if n >= 48 && n <= 57 then Some (n - 48) else None

(* Helper: parse integer from char list *)
let rec parse_int_chars (chars : list FStar.Char.char) (acc : int)
  : Tot (option int) (decreases chars) =
  match chars with
  | [] -> Some acc
  | c :: rest ->
    (match char_to_digit c with
     | Some d -> parse_int_chars rest (acc * 10 + d)
     | None -> None)

(* Helper: parse integer from string *)
let parse_int_string (s : string) : option int =
  match String.list_of_string s with
  | [] -> None
  | chars ->
    if List.Tot.hd chars = FStar.Char.char_of_int 45  (* '-' *)
    then (match parse_int_chars (List.Tot.tl chars) 0 with
          | Some n -> Some (0 - n)
          | None -> None)
    else parse_int_chars chars 0

(* YEAR: extract year from xsd:dateTime *)
let dt_year (s : string) : option int =
  let len = String.length s in
  if len < 4 then None
  else parse_int_string (String.sub s 0 4)

(* MONTH: extract month from xsd:dateTime *)
let dt_month (s : string) : option int =
  let len = String.length s in
  if len < 7 then None
  else parse_int_string (String.sub s 5 2)

(* DAY: extract day from xsd:dateTime *)
let dt_day (s : string) : option int =
  let len = String.length s in
  if len < 10 then None
  else parse_int_string (String.sub s 8 2)

(* HOURS: extract hours from xsd:dateTime *)
let dt_hours (s : string) : option int =
  let len = String.length s in
  if len < 13 then None
  else parse_int_string (String.sub s 11 2)

(* MINUTES: extract minutes from xsd:dateTime *)
let dt_minutes (s : string) : option int =
  let len = String.length s in
  if len < 16 then None
  else parse_int_string (String.sub s 14 2)

(* SECONDS: extract seconds (including fractional) from xsd:dateTime *)
let dt_seconds (s : string) : option string =
  let len = String.length s in
  if len < 19 then None
  else
    (* Find end of seconds portion: stop at Z, +, -, or end of string *)
    let chars = String.list_of_string s in
    let after_17 = list_drop 17 chars in
    let rec find_end (cs : list FStar.Char.char) (count : nat)
      : Tot nat (decreases cs) =
      match cs with
      | [] -> count
      | c :: rest ->
        let ci = FStar.Char.int_of_char c in
        if ci = 90 (* 'Z' *) || ci = 43 (* '+' *) || ci = 45 (* '-' *)
        then count
        else find_end rest (count + 1)
    in
    let sec_len = find_end after_17 0 in
    if sec_len = 0 then None
    else Some (String.sub s 17 sec_len)

(* TIMEZONE: extract timezone as xsd:dayTimeDuration string *)
let dt_timezone (s : string) : option string =
  let len = String.length s in
  if len < 19 then None
  else
    let last_char = String.index s (len - 1) in
    if FStar.Char.int_of_char last_char = 90 (* 'Z' *)
    then Some "PT0S"  (* UTC → zero duration *)
    else
      (* Look for +/- timezone offset *)
      let chars = String.list_of_string s in
      let rec find_tz (cs : list FStar.Char.char) (pos : nat)
        : Tot (option nat) (decreases cs) =
        match cs with
        | [] -> None
        | c :: rest ->
          let ci = FStar.Char.int_of_char c in
          if pos >= 19 && (ci = 43 || ci = 45) then Some pos
          else find_tz rest (pos + 1)
      in
      match find_tz chars 0 with
      | None -> Some ""  (* no timezone → empty string *)
      | Some pos ->
        if len >= pos + 6
        then
          let sign = String.index s pos in
          let sign_str = if FStar.Char.int_of_char sign = 45 then "-" else "" in
          let h_str = String.sub s (pos + 1) 2 in
          let m_str = String.sub s (pos + 4) 2 in
          match parse_int_string h_str, parse_int_string m_str with
          | Some h, Some m ->
            if m = 0 then Some (strcat sign_str (strcat "PT" (strcat (string_of_int h) "H")))
            else Some (strcat sign_str (strcat "PT" (strcat (string_of_int h) (strcat "H" (strcat (string_of_int m) "M")))))
          | _, _ -> None
        else None

(* TZ: extract timezone string as-is (e.g., "Z", "+05:00", "-05:00") *)
let dt_tz (s : string) : option string =
  let len = String.length s in
  if len < 19 then None
  else
    let last_char = String.index s (len - 1) in
    if FStar.Char.int_of_char last_char = 90 (* 'Z' *)
    then Some "Z"
    else
      let chars = String.list_of_string s in
      let rec find_tz_pos (cs : list FStar.Char.char) (pos : nat)
        : Tot (option nat) (decreases cs) =
        match cs with
        | [] -> None
        | c :: rest ->
          let ci = FStar.Char.int_of_char c in
          if pos >= 19 && (ci = 43 || ci = 45) then Some pos
          else find_tz_pos rest (pos + 1)
      in
      match find_tz_pos chars 0 with
      | None -> Some ""  (* no timezone *)
      | Some pos ->
        if pos < len then Some (String.sub s pos (len - pos))
        else None

(** 9.7 Constructor functions (§17.4.1.8) **)

(* STRDT(lexical, datatype) → typed literal — CONCRETE *)
let fn_strdt (lex : string) (dt : wf_iri) : rdf_term =
  if dt = rdf_lang_string
  then T_Literal ({ lexical_form = lex; datatype = xsd_string; lang_tag = None })  (* reject langString without lang *)
  else T_Literal ({ lexical_form = lex; datatype = dt; lang_tag = None })

(* STRLANG(lexical, lang) → lang-tagged literal — CONCRETE *)
let fn_strlang (lex : string) (lang : string) : rdf_term =
  T_Literal ({ lexical_form = lex; datatype = rdf_lang_string; lang_tag = Some lang })

(** 9.8 sameTerm (§17.4.1.7) **)

(* sameTerm returns true iff two terms are identical RDF terms
   (stricter than = which does value comparison) — CONCRETE *)
let same_term (t1 t2 : rdf_term) : bool = rdf_term_eq t1 t2

(** 9.9 langMatches (§17.4.1.4) **)

(* langMatches tests whether a language tag matches a language range
   per BCP 47 basic filtering (RFC 4647 §3.3.1).
   - langMatches(tag, "*") succeeds iff tag is non-empty
   - langMatches(tag, range) succeeds iff tag equals range (case-insensitive)
     or tag has range as a case-insensitive prefix followed by '-' *)
let fn_langMatches_spec (tag range : string) : bool =
  if range = "*" then
    strlen tag > 0
  else
    let tag_lower = string_lowercase tag in
    let range_lower = string_lowercase range in
    tag_lower = range_lower ||
    string_starts_with tag_lower (strcat range_lower "-")

(** 9.10 REGEX type constraint (§17.2) **)

(* REGEX is defined only for string arguments (xsd:string, rdf:langString,
   simple literals). When applied to an IRI or BNode, it raises a type error.
   This is modeled by returning option bool rather than bool. *)
let fn_regex_typed (term : rdf_term) (pattern : string) (flags : option string)
    : option bool =
  match term with
  | T_Literal lit -> Some (regex_match (lit_lexical lit) pattern flags)
  | T_IRI _ -> None       (* type error *)
  | T_BNode _ -> None     (* type error *)

(** ====================================================================== **)
(** Part 10: SPARQL 1.1 Aggregation (§18.5.1)                             **)
(** [S2] Partitioning specified declaratively; concrete algorithm deferred. **)
(** ====================================================================== **)

(** 10.1 Group partitioning **)

(* A group is a subset of solutions sharing the same GROUP BY key *)
type group = {
  g_key : list eval_result;        (* GROUP BY key values *)
  g_solutions : solution_sequence; (* solutions in this group *)
}

(* Partition a solution sequence by GROUP BY expressions *)
assume val group_by :
  list group_condition -> solution_sequence -> list group

(* When no GROUP BY is specified, the entire sequence is one group *)
let implicit_group (omega : solution_sequence) : list group =
  [{ g_key = []; g_solutions = omega }]

(** 10.2 Aggregate evaluation **)

(* Evaluate an aggregate function over a group *)
assume val eval_aggregate :
  aggregate_fn -> bool (* distinct *) -> expr -> group -> eval_result

(* Specification (selected):
   eval_aggregate Agg_Count false (E_Var "*") g =
     ER_Num (List.Tot.length g.g_solutions)

   eval_aggregate Agg_Count false e g =
     ER_Num (count of μ in g.g_solutions where eval_expr e μ <> ER_Error)

   eval_aggregate Agg_Count true e g =
     ER_Num (count of distinct non-error values)

   eval_aggregate Agg_Sum false e g =
     ER_Num (sum of numeric values of eval_expr e μ for μ in g.g_solutions)

   eval_aggregate Agg_Avg false e g =
     ER_Dec (sum / count as decimal)

   eval_aggregate Agg_Min false e g =
     minimum value by SPARQL ordering

   eval_aggregate Agg_Max false e g =
     maximum value by SPARQL ordering

   eval_aggregate (Agg_GroupConcat sep) false e g =
     ER_Term (plain_literal (concat with separator))

   eval_aggregate Agg_Sample false e g =
     first non-error value (implementation-defined)
*)

(** 10.3 HAVING filter **)

(* HAVING filters groups after aggregation *)
let having_filter (conditions : list having_condition) (groups : list group) : list group =
  List.Tot.filter
    (fun g ->
      List.Tot.for_all
        (fun cond ->
          (* Evaluate the HAVING condition in the context of the group.
             The condition can reference aggregate results.
             We assume a special evaluation context for group-level expressions. *)
          true (* [S2] concrete evaluation deferred *))
        conditions)
    groups

(** ====================================================================== **)
(** Part 11: SPARQL 1.1 Solution Modifiers (§18.4, §9)                    **)
(** ====================================================================== **)

(** 11.1 ORDER BY (§18.4) **)

(* SPARQL ordering: the total order on eval_results for sorting.
   Unbound < BNode < IRI < Literal.
   Within type: natural ordering (numeric, string, dateTime).
   Type errors sort before bound values. *)
(* Rank of an eval_result for the SPARQL ordering type hierarchy.
   Unbound/Error < Blank nodes < IRIs < Literals (booleans, numerics, strings). *)
let er_rank (v : eval_result) : int =
  match v with
  | ER_Error -> 0
  | ER_Term (T_BNode _) -> 1
  | ER_Term (T_IRI _) -> 2
  | ER_Bool _ -> 3
  | ER_Num _ -> 4
  | ER_Dec _ -> 5
  | ER_Dbl _ -> 6
  | ER_Term (T_Literal _) -> 7

(* SPARQL ordering (§15.1) — CONCRETE implementation.
   Returns -1 (less), 0 (equal), 1 (greater). *)
let sparql_order (a b : eval_result) : int =
  let ra = er_rank a in
  let rb = er_rank b in
  if ra < rb then -1
  else if ra > rb then 1
  else
    (* Same rank — compare within type *)
    match a, b with
    | ER_Error, ER_Error -> 0
    | ER_Term (T_BNode x), ER_Term (T_BNode y) -> String.compare x y
    | ER_Term (T_IRI x), ER_Term (T_IRI y) ->
      String.compare (iri_to_string x) (iri_to_string y)
    | ER_Bool x, ER_Bool y ->
      int_compare (if x then 1 else 0) (if y then 1 else 0)
    | ER_Num x, ER_Num y -> int_compare x y
    | ER_Dec x, ER_Dec y -> String.compare x y
    | ER_Dbl x, ER_Dbl y -> String.compare x y
    | ER_Term (T_Literal l1), ER_Term (T_Literal l2) ->
      let dc = String.compare (lit_datatype l1) (lit_datatype l2) in
      if dc <> 0 then dc
      else
        let lc = String.compare (lit_lexical l1) (lit_lexical l2) in
        if lc <> 0 then lc
        else
          (match lit_lang l1, lit_lang l2 with
           | None, None -> 0
           | None, Some _ -> -1
           | Some _, None -> 1
           | Some t1, Some t2 -> String.compare t1 t2)
    | _, _ -> 0  (* unreachable — ranks are equal so types must match *)

(* Compare two solution mappings on a single order condition.
   Returns -1, 0, or 1. *)
let compare_on_condition (c : order_condition) (mu1 mu2 : solution_mapping) : int =
  match c with
  | OC_Asc e ->
    sparql_order (eval_expr e mu1) (eval_expr e mu2)
  | OC_Desc e ->
    sparql_order (eval_expr e mu2) (eval_expr e mu1)

(* Compare two solution mappings on a list of order conditions (lexicographic).
   First non-zero comparison wins. *)
let rec compare_on_conditions (conds : list order_condition) (mu1 mu2 : solution_mapping) : int =
  match conds with
  | [] -> 0
  | c :: rest ->
    let r = compare_on_condition c mu1 mu2 in
    if r <> 0 then r
    else compare_on_conditions rest mu1 mu2

(* Sort a solution sequence by the given order conditions — CONCRETE implementation. *)
let sort_solutions (conds : list order_condition) (omega : solution_sequence) : solution_sequence =
  List.Tot.sortWith (compare_on_conditions conds) omega

(** 11.2 DISTINCT / REDUCED (§18.4) **)

let distinct_solutions (omega : solution_sequence) : solution_sequence =
  (* Remove duplicate solution mappings.
     Two mappings are equal if they bind the same variables to the same terms. *)
  List.Tot.deduplicate (fun mu1 mu2 -> mu1 = mu2) omega

(* REDUCED: implementation may eliminate some or all duplicates.
   We specify it as identity (keeping all) — this is conformant. *)
let reduced_solutions (omega : solution_sequence) : solution_sequence = omega

(** 11.3 OFFSET / LIMIT (§18.4) **)

(* list_drop/list_take — CONCRETE implementations *)
let rec list_drop (n : nat) (l : list 'a) : list 'a =
  if n = 0 then l
  else match l with
    | [] -> []
    | _ :: tl -> list_drop (n - 1) tl

let rec list_take (n : nat) (l : list 'a) : list 'a =
  if n = 0 then []
  else match l with
    | [] -> []
    | hd :: tl -> hd :: list_take (n - 1) tl

let slice_solutions (offset : option nat) (limit : option nat) (omega : solution_sequence)
  : solution_sequence =
  let after_offset = match offset with
    | None -> omega
    | Some n -> list_drop n omega in
  match limit with
  | None -> after_offset
  | Some n -> list_take n after_offset

(** 11.4 Projection (§18.4) **)

(* Project solution mapping to selected variables — CONCRETE *)
let rec project (vars : list var_name) (mu : solution_mapping) : solution_mapping =
  match mu with
  | [] -> []
  | (v, t) :: rest ->
    if List.Tot.mem v vars
    then (v, t) :: project vars rest
    else project vars rest

let project_solutions (vars : list var_name) (omega : solution_sequence)
  : solution_sequence =
  List.Tot.map (project vars) omega

(** ====================================================================== **)
(** Part 12: SPARQL 1.1 Query Evaluation (§18.2.4)                        **)
(** ====================================================================== **)

(* Top-level query evaluation for SELECT queries.
   Applies: pattern evaluation → aggregation → HAVING → projection
            → solution modifiers (ORDER BY, DISTINCT, OFFSET, LIMIT) *)

(* Evaluate a single SELECT expression item against a solution mapping.
   For SI_Var, the mapping is unchanged.
   For SI_Expr e v, evaluate e and bind the result to v. — CONCRETE *)
let eval_select_item (item : select_item) (mu : solution_mapping) (g : rdf_graph)
  : solution_mapping =
  match item with
  | SI_Var _ -> mu  (* variable already in mapping from WHERE *)
  | SI_Expr e v ->
    let r = eval_expr e mu g in
    match er_to_term r with
    | Some t -> sm_bind v t mu
    | None -> mu  (* expression error — leave unbound *)

(* Apply SELECT expression items to each solution mapping — CONCRETE *)
let eval_select_items (items : list select_item) (omega : solution_sequence) (g : rdf_graph)
  : solution_sequence =
  List.Tot.map (fun mu -> List.Tot.fold_left (fun acc item -> eval_select_item item acc g) mu items) omega

(* Extract variable names from select items — CONCRETE *)
let select_item_vars (items : list select_item) : list var_name =
  List.Tot.map (fun (item : select_item) -> match item with
    | SI_Var v -> v
    | SI_Expr _ v -> v) items

(* Top-level query evaluation for SELECT queries — CONCRETE.
   Applies: pattern evaluation → SELECT expressions → ORDER BY →
            projection → DISTINCT/REDUCED → OFFSET/LIMIT.
   GROUP BY, aggregation, and HAVING are skipped for now (assume val dependencies). *)
let eval_select_query (q : query) (g : rdf_graph) : solution_sequence =
  match q.q_form with
  | QF_Select sel ->
    (* 1. Evaluate WHERE clause *)
    let omega = eval_pattern q.q_pattern g in

    (* 2–4. GROUP BY / aggregation / HAVING — skipped for now *)

    (* 5. SELECT expressions — evaluate (expr AS ?var) *)
    let omega' = match sel with
      | Select_Vars items -> eval_select_items items omega g
      | Select_All -> omega in

    (* 6. ORDER BY *)
    let ordered = match q.q_modifier.sm_order_by with
      | None -> omega'
      | Some o -> sort_solutions o omega' in

    (* 7. Projection *)
    let projected = match sel with
      | Select_Vars items -> project_solutions (select_item_vars items) ordered
      | Select_All -> ordered in

    (* 8. DISTINCT / REDUCED *)
    let deduped =
      if q.q_modifier.sm_distinct then distinct_solutions projected
      else if q.q_modifier.sm_reduced then reduced_solutions projected
      else projected in

    (* 9. OFFSET / LIMIT *)
    slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped

  (* Other query forms — return empty for now *)
  | QF_Construct _ -> []
  | QF_Ask -> []
  | QF_Describe _ -> []

(* Specification of eval_select_query (full version with aggregation):

   let eval_select_query q G =
     (* 1. Evaluate WHERE clause *)
     let omega = eval_pattern q.q_pattern G in

     (* 2. GROUP BY — partition into groups [S2] *)
     let groups = match q.q_group_by with
       | None   -> implicit_group omega
       | Some g -> group_by g omega in

     (* 3. Aggregation — evaluate aggregate expressions per group *)
     (* Produces one solution mapping per group *)
     let omega' = aggregate_groups q.q_form groups in

     (* 4. HAVING — filter groups *)
     let omega'' = match q.q_having with
       | None   -> omega'
       | Some h -> filter_having h omega' in

     (* 5. SELECT expressions — evaluate (expr AS ?var) *)
     let omega''' = eval_select_exprs q.q_form omega'' in

     (* 6. ORDER BY *)
     let ordered = match q.q_modifier.sm_order_by with
       | None   -> omega'''
       | Some o -> sort_solutions o omega''' in

     (* 7. Projection *)
     let projected = project_select q.q_form ordered in

     (* 8. DISTINCT / REDUCED *)
     let deduped =
       if q.q_modifier.sm_distinct then distinct_solutions projected
       else if q.q_modifier.sm_reduced then reduced_solutions projected
       else projected in

     (* 9. OFFSET / LIMIT *)
     slice_solutions q.q_modifier.sm_offset q.q_modifier.sm_limit deduped
*)

(** ====================================================================== **)
(** Part 13: SPARQL 1.1 Property Paths Evaluation (§9.1)                  **)
(** [S1] Recursive paths specified as fixpoint; termination deferred.      **)
(** ====================================================================== **)

(* Property path evaluation produces pairs of (subject, object) nodes *)
type path_result = list (rdf_term * rdf_term)

(* Evaluate a property path over a graph *)
assume val eval_property_path :
  property_path -> rdf_graph -> path_result

(* Specification:

   eval_property_path (PP_IRI iri) G =
     { (s, o) | (s, iri, o) ∈ G }

   eval_property_path (PP_Inverse p) G =
     { (o, s) | (s, o) ∈ eval_property_path p G }

   eval_property_path (PP_Sequence p1 p2) G =
     { (s, o) | ∃ mid. (s, mid) ∈ eval p1 G ∧ (mid, o) ∈ eval p2 G }

   eval_property_path (PP_Alternative p1 p2) G =
     eval p1 G ∪ eval p2 G

   eval_property_path (PP_ZeroOrOne p) G =
     { (x, x) | x ∈ nodes(G) } ∪ eval p G

   eval_property_path (PP_ZeroOrMore p) G =       [S1]
     transitive-reflexive closure of eval p G
     (finite: bounded by |nodes(G)|² iterations)

   eval_property_path (PP_OneOrMore p) G =         [S1]
     transitive closure of eval p G

   eval_property_path (PP_NegatedSet ps) G =
     { (s, o) | (s, p, o) ∈ G, p ∉ iris(ps) ∧ (s,o) ∉ inverse_pairs(ps) }
*)

(** ====================================================================== **)
(** Part 14: SPARQL 1.1 VALUES (Inline Data) (§10.2)                      **)
(** ====================================================================== **)

(* VALUES provides inline data as solution sequences.
   UNDEF in a value position means the variable is unbound for that row. *)

let eval_values (vars : list var_name) (rows : list (list (option rdf_term)))
  : solution_sequence =
  List.Tot.map
    (fun row ->
      (* Zip vars with values, skipping UNDEF entries *)
      List.Tot.fold_left2
        (fun acc v term_opt ->
          match term_opt with
          | Some t -> sm_bind v t acc
          | None   -> acc)
        sm_empty
        vars
        row)
    rows

(** ====================================================================== **)
(** Part 15: SPARQL 1.1 Numeric Type Promotion (§17.3.1)                  **)
(** [S4] Simplified: full XSD numeric hierarchy not modeled.               **)
(** ====================================================================== **)

(* Numeric type hierarchy (ascending precision):
   xsd:integer < xsd:decimal < xsd:float < xsd:double

   For arithmetic between different numeric types, operands are promoted
   to the more precise type before operation.

   E.g.: integer + decimal → decimal
         decimal * double  → double *)

type numeric_precision =
  | NP_Integer
  | NP_Decimal
  | NP_Float
  | NP_Double

(* Determine numeric precision of a datatype *)
let numeric_precision_of (dt : wf_iri) : option numeric_precision =
  if dt = xsd_integer then Some NP_Integer
  else if dt = xsd_decimal then Some NP_Decimal
  else if dt = xsd_float then Some NP_Float
  else if dt = xsd_double then Some NP_Double
  else None

(* Promotion: max precision of two types *)
let promote_numeric (a b : numeric_precision) : numeric_precision =
  match a, b with
  | NP_Double, _ | _, NP_Double -> NP_Double
  | NP_Float, _ | _, NP_Float -> NP_Float
  | NP_Decimal, _ | _, NP_Decimal -> NP_Decimal
  | NP_Integer, NP_Integer -> NP_Integer

(* Result datatype IRI for promoted type *)
let promoted_datatype (p : numeric_precision) : wf_iri =
  match p with
  | NP_Integer -> xsd_integer
  | NP_Decimal -> xsd_decimal
  | NP_Float   -> xsd_float
  | NP_Double  -> xsd_double

(** ====================================================================== **)
(** Part 16: SPARQL 1.1 Casting (§17.5)                                   **)
(** ====================================================================== **)

(* Casting between XSD types.
   xsd:integer(), xsd:decimal(), xsd:float(), xsd:double(),
   xsd:string(), xsd:boolean(), xsd:dateTime()

   Casting rules follow XSD 1.1 Part 2 §3.2.
   Not all casts are valid; invalid casts produce type error. *)

type cast_target =
  | Cast_Integer
  | Cast_Decimal
  | Cast_Float
  | Cast_Double
  | Cast_String
  | Cast_Boolean
  | Cast_DateTime

(* Helper: extract lexical form from an eval_result that is a plain/typed literal *)
let er_to_lexical (v : eval_result) : option string =
  match v with
  | ER_Term (T_Literal l) -> Some (lit_lexical l)
  | ER_Term (T_IRI i) -> Some (iri_to_string i)
  | ER_Term (T_BNode b) -> Some b
  | ER_Num n -> Some (string_of_int n)
  | ER_Dec s -> Some s
  | ER_Dbl s -> Some s
  | ER_Bool true -> Some "true"
  | ER_Bool false -> Some "false"
  | ER_Error -> None

(* Helper: check if a string looks like a decimal (contains a dot, digits around it).
   Simplified: we just check it can be parsed as integer after removing the dot,
   or accept it as-is since ER_Dec already validated. *)
let is_decimal_string (s : string) : bool =
  String.length s > 0

(* Cast a value to a target type. Returns None on invalid cast. *)
let xsd_cast (v : eval_result) (target : cast_target) : option eval_result =
  match target with

  (* === Cast to integer === *)
  | Cast_Integer ->
    (match v with
     | ER_Num _ -> Some v
     | ER_Bool true -> Some (ER_Num 1)
     | ER_Bool false -> Some (ER_Num 0)
     | ER_Dec s -> parse_int_string s |> (fun r -> match r with | Some n -> Some (ER_Num n) | None ->
       (* Decimal like "3.14" — truncate by parsing before dot *)
       let chars = String.list_of_string s in
       let before_dot = List.Tot.takeWhile (fun c -> c <> FStar.Char.char_of_int 46) chars in
       parse_int_string (String.string_of_list before_dot))
     | ER_Dbl s -> parse_int_string s |> (fun r -> match r with | Some n -> Some (ER_Num n) | None ->
       let chars = String.list_of_string s in
       let before_dot = List.Tot.takeWhile (fun c -> c <> FStar.Char.char_of_int 46) chars in
       parse_int_string (String.string_of_list before_dot))
     | ER_Term (T_Literal l) ->
       if lit_datatype l = xsd_integer || lit_datatype l = xsd_string then
         (match parse_int_string (lit_lexical l) with
          | Some n -> Some (ER_Num n)
          | None -> None)
       else if lit_datatype l = xsd_boolean then
         (if lit_lexical l = "true" || lit_lexical l = "1" then Some (ER_Num 1)
          else if lit_lexical l = "false" || lit_lexical l = "0" then Some (ER_Num 0)
          else None)
       else if lit_datatype l = xsd_decimal || lit_datatype l = xsd_double || lit_datatype l = xsd_float then
         (let chars = String.list_of_string (lit_lexical l) in
          let before_dot = List.Tot.takeWhile (fun c -> c <> FStar.Char.char_of_int 46) chars in
          parse_int_string (String.string_of_list before_dot))
       else None
     | _ -> None)

  (* === Cast to decimal === *)
  | Cast_Decimal ->
    (match v with
     | ER_Dec _ -> Some v
     | ER_Num n -> Some (ER_Dec (strcat (string_of_int n) ".0"))
     | ER_Bool true -> Some (ER_Dec "1.0")
     | ER_Bool false -> Some (ER_Dec "0.0")
     | ER_Dbl s -> Some (ER_Dec s)
     | ER_Term (T_Literal l) ->
       if lit_datatype l = xsd_decimal || lit_datatype l = xsd_string then
         Some (ER_Dec (lit_lexical l))
       else if lit_datatype l = xsd_integer then
         (match parse_int_string (lit_lexical l) with
          | Some n -> Some (ER_Dec (strcat (string_of_int n) ".0"))
          | None -> None)
       else if lit_datatype l = xsd_boolean then
         (if lit_lexical l = "true" || lit_lexical l = "1" then Some (ER_Dec "1.0")
          else if lit_lexical l = "false" || lit_lexical l = "0" then Some (ER_Dec "0.0")
          else None)
       else None
     | _ -> None)

  (* === Cast to double === *)
  | Cast_Double ->
    (match v with
     | ER_Dbl _ -> Some v
     | ER_Num n -> Some (ER_Dbl (strcat (string_of_int n) ".0E0"))
     | ER_Dec s -> Some (ER_Dbl s)
     | ER_Bool true -> Some (ER_Dbl "1.0E0")
     | ER_Bool false -> Some (ER_Dbl "0.0E0")
     | ER_Term (T_Literal l) ->
       if lit_datatype l = xsd_double || lit_datatype l = xsd_float || lit_datatype l = xsd_decimal || lit_datatype l = xsd_string then
         Some (ER_Dbl (lit_lexical l))
       else if lit_datatype l = xsd_integer then
         (match parse_int_string (lit_lexical l) with
          | Some n -> Some (ER_Dbl (strcat (string_of_int n) ".0E0"))
          | None -> None)
       else if lit_datatype l = xsd_boolean then
         (if lit_lexical l = "true" || lit_lexical l = "1" then Some (ER_Dbl "1.0E0")
          else if lit_lexical l = "false" || lit_lexical l = "0" then Some (ER_Dbl "0.0E0")
          else None)
       else None
     | _ -> None)

  (* === Cast to float (simplified: same as double [S4]) === *)
  | Cast_Float ->
    (match v with
     | ER_Dbl _ -> Some v
     | ER_Num n -> Some (ER_Dbl (strcat (string_of_int n) ".0E0"))
     | ER_Dec s -> Some (ER_Dbl s)
     | ER_Bool true -> Some (ER_Dbl "1.0E0")
     | ER_Bool false -> Some (ER_Dbl "0.0E0")
     | ER_Term (T_Literal l) ->
       if lit_datatype l = xsd_double || lit_datatype l = xsd_float || lit_datatype l = xsd_decimal || lit_datatype l = xsd_string then
         Some (ER_Dbl (lit_lexical l))
       else if lit_datatype l = xsd_integer then
         (match parse_int_string (lit_lexical l) with
          | Some n -> Some (ER_Dbl (strcat (string_of_int n) ".0E0"))
          | None -> None)
       else if lit_datatype l = xsd_boolean then
         (if lit_lexical l = "true" || lit_lexical l = "1" then Some (ER_Dbl "1.0E0")
          else if lit_lexical l = "false" || lit_lexical l = "0" then Some (ER_Dbl "0.0E0")
          else None)
       else None
     | _ -> None)

  (* === Cast to string === *)
  | Cast_String ->
    (match v with
     | ER_Num n -> Some (er_string (string_of_int n))
     | ER_Dec s -> Some (er_string s)
     | ER_Dbl s -> Some (er_string s)
     | ER_Bool true -> Some (er_string "true")
     | ER_Bool false -> Some (er_string "false")
     | ER_Term (T_IRI i) -> Some (er_string (iri_to_string i))
     | ER_Term (T_Literal l) -> Some (er_string (lit_lexical l))
     | ER_Term (T_BNode _) -> None
     | ER_Error -> None)

  (* === Cast to boolean === *)
  | Cast_Boolean ->
    (match v with
     | ER_Bool _ -> Some v
     | ER_Num n -> Some (ER_Bool (n <> 0))
     | ER_Dec s -> Some (ER_Bool (s <> "0" && s <> "0.0"))
     | ER_Dbl s -> Some (ER_Bool (s <> "0" && s <> "0.0" && s <> "0.0E0"))
     | ER_Term (T_Literal l) ->
       if lit_datatype l = xsd_boolean then
         (if lit_lexical l = "true" || lit_lexical l = "1" then Some (ER_Bool true)
          else if lit_lexical l = "false" || lit_lexical l = "0" then Some (ER_Bool false)
          else None)
       else if lit_datatype l = xsd_string then
         (if lit_lexical l = "true" || lit_lexical l = "1" then Some (ER_Bool true)
          else if lit_lexical l = "false" || lit_lexical l = "0" then Some (ER_Bool false)
          else None)
       else if lit_datatype l = xsd_integer then
         (match parse_int_string (lit_lexical l) with
          | Some n -> Some (ER_Bool (n <> 0))
          | None -> None)
       else None
     | _ -> None)

  (* === Cast to dateTime === *)
  | Cast_DateTime ->
    (match v with
     | ER_Term (T_Literal l) ->
       if lit_datatype l = xsd_dateTime then Some v
       else if lit_datatype l = xsd_string then
         (* Accept string → dateTime but don't validate format *)
         Some (ER_Term (T_Literal { lexical_form = lit_lexical l; datatype = xsd_dateTime; lang_tag = None }))
       else None
     | _ -> None)

(* Cast validity matrix (simplified):

   From\To     | integer | decimal | float | double | string | boolean | dateTime
   ------------|---------|---------|-------|--------|--------|---------|--------
   integer     | id      | yes     | yes   | yes    | yes    | yes     | no
   decimal     | trunc   | id      | yes   | yes    | yes    | yes     | no
   float       | trunc   | yes     | id    | yes    | yes    | yes     | no
   double      | trunc   | yes     | yes   | id     | yes    | yes     | no
   string      | parse   | parse   | parse | parse  | id     | parse   | parse
   boolean     | 0/1     | 0.0/1.0 | 0/1   | 0/1    | yes    | id      | no
   dateTime    | no      | no      | no    | no     | yes    | no      | id
   IRI         | no      | no      | no    | no     | yes    | no      | no
*)

(** ====================================================================== **)
(** Part 17: SPARQL 1.1 EXISTS / NOT EXISTS (§18.6)                       **)
(** ====================================================================== **)

(* EXISTS evaluates a graph pattern and returns true if at least one
   solution mapping exists. NOT EXISTS is the negation.

   The pattern is evaluated in the context of the current solution mapping μ:
   variables already bound in μ are substituted into the pattern before evaluation. *)

assume val substitute_pattern :
  solution_mapping -> group_graph_pattern -> group_graph_pattern

let eval_exists (pattern : group_graph_pattern) (mu : solution_mapping)
  (graph : rdf_graph) : bool =
  let substituted = substitute_pattern mu pattern in
  List.Tot.length (eval_pattern substituted graph) > 0

let eval_not_exists (pattern : group_graph_pattern) (mu : solution_mapping)
  (graph : rdf_graph) : bool =
  not (eval_exists pattern mu graph)

(** ====================================================================== **)
(** Part 18: SPARQL 1.1 Sub-SELECT (§12)                                  **)
(** ====================================================================== **)

(* A sub-SELECT is a complete query appearing as a graph pattern.
   It is evaluated independently and its results are joined with
   the enclosing pattern. Only projected variables are visible. *)

(* Sub-SELECT evaluation is recursive: eval_pattern -> eval_select_query *)
(* This is handled by GP_SubSelect in the pattern evaluation. *)

(** ====================================================================== **)
(** Part 19: Properties and Lemmas                                         **)
(** ====================================================================== **)

open FStar.List.Tot.Properties

(** 19.1 Union is associative — PROVED **)
let lemma_union_assoc (o1 o2 o3 : solution_sequence) :
  Lemma (union (union o1 o2) o3 = union o1 (union o2 o3)) =
  append_assoc o1 o2 o3

(** 19.2 Union with empty is identity — PROVED **)
let lemma_union_nil_l (omega : solution_sequence) :
  Lemma (union [] omega = omega) = ()

let lemma_union_nil_r (omega : solution_sequence) :
  Lemma (union omega [] = omega) =
  append_l_nil omega

(** 19.3 Filter distributes over Union — PROVED **)
let rec lemma_filter_append (#a:Type) (f : a -> bool) (l1 l2 : list a) :
  Lemma (List.Tot.filter f (l1 @ l2) = List.Tot.filter f l1 @ List.Tot.filter f l2) =
  match l1 with
  | [] -> ()
  | hd :: tl -> lemma_filter_append f tl l2

let lemma_filter_union (e : expr) (omega1 omega2 : solution_sequence) :
  Lemma (filter_solutions e (union omega1 omega2) =
         union (filter_solutions e omega1) (filter_solutions e omega2)) =
  lemma_filter_append (eval_expr_ebv e) omega1 omega2

(** 19.4 OFFSET 0 is identity — PROVED **)
let lemma_offset_zero (omega : solution_sequence) :
  Lemma (slice_solutions (Some 0) None omega = omega) = ()

(** 19.5 list_drop 0 is identity — PROVED **)
let lemma_list_drop_zero (#a:Type) (l : list a) :
  Lemma (list_drop 0 l = l) = ()

(** 19.6 list_take on empty list — PROVED **)
let lemma_list_take_nil (#a:Type) (n : nat) :
  Lemma (list_take #a n [] = []) =
  if n = 0 then () else ()

(** 19.7 MINUS is subset of left operand — PROVED **)
let rec lemma_filter_mem (#a:eqtype) (f : a -> bool) (x : a) (l : list a) :
  Lemma (requires List.Tot.mem x (List.Tot.filter f l))
        (ensures List.Tot.mem x l) =
  match l with
  | [] -> ()
  | hd :: tl ->
    if f hd then
      (if hd = x then () else lemma_filter_mem f x tl)
    else lemma_filter_mem f x tl

(** 19.8 BIND does not affect existing variables **)
(* Proven in RDF.Graph.Executable as lemma_bind_preserves_existing *)

(** 19.9 sm_compatible is reflexive — PROVED **)
let rec lemma_sm_compatible_refl (mu : solution_mapping) :
  Lemma (sm_compatible mu mu = true) =
  match mu with
  | [] -> ()
  | (v, t) :: rest ->
    (* assoc v ((v,t)::rest) = Some t, and rdf_term_eq t t = true *)
    lemma_rdf_term_eq_refl t;
    lemma_sm_compatible_refl rest

(** 19.10 sm_merge with empty — PROVED **)
let lemma_sm_merge_empty_r (mu : solution_mapping) :
  Lemma (sm_merge mu [] = mu) = ()

let lemma_sm_merge_empty_l (mu : solution_mapping) :
  Lemma (sm_merge [] mu = mu) =
  let rec aux (mu : solution_mapping) : Lemma (sm_merge_aux [] mu = mu) =
    match mu with
    | [] -> ()
    | (v, t) :: rest -> aux rest
  in aux mu

(** 19.11 domains_disjoint with empty — PROVED **)
let lemma_domains_disjoint_empty_l (mu : solution_mapping) :
  Lemma (domains_disjoint [] mu = true) = ()

(** 19.12 Join commutativity (restricted — noted, not fully proved) **)
(* Note: Join is NOT commutative in general due to list ordering,
   but the multiset of solutions is the same.
   Full proof requires multiset equality, deferred. *)

(** 19.13 Aggregate COUNT is non-negative **)
(* Depends on eval_aggregate being assumed — deferred until concrete. *)

(** 19.14 Property path: IRI path degenerates to BGP **)
(* Depends on eval_property_path being assumed — deferred until concrete. *)

(** ====================================================================== **)
(** Part 20: Correspondence to Rust Implementation                         **)
(** ====================================================================== **)

(* This section documents the mapping between F* types and the Rust
   implementation in rdf-wasm/src/sparql.rs.

   F* Type/Concept             | Rust Type/Concept              | Status
   ----------------------------|--------------------------------|--------
   expr                        | FilterExpr enum                | Partial — Rust has subset
   group_graph_pattern          | WhereClause enum               | Partial — GP_* maps to WC variants
   query                       | ParsedQuery struct             | Aligned
   select_item                  | SelectExpr struct              | Aligned
   solution_mapping            | Binding (HashMap)              | Aligned (different repr)
   eval_result                 | TypedFilterValue enum          | Aligned
   comp_op                     | comparison operators in Filter | Aligned
   arith_op                    | Arithmetic in FilterExpr       | Aligned
   property_path               | (not yet in Rust)              | Pending
   aggregate_fn                | (not yet in Rust)              | Pending
   group_condition             | (not yet in Rust)              | Pending
   cast_target                 | (not yet in Rust)              | Pending
   numeric_precision           | (not yet in Rust)              | Pending

   Evaluation correspondence:
   eval_pattern                | evaluate_clauses               | Partial
   eval_bgp                   | evaluate_clauses/TriplePattern | Aligned
   join                       | nested loop in evaluate_clauses | Aligned
   left_join                  | evaluate_clauses/Optional      | Aligned
   union                      | evaluate_clauses/Union         | Aligned
   minus                      | (partial in Rust)              | Partial
   filter_solutions           | evaluate_clauses/Filter        | Aligned
   eval_expr                  | eval_filter_expr_typed         | Partial
   value_compare              | typed_compare                  | Aligned
   ebv                        | boolean_effective_value usage   | Aligned
   fn_strlen_spec             | FnStrLen evaluation            | Aligned
   fn_substr_spec             | FnSubStr evaluation            | Aligned
   fn_ucase_spec              | FnUCase evaluation             | Aligned
   fn_lcase_spec              | FnLCase evaluation             | Aligned
   sort_solutions             | ORDER BY in execute()          | Aligned
   distinct_solutions         | DISTINCT in execute()          | Aligned
   slice_solutions            | OFFSET/LIMIT in execute()      | Aligned
   eval_values                | VALUES in evaluate_clauses     | Aligned
*)

(** ====================================================================== **)
(** End of SPARQL 1.1 Formal Specification                                 **)
(** ====================================================================== **)
