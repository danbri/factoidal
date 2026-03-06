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

(* A pattern term matches an RDF term under a solution mapping *)
assume val pattern_term_matches :
  pattern_term -> rdf_term -> solution_mapping -> bool

(* A pattern subject matches a subject under a solution mapping *)
assume val pattern_subject_matches :
  pattern_subject -> subject -> solution_mapping -> bool

(* A triple pattern matches a graph triple, producing extended mapping.
   Literal matching: a plain literal pattern (no explicit datatype, no lang tag)
   matches only terms with datatype xsd:string (or empty datatype, per RDF 1.1
   where untyped literals are implicitly xsd:string). A pattern with explicit
   datatype matches only terms with that exact datatype. *)
assume val tp_match :
  triple_pattern -> triple -> solution_mapping -> option solution_mapping

(** 7.2 BGP evaluation: all matching solution mappings from the graph **)

(* eval_bgp returns all solution mappings μ such that applying μ to each
   triple pattern yields a triple in the graph.
   Per SPARQL semantics, this is the natural join of individual pattern evaluations. *)
assume val eval_bgp : bgp -> rdf_graph -> solution_sequence

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

(** 7.4 Graph pattern evaluation (§18.6) **)

(* Evaluate a group graph pattern against an RDF graph.
   This is the core recursive evaluation function.
   [S6] GRAPH patterns evaluated against single default graph only for now. *)
assume val eval_pattern : group_graph_pattern -> rdf_graph -> solution_sequence

(* Specification of eval_pattern behavior (declarative, not executable):

   eval_pattern (GP_BGP bgp) G           = eval_bgp bgp G
   eval_pattern (GP_Join P1 P2) G        = join (eval P1 G) (eval P2 G)
   eval_pattern (GP_LeftJoin P1 P2 e) G  = left_join (eval P1 G) (eval P2 G) e
   eval_pattern (GP_Filter e P) G        = filter_solutions e (eval P G)
   eval_pattern (GP_Union P1 P2) G       = union (eval P1 G) (eval P2 G)
   eval_pattern (GP_Minus P1 P2) G       = minus (eval P1 G) (eval P2 G)
   eval_pattern GP_Empty G               = [sm_empty]
   eval_pattern (GP_Bind e v P) G        = extend each μ in eval P G with v=eval(e,μ)
   eval_pattern (GP_Values vars rows) G  = inline data as solution sequence
   eval_pattern (GP_SubSelect q) G       = eval_query q G
   eval_pattern (GP_PropertyPath s p o) G = eval_property_path s p o G  [S1]
*)

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

(** 8.2 Expression evaluation function **)

(* Full expression evaluation: expr × solution_mapping → eval_result *)
assume val eval_expr : expr -> solution_mapping -> eval_result

(* Specification (selected cases):

   eval_expr (E_Var v) μ =
     match sm_lookup v μ with
     | Some t -> ER_Term t
     | None   -> ER_Error

   eval_expr (E_Arith Add e1 e2) μ =
     match eval_expr e1 μ, eval_expr e2 μ with
     | ER_Num a, ER_Num b -> ER_Num (a + b)
     | _, _ -> ER_Error  (* type error *)

   eval_expr (E_Compare op e1 e2) μ =
     ER_Bool (value_compare (eval_expr e1 μ) (eval_expr e2 μ) op)

   eval_expr (E_And e1 e2) μ =
     ER_Bool (ebv (eval_expr e1 μ) && ebv (eval_expr e2 μ))

   eval_expr (E_Or e1 e2) μ =
     ER_Bool (ebv (eval_expr e1 μ) || ebv (eval_expr e2 μ))

   eval_expr (E_Not e) μ =
     ER_Bool (not (ebv (eval_expr e μ)))

   eval_expr (E_Bound v) μ =
     ER_Bool (Some? (sm_lookup v μ))

   eval_expr (E_If cond then_e else_e) μ =
     if ebv (eval_expr cond μ) then eval_expr then_e μ
     else eval_expr else_e μ

   eval_expr (E_Coalesce es) μ =
     first non-error result from evaluating es left-to-right

   eval_expr (E_Exists P) μ =
     ER_Bool (List.Tot.length (eval_pattern P G) > 0)
     (* Note: requires access to the active graph G *)
*)

(** 8.3 Value comparison (§17.3) **)

(* SPARQL value comparison with type-aware semantics.
   Returns None for type errors (incompatible types).
   Cross-numeric comparison is always permitted.
   Same-type xsd:string, xsd:dateTime, etc. use natural ordering.
   Different simple literal types → type error. *)
assume val value_compare : eval_result -> eval_result -> comp_op -> option bool

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
assume val string_substring : string -> nat -> option nat -> string
assume val string_upper : string -> string
assume val string_lower : string -> string
assume val string_contains : string -> string -> bool
assume val string_starts_with : string -> string -> bool
assume val string_ends_with : string -> string -> bool
assume val string_before : string -> string -> string
assume val string_after : string -> string -> string
assume val string_concat : list string -> string
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

assume val int_abs : int -> int
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

(** 9.6 Date/time functions (§17.4.5) **)

(* Date/time functions extract components from xsd:dateTime values.
   Input must be a literal with datatype xsd:dateTime.
   Functions return xsd:integer for numeric components, xsd:dayTimeDuration for timezone. *)
assume val dt_year : string -> option int
assume val dt_month : string -> option int
assume val dt_day : string -> option int
assume val dt_hours : string -> option int
assume val dt_minutes : string -> option int
assume val dt_seconds : string -> option string    (* decimal seconds *)
assume val dt_timezone : string -> option string   (* xsd:dayTimeDuration or "" *)
assume val dt_tz : string -> option string         (* timezone string e.g. "Z", "+05:00" *)

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
assume val sparql_order : eval_result -> eval_result -> int  (* -1, 0, 1 *)

assume val sort_solutions :
  list order_condition -> solution_sequence -> solution_sequence

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

assume val eval_select_query : query -> rdf_graph -> solution_sequence

(* Specification of eval_select_query:

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

(* Cast a value to a target type. Returns None on invalid cast. *)
assume val xsd_cast : eval_result -> cast_target -> option eval_result

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

(** 19.1 Join commutativity (restricted) **)
(* Note: Join is NOT commutative in general due to ordering,
   but the set of solutions is the same *)
(* val lemma_join_commutative :
     omega1:solution_sequence -> omega2:solution_sequence ->
     Lemma (as_set (join omega1 omega2) = as_set (join omega2 omega1)) *)

(** 19.2 Union commutativity **)
(* val lemma_union_commutative :
     omega1:solution_sequence -> omega2:solution_sequence ->
     Lemma (as_set (union omega1 omega2) = as_set (union omega2 omega1)) *)

(** 19.3 Empty pattern is Join identity **)
(* val lemma_empty_join_identity :
     omega:solution_sequence ->
     Lemma (join [sm_empty] omega ≡ omega) *)

(** 19.4 Filter distributes over Union **)
(* val lemma_filter_union :
     e:expr -> omega1:solution_sequence -> omega2:solution_sequence ->
     Lemma (filter_solutions e (union omega1 omega2) =
            union (filter_solutions e omega1) (filter_solutions e omega2)) *)

(** 19.5 DISTINCT is idempotent **)
(* val lemma_distinct_idempotent :
     omega:solution_sequence ->
     Lemma (distinct_solutions (distinct_solutions omega) = distinct_solutions omega) *)

(** 19.6 OFFSET 0 is identity **)
(* val lemma_offset_zero :
     omega:solution_sequence ->
     Lemma (slice_solutions (Some 0) None omega = omega) *)

(** 19.7 BIND does not affect existing variables **)
(* Proven in rdfcore11.fstar.txt as lemma_bind_preserves_existing *)

(** 19.8 Aggregate COUNT is non-negative **)
(* val lemma_count_nonneg :
     g:group ->
     Lemma (match eval_aggregate Agg_Count false (E_Var "*") g with
            | ER_Num n -> n >= 0
            | _ -> False) *)

(** 19.9 MINUS is subset of left operand **)
(* val lemma_minus_subset :
     omega1:solution_sequence -> omega2:solution_sequence ->
     Lemma (forall mu. mem mu (minus omega1 omega2) ==> mem mu omega1) *)

(** 19.10 Property path: IRI path degenerates to BGP **)
(* val lemma_iri_path_is_bgp :
     iri:wf_iri -> G:rdf_graph ->
     Lemma (eval_property_path (PP_IRI iri) G =
            { (s, o) | exists t in G. triple_predicate t = iri }) *)

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
