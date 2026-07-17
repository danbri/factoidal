module RDF.GraphIsomorphism

(* Strict graph / SPARQL-result comparison for the W3C test runner.

   Per CLAUDE.md rules #1/#2/#4/#8: comparison SEMANTICS live here in
   F-star and are extracted to OCaml. The w3c_runner is I/O glue that
   only calls these functions; it holds no comparison logic of its own.

   This module replaces the runner's previous lenient comparators,
   which collapsed every blank node to a single placeholder ("BN" /
   "_:b") and thus declared any two graphs (or result sets) equal as
   long as their non-bnode structure and triple/row COUNTS matched.
   That inflated scores by construction (the RDF 1.1 ledger's
   "runner-integrity failure"). Here we compare properly.

   Design (guided by Jena and rdflib):

   1. graphs_isomorphic: canonicalize both graphs with the project's
      verified RDFC-1.0 canonicalizer (RDF.Canonical, 86/86 on the
      rdf-canon suite) and byte-compare the canonical N-Quads. This is
      rdflib's reduction of graph isomorphism to canonicalization.
      RDFC-1.0 carries a Hash-N-Degree-Quads work budget for
      pathological blank-node graphs; if either side trips it we do NOT
      silently pass — we surface Iso_BudgetExceeded so the runner can
      log a countable fallback marker.

   2. reify_solutions: Jena ResultSetCompare semantics. Each SELECT
      solution row is reified into triples under a fresh per-row blank
      node (one binding-node per binding, carrying the variable name as
      a literal and the bound value as an object term), and the whole
      lot is compared with graphs_isomorphic. Value blank nodes stay as
      real blank nodes so a bnode-consistent bijection across rows is
      exactly what canonicalization enforces. ORDER BY results add a
      per-row position literal so the bijection is pinned to position.

   3. RDF 1.1 value equivalence for the two gaps the runner flagged:
      language tags compare case-insensitively ("a"@en-GB == "a"@en-gb),
      handled by lowercasing lang tags before canonicalization; plain
      and xsd:string literals are already the same term in this model
      (the term algebra assigns xsd:string to unsuffixed literals), so
      no separate handling is required. Normalization is applied inside
      this module only; it does NOT touch RDF.Canonical's own output,
      so the rdf-canon suite score is unaffected. *)

open FStar.String
open FStar.List.Tot
open RDF.Graph.Executable
open RDF.Canonical

(* ------------------------------------------------------------------ *)
(* RDF 1.1 term normalization for value equivalence.                   *)
(* ------------------------------------------------------------------ *)

(* Lowercase a language tag (RDF 1.1 Concepts 3.3: language tags are
   compared case-insensitively). Datatype stays rdf:langString, so
   well-formedness is preserved. *)
let normalize_literal (l : wf_literal) : wf_literal =
  match l.lang_tag with
  | Some t -> { l with lang_tag = Some (String.lowercase t) }
  | None -> l

let normalize_term (t : rdf_term) : rdf_term =
  match t with
  | T_Literal l -> T_Literal (normalize_literal l)
  | _ -> t

let normalize_triple (tr : triple) : triple =
  { tr with o = normalize_term tr.o }

let normalize_graph (g : list triple) : list triple =
  List.Tot.map normalize_triple g

(* ------------------------------------------------------------------ *)
(* Canonicalization-based graph isomorphism.                           *)
(* ------------------------------------------------------------------ *)

(* Budget for the RDFC-1.0 Hash-N-Degree-Quads escape. W3C test graphs
   are tiny; the practically-unbounded default is only tripped by
   genuinely pathological blank-node cliques, in which case we report
   Iso_BudgetExceeded rather than guessing. *)
let iso_budget : nat = default_hndq_budget

type iso_outcome =
  | Iso_Equal          (* canonical forms are byte-identical           *)
  | Iso_NotEqual       (* canonical forms differ                        *)
  | Iso_BudgetExceeded (* RDFC-1.0 work budget tripped on either side  *)

let graph_to_dataset (g : list triple) : rdf_dataset =
  { ds_default = normalize_graph g; ds_named = [] }

(* Normalize a whole dataset (default + named graphs) so a TriG/N-Quads
   eval test compares at quad granularity, preserving graph names, rather
   than flattening named graphs into the default graph. *)
let normalize_named (ng : named_graph) : named_graph =
  { ng with ng_graph = normalize_graph ng.ng_graph }

let normalize_dataset (ds : rdf_dataset) : rdf_dataset =
  { ds_default = normalize_graph ds.ds_default;
    ds_named = List.Tot.map normalize_named ds.ds_named }

let compare_datasets (da db : rdf_dataset) : iso_outcome =
  if canonicalize_exceeds_hndq_budget HA_SHA256 iso_budget da
     || canonicalize_exceeds_hndq_budget HA_SHA256 iso_budget db
  then Iso_BudgetExceeded
  else if canonicalize_to_nquads da = canonicalize_to_nquads db
  then Iso_Equal
  else Iso_NotEqual

let graphs_isomorphic_outcome (a b : list triple) : iso_outcome =
  compare_datasets (graph_to_dataset a) (graph_to_dataset b)

let graphs_isomorphic (a b : list triple) : bool =
  Iso_Equal? (graphs_isomorphic_outcome a b)

let datasets_isomorphic_outcome (a b : rdf_dataset) : iso_outcome =
  compare_datasets (normalize_dataset a) (normalize_dataset b)

let datasets_isomorphic (a b : rdf_dataset) : bool =
  Iso_Equal? (datasets_isomorphic_outcome a b)

(* ------------------------------------------------------------------ *)
(* SPARQL SELECT result comparison via row reification.                *)
(* ------------------------------------------------------------------ *)

(* Fixed reification vocabulary. All statically well-formed IRIs. *)
let rrv_binding : wf_iri =
  assert_norm (is_iri "urn:factoidal:resultset#binding");
  "urn:factoidal:resultset#binding"

let rrv_var : wf_iri =
  assert_norm (is_iri "urn:factoidal:resultset#var");
  "urn:factoidal:resultset#var"

let rrv_value : wf_iri =
  assert_norm (is_iri "urn:factoidal:resultset#value");
  "urn:factoidal:resultset#value"

let rrv_index : wf_iri =
  assert_norm (is_iri "urn:factoidal:resultset#index");
  "urn:factoidal:resultset#index"

(* Plain (xsd:string) literal. Same construction as SPARQL11.Algebra's
   mk_plain_literal; xsd:string is not rdf:langString and there is no
   language tag, so literal_wf holds. *)
let iso_plain_literal (s : string) : wf_literal =
  { lexical_form = s; datatype = xsd_string; lang_tag = None; direction = None }

(* A binding is a (variable-name, bound-term) pair; a row is a list of
   them; a result set is a list of rows. Matches the OCaml runner's
   solution representation exactly. *)

let rec reify_bindings (rowbn : bnode_id) (row_ix : nat) (bind_ix : nat)
                       (bs : list (string * rdf_term))
  : Tot (list triple) (decreases bs) =
  match bs with
  | [] -> []
  | (v, t) :: rest ->
    let bindbn : bnode_id =
      "__isob_" ^ string_of_int row_ix ^ "_" ^ string_of_int bind_ix in
    let t_link : triple = { s = S_BNode rowbn; p = rrv_binding; o = T_BNode bindbn } in
    let t_var  : triple = { s = S_BNode bindbn; p = rrv_var; o = T_Literal (iso_plain_literal v) } in
    let t_val  : triple = { s = S_BNode bindbn; p = rrv_value; o = t } in
    t_link :: t_var :: t_val :: reify_bindings rowbn row_ix (bind_ix + 1) rest

let rec reify_rows (ordered : bool) (row_ix : nat)
                   (rows : list (list (string * rdf_term)))
  : Tot (list triple) (decreases rows) =
  match rows with
  | [] -> []
  | row :: rest ->
    let rowbn : bnode_id = "__isorow_" ^ string_of_int row_ix in
    let binding_triples = reify_bindings rowbn row_ix 0 row in
    let with_index =
      if ordered
      then ({ s = S_BNode rowbn; p = rrv_index;
              o = T_Literal (iso_plain_literal (string_of_int row_ix)) })
           :: binding_triples
      else binding_triples in
    with_index @ reify_rows ordered (row_ix + 1) rest

let reify_solutions (ordered : bool)
                    (rows : list (list (string * rdf_term))) : list triple =
  reify_rows ordered 0 rows

let solutions_isomorphic_outcome (ordered : bool)
    (expected actual : list (list (string * rdf_term))) : iso_outcome =
  graphs_isomorphic_outcome
    (reify_solutions ordered expected)
    (reify_solutions ordered actual)

let solutions_isomorphic (ordered : bool)
    (expected actual : list (list (string * rdf_term))) : bool =
  Iso_Equal? (solutions_isomorphic_outcome ordered expected actual)

(* ------------------------------------------------------------------ *)
(* ASK boolean comparison. Trivial, but kept here so the runner holds  *)
(* no comparison logic at all.                                          *)
(* ------------------------------------------------------------------ *)

let ask_results_match (expected actual : bool) : bool = expected = actual
