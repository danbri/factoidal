module RDF.Graph

// Per docs/designissues/2026-07-05-foundational-core-refactor.md
// §2.2/§3.3 step 5. One concept, one screen: what is a graph, what is
// a dataset. Full history + exclusion list in RDF.Graph.fst's banner.
// Transparent `let`s/`type`s throughout — see RDF.Term.fsti's banner
// for why. Concepts run uninterrupted below to the "Appendix" divider,
// which holds the graph-operation surface RDF.Indexed's callers need.

open FStar.String
open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Indexed

(** ==================================================================== *)
(** Concepts — read top to bottom, uninterrupted, to the Appendix.       *)
(** ==================================================================== *)

(** ------------------------------------------------------------------ *)
(** RDF graphs — RDF 1.1 Concepts §3 ("a set of RDF triples")          *)
(** ------------------------------------------------------------------ *)

/// An RDF graph is a set of triples. Represented as a list (not a set)
/// so it extracts and executes directly; the algebra and de-
/// duplication helpers that keep list semantics behaving like set
/// semantics (`graph_add`'s membership check, `graph_dedup_sort`)
/// stay in `RDF.Graph.Executable.fst`.
type rdf_graph = list triple

let empty_graph : rdf_graph = []

(** ------------------------------------------------------------------ *)
(** RDF datasets — RDF 1.1 Concepts §4 ("one default graph ... zero or *)
(** more named graphs, each ... identified by an IRI")                 *)
(** ------------------------------------------------------------------ *)

/// One named graph: an IRI naming a graph, per RDF 1.1 Concepts §4's
/// dataset definition.
noeq type named_graph = {
  ng_name : iri;
  ng_graph : rdf_graph;
}

/// An RDF dataset: exactly one default graph, plus zero or more named
/// graphs. This is the unit SPARQL's `FROM`/`FROM NAMED`/`GRAPH`
/// clauses (SPARQL 1.1 §13.2) query against.
noeq type rdf_dataset = {
  ds_default : rdf_graph;
  ds_named : list named_graph;
}

let empty_dataset : rdf_dataset = { ds_default = empty_graph; ds_named = [] }

/// Look up a named graph by its IRI; `None` if the dataset has no
/// graph under that name.
let rec lookup_named_graph (name : iri) (named : list named_graph) : option rdf_graph =
  match named with
  | [] -> None
  | ng :: rest -> if ng.ng_name = name then Some ng.ng_graph else lookup_named_graph name rest

(** ==================================================================== *)
(** Appendix: mechanical definitions. Nothing below this line is a new  *)
(** RDF concept — it's the graph-operation surface RDF.Indexed's        *)
(** callers (RDFS.Closure / OWL.Closure) need, without depending back    *)
(** on RDF.Graph.Executable.fst.                                        *)
(** ==================================================================== *)

/// Membership check via `triple_eq` (structural, not `mem` on the raw
/// record — literal/lang-tag comparison goes through `triple_eq`).
let rec mem_triple (t:triple) (g:rdf_graph) : bool =
  match g with
  | [] -> false
  | hd :: tl -> triple_eq hd t || mem_triple t tl

/// Set-based add: only add if not already present (deduplication).
let graph_add (t:triple) (g:rdf_graph) : rdf_graph =
  if mem_triple t g then g else g @ [t]

let graph_len (g:rdf_graph) : nat = List.Tot.length g

/// Convert a subject to an rdf_term.
let subject_to_term (s : subject) : rdf_term =
  match s with
  | S_IRI i -> T_IRI i
  | S_BNode b -> T_BNode b

/// Convert an rdf_term to a subject, if possible.
let term_to_subject (t : rdf_term) : option subject =
  match t with
  | T_IRI i -> Some (S_IRI i)
  | T_BNode b -> Some (S_BNode b)
  | T_Literal _ -> None

/// Add a triple only if not already present.
/// #259 followup (2026-05-11): O(n) membership scan + O(n) tail-append.
/// Used inside the RDFS/OWL-RL closure rules and the Tableau solver; for
/// the closure path on a 27K-triple graph, the cumulative O(N^2) cost
/// blows up to 5+ billion ops. The fast-path replacement
/// `add_triple_unchecked` (just `t :: g`) lets the closure step emit
/// duplicates freely and reconcile via one `graph_dedup_sort` at the
/// end of each closure pass. Kept as-is for legacy / Tableau callers.
let add_triple_if_new (g : rdf_graph) (t : triple) : rdf_graph =
  graph_add t g

/// O(1) prepend, no membership check. The closure rules use this and
/// then call `graph_dedup_sort` once at the end of the step instead of
/// reconciling on every insert.
let add_triple_unchecked (g : rdf_graph) (t : triple) : rdf_graph =
  t :: g

/// Total key for any rdf_term — extends `RDF.Indexed`'s `term_to_key_opt`
/// with a literal branch. Used only for in-graph dedup comparisons; not
/// stable across graph encodings.
let term_to_key_total (o : rdf_term) : string =
  match o with
  | T_IRI i     -> String.concat "" ["I_"; i]
  | T_BNode b   -> String.concat "" ["B_"; b]
  | T_Literal l -> String.concat "" ["L_"; l.lexical_form; "^^"; l.datatype;
                                       (match l.lang_tag with
                                        | Some t -> String.concat "" ["@"; t]
                                        | None   -> "")]

/// Triple key: subject + predicate + object, separated by unit-sep so
/// no two distinct triples collide on the string. Reuses
/// `RDF.Indexed.subject_to_key`/`unit_sep` (the same subject-keying and
/// separator the index buckets use) rather than a second copy.
let triple_to_key (t : triple) : string =
  String.concat "" [subject_to_key t.s; unit_sep; t.p; unit_sep; term_to_key_total t.o]

let triple_cmp (t1 t2 : triple) : int =
  String.compare (triple_to_key t1) (triple_to_key t2)

/// Walk a key-sorted triple list, dropping each triple whose key equals
/// the previous one. Linear in the input length.
let rec dedup_sorted_aux
    (prev_key : option string)
    (ts : list triple) (acc : list triple)
  : Tot (list triple) (decreases ts) =
  match ts with
  | [] -> List.Tot.rev acc
  | t :: rest ->
    let k = triple_to_key t in
    let dup = match prev_key with
              | Some p -> p = k
              | None   -> false in
    if dup then dedup_sorted_aux prev_key rest acc
    else dedup_sorted_aux (Some k) rest (t :: acc)

/// O(N log N) dedup for the closure path. Sorts by triple key, then
/// one linear pass collapses adjacent duplicates. Replaces the per-insert
/// `mem_triple` scan when running RDFS / OWL-RL closure on a non-tiny
/// graph (#259 followup).
let graph_dedup_sort (g : rdf_graph) : Tot rdf_graph =
  let sorted = List.Tot.sortWith triple_cmp g in
  dedup_sorted_aux None sorted []

/// Add multiple triples, deduplicating.
let rec add_triples_if_new (g : rdf_graph) (ts : list triple) : Tot rdf_graph (decreases ts) =
  match ts with
  | [] -> g
  | hd :: tl -> add_triples_if_new (add_triple_if_new g hd) tl
