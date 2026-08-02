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
  // RDF 1.2 triple terms are object-position-only and never denote a
  // triple's subject, so there is no subject to recover — None, exactly
  // as for a literal object.
  | T_TripleTerm _ _ _ -> None

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
let rec term_to_key_total (o : rdf_term) : Tot string (decreases o) =
  match o with
  | T_IRI i     -> String.concat "" ["I_"; i]
  | T_BNode b   -> String.concat "" ["B_"; b]
  | T_Literal l -> String.concat "" ["L_"; l.lexical_form; "^^"; l.datatype;
                                       (match l.lang_tag with
                                        | Some t -> String.concat "" ["@"; t]
                                        | None   -> "");
                                       (match l.direction with
                                        | Some Dir_LTR -> "--ltr"
                                        | Some Dir_RTL -> "--rtl"
                                        | None         -> "")]
  // RDF 1.2 triple term: a distinct, structural in-graph dedup key so two
  // different triple terms never collide. (Object-position, so it recurses
  // through the object slot.)
  | T_TripleTerm s p obj ->
    String.concat "" ["T_"; subject_to_key s; unit_sep; p; unit_sep;
                      term_to_key_total obj]

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
/// Comparator over PRE-COMPUTED `(key, triple)` pairs. Same ordering as
/// `triple_cmp` — `String.compare` on `triple_to_key` — but it reads the
/// already-built key instead of building it again. `triple_to_key` is
/// `Tot`, so this decides every pair exactly as `triple_cmp` would and
/// the sorted order is unchanged.
let cmp_decorated_triple (p1 p2 : (string * triple)) : int =
  String.compare (fst p1) (fst p2)

/// `dedup_sorted_aux` over pre-decorated pairs. Same rule: drop each
/// element whose key equals the previous one, keeping the first.
let rec dedup_sorted_decorated_aux
    (prev_key : option string)
    (ts : list (string * triple)) (acc : list triple)
  : Tot (list triple) (decreases ts) =
  match ts with
  | [] -> List.Tot.rev acc
  | (k, t) :: rest ->
    let dup = match prev_key with
              | Some p -> p = k
              | None   -> false in
    if dup then dedup_sorted_decorated_aux prev_key rest acc
    else dedup_sorted_decorated_aux (Some k) rest (t :: acc)

/// O(N log N) dedup for the closure path, via decorate-sort-undecorate
/// (the Schwartzian transform) — the same treatment `build_bucket` in
/// RDF.Indexed.fsti already applies to its six index buckets.
///
/// WHY. `triple_cmp` calls `triple_to_key`, which is a `String.concat`
/// over the subject, predicate and object IRIs in full. Handing that
/// comparator to `sortWith` builds TWO such strings per comparison, so
/// 2·N·log N key constructions where N would do. At N = 500,000 that is
/// roughly 38 times more string building than necessary.
///
/// Measured, callgrind on a 16,000-triple QUDT prefix (151 G
/// instructions retired): string construction — `unsafe_blits` 15.9%,
/// `caml_blit_string` 8.8%, `memcpy` 8.8%, `sum_lengths` 8.2%,
/// `caml_alloc_string` 4.2%, `String.concat` 3.3% — is ~49% of the
/// program, with `triple_to_key` / `term_to_key_total` / `subject_to_key`
/// another ~4% on top, and garbage collection ~17% mostly collecting
/// those same keys.
///
/// The earlier profile taken on schema.org did NOT show this shape. It
/// is a different vocabulary; see measuring-inference rule 2.
let graph_dedup_sort (g : rdf_graph) : Tot rdf_graph =
  let decorated = List.Tot.map (fun (t : triple) -> (triple_to_key t, t)) g in
  let sorted = List.Tot.sortWith cmp_decorated_triple decorated in
  dedup_sorted_decorated_aux None sorted []

/// Add multiple triples, deduplicating.
///
/// QUADRATIC, AND KEPT THAT WAY ON PURPOSE. Each step is
/// `graph_add t g = if mem_triple t g then g else g @ [t]` -- a linear
/// membership scan AND a linear append, per triple. Adding k triples to
/// a graph of n costs O(n*k) comparisons and O(n*k) freshly allocated
/// cons cells.
///
/// `RDF.Entailment.RDFS.Refinement.lemma_add_triples_if_new_memP` is
/// proved about this exact definition, so it does not change. Callers
/// with a LARGE `g` should use `add_triples_if_new_bulk` below instead.
let rec add_triples_if_new (g : rdf_graph) (ts : list triple) : Tot rdf_graph (decreases ts) =
  match ts with
  | [] -> g
  | hd :: tl -> add_triples_if_new (add_triple_if_new g hd) tl

/// Elements of `newer` whose key is not in `older`. Linear merge; BOTH
/// arguments must be key-sorted and duplicate-free, i.e. straight out of
/// `graph_dedup_sort`.
///
/// TAIL-RECURSIVE, and it has to be: written the obvious way as
/// `n :: sorted_diff ns older` it wants one stack frame per element and
/// dies with `Fatal error: exception Stack overflow` on a half-million
/// triples. F* proves termination, not stack depth. `rev_acc acc newer`
/// is `rev acc @ newer`, avoiding a non-tail `append` in the
/// older-exhausted case. See trap 5 in skills/fstar-module-style.
let rec sorted_diff_aux (newer older acc : list triple)
  : Tot (list triple)
        (decreases (List.Tot.length newer + List.Tot.length older)) =
  match newer, older with
  | [], _ -> List.Tot.rev acc
  | _, [] -> List.Tot.rev_acc acc newer
  | n :: ns, o :: os ->
    let c = triple_cmp n o in
    if c < 0 then sorted_diff_aux ns older (n :: acc)
    else if c = 0 then sorted_diff_aux ns older acc
    else sorted_diff_aux newer os acc

let sorted_diff (newer older : list triple) : Tot (list triple) =
  sorted_diff_aux newer older []

/// Set-union of `g` with `ts`, for callers where `g` is large.
///
/// Same SET as `add_triples_if_new g ts`. The ORDER differs: the new
/// triples arrive key-sorted rather than in `ts` order. Every caller
/// switched to this either sorts downstream or is byte-verified against
/// the previous output.
///
/// O(n log n + k log k) instead of O(n*k), and -- the part the profile
/// actually showed -- it allocates one merged list rather than k
/// successive copies of an n-element list. On schema.org, garbage
/// collection was ~31% of all instructions retired and the
/// `mem_triple` / `triple_eq` / `subject_eq` family another ~8%;
/// `graph_add` is the sole caller of `mem_triple` and the sole source
/// of those k copies.
let add_triples_if_new_bulk (g : rdf_graph) (ts : list triple) : Tot rdf_graph =
  match ts with
  | [] -> g
  | _ ->
    let fresh = sorted_diff (graph_dedup_sort ts) (graph_dedup_sort g) in
    List.Tot.append g fresh
