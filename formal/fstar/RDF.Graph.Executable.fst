module RDF.Graph.Executable

open FStar.String
open FStar.List.Tot
// RDF.Vocabulary.fst (2026-07-05, design doc "foundational-core-
// refactor" §2.6/§3.3 step 2) is the canonical, grep-verifiable source
// for the RDF/RDFS/OWL vocabulary IRI *strings*. This file's own
// section 16 (below) used to be a thin re-export shim over it; since
// step 6 that shim lives in RDFS.Closure.fsti instead (see the
// `include RDFS.Closure` banner below), so this `open` now exists only
// for this file's own remaining sections. Its constants are plain
// `string` (not `wf_iri`) specifically so this file (which defines
// `wf_iri`/`is_iri` itself) can depend on it without a cycle: `open
// RDF.Vocabulary` here is a one-directional edge, same direction the
// XSD.Datatypes slice-1 shim used.
open RDF.Vocabulary
// RDF.Indexed.fst (2026-07-05, design doc "foundational-core-refactor"
// §2.3/§3.3 step 3, folded in fully at step 6 §3.3) holds the
// `bucket_map` plumbing AND (since step 6) the RDF-specific
// `indexed_graph` acceleration structure itself — see RDF.Indexed.fsti's
// banner for the cyclic-dependency finding step 3 hit and how step 5's
// RDF.Term/RDF.Triple/RDF.Graph split resolved it. `include` (not
// `open`) because this file's former section 6b defined `indexed_graph`
// locally; now it's defined in RDF.Indexed and re-exported here so the
// ~140 pre-step-6 call sites elsewhere in this file (now moved into
// RDFS.Closure/OWL.Closure) and any remaining external reference still
// resolve `indexed_graph`/`bucket_lookup`/`find_objects_indexed`/etc.
// unqualified.
include RDF.Indexed
// RDFS.Closure.fst / OWL.Closure.fst (2026-07-05, design doc
// "foundational-core-refactor" §2.4/§3.3 step 6) hold the RDFS
// entailment rules and the OWL 2 RL/RDF Datalog closure respectively —
// what used to be this file's sections 16 (RDFS vocab shim, now
// superseded by RDFS.Closure's own copy) and 18 through the end (RDFS
// closure rules, reflexivity axioms, ~40 owl_rule_* functions, OWL/XSD
// vocab, is_inconsistent, entailment_closure). Both modules open
// RDF.Term/RDF.Triple/RDF.Graph/RDF.Indexed but never this file — the
// same one-directional-edge discipline as RDF.Indexed above, so
// `include`ing them back here cannot cycle. See RDFS.Closure.fsti /
// OWL.Closure.fsti banners for the full rule-table cross-reference.
include RDFS.Closure
include OWL.Closure
// RDF.Term.fst / RDF.Triple.fst / RDF.Graph.fst (2026-07-05, design doc
// "foundational-core-refactor" §2.1/§2.2/§3.3 step 5) now hold the
// core term/triple/graph type tier that used to be defined directly
// below: `bnode_id`, `iri`, `wf_iri`, `is_iri`, `literal`, `wf_literal`,
// `rdf_term`, `subject`, `triple`, `rdf_graph`, `named_graph`,
// `rdf_dataset`, their decidable-equality functions, and the four
// per-type reflexivity lemmas (subject/literal/rdf_term/triple). See
// RDF.Term.fsti for the human-readable spec (start there if you want
// "what is a triple/graph/dataset", not this file).
//
// `include` (not `open`) is load-bearing, not a stylistic choice: F*'s
// `open` does not propagate transitively — a module C that does
// `open RDF.Graph.Executable` would not see RDF.Term's `T_IRI`
// unqualified through a mere `open` in this file, only through
// `include`, which re-exports a module's own bindings as part of this
// module's public interface. `include` is what makes all 53 existing
// `open RDF.Graph.Executable` dependents keep resolving
// `T_IRI`/`wf_iri`/`triple`/`rdf_dataset`/… unqualified with zero
// source changes — verified with a throwaway three-module compile
// experiment (A defines a variant + refinement type, B does
// `include A`, C does `open B` and pattern-matches/type-annotates
// unqualified) before relying on it for this file. Step 6 applies the
// exact same mechanism to RDFS.Closure/OWL.Closure below, once the
// RDFS/OWL-RL closure code (formerly this file's remaining ~4,500
// lines) moved out into them.
//
// OCaml extraction has no artifact for F*'s `include` (a module that
// only `include`s another extracts to an empty `.ml` beyond
// `open Prims` — confirmed empirically), so the *qualified* OCaml
// references this tree's hand-written glue makes
// (`RDF_Graph_Executable.T_IRI`, `.wf_iri`, `.rdf_graph`, …, in
// `experimental_ocaml_glue/*.sh` and the `bin/<consumer>/*.ml` files)
// would otherwise go unbound after this split. `build-ocaml.sh`'s
// post-extraction step carries the OCaml-side compatibility shim (a
// real OCaml `include RDF_Term`/`RDF_Triple`/`RDF_Graph` prepended to
// the extracted `RDF_Graph_Executable.ml`, which — unlike F*'s
// `include` — DOES re-export constructors and record field labels
// under the includer's namespace) so none of those consumers need any
// edit either. Retire both shims at design-doc step 7, once every
// consumer's `open`/qualified-reference is updated to name
// RDF.Term/RDF.Triple/RDF.Graph directly.
include RDF.Term
include RDF.Triple
include RDF.Graph

(* Blank node labels are scoped to the source document / dataset they came from.
   When multiple files are loaded independently and then merged for querying,
   equal raw labels like "_:x" must not collide accidentally across inputs.
   These helpers namespace blank nodes by a caller-supplied prefix. *)
let rename_bnode_id (prefix:string) (id:bnode_id) : bnode_id =
  String.concat "" [prefix; ":"; id]

let rename_subject_bnodes (prefix:string) (s:subject) : subject =
  match s with
  | S_IRI i -> S_IRI i
  | S_BNode b -> S_BNode (rename_bnode_id prefix b)

let rename_term_bnodes (prefix:string) (o:rdf_term) : rdf_term =
  match o with
  | T_IRI i -> T_IRI i
  | T_Literal l -> T_Literal l
  | T_BNode b -> T_BNode (rename_bnode_id prefix b)

let rename_triple_bnodes (prefix:string) (t:triple) : triple =
  {
    s = rename_subject_bnodes prefix t.s;
    p = t.p;
    o = rename_term_bnodes prefix t.o;
  }

// Computes the set of all blank nodes in the graph (subject then object per
// triple, triples in graph order). Tail-recursive accumulator form — avoids
// the cons-after-recurse + double-append that blew v8's stack on graphs with
// many bnodes. `List.Tot.rev` at the base restores the original order.
let rec graph_bnodes_acc (acc : list bnode_id) (g : rdf_graph)
  : Tot (list bnode_id) (decreases g) =
  match g with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
      let acc1 = match hd.s with | S_BNode id -> id :: acc  | _ -> acc  in
      let acc2 = match hd.o with | T_BNode id -> id :: acc1 | _ -> acc1 in
      graph_bnodes_acc acc2 tl

let graph_bnodes (g : rdf_graph) : list bnode_id =
  graph_bnodes_acc [] g

(** 6. Graph Operations **)

// mem_triple/graph_add moved to RDF.Graph.fst at step 6 (design doc
// §3.3) — RDFS.Closure/OWL.Closure's rules need graph_add's
// deduplicating insert and cannot `open RDF.Graph.Executable` (this
// file `include`s them back). Available here unqualified via `include
// RDF.Graph` above; graph_union below still calls `graph_add`
// unqualified exactly as before.

// O(1) prepend, no dedup. Bulk-parser hot path only — see
// docs/designissues/2026-04-25-fstar-rdf-graph-perf-prepend-finalise.md.
// Callers MUST run [graph_finalise] / [dataset_finalise] once at the end
// of the bulk parse to restore insertion order.
let graph_add_unchecked (t:triple) (g:rdf_graph) : rdf_graph = t :: g

// Restore insertion order after a sequence of [graph_add_unchecked] calls.
// Single-pass [List.Tot.rev] — Tot, total, F*-trivial termination on the
// list spine. Callers that want set semantics should compose with a
// downstream dedup; this helper does not dedup.
let graph_finalise (g:rdf_graph) : rdf_graph = List.Tot.rev g

// Apply [graph_finalise] to the default graph and every named graph in a
// dataset. Used once at the end of bulk N-Quads / TriG parsing.
let dataset_finalise (ds:rdf_dataset) : rdf_dataset =
  {
    ds_default = graph_finalise ds.ds_default;
    ds_named = List.Tot.map
      (fun (ng:named_graph) -> { ng_name = ng.ng_name;
                                 ng_graph = graph_finalise ng.ng_graph })
      ds.ds_named;
  }

// Remove all occurrences of a triple
let graph_remove (t:triple) (g:rdf_graph) : rdf_graph =
  List.Tot.filter (fun hd -> not (triple_eq hd t)) g

// graph_len moved to RDF.Graph.fst at step 6 (same reasoning as
// mem_triple/graph_add above) — available here unqualified via
// `include RDF.Graph`.

// Graph union (set union — deduplicated)
let rec graph_union (g1 g2:rdf_graph) : rdf_graph =
  match g1 with
  | [] -> g2
  | hd :: tl -> graph_union tl (graph_add hd g2)

// Find triples by subject IRI
let rec find_by_subject (subj:wf_iri) (g:rdf_graph) : rdf_graph =
  match g with
  | [] -> []
  | hd :: tl ->
    let rest = find_by_subject subj tl in
    match hd.s with
    | S_IRI i -> if i = subj then hd :: rest else rest
    | _ -> rest

// Find triples by predicate IRI
let rec find_by_predicate (pred:wf_iri) (g:rdf_graph) : rdf_graph =
  match g with
  | [] -> []
  | hd :: tl ->
    let rest = find_by_predicate pred tl in
    if hd.p = pred then hd :: rest else rest

(** 6b. Indexed Graph — for fast triple-pattern lookup (issue #100 Phase 0) **)
// The `bucket_map`/`indexed_graph`/`subject_to_key`/`find_objects_indexed`/
// `build_indexed`/etc. machinery that used to live here folded into
// RDF.Indexed.fst/.fsti at step 6 (design doc §2.3/§3.3) — step 3 could
// only move the generic `bucket_map` plumbing (see RDF.Indexed.fsti's
// banner for the cyclic-dependency finding that limited step 3's scope);
// step 5's RDF.Term/RDF.Triple/RDF.Graph split dissolved that cycle, so
// this step folds in the RDF-specific glue too. Available here
// unqualified via `include RDF.Indexed` above — no source change for
// any of this file's own remaining code or its 53 external dependents
// (SPARQL11.Algebra.fst's `bucket_lookup` call sites included).

(** 7. Equality Reflexivity Lemmas **)
// subject_eq/literal_eq/rdf_term_eq/triple_eq's own reflexivity lemmas
// (lemma_subject_eq_refl, lemma_literal_eq_refl, lemma_rdf_term_eq_refl,
// lemma_triple_eq_refl) moved to RDF.Term.fsti/RDF.Triple.fsti with
// their types (step 5) — available here unqualified via the `include`
// above. What stays here is graph-level, built on top of those.

// mem_triple finds t at the end of a list
let rec lemma_mem_triple_append (t : triple) (g : rdf_graph) :
  Lemma (mem_triple t (g @ [t]) = true) =
  match g with
  | [] -> lemma_triple_eq_refl t
  | hd :: tl ->
    if triple_eq hd t then ()
    else lemma_mem_triple_append t tl

(** 8. Graph Properties (verified) **)

// Removing a triple guarantees it's gone — PROVED (no more admit)
let rec lemma_remove_absent (t:triple) (g:rdf_graph) :
  Lemma (not (mem_triple t (graph_remove t g))) =
  match g with
  | [] -> ()
  | _ :: tl -> lemma_remove_absent t tl

(** 9. SPARQL Algebra Specification **)

// Variable names in SPARQL patterns
type var_name = string

// A pattern term: either a concrete RDF term or a variable
noeq type pattern_term =
  | PT_Concrete : rdf_term -> pattern_term
  | PT_Var      : var_name -> pattern_term

noeq type pattern_subject =
  | PS_Concrete : subject -> pattern_subject
  | PS_Var      : var_name -> pattern_subject

// A triple pattern in a Basic Graph Pattern
noeq type triple_pattern = {
  tp_s : pattern_subject;
  tp_p : wf_iri;       // Predicates are always IRIs in SPARQL 1.0
  tp_o : pattern_term;
}

// A solution mapping: variable -> RDF term
type solution_mapping = list (var_name * rdf_term)

// Basic Graph Pattern = list of triple patterns
type bgp = list triple_pattern

(* Section 9 once held a prototype `pattern_*_matches` / `algebra_op` /
   `solution_multiset` group; the production implementations of those
   live in `SPARQL11.Algebra.fst`. The dead prototypes were removed
   on 2026-05-16 (~50 lines). Section 10's `graph_isomorphic` /
   `roundtrip_preserves_triples` were spec-only stubs, also removed. *)

(* ======================================================================== *)
(* SPARQL Evaluation Semantics                                              *)
(* ======================================================================== *)
(* Formal specification of SPARQL typed value comparison, FILTER evaluation, *)
(* BIND semantics, and string functions.  Corresponds to the Rust           *)
(* implementation in sparql.rs (TypedFilterValue, typed_compare,            *)
(* eval_filter_expr_typed, evaluate_clauses/Bind).                          *)
(* ======================================================================== *)

(** 11. SPARQL Typed Value Comparison **)

// Numeric sub-types mirroring XSD numeric hierarchy
type numeric_type =
  | NT_Integer
  | NT_Decimal
  | NT_Double
  | NT_Float

// Comparison operators
type comp_op =
  | Eq
  | Ne
  | Lt
  | Gt
  | Le
  | Ge

// SPARQL typed values — mirrors Rust TypedFilterValue enum
// Each variant carries the data needed for comparison and evaluation.
type sparql_value =
  | SV_Numeric      : value:int -> ntype:numeric_type -> sparql_value
  | SV_PlainLiteral : lexical:string -> sparql_value
  | SV_LangLiteral  : lexical:string -> lang:string -> sparql_value
  | SV_Iri          : iri_str:string -> sparql_value
  | SV_BNode        : id:bnode_id -> sparql_value
  | SV_TypedLiteral : lexical:string -> datatype:wf_iri -> sparql_value
  | SV_Boolean      : b:bool -> sparql_value

// String comparison helper (lexicographic, same as OCaml/Rust string ordering)
// We leave this abstract; F* string comparison via = suffices for equality.
let string_lt (s1 s2 : string) : bool =
  String.compare s1 s2 < 0

// Typed value comparison — returns None for type errors (incompatible types)
// Mirrors typed_compare in sparql.rs
let value_compare (lv rv : sparql_value) (op : comp_op) : option bool =
  match lv, rv with
  // Numeric × numeric: cross-type comparison is always allowed
  | SV_Numeric ln _, SV_Numeric rn _ ->
    Some (match op with
          | Eq -> ln = rn
          | Ne -> ln <> rn
          | Lt -> ln < rn
          | Gt -> ln > rn
          | Le -> ln <= rn
          | Ge -> ln >= rn)

  // Boolean × boolean: only equality/inequality
  | SV_Boolean l, SV_Boolean r ->
    (match op with
     | Eq -> Some (l = r)
     | Ne -> Some (l <> r)
     | _  -> None)

  // Plain literal × plain literal: full ordering via string comparison
  | SV_PlainLiteral l, SV_PlainLiteral r ->
    Some (match op with
          | Eq -> l = r
          | Ne -> l <> r
          | Lt -> string_lt l r
          | Gt -> string_lt r l
          | Le -> l = r || string_lt l r
          | Ge -> l = r || string_lt r l)

  // Lang literal × lang literal: eq/ne only, both lexical and lang must match
  // Language tags compared case-insensitively per RDF 1.1
  | SV_LangLiteral llex llang, SV_LangLiteral rlex rlang ->
    (match op with
     | Eq -> Some (llex = rlex && lang_tag_eq llang rlang)
     | Ne -> Some (llex <> rlex || not (lang_tag_eq llang rlang))
     | _  -> None)

  // IRI × IRI: full ordering via string comparison
  | SV_Iri l, SV_Iri r ->
    Some (match op with
          | Eq -> l = r
          | Ne -> l <> r
          | Lt -> string_lt l r
          | Gt -> string_lt r l
          | Le -> l = r || string_lt l r
          | Ge -> l = r || string_lt r l)

  // BNode × BNode: equality/inequality only
  | SV_BNode l, SV_BNode r ->
    (match op with
     | Eq -> Some (l = r)
     | Ne -> Some (l <> r)
     | _  -> None)

  // Typed literal × typed literal: comparable only when datatypes match
  | SV_TypedLiteral llex ldt, SV_TypedLiteral rlex rdt ->
    if ldt = rdt then
      Some (match op with
            | Eq -> llex = rlex
            | Ne -> llex <> rlex
            | Lt -> string_lt llex rlex
            | Gt -> string_lt rlex llex
            | Le -> llex = rlex || string_lt llex rlex
            | Ge -> llex = rlex || string_lt rlex llex)
    else
      None  // different unknown datatypes → type error

  // All other combinations: incompatible types → type error
  | _, _ -> None

(** 12. SPARQL FILTER Evaluation — Boolean Effective Value **)

// The boolean effective value (EBV) of a SPARQL value determines its truth
// when used in a FILTER context.  Mirrors the BooleanEffectiveValue branch
// of eval_filter in sparql.rs.
//
// Rules (SPARQL 1.1 §17.2.2):
//   - Boolean "true" or "1" → true
//   - Numeric non-zero → true
//   - Non-empty plain string → true
//   - Empty string, "false", "0", zero → false
//   - Lang literals with non-empty lexical → true
//   - Other types → type error (we return false, matching Rust impl)

let boolean_effective_value (v : sparql_value) : bool =
  match v with
  | SV_Boolean b -> b
  | SV_Numeric n _ -> n <> 0
  | SV_PlainLiteral s -> String.length s > 0
  | SV_LangLiteral s _ -> String.length s > 0
  | SV_Iri _ -> false       // IRIs have no boolean interpretation
  | SV_BNode _ -> false     // BNodes have no boolean interpretation
  | SV_TypedLiteral _ _ -> false  // Unknown typed literals → false

(** 13. SPARQL BIND Semantics **)

// BIND assigns the result of an expression to a variable in each solution.
// If the expression evaluates to None, the variable remains unbound.
// Crucially, BIND does not overwrite existing bindings — the SPARQL spec
// requires the target variable to be unbound in the current scope.
//
// Mirrors evaluate_clauses/WhereClause::Bind in sparql.rs.

// Expression evaluation result: either a concrete RDF term or error (None)
// We abstract over the expression language; in the Rust impl this is FilterExpr.
type filter_expr_eval = solution_mapping -> option rdf_term

// BIND evaluation: given an expression evaluator and a solution mapping,
// produce a (variable, term) pair if the expression succeeds
let bind_eval (eval : filter_expr_eval) (var : var_name) (mu : solution_mapping)
  : option (var_name * rdf_term) =
  match List.Tot.assoc var mu with
  | Some _ -> None  // variable already bound — do not overwrite (SPARQL spec)
  | None ->
    match eval mu with
    | Some term -> Some (var, term)
    | None      -> None  // expression error → variable stays unbound

// Apply BIND to a solution mapping: extend it if the expression succeeds
let apply_bind (eval : filter_expr_eval) (var : var_name) (mu : solution_mapping)
  : solution_mapping =
  match bind_eval eval var mu with
  | Some pair -> pair :: mu
  | None      -> mu

(** 14. SPARQL String Function Signatures **)

// Type specifications for SPARQL 1.1 string functions. The SPARQL 1.1
// evaluator now lives in `SPARQL11.Algebra.fst` (sparql_value-typed,
// language/datatype-preserving); the once-shadow `sparql_strlen` /
// `sparql_substr` / `sparql_ucase` / `sparql_lcase` were removed
// (2026-05-16). `string_substring` and `sparql_concat` remain — both
// are reused by external callers (OWL.QueryRewrite and the F*-side
// CONCAT spec respectively).

// SUBSTR helper: 1-indexed substring extraction primitive. Used by
// SPARQL11.Algebra.fst and OWL.QueryRewrite.fst.
let string_substring (s : string) (i : nat) (len : nat) : string =
  let slen = String.length s in
  if i >= slen then ""
  else
    let max_len = slen - i in
    let actual_len = if len <= max_len then len else max_len in
    String.sub s i actual_len

// CONCAT: concatenate a list of strings
let rec sparql_concat (args : list string) : string =
  match args with
  | [] -> ""
  | hd :: tl -> String.concat "" [hd; sparql_concat tl]

(** 15. Properties and Lemmas **)

(* Section 15 once held `lemma_compare_reflexive`, `_compare_symmetric`,
   and `_incompatible_types`. They had no callers and no SMTPats, so
   the verifier wasn't using them to discharge anything elsewhere.
   Removed 2026-05-16 (~40 lines). The properties still hold; the
   lemmas can be re-added if a downstream proof obligation needs
   them. *)

// BIND preserves existing bindings: if a variable is already bound,
// apply_bind does not modify the solution mapping — PROVED
let lemma_bind_preserves_existing
  (eval:filter_expr_eval) (var:var_name) (mu:solution_mapping) :
  Lemma (match List.Tot.assoc var mu with
         | Some _ -> apply_bind eval var mu == mu
         | None -> True) =
  match List.Tot.assoc var mu with
  | Some _ -> ()  // bind_eval returns None when var is already bound → apply_bind returns mu
  | None -> ()    // trivially True

(** ======================================================================== *)
(** 16. RDF/RDFS Vocabulary Constants — moved to RDFS.Closure at step 6      *)
(** ======================================================================== *)
// `rdfs_subClassOf`/`rdfs_domain`/`rdfs_range`/`rdf_type`/`rdfs_Class`/
// `rdf_Property`/`rdfs_Resource`/`rdfs_Literal`/
// `rdfs_ContainerMembershipProperty`/`rdfs_member`/`rdfs_Datatype`/
// `rdf_1`..`rdf_5`/`container_membership_properties` (this section's
// former re-export shim, step 2) now have their canonical re-derivation
// in RDFS.Closure.fsti instead (design doc §2.4/§3.3 step 6) — the
// RDFS/OWL-RL closure rules that need them moved there and cannot
// depend on this file (cycle: this file `include`s RDFS.Closure back).
// Available here unqualified via `include RDFS.Closure` above; this
// section is deliberately left with no `let`s of its own to avoid a
// duplicate-definition error against that include.

(** ======================================================================== *)
(** 17. RDFS Helper Functions                                                *)
(** ======================================================================== *)
// subject_to_term/term_to_subject moved to RDF.Graph.fst at step 6
// (design doc §3.3, same reasoning as mem_triple/graph_add above) —
// available here unqualified via `include RDF.Graph`. find_objects/
// find_subjects below stay local: no closure-rule caller (grep-
// confirmed — only external `.fst` modules like ShEx.Validation.fst/
// Tableau.fst/SHACL.Validation.fst use them).

(* Find all objects where (s p ?o) in graph *)
// Tail-recursive accumulator form; List.Tot.rev at base preserves input order.
// Addresses wdt:P31 stack-blow on 60k-triple graphs with 1000+ matches.
let rec find_objects_acc (acc : list rdf_term) (g : rdf_graph) (subj : subject) (pred : wf_iri)
  : Tot (list rdf_term) (decreases g) =
  match g with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
    if subject_eq hd.s subj && hd.p = pred
    then find_objects_acc (hd.o :: acc) tl subj pred
    else find_objects_acc acc tl subj pred

let find_objects (g : rdf_graph) (subj : subject) (pred : wf_iri) : list rdf_term =
  find_objects_acc [] g subj pred

(* Find all subjects where (?s p o) in graph *)
let rec find_subjects_acc (acc : list subject) (g : rdf_graph) (pred : wf_iri) (obj : rdf_term)
  : Tot (list subject) (decreases g) =
  match g with
  | [] -> List.Tot.rev acc
  | hd :: tl ->
    if hd.p = pred && rdf_term_eq hd.o obj
    then find_subjects_acc (hd.s :: acc) tl pred obj
    else find_subjects_acc acc tl pred obj

let find_subjects (g : rdf_graph) (pred : wf_iri) (obj : rdf_term) : list subject =
  find_subjects_acc [] g pred obj

// add_triple_if_new/add_triple_unchecked/term_to_key_total/triple_to_key/
// triple_cmp/dedup_sorted_aux/graph_dedup_sort/add_triples_if_new moved
// to RDF.Graph.fst at step 6 (design doc §3.3) — the RDFS.Closure/
// OWL.Closure closure rules need all of these and cannot `open
// RDF.Graph.Executable` (this file `include`s them back). Available
// here unqualified via `include RDF.Graph` above; Tableau.fst and other
// external dependents of this file see them unqualified too, unchanged.

(** ======================================================================== *)
(** 18-20. RDFS Closure Rules / Fixed-Point Closure / Reflexivity Axioms /   *)
(** OWL 2 RL Datalog Closure / Datatype Value Equivalence / Inconsistency /  *)
(** Entailment Dispatch — moved to RDFS.Closure.fst / OWL.Closure.fst       *)
(** ======================================================================== *)
// The ~40 owl_rule_* functions, the 7 rdfs_rule_* functions, is_inconsistent,
// and the closure drivers (rdfs_closure/rdfs_closure_step/
// rdfs_closure_with_reflexivity, owl_rl_closure_step_mode/
// owl_rl_closure_mode/owl_rl_closure/owl_rl_closure_with_reflexivity_mode/
// owl_rl_closure_with_reflexivity, entailment_closure) moved to
// RDFS.Closure.fst(i) / OWL.Closure.fst(i) at step 6 (design doc
// §2.4/§3.3) — see those modules' banners for the full OWL 2 RL/RDF
// rule-table cross-reference and the dependency-direction reasoning
// (RDFS.Closure / OWL.Closure open RDF.Term/RDF.Triple/RDF.Graph/
// RDF.Indexed but never this file; this file `include`s them back, the
// same mechanism step 5 established for RDF.Term/RDF.Triple/RDF.Graph).
// Available here unqualified via `include RDFS.Closure` / `include
// OWL.Closure` above — Tableau.fst, SHACL.Validation.fst,
// RDF.Vocabulary.Axioms.fst, OWL.QueryRewrite.fst, and
// Parser.OWLFunctional.fst (this file's `.fst`-level dependents on
// these names, confirmed by grep) all keep resolving them unqualified
// with zero source changes. RDF.Graph.Executable.fst's line count:
// 5104 lines before step 6, ~526 after (the foundational term/graph
// scaffolding plus the SPARQL FILTER/BIND fragment and the vocabulary/
// helper functions that don't belong to the closure layer) — see the
// design doc's step-6 row for the measured before/after.
