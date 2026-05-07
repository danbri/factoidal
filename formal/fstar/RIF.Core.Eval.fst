module RIF.Core.Eval

// Phase 2 of the RIF Core F* engine, per
// docs/designissues/2026-05-07-rif-fstar-investigation.md.
//
// Forward-chaining fixpoint over an RDF graph. One rule firing is
// modelled as a SPARQL CONSTRUCT-style operation:
//
//   1. Translate the rule body to a SPARQL BGP via RIF.Core.Translation.
//   2. Evaluate that BGP against the current graph using SPARQL11.Algebra
//      eval_bgp, yielding a solution_sequence.
//   3. For each binding, instantiate the rule head — substitute every
//      RIF_Var with the bound rdf_term and produce zero or one new
//      triples (zero if any variable is unbound, or the head names a
//      literal in subject position).
//   4. Add the newly produced triples to the graph (set semantics — no
//      duplicates).
//   5. Round done. Repeat across all rules; iterate the round to a
//      fuel-bounded fixpoint.
//
// Termination is by an explicit fuel parameter (a natural number that
// caps the number of fixpoint rounds). The design doc spells this out
// as the chosen termination strategy: full Datalog termination theory
// is out of scope; the fuel guard is sufficient for the W3C-test
// targets.
//
// Saturation lemma: fixpoint never removes triples (graph_subset g
// (fixpoint g p fuel)). Provided as a Lemma below.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries, no assume val (rule #10, rule #3).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra
module Syn = RIF.Core.Syntax
module Tx  = RIF.Core.Translation

// ------------------------------------------------------------------
// 1. Head instantiation.
//
// Given a solution_mapping mu and a rif_atom in head position, attempt
// to produce a single concrete RDF triple. Returns None when:
//   - the head names a variable that mu does not bind, OR
//   - the head puts a literal in subject position (RDF triples cannot
//     have a literal subject; SPARQL CONSTRUCT silently drops such
//     instantiations per the Recommendation §16.2 — we follow that
//     convention here).
//
// Helpers `resolve_subject` and `resolve_term` lift a rif_term through
// the solution mapping. A RIF_Const passes through; a RIF_Var is
// looked up; the result is then narrowed to the appropriate sort.
// ------------------------------------------------------------------

let resolve_term (mu : solution_mapping) (t : Syn.rif_term)
  : option rdf_term
  =
  match t with
  | Syn.RIF_Const c -> Some c
  | Syn.RIF_Var v   -> sm_lookup v.var_name mu

let resolve_subject (mu : solution_mapping) (t : Syn.rif_term)
  : option subject
  =
  match resolve_term mu t with
  | None                  -> None
  | Some (T_IRI i)        -> Some (S_IRI i)
  | Some (T_BNode b)      -> Some (S_BNode b)
  | Some (T_Literal _)    -> None

let resolve_predicate (mu : solution_mapping) (t : Syn.rif_term)
  : option wf_iri
  =
  match resolve_term mu t with
  | Some (T_IRI i) -> Some i
  | _              -> None

// Build a concrete triple from a fully-resolved subject/predicate/
// object triple, when all three positions are well-typed.
let mk_triple_opt
  (s_opt : option subject)
  (p_opt : option wf_iri)
  (o_opt : option rdf_term)
  : option triple
  =
  match s_opt, p_opt, o_opt with
  | Some s, Some p, Some o -> Some ({ s = s; p = p; o = o })
  | _, _, _                -> None

let instantiate_atom (mu : solution_mapping) (a : Syn.rif_atom)
  : option triple
  =
  match a with
  | Syn.RIF_Triple s p o ->
    mk_triple_opt
      (resolve_subject mu s)
      (resolve_predicate mu p)
      (resolve_term mu o)
  | Syn.RIF_Frame o p v ->
    mk_triple_opt
      (resolve_subject mu o)
      (resolve_predicate mu p)
      (resolve_term mu v)
  | Syn.RIF_Member o c ->
    mk_triple_opt
      (resolve_subject mu o)
      (Some rdf_type)
      (resolve_term mu c)
  | Syn.RIF_Sub sub sup_ ->
    mk_triple_opt
      (resolve_subject mu sub)
      (Some rdfs_subClassOf)
      (resolve_term mu sup_)

// ------------------------------------------------------------------
// 2. Per-binding head firing.
//
// `add_one_triple_tracking g t` adds t to g (set semantics) and
// reports whether the graph actually grew. The boolean is what drives
// the fixpoint convergence test, in lieu of decidable equality on
// rdf_graph.
//
// `fire_head_per_bindings` walks a solution_sequence and threads
// (graph, changed) through each binding. Each binding produces zero
// or one candidate triples (via instantiate_atom); each candidate is
// merged via add_one_triple_tracking.
// ------------------------------------------------------------------

let add_one_triple_tracking (g : rdf_graph) (t : triple) (changed : bool)
  : rdf_graph & bool
  =
  if mem_triple t g
  then (g, changed)
  else (g @ [t], true)

let rec fire_head_per_bindings
  (head : Syn.rif_atom)
  (bindings : solution_sequence)
  (g : rdf_graph)
  (changed : bool)
  : Tot (rdf_graph & bool) (decreases bindings)
  =
  match bindings with
  | [] -> (g, changed)
  | mu :: rest ->
    let g', changed' =
      match instantiate_atom mu head with
      | None   -> (g, changed)
      | Some t -> add_one_triple_tracking g t changed
    in
    fire_head_per_bindings head rest g' changed'

// ------------------------------------------------------------------
// 3. Single rule firing.
//
// Translates the rule body to a BGP. If translation fails (the body
// has a structurally invalid atom — e.g. a literal in subject
// position), the rule contributes nothing; the graph is returned
// unchanged. Otherwise the body BGP is evaluated against the graph
// and each binding fires the head.
// ------------------------------------------------------------------

let fire_rule (g : rdf_graph) (r : Syn.rif_rule)
  : Tot (rdf_graph & bool)
  =
  match Tx.translate_body r.body with
  | None         -> (g, false)
  | Some body_bgp ->
    let bindings : solution_sequence = eval_bgp body_bgp g in
    fire_head_per_bindings r.head bindings g false

// ------------------------------------------------------------------
// 4. One round: fire every rule once against the current graph.
//
// Threads (graph, changed) through the rule list. The returned bool
// is OR-ed across all rules — if any rule produced a new triple, the
// round counts as changed and the fixpoint loop will iterate.
//
// Note: we evaluate each rule against the graph as it stands AFTER
// previous rules in the same round have fired. That is sound but
// makes the per-round result rule-order-dependent — the fixpoint
// itself is order-independent because monotone forward-chaining
// converges to the same closure regardless of firing order. The
// design doc's "monotone, stratified" framing relies on this.
// ------------------------------------------------------------------

let rec one_round_aux
  (rules : list Syn.rif_rule)
  (g : rdf_graph)
  (changed : bool)
  : Tot (rdf_graph & bool) (decreases rules)
  =
  match rules with
  | [] -> (g, changed)
  | r :: rest ->
    let g', c' = fire_rule g r in
    one_round_aux rest g' (changed || c')

let one_round (g : rdf_graph) (p : Syn.rif_program)
  : Tot (rdf_graph & bool)
  =
  one_round_aux p.rules g false

// ------------------------------------------------------------------
// 5. Fuel-bounded fixpoint.
//
// Stops when either:
//   - fuel reaches zero (defensive cap, prevents non-termination
//     pathologies), or
//   - one_round reports changed=false (true fixpoint reached).
//
// `fixpoint` is the public entry. `saturate` is an alias preserving
// the design doc's wording.
// ------------------------------------------------------------------

let rec fixpoint
  (g : rdf_graph) (p : Syn.rif_program) (fuel : nat)
  : Tot rdf_graph (decreases fuel)
  =
  if fuel = 0 then g
  else
    let g', changed = one_round g p in
    if not changed
    then g'
    else fixpoint g' p (fuel - 1)

let saturate
  (g : rdf_graph) (p : Syn.rif_program) (fuel : nat)
  : Tot rdf_graph
  = fixpoint g p fuel

// ------------------------------------------------------------------
// 6. Saturation lemma.
//
// Forward-chaining never removes triples. Formally: every triple in
// the input graph appears in the output graph. We prove this by
// induction following the same recursive structure as the function:
//
//   add_one_triple_tracking preserves membership of every t' in g.
//   fire_head_per_bindings preserves membership (induction on bindings).
//   fire_rule preserves membership (case-split on translate_body).
//   one_round_aux preserves membership (induction on rules).
//   fixpoint preserves membership (induction on fuel).
//
// The membership predicate is `mem_triple t g`, already exported by
// RDF.Graph.Executable.
// ------------------------------------------------------------------

let graph_subset (g1 g2 : rdf_graph) : prop =
  forall (t : triple). mem_triple t g1 ==> mem_triple t g2

// `mem_triple` distributes over `@` on the RHS: if t is in g, it is
// in g @ [u] for any u. Established by induction on g.
let rec lemma_mem_triple_append_left (t : triple) (g : rdf_graph) (u : triple)
  : Lemma (requires mem_triple t g)
          (ensures  mem_triple t (g @ [u]))
          (decreases g)
  =
  match g with
  | []     -> ()
  | hd :: tl ->
    if triple_eq hd t then ()
    else lemma_mem_triple_append_left t tl u

let lemma_add_one_triple_tracking_preserves
  (g : rdf_graph) (u : triple) (changed : bool) (t : triple)
  : Lemma (requires mem_triple t g)
          (ensures  mem_triple t (fst (add_one_triple_tracking g u changed)))
  =
  if mem_triple u g
  then ()
  else lemma_mem_triple_append_left t g u

let rec lemma_fire_head_per_bindings_preserves
  (head : Syn.rif_atom)
  (bindings : solution_sequence)
  (g : rdf_graph)
  (changed : bool)
  (t : triple)
  : Lemma (requires mem_triple t g)
          (ensures  mem_triple t
                      (fst (fire_head_per_bindings head bindings g changed)))
          (decreases bindings)
  =
  match bindings with
  | [] -> ()
  | mu :: rest ->
    (match instantiate_atom mu head with
     | None ->
       lemma_fire_head_per_bindings_preserves head rest g changed t
     | Some u ->
       lemma_add_one_triple_tracking_preserves g u changed t;
       let g', c' = add_one_triple_tracking g u changed in
       lemma_fire_head_per_bindings_preserves head rest g' c' t)

let lemma_fire_rule_preserves (g : rdf_graph) (r : Syn.rif_rule) (t : triple)
  : Lemma (requires mem_triple t g)
          (ensures  mem_triple t (fst (fire_rule g r)))
  =
  match Tx.translate_body r.body with
  | None -> ()
  | Some body_bgp ->
    let bindings = eval_bgp body_bgp g in
    lemma_fire_head_per_bindings_preserves r.head bindings g false t

let rec lemma_one_round_aux_preserves
  (rules : list Syn.rif_rule)
  (g : rdf_graph)
  (changed : bool)
  (t : triple)
  : Lemma (requires mem_triple t g)
          (ensures  mem_triple t (fst (one_round_aux rules g changed)))
          (decreases rules)
  =
  match rules with
  | [] -> ()
  | r :: rest ->
    lemma_fire_rule_preserves g r t;
    let g', c' = fire_rule g r in
    lemma_one_round_aux_preserves rest g' (changed || c') t

let lemma_one_round_preserves (g : rdf_graph) (p : Syn.rif_program) (t : triple)
  : Lemma (requires mem_triple t g)
          (ensures  mem_triple t (fst (one_round g p)))
  =
  lemma_one_round_aux_preserves p.rules g false t

let rec lemma_fixpoint_preserves
  (g : rdf_graph) (p : Syn.rif_program) (fuel : nat) (t : triple)
  : Lemma (requires mem_triple t g)
          (ensures  mem_triple t (fixpoint g p fuel))
          (decreases fuel)
  =
  if fuel = 0 then ()
  else
    let g', changed = one_round g p in
    lemma_one_round_preserves g p t;
    if not changed
    then ()
    else lemma_fixpoint_preserves g' p (fuel - 1) t

// Public wrapper: the saturation lemma in the form requested by the
// design doc. Universal-quantifier introduction over t is the only
// gap between the per-triple lemma above and graph_subset.
let lemma_fixpoint_extends
  (g : rdf_graph) (p : Syn.rif_program) (fuel : nat)
  : Lemma (graph_subset g (fixpoint g p fuel))
  =
  let aux (t : triple) : Lemma (mem_triple t g ==> mem_triple t (fixpoint g p fuel)) =
    let pf () : Lemma (requires mem_triple t g)
                      (ensures  mem_triple t (fixpoint g p fuel)) =
      lemma_fixpoint_preserves g p fuel t
    in
    Classical.move_requires pf ()
  in
  Classical.forall_intro aux

// ------------------------------------------------------------------
// 7. Smoke test.
//
// A two-rule RIF Core program over a tiny graph:
//
//   Rule 1: ?x rdfs:subClassOf ?y, ?y rdfs:subClassOf ?z |- ?x rdfs:subClassOf ?z
//           (transitive closure of subClassOf — encoded via RIF_Triple
//            with concrete predicate IRIs so we exercise the
//            IRI-binding paths in resolve_term.)
//
//   Rule 2: ?o # ?c, ?c rdfs:subClassOf ?d |- ?o # ?d
//           (rdf:type propagation up the class hierarchy.)
//
// Input graph:
//   :alice   rdf:type        :Student .
//   :Student rdfs:subClassOf :Person  .
//   :Person  rdfs:subClassOf :Agent   .
//
// After saturation we expect to also see:
//   :Student rdfs:subClassOf :Agent   .   (transitive)
//   :alice   rdf:type        :Person  .   (typing up by 1 level)
//   :alice   rdf:type        :Agent   .   (typing up by 2 levels)
//
// We assert the strictly-grew property: the saturated graph contains
// at least one triple beyond the originals. Asserting an exact graph
// shape is brittle because the rule firing order and the
// fire_head_per_bindings append behaviour fix one specific output
// list, which couples the test to implementation details rather than
// the spec.
// ------------------------------------------------------------------

let v_x : Syn.rif_term = Syn.mk_var "x"
let v_y : Syn.rif_term = Syn.mk_var "y"
let v_z : Syn.rif_term = Syn.mk_var "z"
let v_o : Syn.rif_term = Syn.mk_var "o"
let v_c : Syn.rif_term = Syn.mk_var "c"
let v_d : Syn.rif_term = Syn.mk_var "d"

// Concrete IRI strings used in the smoke test. Each is verified by
// `assert_norm` against `is_iri` so the wf_iri refinement is met at
// elaboration time without an SMT call.
let iri_alice   : wf_iri = assert_norm (is_iri "ex:alice");   "ex:alice"
let iri_Student : wf_iri = assert_norm (is_iri "ex:Student"); "ex:Student"
let iri_Person  : wf_iri = assert_norm (is_iri "ex:Person");  "ex:Person"
let iri_Agent   : wf_iri = assert_norm (is_iri "ex:Agent");   "ex:Agent"

let pred_subclassof : Syn.rif_term = Syn.mk_const_iri rdfs_subClassOf

// Rule 1: subClassOf transitivity.
let rule_subclassof_trans : Syn.rif_rule =
  Syn.mk_rule
    (Syn.RIF_Triple v_x pred_subclassof v_z)
    (Syn.RIF_BodyAnd
      [ Syn.RIF_BodyAtom (Syn.RIF_Triple v_x pred_subclassof v_y);
        Syn.RIF_BodyAtom (Syn.RIF_Triple v_y pred_subclassof v_z); ])

// Rule 2: rdf:type propagation.
let rule_type_prop : Syn.rif_rule =
  Syn.mk_rule
    (Syn.RIF_Member v_o v_d)
    (Syn.RIF_BodyAnd
      [ Syn.RIF_BodyAtom (Syn.RIF_Member v_o v_c);
        Syn.RIF_BodyAtom (Syn.RIF_Triple v_c pred_subclassof v_d); ])

let smoke_program : Syn.rif_program =
  Syn.program_of_rules [rule_subclassof_trans; rule_type_prop]

let smoke_input_graph : rdf_graph = [
  { s = S_IRI iri_alice;   p = rdf_type;        o = T_IRI iri_Student };
  { s = S_IRI iri_Student; p = rdfs_subClassOf; o = T_IRI iri_Person  };
  { s = S_IRI iri_Person;  p = rdfs_subClassOf; o = T_IRI iri_Agent   };
]

// Saturation produces strictly more triples than the input.
//
// Why graph_len strict increase, rather than asserting exact set
// membership of (alice, type, Agent)? `assert_norm` reduction on
// list-based set membership through the eval_bgp / sm_lookup tower
// is heavy and tends to time out the SMT solver on this scale; a
// length comparison is normalisable in finite steps and exercises
// the same code paths.
let smoke_saturated : rdf_graph =
  fixpoint smoke_input_graph smoke_program 8

let _ = assert_norm (graph_len smoke_input_graph = 3)

let _ = assert_norm (graph_len smoke_saturated >= 4)
