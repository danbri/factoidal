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
module B   = RIF.Core.Builtins

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

// eval_rif_term / eval_rif_term_list evaluate a rif_term against a
// binding, recursively resolving nested External(...) function calls
// (RIF_TermExternal) via RIF.Core.Builtins.eval_function — needed for
// head atoms like Chaining_strategy_numeric-add_1's
// `ex:a(External(func:numeric-add(?x 1)))` and Equal-RHS terms like
// Factorial_Forward_Chaining's `?N = External(func:numeric-add(?N1 1))`.
// Mutual recursion across rif_term / list rif_term mirrors
// RIF.Core.Syntax.fst's rif_term_eq / rif_term_list_eq (args is a
// genuine structural subterm of RIF_TermExternal op args).
let rec eval_rif_term (mu : solution_mapping) (t : Syn.rif_term)
  : Tot (option rdf_term) (decreases t)
  =
  match t with
  | Syn.RIF_Const c -> Some c
  | Syn.RIF_Var v   -> sm_lookup v.var_name mu
  | Syn.RIF_TermExternal op args ->
    (match eval_rif_term_list mu args with
     | None -> None
     | Some vals -> B.eval_function op vals)

and eval_rif_term_list (mu : solution_mapping) (ts : list Syn.rif_term)
  : Tot (option (list rdf_term)) (decreases ts)
  =
  match ts with
  | [] -> Some []
  | t :: rest ->
    (match eval_rif_term mu t with
     | None -> None
     | Some v ->
       (match eval_rif_term_list mu rest with
        | None -> None
        | Some vs -> Some (v :: vs)))

let resolve_term (mu : solution_mapping) (t : Syn.rif_term)
  : option rdf_term
  =
  eval_rif_term mu t

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

// Lenient subject resolution for RIF_Triple/RIF_Uniterm's internal
// Uniterm-fact encoding — mirrors RIF.Core.Translation.
// rif_term_to_uniterm_subject on the QUERY side, so a literal
// argument round-trips to the SAME blank node on both the assertion
// side (here) and the query side. See that function's comment for
// the full rationale (RIF Uniterms permit a literal in any argument
// position; Frame/Member/Sub's `resolve_subject` above stays strict
// for genuine RDF-in-RIF combination semantics).
let resolve_uniterm_subject (mu : solution_mapping) (t : Syn.rif_term)
  : option subject
  =
  match resolve_term mu t with
  | None                  -> None
  | Some (T_IRI i)        -> Some (S_IRI i)
  | Some (T_BNode b)      -> Some (S_BNode b)
  | Some (T_Literal l)    -> Some (S_BNode (Tx.literal_subject_bnode_label l))

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
      (resolve_uniterm_subject mu s)
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
  | Syn.RIF_Uniterm pred args ->
    // Same internal arity-0/arity-1 encoding RIF.Core.Translation's
    // translate_atom uses for the ASK/BGP side — round-trip
    // consistent since both directions share the same marker
    // constants.
    (match resolve_predicate mu pred, args with
     | Some p, [] ->
       mk_triple_opt (Some (S_IRI Tx.rif_uniterm_nullary_subject)) (Some p)
         (Some Tx.rif_uniterm_true_marker)
     | Some p, [a] ->
       // Argument in OBJECT position (see RIF.Core.Translation.
       // translate_atom's matching RIF_Uniterm/[a] case for why).
       mk_triple_opt (Some (S_IRI Tx.rif_uniterm_nullary_subject)) (Some p) (resolve_term mu a)
     | _, _ -> None)

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
// 2b. External(...)/Equal body-condition evaluation.
//
// RIF.Core.Translation.split_body separates a rule body into the
// ordinary atoms (Triple/Frame/Member/Sub/Uniterm — joined via the
// existing BGP/eval_bgp path below) and the "extra conditions"
// (External-as-formula predicate calls, and Equal atoms) that cannot
// become SPARQL triple patterns. Those extras are evaluated per
// candidate binding AFTER the ordinary-atom BGP join, in the body's
// original left-to-right order:
//   - EC_External op args: a builtin PREDICATE filter — keep the
//     binding iff the builtin evaluates to true (Some true); drop it
//     on Some false OR on evaluation failure (an argument didn't
//     resolve — e.g. an unbound variable this project's binding-
//     pattern EXECUTION does not support, conservatively dropped
//     rather than guessed).
//   - EC_Equal lhs rhs: if lhs is a variable NOT YET bound by this
//     point, this is a BIND — evaluate rhs under the current binding
//     and extend the binding with lhs := rhs (Factorial_Forward_
//     Chaining's `?N = External(func:numeric-add(?N1 1))` and
//     similar chained-computation shapes). If lhs is already bound
//     (or is itself a constant/nested External), this is a ground
//     equality filter — both sides are evaluated and compared, using
//     RIF.Core.Builtins' cross-type numeric comparison when both
//     sides are numeric (so `"2"^^xs:integer = numeric-divide(6 3)`,
//     whose RHS naturally produces an xsd:decimal "2.0", compares
//     equal by VALUE per RIF-DTB, not by strict term/datatype
//     identity) and falling back to structural identity otherwise.
// ------------------------------------------------------------------

let rif_equal_values (a b : rdf_term) : bool =
  match B.numeric_predicate CmpEq a b with
  | Some r -> r
  | None   -> rdf_term_eq a b

let apply_extra_condition (mu : solution_mapping) (ec : Tx.rif_extra_condition)
  : option solution_mapping
  =
  match ec with
  | Tx.EC_External op args ->
    (match eval_rif_term_list mu args with
     | None -> None
     | Some vals ->
       (match B.eval_predicate op vals with
        | Some true  -> Some mu
        | Some false -> None
        | None       -> None))
  | Tx.EC_Equal lhs rhs ->
    (match lhs with
     | Syn.RIF_Var v ->
       (match sm_lookup v.var_name mu with
        | None ->
          // Unbound: this Equal acts as a BIND.
          (match eval_rif_term mu rhs with
           | None    -> None
           | Some rv -> Some (sm_bind v.var_name rv mu))
        | Some existing ->
          // Already bound: plain equality filter.
          (match eval_rif_term mu rhs with
           | None    -> None
           | Some rv -> if rif_equal_values existing rv then Some mu else None))
     | _ ->
       (match eval_rif_term mu lhs, eval_rif_term mu rhs with
        | Some lv, Some rv -> if rif_equal_values lv rv then Some mu else None
        | _, _ -> None))

let rec apply_extra_conditions
  (mu : solution_mapping) (ecs : list Tx.rif_extra_condition)
  : Tot (option solution_mapping) (decreases ecs)
  =
  match ecs with
  | [] -> Some mu
  | ec :: rest ->
    (match apply_extra_condition mu ec with
     | None     -> None
     | Some mu' -> apply_extra_conditions mu' rest)

let rec filter_bindings_by_extras
  (ecs : list Tx.rif_extra_condition) (bindings : solution_sequence)
  : Tot solution_sequence (decreases bindings)
  =
  match bindings with
  | [] -> []
  | mu :: rest ->
    (match apply_extra_conditions mu ecs with
     | Some mu' -> mu' :: filter_bindings_by_extras ecs rest
     | None     -> filter_bindings_by_extras ecs rest)

// ------------------------------------------------------------------
// 3. Single rule firing.
//
// Splits the body into ordinary atoms (translated to a BGP and
// joined via eval_bgp, exactly as before) and extra conditions
// (External/Equal, evaluated per-binding above). If the ordinary-atom
// part fails to translate (a structurally invalid atom — e.g. a
// literal in subject position), the rule contributes nothing.
// ------------------------------------------------------------------

let fire_rule (g : rdf_graph) (r : Syn.rif_rule)
  : Tot (rdf_graph & bool)
  =
  let (ordinary_atoms, extras) = Tx.split_body r.body in
  match Tx.translate_atoms_bgp ordinary_atoms with
  | None         -> (g, false)
  | Some body_bgp ->
    let bindings0 : solution_sequence = eval_bgp body_bgp g in
    let bindings1 = filter_bindings_by_extras extras bindings0 in
    fire_head_per_bindings r.head bindings1 g false

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
  let (ordinary_atoms, extras) = Tx.split_body r.body in
  match Tx.translate_atoms_bgp ordinary_atoms with
  | None -> ()
  | Some body_bgp ->
    let bindings0 = eval_bgp body_bgp g in
    let bindings1 = filter_bindings_by_extras extras bindings0 in
    lemma_fire_head_per_bindings_preserves r.head bindings1 g false t

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

// Saturation produces exactly the three new triples expected by the
// rule semantics:
//   :Student rdfs:subClassOf :Agent   (rule 1, transitivity)
//   :alice   rdf:type        :Person  (rule 2, type propagation 1 step)
//   :alice   rdf:type        :Agent   (rule 2, type propagation 2 steps)
//
// The earlier check `graph_len smoke_saturated >= 4` was technically
// correct but under-specified — it confirmed at least one new triple
// without pinning which inferences fired. Asserting exact-membership
// of all three derived triples is the spec-level statement, and it
// passes once the normaliser has enough fuel to grind through the
// graph_store / eval_bgp / sm_lookup tower across two fixpoint rounds.
let smoke_saturated : rdf_graph =
  fixpoint smoke_input_graph smoke_program 8

let _ = assert_norm (graph_len smoke_input_graph = 3)

#push-options "--initial_fuel 64 --max_fuel 256 --initial_ifuel 16 --max_ifuel 64 --z3rlimit 120"

// Rule 1, transitivity step.
let _ = assert_norm
  (mem_triple
    ({ s = S_IRI iri_Student; p = rdfs_subClassOf; o = T_IRI iri_Agent })
    smoke_saturated)

// Rule 2, type propagation (alice in Person via Student).
let _ = assert_norm
  (mem_triple
    ({ s = S_IRI iri_alice; p = rdf_type; o = T_IRI iri_Person })
    smoke_saturated)

// Rule 2 + rule 1 together: alice ends up in Agent.
let _ = assert_norm
  (mem_triple
    ({ s = S_IRI iri_alice; p = rdf_type; o = T_IRI iri_Agent })
    smoke_saturated)

#pop-options
