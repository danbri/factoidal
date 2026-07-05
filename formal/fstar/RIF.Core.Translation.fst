module RIF.Core.Translation

// Phase 1 of the RIF Core F* engine, per
// docs/designissues/2026-05-07-rif-fstar-investigation.md.
//
// Pure translation from RIF.Core.Syntax to SPARQL11.Algebra:
//
//   rif_atom  -> SPARQL triple_pattern  (a single triple)
//   rif_body  -> SPARQL bgp             (a flat list of triple_patterns)
//   rif_atom  -> SPARQL CONSTRUCT template (one-triple list)
//
// The RIF/RDF/OWL combination spec (W3C, §5) defines the desugaring:
//
//   o[p->v]      ==>  (o, p, v)
//   o # c        ==>  (o, rdf:type, c)
//   sub ## sup   ==>  (sub, rdfs:subClassOf, sup)
//
// Our translation implements that mapping directly. Frame syntax is
// already single-slot at the rif_atom level (RIF.Core.Syntax notes
// that multi-slot frames decompose at parse time into conjoined
// single-slot Frame atoms), so no inner fold is needed here.
//
// Termination: every recursive call goes structurally on the
// rif_body argument, which is a finite tree of finite lists of
// rif_body. F* derives the decreasing measure automatically once we
// give the explicit body argument; we annotate `decreases b` for
// clarity.
//
// Partiality: a few atoms are ill-typed under SPARQL's pattern
// shape — most notably, a literal cannot appear as the subject of
// a triple pattern because pattern_subject excludes literals. We
// surface those as `None` rather than silently dropping them; the
// caller (a future RIF-XML parser, or the test runner) is the
// natural place to report the error.
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries, no assume val (rule #10).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open FStar.List.Tot
open RDF.Graph.Executable
open SPARQL11.Algebra
module Syn = RIF.Core.Syntax

// ------------------------------------------------------------------
// 1. Term-level translation.
//
// A RIF term in subject position becomes a pattern_subject — but
// pattern_subject excludes literals, so a literal-constant here is
// a typing error and we return None. RIF terms in predicate or
// object position become pattern_term, which permits the full
// IRI / BNode / Literal / Var range.
// ------------------------------------------------------------------

let rif_term_to_subject (t : Syn.rif_term)
  : option pattern_subject
  =
  match t with
  | Syn.RIF_Var v ->
    Some (PS_Var v.var_name)
  | Syn.RIF_Const (T_IRI i)   -> Some (PS_IRI i)
  | Syn.RIF_Const (T_BNode b) -> Some (PS_BNode b)
  | Syn.RIF_Const (T_Literal _) -> None
  | Syn.RIF_TermExternal _ _ ->
    // External(...) used as a TERM only ever appears nested inside a
    // rule HEAD atom's arguments or an Equal operand in this project's
    // target corpus — never directly as an ordinary BODY atom's
    // subject fed through translate_atom/eval_bgp (RIF.Core.Eval
    // evaluates it under the current binding before that point).
    // Reaching here means an unevaluated builtin call landed where a
    // BGP pattern subject was expected; fail cleanly rather than
    // fabricate a term.
    None

let rif_term_to_pattern (t : Syn.rif_term)
  : pattern_term
  =
  match t with
  | Syn.RIF_Var v             -> PT_Var v.var_name
  | Syn.RIF_Const (T_IRI i)   -> PT_IRI i
  | Syn.RIF_Const (T_BNode b) -> PT_BNode b
  | Syn.RIF_Const (T_Literal l) -> PT_Literal l
  | Syn.RIF_TermExternal _ _ ->
    // Same rationale as rif_term_to_subject above: an unevaluated
    // builtin call should never reach ordinary-atom BGP translation
    // for this project's target corpus. pattern_term has no "failure"
    // constructor, so fall back to a variable name that can never
    // collide with a real RIF variable (RIF-XML variable names come
    // from <Var> element text, which cannot contain '$').
    PT_Var "$$unevaluated-external$$"

// Pre-defined RIF/RDF combination IRIs. These are aliases for the
// constants already in RDF.Graph.Executable, re-exported here so the
// translation reads cleanly.
let rif_rdf_type : wf_iri      = rdf_type
let rif_rdfs_subclassof : wf_iri = rdfs_subClassOf

// ------------------------------------------------------------------
// 1b. Generic Uniterm (arity != 2) internal encoding.
//
// A binary positional atom p(s,o) already has a direct triple mapping
// (RIF_Triple, s-p-o). Arity 0 (`p()`) and arity 1 (`p(a)`) Uniterms
// have no subject/object pair to draw on, so this project encodes
// them internally (never exposed to any external RDF-semantics check
// — purely a bookkeeping device the fixpoint/ASK machinery uses
// consistently on both the assertion side (RIF.Core.Eval's
// instantiate_atom) and the query side, so round-tripping is sound):
//   p(a)  ==>  (a, p, rif_uniterm_true_marker)
//   p()   ==>  (rif_uniterm_nullary_subject, p, rif_uniterm_true_marker)
// Arity 2 is NOT routed through here (Parser.RIFXML keeps using
// RIF_Triple for it, unchanged); arity >= 3 has no encoding here and
// stays an honest "cannot translate" (None) — no vendored corpus
// fixture needs it.
// ------------------------------------------------------------------

let rif_uniterm_true_marker : rdf_term =
  T_Literal ({ lexical_form = "true"; datatype = xsd_boolean; lang_tag = None })

let rif_uniterm_nullary_subject : wf_iri =
  assert_norm (is_iri "urn:rif-nullary:subject"); "urn:rif-nullary:subject"

// A RIF positional Uniterm p(a) permits a as ANY term, including a
// literal (e.g. Positional_Arguments' `ex:gold("John Doe")`,
// Chaining_strategy_numeric-add_1's conclusion `ex:a(3)`) — unlike
// RIF_Triple/Frame/Member/Sub, which model genuine RDF-in-RIF
// combination shapes where a literal subject really is ill-typed
// (matching SPARQL CONSTRUCT §16.2's silent-drop convention, per
// RIF.Core.Eval.instantiate_atom's own comment) and must stay a hard
// rejection. For the Uniterm encoding's own internal bookkeeping
// only, a literal in the "subject" slot maps to a DETERMINISTIC blank
// node derived from the literal's own (datatype, lang, lexical form)
// — assertion side (RIF.Core.Eval) and query side (translate_atom
// below) both call this SAME function, so a given literal argument
// always round-trips to the same encoding. Never exposed to any
// external RDF-semantics check.
let literal_subject_bnode_label (l : literal) : bnode_id =
  String.concat "" [
    "rif-litsubj:"; l.datatype; ":";
    (match l.lang_tag with Some t -> t | None -> ""); ":";
    l.lexical_form
  ]

let rif_term_to_uniterm_subject (t : Syn.rif_term) : option pattern_subject =
  match t with
  | Syn.RIF_Var v             -> Some (PS_Var v.var_name)
  | Syn.RIF_Const (T_IRI i)   -> Some (PS_IRI i)
  | Syn.RIF_Const (T_BNode b) -> Some (PS_BNode b)
  | Syn.RIF_Const (T_Literal l) -> Some (PS_BNode (literal_subject_bnode_label l))
  | Syn.RIF_TermExternal _ _  -> None

// ------------------------------------------------------------------
// 2. Atom-level translation.
//
// Each atom maps to exactly one triple_pattern. The Member and Sub
// forms substitute a fixed predicate IRI; Frame and Triple use the
// supplied terms as-is. Returns None when the subject term is a
// literal constant (ill-typed in RIF/RDF combination — cannot occur
// in practice because RIF parsers forbid it).
// ------------------------------------------------------------------

let translate_atom (a : Syn.rif_atom) : option triple_pattern =
  match a with
  | Syn.RIF_Triple s p o ->
    // rif_term_to_uniterm_subject (not the strict rif_term_to_subject):
    // Parser.RIFXML routes EVERY 2-argument positional Atom p(a1 a2)
    // through RIF_Triple, whether it represents genuine RDF-in-RIF
    // combination syntax (Frame/Member/Sub cover most of that in
    // practice) or a plain arity-2 Uniterm fact where either argument
    // may legitimately be a literal (Positional_Arguments'
    // `ex:discount("John Doe" 10)`, Factorial_Forward_Chaining's
    // `ex:factorial(6 720)`) — same literal-as-subject bookkeeping
    // RIF_Uniterm's arity-1 case below needs, for the same reason.
    (match rif_term_to_uniterm_subject s with
     | None -> None
     | Some ps ->
       Some ({ tp_s = ps;
               tp_p = rif_term_to_pattern p;
               tp_o = rif_term_to_pattern o; }))
  | Syn.RIF_Frame o p v ->
    (match rif_term_to_subject o with
     | None -> None
     | Some ps ->
       Some ({ tp_s = ps;
               tp_p = rif_term_to_pattern p;
               tp_o = rif_term_to_pattern v; }))
  | Syn.RIF_Member o c ->
    (match rif_term_to_subject o with
     | None -> None
     | Some ps ->
       Some ({ tp_s = ps;
               tp_p = PT_IRI rif_rdf_type;
               tp_o = rif_term_to_pattern c; }))
  | Syn.RIF_Sub sub sup_ ->
    (match rif_term_to_subject sub with
     | None -> None
     | Some ps ->
       Some ({ tp_s = ps;
               tp_p = PT_IRI rif_rdfs_subclassof;
               tp_o = rif_term_to_pattern sup_; }))
  | Syn.RIF_Uniterm pred args ->
    (match pred, args with
     | Syn.RIF_Const (T_IRI pi), [] ->
       Some ({ tp_s = PS_IRI rif_uniterm_nullary_subject;
               tp_p = PT_IRI pi;
               tp_o = rif_term_to_pattern (Syn.RIF_Const rif_uniterm_true_marker); })
     | Syn.RIF_Const (T_IRI pi), [a] ->
       // The argument goes in OBJECT position (using the SAME fixed
       // subject arity-0 uses), not subject — critical when this atom
       // is used in a rule BODY with a as a variable that must bind
       // to its genuine value (Chaining_strategy_numeric-add_1's
       // `ex:a(?x)`: ?x must bind to the real integer, not an opaque
       // marker). Object position has no literal restriction, so this
       // also handles a literal argument (facts like `ex:gold("John
       // Doe")`) directly with no bnode encoding needed at all.
       Some ({ tp_s = PS_IRI rif_uniterm_nullary_subject;
               tp_p = PT_IRI pi;
               tp_o = rif_term_to_pattern a; })
     | _, _ ->
       // Predicate position is not a plain IRI constant (e.g. a
       // rif:local-scoped constant, which cannot be an RDF triple
       // predicate) or the arity is unsupported (>= 2, already routed
       // through RIF_Triple by the parser, or >= 3) — honest failure,
       // not a silent triple.
       None)

// ------------------------------------------------------------------
// 3. Body translation.
//
// A RIF body conjoins atoms; the SPARQL counterpart is a flat BGP
// (a list of triple_patterns). Atomic atoms produce a singleton
// list; And folds the children's BGPs into one. Failure inside a
// child propagates as None — the whole body is rejected.
//
// `translate_body_list` is the eta-expanded mutual recursion on the
// list-of-bodies branch of And, kept separate so the structural
// decreases is straightforward.
// ------------------------------------------------------------------

let rec translate_body (b : Syn.rif_body)
  : Tot (option bgp) (decreases b)
  =
  match b with
  | Syn.RIF_BodyAtom a ->
    (match translate_atom a with
     | None -> None
     | Some tp -> Some [tp])
  | Syn.RIF_BodyAnd bs ->
    translate_body_list bs
  | Syn.RIF_BodyExternal _ _ ->
    // Not translatable to a single triple_pattern (a builtin
    // predicate call, not an RDF join) — unchanged rejection; callers
    // that need External/Equal support use split_body (below) instead.
    None
  | Syn.RIF_BodyEqual _ _ ->
    None

and translate_body_list (bs : list Syn.rif_body)
  : Tot (option bgp) (decreases bs)
  =
  match bs with
  | [] -> Some []
  | b :: rest ->
    (match translate_body b with
     | None -> None
     | Some bgp_b ->
       (match translate_body_list rest with
        | None -> None
        | Some bgp_rest -> Some (List.Tot.append bgp_b bgp_rest)))

// ------------------------------------------------------------------
// 3b. Body splitting: ordinary atoms vs. External/Equal conditions.
//
// RIF_BodyExternal / RIF_BodyEqual conjuncts have no SPARQL
// triple_pattern encoding (they are builtin predicate calls / value
// equalities, not RDF joins), so translate_body above still rejects
// any body that contains them — exactly the existing, unchanged
// behaviour for every currently-passing fixture. RIF.Core.Eval needs
// a body-evaluation path that instead SEPARATES the two: the ordinary
// atoms (Triple/Frame/Member/Sub/Uniterm) still drive a SPARQL BGP
// join via eval_bgp; the extras are evaluated per-binding afterwards
// (RIF.Core.Eval.apply_extra_condition), since a builtin predicate's
// arguments frequently reference variables the ordinary atoms bind
// (e.g. Factorial_Forward_Chaining's `ex:factorial(?N1 ?F1)` binding
// ?N1 before `?N = External(func:numeric-add(?N1 1))` computes ?N).
//
// split_body / split_body_list flatten the (And-nested) body tree
// into (ordinary_atoms, extra_conditions), preserving each list's
// original left-to-right order — RIF.Core.Eval processes extras
// sequentially in this order, which is sufficient for every target
// corpus fixture (each is authored so a variable is computed before
// it is used downstream; this project does not attempt general
// dependency-order solving for extras, only order-preserving
// left-to-right evaluation).
// ------------------------------------------------------------------

noeq type rif_extra_condition =
  | EC_External : wf_iri -> list Syn.rif_term -> rif_extra_condition
  | EC_Equal    : Syn.rif_term -> Syn.rif_term -> rif_extra_condition

let rec split_body (b : Syn.rif_body)
  : Tot (list Syn.rif_atom & list rif_extra_condition) (decreases b)
  =
  match b with
  | Syn.RIF_BodyAtom a -> ([a], [])
  | Syn.RIF_BodyAnd bs -> split_body_list bs
  | Syn.RIF_BodyExternal op args -> ([], [EC_External op args])
  | Syn.RIF_BodyEqual lhs rhs -> ([], [EC_Equal lhs rhs])

and split_body_list (bs : list Syn.rif_body)
  : Tot (list Syn.rif_atom & list rif_extra_condition) (decreases bs)
  =
  match bs with
  | [] -> ([], [])
  | b :: rest ->
    let (a1, e1) = split_body b in
    let (a2, e2) = split_body_list rest in
    (List.Tot.append a1 a2, List.Tot.append e1 e2)

// Translates ONLY a flat list of ordinary atoms (the first component
// split_body/split_body_list produces) to a BGP — same all-or-nothing
// failure propagation as translate_body_list, just without the And
// tree-walking (the tree shape was already flattened by split_body).
let rec translate_atoms_bgp (atoms : list Syn.rif_atom)
  : Tot (option bgp) (decreases atoms)
  =
  match atoms with
  | [] -> Some []
  | a :: rest ->
    (match translate_atom a with
     | None -> None
     | Some tp ->
       (match translate_atoms_bgp rest with
        | None -> None
        | Some tps -> Some (tp :: tps)))

// ------------------------------------------------------------------
// 4. Head translation.
//
// A RIF Core rule head is a single atom, which becomes a
// CONSTRUCT-template list of one triple_pattern. We expose this as
// its own helper because the deferred Eval module uses it directly
// (a CONSTRUCT-and-merge step per rule).
// ------------------------------------------------------------------

let translate_head (a : Syn.rif_atom) : option (list triple_pattern) =
  match translate_atom a with
  | None    -> None
  | Some tp -> Some [tp]

// ------------------------------------------------------------------
// 5. Rule translation.
//
// A RIF Core rule
//   Forall ?x... (head :- body)
// becomes the pair
//   (CONSTRUCT-template, body-BGP)
// suitable for handing to a SPARQL CONSTRUCT-style evaluator: the
// body BGP supplies bindings, the head template instantiates the
// inferred triple. The fixpoint loop that repeatedly evaluates this
// pair is the subject of the next PR (RIF.Core.Eval).
//
// Rejects rules whose head or body is structurally ill-typed as
// outlined above; returns the pair when both parts succeed.
// ------------------------------------------------------------------

let translate_rule (r : Syn.rif_rule)
  : option (list triple_pattern * bgp)
  =
  match translate_head r.head with
  | None -> None
  | Some hd_tpl ->
    (match translate_body r.body with
     | None -> None
     | Some body_bgp -> Some (hd_tpl, body_bgp))

// ------------------------------------------------------------------
// 6. Program translation.
//
// Translates each rule independently. Failures in one rule do not
// cascade — they are dropped from the result and reported by index
// in `translate_program_diag`. The plain `translate_program` keeps
// only the rules that translated cleanly, which is the right
// behaviour for the W3C tests where a parse-time error has already
// been raised before this module sees the program.
// ------------------------------------------------------------------

let translate_program (p : Syn.rif_program)
  : list (list triple_pattern * bgp)
  =
  let opt_pairs : list (option (list triple_pattern * bgp)) =
    List.Tot.map translate_rule p.rules in
  let rec keep_some
    (xs : list (option (list triple_pattern * bgp)))
    : Tot (list (list triple_pattern * bgp)) (decreases xs)
    =
    match xs with
    | [] -> []
    | None :: rest      -> keep_some rest
    | Some pr :: rest   -> pr :: keep_some rest
  in
  keep_some opt_pairs

// Diagnostic variant: returns the list of 0-based indices of rules
// that failed to translate alongside the successful pairs. Useful
// for the test runner to surface "rule N is malformed" rather than
// silently dropping it.
let translate_program_diag (p : Syn.rif_program)
  : list (list triple_pattern * bgp) * list nat
  =
  let rec aux
    (rs : list Syn.rif_rule)
    (idx : nat)
    (acc_ok : list (list triple_pattern * bgp))
    (acc_err : list nat)
    : Tot (list (list triple_pattern * bgp) * list nat) (decreases rs)
    =
    match rs with
    | [] -> (List.Tot.rev acc_ok, List.Tot.rev acc_err)
    | r :: rest ->
      (match translate_rule r with
       | Some pr -> aux rest (idx + 1) (pr :: acc_ok) acc_err
       | None    -> aux rest (idx + 1) acc_ok (idx :: acc_err))
  in
  aux p.rules 0 [] []
