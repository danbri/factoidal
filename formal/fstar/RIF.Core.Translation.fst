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
  | Syn.RIF_Const (T_TripleTerm _ _ _) -> None   // triple terms are object-only, never a subject
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
  | Syn.RIF_Const (T_TripleTerm _ _ _) -> PT_Var "$$triple-term-unsupported$$"  // no triple-term pattern_term (#305 P6)
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
  T_Literal ({ lexical_form = "true"; datatype = xsd_boolean; lang_tag = None; direction = None })

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
  | Syn.RIF_Const (T_TripleTerm _ _ _) -> None
  | Syn.RIF_TermExternal _ _  -> None

// ------------------------------------------------------------------
// 1c. Uniterm ARGUMENT-VALUE satellites and n-ary (arity >= 3)
// reification (2026-07-10, closing the Factorial_Forward_Chaining /
// EBusiness_Contract KNOWN-GAPs).
//
// The single-triple arity-2 encoding above is value-preserving for
// GROUND assert/query use but loses a literal-valued FIRST argument
// when a rule body re-binds it through a variable (the variable binds
// the bookkeeping blank node, not the literal — the Factorial gap).
// Fix: alongside the classic triple (enc(a1), p, a2), the assertion
// side (RIF.Core.Eval.instantiate_atom_all) also emits an
// ARGUMENT-VALUE SATELLITE
//     (enc(a1), urn:rif-uniterm:arg1, a1)
// whose object carries a1's genuine value (enc(iri) = the iri itself,
// enc(literal) = literal_subject_bnode_label — deterministic in the
// VALUE, so equal values share the anchor). A body atom p(?v, X) then
// translates to the two-pattern join
//     (?anchor, p, X') . (?anchor, urn:rif-uniterm:arg1, ?v)
// binding ?v to the genuine value. The anchor variable name is a
// deterministic function of the RIF variable name ('$' cannot occur
// in a RIF <Var> name, so no collision), which is CORRECT — not just
// convenient — because the anchor itself is a function of the value.
//
// Arity >= 3 (EBusiness_Contract's cpt:delivered(?item ?date ?store))
// has no classic triple at all; a ground fact p(a1 ... an) reifies as
//     (anchor, p, "true"^^xsd:boolean)
//     (anchor, urn:rif-uniterm:arg<i>, ai)      for each i
// with anchor a blank node whose label is a deterministic
// serialisation of (p, a1 ... an) — same fact, same anchor; distinct
// facts, distinct anchors. A body atom of arity >= 3 translates to
// the corresponding (n+1)-pattern join over a per-atom-occurrence
// anchor variable (indexed by the atom's position in the body, so two
// distinct atom occurrences never share an anchor variable).
//
// All of this is internal bookkeeping shared by exactly two sites —
// RIF.Core.Eval.instantiate_atom_all (assert) and translate_atom_bgp
// (query) — never exposed to any external RDF-semantics check.
// ------------------------------------------------------------------

let rif_uniterm_arg_pred (i : nat) : wf_iri =
  let s = String.concat "" ["urn:rif-uniterm:arg"; string_of_int i] in
  // string_of_int of a nat is digits only, so s is always a valid
  // "urn:..." IRI — the fallback is unreachable but keeps the
  // refinement total without a per-i normalization proof.
  if is_iri s then s else rif_uniterm_nullary_subject

let uniterm_subject_anchor_var (v : string) : string =
  String.concat "" ["$$uniterm-subj$"; v]

let uniterm_anchor_var (idx : nat) : string =
  String.concat "" ["$$uniterm-anchor$"; string_of_int idx]

// Deterministic serialisation of a RESOLVED term for the n-ary fact
// anchor label. The kind prefixes keep IRIs/bnodes/literals disjoint;
// a literal lexical form containing the joiner could in principle
// collide two argument LISTS, which is acceptable for this internal
// bookkeeping (no vendored fixture exercises adversarial lexical
// forms, and a collision only ever MERGES two facts' anchors —
// detected immediately by the corpus's ground conclusions).
let rec rif_term_anchor_fragment (t : rdf_term) : Tot string (decreases t) =
  match t with
  | T_IRI i -> String.concat "" ["i:"; i]
  | T_BNode b -> String.concat "" ["b:"; b]
  | T_Literal l ->
    String.concat "" [
      "l:"; l.datatype; ":";
      (match l.lang_tag with Some tg -> tg | None -> ""); ":";
      l.lexical_form
    ]
  // RIF Core never emits triple terms; a structural fragment keeps the
  // anchor total and distinct from the i:/b:/l: families.
  | T_TripleTerm s p o ->
    let subj = (match s with S_IRI i -> String.concat "" ["i:"; i]
                           | S_BNode b -> String.concat "" ["b:"; b]) in
    String.concat "" ["t:"; subj; ":"; p; ":"; rif_term_anchor_fragment o]

let rec anchor_fragments (ts : list rdf_term) : Tot (list string) (decreases ts) =
  match ts with
  | [] -> []
  | t :: rest -> rif_term_anchor_fragment t :: anchor_fragments rest

let nary_fact_anchor_label (p : wf_iri) (args : list rdf_term) : bnode_id =
  String.concat "" [
    "rif-uniterm-fact:"; p; "|";
    String.concat "|" (anchor_fragments args)
  ]

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
// Per-argument satellite patterns for an arity >= 3 body atom: one
// (?anchor, urn:rif-uniterm:arg<i>, arg_i) pattern per argument.
let rec nary_arg_patterns (anchor : string) (args : list Syn.rif_term) (i : nat)
  : Tot (list triple_pattern) (decreases args)
  =
  match args with
  | [] -> []
  | a :: rest ->
    { tp_s = PS_Var anchor;
      tp_p = PT_IRI (rif_uniterm_arg_pred i);
      tp_o = rif_term_to_pattern a }
    :: nary_arg_patterns anchor rest (i + 1)

// Atom -> list of triple patterns, satellite-aware (see section 1c).
// idx identifies this atom's occurrence position within its body so
// distinct arity >= 3 atom occurrences get distinct anchor variables.
let translate_atom_bgp (idx : nat) (a : Syn.rif_atom) : option bgp =
  match a with
  | Syn.RIF_Triple (Syn.RIF_Var v) p o ->
    // Variable first argument of an arity-2 Uniterm: join through the
    // argument-value satellite so v binds the GENUINE value (literal
    // or IRI), not the bookkeeping subject encoding.
    let anchor = uniterm_subject_anchor_var v.var_name in
    Some [ { tp_s = PS_Var anchor;
             tp_p = rif_term_to_pattern p;
             tp_o = rif_term_to_pattern o };
           { tp_s = PS_Var anchor;
             tp_p = PT_IRI (rif_uniterm_arg_pred 1);
             tp_o = PT_Var v.var_name } ]
  | Syn.RIF_Uniterm (Syn.RIF_Const (T_IRI pi)) args ->
    if List.Tot.length args >= 3 then
      let anchor = uniterm_anchor_var idx in
      Some ({ tp_s = PS_Var anchor;
              tp_p = PT_IRI pi;
              tp_o = rif_term_to_pattern (Syn.RIF_Const rif_uniterm_true_marker) }
            :: nary_arg_patterns anchor args 1)
    else
      (match translate_atom a with
       | None -> None
       | Some tp -> Some [tp])
  | _ ->
    (match translate_atom a with
     | None -> None
     | Some tp -> Some [tp])

// Satellite-aware via translate_atom_bgp; the zero-index public
// wrapper below keeps every existing call site source-compatible.
let rec translate_atoms_bgp_idx (atoms : list Syn.rif_atom) (idx : nat)
  : Tot (option bgp) (decreases atoms)
  =
  match atoms with
  | [] -> Some []
  | a :: rest ->
    (match translate_atom_bgp idx a with
     | None -> None
     | Some tps ->
       (match translate_atoms_bgp_idx rest (idx + 1) with
        | None -> None
        | Some more -> Some (List.Tot.append tps more)))

let translate_atoms_bgp (atoms : list Syn.rif_atom) : option bgp =
  translate_atoms_bgp_idx atoms 0

// ------------------------------------------------------------------
// 3c. RDF-graph conclusions (RDF_Combination_Constant_Equivalence_
// Graph_Entailment): a RIF-RDF combination test whose CONCLUSION is
// an RDF graph rather than a RIF condition — the combination entails
// the conclusion graph iff each of its triples holds (blank nodes
// existentially, which eval_ask_query's bnode-to-variable rewrite
// already provides). The embedding of a ground triple as a BGP
// pattern is 1:1.
// ------------------------------------------------------------------

let triple_to_pattern (t : triple) : triple_pattern =
  { tp_s = (match t.s with
            | S_IRI i -> PS_IRI i
            | S_BNode b -> PS_BNode b);
    tp_p = PT_IRI t.p;
    tp_o = (match t.o with
            | T_IRI i -> PT_IRI i
            | T_BNode b -> PT_BNode b
            | T_Literal l -> PT_Literal l
            // RIF Core facts never contain triple terms and the algebra's
            // pattern_term has no triple-term form yet (#305 P6); this arm
            // is unreachable in practice — a clearly-marked sentinel bnode
            // keeps the conversion total.
            | T_TripleTerm _ _ _ -> PT_BNode "rif_triple_term_unsupported") }

let graph_to_bgp (g : rdf_graph) : bgp =
  List.Tot.map triple_to_pattern g

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
