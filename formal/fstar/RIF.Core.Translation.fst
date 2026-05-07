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

let rif_term_to_pattern (t : Syn.rif_term)
  : pattern_term
  =
  match t with
  | Syn.RIF_Var v             -> PT_Var v.var_name
  | Syn.RIF_Const (T_IRI i)   -> PT_IRI i
  | Syn.RIF_Const (T_BNode b) -> PT_BNode b
  | Syn.RIF_Const (T_Literal l) -> PT_Literal l

// Pre-defined RIF/RDF combination IRIs. These are aliases for the
// constants already in RDF.Graph.Executable, re-exported here so the
// translation reads cleanly.
let rif_rdf_type : wf_iri      = rdf_type
let rif_rdfs_subclassof : wf_iri = rdfs_subClassOf

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
    (match rif_term_to_subject s with
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
