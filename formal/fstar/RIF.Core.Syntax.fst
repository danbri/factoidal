module RIF.Core.Syntax

// Phase 1 of the RIF Core F* engine, per
// docs/designissues/2026-05-07-rif-fstar-investigation.md.
//
// This module defines the abstract syntax of RIF Core programs as
// a pure ADT layered above RDF.Graph.Executable. No evaluation, no
// translation — just the data model. The companion module
// RIF.Core.Translation lifts these ADTs into SPARQL11.Algebra
// triple-pattern / BGP shapes.
//
// Surface coverage:
//   - Atoms:      Triple, Frame (single slot), Member (#), Subclass (##).
//   - Bodies:     single atom, or conjunction of bodies (And).
//   - Rules:      one head atom + a body, optional name.
//   - Programs:   a list of rules.
//
// The 4 skipped W3C SPARQL `entailment` tests we target:
//   1. RIF Logical Entailment (referencing RIF XML).
//   2. RIF Core WG tests: Frames               -- exercises Frame.
//   3. RIF Core WG tests: Modeling Brain Anatomy -- exercises Member + Sub.
//   4. RIF Core WG tests: RDF Combination Blank Node.
//
// Multi-slot frames `o[p1->v1; p2->v2]` decompose at parse time into
// several single-slot Frame atoms conjoined under RIF_BodyAnd, per
// W3C RIF/RDF/OWL §5. Keeping the Frame constructor single-slot keeps
// the ADT minimal and the Translation step total without an inner
// fold.
//
// Out of scope for this Phase 1 module (deferred to Phase 2+):
//   - Built-in atoms (pred:numeric-equal, pred:numeric-less-than, ...).
//   - Existential quantification in body.
//   - Forward-chaining fixpoint (RIF.Core.Eval.fst).
//   - RIF-XML concrete syntax parser (Parser.RIFXML.fst).
//   - W3C test runner shim (RIF.Core.Tests.fst).
//
// IRON RULES:
//   - F* is the source of truth (rule #1).
//   - No --lax, no --admit_smt_queries, no assume val (rule #10, rule #3).
//   - No "(*" or "*)" inside block comments (rule #12); use //.

open RDF.Graph.Executable

// ------------------------------------------------------------------
// 1. Variables and terms.
//
// RIF Core variables are written `?x` in the presentation syntax; the
// parser strips the `?` and stores the bare name. Constants are RDF
// terms (IRIs, blank nodes, literals) drawn directly from
// RDF.Graph.Executable. We do not model RIF function-symbol terms
// because RIF Core forbids non-equality function symbols.
// ------------------------------------------------------------------

noeq type rif_var = {
  var_name : string;
}

// RIF_TermExternal models External(...) used in TERM (function) position,
// e.g. `External(func:numeric-add(?x 1))` nested as an argument of an
// ordinary atom's head — RIF-DTB builtin FUNCTIONS, not predicates. `op`
// is the builtin's IRI (e.g. the rif-builtin-function#... constant); the
// args are evaluated bottom-up against a solution_mapping by
// RIF.Core.Eval, which delegates the actual computation to
// RIF.Core.Builtins. Kept in the same recursive rif_term type (rather
// than a separate ADT) so ordinary term positions (atom arguments, Equal
// operands) can hold either a plain constant/variable or a builtin call
// uniformly.
noeq type rif_term =
  | RIF_Var          : rif_var -> rif_term
  | RIF_Const        : rdf_term -> rif_term
  | RIF_TermExternal : wf_iri -> list rif_term -> rif_term

// ------------------------------------------------------------------
// 2. Atomic formulas.
//
// Each constructor maps to a single RDF triple under the W3C
// RIF/RDF/OWL combination spec, which is the form the SPARQL
// evaluator can consume directly.
//
//   RIF_Triple s p o      -> (s, p, o)
//   RIF_Frame  o p v      -> (o, p, v)              // single slot
//   RIF_Member o c        -> (o, rdf:type, c)
//   RIF_Sub    sub sup    -> (sub, rdfs:subClassOf, sup)
//
// Built-in atoms (RIF_Builtin) are deferred to a follow-up PR; they
// require the SPARQL expression / FILTER lowering described in the
// design doc's "SPARQL stack reuse map" table.
// ------------------------------------------------------------------

// RIF_Uniterm covers the generic positional atom p(a1 ... an) for any
// arity OTHER than 2 (arity-2 Uniterms already have a direct triple
// encoding via RIF_Triple, parsed that way by Parser.RIFXML for
// backward compatibility with every already-passing fixture). Only
// arity 0 and arity 1 are given a translation (RIF.Core.Translation);
// see the corpus fixtures Positional_Arguments (arity 1: `ex:gold(?C)`)
// and the Builtins_* battery (arity 0: `ex:ok()`) for the two shapes
// this project's vendored W3C RIF Core corpus actually exercises.
noeq type rif_atom =
  | RIF_Triple  : rif_term -> rif_term -> rif_term -> rif_atom
  | RIF_Frame   : rif_term -> rif_term -> rif_term -> rif_atom
  | RIF_Member  : rif_term -> rif_term -> rif_atom
  | RIF_Sub     : rif_term -> rif_term -> rif_atom
  | RIF_Uniterm : rif_term -> list rif_term -> rif_atom

// ------------------------------------------------------------------
// 3. Rule body.
//
// RIF Core admits conjunction in bodies; a single atom is the
// degenerate case. The And constructor takes a list of rif_body so
// that the recursion is finite-depth and every well-formed program
// has a Tot-decreasing structural measure (the body is a finite
// tree of finite lists).
// ------------------------------------------------------------------

// RIF_BodyExternal models External(...) used in FORMULA (predicate)
// position, i.e. as a standalone body conjunct — RIF-DTB builtin
// PREDICATES (e.g. `External(pred:numeric-greater-than(?x 0))`). op is
// the builtin's IRI; RIF.Core.Eval evaluates the args against the
// current binding and keeps/drops the binding per the boolean result
// (a FILTER, not a BGP join).
//
// RIF_BodyEqual models `lhs = rhs` as a body conjunct. When lhs is an
// as-yet-unbound variable, this acts as a BIND (the RIF Core corpus
// exercises this shape heavily for builtin-function chaining, e.g.
// Factorial_Forward_Chaining's `?N = External(func:numeric-add(?N1 1))`);
// when lhs is already bound, it is a plain equality filter.
noeq type rif_body =
  | RIF_BodyAtom     : rif_atom -> rif_body
  | RIF_BodyAnd      : list rif_body -> rif_body
  | RIF_BodyExternal : wf_iri -> list rif_term -> rif_body
  | RIF_BodyEqual    : rif_term -> rif_term -> rif_body

// ------------------------------------------------------------------
// 4. Rule.
//
// Per RIF Core, a rule has the form
//   Forall ?x1 ... ?xn (head :- body)
// where the head is a single atom (Core forbids head disjunction
// and head function symbols). A rule may carry an optional name
// from the RIF-XML <id> attribute for diagnostics.
//
// The universally quantified variables are NOT stored explicitly;
// they are exactly the variables that appear free in the rule. This
// matches the SPARQL convention where BGP variables are implicitly
// existentially quantified at the WHERE level. Reconstructing the
// quantifier list, if needed, is an O(|rule|) walk over rif_atom.
// ------------------------------------------------------------------

noeq type rif_rule = {
  rule_name : option string;
  head      : rif_atom;
  body      : rif_body;
}

// ------------------------------------------------------------------
// 5. Program.
//
// A RIF Core program is a list of rules. The order is preserved for
// diagnostics but is semantically irrelevant — RIF Core entailment
// is monotonic and the fixpoint does not depend on rule order.
// ------------------------------------------------------------------

noeq type rif_program = {
  rules : list rif_rule;
}

// ------------------------------------------------------------------
// 6. Smart constructors.
//
// Convenience helpers used by the Translation module and (later) by
// the RIF-XML parser. Kept Tot, no SMT lemmas required.
// ------------------------------------------------------------------

let mk_var (n : string) : rif_term =
  RIF_Var ({ var_name = n })

let mk_const (t : rdf_term) : rif_term =
  RIF_Const t

let mk_const_iri (i : wf_iri) : rif_term =
  RIF_Const (T_IRI i)

let mk_atom_triple (s p o : rif_term) : rif_atom =
  RIF_Triple s p o

let mk_atom_frame (o p v : rif_term) : rif_atom =
  RIF_Frame o p v

let mk_atom_member (o c : rif_term) : rif_atom =
  RIF_Member o c

let mk_atom_sub (sub sup_ : rif_term) : rif_atom =
  RIF_Sub sub sup_

let mk_atom_uniterm (p : rif_term) (args : list rif_term) : rif_atom =
  RIF_Uniterm p args

let mk_term_external (op : wf_iri) (args : list rif_term) : rif_term =
  RIF_TermExternal op args

let mk_body_atom (a : rif_atom) : rif_body =
  RIF_BodyAtom a

let mk_body_and (bs : list rif_body) : rif_body =
  RIF_BodyAnd bs

let mk_body_external (op : wf_iri) (args : list rif_term) : rif_body =
  RIF_BodyExternal op args

let mk_body_equal (lhs rhs : rif_term) : rif_body =
  RIF_BodyEqual lhs rhs

let mk_rule (head_ : rif_atom) (body_ : rif_body) : rif_rule =
  { rule_name = None; head = head_; body = body_; }

let mk_named_rule (n : string) (head_ : rif_atom) (body_ : rif_body) : rif_rule =
  { rule_name = Some n; head = head_; body = body_; }

let empty_program : rif_program = { rules = [] }

let program_of_rules (rs : list rif_rule) : rif_program = { rules = rs }

// ------------------------------------------------------------------
// 7. Equality predicates.
//
// Decidable structural equality on terms and atoms, useful for
// fixpoint convergence checks in the (deferred) Eval module and for
// test assertions. Kept fully concrete, no SMT.
// ------------------------------------------------------------------

let rif_var_eq (a b : rif_var) : bool =
  a.var_name = b.var_name

// Mutual recursion across rif_term and list rif_term mirrors the
// translate_body / translate_body_list pattern already established in
// RIF.Core.Translation.fst — `args` is a genuine structural subterm of
// `RIF_TermExternal op args`, so F*'s default subterm ordering accepts
// `decreases a` / `decreases ts` across the two functions unchanged.
let rec rif_term_eq (a b : rif_term) : Tot bool (decreases a) =
  match a, b with
  | RIF_Var v1,   RIF_Var v2   -> rif_var_eq v1 v2
  | RIF_Const c1, RIF_Const c2 -> rdf_term_eq c1 c2
  | RIF_TermExternal op1 args1, RIF_TermExternal op2 args2 ->
    op1 = op2 && rif_term_list_eq args1 args2
  | _, _ -> false

and rif_term_list_eq (a b : list rif_term) : Tot bool (decreases a) =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> rif_term_eq x y && rif_term_list_eq xs ys
  | _, _ -> false

let rif_atom_eq (a b : rif_atom) : bool =
  match a, b with
  | RIF_Triple s1 p1 o1, RIF_Triple s2 p2 o2 ->
    rif_term_eq s1 s2 && rif_term_eq p1 p2 && rif_term_eq o1 o2
  | RIF_Frame o1 p1 v1,  RIF_Frame o2 p2 v2 ->
    rif_term_eq o1 o2 && rif_term_eq p1 p2 && rif_term_eq v1 v2
  | RIF_Member o1 c1,    RIF_Member o2 c2 ->
    rif_term_eq o1 o2 && rif_term_eq c1 c2
  | RIF_Sub sub1 sup1,   RIF_Sub sub2 sup2 ->
    rif_term_eq sub1 sub2 && rif_term_eq sup1 sup2
  | RIF_Uniterm p1 a1,   RIF_Uniterm p2 a2 ->
    rif_term_eq p1 p2 && rif_term_list_eq a1 a2
  | _, _ -> false

// Reflexivity sanity check on rif_term equality. Verifies via a
// case split on the constructor; the RIF_Const case calls the
// matching reflexivity lemma already established in
// RDF.Graph.Executable (lemma_rdf_term_eq_refl); the RIF_TermExternal
// case recurses over its argument list via the companion lemma below
// (same mutual-recursion shape as rif_term_eq / rif_term_list_eq).
let rec rif_term_eq_refl (t : rif_term) :
  Lemma (ensures rif_term_eq t t == true) (decreases t)
  =
  match t with
  | RIF_Var _   -> ()
  | RIF_Const c -> lemma_rdf_term_eq_refl c
  | RIF_TermExternal _ args -> rif_term_list_eq_refl args

and rif_term_list_eq_refl (ts : list rif_term) :
  Lemma (ensures rif_term_list_eq ts ts == true) (decreases ts)
  =
  match ts with
  | [] -> ()
  | x :: xs -> rif_term_eq_refl x; rif_term_list_eq_refl xs
