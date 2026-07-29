module OWL.Semantics

// Model-theoretic semantics for RDF graphs, targeting the OWL 2
// RDF-Based Semantics (W3C Rec 2012-12-11) restricted to the semantic
// conditions the shipping OWL 2 RL closure rules (OWL.Closure.fsti /
// RDFS.Closure.fsti) need for their soundness proofs. This module is a
// PROOF-LAYER module: it defines interpretations, denotation,
// satisfaction, entailment, and the pilot slice of semantic
// conditions. It computes nothing at runtime; the soundness theorems
// live in OWL.Semantics.Soundness.fst.
//
// Design doc: docs/designissues/2026-07-29-rdf-based-semantics-
// formalization.md. Read that first — it records the formalization
// SHAPE decisions (why IEXT is a ternary prop over an arbitrary
// domain type, why bnode satisfaction is an existential over total
// assignments, why every semantic condition below is stated in the
// weakest form the W3C tables imply) and the citations into Hayes'
// RDF Semantics and the OWL 2 RDF-Based Semantics tables.
//
// The simplifications relative to the full W3C interpretation
// structure are all in the SOUND direction: this module's class of
// interpretations is a SUPERSET of the OWL 2 RDF-Based
// interpretations (we drop conditions — e.g. IP membership guards,
// datatype map conformance, the only-if halves of iff conditions —
// and we totalize partial maps). A rule proven sound against every
// interpretation here is therefore sound against every genuine OWL 2
// RDF-Based interpretation. The converse (completeness) is out of
// scope and would need the missing conditions.

open FStar.List.Tot
open RDF.Term
open RDF.Triple
open RDF.Graph
open RDF.Indexed
open RDFS.Closure
open OWL.Closure

// ===================================================================
// Interpretations — Hayes, RDF 1.1 Semantics section 5 ("simple
// interpretations"), merged with the OWL 2 RDF-Based Semantics
// interpretation structure (section 4: IR, IP, IEXT, ICEXT).
// ===================================================================

// A simple interpretation over a vocabulary, folded into one record:
//
//   idom      the domain of discourse IR (a nonempty set of
//             "resources"). Represented as an arbitrary F* type
//             carrying at least one inhabitant (idom_wit). Infinite
//             domains — and datatype value spaces embedded in IR —
//             enter for free: any F* type may serve, and nothing
//             below ever needs to decide or enumerate membership.
//   i_iri     IS: IRI -> IR. Total, as in Hayes section 5.
//   i_lit     IL: literal -> IR. Total over well-formed literals.
//             The W3C structure sends ill-typed literals to
//             arbitrary resources anyway (RDF 1.1 Semantics section
//             7), so totalizing loses no generality for soundness.
//   i_tt      denotation constructor for RDF 1.2 triple terms, taking
//             the denotations of the three components. The pilot
//             rules never inspect triple terms; making their
//             denotation an uninterpreted function of the component
//             denotations keeps denot_term total and compositional.
//   iext      IEXT as a curried ternary relation:
//             iext p x y  means  <x,y> `elem` IEXT(p).
//             The W3C structure types IEXT : IP -> P(IR x IR); we
//             totalize it over all of IR (equivalently: we drop the
//             "p `elem` IP" side conditions). Dropping a condition
//             ENLARGES the interpretation class, which only
//             strengthens soundness results (see module banner).
//
// prop (not bool) throughout: satisfaction over an infinite domain is
// definable but not decidable, and never needs to be decided — the
// theorems quantify over it.
noeq type interp = {
  idom     : Type0;
  idom_wit : idom;
  i_iri    : wf_iri -> idom;
  i_lit    : wf_literal -> idom;
  i_tt     : idom -> idom -> idom -> idom;
  iext     : idom -> idom -> idom -> prop;
}

// A blank-node assignment ("mapping A" in Hayes section 5.2): a total
// function from bnode labels to domain elements. Totality is another
// enlarging simplification — every partial assignment extends to a
// total one using idom_wit, so the existential below is unchanged.
let bnode_assignment (d : Type0) = bnode_id -> d

// ===================================================================
// Denotation — [I+A] in Hayes section 5.2.
// ===================================================================

let denot_subject (i : interp) (a : bnode_assignment i.idom) (s : subject) : i.idom =
  match s with
  | S_IRI x   -> i.i_iri x
  | S_BNode b -> a b

let rec denot_term (i : interp) (a : bnode_assignment i.idom) (t : rdf_term)
  : Tot i.idom (decreases t) =
  match t with
  | T_IRI x            -> i.i_iri x
  | T_BNode b          -> a b
  | T_Literal l        -> i.i_lit l
  | T_TripleTerm s p o -> i.i_tt (denot_subject i a s) (i.i_iri p) (denot_term i a o)

// A subject seen through term_to_subject / subject_to_term denotes
// the same resource in both roles. (Mechanical; used constantly by
// the soundness proofs because the closure rules round-trip objects
// into subjects via term_to_subject.)
let lemma_denot_subject_to_term (i : interp) (a : bnode_assignment i.idom) (s : subject)
  : Lemma (denot_term i a (subject_to_term s) == denot_subject i a s) = ()

let lemma_denot_term_to_subject (i : interp) (a : bnode_assignment i.idom)
    (t : rdf_term) (s : subject)
  : Lemma (requires term_to_subject t == Some s)
          (ensures  denot_subject i a s == denot_term i a t) = ()

// ===================================================================
// Satisfaction and entailment — Hayes section 5.2 (truth of triples
// and graphs), with the existential bnode semantics on both sides.
// ===================================================================

// Truth of one triple under a fixed assignment: the pair of the
// subject's and object's denotations is in IEXT of the predicate's
// denotation.
let triple_holds (i : interp) (a : bnode_assignment i.idom) (t : triple) : prop =
  i.iext (i.i_iri t.p) (denot_subject i a t.s) (denot_term i a t.o)

// Truth of a whole graph under a FIXED assignment. The soundness
// proofs work at this level: the closure rules never mint fresh
// blank nodes (in the pilot slice), so one assignment serves the
// input and the output graph alike.
let holds_all (i : interp) (a : bnode_assignment i.idom) (g : rdf_graph) : prop =
  forall (t : triple). List.Tot.memP t g ==> triple_holds i a t

// Graph satisfaction: some assignment of the blank nodes makes every
// triple true (Hayes section 5.2: "I(G) = true if [I+A](G) = true for
// some mapping A").
let satisfies (i : interp) (g : rdf_graph) : prop =
  exists (a : bnode_assignment i.idom). holds_all i a g

// Entailment relative to a class of interpretations (a set of
// semantic conditions): every interpretation in the class satisfying
// g1 satisfies g2. Instantiated below with the pilot condition
// bundle; the framework deliberately keeps the class a parameter so
// later waves can grow the bundle without restating theorems.
let entails_under (conds : interp -> prop) (g1 g2 : rdf_graph) : prop =
  forall (i : interp). conds i ==> satisfies i g1 ==> satisfies i g2

// ===================================================================
// Class extension — ICEXT, OWL 2 RDF-Based Semantics section 4.2:
// ICEXT(c) = { x | <x,c> `elem` IEXT(I(rdf:type)) }.
// ===================================================================

let icext (i : interp) (x c : i.idom) : prop =
  i.iext (i.i_iri rdf_type) x c

// ===================================================================
// Semantic sequences — the denotation-level image of rdf:List
// structure. OWL 2 RDF-Based Semantics section 3 defines "s is a
// sequence of a1 ... an over IR" as: there are l1 ... ln in IR with
// l1 = s, <lk, ak> in IEXT(I(rdf:first)), <lk, l(k+1)> in
// IEXT(I(rdf:rest)), and l(n+1) = I(rdf:nil). seq_is transcribes
// that definition with the element list as the induction handle.
// ===================================================================

let rec seq_is (i : interp) (l : i.idom) (elems : list i.idom)
  : Tot prop (decreases elems) =
  match elems with
  | [] -> l == i.i_iri rdf_nil_iri
  | x :: rest ->
    exists (l' : i.idom).
      i.iext (i.i_iri rdf_first) l x /\
      i.iext (i.i_iri rdf_rest) l l' /\
      seq_is i l' rest

// ===================================================================
// The pilot semantic conditions — SUFFICIENT per-rule semantic
// conditions. (Terminology per the 2026-07-29 external review: the
// earlier "weakest" claimed a minimality nobody established. These
// are readings the cited W3C table rows imply — only-if halves and
// IP/IC membership side conditions dropped — that SUFFICE for the
// rule soundness proofs; that every faithful W3C row implies its
// cond_* here is machine-checked by
// OWL.Semantics.W3C.lemma_embed_conditions.)
//
// SEMANTIC BASELINE (phase-2 addendum): the normative target is the
// OWL 2 RDF-Based Semantics (W3C Rec 2012-12-11), which is defined
// over the 2004 RDF Semantics — NOT RDF 1.1 (2014) and NOT RDF 1.2.
// The table rows cited below are identical in wording across the
// 2004-based and 1.1 presentations for the vocabulary used here; the
// per-deviation baseline audit (which 1.1/1.2-flavored REPRESENTATION
// choices are class-enlarging or neutral for 2004-based
// interpretations) lives in OWL.Semantics.W3C.fst and the design
// doc's delta table. RDF 1.2 constructs (triple terms, directional
// literals) are quarantined off the theorem surface by
// OWL.Semantics.W3C.graph_on_owl2_surface.
//
// Only conditions the four pilot rules need are present; the
// full-program plan adds one small prop per rule family.
// ===================================================================

// rdfs:domain — 2004 RDF Semantics, RDFS semantic conditions (the
// normative basis of the OWL 2 RDF-Based Semantics; the same row
// appears unchanged in RDF 1.1 Semantics section 9 and in OWL 2
// RDF-Based Table 5.8). If <p,c> in IEXT(I(rdfs:domain)) and <x,y>
// in IEXT(p) then x in ICEXT(c).
let cond_domain (i : interp) : prop =
  forall (p c x y : i.idom).
    i.iext (i.i_iri rdfs_domain) p c ==> i.iext p x y ==> icext i x c

// rdfs:range — dual of cond_domain (same table rows): the OBJECT
// falls in the class.
let cond_range (i : interp) : prop =
  forall (p c x y : i.idom).
    i.iext (i.i_iri rdfs_range) p c ==> i.iext p x y ==> icext i y c

// owl:SymmetricProperty — OWL 2 RDF-Based Semantics Table 5.14
// (property characteristics), if-direction: membership in
// ICEXT(I(owl:SymmetricProperty)) makes the extension symmetric.
let cond_symmetric (i : interp) : prop =
  forall (p x y : i.idom).
    icext i p (i.i_iri owl_SymmetricProperty) ==> i.iext p x y ==> i.iext p y x

// owl:sameAs — OWL 2 RDF-Based Semantics Table 5.2 (equality):
// IEXT(I(owl:sameAs)) = { <x,y> | x = y }. Stated as the full iff:
// both directions are exactly what the table asserts, and the
// congruence rules (eq-rep-*) need the forward direction while
// eq-ref needs the backward one.
let cond_sameas_identity (i : interp) : prop =
  forall (x y : i.idom).
    i.iext (i.i_iri owl_sameAs) x y <==> x == y

// owl:oneOf — OWL 2 RDF-Based Semantics Table 5.9 (enumerations):
// if <c,l> in IEXT(I(owl:oneOf)) and l is a sequence of a1 ... an
// over IR, then ICEXT(c) = { a1, ..., an }. The pilot needs only the
// superset half (every listed element is a member); the hypothesis
// keeps the table's shape — the sequence reading is a PREMISE, so
// the condition constrains every sequence reading the interpretation
// gives l, which is what makes the syntactic-list argument in the
// soundness proof go through (see the design doc, "The oneOf
// condition and sequence readings").
let cond_oneof (i : interp) : prop =
  forall (c l : i.idom) (elems : list i.idom).
    i.iext (i.i_iri owl_oneOf_iri) c l ==> seq_is i l elems ==>
    (forall (x : i.idom). List.Tot.memP x elems ==> icext i x c)

// The pilot bundle. Every OWL 2 RDF-Based interpretation (in the
// W3C sense, with any datatype map) satisfies all five conditions,
// so entails_under owl_rl_pilot_conditions is implied by (is weaker
// than) RDF-Based entailment — the safe direction for soundness.
let owl_rl_pilot_conditions (i : interp) : prop =
  cond_domain i /\ cond_range i /\ cond_symmetric i /\
  cond_sameas_identity i /\ cond_oneof i

let pilot_entails (g1 g2 : rdf_graph) : prop =
  entails_under owl_rl_pilot_conditions g1 g2

// ===================================================================
// Index well-formedness — the hypotheses the soundness proofs need
// about the indexed_graph snapshot the rules consult. Split per
// bucket because different rules touch different buckets, and
// because the two clauses have different discharge status against
// build_indexed (see OWL.Semantics.Soundness.fst: the ig_pred clause
// is proven outright; the ig_sp clause's key-decomposition half
// depends on sp_key injectivity — a FINDING, see the design doc).
// ===================================================================

// Every triple the predicate bucket serves up under key k is a real
// triple of the snapshot and really has predicate k.
let ig_wf_pred (ig : indexed_graph) : prop =
  forall (k : string) (t : triple).
    List.Tot.memP t (bucket_lookup ig.ig_pred k) ==>
    List.Tot.memP t ig.ig_triples /\ t.p == k

// Every triple the subject-predicate bucket serves up under the
// composite key sp_key s p is a real triple of the snapshot with
// exactly that subject and predicate.
let ig_wf_sp (ig : indexed_graph) : prop =
  forall (s : subject) (p : wf_iri) (t : triple).
    List.Tot.memP t (bucket_lookup ig.ig_sp (sp_key s p)) ==>
    List.Tot.memP t ig.ig_triples /\ t.s == s /\ t.p == p

// ===================================================================
// Blank-node occurrence and assignment infrastructure (phase-2,
// external-review obligation 2). Decidable occurrence checks, the
// "assignments agreeing on a graph's bnodes give the same truth"
// lemma family, the total-vs-Hayes-graph-local equivalence, the
// fresh-assignment override machinery, and the two reusable theorem
// shapes (no_fresh_bnodes_sound_shape / fresh_bnodes_sound_shape)
// every rule corollary routes through.
// ===================================================================

// Decidable blank-node occurrence. bnode_id is a string, so equality
// is decidable and the walk is a boolean, which lets refinement types
// and Tot assignment constructors branch on it.
let bnode_in_subject (b : bnode_id) (s : subject) : bool =
  match s with
  | S_BNode b' -> b = b'
  | S_IRI _ -> false

let rec bnode_in_term (b : bnode_id) (t : rdf_term) : Tot bool (decreases t) =
  match t with
  | T_BNode b' -> b = b'
  | T_TripleTerm s _ o -> bnode_in_subject b s || bnode_in_term b o
  | _ -> false

let bnode_in_triple (b : bnode_id) (t : triple) : bool =
  bnode_in_subject b t.s || bnode_in_term b t.o

let rec bnode_in_graph (b : bnode_id) (g : rdf_graph) : Tot bool (decreases g) =
  match g with
  | [] -> false
  | t :: tl -> bnode_in_triple b t || bnode_in_graph b tl

// Two assignments agree on every blank node the graph mentions.
// This is the review's "agreement only where needed" relation: fresh
// extensions must preserve exactly these values, nothing more.
let agrees_on_graph_bnodes (#d : Type0) (g : rdf_graph) (a1 a2 : bnode_id -> d) : prop =
  forall (b : bnode_id). bnode_in_graph b g ==> a1 b == a2 b

// Truth depends only on the values an assignment takes at the
// blank nodes that actually occur.
let rec lemma_denot_term_agrees
    (i : interp) (a1 a2 : bnode_assignment i.idom) (t : rdf_term)
  : Lemma
    (requires forall (b : bnode_id). bnode_in_term b t ==> a1 b == a2 b)
    (ensures denot_term i a1 t == denot_term i a2 t)
    (decreases t) =
  match t with
  | T_TripleTerm _ _ o -> lemma_denot_term_agrees i a1 a2 o
  | _ -> ()

let lemma_triple_holds_agrees
    (i : interp) (a1 a2 : bnode_assignment i.idom) (t : triple)
  : Lemma
    (requires forall (b : bnode_id). bnode_in_triple b t ==> a1 b == a2 b)
    (ensures triple_holds i a1 t <==> triple_holds i a2 t) =
  lemma_denot_term_agrees i a1 a2 t.o

// A member triple's bnodes are among its graph's bnodes.
let rec lemma_bnode_in_graph_of_triple (t : triple) (g : rdf_graph) (b : bnode_id)
  : Lemma
    (ensures (List.Tot.memP t g /\ bnode_in_triple b t) ==> bnode_in_graph b g)
    (decreases g) =
  match g with
  | [] -> ()
  | _ :: tl -> lemma_bnode_in_graph_of_triple t tl b

let lemma_holds_all_agrees
    (i : interp) (a1 a2 : bnode_assignment i.idom) (g : rdf_graph)
  : Lemma
    (requires agrees_on_graph_bnodes g a1 a2)
    (ensures holds_all i a1 g <==> holds_all i a2 g) =
  introduce forall (t : triple).
      List.Tot.memP t g ==> (triple_holds i a1 t <==> triple_holds i a2 t)
  with introduce List.Tot.memP t g ==> (triple_holds i a1 t <==> triple_holds i a2 t)
  with _ . begin
    introduce forall (b : bnode_id). bnode_in_triple b t ==> a1 b == a2 b
    with introduce bnode_in_triple b t ==> a1 b == a2 b
    with _ . lemma_bnode_in_graph_of_triple t g b;
    lemma_triple_holds_agrees i a1 a2 t
  end

// ===================================================================
// Total assignments vs Hayes graph-local mappings (review obligation
// 2a). Hayes defines satisfaction through a mapping whose domain is
// exactly the graph's blank nodes; this tree uses total assignments.
// The two are equivalent: restriction in one direction, extension by
// the inhabited domain's witness in the other. Machine-checked here.
// ===================================================================

// The type of a Hayes graph-local mapping: defined exactly on the
// blank nodes occurring in g.
let graph_bnode (g : rdf_graph) = b:bnode_id{bnode_in_graph b g}

// Extend a graph-local mapping to a total assignment, sending every
// off-graph identifier to the domain witness (any value works — truth
// over g cannot see those, per lemma_holds_all_agrees).
let extend_local (i : interp) (g : rdf_graph) (al : graph_bnode g -> i.idom)
  : bnode_assignment i.idom =
  fun (b : bnode_id) -> if bnode_in_graph b g then al b else i.idom_wit

// Hayes-form satisfaction: some GRAPH-LOCAL mapping makes g true
// (truth evaluated through its total extension, which agrees with it
// everywhere on g).
let satisfies_hayes (i : interp) (g : rdf_graph) : prop =
  exists (al : graph_bnode g -> i.idom). holds_all i (extend_local i g al) g

// The equivalence, both directions. Left-to-right restricts the total
// witness to g's bnodes; right-to-left is immediate because the
// extension IS total.
let lemma_satisfies_hayes_equiv (i : interp) (g : rdf_graph)
  : Lemma (satisfies i g <==> satisfies_hayes i g) =
  introduce satisfies i g ==> satisfies_hayes i g
  with _ . begin
    eliminate exists (a : bnode_assignment i.idom). holds_all i a g
    returns satisfies_hayes i g
    with _ . begin
      let al : graph_bnode g -> i.idom = fun b -> a b in
      assert (agrees_on_graph_bnodes g a (extend_local i g al));
      lemma_holds_all_agrees i a (extend_local i g al) g;
      assert (holds_all i (extend_local i g al) g)
    end
  end;
  introduce satisfies_hayes i g ==> satisfies i g
  with _ . begin
    eliminate exists (al : graph_bnode g -> i.idom). holds_all i (extend_local i g al) g
    returns satisfies i g
    with _ . assert (holds_all i (extend_local i g al) g)
  end

// ===================================================================
// Fresh-assignment machinery (review obligation 2b). A witness-
// minting rule proves satisfaction of its output by OVERRIDING the
// input assignment at its minted identifiers — one shared override
// for ALL triples the rule emits (never independent local witnesses;
// the review's condition 3). The freshness condition is explicit:
// minted identifiers collide neither with the input graph's bnodes
// (lemma_override_agrees needs exactly that) nor with one another
// (upds_keys_distinct, which lemma_override_at_key needs to read a
// specific witness back).
// ===================================================================

let override_asg (#d : Type0) (a : bnode_id -> d) (upds : list (bnode_id * d))
  : bnode_id -> d =
  fun b -> match List.Tot.assoc b upds with
        | Some v -> v
        | None -> a b

let rec lemma_assoc_not_key (#d : Type0) (b : bnode_id) (upds : list (bnode_id * d))
  : Lemma
    (requires forall (p : bnode_id * d). List.Tot.memP p upds ==> fst p =!= b)
    (ensures List.Tot.assoc b upds == None)
    (decreases upds) =
  match upds with
  | [] -> ()
  | _ :: tl -> lemma_assoc_not_key b tl

// Freshness w.r.t. the input graph gives agreement on the input
// graph's bnodes — the hypothesis fresh_bnodes_sound_shape consumes.
let lemma_override_agrees (#d : Type0)
    (a : bnode_id -> d) (upds : list (bnode_id * d)) (g : rdf_graph)
  : Lemma
    (requires forall (p : bnode_id * d).
                List.Tot.memP p upds ==> not (bnode_in_graph (fst p) g))
    (ensures agrees_on_graph_bnodes g a (override_asg a upds)) =
  introduce forall (b : bnode_id).
      bnode_in_graph b g ==> a b == override_asg a upds b
  with introduce bnode_in_graph b g ==> a b == override_asg a upds b
  with _ . lemma_assoc_not_key b upds

// Pairwise-distinct minted identifiers.
let rec upds_keys_distinct (#d : Type0) (upds : list (bnode_id * d)) : Tot prop =
  match upds with
  | [] -> True
  | (b, _) :: tl ->
    (forall (p : bnode_id * d). List.Tot.memP p tl ==> fst p =!= b) /\
    upds_keys_distinct tl

// Read a minted witness back out of the override: with distinct keys,
// the assignment takes exactly the recorded value at each minted id.
let rec lemma_override_at_key (#d : Type0)
    (a : bnode_id -> d) (upds : list (bnode_id * d)) (b : bnode_id) (v : d)
  : Lemma
    (requires upds_keys_distinct upds /\ List.Tot.memP (b, v) upds)
    (ensures override_asg a upds b == v)
    (decreases upds) =
  match upds with
  | [] -> ()
  | (b', _) :: tl ->
    if b = b'
    then eliminate (b', snd (List.Tot.hd upds)) == (b, v) \/ List.Tot.memP (b, v) tl
         returns squash (override_asg a upds b == v)
         with _ . ()
         and  _ . ()   // memP (b,v) tl contradicts distinctness with b = b'
    else lemma_override_at_key a tl b v

// ===================================================================
// The two reusable theorem shapes (review obligation 2c). Every rule
// corollary derives satisfaction through exactly one of these; the
// stronger no-fresh result stays visibly distinct from the genuinely
// existential fresh-witness case.
// ===================================================================

// No fresh blank nodes: the input's witness assignment is reused
// verbatim.
let no_fresh_bnodes_sound_shape (i : interp) (g g_out : rdf_graph)
  : Lemma
    (requires satisfies i g /\
              (forall (a : bnode_assignment i.idom).
                 holds_all i a g ==> holds_all i a g_out))
    (ensures satisfies i g_out) =
  eliminate exists (a : bnode_assignment i.idom). holds_all i a g
  returns satisfies i g_out
  with _ . assert (holds_all i a g_out)

// Fresh blank nodes: some override of the input's witness — agreeing
// with it on every input bnode — makes the whole output true at once.
let fresh_bnodes_sound_shape (i : interp) (g g_out : rdf_graph)
  : Lemma
    (requires satisfies i g /\
              (forall (a : bnode_assignment i.idom).
                 holds_all i a g ==>
                 (exists (a' : bnode_assignment i.idom).
                    agrees_on_graph_bnodes g a a' /\ holds_all i a' g_out)))
    (ensures satisfies i g_out) =
  eliminate exists (a : bnode_assignment i.idom). holds_all i a g
  returns satisfies i g_out
  with _ . begin
    eliminate exists (a' : bnode_assignment i.idom).
        agrees_on_graph_bnodes g a a' /\ holds_all i a' g_out
    returns satisfies i g_out
    with _ . assert (holds_all i a' g_out)
  end
