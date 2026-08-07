module RDF.Entailment.Simple.Spec

// ===================================================================
// A DECLARATIVE specification of RDF simple entailment, transcribed
// from the W3C spec text, written to be readable and checkable
// against that text WITHOUT reference to any algorithm.
//
// This module deliberately computes nothing and mentions no function
// from RDF.Entailment.Simple. It is the independent statement against
// which the shipping search is proven sound and complete in
// RDF.Entailment.Simple.Refinement.fst (and related to the model
// theory in RDF.Entailment.Simple.ModelTheory.fst).
//
// -------------------------------------------------------------------
// BASELINE PINNING (issue #318; the pilot's phase-2 obligation)
// -------------------------------------------------------------------
// Primary baseline: RDF 1.1 Semantics, W3C Recommendation
// 25 February 2014 (https://www.w3.org/TR/rdf11-mt/).
//
//   section 4 (Notation and terminology), definition of INSTANCE,
//   quoted verbatim:
//
//     "Suppose that M is a functional mapping from a set of blank
//      nodes to some set of literals, blank nodes and IRIs. Any graph
//      obtained from a graph G by replacing some or all of the blank
//      nodes N in G by M(N) is an instance of G."
//
//   section 5.3 (Properties of simple entailment), the INTERPOLATION
//   LEMMA, quoted verbatim:
//
//     "G simply entails a graph E if and only if a subgraph of G is
//      an instance of E."
//
// Cross-checked against the earlier baseline, Hayes, RDF Semantics,
// W3C Recommendation 10 February 2004 (REC-rdf-mt-20040210), which the
// normative OWL 2 (2012) specifications build on:
//
//   section 0.3, instance: "Suppose that M is a mapping from a set of
//     blank nodes to some set of literals, blank nodes and URI
//     references; then any graph obtained from a graph G by replacing
//     some or all of the blank nodes N in G by M(N) is an instance of
//     G."
//   section 2, interpolation lemma: "S entails a graph E if and only
//     if a subgraph of S is an instance of E."
//
// The two texts agree on the instance/subgraph condition up to the
// rename of "URI reference" to "IRI". Simple entailment really is the
// stable part across baselines; the places the versions DO diverge,
// and which of them touch this module, are listed under "Version
// divergences" below.
//
// The relation defined here is the RIGHT-HAND SIDE of the
// interpolation lemma ("a subgraph of A is an instance of B"). It is
// the standard finite, syntactic characterisation of simple
// entailment, and it is what a search procedure can be compared
// against directly. The MODEL-THEORETIC definition
// ("every interpretation which satisfies A satisfies B", RDF 1.1
// Semantics section 5.2) is stated separately in
// RDF.Entailment.Simple.ModelTheory.fst, and the interpolation lemma
// itself -- the equivalence of the two -- is PROVED there rather than
// assumed. So nothing in this vertical takes the syntactic
// characterisation on faith.
//
// -------------------------------------------------------------------
// Version divergences that touch this module
// -------------------------------------------------------------------
// 1. LANGUAGE TAGS. RDF 1.1 Concepts section 3.3: "Two literals are
//    term-equal (the same RDF literal) if and only if the two lexical
//    forms, the two datatype IRIs, and the two language tags (if any)
//    compare equal, character by character", and "Lexical
//    representations of language tags MAY be converted to lower case.
//    The value space of language tags is always in lower case." So
//    under RDF 1.1 `"x"@en` and `"x"@EN` are DISTINCT literal terms
//    (same value, different term). RDF 2004 Concepts section 6.5
//    instead required the abstract syntax's language identifier to be
//    "normalized to lowercase", so under that baseline `"x"@EN` is
//    not a well-formed abstract-syntax literal at all. Either way,
//    two literal terms match under simple entailment only when they
//    are the SAME term -- which is what `term_inst` below says.
// 2. rdf:XMLLiteral. In RDF 2004 the XMLLiteral value space is a
//    condition on RDF-INTERPRETATIONS (section 3.1), not on simple
//    interpretations; in RDF 1.1 rdf:XMLLiteral is not even a
//    normative built-in datatype (Concepts section 5.3 is marked
//    non-normative). Under NEITHER baseline does simple entailment
//    identify two XMLLiterals with different lexical forms.
// 3. RDF 1.2 TRIPLE TERMS. `T_TripleTerm` is an RDF 1.2 construct with
//    no counterpart in either baseline. It is handled here (the
//    shipping engine handles it, and this spec must be able to talk
//    about the same graphs the engine runs on), but it is
//    QUARANTINED from the model-theoretic surface: the model-theory
//    module's theorems carry a `tt_free` hypothesis. See that
//    module's banner.
//
// -------------------------------------------------------------------
// Why the instance relation is stated RELATIONALLY
// -------------------------------------------------------------------
// The spec text applies a mapping M to a graph to get a graph. Doing
// that literally in F* runs into a typing obstacle that the prose
// glosses over: a triple's subject has type `subject` (IRI or blank
// node -- never a literal), so "replace blank node b by literal L" is
// not a total operation on triples. RDF 1.1 Semantics section 4 is
// explicit that instances may substitute literals for blank nodes,
// and RDF simply has no term for the result when the blank node was
// in subject position.
//
// Rather than make substitution partial (an `option triple`, which
// then infects every statement with a `Some`), the instance relation
// is written as a RELATION between a pattern triple and a ground
// triple. `subj_inst` demands that the substitute for a
// subject-position blank node be a term that IS a subject
// (`subj_as_term gs` ranges exactly over IRI and blank-node terms), so
// the ill-typed cases simply fail to relate, which is the intended
// reading. `instance_subgraph_form` at the bottom of this file states
// the spec text's own shape literally ("there is a subgraph of A which
// is an instance of B"), and the two are proved equivalent in
// RDF.Entailment.Simple.Refinement.fst
// (`lemma_spec_is_instance_subgraph`) -- so the relational form is a
// presentation choice, not a change of meaning.
// ===================================================================

open FStar.List.Tot
open RDF.Term
open RDF.Triple

// -------------------------------------------------------------------
// The mapping M of the spec text: blank node labels to RDF terms.
// Total (every label gets an image); a mapping defined only on the
// blank nodes of B extends to a total one by sending everything else
// to itself, and only the labels occurring in B are ever consulted
// below, so totality is a presentation convenience and not a
// restriction. "some or all of the blank nodes" in the spec text is
// covered because M may send a label to its own blank node
// (`fun l -> T_BNode l` is the identity instance).
// -------------------------------------------------------------------
let bnode_subst = bnode_id -> rdf_term

// A subject seen as a term. (RDF 1.1 Concepts section 3.1: subjects
// are IRIs or blank nodes, so this is injective and its image is
// exactly the subject-eligible terms.)
let subj_term (s : subject) : rdf_term =
  match s with
  | S_IRI i   -> T_IRI i
  | S_BNode b -> T_BNode b

// "gs is the result of replacing the blank nodes of ps by M(-)",
// in subject position.
//   - an IRI subject is not a blank node, so it is unchanged;
//   - a blank node subject b is replaced by M(b), and the result is
//     the subject gs exactly when M(b) is the term form of gs.
let subj_inst (m : bnode_subst) (ps : subject) (gs : subject) : prop =
  match ps with
  | S_IRI i   -> gs == S_IRI i
  | S_BNode b -> m b == subj_term gs

// "g is the result of replacing the blank nodes of pat by M(-)", in
// term (object) position. Structural, one clause per RDF term kind:
//   - a blank node is replaced by its image;
//   - an IRI is not a blank node, so it is unchanged;
//   - a literal is not a blank node, so it is unchanged -- and
//     "unchanged" means the SAME literal term (see divergence notes 1
//     and 2 in the banner: term identity, not any value equality);
//   - a triple term (RDF 1.2) contains blank nodes at every depth,
//     which are ordinary graph-scoped blank nodes, so substitution
//     recurses through it and the predicate IRI is unchanged.
// `decreases pat`: the only recursive call is on the object sub-term.
let rec term_inst (m : bnode_subst) (pat : rdf_term) (g : rdf_term)
  : Tot prop (decreases pat) =
  match pat with
  | T_BNode b   -> m b == g
  | T_IRI i     -> g == T_IRI i
  | T_Literal l -> g == T_Literal l
  | T_TripleTerm ps pp po ->
    exists (gs : subject) (go : rdf_term).
      g == T_TripleTerm gs pp go /\ subj_inst m ps gs /\ term_inst m po go

// "ta is the result of replacing the blank nodes of tb by M(-)":
// predicates are IRIs, hence never blank nodes, hence unchanged.
let triple_inst (m : bnode_subst) (tb ta : triple) : prop =
  tb.p == ta.p /\ subj_inst m tb.s ta.s /\ term_inst m tb.o ta.o

// ===================================================================
// THE SPECIFICATION.
//
// RDF 1.1 Semantics section 5.3 (interpolation lemma): graph A simply
// entails graph B iff A has a SUBGRAPH which is an INSTANCE of B.
//
// Reading RDF graphs as sets of triples (RDF 1.1 Concepts section 3:
// "An RDF graph is a set of RDF triples"), "the instance of B under M
// is a subgraph of A" says exactly: every triple of B, after
// substitution, is a triple of A. That is the form below -- no
// ordering, no multiplicity, no search: one existential over the
// mapping M, then a universal over B's triples.
// ===================================================================
let simple_entailment_spec (a b : list triple) : prop =
  exists (m : bnode_subst).
    forall (tb : triple). memP tb b ==>
      (exists (ta : triple). memP ta a /\ triple_inst m tb ta)

// ===================================================================
// The literal fragment on which the shipping matcher's literal test
// coincides with RDF literal TERM equality.
//
// This is NOT part of the specification; it is the side condition the
// soundness theorem needs, isolated here so the specification above
// stays clean. It exists because the shipping `literal_eq` is
// deliberately coarser than term equality in two places (see the
// banner's divergence notes, and finding SE-1 in the design doc):
//   - it compares language tags case-insensitively;
//   - it compares two rdf:XMLLiteral-typed literals by exclusive
//     canonical XML rather than by lexical form.
// Both are RDF-interpretation (D-entailment) behaviours; neither is
// licensed by SIMPLE entailment.
//
// `lit_exact` names the literals where those two branches cannot
// fire: not XMLLiteral-typed, and language tag already lowercase.
// ===================================================================
let lit_exact (l : literal) : prop =
  l.datatype =!= rdf_XMLLiteral /\
  (match l.lang_tag with
   | None   -> True
   | Some t -> FStar.String.lowercase t == t)

let rec term_exact (t : rdf_term) : Tot prop (decreases t) =
  match t with
  | T_IRI _     -> True
  | T_BNode _   -> True
  | T_Literal l -> lit_exact l
  | T_TripleTerm _ _ o -> term_exact o

let triple_exact (t : triple) : prop = term_exact t.o

let graph_exact (g : list triple) : prop =
  forall (t : triple). memP t g ==> triple_exact t

// ===================================================================
// Triple-term freedom -- the RDF 1.2 quarantine predicate. Used by
// the model-theory module (RDF 1.2 triple terms have no denotation in
// either baseline's model theory), never by the syntactic spec above.
// ===================================================================
let rec term_tt_free (t : rdf_term) : Tot prop (decreases t) =
  match t with
  | T_IRI _     -> True
  | T_BNode _   -> True
  | T_Literal _ -> True
  | T_TripleTerm _ _ _ -> False

let graph_tt_free (g : list triple) : prop =
  forall (t : triple). memP t g ==> term_tt_free t.o

// ===================================================================
// Appendix: the spec text's own shape, stated literally.
//
// "A subgraph of A is an instance of B" names an intermediate graph:
// the instance. `instance_subgraph_form` below spells that out --
// there is a mapping M and a graph G_inst such that G_inst is a
// subgraph of A, and G_inst is the image of B under M (every
// B-triple has its image in G_inst, and every G_inst triple is the
// image of a B-triple).
//
// `simple_entailment_spec` collapses the intermediate graph, which is
// the form a refinement proof can use. The two are proved equivalent
// in RDF.Entailment.Simple.Refinement.fst
// (`lemma_spec_is_instance_subgraph`), so the collapse is checked and
// not assumed. Nothing else in the vertical depends on this appendix;
// it is here so a reader can check the transcription against the
// spec's own wording.
// ===================================================================

let is_subgraph (g h : list triple) : prop =
  forall (t : triple). memP t g ==> memP t h

// "g_inst is an instance of g_pat under M", graph level.
let is_instance_of (m : bnode_subst) (g_inst g_pat : list triple) : prop =
  (forall (tp : triple). memP tp g_pat ==>
     (exists (ti : triple). memP ti g_inst /\ triple_inst m tp ti)) /\
  (forall (ti : triple). memP ti g_inst ==>
     (exists (tp : triple). memP tp g_pat /\ triple_inst m tp ti))

let instance_subgraph_form (a b : list triple) : prop =
  exists (m : bnode_subst) (g_inst : list triple).
    is_subgraph g_inst a /\ is_instance_of m g_inst b
