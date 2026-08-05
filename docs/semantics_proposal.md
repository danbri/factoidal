# Proposal: A Model-Theoretic Verification Layer for Factoidal

> Owner-supplied draft design proposal, saved verbatim 2026-08-05.
> Adoption assessment:
> [`designissues/2026-08-05-semantics-proposal-adoption.md`](designissues/2026-08-05-semantics-proposal-adoption.md)
> — much of this proposal is ALREADY IMPLEMENTED in the tree (the
> 2026-07 entailment verticals + the 2026-08-04/05 proof program);
> the assessment maps each element to its landed theorem or adopts
> it into the queue.

---

Proposal: A Model-Theoretic Verification Layer for Factoidal

Status

Draft design proposal.

Summary

Factoidal already contains a substantial executable implementation of RDF, RDFS, selected OWL 2 RL/RDF rules, SPARQL, concrete syntaxes, storage formats, and related W3C technologies in F*.

Its current verification work primarily establishes properties of the implementation itself:

* datatype and refinement correctness;
* totality and termination;
* preservation of local representation invariants;
* selected algebraic and round-trip lemmas;
* mechanically checked extraction from F*;
* empirical conformance through W3C and open-source test suites.

The proposed work adds an independent model-theoretic specification layer for RDF and RDFS and proves that selected existing Factoidal operations are sound with respect to it.

This is an additive layer. It does not replace the current RDF term representation, parsers, closure rules, indexes, stores, or extracted engines.

The initial target is a small, reviewable semantic kernel supporting:

1. simple RDF interpretations;
2. satisfaction of RDF triples and graphs;
3. simple entailment;
4. RDF interpretations and RDF axiomatic conditions;
5. RDFS interpretations and selected RDFS semantic conditions;
6. soundness of selected existing Factoidal closure rules;
7. soundness of the fixed-point closure composed from those rules.

The design deliberately separates:

* syntax, represented by existing Factoidal RDF datatypes;
* model theory, represented by new non-executable or ghost-oriented F* definitions;
* reference inference, optionally represented by declarative rules;
* optimized execution, represented by existing Factoidal closure functions.

Motivation

Factoidal currently implements RDFS and OWL RL/RDF inference primarily through specialized forward-chaining functions such as:

* rdfs_rule_domain;
* rdfs_rule_range;
* rdfs_rule_subPropertyOf;
* rdfs_rule_subClassOf;
* rdfs_rule_subClassOf_trans;
* rdfs_rule_subPropertyOf_trans;
* the corresponding OWL closure functions.

These functions are executable, indexed, extractable, and tested. However, each function currently acts simultaneously as:

1. the operational interpretation of a W3C rule;
2. the production implementation of that rule.

An implementation function can be internally well typed and still encode the wrong semantic condition. Test suites reduce this risk but do not eliminate it.

The proposed semantic layer introduces an independent meaning for RDF graphs. Existing implementation functions can then be related to that meaning through explicit theorems.

The important target property is not merely:

rdfs_rule_domain returns a well-formed rdf_graph

but:

Every RDFS interpretation satisfying the input graph
also satisfies every triple emitted by rdfs_rule_domain.

Non-goals

The first phase will not attempt to formalize all of RDF 1.2, generalized RDF, datatypes, D-entailment, OWL 2 Direct Semantics, OWL 2 RL completeness, SPARQL entailment regimes, or every axiomatic triple.

The first phase will not replace the existing optimized closure engine with a generic theorem prover.

The first phase will not claim completeness unless a deliberately bounded fragment has been defined and proved complete.

The first phase will not require interpretation structures or satisfaction relations to be extracted into production executables.

Proposed module structure

formal/fstar/
  RDF.Semantics.Core.fsti
  RDF.Semantics.Core.fst
  RDF.Semantics.Simple.fsti
  RDF.Semantics.Simple.fst
  RDF.Semantics.RDF.fsti
  RDF.Semantics.RDF.fst
  RDFS.Semantics.fsti
  RDFS.Semantics.fst
  RDFS.Closure.Soundness.fsti
  RDFS.Closure.Soundness.fst
  RDF.Semantics.Examples.fst
  RDFS.Semantics.Examples.fst

Optional later modules:

  RDF.Rules.Syntax.fsti
  RDF.Rules.Eval.fst
  RDF.Rules.Soundness.fst
  OWL.RL.Semantics.Fragment.fsti
  OWL.RL.Closure.Soundness.fst

The semantic modules should depend on the decomposed RDF core:

RDF.Term
RDF.Triple
RDF.Graph

They should not depend on RDF.Graph.Executable, storage modules, parsers, SPARQL, or OWL closure.

The soundness bridge module may depend on both:

RDFS.Semantics
RDFS.Closure
RDF.Indexed

This preserves a clear dependency direction:

RDF syntax datatypes
       ↓
semantic specification
       ↓
soundness bridge ← existing executable closure

Existing syntax layer

The proposal reuses Factoidal’s existing term and graph types.

Conceptually:

type bnode_id = string
type iri = string
type wf_iri = s:iri{is_iri s}
type subject =
  | S_IRI   : wf_iri -> subject
  | S_BNode : bnode_id -> subject
type rdf_term =
  | T_IRI        : wf_iri -> rdf_term
  | T_BNode      : bnode_id -> rdf_term
  | T_Literal    : wf_literal -> rdf_term
  | T_TripleTerm : subject -> wf_iri -> rdf_term -> rdf_term
type triple = {
  s : subject;
  p : wf_iri;
  o : rdf_term;
}
type rdf_graph = list triple

The semantic layer must not introduce a competing simplified RDF AST in which variables, literals, IRIs, subjects, predicates, and objects are conflated.

Rule variables, when introduced, belong to a separate rule or pattern language.

Semantic universe

A first draft should use a shallow, relational representation rather than attempting to encode every set-theoretic detail of the W3C prose literally.

One possible structure is:

module RDF.Semantics.Core
open RDF.Term
open RDF.Triple
open RDF.Graph
noeq type interpretation = {
  resource : Type0;
  denotes_iri :
    wf_iri -> resource;
  denotes_bnode :
    bnode_id -> resource;
  denotes_literal :
    wf_literal -> resource;
  property_extension :
    resource -> resource -> resource -> prop;
}

Here:

property_extension p s o

means that the denotation p is interpreted as a property whose extension contains the pair (s,o).

A richer structure may later distinguish IR, IP, LV, IEXT, and related sets and mappings more literally. The minimal first representation should nevertheless preserve enough structure to state the semantic conditions faithfully.

Because blank nodes are existentially scoped, denotes_bnode should not ultimately be fixed globally by an interpretation. Satisfaction of a graph should quantify over a graph-local blank-node assignment.

A better final core is therefore:

type bnode_assignment (i:interpretation) =
  bnode_id -> i.resource

IRI and literal interpretation remain part of interpretation, while blank-node interpretation is supplied separately when evaluating a graph.

Term interpretation

val interp_subject :
  i:interpretation ->
  a:bnode_assignment i ->
  subject ->
  i.resource
val interp_term :
  i:interpretation ->
  a:bnode_assignment i ->
  rdf_term ->
  i.resource

For RDF 1.1:

let interp_subject i a s =
  match s with
  | S_IRI iri -> i.denotes_iri iri
  | S_BNode b -> a b
let interp_term i a t =
  match t with
  | T_IRI iri     -> i.denotes_iri iri
  | T_BNode b     -> a b
  | T_Literal lit -> i.denotes_literal lit

RDF 1.2 triple terms should initially be excluded through a fragment predicate, or interpreted in a later dedicated module.

For example:

val rdf11_term : rdf_term -> bool
val rdf11_graph : rdf_graph -> bool

The first semantic theorems may require:

requires (rdf11_graph g)

This is preferable to silently assigning an improvised meaning to RDF 1.2 triple terms.

Triple satisfaction

let satisfies_triple
  (i : interpretation)
  (a : bnode_assignment i)
  (t : triple)
  : prop
=
  i.property_extension
    (i.denotes_iri t.p)
    (interp_subject i a t.s)
    (interp_term i a t.o)

This states the simple RDF condition that the predicate IRI denotes a property whose extension contains the denotations of the subject and object.

Graph satisfaction

Blank nodes in an RDF graph are existential variables.

let satisfies_graph
  (i : interpretation)
  (g : rdf_graph)
  : prop
=
  exists (a : bnode_assignment i).
    forall (t : triple).
      mem_triple t g ==>
      satisfies_triple i a t

A more extraction-friendly or solver-friendly representation may quantify only over the finite set of blank nodes occurring in g.

That refinement creates an early proof obligation:

val graph_bnodes_complete :
  g:rdf_graph ->
  b:bnode_id ->
  Lemma (
    bnode_occurs_in_graph b g
    <==>
    List.Tot.mem b (graph_bnodes g)
  )

This is especially important for RDF 1.2 triple terms, because blank-node collection must recurse into embedded triple terms.

Simple entailment

let simple_entails
  (premise : rdf_graph)
  (conclusion : rdf_graph)
  : prop
=
  forall (i : interpretation).
    satisfies_graph i premise ==>
    satisfies_graph i conclusion

This is the fundamental semantic relation around which later RDF and RDFS entailment can be constructed.

The implementation may also provide single-triple entailment:

let simple_entails_triple
  (g : rdf_graph)
  (t : triple)
  : prop
=
  simple_entails g [t]

RDF interpretations

A new module should add the semantic conditions required for an RDF interpretation.

Sketch:

module RDF.Semantics.RDF
open RDF.Semantics.Core
open RDF.Vocabulary
val is_rdf_interpretation :
  interpretation -> prop

The first version may cover a deliberately small subset:

* rdf:type;
* rdf:Property;
* required RDF axiomatic triples used by the implemented entailment regime;
* semantic treatment of plain and typed literals only where formalized.

RDF entailment then becomes:

let rdf_entails
  (premise : rdf_graph)
  (conclusion : rdf_graph)
  : prop
=
  forall (i : interpretation).
    is_rdf_interpretation i /\
    satisfies_graph i premise
    ==>
    satisfies_graph i conclusion

RDFS interpretations

module RDFS.Semantics
open RDF.Semantics.RDF
open RDFS.Closure
val is_rdfs_interpretation :
  interpretation -> prop

The semantic conditions should initially correspond directly to the closure rules already implemented.

Subproperty condition

Conceptually:

If P rdfs:subPropertyOf Q is true,
then IEXT(P) is a subset of IEXT(Q).

Sketch:

val rdfs_subproperty_condition :
  i:interpretation ->
  prop

Equivalent logical shape:

forall p q.
  i.property_extension
    (i.denotes_iri rdfs_subPropertyOf)
    p
    q
  ==>
  forall x y.
    i.property_extension p x y
    ==>
    i.property_extension q x y

Domain condition

If P rdfs:domain C is true and x P y is true,
then x rdf:type C is true.

Sketch:

forall p c x y.
  i.property_extension
    (i.denotes_iri rdfs_domain)
    p
    c
  /\
  i.property_extension p x y
  ==>
  i.property_extension
    (i.denotes_iri rdf_type)
    x
    c

Range condition

forall p c x y.
  i.property_extension
    (i.denotes_iri rdfs_range)
    p
    c
  /\
  i.property_extension p x y
  ==>
  i.property_extension
    (i.denotes_iri rdf_type)
    y
    c

Subclass condition

forall c d x.
  i.property_extension
    (i.denotes_iri rdfs_subClassOf)
    c
    d
  /\
  i.property_extension
    (i.denotes_iri rdf_type)
    x
    c
  ==>
  i.property_extension
    (i.denotes_iri rdf_type)
    x
    d

Transitivity conditions

The RDFS interpretation should also state the semantic consequences corresponding to transitive rdfs:subClassOf and rdfs:subPropertyOf.

The initial semantic kernel may state these conditions directly, even if a later version models class extensions and property extensions through separate typed sets.

RDFS entailment

let rdfs_entails
  (premise : rdf_graph)
  (conclusion : rdf_graph)
  : prop
=
  forall (i : interpretation).
    is_rdfs_interpretation i /\
    satisfies_graph i premise
    ==>
    satisfies_graph i conclusion

Bridge to the existing closure implementation

The existing functions should remain unchanged initially.

The new bridge module proves each rule sound.

module RDFS.Closure.Soundness
open RDF.Semantics.Core
open RDF.Semantics.RDF
open RDFS.Semantics
open RDFS.Closure

Rule-level soundness theorem

For rdfs_rule_domain:

val rdfs_rule_domain_sound :
  i:interpretation ->
  g:rdf_graph ->
  Lemma
    (requires
      rdf11_graph g /\
      is_rdfs_interpretation i /\
      satisfies_graph i g)
    (ensures
      satisfies_graph i
        (rdfs_rule_domain g (build_indexed g)))

Equivalent entailment-oriented form:

val rdfs_rule_domain_entails :
  g:rdf_graph ->
  Lemma (
    rdfs_entails
      g
      (rdfs_rule_domain g (build_indexed g))
  )

The first form is often easier to prove because it exposes the interpretation and satisfaction witness directly.

Similar theorems should be added for:

rdfs_rule_range_sound
rdfs_rule_subPropertyOf_sound
rdfs_rule_subClassOf_sound
rdfs_rule_subClassOf_trans_sound
rdfs_rule_subPropertyOf_trans_sound

Container membership and reflexivity axioms should be handled separately because they depend on axiomatic or extensional semantic conditions beyond ordinary two-premise closure rules.

Preservation of existing triples

Most Factoidal closure rules are inflationary: they return the original graph plus inferred triples.

This should be proved independently:

val rdfs_rule_domain_inflationary :
  g:rdf_graph ->
  t:triple ->
  Lemma (
    mem_triple t g ==>
    mem_triple t (rdfs_rule_domain g (build_indexed g))
  )

Then satisfaction preservation for existing triples follows immediately from the same blank-node assignment.

For newly emitted triples, the proof uses the corresponding RDFS semantic condition.

This suggests a reusable proof pattern:

For each triple in output:
  Case 1: it was already in input.
          Use input graph satisfaction.
  Case 2: it was generated by the rule.
          Recover matching premise triples.
          Use satisfaction of those premises.
          Apply the relevant RDFS semantic condition.

Index correctness prerequisite

The production functions use indexed_graph lookups. Soundness proofs therefore need either:

1. direct lemmas about every lookup used by the rule; or
2. a general refinement theorem for the index.

Recommended:

val bucket_lookup_sound :
  ig:indexed_graph ->
  p:wf_iri ->
  t:triple ->
  Lemma (
    List.Tot.mem t (bucket_lookup ig.ig_pred p)
    ==>
    mem_triple t ig.ig_graph /\
    t.p = p
  )

and, where required:

val bucket_lookup_complete :
  ig:indexed_graph ->
  p:wf_iri ->
  t:triple ->
  Lemma (
    mem_triple t ig.ig_graph /\
    t.p = p
    ==>
    List.Tot.mem t (bucket_lookup ig.ig_pred p)
  )

The indexed representation should retain or expose its source graph:

type indexed_graph = {
  ig_graph : rdf_graph;
  ...
}

with a construction theorem:

val build_indexed_preserves_graph :
  g:rdf_graph ->
  Lemma ((build_indexed g).ig_graph == g)

If the current type does not retain the source graph, equivalent relational predicates can be introduced:

val index_represents :
  indexed_graph -> rdf_graph -> prop

Rule soundness needs lookup soundness. Equivalence of optimized execution to a simple reference rule additionally needs lookup completeness.

Fixed-point closure soundness

After proving each closure step sound, prove the combined step:

val rdfs_closure_step_sound :
  i:interpretation ->
  g:rdf_graph ->
  Lemma
    (requires
      is_rdfs_interpretation i /\
      satisfies_graph i g)
    (ensures
      satisfies_graph i (rdfs_closure_step g))

Then prove bounded iteration sound by induction on fuel:

val rdfs_closure_fuel_sound :
  fuel:nat ->
  i:interpretation ->
  g:rdf_graph ->
  Lemma
    (requires
      is_rdfs_interpretation i /\
      satisfies_graph i g)
    (ensures
      satisfies_graph i (rdfs_closure_fuel fuel g))

The existing closure implementation may terminate either by:

* detecting graph stability;
* exhausting a fuel bound;
* or both.

Soundness does not require reaching a true fixed point. Every intermediate inflationary application of sound rules is sound.

Completeness does require stronger fixed-point and finite-domain arguments and should be deferred.

Declarative rule layer

A separate declarative rule AST is optional but recommended.

It should not replace Factoidal’s RDF term representation.

type variable = string
type rule_subject =
  | RS_Var   : variable -> rule_subject
  | RS_IRI   : wf_iri -> rule_subject
  | RS_BNode : bnode_id -> rule_subject
type rule_predicate =
  | RP_Var : variable -> rule_predicate
  | RP_IRI : wf_iri -> rule_predicate
type rule_object =
  | RO_Var  : variable -> rule_object
  | RO_Term : rdf_term -> rule_object
type rule_atom = {
  ra_s : rule_subject;
  ra_p : rule_predicate;
  ra_o : rule_object;
}
type positive_rule = {
  rule_name : string;
  body      : list rule_atom;
  head      : list rule_atom;
}

For example, RDFS domain can be represented as:

let rdfs2_rule : positive_rule = {
  rule_name = "rdfs2";
  body = [
    {
      ra_s = RS_Var "p";
      ra_p = RP_IRI rdfs_domain;
      ra_o = RO_Var "c";
    };
    {
      ra_s = RS_Var "x";
      ra_p = RP_Var "p";
      ra_o = RO_Var "y";
    }
  ];
  head = [
    {
      ra_s = RS_Var "x";
      ra_p = RP_IRI rdf_type;
      ra_o = RO_Var "c";
    }
  ];
}

A slow generic evaluator can serve as a reference implementation:

val eval_positive_rule :
  positive_rule ->
  rdf_graph ->
  rdf_graph

Then prove:

val rdfs2_compiled_correct :
  g:rdf_graph ->
  Lemma (
    graph_set_equiv
      (eval_positive_rule rdfs2_rule g)
      (rdfs_rule_domain g (build_indexed g))
  )

This theorem is distinct from model-theoretic soundness:

compiled correctness:
  optimized function = declarative rule evaluator
semantic soundness:
  declarative rule preserves truth in every RDFS interpretation

Together:

optimized Factoidal function
          =
declarative W3C-shaped rule
          ⊨
RDFS semantic consequence

Blank-node handling

Blank nodes require particular care.

Graph satisfaction is existential over blank-node assignments. When a closure rule only reuses existing terms, the same assignment can generally witness satisfaction of the output graph.

Rules that create fresh blank nodes or witnesses require an extended assignment.

The initial RDF/RDFS rules should be divided into:

term-preserving rules
fresh-term-producing rules

The first soundness phase should focus on term-preserving rules.

For term-preserving rules:

terms(output) ⊆ terms(input) ∪ fixed vocabulary

For rules that introduce fixed vocabulary IRIs, interpretation is already provided by denotes_iri.

For rules that synthesize fresh blank nodes, the soundness proof must construct a larger blank-node assignment and show that it agrees with the original assignment on existing blank nodes.

Axiomatic triples

RDF and RDFS entailment include axiomatic triples and infinite families such as container membership properties.

These should not initially be hidden inside the ordinary rule proofs.

Introduce explicit predicates:

val is_rdf_axiomatic_triple :
  triple -> prop
val is_rdfs_axiomatic_triple :
  triple -> prop

and prove:

val rdf_axiomatic_triple_valid :
  i:interpretation ->
  t:triple ->
  Lemma
    (requires
      is_rdf_interpretation i /\
      is_rdf_axiomatic_triple t)
    (ensures
      satisfies_ground_triple i t)

The finite implementation tables can then be related to the semantic predicates:

val finite_rdf_axioms_sound :
  t:triple ->
  Lemma (
    mem_triple t rdf_axiomatic_graph
    ==>
    is_rdf_axiomatic_triple t
  )

Completeness of a finite table with respect to an infinite axiomatic family should not be claimed.

For rdf:_n, introduce a syntactic recognizer rather than enumerating only _1 through _5 in the semantic layer.

Datatypes

Datatype semantics should be staged.

Phase 1:

* treat literal denotation abstractly;
* require only that every well-formed literal denotes a resource;
* exclude datatype entailment and value-space equality theorems.

Phase 2:

* introduce datatype maps;
* distinguish lexical-to-value mappings;
* model ill-typed literals where required;
* connect XSD.Datatypes functions to semantic value equality.

No theorem should infer model-theoretic datatype soundness merely from lexical normalization code.

Proof engineering strategy

The model theory should be optimized for comprehensibility and proof tractability, not extraction performance.

Recommended techniques:

* use prop and ghost definitions freely;
* isolate existential blank-node witnesses;
* prove list-membership lemmas once;
* use rule-specific witness recovery lemmas;
* avoid unfolding the entire indexed graph implementation in semantic proofs;
* expose small .fsti interfaces for index soundness;
* maintain one theorem per W3C rule identifier;
* attach specification citations in comments;
* avoid proving completeness before soundness is stable.

Each theorem should record:

W3C rule or semantic condition
Factoidal function
fragment restrictions
assumptions
proof status
tests linked

Initial milestone

The first milestone should cover four rules:

1. rdfs2 — domain;
2. rdfs3 — range;
3. rdfs7 — subproperty propagation;
4. rdfs9 — subclass propagation.

These are preferable because they:

* are semantically central;
* are positive and monotonic;
* do not require fresh witnesses;
* correspond to existing optimized functions;
* exercise indexed joins;
* have simple model-theoretic conditions;
* can be tested through small generated graphs.

Deliverables:

RDF.Semantics.Core
RDFS.Semantics
index lookup soundness lemmas
four rule soundness proofs
four optimized-vs-reference equivalence proofs
generated property tests
CI target
documentation page

Suggested CI target:

verify-rdf-mt:
	fstar.exe RDF.Semantics.Core.fst
	fstar.exe RDF.Semantics.RDF.fst
	fstar.exe RDFS.Semantics.fst
	fstar.exe RDFS.Closure.Soundness.fst

Generated tests

The semantic proofs should also produce executable test templates.

For rdfs2:

Generate:
  p rdfs:domain c
  x p y
Require:
  x rdf:type c appears after closure.

For index equivalence:

For generated graphs g:
  generic_eval(rdfs2, g)
  and
  rdfs_rule_domain(g, build_indexed(g))
  produce extensionally equivalent graph sets.

For soundness boundary tests:

* literal objects must not become subjects under rdfs3;
* blank-node subjects and class expressions should be retained where allowed;
* duplicate premises should not affect set-equivalent output;
* graph ordering should not affect inferred graph content;
* optimized join ordering should not affect results.

The tests do not replace proofs. They exercise extraction and implementation boundaries that the pure F* theorem may not cover.

Claims enabled by this work

After the first milestone, the project may accurately claim:

Factoidal’s implementations of selected RDFS closure rules have been proved sound with respect to an independent F* formalization of the corresponding RDFS semantic conditions.

It should not yet claim:

Factoidal is a complete formally verified implementation of RDF or RDFS semantics.

After closure-step and bounded-iteration proofs:

Every triple added by the verified RDFS closure fragment is an RDFS semantic consequence of the input graph, under the stated fragment restrictions.

Completeness requires separate work.

Longer-term extensions

Complete simple entailment characterization

Prove equivalence between simple entailment and blank-node graph homomorphism for a bounded RDF 1.1 fragment.

RDFS rule completeness

For the appropriate finite vocabulary and datatype-free fragment, prove that saturated closure is complete for RDFS entailment.

This requires:

* termination or finite-domain saturation;
* closure fixed-point characterization;
* canonical-model construction;
* treatment of axiomatic triples;
* precise fragment restrictions.

OWL 2 RL/RDF

Add semantic soundness for the positive OWL RL/RDF rule subset.

Do not begin by formalizing all OWL Direct Semantics. Formalize only the interpretation conditions required by selected rules and state the supported profile precisely.

SPARQL entailment regimes

Relate graph closure and query evaluation:

evaluate(query, closure(graph))

to the formal SPARQL entailment-regime semantics.

Extracted implementation correspondence

Extend theorem coverage across:

* F* source;
* extracted OCaml;
* JavaScript;
* WebAssembly;
* storage-backed graph interfaces.

This will require explicit contracts at foreign and storage boundaries.

Open questions

1. Should the first interpretation structure closely mirror W3C notation (IR, IP, IEXT, IS, IL, LV) or use a smaller relational encoding?
2. Should RDF 1.2 triple terms be excluded from the first fragment or modeled immediately?
3. Should blank-node assignments range over all identifiers or only the finite identifiers occurring in a graph?
4. Should rule-output graphs be compared as lists, sets, or multisets?
5. Which existing indexed_graph invariants are already proved and which require new bridge lemmas?
6. Should declarative rules be introduced immediately or only after direct soundness proofs for the existing functions?
7. How should axiomatic triples be divided between finite tables and syntactically generated infinite families?

Recommendation

Implement the work in two parallel tracks:

Track A: semantic soundness

Build the interpretation, satisfaction, and entailment definitions and prove the existing rule functions sound.

Track B: executable correspondence

Build a small declarative positive-rule evaluator and prove it extensionally equivalent to the optimized Factoidal functions.

Track A establishes semantic meaning.

Track B establishes that optimization has not changed the intended rule.

The combined architecture is:

W3C model-theoretic condition
             ↑ soundness
declarative rule representation
             ↑ compilation/refinement
existing Factoidal optimized function
             ↑ extraction and boundary testing
native / JS / WASM executable

This wraps a model-theoretic verification layer around the current Factoidal architecture while preserving the project’s existing implementation and performance work.
