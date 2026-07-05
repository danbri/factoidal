module RDF.Vocabulary.Axioms

// Owner addition (2026-07-05) to docs/designissues/2026-07-05-
// foundational-core-refactor.md: the RDF/RDFS axiomatic triple sets
// that W3C publishes in RDF 1.1 Semantics (https://www.w3.org/TR/
// rdf11-mt/) §"RDF axiomatic triples" and §"RDFS axiomatic triples"
// currently have NO declarative representation anywhere in this tree
// — their consequences are hard-coded as closure rules
// (`rdfs_rule_range` et al. in RDF.Graph.Executable.fst) and
// reflexivity axioms are harvested programmatically
// (`rdfs_reflexivity_axioms`). This module is the finite axiomatic
// tables as literal `triple` lists, auditable line-by-line against
// the spec text — one `let` per triple, one spec-table-row citation
// per `let`, so a reviewer can check this module against the W3C
// document without executing anything.
//
// Only the genuinely infinite families stay rule-generated, per the
// spec's own note on infinitude:
//   - RDF axiomatic triples: `rdf:_1 rdf:type rdf:Property .`,
//     `rdf:_2 rdf:type rdf:Property .`, ... (all n) — NOT included
//     here; `RDF.Graph.Executable.fst`'s `rdfs_rule_container_membership`
//     already generates the rdf:_n member-property triples it needs
//     (`rdf:_n rdfs:subPropertyOf rdfs:member`, `rdf:_n rdf:type
//     rdfs:ContainerMembershipProperty`) for whatever finite set of
//     rdf:_n IRIs actually appears in a given graph — the rule-
//     generated approach is *correct* for an infinite family; only the
//     FINITE tables belong here.
//   - RDFS axiomatic triples: `rdf:_1 rdf:type rdfs:ContainerMembership
//     Property .`, `rdf:_1 rdfs:domain rdfs:Resource .`, `rdf:_1
//     rdfs:range rdfs:Resource .`, ... (all n) — same exclusion,
//     same reason.
//
// Scope note (2026-07-05 migration step 2, RDF.Vocabulary
// consolidation): this module is created and verified in this slice,
// but is NOT YET wired into `rdfs_closure`/`entailment_closure` as a
// seed graph — those functions still live inside
// `RDF.Graph.Executable.fst` (design doc step 6, "RDFS.Closure /
// OWL.Closure extraction", not yet landed), and wiring a new seed into
// them is a behavior change that belongs in that step's own gate, not
// this one (this step's gate is "no logic change, pure constant
// re-homing" — see design doc §3.3 step 2's row). The table below is
// therefore additive-only: it exists, is verified against the spec
// text, and is available for the closure-rewiring step to consume
// once it lands, but the rdf-mt / OWL suite scores in this commit are
// unaffected by its existence (nothing calls into this module yet).

open RDF.Graph.Executable
open FStar.List.Tot
module Vocab = RDF.Vocabulary

(** ------------------------------------------------------------------ *)
(** wf_iri casts — one per distinct IRI this table needs. Same pattern *)
(** as every other vocabulary block in the tree (assert_norm on a      *)
(** literal string via RDF.Vocabulary's canonical value).              *)
(** ------------------------------------------------------------------ *)

let i_rdf_type : wf_iri = assert_norm (is_iri Vocab.rdf_type); Vocab.rdf_type
let i_rdf_Property : wf_iri = assert_norm (is_iri Vocab.rdf_Property); Vocab.rdf_Property
let i_rdf_List : wf_iri = assert_norm (is_iri Vocab.rdf_List); Vocab.rdf_List
let i_rdf_Statement : wf_iri = assert_norm (is_iri Vocab.rdf_Statement); Vocab.rdf_Statement
let i_rdf_first : wf_iri = assert_norm (is_iri Vocab.rdf_first); Vocab.rdf_first
let i_rdf_rest : wf_iri = assert_norm (is_iri Vocab.rdf_rest); Vocab.rdf_rest
let i_rdf_nil : wf_iri = assert_norm (is_iri Vocab.rdf_nil); Vocab.rdf_nil
let i_rdf_subject : wf_iri = assert_norm (is_iri Vocab.rdf_subject); Vocab.rdf_subject
let i_rdf_predicate : wf_iri = assert_norm (is_iri Vocab.rdf_predicate); Vocab.rdf_predicate
let i_rdf_object : wf_iri = assert_norm (is_iri Vocab.rdf_object); Vocab.rdf_object
let i_rdf_value : wf_iri = assert_norm (is_iri Vocab.rdf_value); Vocab.rdf_value
let i_rdf_Alt : wf_iri = assert_norm (is_iri Vocab.rdf_Alt); Vocab.rdf_Alt
let i_rdf_Bag : wf_iri = assert_norm (is_iri Vocab.rdf_Bag); Vocab.rdf_Bag
let i_rdf_Seq : wf_iri = assert_norm (is_iri Vocab.rdf_Seq); Vocab.rdf_Seq

let i_rdfs_subClassOf : wf_iri = assert_norm (is_iri Vocab.rdfs_subClassOf); Vocab.rdfs_subClassOf
let i_rdfs_subPropertyOf : wf_iri = assert_norm (is_iri Vocab.rdfs_subPropertyOf); Vocab.rdfs_subPropertyOf
let i_rdfs_domain : wf_iri = assert_norm (is_iri Vocab.rdfs_domain); Vocab.rdfs_domain
let i_rdfs_range : wf_iri = assert_norm (is_iri Vocab.rdfs_range); Vocab.rdfs_range
let i_rdfs_Class : wf_iri = assert_norm (is_iri Vocab.rdfs_Class); Vocab.rdfs_Class
let i_rdfs_Resource : wf_iri = assert_norm (is_iri Vocab.rdfs_Resource); Vocab.rdfs_Resource
let i_rdfs_Literal : wf_iri = assert_norm (is_iri Vocab.rdfs_Literal); Vocab.rdfs_Literal
let i_rdfs_Datatype : wf_iri = assert_norm (is_iri Vocab.rdfs_Datatype); Vocab.rdfs_Datatype
let i_rdfs_ContainerMembershipProperty : wf_iri =
  assert_norm (is_iri Vocab.rdfs_ContainerMembershipProperty); Vocab.rdfs_ContainerMembershipProperty
let i_rdfs_member : wf_iri = assert_norm (is_iri Vocab.rdfs_member); Vocab.rdfs_member
let i_rdfs_Container : wf_iri = assert_norm (is_iri Vocab.rdfs_Container); Vocab.rdfs_Container
let i_rdfs_seeAlso : wf_iri = assert_norm (is_iri Vocab.rdfs_seeAlso); Vocab.rdfs_seeAlso
let i_rdfs_isDefinedBy : wf_iri = assert_norm (is_iri Vocab.rdfs_isDefinedBy); Vocab.rdfs_isDefinedBy
let i_rdfs_comment : wf_iri = assert_norm (is_iri Vocab.rdfs_comment); Vocab.rdfs_comment
let i_rdfs_label : wf_iri = assert_norm (is_iri Vocab.rdfs_label); Vocab.rdfs_label

(** ------------------------------------------------------------------ *)
(** RDF axiomatic triples                                              *)
(** (https://www.w3.org/TR/rdf11-mt/ §"RDF axiomatic triples", finite  *)
(** rows only — the rdf:_n family is excluded, see module banner)      *)
(** ------------------------------------------------------------------ *)

let rdf_axiom_type_type_property : triple =
  { s = S_IRI i_rdf_type; p = i_rdf_type; o = T_IRI i_rdf_Property }
let rdf_axiom_subject_type_property : triple =
  { s = S_IRI i_rdf_subject; p = i_rdf_type; o = T_IRI i_rdf_Property }
let rdf_axiom_predicate_type_property : triple =
  { s = S_IRI i_rdf_predicate; p = i_rdf_type; o = T_IRI i_rdf_Property }
let rdf_axiom_object_type_property : triple =
  { s = S_IRI i_rdf_object; p = i_rdf_type; o = T_IRI i_rdf_Property }
let rdf_axiom_first_type_property : triple =
  { s = S_IRI i_rdf_first; p = i_rdf_type; o = T_IRI i_rdf_Property }
let rdf_axiom_rest_type_property : triple =
  { s = S_IRI i_rdf_rest; p = i_rdf_type; o = T_IRI i_rdf_Property }
let rdf_axiom_value_type_property : triple =
  { s = S_IRI i_rdf_value; p = i_rdf_type; o = T_IRI i_rdf_Property }
let rdf_axiom_nil_type_list : triple =
  { s = S_IRI i_rdf_nil; p = i_rdf_type; o = T_IRI i_rdf_List }

let rdf_axiomatic_triples : list triple = [
  rdf_axiom_type_type_property;
  rdf_axiom_subject_type_property;
  rdf_axiom_predicate_type_property;
  rdf_axiom_object_type_property;
  rdf_axiom_first_type_property;
  rdf_axiom_rest_type_property;
  rdf_axiom_value_type_property;
  rdf_axiom_nil_type_list;
]

(** ------------------------------------------------------------------ *)
(** RDFS axiomatic triples                                             *)
(** (https://www.w3.org/TR/rdf11-mt/ §"RDFS axiomatic triples", finite *)
(** rows only — the rdf:_n family is excluded, see module banner)      *)
(** ------------------------------------------------------------------ *)

// --- rdfs:domain group (16 rows) -----------------------------------
let rdfs_axiom_dom_type : triple =
  { s = S_IRI i_rdf_type; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_dom_domain : triple =
  { s = S_IRI i_rdfs_domain; p = i_rdfs_domain; o = T_IRI i_rdf_Property }
let rdfs_axiom_dom_range : triple =
  { s = S_IRI i_rdfs_range; p = i_rdfs_domain; o = T_IRI i_rdf_Property }
let rdfs_axiom_dom_subPropertyOf : triple =
  { s = S_IRI i_rdfs_subPropertyOf; p = i_rdfs_domain; o = T_IRI i_rdf_Property }
let rdfs_axiom_dom_subClassOf : triple =
  { s = S_IRI i_rdfs_subClassOf; p = i_rdfs_domain; o = T_IRI i_rdfs_Class }
let rdfs_axiom_dom_subject : triple =
  { s = S_IRI i_rdf_subject; p = i_rdfs_domain; o = T_IRI i_rdf_Statement }
let rdfs_axiom_dom_predicate : triple =
  { s = S_IRI i_rdf_predicate; p = i_rdfs_domain; o = T_IRI i_rdf_Statement }
let rdfs_axiom_dom_object : triple =
  { s = S_IRI i_rdf_object; p = i_rdfs_domain; o = T_IRI i_rdf_Statement }
let rdfs_axiom_dom_member : triple =
  { s = S_IRI i_rdfs_member; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_dom_first : triple =
  { s = S_IRI i_rdf_first; p = i_rdfs_domain; o = T_IRI i_rdf_List }
let rdfs_axiom_dom_rest : triple =
  { s = S_IRI i_rdf_rest; p = i_rdfs_domain; o = T_IRI i_rdf_List }
let rdfs_axiom_dom_seeAlso : triple =
  { s = S_IRI i_rdfs_seeAlso; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_dom_isDefinedBy : triple =
  { s = S_IRI i_rdfs_isDefinedBy; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_dom_comment : triple =
  { s = S_IRI i_rdfs_comment; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_dom_label : triple =
  { s = S_IRI i_rdfs_label; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_dom_value : triple =
  { s = S_IRI i_rdf_value; p = i_rdfs_domain; o = T_IRI i_rdfs_Resource }

// --- rdfs:range group (16 rows) --------------------------------------
let rdfs_axiom_rng_type : triple =
  { s = S_IRI i_rdf_type; p = i_rdfs_range; o = T_IRI i_rdfs_Class }
let rdfs_axiom_rng_domain : triple =
  { s = S_IRI i_rdfs_domain; p = i_rdfs_range; o = T_IRI i_rdfs_Class }
let rdfs_axiom_rng_range : triple =
  { s = S_IRI i_rdfs_range; p = i_rdfs_range; o = T_IRI i_rdfs_Class }
let rdfs_axiom_rng_subPropertyOf : triple =
  { s = S_IRI i_rdfs_subPropertyOf; p = i_rdfs_range; o = T_IRI i_rdf_Property }
let rdfs_axiom_rng_subClassOf : triple =
  { s = S_IRI i_rdfs_subClassOf; p = i_rdfs_range; o = T_IRI i_rdfs_Class }
let rdfs_axiom_rng_subject : triple =
  { s = S_IRI i_rdf_subject; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_rng_predicate : triple =
  { s = S_IRI i_rdf_predicate; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_rng_object : triple =
  { s = S_IRI i_rdf_object; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_rng_member : triple =
  { s = S_IRI i_rdfs_member; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_rng_first : triple =
  { s = S_IRI i_rdf_first; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_rng_rest : triple =
  { s = S_IRI i_rdf_rest; p = i_rdfs_range; o = T_IRI i_rdf_List }
let rdfs_axiom_rng_seeAlso : triple =
  { s = S_IRI i_rdfs_seeAlso; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_rng_isDefinedBy : triple =
  { s = S_IRI i_rdfs_isDefinedBy; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }
let rdfs_axiom_rng_comment : triple =
  { s = S_IRI i_rdfs_comment; p = i_rdfs_range; o = T_IRI i_rdfs_Literal }
let rdfs_axiom_rng_label : triple =
  { s = S_IRI i_rdfs_label; p = i_rdfs_range; o = T_IRI i_rdfs_Literal }
let rdfs_axiom_rng_value : triple =
  { s = S_IRI i_rdf_value; p = i_rdfs_range; o = T_IRI i_rdfs_Resource }

// --- rdfs:subClassOf group (4 rows) -----------------------------------
let rdfs_axiom_alt_subClassOf_container : triple =
  { s = S_IRI i_rdf_Alt; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Container }
let rdfs_axiom_bag_subClassOf_container : triple =
  { s = S_IRI i_rdf_Bag; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Container }
let rdfs_axiom_seq_subClassOf_container : triple =
  { s = S_IRI i_rdf_Seq; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Container }
let rdfs_axiom_cmp_subClassOf_property : triple =
  { s = S_IRI i_rdfs_ContainerMembershipProperty; p = i_rdfs_subClassOf; o = T_IRI i_rdf_Property }

// --- rdfs:subPropertyOf (1 row) ---------------------------------------
let rdfs_axiom_isDefinedBy_subPropertyOf_seeAlso : triple =
  { s = S_IRI i_rdfs_isDefinedBy; p = i_rdfs_subPropertyOf; o = T_IRI i_rdfs_seeAlso }

// --- Datatype (1 row) --------------------------------------------------
let rdfs_axiom_datatype_subClassOf_class : triple =
  { s = S_IRI i_rdfs_Datatype; p = i_rdfs_subClassOf; o = T_IRI i_rdfs_Class }

let rdfs_axiomatic_triples : list triple = [
  rdfs_axiom_dom_type; rdfs_axiom_dom_domain; rdfs_axiom_dom_range;
  rdfs_axiom_dom_subPropertyOf; rdfs_axiom_dom_subClassOf;
  rdfs_axiom_dom_subject; rdfs_axiom_dom_predicate; rdfs_axiom_dom_object;
  rdfs_axiom_dom_member; rdfs_axiom_dom_first; rdfs_axiom_dom_rest;
  rdfs_axiom_dom_seeAlso; rdfs_axiom_dom_isDefinedBy; rdfs_axiom_dom_comment;
  rdfs_axiom_dom_label; rdfs_axiom_dom_value;

  rdfs_axiom_rng_type; rdfs_axiom_rng_domain; rdfs_axiom_rng_range;
  rdfs_axiom_rng_subPropertyOf; rdfs_axiom_rng_subClassOf;
  rdfs_axiom_rng_subject; rdfs_axiom_rng_predicate; rdfs_axiom_rng_object;
  rdfs_axiom_rng_member; rdfs_axiom_rng_first; rdfs_axiom_rng_rest;
  rdfs_axiom_rng_seeAlso; rdfs_axiom_rng_isDefinedBy; rdfs_axiom_rng_comment;
  rdfs_axiom_rng_label; rdfs_axiom_rng_value;

  rdfs_axiom_alt_subClassOf_container; rdfs_axiom_bag_subClassOf_container;
  rdfs_axiom_seq_subClassOf_container; rdfs_axiom_cmp_subClassOf_property;

  rdfs_axiom_isDefinedBy_subPropertyOf_seeAlso;

  rdfs_axiom_datatype_subClassOf_class;
]

(** ------------------------------------------------------------------ *)
(** Combined finite seed graph (46 triples: 8 RDF + 38 RDFS). Not      *)
(** consumed anywhere yet — see the module banner's "Scope note".     *)
(** ------------------------------------------------------------------ *)

let finite_axiomatic_triples : list triple =
  rdf_axiomatic_triples @ rdfs_axiomatic_triples
