module OWL.ProfileSpec

open RDF.CoreSpec
open RDF.ModelTheory
open OWL.Vocabulary

// OWL profile and entailment-spec placement.
//
// Bucket: CORE SPEC.
//
// The current executable code has OWL-RL-shaped closure rules embedded inside
// `RDF.Graph.Executable`. This file marks the standards-facing home for that
// material without pretending that the executable rule subset is already a
// complete OWL formalisation.

type owl_profile =
  | OWL2RL
  | OWL2QL
  | OWL2EL
  | OWL2DL

type owl_semantics =
  | OWLRDFBasedSemantics
  | OWLDirectSemantics

noeq type owl_regime = {
  profile   : owl_profile;
  semantics : owl_semantics;
}

let owl_entails (_:owl_regime) (_:graph) (_:graph) : proposition =
  True

let owl_rl_rule_closure_sound_shape
  (regime:owl_regime)
  (source:graph)
  (closed:graph)
  : proposition =
  regime.profile == OWL2RL /\ owl_entails regime source closed

let owl_same_as_predicate : predicate = owl_sameAs
