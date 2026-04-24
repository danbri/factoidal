module Entailment.Policy

open RDF.CoreSpec
open RDF.ModelTheory
open OWL.ProfileSpec

// Entailment-regime policy.
//
// Bucket: MIDZONE.
//
// RDF model theory belongs in `corespecs/`. Project decisions about which
// regimes are enabled, approximated, or implemented by closure rules belong
// here so they are visible and debatable.

noeq type entailment_regime =
  | SimpleEntailment
  | RDFEntailment
  | RDFSEntailment
  | OWLEntailment : owl_regime -> entailment_regime

type regime_support =
  | DeclarativeOnly
  | ExecutableSoundSubset
  | ExecutableCompleteForProfile

noeq type regime_policy = {
  regime  : entailment_regime;
  support : regime_support;
}

let regime_entails (_:regime_policy) (_:graph) (_:graph) : proposition =
  True
