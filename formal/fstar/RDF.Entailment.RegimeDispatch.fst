module RDF.Entailment.RegimeDispatch

// Experimental SPARQL entailment regimes x-rdfscore and x-rdfsplus,
// plus the full regime dispatch consumers call (iron rules #1/#15:
// regime dispatch is engine logic and lives HERE, not in CLI or npm
// glue -- the consumers pass the regime string through verbatim).
//
// SPARQL 1.1 Entailment Regimes is an explicit extension point: a
// regime is an entailment relation plus conditions on BGP matching.
// Both regimes here are materialisation-based -- answers are defined
// as SIMPLE entailment over the named closure of the queried graph --
// which is the standard construction for finite answer sets. The x-
// prefix marks them as experimental (non-W3C) names.
//
//   x-rdfscore  BGP answers over rho_df_closure
//               (RDF.Entailment.RDFS.RhoDFClosure.fst). This regime's
//               definition IS a theorem: on fragment data,
//               theorem_rdfs_regime_bgp_exact_answer and its ASK
//               corollaries (SPARQL11.EntailmentRegime.RDFS.fst) state
//               that the answers computed this way are EXACTLY the
//               rho-df-entailed consequences -- sound and complete,
//               chain-level (see docs/theorem-registry.md for the
//               definition of that term and every link in the chain).
//
//   x-rdfsplus  BGP answers over rdfs_plus_closure
//               (RDF.Entailment.RDFSPlus.fst): RDFS plus the practical
//               OWL subset (sameAs, inverseOf, symmetric/transitive/
//               functional/inverse-functional, equivalence). Every OWL
//               row runs under proved licensing + truth lemmas;
//               chain-level completeness is deliberately NOT claimed
//               (owl:sameAs equality breaks the Herbrand construction
//               -- see the registry's RDFS-Plus tier note).
//
// All other regime strings fall through to OWL.Closure's
// entailment_closure_for_query, which owns the W3C-named regimes
// ("RDFS", "OWL-RL", ...) and the comprehension-witness strip (#346).
// The two new closures mint no witness scaffolding, so no strip is
// needed on the new paths.

open RDF.Triple
open RDF.Graph
open OWL.Closure

let regime_x_rdfscore : string = "x-rdfscore"
let regime_x_rdfsplus : string = "x-rdfsplus"

let entailment_closure_for_query_ext (regime : string) (g : rdf_graph) (fuel : nat)
  : Tot rdf_graph =
  if regime = regime_x_rdfscore
  then RDF.Entailment.RDFS.RhoDFClosure.rho_df_closure g fuel
  else if regime = regime_x_rdfsplus
  then RDF.Entailment.RDFSPlus.rdfs_plus_closure g fuel
  else entailment_closure_for_query regime g fuel
