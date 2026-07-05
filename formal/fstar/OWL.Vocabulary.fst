module OWL.Vocabulary

(* Shared OWL + RDF vocabulary IRI constants — now a thin re-export
 * shim over RDF.Vocabulary.fst (2026-07-05, design doc
 * "foundational-core-refactor" §2.6/§3.3 step 2).
 *
 * History: per #209 (Tableau audit), the same OWL IRI strings were
 * once defined in two places — Tableau.fst (no suffix) and
 * OWL.QueryRewrite.fst (`_iri` suffix) — with a comment in
 * OWL.QueryRewrite.fst:76-80 noting the deliberate duplication. This
 * module became the single source of truth for that; RDF.Vocabulary
 * is now the source of truth one level further down (widening the
 * scope from "OWL, without duplication" to "RDF/RDFS/OWL, in one
 * place" per the design doc). Tableau.fst (this module's one
 * dependent) is unaffected — every name it opens still resolves here,
 * unqualified, exactly as before.
 *
 * Each constant re-derives the same `wf_iri`-refined value from
 * RDF.Vocabulary's canonical string, `assert_norm`-proved locally
 * (same pattern used everywhere else in the tree).
 *)

open RDF.Graph.Executable
open RDF.Vocabulary

(* ----- Class-expression bookkeeping ----------------------------------- *)

let owl_intersectionOf : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_intersectionOf);
  RDF.Vocabulary.owl_intersectionOf

let owl_unionOf : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_unionOf);
  RDF.Vocabulary.owl_unionOf

let owl_complementOf : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_complementOf);
  RDF.Vocabulary.owl_complementOf

let owl_disjointWith : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_disjointWith);
  RDF.Vocabulary.owl_disjointWith

(* ----- Restrictions --------------------------------------------------- *)

let owl_Restriction : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_Restriction);
  RDF.Vocabulary.owl_Restriction

let owl_onProperty : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_onProperty);
  RDF.Vocabulary.owl_onProperty

let owl_someValuesFrom : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_someValuesFrom);
  RDF.Vocabulary.owl_someValuesFrom

let owl_allValuesFrom : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_allValuesFrom);
  RDF.Vocabulary.owl_allValuesFrom

let owl_hasValue : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_hasValue);
  RDF.Vocabulary.owl_hasValue

(* ----- Cardinality family --------------------------------------------- *)

let owl_cardinality : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_cardinality);
  RDF.Vocabulary.owl_cardinality

let owl_minCardinality : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_minCardinality);
  RDF.Vocabulary.owl_minCardinality

let owl_maxCardinality : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_maxCardinality);
  RDF.Vocabulary.owl_maxCardinality

let owl_qualifiedCardinality : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_qualifiedCardinality);
  RDF.Vocabulary.owl_qualifiedCardinality

let owl_minQualifiedCardinality : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_minQualifiedCardinality);
  RDF.Vocabulary.owl_minQualifiedCardinality

let owl_maxQualifiedCardinality : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_maxQualifiedCardinality);
  RDF.Vocabulary.owl_maxQualifiedCardinality

let owl_onClass : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.owl_onClass);
  RDF.Vocabulary.owl_onClass

(* ----- RDF list-chain markers (used by OWL collections) --------------- *)

let rdf_first : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_first);
  RDF.Vocabulary.rdf_first

let rdf_rest : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_rest);
  RDF.Vocabulary.rdf_rest

let rdf_nil : wf_iri =
  assert_norm (is_iri RDF.Vocabulary.rdf_nil);
  RDF.Vocabulary.rdf_nil
