/-
L4Factoidal.OWL.TestsManifest — the W3C OWL test-type classifier.

Port of `formal/fstar/OWL.Tests.Manifest.fst` (28 lines). Migrated in
the F\* tree out of `owl_runner.ml`, because iron rule #11 keeps test-type
classification out of glue.
-/

namespace L4Factoidal.OWL

def owlTestNs : String := "http://www.w3.org/2007/OWL/testOntology#"

/-- Is this IRI one of the five OWL test types the suite declares? -/
def isTestTypeIri (iri : String) : Bool :=
  if !iri.startsWith owlTestNs then false
  else
    let suffix := iri.drop owlTestNs.length
    suffix == "PositiveEntailmentTest" ||
    suffix == "NegativeEntailmentTest" ||
    suffix == "ConsistencyTest" ||
    suffix == "InconsistencyTest" ||
    suffix == "ProfileIdentificationTest"

/-! ## Build-time checks -/

#guard isTestTypeIri (owlTestNs ++ "PositiveEntailmentTest")
#guard isTestTypeIri (owlTestNs ++ "NegativeEntailmentTest")
#guard isTestTypeIri (owlTestNs ++ "ConsistencyTest")
#guard isTestTypeIri (owlTestNs ++ "InconsistencyTest")
#guard isTestTypeIri (owlTestNs ++ "ProfileIdentificationTest")

/-! The namespace alone is not a test type, and neither is an unknown
    suffix inside it. A classifier written as "starts with the
    namespace" would accept both, and would then count every ontology
    term in that namespace as a test. -/

#guard !isTestTypeIri owlTestNs
#guard !isTestTypeIri (owlTestNs ++ "SomethingElse")
#guard !isTestTypeIri (owlTestNs ++ "PositiveEntailmentTestX")
#guard !isTestTypeIri ""

/-! A right-hand match in the WRONG namespace is not a test type
    either — the check is on the whole IRI, not on the local name. -/

#guard !isTestTypeIri "http://example.org/PositiveEntailmentTest"

/-! Positive and Negative entailment tests are distinct, and their names
    share a suffix. A `endsWith "EntailmentTest"` classifier would merge
    them; this one does not merge anything, but the five are checked
    individually above so a dropped arm shows up. -/

#guard (([owlTestNs ++ "PositiveEntailmentTest",
          owlTestNs ++ "NegativeEntailmentTest",
          owlTestNs ++ "ConsistencyTest",
          owlTestNs ++ "InconsistencyTest",
          owlTestNs ++ "ProfileIdentificationTest"]).filter isTestTypeIri).length == 5

end L4Factoidal.OWL
