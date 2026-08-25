/-
L4Factoidal.RDF.CanonicalManifest — RDFC-1.0 test-manifest vocabulary.

Port of `formal/fstar/RDF.Canonical.Manifest.fst` (38 lines). Migrated
in the F\* tree out of `rdfc10_runner.ml`: per iron rule #11, OCaml glue
may not classify test kinds.
-/

namespace L4Factoidal.RDF

/-- The three test types the rdf-canon manifests declare, plus the
    catch-all. `unknown` is a real outcome, not an error: a manifest may
    carry an entry type this runner does not implement, and reporting it
    as `unknown` is what keeps it out of both the numerator and the
    denominator. -/
inductive RdfcTestKind where
  | eval | negEval | map | unknown
  deriving Repr, DecidableEq, Inhabited

def rdfcNs : String := "https://w3c.github.io/rdf-canon/tests/vocab#"

def rdfcEvalTest : String := rdfcNs ++ "RDFC10EvalTest"
def rdfcNegEvalTest : String := rdfcNs ++ "RDFC10NegativeEvalTest"
def rdfcMapTest : String := rdfcNs ++ "RDFC10MapTest"

/-- Some entries (test075c, test075m) declare
    `rdfc:hashAlgorithm "SHA384"` to select a non-default hash for
    RDFC-1.0 §4.4 / §4.8. A runner reads this the same way it reads
    `mf:action` — a plain literal-object lookup. -/
def rdfcHashAlgorithm : String := rdfcNs ++ "hashAlgorithm"

def kindOfIri (iri : String) : RdfcTestKind :=
  if iri == rdfcEvalTest then .eval
  else if iri == rdfcNegEvalTest then .negEval
  else if iri == rdfcMapTest then .map
  else .unknown

def kindLabel : RdfcTestKind → String
  | .eval    => "Eval"
  | .negEval => "NegEval"
  | .map     => "Map"
  | .unknown => "Unknown"

/-! ## Build-time checks

The three IRIs are spelled out here rather than concatenated in the
guards, so a typo in `rdfcNs` fails rather than being absorbed by both
sides of the comparison. -/

#guard rdfcEvalTest == "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10EvalTest"
#guard rdfcNegEvalTest == "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10NegativeEvalTest"
#guard rdfcMapTest == "https://w3c.github.io/rdf-canon/tests/vocab#RDFC10MapTest"
#guard rdfcHashAlgorithm == "https://w3c.github.io/rdf-canon/tests/vocab#hashAlgorithm"

#guard kindOfIri rdfcEvalTest == .eval
#guard kindOfIri rdfcNegEvalTest == .negEval
#guard kindOfIri rdfcMapTest == .map
#guard kindOfIri "" == .unknown
#guard kindOfIri "https://example.org/other" == .unknown

/-! An eval test and a NEGATIVE eval test must not collide: their IRIs
    share a prefix, and a `startsWith` implementation would classify
    both as `eval`. -/

#guard rdfcNegEvalTest.startsWith rdfcNs
#guard kindOfIri rdfcNegEvalTest != kindOfIri rdfcEvalTest

#guard kindLabel (kindOfIri rdfcEvalTest) == "Eval"
#guard kindLabel .unknown == "Unknown"

end L4Factoidal.RDF
