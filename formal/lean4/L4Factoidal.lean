-- L4Factoidal — Lean 4 port of the Factoidal F* RDF/SPARQL core.
-- See PORT_NOTES.md for scope, correspondences, and the assumption
-- report against the F* originals.
import L4Factoidal.RDF.XmlCanon
import L4Factoidal.RDF.Core
import L4Factoidal.RDF.Graph
import L4Factoidal.SPARQL.Algebra
import L4Factoidal.SPARQL.Invariants
import L4Factoidal.RDFS.Vocabulary
import L4Factoidal.RDFS.RhoDF
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.ClosureTheorems
import L4Factoidal.RDFS.ClosureTests
import L4Factoidal.Tests
