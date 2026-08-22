/-
L4Factoidal.RDFS.Vocabulary — the five RDF/RDFS vocabulary IRIs the
rdfs-core fragment uses.

Port of the corresponding constants in `formal/fstar/RDF.Vocabulary.fsti`
(`rdf_type`, `rdfs_subClassOf`, `rdfs_subPropertyOf`, `rdfs_domain`,
`rdfs_range`). Only those five are ported: the rdfs-core fragment
(Munoz/Perez/Gutierrez, "Simple and Efficient Minimal RDFS", JWS 2009 —
the fragment RDF 1.1 Semantics §9.2 rows rdfs2/3/5/7/9/11 range over)
mentions no other vocabulary term. The F* file carries the whole RDF +
RDFS + OWL vocabulary; porting the rest is not needed here and would be
dead weight.

Every constant is a `WfIri` whose well-formedness witness is `rfl` — the
Lean counterpart of the F* tree's `assert_norm` witnesses: the kernel
evaluates `isIri` on the literal string at elaboration time, so a
mistyped IRI that failed the gate would be a build error, not a runtime
surprise.
-/
import L4Factoidal.RDF.Core

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-- `rdf:type` — RDF 1.1 Concepts §3.3.1 / Semantics §9.2 (the
conclusion predicate of rows rdfs2, rdfs3, rdfs9). -/
def rdfType : WfIri :=
  ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

/-- `rdfs:subClassOf` — RDF Schema §3.4 (rows rdfs9, rdfs11). -/
def rdfsSubClassOf : WfIri :=
  ⟨"http://www.w3.org/2000/01/rdf-schema#subClassOf", rfl⟩

/-- `rdfs:subPropertyOf` — RDF Schema §3.5 (rows rdfs5, rdfs7). -/
def rdfsSubPropertyOf : WfIri :=
  ⟨"http://www.w3.org/2000/01/rdf-schema#subPropertyOf", rfl⟩

/-- `rdfs:domain` — RDF Schema §3.2 (row rdfs2). -/
def rdfsDomain : WfIri :=
  ⟨"http://www.w3.org/2000/01/rdf-schema#domain", rfl⟩

/-- `rdfs:range` — RDF Schema §3.3 (row rdfs3). -/
def rdfsRange : WfIri :=
  ⟨"http://www.w3.org/2000/01/rdf-schema#range", rfl⟩

end L4Factoidal.RDFS
