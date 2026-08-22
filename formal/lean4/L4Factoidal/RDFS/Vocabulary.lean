/-
L4Factoidal.RDFS.Vocabulary — the RDF/RDFS vocabulary IRIs the
entailment layers use.

Port of the corresponding constants in `formal/fstar/RDF.Vocabulary.fsti`.
The first five (`rdf_type`, `rdfs_subClassOf`, `rdfs_subPropertyOf`,
`rdfs_domain`, `rdfs_range`) are all the rdfs-core fragment
(Munoz/Perez/Gutierrez, "Simple and Efficient Minimal RDFS", JWS 2009 —
the fragment RDF 1.1 Semantics §9.2 rows rdfs2/3/5/7/9/11 range over)
mentions. The rest (added 2026-08-22 with `RDFS/FullClosure.lean`) are
the terms the full RDF 1.1 Semantics §8 / §9 rule tables and the §8.2 /
§9.3 axiomatic triples name. The F* file also carries the OWL
vocabulary; that lives in `OWL/Vocabulary.lean` here.

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

/-! ## The rest of the RDF / RDFS vocabulary (RDF 1.1 Semantics §8–§9)

Namespace strings first, so the `rdf:_n` container-membership family
— which is infinite and therefore cannot be a constant table — can be
recognised by prefix (`isContainerMembershipIri` in `FullClosure.lean`). -/

def rdfNs  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def rdfsNs : String := "http://www.w3.org/2000/01/rdf-schema#"

/-- `rdf:Property` — conclusion class of rdfD2, premise of rdfs6. -/
def rdfProperty : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Property", rfl⟩
/-- `rdf:List`, `rdf:nil`, `rdf:first`, `rdf:rest` — §8.2 / §9.3 axioms. -/
def rdfList  : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#List", rfl⟩
def rdfNil   : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil", rfl⟩
def rdfFirst : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#first", rfl⟩
def rdfRest  : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#rest", rfl⟩
/-- `rdf:Statement`, `rdf:subject`, `rdf:predicate`, `rdf:object` — the
reification vocabulary (axioms only; no rule concludes a reification,
which is what rdf-mt's `statement-entailment-*` negatives check). -/
def rdfStatement : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Statement", rfl⟩
def rdfSubject   : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#subject", rfl⟩
def rdfPredicate : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#predicate", rfl⟩
def rdfObject    : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#object", rfl⟩
def rdfValue     : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#value", rfl⟩
/-- `rdf:Alt`, `rdf:Bag`, `rdf:Seq` — §9.3 subclasses of `rdfs:Container`. -/
def rdfAlt : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Alt", rfl⟩
def rdfBag : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Bag", rfl⟩
def rdfSeq : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#Seq", rfl⟩
/-- `rdf:_1` — the one container-membership property every closure
carries (§9.3 lists `rdf:_n` for all n; the finite instantiation is
`rdf:_1` plus every `rdf:_n` the graphs mention). -/
def rdf1 : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#_1", rfl⟩

/-- `rdfs:Resource`, `rdfs:Class`, `rdfs:Literal`, `rdfs:Datatype`,
`rdfs:Container`, `rdfs:ContainerMembershipProperty`, `rdfs:member` —
RDF Schema §2 / §5. -/
def rdfsResource  : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#Resource", rfl⟩
def rdfsClass     : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#Class", rfl⟩
def rdfsLiteral   : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#Literal", rfl⟩
def rdfsDatatype  : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#Datatype", rfl⟩
def rdfsContainer : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#Container", rfl⟩
def rdfsContainerMembershipProperty : WfIri :=
  ⟨"http://www.w3.org/2000/01/rdf-schema#ContainerMembershipProperty", rfl⟩
def rdfsMember : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#member", rfl⟩
/-- `rdfs:seeAlso`, `rdfs:isDefinedBy`, `rdfs:comment`, `rdfs:label` —
RDF Schema §5.4; §9.3 axioms only. -/
def rdfsSeeAlso     : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#seeAlso", rfl⟩
def rdfsIsDefinedBy : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#isDefinedBy", rfl⟩
def rdfsComment     : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#comment", rfl⟩
def rdfsLabel       : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#label", rfl⟩

end L4Factoidal.RDFS
