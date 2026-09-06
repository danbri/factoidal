/-
L4Factoidal.Solid.Server.Containment — containment triples and the path
hierarchy.

Wraps: `L4Factoidal.LWS.Operations.containedPaths` (which container holds
which resource).
Adds: the RDF representation of a container as LDP Basic Container
containment triples, and the correspondence theorem.

Source: https://solidproject.org/TR/protocol §4.2 Resource Containment,
verbatim:

  "There is a 1-1 correspondence between containment triples and relative
  reference within the path name hierarchy. It follows that all resources
  are discoverable from a container and that it is not possible to create
  orphan resources."

  "The representation and behaviour of containers in Solid corresponds to
  LDP Basic Container and MUST be supported by server."

  "Servers can determine the field value of the HTTP Last-Modified header
  field in response to HEAD and GET requests targeting a container based on
  changes to containment triples."

§4.2.1 Contained Resource Metadata, verbatim:

  "Servers SHOULD include resource metadata about contained resources as
  part of the container description, unless that information is inapplicable
  to the server."

The correspondence is proved at the PATH level, which is where it lives: a
containment triple exists exactly when the object path's parent is the
subject path, and a path has at most one parent. The triple-building
function is a `filterMap` through `LWS.mkIri?`, so it cannot be proved
total without an IRI-syntax lemma about string concatenation; the guards in
`L4Factoidal.Solid.Tests` check the triples themselves.
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.RDF.Graph
import L4Factoidal.Solid.Server.Storage

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.LWS

/-! ## Vocabulary -/

def ldpContains : WfIri := ⟨"http://www.w3.org/ns/ldp#contains", by rfl⟩
def rdfType : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", by rfl⟩
def dctermsModified : WfIri := ⟨"http://purl.org/dc/terms/modified", by rfl⟩
def statSize : WfIri := ⟨"http://www.w3.org/ns/posix/stat#size", by rfl⟩
def statMtime : WfIri := ⟨"http://www.w3.org/ns/posix/stat#mtime", by rfl⟩
def xsdDateTime : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#dateTime", by rfl⟩
def ldpBasicContainerIri : WfIri := ⟨"http://www.w3.org/ns/ldp#BasicContainer", by rfl⟩
def ldpResourceIri : WfIri := ⟨"http://www.w3.org/ns/ldp#Resource", by rfl⟩

/-- An `xsd:integer` literal. -/
def intLiteral (n : Nat) : WfLiteral :=
  ⟨{ lexicalForm := toString n, datatype := xsdInteger,
     langTag := none, direction := none }, rfl⟩

/-! ## The container's RDF representation -/

variable {σ : Type}

/-- One containment triple: `<container> ldp:contains <child>`. -/
def containmentTriple (baseIri container childPath : String) : Option Triple :=
  match mkIri? (iriOfPath baseIri container), mkIri? (iriOfPath baseIri childPath) with
  | some s, some o => some { s := .iri s, p := ldpContains, o := .iri o }
  | _, _ => none

/-- The containment triples of a container: one per DIRECTLY contained
resource, in the store's own order. -/
def containmentTriples (S : Store σ) (baseIri : String) (st : σ) (c : String) :
    List Triple :=
  (containedPaths S st c).filterMap (containmentTriple baseIri c)

/-- The metadata triples §4.2.1 says a server SHOULD include about a
contained resource: its LDP type, its size in bytes and its modification
time. -/
def containedMetadata (baseIri : String) (e : Entry) : List Triple :=
  match mkIri? (iriOfPath baseIri e.path) with
  | none => []
  | some s =>
      [ { s := .iri s, p := rdfType,
          o := .iri (if e.kind.isContainer then ldpBasicContainerIri else ldpResourceIri) }
      , { s := .iri s, p := statSize, o := .literal (intLiteral e.body.length) }
      , { s := .iri s, p := statMtime, o := .literal (intLiteral e.mtime) } ]

/-- The whole RDF representation of a container: its own type triples, its
containment triples, and the metadata of each contained resource. -/
def containerGraph (S : Store σ) (baseIri : String) (st : σ) (c : String) : List Triple :=
  let selfTriples : List Triple :=
    match mkIri? (iriOfPath baseIri c) with
    | none => []
    | some s => [ { s := .iri s, p := rdfType, o := .iri ldpBasicContainerIri }
                , { s := .iri s, p := rdfType, o := .iri ldpResourceIri } ]
  selfTriples ++ containmentTriples S baseIri st c ++
    (containedPaths S st c).flatMap (fun p =>
      match S.lookup st p with
      | some e => containedMetadata baseIri e
      | none   => [])

/-! ## The 1-1 correspondence — §4.2 -/

/-- A resource is contained by AT MOST ONE container. This is one half of
"There is a 1-1 correspondence between containment triples and relative
reference within the path name hierarchy": no resource appears in two
containers, so no containment triple can be added by a second container. -/
theorem containerOfChildUnique (c1 c2 child : String)
    (h1 : LWS.contains c1 child = true) (h2 : LWS.contains c2 child = true) :
    c1 = c2 := by
  simp only [LWS.contains, Bool.and_eq_true, beq_iff_eq] at h1 h2
  exact Option.some.inj (h1.2.symm.trans h2.2)

/-- The other half: the container of a path is decided by the path itself,
through `parent?`, so a containment triple exists for a path exactly when
that path's parent is a container in the store. Nothing else can create one,
which is what "it is not possible to create orphan resources" means here. -/
theorem containedByParent (c child : String) (h : LWS.contains c child = true) :
    parent? child = some c ∧ pathIsContainer c = true := by
  simp only [LWS.contains, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.2, h.1⟩

/-- A path is enumerated by a container exactly when it is in the store AND
its parent is that container. `MemStore` instance of the general statement:
`containedPaths` filters `paths`, and `paths` lists exactly what resolves
(`L4Factoidal.LWS.memPaths_memLookup`). -/
theorem memContainedPaths_iff (st : MemState) (c child : String) :
    child ∈ containedPaths MemStore st c ↔
      (child ∈ memPaths st ∧ LWS.contains c child = true) := by
  simp [containedPaths, MemStore, memPaths, List.mem_filter]

end L4Factoidal.Solid.Server
