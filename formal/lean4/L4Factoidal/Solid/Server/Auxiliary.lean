/-
L4Factoidal.Solid.Server.Auxiliary — the `acl` and `describedby` auxiliary
resources and their lifecycle.

Wraps: `L4Factoidal.LWS.Discovery` (`aclPathOf`, `describedByPathOf`, the
auxiliary links) and `L4Factoidal.LWS.Store` (`remove`).
Adds: the rule that an auxiliary resource is deleted with its subject
resource, and the rule that a description resource is authorized as its
subject is.

Source: https://solidproject.org/TR/protocol §4.3 Auxiliary Resources,
verbatim:

  "Servers MUST support auxiliary resources defined by this specification
  and manage the association between a subject resource and auxiliary
  resources. When a subject resource is deleted its auxiliary resources are
  also deleted by the server."

  "Servers MUST advertise auxiliary resources associated with a subject
  resource by responding to HEAD and GET requests by including the HTTP Link
  header field with the rel parameter [RFC8288]."

§4.3.2 Description Resource, verbatim:

  "Servers MUST NOT directly associate more than one description resource to
  a subject resource."

  "When an HTTP request targets a description resource, the server MUST
  apply the authorization rule that is used for the subject resource with
  which the description resource is associated."

Web Access Control §3.1, verbatim:

  "Servers MUST NOT directly associate more than one ACL resource to a
  resource."

  "Clients MUST NOT derive ACL resource URIs through string operations on
  resource URIs."

The server DOES derive them (`aclPathOf`, `describedByPathOf` in
`L4Factoidal.LWS.Discovery`): that rule binds clients, and a server has to
choose the URI somehow. A client of this server finds them through the
`Link` header field, which is what §4.3 requires it to advertise.
-/
import L4Factoidal.LWS.Operations

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.LWS

/-- The auxiliary resources of a subject resource. Exactly one of each
kind, which is what "Servers MUST NOT directly associate more than one
description resource to a subject resource" and its ACL counterpart
require. -/
def auxiliaryPaths (p : String) : List String :=
  [aclPathOf p, describedByPathOf p]

/-- Is this path an auxiliary resource, and if so, of what subject? An ACL
resource is never itself given an ACL, so this stops the recursion. -/
def subjectOfAuxiliary? (p : String) : Option String :=
  let cs := p.toList
  if p.endsWith ".acl" then some (String.ofList (cs.take (cs.length - 4)))
  else if p.endsWith ".meta" then some (String.ofList (cs.take (cs.length - 5)))
  else none

/-- The path whose ACL governs a request on `p` — the subject resource for
an auxiliary, and `p` itself otherwise. §4.3.2: "When an HTTP request
targets a description resource, the server MUST apply the authorization rule
that is used for the subject resource". -/
def authorizationSubject (p : String) : String :=
  (subjectOfAuxiliary? p).getD p

variable {σ : Type}

/-- Delete a resource and its auxiliary resources. §4.3: "When a subject
resource is deleted its auxiliary resources are also deleted by the
server." -/
def deleteWithAuxiliaries (S : Store σ) (st : σ) (p : String) : σ :=
  (auxiliaryPaths p).foldl (fun s a => S.remove s a) (S.remove st p)

/-! ## The lifecycle theorem -/

/-- The two auxiliary paths of a subject differ, so removing one does not
undo the removal of the other. The suffixes have different lengths, which is
the whole argument. -/
theorem aclNeDescribedBy (p : String) : aclPathOf p ≠ describedByPathOf p := by
  intro h
  have hlen := congrArg String.length h
  simp only [aclPathOf, describedByPathOf, String.length_append] at hlen
  have h4 : (".acl" : String).length = 4 := by decide
  have h5 : (".meta" : String).length = 5 := by decide
  omega

/-- After deleting a subject resource, neither it nor either of its
auxiliary resources resolves. §4.3, over the reference store. -/
theorem auxiliariesDeletedWithSubject (st : MemState) (p : String) :
    memLookup (deleteWithAuxiliaries MemStore st p) p = none ∧
    memLookup (deleteWithAuxiliaries MemStore st p) (aclPathOf p) = none ∧
    memLookup (deleteWithAuxiliaries MemStore st p) (describedByPathOf p) = none := by
  have haclP : p ≠ aclPathOf p := by
    intro h
    have hlen := congrArg String.length h
    simp only [aclPathOf, String.length_append] at hlen
    have h4 : (".acl" : String).length = 4 := by decide
    omega
  have hmetaP : p ≠ describedByPathOf p := by
    intro h
    have hlen := congrArg String.length h
    simp only [describedByPathOf, String.length_append] at hlen
    have h5 : (".meta" : String).length = 5 := by decide
    omega
  refine ⟨?_, ?_, ?_⟩
  · show memLookup (memRemove (memRemove (memRemove st p) (aclPathOf p))
                     (describedByPathOf p)) p = none
    rw [memLookup_memRemove_other _ _ _ hmetaP,
        memLookup_memRemove_other _ _ _ haclP,
        memLookup_memRemove_same]
  · show memLookup (memRemove (memRemove (memRemove st p) (aclPathOf p))
                     (describedByPathOf p)) (aclPathOf p) = none
    rw [memLookup_memRemove_other _ _ _ (aclNeDescribedBy p),
        memLookup_memRemove_same]
  · show memLookup (memRemove (memRemove (memRemove st p) (aclPathOf p))
                     (describedByPathOf p)) (describedByPathOf p) = none
    rw [memLookup_memRemove_same]

end L4Factoidal.Solid.Server
