/-
Harness/SolidProbe — run the Solid Protocol and Web Access Control
conformance registry and print its score.

Same discipline as `Harness/LwsProbe.lean`: every `guarded` row names a
`def … : Bool` in `L4Factoidal.Solid.Tests`, `#guard` evaluates it at build
time, and this probe evaluates the same function so the score is readable
without a build. A `guarded` row with no check here is reported as unlinked
and the probe exits non-zero, so a row cannot claim a check that does not
exist.

Usage: `lake exe l4solid-probe`
-/
import L4Factoidal.Solid.Tests
import L4Factoidal.LWS.Tests

namespace SolidProbe

open L4Factoidal.Solid

/-- The registry this probe reports, named once so no `open` can make
`registry` ambiguous between the two specifications' registries. -/
abbrev registry := L4Factoidal.Solid.Conformance.registry
abbrev counts := L4Factoidal.Solid.Conformance.counts

def checks : List (String × Bool) :=
  [ ("solid-02-02", Tests.solidGuardContentTypeRequired400)
  , ("solid-02-03", Tests.solidGuardWacEnforced)
  , ("solid-02-05", Tests.solidGuardAcceptHeaders)
  , ("solid-03-01", Tests.solidGuardContainment)
  , ("solid-03-02", Tests.solidGuardSlashRedirect)
  , ("solid-03-03", Tests.solidGuardWacEnforced)
  , ("solid-04-01", Tests.solidGuardStorageTypeLink)
  , ("solid-04-03", Tests.solidGuardStorageTypeLink)
  , ("solid-04-04", Tests.solidGuardStorageDescriptionLink)
  , ("solid-04-06", Tests.solidGuardOwnerLink)
  , ("solid-04-07", Tests.solidGuardOwnerLink)
  , ("solid-04-15", Tests.solidGuardClientStorageWalkSteps)
  , ("solid-04-09", Tests.solidGuardContainment)
  , ("solid-04-10", Tests.solidGuardContainment)
  , ("solid-04-12", Tests.solidGuardAuxiliaryLinks)
  , ("solid-04-13", Tests.solidGuardDescriptionAuthorizedAsSubject)
  , ("solid-04-14", Tests.solidGuardDescriptionAuthorizedAsSubject)
  , ("solid-05-01", Tests.solidGuardUnsupportedMethod405)
  , ("solid-05-02", Tests.solidGuardPostAssignsName)
  , ("solid-05-03", Tests.solidGuardAllowHeader)
  , ("solid-05-04", Tests.solidGuardAllowHeader)
  , ("solid-05-05", Tests.solidGuardAcceptHeaders)
  , ("solid-05-06", Tests.solidGuardPostAssignsName)
  , ("solid-05-07", Tests.solidGuardIntermediateContainers)
  , ("solid-05-08", Tests.solidGuardPostAssignsName)
  , ("solid-05-09", Tests.solidGuardPostMissingTarget404)
  , ("solid-05-10", Tests.solidGuardPutAuxiliary)
  , ("solid-05-11", Tests.solidGuardPutRefusesContainmentEdit409)
  , ("solid-05-13", Tests.solidGuardN3PatchApplies)
  , ("solid-05-14", Tests.solidGuardN3PatchAcceptPatch)
  , ("solid-05-15", Tests.solidGuardN3PatchBlankNode422)
  , ("solid-05-16", Tests.solidGuardPatchMediaType415)
  , ("solid-05-30", Tests.solidGuardN3PatchRelativeIri)
  , ("solid-05-17", _root_.L4Factoidal.LWS.Tests.lwsGuardInsertionsRefuseBlankNodes)
  , ("solid-05-18", Tests.solidGuardN3PatchBlankNode422)
  , ("solid-05-19", Tests.solidGuardN3PatchBlankNode422)
  , ("solid-05-20", Tests.solidGuardN3PatchOperations)
  , ("solid-05-21", Tests.solidGuardN3PatchNoMatch409 &&
                    Tests.solidGuardN3PatchMultipleMatch409)
  , ("solid-05-22", Tests.solidGuardN3PatchDeletionsAbsent409)
  , ("solid-05-23", Tests.solidGuardDeleteRemovesContainment)
  , ("solid-05-24", Tests.solidGuardDeleteRootRefused405)
  , ("solid-05-25", Tests.solidGuardDeleteRemovesContainment)
  , ("solid-05-26", Tests.solidGuardDeleteRemovesAuxiliaries)
  , ("solid-05-27", Tests.solidGuardDeleteNonEmptyContainer409)
  , ("solid-06-01", Tests.solidGuardInboxAcceptsPost && Tests.solidGuardInboxAdvertised)
  , ("solid-06-03", Tests.solidGuardInboxAdvertised)
  , ("solid-06-02", Tests.solidGuardClientReadsLinks)
  , ("solid-08-01", Tests.solidGuardCorsHeaders)
  , ("solid-08-02", Tests.solidGuardCorsHeaders)
  , ("solid-08-03", Tests.solidGuardCorsHeaders)
  , ("solid-08-04", Tests.solidGuardCorsPreflight)
  , ("solid-09-01", Tests.solidGuardClientProfile)
  , ("solid-11-01", Tests.solidGuardWacEnforced)
  , ("solid-wac-01", Tests.solidGuardWacDenies)
  , ("solid-wac-02", Tests.solidGuardWacAccessToAgentMode)
  , ("solid-wac-03", Tests.solidGuardWacDefaultAgentClassSuperclassMode)
  , ("solid-wac-04", Tests.solidGuardWacAgentGroup)
  , ("solid-wac-05", Tests.solidGuardWacEnforced)
  , ("solid-wac-07", Tests.solidGuardWacAllowHeader)
  , ("solid-wac-08", Tests.solidGuardClientWacAllowParsing)
  , ("solid-wac-09", Tests.solidGuardClientReadsLinks)
  , ("solid-cl-02", Tests.solidGuardClientLinkFieldShapes)
  , ("solid-cl-01", Tests.solidGuardClientStorageWalk) ]

def check? (id : String) : Option Bool :=
  (checks.find? (fun (rid, _) => rid == id)).map (·.2)


/-- The registry as a markdown table, for `docs/lws-solid-conformance.md`.
Printed by `--markdown` so the ledger in the repository is generated from
the registry rather than typed beside it. -/
def markdown : IO Unit := do
  IO.println "| id | section | statement | module | status | decided by |"
  IO.println "|---|---|---|---|---|---|"
  for r in registry do
    let stmt := r.statement.replace "|" "\\|"
    IO.println s!"| `{r.id}` | {r.section_} | {stmt} | `{r.module}` | {r.status.label} | {r.status.detail} |"

def main : IO UInt32 := do
  IO.println "=== Solid Protocol v0.11.0 and Web Access Control — conformance registry"
  IO.println "Sources: https://solidproject.org/TR/protocol , https://solidproject.org/TR/wac"
  IO.println "         (both read 2026-09-06)"
  IO.println ""
  let mut pass := 0
  let mut fail := 0
  let mut unlinked : List String := []
  for r in registry do
    match r.status with
    | .guarded name =>
        match check? r.id with
        | some true  => pass := pass + 1
        | some false => do
            fail := fail + 1
            IO.println s!"FAIL {r.id}  {name}"
            IO.println s!"     {r.statement}"
        | none => unlinked := unlinked ++ [r.id]
    | _ => pure ()
  let total := pass + fail
  IO.println s!"guarded checks: {pass} pass, {fail} fail (out of {total})"
  IO.println ""
  let (proved, guarded, host, open_) := counts
  IO.println s!"registry: {proved} proved, {guarded} guarded, {host} host-verified, {open_} open (out of {registry.length})"
  IO.println ""
  IO.println "open rows:"
  for r in registry do
    match r.status with
    | .«open» why =>
        IO.println s!"  {r.id}  [{r.section_}]"
        IO.println s!"      {r.statement}"
        IO.println s!"      why: {why}"
    | _ => pure ()
  if !unlinked.isEmpty then
    IO.println ""
    IO.println s!"UNLINKED guarded rows (no check in Harness/SolidProbe.lean): {unlinked}"
  IO.println ""
  IO.println "host-verified rows:"
  for r in registry do
    match r.status with
    | .hostVerified suite => IO.println s!"  {r.id}  {suite}"
    | _ => pure ()
  if fail > 0 || !unlinked.isEmpty then pure 1 else pure 0

end SolidProbe

def main (args : List String) : IO UInt32 := do
  if args.contains "--markdown" then
    SolidProbe.markdown
    pure 0
  else
    SolidProbe.main
