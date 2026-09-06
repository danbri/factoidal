/-
Harness/LwsProbe — run the Linked Web Storage Protocol 1.0 Core conformance
registry and print its score.

This is a HARNESS, not part of the verified library: it prints. What it
prints is not a second opinion — every `guarded` row names a `def … : Bool`
in `L4Factoidal.LWS.Tests`, which `#guard` already evaluates at build time,
and this probe evaluates the SAME function so a reader who cannot run
`lake build` still sees the score.

Usage: `lake exe l4lws-probe`
-/
import L4Factoidal.LWS.Tests
import L4Factoidal.Solid.Tests

open L4Factoidal.LWS
open L4Factoidal.LWS.Conformance

namespace LwsProbe

/-- The checks, by the registry id they decide. A row whose status is
`guarded` and whose id is missing here is reported as unlinked, so a registry
row cannot claim a check that no longer exists. -/
def checks : List (String × Bool) :=
  [ ("lws-core-03", Tests.lwsGuardLastModifiedOnGet && Tests.lwsGuardLastModifiedOnHead)
  , ("lws-core-04", Tests.lwsGuardInsertionsRefuseBlankNodes &&
                    Tests.lwsGuardInsertionsAcceptWithoutBlankNodes)
  , ("lws-core-05", Tests.lwsGuardContainerEnumerates)
  , ("lws-core-08", Tests.lwsGuardAuxiliaryLinksAdvertised)
  , ("lws-core-11", Tests.lwsGuardCreateReadUpdateDelete)
  , ("lws-core-12", Tests.lwsGuardCreatedIsNotSuccess)
    -- The draft's "not permitted" response is decided by Web Access
    -- Control, which is Solid's layer; the check lives there.
  , ("lws-core-13", L4Factoidal.Solid.Tests.solidGuardWacDenies) ]

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
  IO.println "=== Linked Web Storage Protocol 1.0 Core — conformance registry"
  IO.println "Source: https://w3c.github.io/lws-protocol/lws10-core/ (read 2026-09-06)"
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
    IO.println s!"UNLINKED guarded rows (no check in Harness/LwsProbe.lean): {unlinked}"
  IO.println ""
  IO.println "host-verified rows:"
  for r in registry do
    match r.status with
    | .hostVerified suite => IO.println s!"  {r.id}  {suite}"
    | _ => pure ()
  if fail > 0 || !unlinked.isEmpty then pure 1 else pure 0

end LwsProbe

def main (args : List String) : IO UInt32 := do
  if args.contains "--markdown" then
    LwsProbe.markdown
    pure 0
  else
    LwsProbe.main
