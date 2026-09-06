/-
Wasm.Ops.Lws — LWS storage handles: open a storage, step requests through
it, close it.

  lwsOpen(configJson)
    -> {"ok":true,"handle":"lws1","root":"/"} | {"ok":false,"error":"…"}
  lwsStep(handle, requestJson)
    -> {"ok":true,"response":{"status":N,"headers":[[n,v],…],"body":"…"}}
  lwsClose(handle)
    -> {"ok":true}

The JSON contract is `docs/lws-solid-conformance.md` § "wasm ABI"; the Node
hosts under `npm/factoidal/lws/` code against that section.

State lives HERE, in `Wasm/*`, exactly as `Wasm/Ops/Handles.lean` and
`Wasm/Ops/StoreHandles.lean` hold theirs: the protocol modules under
`L4Factoidal/LWS/` stay pure, and `L4Factoidal.LWS.Operations.step` is a
total function from a request and a state to a response and a state. This
module holds the state in an `IO.Ref`, so the operations are reachable only
through `L4Wasm.callIO`.

The clock is part of the state, not a call into a real clock. `lwsOpen`
takes `now` (seconds since the Unix epoch) and every mutation advances it by
one second; a request document may carry its own `now` to set it, which is
what a host with a real clock does.
-/
import Std.Data.HashMap
import Wasm.Ops.Support
import L4Factoidal.LWS.Operations

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.LWS
open L4Factoidal.HTTP (Request Response)

/-! ## Reading the JSON contract -/

/-- Decode a request document: `{method, target, headers, body}`, with the
optional `now` and `agent` overrides. Header names are lower-cased on the
way in, which is what `HTTP.Request.header?` expects. -/
def requestOfJson (j : Json) : Except String (Request × Option Nat × Option String) := do
  let method ← match j.getString? "method" with
    | some m => .ok m
    | none   => .error "request: member \"method\" is required"
  let target ← match j.getString? "target" with
    | some t => .ok t
    | none   => .error "request: member \"target\" is required"
  let headers : List (String × String) :=
    match j.getArray? "headers" with
    | none => []
    | some items => items.filterMap (fun it =>
        match it with
        | .array [.string n, .string v] => some (n.toLower, v)
        | _ => none)
  let body := (j.getString? "body").getD ""
  let now : Option Nat :=
    match j.field? "now" with
    | some (.number s) => s.toNat?
    | _ => none
  let agent := j.getString? "agent"
  .ok ({ method, path := target, queryStr := "", headers, body }, now, agent)

/-- Encode a response document: `{status, headers, body}`. -/
def jsonOfResponse (r : Response) : Json :=
  .object [ ("status", .number (toString r.status))
          , ("headers", .array (r.headers.map (fun (n, v) =>
              Json.array [.string n, .string v])))
          , ("body", .string r.body) ]

/-- Decode the handle configuration. Every member is optional. -/
structure OpenConfig where
  cfg : Config := {}
  now : Nat := 0
  /-- The ACL document of the storage root, written at open time.

  Web Access Control §3.2: "Root container ACL resources MUST have
  representations. The ACL resource of the root container MUST include an
  Authorization allowing the acl:Control access privilege." A storage cannot
  bootstrap that itself under enforcement — the request that would write the
  root ACL is the first request the root ACL would authorize — so it is a
  PROVISIONING input, given by the host when the storage is created. -/
  rootAcl : Option String := none
deriving Inhabited

def openConfigOfJson (text : String) : Except String OpenConfig :=
  if text.trim == "" then .ok {}
  else match parseJson text with
    | .error e => .error s!"config: {toString e}"
    | .ok j =>
        let baseIri := (j.getString? "baseIri").getD "http://localhost/"
        let owner := j.getString? "owner"
        let agent := j.getString? "agent"
        let now := match j.field? "now" with
          | some (.number s) => (s.toNat?).getD 0
          | _ => 0
        .ok { cfg := { baseIri, owner, agent }, now,
              rootAcl := j.getString? "rootAcl" }

/-! ## The handle table -/

/-- One open storage: its configuration and its state. -/
structure OpenStorage where
  cfg : Config
  mem : MemState

initialize lwsCounter : IO.Ref Nat ← IO.mkRef 0
initialize lwsTable : IO.Ref (Std.HashMap String OpenStorage) ← IO.mkRef ∅

def unknownLwsHandle (h : String) : String :=
  errJson s!"unknown LWS handle: {h}"

/-- A new storage holds only its root container, stamped with the opening
clock. Solid Protocol §4.1: "Servers MUST provide one or more storages"; one
handle is one storage. -/
def initialStorage (now : Nat) (rootAcl : Option String := none) : MemState :=
  { entries :=
      { path := rootPath, kind := .storageRoot,
        contentType := "text/turtle", body := "", mtime := now } ::
      (match rootAcl with
       | none => []
       | some body =>
           [{ path := aclPathOf rootPath, kind := .metadataResource,
              contentType := "text/turtle", body, mtime := now }])
  , clock := now + 1 }

def lwsOpen (configJson : String) : IO String := do
  match openConfigOfJson configJson with
  | .error e => pure (errJson e)
  | .ok oc =>
      let n ← lwsCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"lws{n}"
      lwsTable.modify (·.insert h
        { cfg := oc.cfg, mem := initialStorage oc.now oc.rootAcl })
      pure (okWith [("handle", .string h), ("root", .string rootPath)])

def lwsStep (h requestJson : String) : IO String := do
  match (← lwsTable.get)[h]? with
  | none => pure (unknownLwsHandle h)
  | some open_ =>
      match parseJson requestJson with
      | .error e => pure (errJson s!"request: {toString e}")
      | .ok j =>
          match requestOfJson j with
          | .error e => pure (errJson e)
          | .ok (r, now?, agent?) => do
              let mem := match now? with
                | some t => { open_.mem with clock := t }
                | none   => open_.mem
              let cfg := match agent? with
                | some a => { open_.cfg with agent := some a }
                | none   => open_.cfg
              let (resp, mem') := L4Factoidal.LWS.step MemStore cfg r mem
              lwsTable.modify (·.insert h { open_ with mem := mem' })
              pure (okWith [("response", jsonOfResponse resp)])

def lwsClose (h : String) : IO String := do
  let table ← lwsTable.get
  if table.contains h then
    lwsTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownLwsHandle h)

/-- The op names this module serves. -/
def lwsOpNames : List String := ["lwsOpen", "lwsStep", "lwsClose"]

end L4Wasm.Ops
