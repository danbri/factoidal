/-
Wasm.Ops.Solid — Solid Protocol handles for the SERVER, and two stateless
operations for the CLIENT.

  solidOpen(configJson)
    -> {"ok":true,"handle":"solid1","root":"/","storage":"<baseIri>"}
  solidStep(handle, requestJson)
    -> {"ok":true,"response":{"status":N,"headers":[[n,v],…],"body":"…"}}
  solidClose(handle)
    -> {"ok":true}

  solidClientRequest(kind, argsJson)
    -> {"ok":true,"request":{"method":"…","target":"…","headers":[…],"body":"…"}}
  solidClientResponse(kind, responseJson)
    -> {"ok":true,"interpretation":{…}}

The JSON contract is `docs/lws-solid-conformance.md` § "wasm ABI"; the Node
hosts under `npm/factoidal/solid/` code against that section.

Server and client stay distinct here as they do in `L4Factoidal/Solid/`: the
server operations hold state in a handle table, the client operations hold
none, because a client's state is its own host's.

`solidStep` calls `L4Factoidal.Solid.Server.step`, which refines
`L4Factoidal.LWS.Operations.step`. The request and response documents are
the same records `Wasm/Ops/Lws.lean` reads and writes, so a host can drive
either engine through one code path.
-/
import Std.Data.HashMap
import Wasm.Ops.Lws
import L4Factoidal.Solid.Server.Methods
import L4Factoidal.Solid.Client.Requests
import L4Factoidal.Solid.Client.Responses
import L4Factoidal.Solid.Client.Profile

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF
open L4Factoidal.LWS
open L4Factoidal.Solid.Server
open L4Factoidal.Solid.Client
open L4Factoidal.HTTP (Request Response)

/-! ## The server handle table -/

structure OpenSolid where
  cfg : ServerConfig
  mem : MemState

initialize solidCounter : IO.Ref Nat ← IO.mkRef 0
initialize solidTable : IO.Ref (Std.HashMap String OpenSolid) ← IO.mkRef ∅

def unknownSolidHandle (h : String) : String :=
  errJson s!"unknown Solid handle: {h}"

/-- `enforceWac` is read from the configuration, defaulting to false — the
first slice serves public resources (see `L4Factoidal/Solid/README.md`). -/
def serverConfigOfJson (text : String) :
    Except String (ServerConfig × Nat × Option String) :=
  match openConfigOfJson text with
  | .error e => .error e
  | .ok oc =>
      let enforce :=
        if text.trim == "" then false
        else match parseJson text with
          | .ok j => (j.getBool? "enforceWac").getD false
          | .error _ => false
      .ok ({ lws := oc.cfg, enforceWac := enforce }, oc.now, oc.rootAcl)

def solidOpen (configJson : String) : IO String := do
  match serverConfigOfJson configJson with
  | .error e => pure (errJson e)
  | .ok (cfg, now, rootAcl) =>
      let n ← solidCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"solid{n}"
      solidTable.modify (·.insert h { cfg, mem := initialStorage now rootAcl })
      pure (okWith [ ("handle", .string h)
                   , ("root", .string rootPath)
                   , ("storage", .string cfg.lws.baseIri) ])

def solidStep (h requestJson : String) : IO String := do
  match (← solidTable.get)[h]? with
  | none => pure (unknownSolidHandle h)
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
                | some a => { open_.cfg with
                              lws := { open_.cfg.lws with agent := some a } }
                | none   => open_.cfg
              let (resp, mem') := L4Factoidal.Solid.Server.step MemStore cfg r mem
              solidTable.modify (·.insert h { open_ with mem := mem' })
              pure (okWith [("response", jsonOfResponse resp)])

def solidClose (h : String) : IO String := do
  let table ← solidTable.get
  if table.contains h then
    solidTable.set (table.erase h)
    pure (okWith [])
  else
    pure (unknownSolidHandle h)

/-! ## The client operations

Both are pure functions of their arguments; they are declared `IO` only so
they sit beside the handle operations in one dispatch table. -/

/-- `solidClientRequest(kind, argsJson)` — build a conformant request. -/
def solidClientRequest (kind argsJson : String) : String :=
  match RequestKind.ofString? kind with
  | none => errJson s!"solidClientRequest: unknown kind '{kind}' (read | create | replace | patch | delete | discoverStorage | readProfile)"
  | some k =>
      match parseJson argsJson with
      | .error e => errJson s!"args: {toString e}"
      | .ok j =>
          match j.getString? "target" with
          | none => errJson "args: member \"target\" is required"
          | some target =>
              let a : RequestArgs :=
                { target
                , body := (j.getString? "body").getD ""
                , contentType := (j.getString? "contentType").getD "text/turtle"
                , slug := j.getString? "slug"
                , ifNoneMatchStar := (j.getBool? "ifNoneMatchStar").getD false }
              let r := buildRequest k a
              okWith [("request", .object
                [ ("method", .string r.method)
                , ("target", .string r.path)
                , ("headers", .array (r.headers.map (fun (n, v) =>
                    Json.array [.string n, .string v])))
                , ("body", .string r.body) ])]

private def stringsJson (xs : List String) : Json := .array (xs.map Json.string)

private def optJson : Option String → Json
  | some s => .string s
  | none   => .null

/-- `solidClientResponse(kind, responseJson)` — interpret a response.

The response document is the one `solidStep` answers, with two extra members
the `profile` kind needs: `webId` and `baseIri`. -/
def solidClientResponse (kind responseJson : String) : String :=
  match parseJson responseJson with
  | .error e => errJson s!"response: {toString e}"
  | .ok j =>
      let headers : List (String × String) :=
        match j.getArray? "headers" with
        | none => []
        | some items => items.filterMap (fun it =>
            match it with
            | .array [.string n, .string v] => some (n.toLower, v)
            | _ => none)
      let status := match j.field? "status" with
        | some (.number s) => (s.toNat?).getD 0
        | _ => 0
      let body := (j.getString? "body").getD ""
      let resp : Response := { status, headers, body }
      match kind with
      | "storage" =>
          let f := resourceFacts resp
          okWith [("interpretation", .object
            [ ("isStorage", .bool f.isStorage)
            , ("storageDescription", optJson f.storageDescription)
            , ("owner", optJson f.owner)
            , ("lastModified", optJson f.lastModified)
            , ("allow", stringsJson f.allow) ])]
      | "auxiliaries" =>
          let f := resourceFacts resp
          okWith [("interpretation", .object
            [ ("acl", optJson f.acl)
            , ("describedby", optJson f.describedBy)
            , ("inbox", optJson f.inbox) ])]
      | "containment" =>
          let g := aclGraphOf body
          let members := g.filterMap (fun t =>
            if t.p == ldpContains then
              match t.o with | .iri i => some i.val | _ => none
            else none)
          okWith [("interpretation", .object
            [ ("contains", stringsJson members)
            , ("count", .number (toString members.length)) ])]
      | "wacAllow" =>
          okWith [("interpretation", .object
            ((wacAllowOf resp).map (fun (g, ms) => (g, stringsJson ms))))]
      | "profile" =>
          match j.getString? "webId" with
          | none => errJson "response: the profile kind needs a \"webId\" member"
          | some webId =>
              let baseIri := (j.getString? "baseIri").getD webId
              let p := readProfile webId baseIri body
              okWith [("interpretation", .object
                [ ("webId", .string p.webId)
                , ("storages", stringsJson p.storages)
                , ("inbox", optJson p.inbox)
                , ("oidcIssuers", stringsJson p.oidcIssuers)
                , ("names", stringsJson p.names) ])]
      | "created" =>
          okWith [("interpretation", .object
            [ ("status", .number (toString resp.status))
            , ("location", optJson (createdLocation? resp))
            , ("mayRetryWithCredentials", .bool (mayRetryWithCredentials resp)) ])]
      | _ => errJson s!"solidClientResponse: unknown kind '{kind}' (storage | containment | auxiliaries | profile | wacAllow | created)"

/-- The op names this module serves. -/
def solidOpNames : List String :=
  ["solidOpen", "solidStep", "solidClose", "solidClientRequest", "solidClientResponse"]

end L4Wasm.Ops
