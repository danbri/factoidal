/-
Wasm.Ops.XmppSession — the XMPP SERVER as handles: open a server, open
one session per client connection on it, feed the session the bytes a
socket read, perform what it answers.

  xmppOpen(configJson)
    -> {"ok":true,"handle":"xmpp1","domain":"…","accounts":N}
  xmppSessionOpen(serverHandle, optionsJson)
    -> {"ok":true,"handle":"xmpps1"}
  xmppSessionFeed(sessionHandle, text)
    -> {"ok":true,"send":[…],"route":[{"to":bare,"text":…},…],
        "presence":[{"bare","full","available"},…],
        "rostersSaved":[bare,…],"close":bool,
        "stage":"…","bare":s|null,"full":s|null}
  xmppSessionDeliver(sessionHandle, text)
    -> {"ok":true,"delivered":bool,"send":[…]}
  xmppSessionClose(sessionHandle)
    -> {"ok":true,"send":[…]}
  xmppRosterGet(serverHandle, bareJid)
    -> {"ok":true,"encoded":"…","items":[{"jid","name","subscription","ask"},…]}
  xmppRosterSet(serverHandle, bareJid, encoded)
    -> {"ok":true}
  xmppClose(serverHandle)
    -> {"ok":true,"sessions":N}

This module is to `Harness/XmppServe.lean` what `Wasm/Ops/Lws.lean` is to
`npm/factoidal/lws/server.mjs`: the same protocol library behind a handle
table instead of behind a process. Every protocol decision is still
`L4Factoidal.XMPP.Server.step` (and `deliver`, `streamError`,
`Session.awaitingStreamOpen`, `Session.canDeliver`); every cut of the
byte stream is still `L4Factoidal.XMPP.Framing.nextUnit`. What the
native harness does with files — the roster of a bare JID, who is
available, the mailbox a stanza is routed to — is here held in the
server handle or handed back to the host:

  * `Out.saveRoster` updates the server handle's roster table, so a
    second session on the same server reads what the first wrote, as
    the harness reads the roster file fresh before every `step`.
  * `Out.presence` updates the server handle's presence table and is
    also reported, so a host that keeps its own view can.
  * `Out.route` is REPORTED, not performed: the host owns the sockets,
    so the host finds the session bound to that bare JID and calls
    `xmppSessionDeliver` on it, or holds the stanza until one binds.
    `xmppSessionDeliver` asks `Session.canDeliver` before anything else,
    which is the gate the harness learned to ask first (see the design
    record's "two defects").
  * `Out.send` and `Out.close` are reported as `send` and `close`.

What the host supplies and this module never invents: the stream id and
the SCRAM server nonce of each session (RFC 6120 section 4.7.3 and
RFC 5802 section 5.1 want them unpredictable; the module has no random
source), the account list, and the bytes. The one-salt-per-deployment
limitation of the harness is kept and stated: `saltB64` is a server
configuration value, defaulting to the harness's.

State lives HERE, in `Wasm/*`, in `IO.Ref`s, exactly as `Wasm/Ops/Lws.lean`
holds a storage; `L4Factoidal/XMPP/` stays pure. Reachable only through
`L4Wasm.callIO`.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Std.Data.HashMap
import Wasm.Ops.Support
import L4Factoidal.XMPP.Server

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.XMPP
open L4Factoidal.XMPP.Server (Session Env Out Config Account Roster RosterItem
  rosterDecode rosterEncode)

/-! ## Reading the JSON contract -/

private def jsonOfOptString (o : Option String) : Json :=
  o.elim .null .string

private def natField? (j : Json) (key : String) : Option Nat :=
  match j.field? key with
  | some (.number s) => s.toNat?
  | _ => none

/-- `user:password` lines, the accounts-file format of the harness
(`Harness.XmppServe.parseAccounts`), accepted here as `accountsText` so one
file serves both hosts. -/
private def accountsOfText (text : String) : List Account :=
  (text.splitOn "\n").filterMap (fun line =>
    let l := line.trim
    if l.isEmpty || l.startsWith "#" then none
    else match l.splitOn ":" with
      | u :: rest => if u.isEmpty then none else some ⟨u, String.intercalate ":" rest⟩
      | [] => none)

/-- `accounts`: an array of `{"username","password"}` objects. -/
private def accountsOfArray (items : List Json) : List Account :=
  items.filterMap (fun it =>
    match it.getString? "username", it.getString? "password" with
    | some u, some p => if u.isEmpty then none else some ⟨u, p⟩
    | _, _ => none)

/-- The server configuration: every per-session value (`streamId`,
`serverNonce`) is left empty here and filled by `xmppSessionOpen`. -/
structure XmppServerConfig where
  domain : String
  saltB64 : String
  iterationCount : Nat
  accounts : List Account
  tlsCarrier : Bool
  deriving Inhabited

def xmppServerConfigOfJson (text : String) : Except String XmppServerConfig :=
  match parseJson text with
  | .error e => .error s!"config: {toString e}"
  | .ok j =>
    let domain := (j.getString? "domain").getD "localhost"
    if domain.isEmpty then .error "config: \"domain\" must not be empty"
    else
      let fromArray := (j.getArray? "accounts").map accountsOfArray
      let fromText := (j.getString? "accountsText").map accountsOfText
      let accounts := (fromArray.getD []) ++ (fromText.getD [])
      -- RFC 5802 section 5.1 salt and RFC 7677 section 3 iteration count.
      -- The default salt is the one `Harness/XmppServe.lean` fixes per
      -- deployment, so a transcript recorded against the harness replays
      -- here byte for byte.
      let saltB64 := (j.getString? "saltB64").getD "W22ZaJ0SNY7soEsUEjb6gQ=="
      let iterationCount := (natField? j "iterationCount").getD 4096
      if iterationCount < 1 then .error "config: \"iterationCount\" must be at least 1"
      else
        .ok { domain, saltB64, iterationCount, accounts,
              tlsCarrier := (j.getBool? "tlsCarrier").getD false }

/-! ## The handle tables -/

/-- One open server: its configuration, and the two things the native
harness keeps as files — the roster of each bare JID and the full JIDs
currently available under each bare JID. -/
structure XmppOpenServer where
  cfg : XmppServerConfig
  rosters : Std.HashMap String Roster
  presence : Std.HashMap String (List String)

/-- One open client connection on a server. -/
structure XmppOpenSession where
  server : String
  session : Session
  /-- Bytes received and not yet cut into a complete unit. -/
  buffer : String
  /-- Top-level units processed, against `maxUnits`. -/
  units : Nat
  /-- See `Harness.XmppServe.Options.maxUnits`: exceeding it is
  RFC 6120 section 4.9.3.14 `policy-violation`, a stated refusal rather
  than an unbounded loop. -/
  maxUnits : Nat
  closed : Bool

initialize xmppServerCounter : IO.Ref Nat ← IO.mkRef 0
initialize xmppSessionCounter : IO.Ref Nat ← IO.mkRef 0
initialize xmppServers : IO.Ref (Std.HashMap String XmppOpenServer) ← IO.mkRef ∅
initialize xmppSessions : IO.Ref (Std.HashMap String XmppOpenSession) ← IO.mkRef ∅

def unknownXmppServer (h : String) : String :=
  errJson s!"unknown XMPP server handle: {h}"

def unknownXmppSession (h : String) : String :=
  errJson s!"unknown XMPP session handle: {h}"

/-! ## Performing `Out` actions

What the harness does to a file or a socket, this does to the server
handle or to the answer document. -/

/-- The host-facing result of one feed. -/
structure XmppCollected where
  send : List String := []
  route : List (String × String) := []
  presence : List (String × String × Bool) := []
  /-- Bare JIDs whose roster `Out.saveRoster` replaced during this feed, so
  a host that persists rosters knows which to fetch with `xmppRosterGet`. -/
  rostersSaved : List String := []
  close : Bool := false

private def perform (srv : XmppOpenServer) (c : XmppCollected) : Out → XmppOpenServer × XmppCollected
  | .send text => (srv, { c with send := c.send ++ [text] })
  | .route bare text => (srv, { c with route := c.route ++ [(bare, text)] })
  | .saveRoster bare encoded =>
      ({ srv with rosters := srv.rosters.insert bare (rosterDecode encoded) },
       { c with rostersSaved := if c.rostersSaved.contains bare then c.rostersSaved
                                else c.rostersSaved ++ [bare] })
  | .presence bare full available =>
      let others := (srv.presence.getD bare []).filter (· != full)
      let now := if available then full :: others else others
      ({ srv with presence := srv.presence.insert bare now },
       { c with presence := c.presence ++ [(bare, full, available)] })
  | .close => (srv, { c with close := true })

private def performAll (srv : XmppOpenServer) (c : XmppCollected) : List Out → XmppOpenServer × XmppCollected
  | [] => (srv, c)
  | o :: os =>
    let (srv', c') := perform srv c o
    performAll srv' c' os

/-- Process every complete unit in the buffer, as `Harness.XmppServe.drainBuffer`
does. `fuel` bounds the recursion: every unit consumes at least one
character, so the buffer's length is always enough. The roster handed to
`step` is read from the server table fresh for every unit, so a change
another session made is seen, as the harness reads the file fresh. -/
private def drain (srv : XmppOpenServer) (os : XmppOpenSession) (c : XmppCollected) :
    Nat → XmppOpenServer × XmppOpenSession × XmppCollected
  | 0 => (srv, os, c)
  | fuel + 1 =>
    if os.closed then (srv, os, c)
    else
      match Framing.nextUnit (!os.session.awaitingStreamOpen) os.buffer with
      | none => (srv, os, c)
      | some (unit, rest) =>
        if os.units ≥ os.maxUnits then
          let (srv', c') := performAll srv c
            (Server.streamError "policy-violation" "too many stream units")
          (srv', { os with buffer := rest, closed := true }, { c' with close := true })
        else
          let roster := match os.session.bareJid with
            | some b => srv.rosters.getD b []
            | none => []
          let (s', _env', outs) := Server.step os.session ⟨roster⟩ unit
          let (srv', c') := performAll srv c outs
          let closed := c'.close || s'.stage == .closed
          drain srv'
            { os with session := s', buffer := rest, units := os.units + 1, closed }
            c' fuel

private def stageName : Server.Stage → String
  | .initial => "initial"
  | .awaitingAuth => "awaitingAuth"
  | .awaitingScramResponse .. => "awaitingScramResponse"
  | .authenticated _ => "authenticated"
  | .awaitingBind _ => "awaitingBind"
  | .bound .. => "bound"
  | .closed => "closed"

private def jsonOfCollected (os : XmppOpenSession) (c : XmppCollected) : List (String × Json) :=
  [ ("send", .array (c.send.map .string))
  , ("route", .array (c.route.map (fun (to, text) =>
      .object [("to", .string to), ("text", .string text)])))
  , ("presence", .array (c.presence.map (fun (bare, full, available) =>
      .object [("bare", .string bare), ("full", .string full), ("available", .bool available)])))
  , ("rostersSaved", .array (c.rostersSaved.map .string))
  , ("close", .bool c.close)
  , ("stage", .string (stageName os.session.stage))
  , ("bare", jsonOfOptString os.session.bareJid)
  , ("full", jsonOfOptString os.session.fullJid) ]

/-! ## The ops -/

def xmppOpen (configJson : String) : IO String := do
  match xmppServerConfigOfJson (if configJson.trim.isEmpty then "{}" else configJson) with
  | .error e => pure (errJson e)
  | .ok cfg =>
      let n ← xmppServerCounter.modifyGet fun n => (n + 1, n + 1)
      let h := s!"xmpp{n}"
      xmppServers.modify (·.insert h { cfg, rosters := ∅, presence := ∅ })
      pure (okWith [ ("handle", .string h)
                   , ("domain", .string cfg.domain)
                   , ("accounts", .number (toString cfg.accounts.length)) ])

def xmppClose (h : String) : IO String := do
  let servers ← xmppServers.get
  if servers.contains h then
    xmppServers.set (servers.erase h)
    -- Every session of that server goes with it.
    let sessions ← xmppSessions.get
    let mine := sessions.fold (fun acc k v => if v.server == h then k :: acc else acc) []
    xmppSessions.set (mine.foldl (fun t k => t.erase k) sessions)
    pure (okWith [("sessions", .number (toString mine.length))])
  else
    pure (unknownXmppServer h)

/-- `xmppSessionOpen(serverHandle, {"streamId","nonce","tlsCarrier"?,"maxUnits"?})`.
`streamId` and `nonce` are required: they must be unpredictable and this
module has no random source. -/
def xmppSessionOpen (server optionsJson : String) : IO String := do
  match (← xmppServers.get)[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    match parseJson (if optionsJson.trim.isEmpty then "{}" else optionsJson) with
    | .error e => pure (errJson s!"options: {toString e}")
    | .ok j =>
      match j.getString? "streamId", j.getString? "nonce" with
      | none, _ => pure (errJson "xmppSessionOpen: \"streamId\" is required (RFC 6120 section 4.7.3: the host supplies an unpredictable value)")
      | _, none => pure (errJson "xmppSessionOpen: \"nonce\" is required (RFC 5802 section 5.1: the host supplies an unpredictable value)")
      | some streamId, some nonce =>
        if streamId.isEmpty || nonce.isEmpty then
          pure (errJson "xmppSessionOpen: \"streamId\" and \"nonce\" must not be empty")
        else
          let cfg : Config :=
            { domain := srv.cfg.domain
              streamId
              serverNonce := nonce
              saltB64 := srv.cfg.saltB64
              iterationCount := srv.cfg.iterationCount
              accounts := srv.cfg.accounts
              tlsCarrier := (j.getBool? "tlsCarrier").getD srv.cfg.tlsCarrier }
          let n ← xmppSessionCounter.modifyGet fun n => (n + 1, n + 1)
          let h := s!"xmpps{n}"
          xmppSessions.modify (·.insert h
            { server, session := Session.init cfg, buffer := "", units := 0
              maxUnits := (natField? j "maxUnits").getD 1000000, closed := false })
          pure (okWith [("handle", .string h)])

/-- `xmppSessionFeed(sessionHandle, text)`: the bytes a socket read, as
UTF-8 text. An incomplete unit stays in the buffer until the rest
arrives. -/
def xmppSessionFeed (h text : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    match (← xmppServers.get)[os.server]? with
    | none => pure (unknownXmppServer os.server)
    | some srv =>
      let os := { os with buffer := os.buffer ++ text }
      let (srv', os', c) := drain srv os {} (os.buffer.length + 1)
      xmppServers.modify (·.insert os.server srv')
      xmppSessions.modify (·.insert h os')
      pure (okWith (jsonOfCollected os' c))

/-- `xmppSessionDeliver(sessionHandle, text)`: a stanza another session
routed to this one. Refused — `delivered:false`, nothing lost — unless
the session is bound (RFC 6121 section 8.5.3), so the host holds it
rather than this module destroying it. -/
def xmppSessionDeliver (h text : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    if os.closed || !os.session.canDeliver then
      pure (okWith [("delivered", .bool false), ("send", .array [])])
    else
      let sends := (Server.deliver os.session text).filterMap (fun o =>
        match o with | .send t => some t | _ => none)
      pure (okWith [("delivered", .bool true), ("send", .array (sends.map .string))])

/-- `xmppSessionClose(sessionHandle)`: the socket reached end of input or
is being closed by the host. A half-closed stream is answered the way
RFC 6120 section 4.4 asks, then the handle is released. The presence
table is NOT touched: an available full JID stays available until an
`unavailable` presence is seen, as in the harness. -/
def xmppSessionClose (h : String) : IO String := do
  match (← xmppSessions.get)[h]? with
  | none => pure (unknownXmppSession h)
  | some os =>
    let closing : List String :=
      if os.closed || os.session.stage == .closed then [] else ["</stream:stream>"]
    xmppSessions.modify (·.erase h)
    pure (okWith [("send", .array (closing.map .string))])

private def jsonOfRosterItem (i : RosterItem) : Json :=
  .object [ ("jid", .string i.jid), ("name", .string i.name)
          , ("subscription", .string i.subscription), ("ask", .bool i.ask) ]

/-- `xmppRosterGet(serverHandle, bareJid)`: the roster as the server
encodes it on disk (`rosterEncode`) and as items. A host that persists
rosters stores `encoded` and hands it back through `xmppRosterSet`;
it never has to read the format. -/
def xmppRosterGet (server bare : String) : IO String := do
  match (← xmppServers.get)[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    let r := srv.rosters.getD bare []
    pure (okWith [ ("encoded", .string (rosterEncode r))
                 , ("items", .array (r.map jsonOfRosterItem)) ])

/-- `xmppRosterSet(serverHandle, bareJid, encoded)`: load a roster the
host persisted. The bytes are the server's own format; lines it does not
recognise are dropped by `rosterDecode`, as the harness drops them. -/
def xmppRosterSet (server bare encoded : String) : IO String := do
  let servers ← xmppServers.get
  match servers[server]? with
  | none => pure (unknownXmppServer server)
  | some srv =>
    xmppServers.set (servers.insert server
      { srv with rosters := srv.rosters.insert bare (rosterDecode encoded) })
    pure (okWith [])

/-- The op names this module serves, through `callIO` only. -/
def xmppSessionOpNames : List String :=
  [ "xmppOpen", "xmppClose"
  , "xmppSessionOpen", "xmppSessionFeed", "xmppSessionDeliver", "xmppSessionClose"
  , "xmppRosterGet", "xmppRosterSet" ]

end L4Wasm.Ops
