/-
L4Factoidal.XMPP.Server — every protocol decision an XMPP server makes
for ONE client connection, as a total function.

  step : Session → Env → Framing.Unit → Session × Env × List Out

The host that carries the bytes (see `Harness/XmppServe.lean` and
`deploy/fly/xmpp/`) does four things and decides nothing: it reads bytes
into a buffer, asks `Framing.nextUnit` where the next unit ends, calls
`step`, and performs the `Out` actions it gets back — write these bytes
to the socket, append these bytes to that file, replace that file's
contents, close. Which stanza goes where, what a stream error is, when
authentication succeeded, what a roster looks like on disk: all of it is
here.

Specifications implemented, by section:

  RFC 6120 section 4.2   stream open, `<stream:features>`
  RFC 6120 section 4.4   `</stream:stream>` close
  RFC 6120 section 4.9   stream errors
  RFC 6120 section 6     SASL, with the mechanism list from `Core`
  RFC 6120 section 7     resource binding
  RFC 6120 section 8     stanza addressing and the three stanza kinds
  RFC 6120 section 8.4   `service-unavailable` for unhandled IQ
  RFC 6121 section 2     the roster: get, set, push, remove
  RFC 6121 section 3     presence subscription
  RFC 6121 section 4     presence broadcast to the roster
  RFC 6121 section 8     message delivery
  RFC 7677               SASL SCRAM-SHA-256 (via `XMPP.Scram`)
  XEP-0368               direct TLS: the carrier terminates it, so this
                         module never negotiates STARTTLS — see
                         `tlsCarrier` below.

NOT implemented, stated rather than silently skipped:
  * STARTTLS (RFC 6120 section 5). Confidentiality is the carrier's, per
    XEP-0368. On the plaintext test listener there is none, and
    `featuresFor` is still asked for the post-TLS stage: the code says so
    at `initialFeatures` rather than pretending otherwise.
  * SCRAM channel binding (`p=tls-server-end-point`). The Lean process
    cannot see the TLS layer, so only `n`/`y` gs2 headers are accepted.
  * SASL mechanisms other than PLAIN and SCRAM-SHA-256. SCRAM-SHA-1 is
    NOT offered: `L4Factoidal/Crypto/` has SHA-1 only as a pure-Lean
    codec for the SPARQL `SHA1()` builtin, explicitly forbidden by its
    own module header from being used "for integrity or authentication".
    RFC 7677 is the current mechanism; offering it and PLAIN is the
    honest set given what is vendored.
  * Server-to-server (RFC 6120 section 4.9.3.4 dialback, and federation
    generally). One process, one client connection.
  * GC3 rooms. `L4Factoidal/XMPP/Gc3.lean` is a scope-only stub because
    the XSF specification is unfinished; implementing rooms here would be
    inventing a wire format, not implementing one.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XMPP.Core
import L4Factoidal.XMPP.Framing
import L4Factoidal.XMPP.Scram

namespace L4Factoidal.XMPP.Server

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP (Jid)
open L4Factoidal.XMPP.Core (Stanza StanzaKind ConnStage featuresFor findAttr)

/-! ## Namespaces -/

def nsStreams : String := "http://etherx.jabber.org/streams"
def nsClient : String := "jabber:client"
def nsSasl : String := "urn:ietf:params:xml:ns:xmpp-sasl"
def nsBind : String := "urn:ietf:params:xml:ns:xmpp-bind"
def nsSession : String := "urn:ietf:params:xml:ns:xmpp-session"
def nsStanzas : String := "urn:ietf:params:xml:ns:xmpp-stanzas"
def nsStreamErr : String := "urn:ietf:params:xml:ns:xmpp-streams"
def nsRoster : String := "jabber:iq:roster"
def nsDiscoInfo : String := "http://jabber.org/protocol/disco#info"

/-! ## The roster (RFC 6121 section 2)

An item's on-disk form is decided here, not by the host: one line per
item, four tab-separated fields, so the host's whole job is
`IO.FS.writeFile` of a string this module produced. -/

structure RosterItem where
  jid : String
  name : String
  /-- RFC 6121 section 2.1.2.5: `none`, `to`, `from` or `both`. -/
  subscription : String
  /-- RFC 6121 section 2.1.2.2: a pending outbound subscription request. -/
  ask : Bool
  deriving Repr, DecidableEq, Inhabited

namespace RosterItem

def encode (i : RosterItem) : String :=
  s!"{i.jid}\t{i.name}\t{i.subscription}\t{if i.ask then "1" else "0"}"

def decode (line : String) : Option RosterItem :=
  match line.splitOn "\t" with
  | [j, n, sub, a] => if j.isEmpty then none else some ⟨j, n, sub, a == "1"⟩
  | _ => none

/-- The `<item/>` a roster result or push carries. -/
def toXml (i : RosterItem) : Node :=
  let attrs :=
    [Attribute.mk "jid" i.jid] ++
    (if i.name.isEmpty then [] else [Attribute.mk "name" i.name]) ++
    [Attribute.mk "subscription" i.subscription] ++
    (if i.ask then [Attribute.mk "ask" "subscribe"] else [])
  .element "item" attrs []

end RosterItem

abbrev Roster := List RosterItem

def rosterEncode (r : Roster) : String :=
  String.intercalate "\n" (r.map RosterItem.encode)

def rosterDecode (s : String) : Roster :=
  (s.splitOn "\n").filterMap (fun l =>
    if l.trim.isEmpty then none else RosterItem.decode l)

def rosterFind (r : Roster) (jid : String) : Option RosterItem :=
  r.find? (fun i => i.jid == jid)

/-- Insert or replace by JID, keeping the existing order so a roster does
not reshuffle on every edit. -/
def rosterPut (r : Roster) (item : RosterItem) : Roster :=
  if (rosterFind r item.jid).isSome then
    r.map (fun i => if i.jid == item.jid then item else i)
  else r ++ [item]

def rosterRemove (r : Roster) (jid : String) : Roster :=
  r.filter (fun i => i.jid != jid)

/-- RFC 6121 section 4.4.2: presence is broadcast to contacts whose
subscription state means they are allowed to see it — `from` or `both`. -/
def presenceTargets (r : Roster) : List String :=
  (r.filter (fun i => i.subscription == "from" || i.subscription == "both")).map (·.jid)

/-! ## Accounts and configuration -/

structure Account where
  username : String
  password : String
  deriving Repr, Inhabited

structure Config where
  /-- The domain this server is authoritative for (RFC 6120 section 4.3.2's
  `to` on the initial stream). -/
  domain : String
  /-- Supplied by the host from a random source. RFC 6120 section 4.7.3
  requires the stream `id` to be unpredictable. -/
  streamId : String
  /-- Supplied by the host from a random source; the server half of the
  SCRAM nonce (RFC 5802 section 5.1). -/
  serverNonce : String
  /-- The SCRAM salt, base64, and its iteration count (RFC 7677 section 3
  recommends at least 4096). -/
  saltB64 : String
  iterationCount : Nat
  accounts : List Account
  /-- True when the carrier already terminated TLS (XEP-0368 direct TLS on
  port 5223). False on the plaintext test listener. It changes no wire
  behaviour today — there is no STARTTLS to offer or withhold — and is
  carried so a later STARTTLS implementation has one place to branch, and
  so the value is visible rather than assumed. -/
  tlsCarrier : Bool
  deriving Inhabited

def Config.accountOf (c : Config) (user : String) : Option Account :=
  c.accounts.find? (fun a => a.username == user)

/-! ## What the host must do -/

inductive Out where
  /-- Write these bytes to this connection's socket. -/
  | send (text : String)
  /-- Append these bytes to the mailbox of that bare JID, as one framed
  stanza. The host chooses the file name; the bytes and the destination
  are decided here. -/
  | route (bareJid : String) (text : String)
  /-- Replace that bare JID's roster file with this exact text. -/
  | saveRoster (bareJid : String) (encoded : String)
  /-- Record this full JID as available or not, so other connections can
  see it. -/
  | presence (bareJid : String) (fullJid : String) (available : Bool)
  /-- Close the connection after flushing. -/
  | close
  deriving Repr, DecidableEq, Inhabited

/-! ## Session state -/

/-- What the server is waiting for. The constructors are the RFC 6120
section 4.3 negotiation sequence in order. -/
inductive Stage where
  /-- No stream open seen yet. -/
  | initial
  /-- Stream open seen, SASL features sent, waiting for `<auth/>`. -/
  | awaitingAuth
  /-- SCRAM client-first seen and challenged; waiting for `<response/>`.
  Carries the state RFC 5802 section 3 needs to finish: the account, the
  combined nonce, and the two AuthMessage parts already exchanged. -/
  | awaitingScramResponse (user : String) (nonce : String)
      (clientFirstBare : String) (serverFirst : String)
  /-- SASL succeeded; RFC 6120 section 6.4.6 requires a NEW stream. -/
  | authenticated (user : String)
  /-- The restarted stream is open and bind is offered. -/
  | awaitingBind (user : String)
  /-- Bound (RFC 6120 section 7); stanzas flow. -/
  | bound (user : String) (resource : String)
  /-- The stream is finished; nothing further is processed. -/
  | closed
  deriving Repr, DecidableEq, Inhabited

structure Session where
  cfg : Config
  stage : Stage
  deriving Inhabited

def Session.user (s : Session) : Option String :=
  match s.stage with
  | .awaitingScramResponse u _ _ _ => some u
  | .authenticated u => some u
  | .awaitingBind u => some u
  | .bound u _ => some u
  | _ => none

def Session.bareJid (s : Session) : Option String :=
  s.user.map (fun u => u ++ "@" ++ s.cfg.domain)

def Session.fullJid (s : Session) : Option String :=
  match s.stage, s.bareJid with
  | .bound _ r, some b => some (b ++ "/" ++ r)
  | _, _ => none

/-- What the host read from disk before calling `step`, and hands back
after. Only the authenticated user's roster is ever needed. -/
structure Env where
  roster : Roster
  deriving Inhabited

def Session.init (cfg : Config) : Session := { cfg := cfg, stage := .initial }

/-- Is the next unit expected to be a `<stream:stream>` opening tag? True
twice per connection: at the start (RFC 6120 section 4.2) and again right
after SASL succeeds (section 6.4.6, the stream restart). The framer needs
this, because a `<stream:stream>` that never closes can only be cut as a
unit when it is expected; at any other point the same text is an
ill-formed child element. Deciding it here rather than in the host keeps
the host free of protocol state. -/
def Session.awaitingStreamOpen (s : Session) : Bool :=
  match s.stage with
  | .initial => true
  | .authenticated _ => true
  | _ => false

/-! ## Rendering -/

def render (n : Node) : String := Wire.render n

/-- RFC 6120 section 4.2: the server's response stream header. The `from`
is the server's domain, and `id` is the unpredictable stream id. -/
def streamOpenText (cfg : Config) : String :=
  "<?xml version='1.0'?>" ++
  s!"<stream:stream xmlns='{nsClient}' xmlns:stream='{nsStreams}'" ++
  s!" from='{cfg.domain}' id='{cfg.streamId}' version='1.0' xml:lang='en'>"

/-- RFC 6120 section 6.4.1: the mechanisms this build actually
implements. Nothing else is advertised — a mechanism in this list that
`handleAuth` cannot finish would be a lie the client pays for. -/
def mechanisms : List String := ["SCRAM-SHA-256", "PLAIN"]

/-- The features offered on the FIRST stream. `Core.featuresFor .postTls`
is the source: this build has no STARTTLS to offer (the carrier holds
TLS, XEP-0368), so the stage that names "TLS settled, authenticate now"
is the correct one, and the RFC 6120 ordering theorems in `Core` apply
unchanged. -/
def initialFeatures (_cfg : Config) : String :=
  render (Core.StreamFeatures.toXml (featuresFor .postTls mechanisms))

/-- The features offered on the RESTARTED stream (RFC 6120 section 7.4):
resource binding, plus the legacy session element clients still ask for. -/
def postAuthFeatures : String :=
  render (Core.StreamFeatures.toXml (featuresFor .authenticated []))

/-- RFC 6120 section 4.9: a stream error closes the stream. -/
def streamError (condition : String) (text : String) : List Out :=
  let body : List Node :=
    [.element condition [⟨"xmlns", nsStreamErr⟩] []] ++
    (if text.isEmpty then []
     else [.element "text" [⟨"xmlns", nsStreamErr⟩, ⟨"xml:lang", "en"⟩] [.text text]])
  [ .send (render (.element "stream:error" [] body)), .send "</stream:stream>", .close ]

/-- RFC 6120 section 8.3: a stanza error reply, `type='error'`, keeping
the original id and swapping the addresses. -/
def stanzaError (kind : StanzaKind) (id : Option String) (to : Option String)
    (from_ : Option String) (errType : String) (condition : String) : String :=
  let attrs :=
    (to.map (Attribute.mk "to")).toList ++
    (from_.map (Attribute.mk "from")).toList ++
    [Attribute.mk "type" "error"] ++
    (id.map (Attribute.mk "id")).toList
  render (.element kind.tagName attrs
    [.element "error" [⟨"type", errType⟩] [.element condition [⟨"xmlns", nsStanzas⟩] []]])

/-! ## XML helpers over a stanza payload -/

def elemName : Node → Option String
  | .element t _ _ => some t
  | _ => none

def elemAttr (n : Node) (name : String) : Option String :=
  match n with
  | .element _ attrs _ => findAttr attrs name
  | _ => none

def elemChildren : Node → List Node
  | .element _ _ cs => cs
  | _ => []

/-- The first child element whose `xmlns` is `ns` (and, when `tag` is
given, whose name matches). Namespace handling is by the literal `xmlns`
attribute: XMPP payload elements always carry it explicitly. -/
def childByNs (payload : List Node) (ns : String) (tag : Option String) : Option Node :=
  payload.find? (fun n =>
    elemAttr n "xmlns" == some ns &&
    (match tag with | none => true | some t => elemName n == some t))

/-- The concatenated text directly inside an element. -/
def textOf (n : Node) : String :=
  String.join ((elemChildren n).filterMap (fun c =>
    match c with | .text t => some t | _ => none))

/-! ## SASL -/

/-- Split a decoded SASL PLAIN payload on its NUL separators
(RFC 4616 section 2: `authzid NUL authcid NUL passwd`). -/
def splitNul (b : ByteArray) : List String :=
  let parts := b.toList.foldl
    (fun (acc : List (List UInt8)) (c : UInt8) =>
      if c == 0 then [] :: acc
      else match acc with
        | [] => [[c]]
        | h :: t => (c :: h) :: t)
    [[]]
  (parts.map (fun bs => String.fromUTF8! (ByteArray.mk bs.reverse.toArray))).reverse

def saslSuccess (payload : String) : String :=
  if payload.isEmpty then s!"<success xmlns='{nsSasl}'/>"
  else s!"<success xmlns='{nsSasl}'>{payload}</success>"

/-- RFC 6120 section 6.5: a SASL failure element. The condition is
`not-authorized` for a bad password and `invalid-mechanism` /
`malformed-request` for the two structural refusals. -/
def saslFailure (condition : String) : String :=
  s!"<failure xmlns='{nsSasl}'><{condition}/></failure>"

def saslChallenge (payload : String) : String :=
  s!"<challenge xmlns='{nsSasl}'>{payload}</challenge>"

/-- Verify a PLAIN payload against the configured accounts. Returns the
authenticated username. RFC 4616: an authzid different from the authcid
is refused rather than ignored — ignoring it would let a client believe
it had authorised as somebody else. -/
def checkPlain (cfg : Config) (decoded : List String) : Option String :=
  match decoded with
  | [authzid, authcid, password] =>
    if !authzid.isEmpty && authzid != authcid && authzid != authcid ++ "@" ++ cfg.domain then none
    else match cfg.accountOf authcid with
      | some a => if a.password == password then some authcid else none
      | none => none
  | _ => none

/-! ## The step function -/

private def bindResult (id : Option String) (fullJid : String) : String :=
  render (.element "iq"
    ([Attribute.mk "type" "result"] ++ (id.map (Attribute.mk "id")).toList)
    [.element "bind" [⟨"xmlns", nsBind⟩] [.element "jid" [] [.text fullJid]]])

private def iqResult (id : Option String) (to : Option String) (children : List Node) : String :=
  render (.element "iq"
    ((to.map (Attribute.mk "to")).toList ++ [Attribute.mk "type" "result"] ++
      (id.map (Attribute.mk "id")).toList)
    children)

/-- The bare form of a JID string. -/
def bareOf (s : String) : String :=
  match (Jid.parse s) with
  | some j => Jid.render { j with resourcepart := none }
  | none => s

/-- Handle `<auth/>` — the SASL first step (RFC 6120 section 6.4.2). -/
def handleAuth (s : Session) (n : Node) : Session × List Out :=
  let mech := (elemAttr n "mechanism").getD ""
  let payload := textOf n
  if mech == "PLAIN" then
    match Scram.b64Decode payload with
    | none => (s, [.send (saslFailure "incorrect-encoding")])
    | some bytes =>
      match checkPlain s.cfg (splitNul bytes) with
      | some user => ({ s with stage := .authenticated user }, [.send (saslSuccess "")])
      | none => (s, [.send (saslFailure "not-authorized")])
  else if mech == "SCRAM-SHA-256" then
    match Scram.b64Decode payload with
    | none => (s, [.send (saslFailure "incorrect-encoding")])
    | some bytes =>
      let text := String.fromUTF8! bytes
      match Sasl.ClientFirstMessage.parse text with
      | none => (s, [.send (saslFailure "malformed-request")])
      | some cf =>
        match s.cfg.accountOf cf.username with
        | none => (s, [.send (saslFailure "not-authorized")])
        | some acct =>
          match Scram.credentialsOfPassword acct.password s.cfg.saltB64 s.cfg.iterationCount with
          | none => (s, [.send (saslFailure "temporary-auth-failure")])
          | some cred =>
            let nonce := cf.clientNonce ++ s.cfg.serverNonce
            let serverFirst := Scram.serverFirstOf cred nonce
            ({ s with stage := .awaitingScramResponse cf.username nonce
                        (Scram.clientFirstBare cf) serverFirst },
             [.send (saslChallenge (Scram.b64Encode serverFirst.toUTF8))])
  else (s, [.send (saslFailure "invalid-mechanism")])

/-- Handle `<response/>` — the SCRAM second step (RFC 5802 section 3). -/
def handleScramResponse (s : Session) (user nonce cfb sf : String) (n : Node) :
    Session × List Out :=
  match Scram.b64Decode (textOf n) with
  | none => (s, [.send (saslFailure "incorrect-encoding")])
  | some bytes =>
    match Sasl.ClientFinalMessage.parse (String.fromUTF8! bytes) with
    | none => (s, [.send (saslFailure "malformed-request")])
    | some cfin =>
      -- RFC 5802 section 5.1: the client MUST echo the combined nonce. A
      -- server that skips this check accepts a replayed client-first.
      if cfin.nonce != nonce then (s, [.send (saslFailure "not-authorized")])
      else
        match s.cfg.accountOf user with
        | none => (s, [.send (saslFailure "not-authorized")])
        | some acct =>
          match Scram.credentialsOfPassword acct.password s.cfg.saltB64 s.cfg.iterationCount with
          | none => (s, [.send (saslFailure "temporary-auth-failure")])
          | some cred =>
            let auth := Scram.authMessage cfb sf (Scram.clientFinalNoProof cfin)
            match Scram.verifyClientProof cred auth cfin.proof with
            | none => (s, [.send (saslFailure "not-authorized")])
            | some serverSig =>
              ({ s with stage := .authenticated user },
               [.send (saslSuccess (Scram.b64Encode ("v=" ++ serverSig).toUTF8))])

/-- Handle an IQ once bound. -/
def handleIq (s : Session) (env : Env) (st : Stanza) (raw : String) (bare full : String) :
    Env × List Out :=
  let ty := st.type.getD "get"
  let target := st.to.map Jid.render
  -- Addressed to another entity: route it there (RFC 6120 section 8.1.1).
  match target with
  | some t =>
    if bareOf t != bare && bareOf t != s.cfg.domain then
      (env, [.route (bareOf t) (Wire.render (Core.Stanza.toXml
        { st with from_ := Jid.parse full }))])
    else handleLocal ty
  | none => handleLocal ty
where
  handleLocal (ty : String) : Env × List Out :=
    let roster := childByNs st.payload nsRoster (some "query")
    let session := childByNs st.payload nsSession (some "session")
    let disco := childByNs st.payload nsDiscoInfo (some "query")
    match roster with
    | some q =>
      if ty == "get" then
        -- RFC 6121 section 2.1.3: the roster result.
        (env, [.send (iqResult st.id none
          [.element "query" [⟨"xmlns", nsRoster⟩] (env.roster.map RosterItem.toXml)])])
      else
        -- RFC 6121 section 2.3 / 2.5: set and remove, then push.
        let items := (elemChildren q).filter (fun c => elemName c == some "item")
        let applyOne : (Roster × List Node) → Node → (Roster × List Node) :=
          fun (r, pushes) it =>
            match elemAttr it "jid" with
            | none => (r, pushes)
            | some j =>
              let jb := bareOf j
              if elemAttr it "subscription" == some "remove" then
                let gone : RosterItem := ⟨jb, "", "remove", false⟩
                (rosterRemove r jb, pushes ++ [RosterItem.toXml gone])
              else
                let existing := rosterFind r jb
                let item : RosterItem :=
                  { jid := jb
                    name := (elemAttr it "name").getD ((existing.map (·.name)).getD "")
                    subscription := (existing.map (·.subscription)).getD "none"
                    ask := (existing.map (·.ask)).getD false }
                (rosterPut r item, pushes ++ [RosterItem.toXml item])
        let (r', pushes) := items.foldl applyOne (env.roster, [])
        ({ env with roster := r' },
         [ .send (iqResult st.id none []),
           .saveRoster bare (rosterEncode r'),
           .send (render (.element "iq"
             [⟨"to", (s.fullJid).getD bare⟩, ⟨"type", "set"⟩, ⟨"id", "push-" ++ st.id.getD "0"⟩]
             [.element "query" [⟨"xmlns", nsRoster⟩] pushes])) ])
    | none =>
      match session with
      | some _ => (env, [.send (iqResult st.id none [])])
      | none =>
        match disco with
        | some _ =>
          (env, [.send (iqResult st.id none
            [.element "query" [⟨"xmlns", nsDiscoInfo⟩]
              [ .element "identity"
                  [⟨"category", "server"⟩, ⟨"type", "im"⟩, ⟨"name", "Factoidal XMPP"⟩] [],
                .element "feature" [⟨"var", nsRoster⟩] [],
                .element "feature" [⟨"var", nsDiscoInfo⟩] [] ]])])
        | none =>
          if ty == "result" || ty == "error" then (env, [])
          else
            -- RFC 6120 section 8.4: an unhandled IQ gets
            -- `service-unavailable`, never silence.
            (env, [.send (stanzaError .iq st.id none (some s.cfg.domain)
              "cancel" "service-unavailable")])

/-- Handle a presence stanza once bound (RFC 6121 sections 3 and 4). -/
def handlePresence (s : Session) (env : Env) (st : Stanza) (bare full : String) :
    Env × List Out :=
  let ty := st.type.getD "available"
  match st.to with
  | none =>
    -- RFC 6121 section 4.4.2: broadcast to every contact allowed to see
    -- it, and back to this session (section 4.4.3).
    let available := ty != "unavailable"
    let out := Core.Stanza.toXml { st with from_ := Jid.parse full }
    (env,
     [.presence bare full available] ++
     (presenceTargets env.roster).map (fun t => Out.route t (render out)) ++
     [.send (render out)])
  | some target =>
    let t := bareOf (Jid.render target)
    let out := render (Core.Stanza.toXml { st with from_ := Jid.parse bare })
    if ty == "subscribe" then
      -- RFC 6121 section 3.1.2: record the pending request, push the
      -- item, then forward.
      let existing := rosterFind env.roster t
      let item : RosterItem :=
        { jid := t, name := (existing.map (·.name)).getD ""
          subscription := (existing.map (·.subscription)).getD "none", ask := true }
      let r' := rosterPut env.roster item
      ({ env with roster := r' },
       [.saveRoster bare (rosterEncode r'), .route t out])
    else if ty == "subscribed" then
      -- RFC 6121 section 3.1.4: the contact may now see our presence.
      let existing := rosterFind env.roster t
      let sub := match (existing.map (·.subscription)).getD "none" with
        | "to" => "both"
        | "both" => "both"
        | _ => "from"
      let item : RosterItem :=
        { jid := t, name := (existing.map (·.name)).getD ""
          subscription := sub, ask := (existing.map (·.ask)).getD false }
      let r' := rosterPut env.roster item
      ({ env with roster := r' },
       [.saveRoster bare (rosterEncode r'), .route t out])
    else (env, [.route t out])

/-- Handle one framed unit. Total: every input produces a session, an
environment and a list of actions, and no input can fail to be answered. -/
def step (s : Session) (env : Env) (u : Framing.Unit) : Session × Env × List Out :=
  match s.stage with
  | .closed => (s, env, [])
  | _ =>
  match u with
  | .decl _ => (s, env, [])
  | .streamClose =>
    ({ s with stage := .closed }, env, [.send "</stream:stream>", .close])
  | .streamOpen text =>
    (match Core.StreamHeader.parse text with
     | none =>
       ({ s with stage := .closed }, env,
        [.send (streamOpenText s.cfg)] ++
          streamError "invalid-xml" "the stream header did not parse")
     | some (h, _) =>
       -- RFC 6120 section 4.9.3.6: a `to` naming a domain this server is
       -- not authoritative for is `host-unknown`.
       if (h.to.map (·.domainpart)).elim false (fun d => d != s.cfg.domain) then
         ({ s with stage := .closed }, env,
          [.send (streamOpenText s.cfg)] ++
            streamError "host-unknown" "this server is not authoritative for that domain")
       else match s.stage with
         | .authenticated user =>
           -- RFC 6120 section 6.4.6: the post-SASL stream restart.
           ({ s with stage := .awaitingBind user }, env,
            [.send (streamOpenText s.cfg), .send postAuthFeatures])
         | .initial =>
           ({ s with stage := .awaitingAuth }, env,
            [.send (streamOpenText s.cfg), .send (initialFeatures s.cfg)])
         | _ =>
           ({ s with stage := .closed }, env,
            streamError "not-well-formed" "a second stream header in this state"))
  | .element text =>
    match Wire.parseElement text with
    | none =>
      ({ s with stage := .closed }, env,
       streamError "not-well-formed" "the element did not parse")
    | some node =>
      let tag := (elemName node).getD ""
      match s.stage with
      | .initial =>
        ({ s with stage := .closed }, env,
         streamError "not-well-formed" "a stanza before the stream header")
      | .awaitingAuth =>
        if tag == "auth" then
          let (s', outs) := handleAuth s node
          (s', env, outs)
        else (s, env, [.send (saslFailure "malformed-request")])
      | .awaitingScramResponse user nonce cfb sf =>
        if tag == "response" then
          let (s', outs) := handleScramResponse s user nonce cfb sf node
          (s', env, outs)
        else if tag == "abort" then
          ({ s with stage := .awaitingAuth }, env, [.send (saslFailure "aborted")])
        else (s, env, [.send (saslFailure "malformed-request")])
      | .authenticated _ =>
        ({ s with stage := .closed }, env,
         streamError "not-authorized" "a stanza before the stream restart")
      | .awaitingBind user =>
        -- RFC 6120 section 7.5/7.6: bind, with a client-proposed
        -- resource or a server-generated one.
        if tag == "iq" then
          match childByNs (elemChildren node) nsBind (some "bind") with
          | none =>
            (s, env, [.send (stanzaError .iq (elemAttr node "id") none (some s.cfg.domain)
              "cancel" "not-allowed")])
          | some b =>
            let proposed := (elemChildren b).find? (fun c => elemName c == some "resource")
            let resource := match proposed.map textOf with
              | some r => if r.isEmpty then s.cfg.streamId else r
              | none => s.cfg.streamId
            let full := user ++ "@" ++ s.cfg.domain ++ "/" ++ resource
            ({ s with stage := .bound user resource }, env,
             [.send (bindResult (elemAttr node "id") full)])
        else (s, env, [.send (saslFailure "malformed-request")])
      | .bound user resource =>
        let bare := user ++ "@" ++ s.cfg.domain
        let full := bare ++ "/" ++ resource
        match Core.Stanza.ofXml node with
        | none =>
          ({ s with stage := .closed }, env,
           streamError "unsupported-stanza-type" s!"unsupported top-level element `{tag}`")
        | some st =>
          match st.kind with
          | .iq =>
            let (env', outs) := handleIq s env st text bare full
            (s, env', outs)
          | .presence =>
            let (env', outs) := handlePresence s env st bare full
            (s, env', outs)
          | .message =>
            -- RFC 6121 section 8.1: a message with no `to` is addressed
            -- to the sender's own account.
            match st.to with
            | none => (s, env, [.send (render (Core.Stanza.toXml
                { st with from_ := Jid.parse full, to := Jid.parse bare }))])
            | some target =>
              (s, env, [.route (bareOf (Jid.render target))
                (render (Core.Stanza.toXml { st with from_ := Jid.parse full }))])
      | .closed => (s, env, [])

/-- May this session receive a stanza that arrived for it from another
connection? Only a BOUND session may (RFC 6121 section 8.5.3: an
unavailable resource is not a delivery target). The host asks BEFORE it
touches the mailbox, because a host that reads and unlinks a stanza this
function would refuse has destroyed it — measured 2026-09-07, when
exactly that lost a message between two sessions in
`tests/xmpp/server.mjs`. -/
def Session.canDeliver (s : Session) : Bool :=
  match s.stage with
  | .bound _ _ => true
  | _ => false

/-- A stanza that arrived from another connection through the host's
mailbox. It reaches the client only once the session is bound — RFC 6121
section 8.5.3 says an unavailable resource is not a delivery target — so
the gate is here, not in the host. -/
def deliver (s : Session) (text : String) : List Out :=
  match s.stage with
  | .bound _ _ => [.send text]
  | _ => []

/-- What the server sends the moment the connection opens: nothing. RFC
6120 section 4.2 makes the INITIATING entity send the first stream
header. -/
def greeting : List Out := []

/-! ## Checks

The negotiation sequence, exercised as the RFC prints it. `sends` keeps
only the bytes that go to the socket, which is what a client sees. -/

/-- Is `needle` anywhere in `hay`? Used by the checks below to assert on
the bytes a client would actually see. -/
private def has (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def sends (outs : List Out) : List String :=
  outs.filterMap (fun o => match o with | .send t => some t | _ => none)

private def testCfg : Config :=
  { domain := "example.com", streamId := "SID-1", serverNonce := "SRVNONCE"
    saltB64 := "W22ZaJ0SNY7soEsUEjb6gQ==", iterationCount := 4096
    accounts := [⟨"juliet", "r0m30"⟩, ⟨"romeo", "juli3t"⟩], tlsCarrier := true }

private def run (s : Session) (env : Env) : List Framing.Unit →
    Session × Env × List Out
  | [] => (s, env, [])
  | u :: us =>
    let (s', env', outs) := step s env u
    let (s'', env'', outs') := run s' env' us
    (s'', env'', outs ++ outs')

-- RFC 6120 section 4.2: the stream header is answered with a header and
-- features, and the features offer SASL.
#guard
  let (s, _, outs) := step (Session.init testCfg) ⟨[]⟩
    (.streamOpen "<stream:stream to='example.com' version='1.0'>")
  s.stage == .awaitingAuth &&
  (sends outs).length == 2 &&
  has ((sends outs)[1]!) "SCRAM-SHA-256"

-- RFC 6120 section 4.9.3.6: a stream for the wrong domain is
-- `host-unknown` and the stream closes.
#guard
  let (s, _, outs) := step (Session.init testCfg) ⟨[]⟩
    (.streamOpen "<stream:stream to='elsewhere.example' version='1.0'>")
  s.stage == .closed && has (String.join (sends outs)) "host-unknown"

-- SASL PLAIN, RFC 4616: base64 of NUL "juliet" NUL "r0m30" authenticates.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, _) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>" ]
  s.stage == .authenticated "juliet"

-- The wrong password is `not-authorized` and the stage does not advance.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet wrong").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>" ]
  s.stage == .awaitingAuth &&
  has (String.join (sends outs)) "not-authorized"

-- An unknown mechanism is refused rather than accepted by default.
#guard
  let (s, _, outs) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='ANONYMOUS'/>" ]
  s.stage == .awaitingAuth &&
  has (String.join (sends outs)) "invalid-mechanism"

-- RFC 6120 section 6.4.6 and section 7: restart, bind, then the full JID
-- comes back in the bind result.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, outs) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
      .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'><resource>balcony</resource></bind></iq>" ]
  s.stage == .bound "juliet" "balcony" &&
  has (String.join (sends outs)) "juliet@example.com/balcony"

-- RFC 6120 section 7.6: no resource proposed means the server assigns one.
#guard
  let payload := Scram.b64Encode (ByteArray.mk
    (((" juliet r0m30").toUTF8).toList.toArray))
  let (s, _, _) := run (Session.init testCfg) ⟨[]⟩
    [ .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<auth xmlns='{nsSasl}' mechanism='PLAIN'>{payload}</auth>",
      .streamOpen "<stream:stream to='example.com' version='1.0'>",
      .element s!"<iq type='set' id='b1'><bind xmlns='{nsBind}'/></iq>" ]
  s.stage == .bound "juliet" "SID-1"

-- RFC 6120 section 6: a stanza sent before authentication is a stream
-- error, not a silently dropped stanza.
#guard
  let (s, _, outs) := step (Session.init testCfg) ⟨[]⟩ (.element "<message to='x'/>")
  s.stage == .closed &&
  has (String.join (sends outs)) "not-well-formed"

-- RFC 6121 section 8.1: a message to another account is routed to that
-- bare JID with a `from` the server stamped, not the one the client
-- claimed.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, _, outs) := step s ⟨[]⟩
    (.element "<message to='romeo@example.com' from='mallory@evil.example' type='chat'><body>hi</body></message>")
  outs.any (fun o => match o with
    | .route t x => t == "romeo@example.com" &&
        has x "from=\"juliet@example.com/balcony\""
    | _ => false)

-- RFC 6121 section 2.1.3: the roster get returns every stored item.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := ⟨[⟨"romeo@example.com", "Romeo", "both", false⟩]⟩
  let (_, _, outs) := step s env (.element s!"<iq type='get' id='r1'><query xmlns='{nsRoster}'/></iq>")
  has (String.join (sends outs)) "romeo@example.com"

-- RFC 6121 section 2.3: a roster set stores the item, saves the file and
-- pushes the change back.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, env', outs) := step s ⟨[]⟩
    (.element s!"<iq type='set' id='r2'><query xmlns='{nsRoster}'><item jid='nurse@example.com' name='Nurse'/></query></iq>")
  env'.roster == [⟨"nurse@example.com", "Nurse", "none", false⟩] &&
  outs.any (fun o => match o with
    | .saveRoster b _ => b == "juliet@example.com" | _ => false)

-- RFC 6121 section 2.5: `subscription='remove'` deletes the item.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := ⟨[⟨"romeo@example.com", "Romeo", "both", false⟩]⟩
  let (_, env', _) := step s env
    (.element s!"<iq type='set' id='r3'><query xmlns='{nsRoster}'><item jid='romeo@example.com' subscription='remove'/></query></iq>")
  env'.roster == []

-- RFC 6121 section 4.4.2: available presence with no `to` goes to every
-- contact with subscription `from` or `both`, and back to the sender.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let env : Env := ⟨[⟨"romeo@example.com", "", "both", false⟩,
                     ⟨"nurse@example.com", "", "to", false⟩]⟩
  let (_, _, outs) := step s env (.element "<presence/>")
  (outs.filterMap (fun o => match o with | .route t _ => some t | _ => none))
    == ["romeo@example.com"]

-- RFC 6121 section 3.1.2: a subscription request sets `ask` and is
-- forwarded.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, env', outs) := step s ⟨[]⟩
    (.element "<presence to='romeo@example.com' type='subscribe'/>")
  env'.roster == [⟨"romeo@example.com", "", "none", true⟩] &&
  outs.any (fun o => match o with | .route t _ => t == "romeo@example.com" | _ => false)

-- RFC 6120 section 8.4: an IQ nobody handles gets `service-unavailable`.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (_, _, outs) := step s ⟨[]⟩
    (.element "<iq type='get' id='q1'><query xmlns='urn:example:nothing'/></iq>")
  has (String.join (sends outs)) "service-unavailable"

-- RFC 6120 section 4.4: the close is answered with a close and the
-- session ends.
#guard
  let s : Session := { cfg := testCfg, stage := .bound "juliet" "balcony" }
  let (s', _, outs) := step s ⟨[]⟩ .streamClose
  s'.stage == .closed && outs.contains .close

-- A stanza that arrives for an unbound session is held, not delivered.
#guard deliver (Session.init testCfg) "<message/>" == []
#guard deliver { cfg := testCfg, stage := .bound "juliet" "balcony" } "<message/>"
  == [.send "<message/>"]

-- Nothing at all happens after the stream is closed.
#guard
  let s : Session := { cfg := testCfg, stage := .closed }
  let (_, _, outs) := step s ⟨[]⟩ (.element "<message to='x'/>")
  outs == []

-- The roster's on-disk form round-trips.
#guard rosterDecode (rosterEncode [⟨"a@b", "A", "both", false⟩, ⟨"c@d", "", "to", true⟩])
  == [⟨"a@b", "A", "both", false⟩, ⟨"c@d", "", "to", true⟩]

end L4Factoidal.XMPP.Server
