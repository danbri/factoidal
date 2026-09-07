import L4Factoidal.XMPP.Jid
import L4Factoidal.XMPP.Wire

/-!
RFC 6120 (XMPP Core): stream headers, feature negotiation, and stanzas,
built on `L4Factoidal.XML` (via `L4Factoidal.XMPP.Wire`) and
`L4Factoidal.XMPP.Jid`.

- `StreamHeader` / `StreamFeatures` / `ConnStage` / `featuresFor`: the
  `<stream:stream>` open tag and the `<stream:features>` negotiation
  sequence, expressed so the RFC 6120 ordering (TLS, then SASL, then
  bind/session) is structural rather than a runtime check.
- `Stanza`: the three stanza kinds (`message`/`presence`/`iq`) and their
  common attributes (`from`, `to`, `type`, `id`), converted to/from
  `L4Factoidal.XML.Node`. Payload children are kept as generic nodes for
  now — typed payloads (e.g. `<body>`, GC3 elements) are a later layer.

Not yet implemented: the actual TLS handshake and SASL mechanism logic
(both are separate concerns — see `Crypto` in the root `L4Factoidal/Crypto`
tree, and `L4Factoidal.XMPP.Sasl`), resource binding, and stanza routing
decisions — see `README.md`.
-/

namespace L4Factoidal.XMPP.Core

open L4Factoidal.XML (Node Attribute)
open L4Factoidal.XMPP (Jid)

def findAttr (attrs : List Attribute) (name : String) : Option String :=
  (attrs.find? (fun a => a.name == name)).map (·.value)

/-- An RFC 6120 stream header (`<stream:stream ...>`). Unlike a `Stanza`,
this element is never closed until the connection ends, so it's parsed via
`Wire.parseOpenTag`, not a complete-element parse. -/
structure StreamHeader where
  from_ : Option Jid
  to : Option Jid
  id : Option String
  version : Option String
  lang : Option String
  deriving Repr

namespace StreamHeader

def ofAttrs (attrs : List Attribute) : Option StreamHeader :=
  let fromRaw := findAttr attrs "from"
  let toRaw := findAttr attrs "to"
  let from? := fromRaw.bind Jid.parse
  let to? := toRaw.bind Jid.parse
  if fromRaw.isSome && from?.isNone then none
  else if toRaw.isSome && to?.isNone then none
  else some {
    from_ := from?
    to := to?
    id := findAttr attrs "id"
    version := findAttr attrs "version"
    lang := findAttr attrs "xml:lang"
  }

def toAttrs (h : StreamHeader) : List Attribute :=
  (h.from_.map (fun j => Attribute.mk "from" (Jid.render j))).toList ++
  (h.to.map (fun j => Attribute.mk "to" (Jid.render j))).toList ++
  (h.id.map (Attribute.mk "id")).toList ++
  (h.version.map (Attribute.mk "version")).toList ++
  (h.lang.map (Attribute.mk "xml:lang")).toList

/-- Parse a `<stream:stream ...>` opening tag. Returns the header and the
unconsumed remainder (features, stanzas, and eventually
`</stream:stream>`, all still to be parsed separately). Fails if the tag
isn't `stream:stream` or its `from`/`to` attributes aren't valid JIDs. -/
def parse (s : String) : Option (StreamHeader × String) :=
  match Wire.parseOpenTag s with
  | none => none
  | some (tag, attrs, _selfClosing, rest) =>
    if tag != "stream:stream" then none
    else match ofAttrs attrs with
      | none => none
      | some h => some (h, rest)

def render (h : StreamHeader) : String :=
  let attrStr := String.join ((toAttrs h).map (fun a => s! " {a.name}=\"{Wire.escapeAttr a.value}\""))
  s!"<stream:stream{attrStr}>"

end StreamHeader

/-- What a server offers in `<stream:features>`, per RFC 6120 §4.3 /
RFC 6120bis §14.8 and RFC 6120 §6 (SASL) / XEP-0163's bind. -/
structure StreamFeatures where
  /-- `none` = STARTTLS not offered; `some required` = offered, with the
  "MUST negotiate TLS before anything else" flag per RFC 6120 §5.4.1. -/
  startTls : Option Bool
  saslMechanisms : List String
  canBind : Bool
  canSession : Bool
  deriving Repr

namespace StreamFeatures

def toXml (f : StreamFeatures) : Node :=
  let tlsNodes : List Node :=
    match f.startTls with
    | none => []
    | some required =>
      let children : List Node := if required then [.element "required" [] []] else []
      [.element "starttls" [⟨"xmlns", "urn:ietf:params:xml:ns:xmpp-tls"⟩] children]
  let saslNodes : List Node :=
    if f.saslMechanisms.isEmpty then []
    else [.element "mechanisms" [⟨"xmlns", "urn:ietf:params:xml:ns:xmpp-sasl"⟩]
           (f.saslMechanisms.map (fun m => Node.element "mechanism" [] [.text m]))]
  let bindNodes : List Node :=
    if f.canBind then [.element "bind" [⟨"xmlns", "urn:ietf:params:xml:ns:xmpp-bind"⟩] []] else []
  let sessionNodes : List Node :=
    if f.canSession then [.element "session" [⟨"xmlns", "urn:ietf:params:xml:ns:xmpp-session"⟩] []] else []
  .element "stream:features" [] (tlsNodes ++ saslNodes ++ bindNodes ++ sessionNodes)

end StreamFeatures

/-- Coarse negotiation stage. Real RFC 6120 policy: STARTTLS (required)
before anything else; SASL mechanisms once TLS is active but before
authentication; bind/session once authenticated. -/
inductive ConnStage where
  | preTls
  | postTls
  | authenticated
  | bound
  deriving Repr, DecidableEq

/-- What to advertise in `<stream:features>` at a given stage. This is the
actual RFC 6120 ordering constraint expressed as a total function: it is
not possible to construct a `StreamFeatures` value from this function that
offers SASL before TLS, or bind before authentication. -/
def featuresFor (stage : ConnStage) (mechanisms : List String) : StreamFeatures :=
  match stage with
  | .preTls => { startTls := some true, saslMechanisms := [], canBind := false, canSession := false }
  | .postTls => { startTls := none, saslMechanisms := mechanisms, canBind := false, canSession := false }
  | .authenticated => { startTls := none, saslMechanisms := [], canBind := true, canSession := true }
  | .bound => { startTls := none, saslMechanisms := [], canBind := false, canSession := false }

/-! ## RFC 6120 negotiation ordering, as theorems, not prose.

Adversarial framing: no matter how a future refactor of `featuresFor`
changes case order, adds a stage, or restructures the match, these fail
to compile the moment the ordering constraint they name is violated —
catching the regression at build time instead of needing a human to
notice a stray field in a test. Each is `rfl`: the guarantee is that
strong, since `featuresFor` is a plain total function over a 4-constructor
enum. -/

/-- STARTTLS is offered only pre-TLS. -/
theorem featuresFor_startTls_iff_preTls (stage : ConnStage) (mechs : List String) :
    (featuresFor stage mechs).startTls.isSome = true ↔ stage = .preTls := by
  cases stage <;> simp [featuresFor]

/-- SASL mechanisms are advertised only post-TLS, pre-authentication — never
before TLS, and never re-advertised after authentication. -/
theorem featuresFor_sasl_iff_postTls (stage : ConnStage) (mechs : List String) :
    mechs ≠ [] → ((featuresFor stage mechs).saslMechanisms ≠ [] ↔ stage = .postTls) := by
  cases stage <;> simp [featuresFor]

/-- Resource binding is offered only once authenticated — never before
SASL has actually succeeded. -/
theorem featuresFor_bind_iff_authenticated (stage : ConnStage) (mechs : List String) :
    (featuresFor stage mechs).canBind = true ↔ stage = .authenticated := by
  cases stage <;> simp [featuresFor]

/-- No stage ever offers both STARTTLS and bind at once — the two ends of
the negotiation sequence are never simultaneously advertised. -/
theorem featuresFor_not_tls_and_bind (stage : ConnStage) (mechs : List String) :
    ¬((featuresFor stage mechs).startTls.isSome = true ∧ (featuresFor stage mechs).canBind = true) := by
  cases stage <;> simp [featuresFor]

inductive StanzaKind where
  | message
  | presence
  | iq
  deriving Repr, DecidableEq

def StanzaKind.tagName : StanzaKind → String
  | .message => "message"
  | .presence => "presence"
  | .iq => "iq"

def StanzaKind.ofTag : String → Option StanzaKind
  | "message" => some .message
  | "presence" => some .presence
  | "iq" => some .iq
  | _ => none

structure Stanza where
  kind : StanzaKind
  id : Option String
  from_ : Option Jid
  to : Option Jid
  type : Option String
  payload : List Node
  deriving Repr

namespace Stanza

/-- Convert a generic XML node (from `Wire.parseElement`, i.e.
`L4Factoidal.XML.parseXML`) to a `Stanza`. Fails if the tag isn't one of
`message`/`presence`/`iq`, or if a `from`/`to` attribute is present but
isn't a well-formed-enough JID to parse. -/
def ofXml (n : Node) : Option Stanza :=
  match n with
  | .element tag attrs children =>
    match StanzaKind.ofTag tag with
    | none => none
    | some kind =>
      let fromRaw := findAttr attrs "from"
      let toRaw := findAttr attrs "to"
      let from? := fromRaw.bind Jid.parse
      let to? := toRaw.bind Jid.parse
      if fromRaw.isSome && from?.isNone then none
      else if toRaw.isSome && to?.isNone then none
      else
        some {
          kind := kind
          id := findAttr attrs "id"
          from_ := from?
          to := to?
          type := findAttr attrs "type"
          payload := children
        }
  | _ => none

/-- Parse a complete stanza string end to end (via the real XML parser). -/
def parse (s : String) : Option Stanza :=
  (Wire.parseElement s).bind ofXml

def toXml (s : Stanza) : Node :=
  let attrs :=
    (s.from_.map (fun j => Attribute.mk "from" (Jid.render j))).toList ++
    (s.to.map (fun j => Attribute.mk "to" (Jid.render j))).toList ++
    (s.type.map (fun t => Attribute.mk "type" t)).toList ++
    (s.id.map (fun i => Attribute.mk "id" i)).toList
  .element s.kind.tagName attrs s.payload

end Stanza

end L4Factoidal.XMPP.Core
