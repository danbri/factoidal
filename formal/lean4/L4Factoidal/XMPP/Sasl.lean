/-!
SASL SCRAM message format (RFC 5802 base mechanism; RFC 7677 pins the hash
to SHA-256 for `SCRAM-SHA-256`) — the client-first/server-first/
client-final/server-final message grammar, parsed and rendered.

Does NOT implement the hash/HMAC/PBKDF2 computation itself — that boundary
belongs to `XmppLean.Crypto` (HACL*, not yet wired). This module covers the
message FORMAT only, which is independently real and testable against the
RFC 5802 §5 worked example without needing the crypto finished.

Known gap: RFC 5802's escaping of literal `,` and `=` within a SASL
username (`=2C` / `=3D`) is not implemented — usernames containing those
characters will not round-trip correctly. Flagged, not silent.
-/

namespace L4Factoidal.XMPP.Sasl

private def attrOf (part : String) : Option (Char × String) :=
  match part.toList with
  | k :: '=' :: rest => some (k, String.ofList rest)
  | _ => none

def parseAttrList (parts : List String) : List (Char × String) :=
  parts.filterMap attrOf

def findAttr (attrs : List (Char × String)) (k : Char) : Option String :=
  (attrs.find? (fun p => p.1 == k)).map (·.2)

/-- `n,,n=<username>,r=<client-nonce>` — the "no channel binding, no
authzid" case, the common one for a first cut. -/
structure ClientFirstMessage where
  username : String
  clientNonce : String
  deriving Repr

namespace ClientFirstMessage

def render (m : ClientFirstMessage) : String :=
  s!"n,,n={m.username},r={m.clientNonce}"

def parse (s : String) : Option ClientFirstMessage :=
  match s.splitOn "," with
  | _gs2cbFlag :: _gs2authzid :: rest =>
    let attrs := parseAttrList rest
    match findAttr attrs 'n', findAttr attrs 'r' with
    | some u, some r => some { username := u, clientNonce := r }
    | _, _ => none
  | _ => none

end ClientFirstMessage

/-- `r=<combined nonce>,s=<base64 salt>,i=<iteration count>` -/
structure ServerFirstMessage where
  nonce : String
  salt : String
  iterationCount : Nat
  deriving Repr

namespace ServerFirstMessage

def render (m : ServerFirstMessage) : String :=
  s!"r={m.nonce},s={m.salt},i={m.iterationCount}"

def parse (s : String) : Option ServerFirstMessage :=
  let attrs := parseAttrList (s.splitOn ",")
  match findAttr attrs 'r', findAttr attrs 's', findAttr attrs 'i' with
  | some r, some salt, some iStr =>
    match iStr.toNat? with
    | some i => some { nonce := r, salt := salt, iterationCount := i }
    | none => none
  | _, _, _ => none

end ServerFirstMessage

/-- `c=<base64 gs2-header(+channel binding)>,r=<combined nonce>,p=<base64 proof>` -/
structure ClientFinalMessage where
  channelBinding : String
  nonce : String
  proof : String
  deriving Repr

namespace ClientFinalMessage

def render (m : ClientFinalMessage) : String :=
  s!"c={m.channelBinding},r={m.nonce},p={m.proof}"

def parse (s : String) : Option ClientFinalMessage :=
  let attrs := parseAttrList (s.splitOn ",")
  match findAttr attrs 'c', findAttr attrs 'r', findAttr attrs 'p' with
  | some c, some r, some p => some { channelBinding := c, nonce := r, proof := p }
  | _, _, _ => none

end ClientFinalMessage

/-- `v=<base64 server signature>` on success, `e=<error>` on failure. -/
structure ServerFinalMessage where
  verifier : Option String
  error : Option String
  deriving Repr

namespace ServerFinalMessage

def render (m : ServerFinalMessage) : String :=
  match m.verifier, m.error with
  | some v, _ => s!"v={v}"
  | none, some e => s!"e={e}"
  | none, none => ""

def parse (s : String) : Option ServerFinalMessage :=
  let attrs := parseAttrList (s.splitOn ",")
  match findAttr attrs 'v', findAttr attrs 'e' with
  | some v, _ => some { verifier := some v, error := none }
  | none, some e => some { verifier := none, error := some e }
  | none, none => none

end ServerFinalMessage

end L4Factoidal.XMPP.Sasl
