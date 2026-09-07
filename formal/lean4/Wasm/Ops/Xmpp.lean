/-
Wasm.Ops.Xmpp — the stateless XMPP/GC3 ops surface, over
`L4Factoidal.XMPP` (`formal/lean4/L4Factoidal/XMPP/README.md`).

  xmppJidParse(jid)
    -> {"ok":true,"localpart":s|null,"domainpart":s,"resourcepart":s|null,"wellFormed":bool}
  xmppJidRender({"localpart":s|null,"domainpart":s,"resourcepart":s|null})
    -> {"ok":true,"jid":"…"}
  xmppStreamHeaderParse(xml)
    -> {"ok":true,"from":s|null,"to":s|null,"id":s|null,"version":s|null,"lang":s|null,"rest":"…unconsumed…"}
  xmppStreamHeaderRender({"from":s|null,"to":s|null,"id":s|null,"version":s|null,"lang":s|null})
    -> {"ok":true,"xml":"<stream:stream …>"}
  xmppFeaturesFor({"stage":"preTls"|"postTls"|"authenticated"|"bound","mechanisms":[…]})
    -> {"ok":true,"startTlsRequired":"required"|"optional"|null,"saslMechanisms":[…],
        "canBind":bool,"canSession":bool,"xml":"<stream:features>…</stream:features>"}
  xmppStanzaParse(xml)
    -> {"ok":true,"kind":"message"|"presence"|"iq","id":s|null,"from":s|null,"to":s|null,
        "type":s|null,"payloadXml":"…serialized children…"}

Every op returns the same `{"ok":…}` envelope every other op in this
dispatch uses (`Wasm.Ops.Support`). Scope matches exactly what
`L4Factoidal.XMPP` implements today (2026-09-07): no stanza-render-from-
JSON (payload reconstruction from JSON needs a sibling-node XML parser
this module doesn't have yet — a stated gap, not a silent one), no GC3
(still an unfinished upstream spec), no SASL/crypto (no HACL* HMAC yet).

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.XMPP.Jid
import L4Factoidal.XMPP.Wire
import L4Factoidal.XMPP.Core

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.XMPP
open L4Factoidal.XMPP.Core
open L4Factoidal.XMPP.Wire

private def jsonOfOptString (o : Option String) : Json :=
  o.elim .null .string

/-- `xmppJidParse(jid)`. -/
def xmppJidParse (s : String) : String :=
  match Jid.parse s with
  | none => errJson s!"not a structurally valid JID: {s}"
  | some j =>
    okWith [
      ("localpart", jsonOfOptString j.localpart),
      ("domainpart", .string j.domainpart),
      ("resourcepart", jsonOfOptString j.resourcepart),
      ("wellFormed", .bool (Jid.isWellFormed j))
    ]

/-- `xmppJidRender({"localpart":s|null,"domainpart":s,"resourcepart":s|null})`. -/
def xmppJidRender (jidJson : String) : String :=
  match parseJson jidJson with
  | .error e => errJson s!"jidJson: {toString e}"
  | .ok j =>
    match j.getString? "domainpart" with
    | none => errJson "xmppJidRender: missing required field 'domainpart'"
    | some domainpart =>
      let jid : Jid := {
        localpart := j.getString? "localpart"
        domainpart := domainpart
        resourcepart := j.getString? "resourcepart"
      }
      okWith [("jid", .string (Jid.render jid))]

/-- `xmppStreamHeaderParse(xml)`. Tolerates one leading `<?xml ...?>`
declaration, since real servers send one (`Wire.skipXmlDecl`). -/
def xmppStreamHeaderParse (s : String) : String :=
  match StreamHeader.parse s with
  | none => errJson "not a valid <stream:stream> open tag"
  | some (h, rest) =>
    okWith [
      ("from", jsonOfOptString (h.from_.map Jid.render)),
      ("to", jsonOfOptString (h.to.map Jid.render)),
      ("id", jsonOfOptString h.id),
      ("version", jsonOfOptString h.version),
      ("lang", jsonOfOptString h.lang),
      ("rest", .string rest)
    ]

/-- `xmppStreamHeaderRender({"from":s|null,"to":s|null,"id":s|null,"version":s|null,"lang":s|null})`. -/
def xmppStreamHeaderRender (headerJson : String) : String :=
  match parseJson headerJson with
  | .error e => errJson s!"headerJson: {toString e}"
  | .ok j =>
    let h : StreamHeader := {
      from_ := (j.getString? "from").bind Jid.parse
      to := (j.getString? "to").bind Jid.parse
      id := j.getString? "id"
      version := j.getString? "version"
      lang := j.getString? "lang"
    }
    okWith [("xml", .string (StreamHeader.render h))]

/-- `xmppFeaturesFor({"stage":"preTls"|"postTls"|"authenticated"|"bound","mechanisms":[…]})`. -/
def xmppFeaturesFor (argsJson : String) : String :=
  match parseJson argsJson with
  | .error e => errJson s!"argsJson: {toString e}"
  | .ok j =>
    match j.getString? "stage" with
    | none => errJson "xmppFeaturesFor: missing required field 'stage'"
    | some stageStr =>
      match (match stageStr with
        | "preTls" => some ConnStage.preTls
        | "postTls" => some ConnStage.postTls
        | "authenticated" => some ConnStage.authenticated
        | "bound" => some ConnStage.bound
        | _ => none) with
      | none =>
        errJson s!"xmppFeaturesFor: unknown stage '{stageStr}' (expected preTls/postTls/authenticated/bound)"
      | some stage =>
        let mechs := (j.getStringArray? "mechanisms").getD []
        let f := featuresFor stage mechs
        okWith [
          ("startTlsRequired",
            jsonOfOptString (f.startTls.map (fun required => if required then "required" else "optional"))),
          ("saslMechanisms", .array (f.saslMechanisms.map .string)),
          ("canBind", .bool f.canBind),
          ("canSession", .bool f.canSession),
          ("xml", .string (Wire.render (StreamFeatures.toXml f)))
        ]

/-- `xmppStanzaParse(xml)`. -/
def xmppStanzaParse (s : String) : String :=
  match Stanza.parse s with
  | none => errJson "not a valid message/presence/iq stanza"
  | some stz =>
    okWith [
      ("kind", .string stz.kind.tagName),
      ("id", jsonOfOptString stz.id),
      ("from", jsonOfOptString (stz.from_.map Jid.render)),
      ("to", jsonOfOptString (stz.to.map Jid.render)),
      ("type", jsonOfOptString stz.type),
      ("payloadXml", .string (Wire.renderList stz.payload))
    ]

end L4Wasm.Ops
