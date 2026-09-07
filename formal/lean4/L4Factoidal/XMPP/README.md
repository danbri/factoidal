# L4Factoidal.XMPP — design record

Started 2026-09-07, initially scaffolded as a standalone repo/module
(`factoidal/xmpp/`), then folded into `formal/lean4/L4Factoidal/XMPP/` the
same day on owner correction: "The implementation *is* part of Factoidal
(the Lean aspect of it, so yeah L4Factoidal). You might use our XML,
XPath etc. but it needn't be any more tightly tangled than say our
jsonschemas vs our OWL, or CSVW vs MathML." This file exists because chat
logs are not where decisions belong — see the same rule in
`factoidal/CLAUDE.md`. Update it when a decision here is revisited.

**Location and coupling**: a sibling module under `L4Factoidal/`, same as
`CSVW/`, `MathML/`, `JOSE/`, `XML/`, etc. — built and imported as part of
the single `l4factoidal` Lake package (`formal/lean4/lakefile.lean`), not
its own Lake project. Loosely coupled: reuses `L4Factoidal.XML` for wire
parsing (see below) and will reuse the root `L4Factoidal/Crypto/` HACL*
FFI for hashing/HMAC when SASL needs it, but otherwise stays independent
of unrelated spec areas — the same degree of coupling as CSVW has to OWL.

**License**: inherits the repo's top-level Apache-2.0; no separate LICENSE
file in this directory.

## What this is

A fresh XMPP server implementation, built to make GC3 ("Groupchat 3.0" —
the XSF's early-stage MUC/MIX successor, see
https://matthewwild.co.uk/uploads/xmpp-gc3-jan-2025.pdf) a first-class,
formally-checked citizen instead of a bolt-on. Core protocol logic
(RFC 6120/6121 stream handling, SASL, stanza routing, GC3 itself) is
written in Lean 4.

## Why fresh, not built on an existing server

Considered and rejected: Prosody (MIT, and where the reference GC3
prototype already lives — but the point is an independent,
architecturally unrelated implementation, so the ecosystem gets real
interop signal rather than a second instance of the same assumptions),
MongooseIM / ejabberd (Erlang; ejabberd is GPLv2, excluded on license),
xmpp-rs / Mellium / Jackal (libraries or archived, not complete
maintained servers). Full survey and reasoning: 2026-09-07 chat log, "top
10 actively maintained Apache2/MIT ... XMPP server codebases" thread.

**License policy: Apache-2.0 / MIT only, no GPL/AGPL anywhere in the
dependency graph.** Owner instruction, 2026-09-07.

## Why GC3, not MIX

MIX (XEP-0369) is architecturally interesting (PubSub/MAM-native, no
presence-coupled membership) but the XSF's own 2025 assessment is that it
stalled ("Sisyphus every summit where we discuss MIX again and still go
nowhere" — XMPP Summit 27 report) and requires participant-side PubSub
capability that hindered adoption. GC3 is deliberately MUC-shaped with
incremental fixes (persistent joins, stable participant JIDs via
occupant-id, optional presence) rather than a from-scratch data model,
and is where the XSF's actual current design energy is
(`xmpp:gc3@rooms.modernxmpp.org`, prototypes in Prosody and xmpp-rs).
MIX's JID-hidden-channel work (XEP-0404) is deferred/dead; GC3 does not
currently address anonymity at all. Per owner priority (2026-09-07):
implement GC3 as the primary target, with separate MODULES for classic
MUC and MIX interop — not GC3-only, but GC3-native.

MLS (RFC 9420) is the community's stated direction for group E2EE
("groupchat OMEMO" is explicitly considered the wrong shape — pairwise
Double Ratchet per device-pair, O(n·devices) fan-out, incompatible with
JID-hidden membership since key discovery needs real bare JIDs). MIMI
(IETF, EU DMA-driven interop) is standardizing on MLS + HTTPS for
cross-provider federation; Matrix has proposed Matrix-over-MLS into the
same process. MLS is the target E2EE layer for any future
group-encryption work here (owner priority: "MLS centred").

## XML: reuse `L4Factoidal.XML`, don't reimplement it

Per Iron Rule #7 ("no hand-written reimplementations of what the formal
tree defines") and owner instruction (2026-09-07: "XML for the XML
parts"), all general XML parsing goes through the existing, W3C-XML-1.0-
conformant, F*-ported `L4Factoidal.XML` (`Parser.lean`, `Document.lean` —
4,000+ lines, with its own `Theorems.lean` and W3C-conformance
`ConfProbe.lean`), not a competing parser. `L4Factoidal.XMPP.Wire` is the
thin XMPP-specific glue on top of it:
- complete elements (stanzas, `<stream:features>`) parse via
  `L4Factoidal.XML.parseXML` and its `.root`;
- rendering is new work (`L4Factoidal.XML` is parse-only, built for W3C
  conformance testing, not round-tripping) — not a duplicate of anything;
- the one real, stated gap: `<stream:stream ...>` is never closed until
  the connection ends, so it can never be a complete `Node` the way
  `parseXML` expects. `Wire.parseOpenTag` is a narrow, minimal supplement
  for exactly this case, reusing nothing from `L4Factoidal.XML` only
  because that module doesn't (yet) expose an unclosed-root parsing mode.
  The better long-term fix is probably a small, generic addition to
  `L4Factoidal.XML` itself (useful to any streaming-XML protocol, not
  XMPP-specific) — filed as future work, not silently worked around.

An RDF-ish data structure may be worth reaching for elsewhere (see
"Priorities" below) if a good niche shows up — groups/PEP/PubSub
modeling, not the wire format.

## Architecture: tight core + community extensions (Prosody's model)

Prosody's real lesson isn't its language choice, it's the split: `core/`
+ `net/` + `util/` (~32,000 lines) is the actually-required RFC 6120/6121
machinery; everything XEP-shaped lives in `plugins/mod_*`, and the *bulk*
of Prosody's real-world feature set lives in a separate,
community-maintained `prosody-modules` repo, not the main tree. ejabberd
took the opposite "batteries included" approach and its `mod_*.erl` alone
is 82,000 lines — bigger than its whole core.

This module follows Prosody's split, not ejabberd's:
- **Verified core**: stream negotiation, SASL, stanza routing, JID
  handling, GC3 (+ MUC/MIX modules). Proved, not just tested, where the
  property is a real safety property (join persistence, affiliation
  transitions, occupant-id stability, idempotency — see
  `skills/lean4-proof-patterns` for the proof style to reuse).
- **Extensions**: everything else (most XEPs) should be independently
  addable without touching the verified core, the same way a `mod_*.lua`
  drops into Prosody. Design the core's plugin/hook surface for this from
  the start rather than retrofitting it.

## Runtime: Lean → wasm, hosted on the BEAM

Lean 4's easiest export targets are JS/wasm — `formal/lean4/Wasm/`
already has a working export pipeline for other parts of L4Factoidal,
worth reusing/extending rather than building a second one. But the actual
runtime properties this workload needs — one lightweight process per
connection, preemptive scheduling so one client can't starve others,
supervision trees that isolate and restart a crashed session — are BEAM
(Erlang VM) properties, not Node's. Resolution: wasm is the *artifact*,
BEAM is the *host* — call the Lean-compiled wasm module from
Erlang/Elixir via a NIF wrapping `wasmtime` (prior art: `wasmex`,
https://github.com/tessi/wasmex). This keeps the server "fresh" (new
supervision tree, new connection handling — none of it ejabberd's or
MongooseIM's code) while keeping BEAM's concurrency/fault-isolation
model, at the cost of NIF marshalling discipline (cross the boundary once
per stanza with flat byte buffers, not per-field). Not yet implemented;
core Lean logic comes first and is host-agnostic by construction.

## Cryptography: the root `L4Factoidal/Crypto/` HACL* FFI, not a new one

`formal/lean4/lakefile.lean` already compiles and links vendored,
F*/Low*-verified HACL* C (`third_party/hacl/`) for Ed25519, SHA-2, P-256,
and RSA (`L4Factoidal/Crypto/{Ed25519,SHA2Native,P256Native,RsaNative}.lean`
— the P-256/RSA pair landed 2026-09-06 for JOSE, one day before this
module started). SASL SCRAM-SHA-256 needs HMAC-SHA-256, which doesn't
exist there yet but is buildable in pure Lean on top of the existing
`l4_hacl_sha256`/`l4_hacl_sha256_blocks` externs (HMAC's construction
doesn't need its own native primitive) — add it to `L4Factoidal/Crypto/`
when needed, not as an XMPP-local crypto boundary. No new HACL* binding
work should be XMPP-specific; extend the shared FFI, per the existing
extern-family pattern.

## Testing: reuse the world's test suites, don't invent our own protocol oracle

- **MongooseIM's `big_tests`** (Apache-2.0, Common Test + `escalus`
  client) — black-box, wire-level protocol interop tests against a real
  client library. Worth evaluating for direct reuse against this server,
  since it tests protocol behavior over the wire, not MongooseIM
  internals.
- **RFC 5802 / RFC 7677** — official SCRAM-SHA-1 / SCRAM-SHA-256 test
  vectors, for the SASL layer.
- **RFC 8264 / RFC 8265 (PRECIS)** — official test cases for JID
  localpart/resourcepart enforcement.
- **HACL\*'s own upstream test vectors** (NIST CAVP, RFC vectors) —
  already validated upstream; no need to re-derive, just confirm the
  binding reproduces them.
- **XSF Compliance Suites** (e.g. XEP-0479 and successors) — use as a
  checklist for "what does complete mean this year," not as a test
  format.
- Differential testing against the Prosody and xmpp-rs GC3 prototypes
  once GC3's wire format stabilizes — this implementation's value to the
  standards process is partly *as* an independent check on the other two.

## Why now — 2026 context (owner steer, 2026-09-07)

Design against the world this actually ships into, not the world
MUC/MIX were designed for circa 2002/2016:

- **AI everywhere.** Participants won't all be humans typing on
  keyboards — expect agents/bots as first-class, high-volume clients
  (this is also factoidal's own original motivation for wanting MIX at
  all — see `docs/20260831-xmpp-mix-pilot.md`'s "collaboration surface"
  for coding agents and humans together). Don't design
  auth/rate-limiting/identity around "one human, one client, modest
  message rate" as the only shape.
- **Streams, video, audio, phones.** Real-time media has to be a clean
  extension point from day one — owner priority sharpens this to
  "WebRTC baked in" (not just an extension point) plus WebGPU/WebAudio/
  WebXR assumed client-side. GC3's own presence-optional, persistent-join
  design is already the right call for mobile — validated, not new work.
- **Things going viral / "1:billions ready(ish)".** A room's membership
  shape can jump from a handful of people to a huge, bursty audience with
  no warning. Don't assume every channel is small-group-interactive; the
  core needs to accommodate a broadcast/large-audience shape — different
  fan-out, moderation-at-scale, and rate-limiting needs than a family
  group chat — as a distinct room capability, not a scale failure mode.
- **Distrust of tech megacorps.** Reinforces the license policy and the
  fresh-implementation decision, and argues against defaulting to a
  big-tech OIDC/SSO identity anchor even though it would be the
  lowest-friction option — self-hostability and independent verifiability
  are the point, not a compliance checkbox. (Reconciled with the "modern
  auth — OIDC" priority below: OIDC as one pluggable method, not the only
  one.)
- **Zeroconf/serverless (XEP-0174) and IoT/Thread-ready.** New, distinct
  deployment shapes — a constrained/mesh/no-central-server target is
  materially different from "cloud server handling many phone/browser
  clients," and shouldn't be assumed to fall out of the same architecture
  for free.

## Priorities (owner, 2026-09-07, verbatim)

> SECURE / PRIVATE / ELEGANT / UNDERSTANDABLE / AUDITABLE / MODULAR /
> REGULATED INDUSTRY READY / MOBILE FIRST / POST-slack post-discord
> post-socialweb post-AI / 1:billions ready(ish) / WebRTC baked in /
> WebGPU and webaudio webxr assumed / Minimizes xml / Uses a Knowledge
> Graph RDF abstraction for groups, pep, pubsub, feeds, apis, MCP/AI /
> Modern wrt auth etc - OIDC, email based specs, jose / MLS centred /
> implements GC3, with modules for classic MUC and MIX / MIMI and interop
> is centred including the e2e vs groups/ai tradeoffs / Zeroconf/serverless
> xmpp ready / IoT thread/etc ready / Etc

Read as an ordering/ambition statement, not a spec. "Etc" taken as license
to keep applying this list's spirit to future decisions, not as a literal
further requirement.

**Resolved, 2026-09-07** (owner replies, in order):
1. "XML for the XML parts. An RDF-esque data structure elsewhere if there
   is a niche." → settles the XML-vs-RDF question above: reuse
   `L4Factoidal.XML` for the wire format; RDF/knowledge-graph modeling is
   a genuine sub-theme ("don't bog down in the RDF, it is a sub-theme"),
   reached for opportunistically for groups/PEP/PubSub if a good fit
   shows up, never a blocking dependency.
2. "Loosely coupled to other parts of L4Factoidal but defo part of it." →
   settles the module-location question: `L4Factoidal/XMPP/`, sibling to
   `CSVW/`/`MathML/`/`JOSE/`, not a separate Lake project.
3. "I don't know, find out" (re: what "regulated industry ready"
   concretely requires) → open research item, not urgent, no code depends
   on it yet.

### Still open

1. What does "regulated industry ready" concretely require (retention/
   eDiscovery/audit-log capability), and how is it kept separably opt-in
   from the private-by-default path? Owner: "I don't know, find out" —
   needs research, not a design call yet.
2. The MIMI e2e-vs-groups/AI tradeoff — what mechanism (if any) resolves
   it (see the TEE/Key-Transparency discussion, 2026-09-05/06 chat log) —
   not urgent, no code depends on this yet.

## Status

2026-09-07: module lives at `formal/lean4/L4Factoidal/XMPP/`, imported
from the root `L4Factoidal.lean`, builds as part of the main
`l4factoidal` package (`lake build` from `formal/lean4/`). Real, tested
modules so far:

- `Jid.lean` — RFC 7622 structural + length well-formedness. PRECIS
  enforcement explicitly not yet implemented (flagged in the module
  header, not silently skipped).
- `Wire.lean` — XMPP-specific glue over `L4Factoidal.XML`: `render`/
  `renderList` (serialization — new work, nothing to reuse), `parseElement`
  (delegates to `L4Factoidal.XML.parseXML`), and `parseOpenTag` (the one
  genuinely unsupported case — an unclosed `<stream:stream>` root; see
  "XML" section above for why this isn't a reimplementation of the real
  parser).
- `Core.lean` — `StreamHeader`/`StreamFeatures`/`ConnStage`/`featuresFor`
  (RFC 6120 negotiation, ordering made structural rather than checked)
  and `Stanza` (`message`/`presence`/`iq`), all built on
  `L4Factoidal.XML.Node`/`Attribute` and `Jid`. Round-trip and negative
  cases tested before the move to this location; retesting after the
  move is the immediate next step (see below).
- `Sasl.lean` — SCRAM (RFC 5802/7677) message format only (client-first/
  server-first/client-final/server-final parse+render); hash/HMAC
  computation deliberately not called from here yet (see Crypto section).
- `Gc3.lean` remains a scope-only stub — GC3 itself is still an
  early-stage, unfinished XSF spec.
- Not yet implemented: the actual TLS handshake, SASL hash/HMAC
  computation (needs HMAC-SHA-256 added to `L4Factoidal/Crypto/`),
  resource binding, stanza routing, MUC/MIX interop modules, and the BEAM
  host.
- **Retested after the move**: all round-trip/negative-case checks pass
  against the new `L4Factoidal.XML`-backed `Wire`/`Core`.
- **Tested against a live ejabberd instance** (the `foafmixer` pilot
  container, `localhost/foafmixer/ejabberd-mix:26.07-pilot`, running on
  `127.0.0.1:5222`), not just hand-written strings — per owner instruction
  2026-09-07 ("you can and should test against our ejabberd installation").
  Opened a raw TCP connection and captured ejabberd's actual
  `<stream:stream>` + `<stream:features>` response. This caught a real
  bug: `Wire.parseOpenTag` didn't expect the leading `<?xml version='1.0'?>`
  declaration real servers send (every hand-written test string had
  omitted it), so the first real capture failed to parse. Fixed
  (`Wire.skipXmlDecl`); the full, real, byte-for-byte capture now parses
  correctly (from/id/version/xml:lang all extracted) and the real
  `<stream:features>` element round-trips through the reused
  `L4Factoidal.XML` parser. This is exactly why "test against the real
  server" was worth doing over more hand-written strings — it found
  something hand-written tests didn't, on the first try.
- **Proved, not just tested** (owner instruction 2026-09-07: "make the
  most of Lean4 by actually proving interesting/useful things ... near-
  adversarial conditions"):
  - `Jid.parse_some_domain_nonempty` / `_localpart_nonempty` /
    `_resourcepart_nonempty` — for every input string, `parse` never
    returns a JID with an empty-but-present part. Required refactoring
    `Jid.parse` to route through a single `splitParts` helper with one
    guard chain and one constructor call (the original nested
    match-inside-if-inside-match shape produced unmanageable dependent-
    elimination goals) — a case where making code provable also made it
    more readable, not a tradeoff.
  - `Core.featuresFor_startTls_iff_preTls` / `_sasl_iff_postTls` /
    `_bind_iff_authenticated` / `_not_tls_and_bind` — the RFC 6120
    negotiation ordering as actual `iff` theorems, not prose: a future
    refactor that leaks SASL before TLS or bind before authentication
    fails to *compile*, not just fails a test someone has to think to
    write.
  - All seven theorems checked with `#print axioms`: only Lean's standard
    foundational axioms (`propext`, `Classical.choice`, `Quot.sound`,
    only where genuinely needed), no `sorry`, no custom escape hatch.
  - Adversarial `#eval` stress tests (empirical confirmation the
    fuel-bounded, non-`partial` parsers can't be hung or crashed by
    malicious input, on top of the termination guarantee Lean's kernel
    already enforces by accepting the definitions): 100,000 unmatched
    `<` characters, 20,000 attributes on one tag, 20,000 chained `&amp;`
    entities in one attribute value, 5,000 levels of element nesting
    (through the reused `L4Factoidal.XML` parser), and every truncation
    point of the real captured ejabberd stream-open tag — all return
    promptly, none hang, none crash.
- Nothing committed to git yet.
