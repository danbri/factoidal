# The Factoidal XMPP server — a deployment whose non-Lean part is one command

Owner, 2026-09-07: "a deployable, server-capable XMPP with the utter
minimum of non-Lean code (none if it can be pulled off)."

## The exact non-Lean line count

Everything in this directory, and nothing else in the running system,
is not Lean:

| file | lines | what it is |
|---|---|---|
| `Dockerfile` | 43 | fetch the repository, build one binary, put it in an image with socat |
| `entrypoint.sh` | 20 | choose the port and certificate, then run socat |
| `fly.toml` | 28 | Fly.io machine size, region, volume, ports |
| **total** | **91** | |

Counted with `grep -vE '^\s*#|^\s*$'` over the three files, 2026-09-07;
run it again rather than trusting this number. Most of the 91 is build
plumbing — a sparse git fetch, an elan toolchain install, a `lake build`
of one target. Of the 91, **one command carries the connection**:

```sh
socat OPENSSL-LISTEN:5223,reuseaddr,fork,cert=/certs/fullchain.pem,key=/certs/privkey.pem,verify=0 \
  EXEC:/opt/factoidal/bin/l4xmpp-serve,pipes
```

and the plaintext variant used for local tests:

```sh
socat TCP-LISTEN:5222,reuseaddr,fork \
  EXEC:/opt/factoidal/bin/l4xmpp-serve --plaintext,pipes
```

`socat` accepts a connection, terminates TLS, and forks one
`l4xmpp-serve` process with the socket on its standard input and output.
It never reads the stream: it does not know XMPP, does not frame stanzas,
and makes no decision about any of them.

No C, no JavaScript, no Go, no Erlang, no Lua. Zero lines of any of them
are involved in serving a connection.

## Why no C and no JavaScript are needed

Three things a server normally needs from a runtime, and where each one
comes from here:

1. **A socket.** `socat` provides it. The process reads standard input.
2. **TLS.** `socat`'s `OPENSSL-LISTEN` provides it. XEP-0368 (direct TLS
   on port 5223) is what makes this a complete answer rather than a
   partial one: with direct TLS the stream is encrypted from the first
   byte, so there is no STARTTLS step for the application to perform and
   no TLS library needs to be linked into the Lean binary. RFC 7590's
   requirements land on the carrier's OpenSSL, which is the code the
   world already audits for exactly this.
3. **One process per connection, isolated from the others.** `socat`'s
   `fork` provides it, and the operating system provides the isolation —
   a crashed session cannot take another down, because it is a different
   process.

What is left is protocol, and protocol is what Lean is for.

## What is Lean

| file | what it decides |
|---|---|
| `formal/lean4/L4Factoidal/XMPP/Jid.lean` | RFC 7622 addresses |
| `.../XMPP/Wire.lean` | rendering, and parsing through `L4Factoidal.XML` |
| `.../XMPP/Framing.lean` | where the next top-level unit of the stream ends |
| `.../XMPP/Core.lean` | the stream header, `<stream:features>`, stanzas, and the RFC 6120 ordering as theorems |
| `.../XMPP/Sasl.lean` | the SCRAM message grammar (RFC 5802) |
| `.../XMPP/Scram.lean` | the SCRAM-SHA-256 arithmetic (RFC 5802 section 3, RFC 7677) |
| `.../XMPP/Server.lean` | every remaining decision: SASL, binding, roster, presence, routing, stream errors |
| `formal/lean4/L4Factoidal/Crypto/Hmac.lean` | HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 |
| `formal/lean4/Harness/XmppServe.lean` | the I/O: read bytes, ask where a unit ends, call `step`, perform the result |

`Harness/XmppServe.lean` is Lean but is NOT part of the verified library:
it does file and stream I/O, the same boundary that keeps the W3C harness
out. It contains no protocol decision. Where it looked like it might —
"may this session receive a stanza that is waiting for it?" — the
question is asked of `Server.Session.canDeliver` rather than answered
locally.

## Deploying

```sh
fly deploy -c deploy/fly/xmpp/fly.toml --build-arg FACTOIDAL_REF=<sha>
```

Before the first deploy:

```sh
fly apps create factoidal-xmpp
fly volumes create xmpp_data -a factoidal-xmpp -r lhr -s 1
fly certs create -a factoidal-xmpp <your domain>      # or mount your own
```

Accounts are one `user:password` line each in `$XMPP_STATE/accounts` on
the volume. Set `XMPP_DOMAIN` to the domain the server is authoritative
for; a client that opens a stream naming any other domain gets
`host-unknown` (RFC 6120 section 4.9.3.6).

To run it locally with no TLS:

```sh
(cd formal/lean4 && lake build l4xmpp-serve)
mkdir -p /tmp/xmpp && printf 'juliet:r0m30\nromeo:juli3t\n' > /tmp/xmpp/accounts
socat TCP-LISTEN:5222,reuseaddr,fork \
  "EXEC:$PWD/formal/lean4/.lake/build/bin/l4xmpp-serve --domain localhost --state /tmp/xmpp --plaintext,pipes"
```

## What it speaks

Implemented, by specification section:

* RFC 6120 section 4.2 — stream open and `<stream:features>`
* RFC 6120 section 4.4 — `</stream:stream>`
* RFC 6120 section 4.9 — stream errors, including `host-unknown`,
  `not-well-formed`, `not-authorized`, `policy-violation`
* RFC 6120 section 6 — SASL: **PLAIN** (RFC 4616) and
  **SCRAM-SHA-256** (RFC 7677), and the section 6.4.6 stream restart
* RFC 6120 section 7 — resource binding, with a client-proposed or a
  server-assigned resource
* RFC 6120 section 8 — stanza addressing, and section 8.4's
  `service-unavailable` for an IQ nothing handles
* RFC 6121 section 2 — the roster: get, set, push, remove, persisted
* RFC 6121 section 3 — presence subscription (`subscribe`,
  `subscribed`), with the roster item updated
* RFC 6121 section 4 — presence broadcast to contacts whose
  subscription is `from` or `both`
* RFC 6121 section 8 — message delivery between sessions, with the
  `from` stamped by the server rather than trusted from the client
* XEP-0030 — a minimal `disco#info` reply
* XEP-0368 — direct TLS, by the carrier

Not implemented, and said here rather than left to be discovered:

* **STARTTLS** (RFC 6120 section 5). The carrier holds TLS. On the
  plaintext test listener there is no confidentiality at all, and
  `--plaintext` records that in the session.
* **SCRAM channel binding.** The process cannot see the TLS layer, so
  only `n` and `y` gs2 headers are accepted, never
  `p=tls-server-end-point`.
* **SCRAM-SHA-1.** `formal/lean4/L4Factoidal/Crypto/SHA1.lean` exists
  only as a pure-Lean codec for the SPARQL `SHA1()` builtin and its own
  header forbids using it "for integrity or authentication". RFC 7677 is
  the current mechanism, so SCRAM-SHA-256 and PLAIN are what is offered.
* **Server-to-server / federation** (RFC 6120 section 4.9.3.4 and the
  dialback family). One process, one client connection.
* **GC3 rooms.** `L4Factoidal/XMPP/Gc3.lean` is a scope-only stub: the
  XSF specification is unfinished, so implementing rooms would be
  inventing a wire format rather than implementing one.
* **PRECIS** (RFC 8264 / 8265) enforcement on JID parts. `Jid.lean`
  checks structure and length only, and says so.

## Known limits of this first slice

* **Accounts are a plaintext file, and one salt serves all of them.**
  `Scram.credentialsOfPassword` derives the stored keys at
  authentication time from the password on disk. RFC 5802 wants a
  per-account salt and a server that never holds the password;
  `Scram.StoredCredentials` is already the right shape for that, and the
  change is an account-file format, not a protocol change.
* **A SCRAM login costs two 4096-iteration PBKDF2 runs.** Measured
  2026-09-07 against the compiled binary: 67 ms for the challenge and
  72 ms for the response, so about 140 ms of CPU per SCRAM login. (The
  same derivation in the Lean *interpreter* takes about seventy seconds,
  which is why `Scram.lean`'s build-time checks use stored keys as
  constants rather than deriving them.) It is per login rather than per
  account because the account file holds a password; storing the derived
  keys removes both runs. PLAIN costs nothing extra.
* **Routing between connections is a directory of files.** One file per
  stanza under `$XMPP_STATE/spool/<bare jid>/`, polled every 50 ms by a
  task beside the read loop. It is inspectable when a test fails, and it
  is not fast. `Server.Out.route` names a destination and a payload, not
  a file, so a socket-pair or shared-memory carrier replaces it without
  touching `L4Factoidal/XMPP/`.
* **No message archive.** A stanza for an account with no bound session
  waits in the spool until one binds; nothing expires it.

## Tests

```sh
node tests/xmpp/server.mjs      # the RFC sequences, through the live binary
bash tools/xmpp-interop.sh      # @xmpp/client, over a real socket, through socat
```

`tools/xmpp-interop.sh` exits **2** with a reason when socat or
`@xmpp/client` is missing. It never reports a green skip: "the interop
did not run" and "the interop passed" are different facts.
