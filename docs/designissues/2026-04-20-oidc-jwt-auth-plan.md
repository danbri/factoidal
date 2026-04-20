# Self-hosted OIDC / JWT verification for factoidal-http — plan 2026-04-20

Companion to the auth-layer design already landed in `46f7104`
(trusted-header mode). This doc scopes what it takes to let
factoidal-http accept a `Bearer <JWT>` from any OIDC provider
without trusting an intermediary proxy.

## Why a second auth mode at all?

Trusted-header mode (commit `46f7104`) works beautifully when
Cloudflare Access (or a similar gateway) is doing the real
authentication. The server just believes the header CF sets because
nobody else can reach the 127.0.0.1 port. Two downsides:

1. **Requires Cloudflare** (or some proxy you run yourself). Can't
   authenticate "just" from a direct hit.
2. **No signature check**: if the bind-to-localhost assumption breaks
   (accidental bind to 0.0.0.0, container network mistake), anyone
   can spoof the header and impersonate any user.

OIDC mode lets factoidal-http verify the identity itself against a
known issuer's public keys. No trusted intermediary required.

## What "OIDC" means here (minimally)

The user presents `Authorization: Bearer <JWT>`. The JWT is signed
by some issuer (Google, Auth0, Keycloak, Okta, Zitadel, a homegrown
IDP). factoidal-http:

1. Parses the JWT header for `kid` (key ID) and `alg`.
2. Looks up the key by `kid` in a **JWKS** (JSON Web Key Set) fetched
   from the issuer's `.well-known/openid-configuration` →
   `jwks_uri`.
3. Verifies the signature.
4. Checks `iss` matches the configured issuer, `aud` matches the
   configured audience, `exp` is in the future, `nbf` is in the past.
5. Extracts a claim as the authid (default `email`; configurable).

That authid flows into the same per-user-graph sandbox already built
in `46f7104`.

## Proposed flags

| Flag | Purpose | Default |
|---|---|---|
| `--oidc-issuer=URL` | OIDC discovery endpoint root, e.g. `https://accounts.google.com` | unset (OIDC off) |
| `--oidc-audience=STR` | Required `aud` claim value | unset — must set or startup errors |
| `--oidc-claim-authid=NAME` | Which JWT claim becomes the authid | `email` |
| `--oidc-jwks-refresh=SECS` | JWKS cache TTL | `86400` (1 day) |
| `--oidc-jwks-file=FILE` | Skip discovery — use static JWKS JSON from disk | unset |
| `--auth-log-dir=DIR` | Directory for auth-event log | `./tmp/auth-events_gdpr-may-contain-pii-rotate-me/` |

`--oidc-issuer` is the headline switch. If set, factoidal-http
requires a valid JWT on `POST /update`. `GET /query` remains
unauthenticated by default (public reads); a future
`--oidc-gate-queries` flag could tighten that.

Interaction with `--auth-header` (the existing trusted-header mode):
- Both unset → fallback to `--read-only`'s behaviour (anonymous
  reads, UPDATE 403).
- Only `--auth-header` set → trusted-header mode (current
  `46f7104` behaviour).
- Only `--oidc-issuer` set → JWT verification mode.
- Both set → OIDC verification wins; if no Bearer token present,
  fall back to the trusted header (useful for a transition period).

## Dependencies (opam)

The work needs:

1. **Signature verification**: `mirage-crypto` + `mirage-crypto-pk`
   for RSA-SHA256 (`RS256`). Most OIDC providers sign with `RS256`;
   Google does. `ES256` (ECDSA P-256) is also common enough to
   support in a v1 (`mirage-crypto-ec`).
2. **HTTP fetch** for the JWKS: `cohttp-lwt-unix` (already blessed
   by the SERVICE plan). Or hand-rolled TLS via `tls` + `lwt` since
   we only fetch once per refresh interval.
3. **JSON parsing**: `yojson` — probably already transitively pulled
   by `jose`; add it explicitly.
4. **JWT parsing wrapper**: `jose` (opam) bundles all three of the
   above into a `Jose.Jwt.verify` / `Jose.Jwks.find` API. If `jose`
   works cleanly, use it; if its transitive deps balloon the binary
   or fight our build setup, fall back to a hand-rolled 120-line
   minimum using `mirage-crypto-pk` + `yojson` directly.

Risk: `jose` hasn't seen aggressive maintenance in a while; check
its last release date and opam compatibility with OCaml 4.14.1
before committing. If it's stale, go hand-rolled.

**Linkage**: native only. js_of_ocaml / wasm_of_ocaml builds don't
need it — the Protocol server is native-only.

## Startup flow

```
1. Parse flags.
2. If --oidc-issuer set:
   a. Fetch <issuer>/.well-known/openid-configuration → jwks_uri.
   b. Fetch jwks_uri → JWKS JSON, cache.
   c. Start a background refresh timer (Unix.setitimer or
      a simple loop on a sleeping fiber).
3. Start the accept loop.
```

If step (a) or (b) fails, print to stderr and exit 1 — OIDC mode is
unusable without a cached JWKS.

## Per-request flow

```
1. Extract Authorization header. Strip "Bearer " prefix.
2. Parse JWT: split on '.', base64url-decode header + payload.
3. Look up key by kid in cached JWKS. If missing:
   a. If JWKS last refresh was > refresh_interval / 2 ago,
      force-refresh once and retry.
   b. Otherwise 401 "unknown key id".
4. Verify signature with key.alg + key.n + key.e.
5. Check iss == configured issuer; aud contains configured audience;
   exp > now; nbf < now (if present).
6. Extract claim[authid-claim-name] → authid string.
7. Continue into existing rewrite-to-user-graph path.
```

Any failure → 401 with `WWW-Authenticate: Bearer error="..."`.

## Auth-event log (GDPR concerns)

User's request: auth events logged but flagged as accumulating
GDPR burden. Proposal:

- Log every authn attempt (success OR failure) to
  `<auth-log-dir>/auth-YYYYMMDD.jsonl`, one JSON object per line:
  ```
  {"ts":"2026-04-20T12:34:56Z","ip":"10.1.2.3","status":"ok",
   "authid":"alice@example.com","kid":"abc123","iss":"https://.../"}
  ```
- The log-dir name itself carries the warning
  (`auth-events_gdpr-may-contain-pii-rotate-me`). Same pattern as
  the RW-graphs dump dir (`autoexec.bot-llms_exclude-...`) — the
  path is the documentation.
- Auto-write a `README.md` into the log-dir the first time:
  - What's stored (IP, email, kid, iss, outcome).
  - Why it's kept (auditability).
  - What to do about it (rotate periodically, pseudonymise if
    publishing, delete on user request per Art. 17).
  - Suggested retention policy (30 days by default; document
    breach-detection trade-offs if shorter).
- Optional `--auth-log-redact-ip=true` flag to hash the IP field
  with a rotating per-day salt — good default for anyone who
  doesn't need IP-level auditing.

Rotation is NOT factoidal's job. The path warning + README nudge
the operator to run `logrotate` or equivalent.

## Staged rollout

1. **OIDC v0** (one subagent, ~300 LOC): `--oidc-jwks-file` (static
   JWKS from disk, no discovery fetch), RS256 signature verify,
   claim extraction, integrate with existing authid path. No log
   dir yet; stderr audit only.
2. **OIDC v1**: add `--oidc-issuer` with discovery + live JWKS fetch
   + 24 h refresh timer.
3. **OIDC v2**: auth-event log file with the GDPR-flagged directory
   + README.
4. **OIDC v3**: ES256 support, optional `--oidc-gate-queries` for
   authenticated-only reads, `--oidc-required-scope=STR` for
   coarse scope check.

v0 is a single subagent session (~3-5 hours for a competent one).
v1 adds HTTP client + timer (2-3 hrs). v2 is log formatting (1 hr).
v3 is polish.

## Honest caveats for downstream users

- Token revocation is NOT supported (no introspection endpoint
  call). A revoked token remains valid until its `exp`. Issue short
  tokens (< 15 min) and rely on expiry.
- `offline_access` refresh flows are not handled — factoidal-http
  only verifies the access token presented.
- Audience binding is per-factoidal deployment: set a unique `aud`
  (e.g. `urn:factoidal:my-instance`) in your IDP and require it
  via `--oidc-audience`. Otherwise any token for the same issuer
  (e.g. "a Google login") passes.

## Design hole to fix in parallel

The per-user-graph sandbox currently accepts the authid verbatim
into the graph IRI template. If the IDP emits an email with
characters that need URI-escaping (unlikely — RFC 5321 mostly
reserves those — but possible with unusual `sub` values), the
graph IRI might be malformed. Add a sanity check: authid must
match a restricted character class, else 400. Out of scope for
this plan but noted so the first OIDC commit can land it.
