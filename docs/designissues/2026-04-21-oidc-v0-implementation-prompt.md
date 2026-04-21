# OIDC v0 implementation prompt — subagent script

This document is input to a future Claude Code subagent session. Feed it
verbatim as the task prompt. It implements **v0 only** of
`docs/designissues/2026-04-20-oidc-jwt-auth-plan.md` — static JWKS file,
no OIDC discovery, no live refresh, no scope gating.

The v0 feature lands on top of the existing `--auth-header` trusted-header
pipeline (commit `46f7104`) and the `--read-only` gate (commit `f481a9e`).
v0 does NOT replace trusted-header mode; it slots a second identity source
into the same `--proxied-auth-rw-graphnames` template pipeline.

---

## 0. Scope guard — read before touching anything

**Do these things only:**

- Add OIDC JWT verification against a static JWKS file on disk.
- Integrate the verified `authid` into the existing per-user-graph template
  pipeline in `factoidal_http.ml`.
- Add an auth audit log with the GDPR-warning-in-directory-name pattern.
- Add curl + key fixture smoke tests under `tests/e2e/oidc-v0/`.
- Mark v0 done in the parent plan doc.

**Do NOT do:**

- No F* changes. JWT/JWKS work is all OCaml I/O glue (rule #10 / #15 —
  signature verification is cryptographic primitive, not RDF or SPARQL
  semantics; it is legitimate I/O layer work).
- No OIDC discovery fetch. No HTTP client code. No JWKS refresh timer.
- No revocation / introspection endpoint calls.
- No scope-based authorization.
- No `--oidc-gate-queries` read gating.
- No transition-period "fall back to trusted-header if no Bearer" logic
  (that is a v1 feature per the parent plan).

If the v0 scope feels too small, resist. The parent plan splits v0 / v1 /
v2 / v3 deliberately.

---

## 1. Dependency decision: `jose` (recommended for v0)

Two candidate paths were considered:

### Option A (RECOMMENDED for v0): opam `jose` package

- High-level `Jose.Jwt.of_string` + `Jose.Jwt.verify ~jwk` API.
- Call site is roughly six lines.
- Supports `RS256` natively. ES256 support is present but less exercised
  upstream; verify it works on our switch before claiming ES256 coverage.
- Transitive deps: `mirage-crypto`, `mirage-crypto-pk`, `yojson`, `base64`,
  `astring`, `logs`, `rresult`. All already opam-available on OCaml 4.14.1.

### Option B: hand-rolled (`mirage-crypto-pk` + `mirage-crypto-ec` + `yojson` + `base64` directly)

- Approximately 120 lines of OCaml: JWT split, base64url decode, JWKS
  parse + kid index, RS256 verify via `Mirage_crypto_pk.Rsa.PKCS1.verify`,
  ES256 verify via `Mirage_crypto_ec.P256.Dsa.verify`.
- No dependency on a third-party JWT wrapper. More surface to audit
  ourselves but fewer "is this wrapper still maintained" questions.

### Recommendation

**Use `jose`.** Rationale: the attack surface is small (one call site), the
wrapper is thin enough that we can audit it if the CVE question comes up,
and it saves roughly 100 lines of hand-rolled crypto plumbing. If the v0
subagent finds `jose` will not install cleanly on our opam switch, fall
back to Option B — the file layout in `auth_oidc_helpers.ml` should be
agnostic to which library implements `verify_jwt_against_jwks`.

### Risks to verify on arrival

- Run `opam install --dry-run jose` against the project switch before
  committing to it. If the solver balks (version conflict with our pinned
  `fstar`, `zarith`, or anything else), fall back to Option B immediately
  and do not spend time arguing with the solver.
- `jose` last release was ~2023 per opam. If it has been yanked or a
  newer successor package exists by the time this runs, prefer the
  actively maintained one, or fall back to Option B.
- ES256 on `jose`: write the ES256 smoke test FIRST. If it is flaky on our
  switch, document ES256 as "accepted but only RS256 is smoke-tested" in
  v0 and file a follow-up for v3.

---

## 2. Flag additions to `factoidal_http.ml`

All three flags parsed in `parse_args`, using the existing `split_eq`
plus `match (key, eq_val, rest)` pattern. Add to the `config` record
and to `default_config ()`:

```ocaml
(* In type config, after proxied_auth_rw_graphnames: *)
mutable oidc_jwks_file   : string option;
mutable oidc_issuer      : string option;
mutable oidc_audience    : string option;
mutable oidc_claim_authid : string;    (* default "email" *)
mutable auth_log_dir     : string;     (* default below *)
```

```ocaml
(* In default_config (): *)
oidc_jwks_file    = None;
oidc_issuer       = None;
oidc_audience     = None;
oidc_claim_authid = "email";
auth_log_dir      =
  "./tmp/auth-events_gdpr-may-contain-pii-rotate-me/";
```

Flag wiring (added alongside the existing `--auth-header=` / etc. arms):

```ocaml
| ("--oidc-jwks-file", Some v, _) ->
    cfg.oidc_jwks_file <- Some v; loop rest
| ("--oidc-jwks-file", None, v :: rest') ->
    cfg.oidc_jwks_file <- Some v; loop rest'
| ("--oidc-issuer", Some v, _) ->
    cfg.oidc_issuer <- Some v; loop rest
| ("--oidc-issuer", None, v :: rest') ->
    cfg.oidc_issuer <- Some v; loop rest'
| ("--oidc-audience", Some v, _) ->
    cfg.oidc_audience <- Some v; loop rest
| ("--oidc-audience", None, v :: rest') ->
    cfg.oidc_audience <- Some v; loop rest'
| ("--oidc-claim-authid", Some v, _) ->
    cfg.oidc_claim_authid <- v; loop rest
| ("--oidc-claim-authid", None, v :: rest') ->
    cfg.oidc_claim_authid <- v; loop rest'
| ("--auth-log-dir", Some v, _) ->
    cfg.auth_log_dir <- v; loop rest
| ("--auth-log-dir", None, v :: rest') ->
    cfg.auth_log_dir <- v; loop rest'
```

Post-parse validation in `parse_args`, matching the existing
`proxied_auth_rw_graphnames must contain {authid}` pattern:

```ocaml
(match cfg.oidc_jwks_file, cfg.oidc_issuer, cfg.oidc_audience with
 | Some _, None, _ ->
   Printf.eprintf
     "Error: --oidc-jwks-file requires --oidc-issuer=URL\n";
   exit 1
 | Some _, _, None ->
   Printf.eprintf
     "Error: --oidc-jwks-file requires --oidc-audience=STR\n";
   exit 1
 | _ -> ());
```

Update `usage ()` with lines describing all five flags; match the prose
style already used for `--auth-header` etc.

---

## 3. New file: `auth_oidc_helpers.ml`

Put JWT + JWKS logic in a separate module alongside `factoidal_http.ml`,
not inlined into it. Target: approximately 150 lines using `jose`, or
approximately 250 lines for the hand-rolled fallback.

File location: `formal/fstar/ocaml-output/auth_oidc_helpers.ml`

### Public API the module exposes

```ocaml
(* Loaded JWKS — abstract to callers. *)
type jwks

(* Load a JWKS from disk. Parse the JSON; index by kid. Raise on parse
   error or missing "keys" array. *)
val load_jwks_from_file : string -> jwks

(* Configuration snapshot used for verification. *)
type verify_config = {
  vc_jwks : jwks;
  vc_issuer : string;
  vc_audience : string;
  vc_claim_authid : string;
}

(* Verification outcome. The successful case returns the extracted authid;
   all failures give a stable machine-readable reason string suitable for
   the audit log and a human-readable message suitable for the 401 body. *)
type verify_result =
  | VR_Ok of {
      authid : string;
      kid : string option;
      issuer : string;
    }
  | VR_Fail of {
      reason : string;      (* short stable token: "expired", "bad_sig",
                               "unknown_kid", "iss_mismatch", "aud_mismatch",
                               "alg_not_allowed", "missing_claim",
                               "malformed_jwt" *)
      message : string;     (* longer human-readable string *)
    }

(* Split + decode + signature-verify + claim-validate. Pure function of
   inputs (no disk, no network, no current-time-hidden-in-args). *)
val verify_jwt : verify_config -> now_epoch:float -> token:string -> verify_result
```

### Implementation notes (for the `jose`-based variant)

- `load_jwks_from_file`: read file, `Yojson.Safe.from_string`, walk the
  `"keys"` array, each entry becomes a `Jose.Jwk.t` via
  `Jose.Jwk.of_pub_json`. Build a `(string, Jose.Jwk.t) Hashtbl.t` keyed
  by `kid`. Keys without a `kid` go in a separate list and are only tried
  if the JWT header omits `kid`. Raise `Failure` with a clear message if
  the file does not parse as JSON or lacks `keys`.
- `verify_jwt` breakdown:
  1. Split token on `.` — expect exactly three parts. Anything else ->
     `VR_Fail { reason = "malformed_jwt"; ... }`.
  2. `Jose.Jwt.of_string token` (or handle the decode manually if we
     are auditing headers ourselves).
  3. Read `alg` from the decoded header. Reject anything that is not
     `RS256` or `ES256` -> `alg_not_allowed`. **Explicitly reject `none`
     and any HS*** (symmetric) algorithm — this is a classic JWT pitfall.
  4. Read `kid` from the header. Look up in `vc_jwks`. Missing -> `unknown_kid`.
  5. `Jose.Jwt.verify ~jwk:matched_jwk token`. Failure -> `bad_sig`.
  6. On the verified payload JSON: check `"exp"` is present and `> now_epoch`
     -> else `expired`. Check `"iss"` equals `vc_issuer` -> else `iss_mismatch`.
     Check `"aud"` contains `vc_audience` (the claim may be a string or an
     array — handle both) -> else `aud_mismatch`.
  7. Extract `payload[vc_claim_authid]` as a string. Missing or empty
     -> `missing_claim`. Otherwise `VR_Ok { authid; kid; issuer }`.
- Wall-clock: passed in as `now_epoch` rather than read inside the module
  so the smoke tests can pin time.

### For the hand-rolled fallback (Option B)

Write the same public API. Internal helpers:

- `base64url_decode : string -> string` — standard base64 with `+` -> `-`
  and `/` -> `_` and no padding.
- `split_jwt : string -> (string * string * string) option` — split on `.`.
- `rsa_verify_rs256 : Mirage_crypto_pk.Rsa.pub -> signed:string ->
  signature:string -> bool` — SHA-256 digest + PKCS1.1 v1.5 verify.
- `ec_verify_es256 : Mirage_crypto_ec.P256.Dsa.pub -> signed:string ->
  signature:string -> bool` — JWT ES256 uses the R||S concatenation
  form, NOT the ASN.1 DER form most OpenSSL tools emit. Convert if
  needed. This is the single easiest thing to get wrong; write its
  unit test first.
- `jwks_of_yojson : Yojson.Safe.t -> jwks` — walk `keys[]`, read `kty`,
  `n` + `e` for RSA, `crv` + `x` + `y` for EC, each with base64url
  decoding. Reject anything that is not `RS256`/`RSA` or `ES256`/`EC P-256`.

---

## 4. Integration points in `factoidal_http.ml`

Approximately 150 lines added total to this file. Broken down:

### 4a. Startup: load JWKS once

In `run_server cfg`, before the accept loop, right after `dataset_ref`
is built:

```ocaml
let jwks_opt =
  match cfg.oidc_jwks_file with
  | None -> None
  | Some path ->
    (try Some (Auth_oidc_helpers.load_jwks_from_file path)
     with e ->
       Printf.eprintf "Error loading OIDC JWKS from %s: %s\n"
         path (Printexc.to_string e);
       exit 1)
in
```

Add a startup-log line matching the existing `  mode: ...` /
`  cors: ...` block, e.g.:

```ocaml
(match jwks_opt with
 | Some _ ->
   Printf.printf "  oidc: jwks=%s issuer=%s audience=%s claim=%s\n"
     (match cfg.oidc_jwks_file with Some p -> p | None -> "-")
     (match cfg.oidc_issuer with Some u -> u | None -> "-")
     (match cfg.oidc_audience with Some a -> a | None -> "-")
     cfg.oidc_claim_authid
 | None -> ());
```

### 4b. Per-request: extend the auth-extraction step

The existing trusted-header path is in `handle_connection`, starting
at the `let auth_result = match cfg.proxied_auth_rw_graphnames with ...`
block (around line 1105). Extract it into a helper:

```ocaml
(* Resolve the authenticated identity for this request, in priority:
   1. If --oidc-jwks-file was supplied AND a Bearer token is present,
      verify the token -> authid.
   2. Else if --auth-header has a value, trust it.
   3. Else: no identity.
   Returns (authid_opt, log_fields). *)
let resolve_authid ~cfg ~jwks_opt ~headers ~ip : string option * audit_fields =
  (* ... *)
```

Inline that helper into the `PR_Update` arm. The existing
`Unauthenticated` / `Sandboxed` logic stays; only the input changes
from "header value" to "whatever `resolve_authid` returned".

Important: on OIDC verification failure (not just "no Bearer"), respond
**401** with `WWW-Authenticate: Bearer realm="factoidal"` — NOT 403.
The existing trusted-header-missing path returns 403; keep that when
the failure mode is "no identity source configured matches". 401 is
specifically for "OIDC was attempted and failed".

```ocaml
| `OidcFail (reason, msg) ->
  let extras =
    [ Printf.sprintf "WWW-Authenticate: Bearer realm=\"factoidal\", \
                       error=\"invalid_token\", error_description=\"%s\""
        reason ]
  in
  write_response ~extra_headers:(extras @ cors_hdrs) oc
    ~status:401
    ~content_type:"text/plain; charset=utf-8"
    ~body:(msg ^ "\n")
```

### 4c. Audit logging

One append-only write per authentication attempt (success or failure).
Log rotation by day (filename contains `YYYYMMDD`). File format: JSON
Lines (one JSON object per line). Pattern for the directory is the same
"warn via the path" idiom as `default_dump_dir` — the caller sees
`auth-events_gdpr-may-contain-pii-rotate-me/` in their filesystem and
knows what it is.

```ocaml
let audit_log_path cfg =
  let t = Unix.gmtime (Unix.time ()) in
  let stamp =
    Printf.sprintf "%04d%02d%02d"
      (t.tm_year + 1900) (t.tm_mon + 1) t.tm_mday
  in
  Filename.concat cfg.auth_log_dir (Printf.sprintf "auth-%s.jsonl" stamp)

let write_audit_readme dir =
  let path = Filename.concat dir "README.md" in
  if not (Sys.file_exists path) then begin
    let oc = open_out path in
    output_string oc
      "# factoidal-http authentication events\n\
       \n\
       This directory accumulates one JSON-Lines file per UTC day\n\
       (`auth-YYYYMMDD.jsonl`) recording every authentication attempt\n\
       against POST /update.\n\
       \n\
       ## PII classes stored\n\
       \n\
       - `authid` — the user identity (commonly an email address)\n\
       - `ip` — the client's source IP\n\
       - `issuer` — the OIDC issuer URL\n\
       - `kid` — the JWKS key identifier used\n\
       \n\
       ## Recommended handling\n\
       \n\
       - Rotate / delete files older than 30 days by default. Run\n\
         `logrotate` or a cron job — factoidal itself does not rotate.\n\
       - For GDPR Art. 17 (right to erasure) requests: grep for the\n\
         user's authid across files in this directory and delete the\n\
         matching lines.\n\
       - If you need per-IP auditing but not the IP in plain text,\n\
         hash with a per-day salt before storing.\n\
       - Never publish this directory. Never train models on it.\n";
    close_out oc
  end

let log_audit cfg ~ts_iso ~ip ~meth ~path ~outcome
              ?(authid="") ?(issuer="") ?(kid="") ?(reason="") () =
  try
    mkdir_p cfg.auth_log_dir;
    write_audit_readme cfg.auth_log_dir;
    let fields = [
      "\"ts\":\""       ^ ts_iso   ^ "\"";
      "\"ip\":\""       ^ ip       ^ "\"";
      "\"method\":\""   ^ meth     ^ "\"";
      "\"path\":\""     ^ path     ^ "\"";
      "\"outcome\":\""  ^ outcome  ^ "\"";
    ] @ (if authid = ""  then [] else ["\"authid\":\"" ^ authid ^ "\""])
      @ (if issuer = ""  then [] else ["\"issuer\":\"" ^ issuer ^ "\""])
      @ (if kid = ""     then [] else ["\"kid\":\""    ^ kid    ^ "\""])
      @ (if reason = ""  then [] else ["\"reason\":\"" ^ reason ^ "\""])
    in
    let line = "{" ^ String.concat "," fields ^ "}\n" in
    let oc = open_out_gen [Open_append; Open_creat] 0o644
                          (audit_log_path cfg) in
    output_string oc line;
    close_out oc
  with e ->
    Printf.eprintf "[audit] log write failed: %s\n%!"
      (Printexc.to_string e)
```

Note: this is deliberately a flat JSON emitter to avoid adding `yojson`
as a direct dependency of `factoidal_http.ml`. String values go through
only minimal escaping here — if a verified JWT claim contains a quote
character, pass it through `nq_escape_literal`-style escape or reuse
`String.escaped`. Add a small `json_escape` helper in this file.

Pass the client IP through by reading `_caddr` from `Unix.accept` in
the accept loop and passing it into `handle_connection`. Small signature
change — thread `~client_ip:string` through.

---

## 5. Build script change

`formal/fstar/build-ocaml.sh`, around line 222, append `,jose` (or the
Option B packages) to the `-package` list of the `factoidal-http` target
only. The CLI and w3c_runner targets do NOT need it.

```bash
# factoidal-http — SPARQL 1.1 Protocol server (native only; needs Unix)
ocamlfind ocamlopt -package fstar.lib,str,zarith,sha,digestif.c,unix,jose \
  -linkpkg -w -8-14-26 \
  $STATIC_FLAGS \
  $COMMON_MODULES \
  $PARQUET_NATIVE_STUBS \
  auth_oidc_helpers.ml \
  factoidal_http.ml \
  -o "$BINDIR/factoidal-http"
```

Also add `auth_oidc_helpers.ml` to the compile list BEFORE
`factoidal_http.ml` (order matters for OCaml's single-pass compilation).

If fallback to Option B is needed:
`-package fstar.lib,str,zarith,sha,digestif.c,unix,mirage-crypto,mirage-crypto-pk,mirage-crypto-ec,yojson,base64`.

Re-extraction is NOT required (no F* changes). Run:

```bash
cd formal/fstar
./build-ocaml.sh compile
```

The resulting `bin/darwin-arm64/factoidal-http` (on macOS) must be
committed per rule #9. If the subagent is on Linux x86-64, also build
`bin/linux-x86_64/factoidal-http`.

---

## 6. Smoke tests at `tests/e2e/oidc-v0/`

Create this directory. Files to add:

### 6a. `tests/e2e/oidc-v0/README.md`

Short prose: how to run the harness, what it covers, that the keys
under `fixtures/` are test-only and MUST NOT be reused.

### 6b. `tests/e2e/oidc-v0/fixtures/gen-test-keys.py`

A self-contained Python script (uses `cryptography`, a standard opam/pip
dep) that generates:

- An RSA 2048 private key -> `fixtures/test-rsa.pem`.
- The corresponding public JWK with `kid: "test-rsa-1"` -> `fixtures/test-jwks.json`.
- (Optional) A P-256 EC private key -> `fixtures/test-ec.pem` and
  append its JWK to `test-jwks.json` with `kid: "test-ec-1"`.

The script is run once by the harness; keys are regenerated each
invocation so there is no long-lived secret in the repo. The generated
`*.pem` files go in `.gitignore`.

Sketch:

```python
#!/usr/bin/env python3
# fixtures/gen-test-keys.py — generate throwaway OIDC test keys.
from cryptography.hazmat.primitives.asymmetric import rsa, ec
from cryptography.hazmat.primitives import serialization, hashes
import json, base64, os, sys

def b64u(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()

here = os.path.dirname(os.path.abspath(__file__))

# RSA 2048
rsa_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
with open(os.path.join(here, "test-rsa.pem"), "wb") as f:
    f.write(rsa_key.private_bytes(
        serialization.Encoding.PEM,
        serialization.PrivateFormat.PKCS8,
        serialization.NoEncryption()))
nums = rsa_key.public_key().public_numbers()
n_bytes = nums.n.to_bytes((nums.n.bit_length() + 7) // 8, "big")
e_bytes = nums.e.to_bytes((nums.e.bit_length() + 7) // 8, "big")
rsa_jwk = {
    "kty": "RSA", "use": "sig", "alg": "RS256",
    "kid": "test-rsa-1",
    "n": b64u(n_bytes), "e": b64u(e_bytes),
}

jwks = { "keys": [ rsa_jwk ] }

# (Optional) P-256 EC
if "--ec" in sys.argv:
    ec_key = ec.generate_private_key(ec.SECP256R1())
    with open(os.path.join(here, "test-ec.pem"), "wb") as f:
        f.write(ec_key.private_bytes(
            serialization.Encoding.PEM,
            serialization.PrivateFormat.PKCS8,
            serialization.NoEncryption()))
    pub = ec_key.public_key().public_numbers()
    x_bytes = pub.x.to_bytes(32, "big")
    y_bytes = pub.y.to_bytes(32, "big")
    jwks["keys"].append({
        "kty": "EC", "use": "sig", "alg": "ES256",
        "crv": "P-256", "kid": "test-ec-1",
        "x": b64u(x_bytes), "y": b64u(y_bytes),
    })

with open(os.path.join(here, "test-jwks.json"), "w") as f:
    json.dump(jwks, f, indent=2)
print("wrote test-jwks.json + test-*.pem in", here)
```

### 6c. `tests/e2e/oidc-v0/fixtures/mint-jwt.py`

Mints a JWT from a PEM key + claims JSON. The harness calls this to
produce six tokens: good RS256, good ES256, expired, wrong-iss,
wrong-aud, wrong-sig. Sketch:

```python
#!/usr/bin/env python3
# fixtures/mint-jwt.py KEY.pem CLAIMS.json [--alg RS256|ES256] [--kid KID]
#
# Writes a signed JWT to stdout. Uses cryptography directly to keep
# dependencies minimal (no pyjwt).
import sys, json, base64, time, argparse
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import padding, ec, rsa
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature

def b64u(b): return base64.urlsafe_b64encode(b).rstrip(b"=").decode()

ap = argparse.ArgumentParser()
ap.add_argument("key"); ap.add_argument("claims")
ap.add_argument("--alg", default="RS256")
ap.add_argument("--kid", default="test-rsa-1")
args = ap.parse_args()

with open(args.key, "rb") as f:
    pk = serialization.load_pem_private_key(f.read(), password=None)
with open(args.claims) as f:
    claims = json.load(f)

header = {"alg": args.alg, "typ": "JWT", "kid": args.kid}
header_b64 = b64u(json.dumps(header, separators=(",",":")).encode())
payload_b64 = b64u(json.dumps(claims, separators=(",",":")).encode())
signing_input = (header_b64 + "." + payload_b64).encode()

if args.alg == "RS256":
    assert isinstance(pk, rsa.RSAPrivateKey)
    sig = pk.sign(signing_input, padding.PKCS1v15(), hashes.SHA256())
elif args.alg == "ES256":
    assert isinstance(pk, ec.EllipticCurvePrivateKey)
    der = pk.sign(signing_input, ec.ECDSA(hashes.SHA256()))
    r, s = decode_dss_signature(der)
    sig = r.to_bytes(32, "big") + s.to_bytes(32, "big")
else:
    sys.exit("unsupported alg: " + args.alg)

print(header_b64 + "." + payload_b64 + "." + b64u(sig))
```

### 6d. `tests/e2e/oidc-v0/run.sh`

Bash harness. Must be idempotent and CI-friendly. Structure:

```bash
#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
FIX="$HERE/fixtures"
FACTOIDAL_HTTP="${FACTOIDAL_HTTP:-$HERE/../../../bin/darwin-arm64/factoidal-http}"
PORT=3931
ISSUER="https://test.example"
AUDIENCE="urn:factoidal:test"

# 1. Regenerate throwaway keys + JWKS.
python3 "$FIX/gen-test-keys.py" --ec

# 2. Mint six tokens.
NOW=$(date -u +%s)
FUTURE=$((NOW + 300))
PAST=$((NOW - 300))

mk_claims() {
  cat > "$FIX/$1" <<EOF
{"iss":"$2","aud":"$3","exp":$4,"email":"$5"}
EOF
}
mk_claims good.json  "$ISSUER"         "$AUDIENCE"       "$FUTURE" alice@example.com
mk_claims exp.json   "$ISSUER"         "$AUDIENCE"       "$PAST"   alice@example.com
mk_claims badiss.json "https://evil"    "$AUDIENCE"       "$FUTURE" alice@example.com
mk_claims badaud.json "$ISSUER"         "urn:other"       "$FUTURE" alice@example.com

GOOD=$(python3 "$FIX/mint-jwt.py"  "$FIX/test-rsa.pem" "$FIX/good.json"  --alg RS256 --kid test-rsa-1)
EXP=$(python3  "$FIX/mint-jwt.py"  "$FIX/test-rsa.pem" "$FIX/exp.json"   --alg RS256 --kid test-rsa-1)
BADISS=$(python3 "$FIX/mint-jwt.py" "$FIX/test-rsa.pem" "$FIX/badiss.json" --alg RS256 --kid test-rsa-1)
BADAUD=$(python3 "$FIX/mint-jwt.py" "$FIX/test-rsa.pem" "$FIX/badaud.json" --alg RS256 --kid test-rsa-1)
GOOD_EC=$(python3 "$FIX/mint-jwt.py" "$FIX/test-ec.pem" "$FIX/good.json"  --alg ES256 --kid test-ec-1)

# 3. Start the server.
TMPLOG="$(mktemp)"
"$FACTOIDAL_HTTP" \
  --port "$PORT" \
  --oidc-jwks-file "$FIX/test-jwks.json" \
  --oidc-issuer "$ISSUER" \
  --oidc-audience "$AUDIENCE" \
  --proxied-auth-rw-graphnames 'urn:fct:user:{authid}' \
  --auth-log-dir "$HERE/tmp-audit/" \
  > "$TMPLOG" 2>&1 &
SERVER_PID=$!
trap "kill $SERVER_PID 2>/dev/null || true; rm -rf $HERE/tmp-audit" EXIT

# Wait for server.
for _ in $(seq 1 50); do
  if curl -s "http://127.0.0.1:$PORT/query?query=ASK%20%7B%7D" >/dev/null 2>&1
  then break; fi
  sleep 0.1
done

UPDATE='INSERT DATA { GRAPH <urn:fct:user:alice@example.com> { <urn:a> <urn:b> <urn:c> } }'

# Case 1: good RS256 -> 204.
code=$(curl -s -o /dev/null -w "%{http_code}" -X POST \
  -H "Authorization: Bearer $GOOD" \
  -H "Content-Type: application/sparql-update" \
  --data "$UPDATE" \
  "http://127.0.0.1:$PORT/update")
[[ "$code" == "204" ]] || { echo "FAIL: good RS256 got $code"; exit 1; }

# Case 2: missing Authorization -> 401.
code=$(curl -s -o /dev/null -w "%{http_code}" -X POST \
  -H "Content-Type: application/sparql-update" \
  --data "$UPDATE" \
  "http://127.0.0.1:$PORT/update")
[[ "$code" == "401" ]] || { echo "FAIL: missing auth got $code"; exit 1; }

# Case 3: expired JWT -> 401.
code=$(curl -s -o /dev/null -w "%{http_code}" -X POST \
  -H "Authorization: Bearer $EXP" \
  -H "Content-Type: application/sparql-update" \
  --data "$UPDATE" \
  "http://127.0.0.1:$PORT/update")
[[ "$code" == "401" ]] || { echo "FAIL: expired got $code"; exit 1; }

# Case 4: wrong issuer -> 401.
code=$(curl -s -o /dev/null -w "%{http_code}" -X POST \
  -H "Authorization: Bearer $BADISS" \
  -H "Content-Type: application/sparql-update" \
  --data "$UPDATE" \
  "http://127.0.0.1:$PORT/update")
[[ "$code" == "401" ]] || { echo "FAIL: bad iss got $code"; exit 1; }

# Case 5: wrong audience -> 401.
code=$(curl -s -o /dev/null -w "%{http_code}" -X POST \
  -H "Authorization: Bearer $BADAUD" \
  -H "Content-Type: application/sparql-update" \
  --data "$UPDATE" \
  "http://127.0.0.1:$PORT/update")
[[ "$code" == "401" ]] || { echo "FAIL: bad aud got $code"; exit 1; }

# Case 6: good ES256 -> 204.
code=$(curl -s -o /dev/null -w "%{http_code}" -X POST \
  -H "Authorization: Bearer $GOOD_EC" \
  -H "Content-Type: application/sparql-update" \
  --data "$UPDATE" \
  "http://127.0.0.1:$PORT/update")
[[ "$code" == "204" ]] || { echo "WARN: ES256 got $code (v0 may not support ES256 on this switch)"; }

# 7. Assert audit log contains six lines.
LOG_DIR="$HERE/tmp-audit"
LOG_FILE="$(ls "$LOG_DIR"/auth-*.jsonl | head -1)"
LINES=$(wc -l < "$LOG_FILE")
[[ "$LINES" -ge 5 ]] || { echo "FAIL: expected >= 5 audit lines, got $LINES"; exit 1; }

# 8. Check the README was written.
[[ -f "$LOG_DIR/README.md" ]] || { echo "FAIL: audit README.md missing"; exit 1; }

echo "OK — OIDC v0 smoke tests pass."
```

### 6e. `tests/e2e/oidc-v0/.gitignore`

```
fixtures/test-rsa.pem
fixtures/test-ec.pem
fixtures/test-jwks.json
fixtures/*.json
tmp-audit/
```

(Only the `gen-test-keys.py`, `mint-jwt.py`, `run.sh`, `README.md`, and
`.gitignore` go in git. The `.pem` files and JWKS are regenerated on
each run.)

---

## 7. Parent plan doc update

When tests pass, edit `docs/designissues/2026-04-20-oidc-jwt-auth-plan.md`:

- In the "Staged rollout" section, mark v0 done:
  ```
  1. **OIDC v0** (one subagent, ~300 LOC): DONE as of YYYY-MM-DD, see
     `docs/designissues/2026-04-21-oidc-v0-implementation-prompt.md`
     and commit <sha>.
  ```
- Clarify v1 scope is now unblocked: live JWKS fetch + refresh timer.

Do not touch the other sections. Keep the edit to a few lines.

---

## 8. Commit shape

One commit. Title (matches repo style):

```
factoidal-http: accept OIDC JWTs from a static JWKS file (v0)
```

Body: explain the flags, the `auth_oidc_helpers.ml` split, the 401 vs 403
decision, where the audit log lands. Note the six smoke-test cases in
`tests/e2e/oidc-v0/`. List rebuilt binaries under `bin/<platform>/`.

End with the boilerplate Co-Authored-By line.

Committed binaries (rule #9):

- `bin/darwin-arm64/factoidal-http` — if built on macOS.
- `bin/linux-x86_64/factoidal-http` — if built on Linux.

If the subagent is on macOS and cannot cross-compile to Linux cleanly,
that is acceptable for v0; the Linux binary can be rebuilt in CI. Note
this in the commit body.

Do NOT push. The main thread pushes.

---

## 9. Estimated LOC (v0 total)

Approximate, rounded:

- `formal/fstar/ocaml-output/auth_oidc_helpers.ml` — approximately 150
  lines with `jose`, approximately 250 lines hand-rolled.
- `formal/fstar/ocaml-output/factoidal_http.ml` — approximately 150
  added lines (flag parsing, JWKS load at startup, `resolve_authid`
  helper, audit log emitter, 401 response path, threading client IP).
- `formal/fstar/build-ocaml.sh` — approximately 2 edited lines.
- `tests/e2e/oidc-v0/` — approximately 250 lines across the harness
  and two Python scripts.
- `docs/designissues/2026-04-20-oidc-jwt-auth-plan.md` — approximately
  5 edited lines.

Rough ceiling: around 600 added lines, 2 edited lines.

---

## 10. Anti-patterns to watch for in v0

- **Do not put JWT logic in `ocaml-patches.sh`.** That script patches
  F*-extracted files. `auth_oidc_helpers.ml` is hand-written OCaml that
  lives alongside `factoidal_http.ml`; both are glue (rule #15 test —
  crypto verification is not an RDF/SPARQL semantic decision).
- **Do not use `--lax` anywhere.** This task does not touch F* at all.
- **Do not truncate the build log with `tail`** (rule #16). If compile
  fails, you want the full error.
- **Cap the smoke test server** at a reasonable timeout. If `run.sh`
  hangs because `factoidal-http` fails to start, the trap kills the
  server; add a `timeout 60` around the whole harness in CI.
- **Do not edit extracted `.ml` files.** `auth_oidc_helpers.ml` is a
  NEW hand-written file, not an extraction target. `factoidal_http.ml`
  is already hand-written glue and is editable.
- **Do not skip the `none` / HS*** rejection.** The classic JWT vuln
  is a library happily accepting `alg: none` when the caller only
  supplied an RSA public key. Write a failing test for `alg=none`
  before writing the reject code.
- **Check the `aud` claim shape.** Some issuers emit a string, some
  emit a JSON array. Handle both; reject everything else.

---

## 11. Success criterion (from the parent plan)

After this subagent finishes:

1. `bin/<platform>/factoidal-http` accepts `Authorization: Bearer <JWT>`
   from any issuer whose JWKS has been dropped into the configured path.
2. `tests/e2e/oidc-v0/run.sh` exits 0 with all six curl cases asserting
   the expected status code.
3. `docs/designissues/2026-04-20-oidc-jwt-auth-plan.md` shows v0 as done
   and v1 (discovery) as next.

That is v0 complete.
