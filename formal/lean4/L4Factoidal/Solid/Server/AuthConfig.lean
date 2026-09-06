/-
L4Factoidal.Solid.Server.AuthConfig — the Solid-OIDC authentication
configuration, alone in its own module.

It is separate from `Solid/Server/Auth.lean` for one reason:
`Methods.lean` carries the field (`ServerConfig.auth`) and `Auth.lean`
imports `Methods.lean`, so the type must be defined before both. The
decision, the outcome type and every theorem are in `Auth.lean`; there
is nothing here but the record and its defaults.

The defaults are the OFF position. `enforceAuth` is `false`, the key
list is empty, and the issuer and audience are the empty string, so a
deployment that turns authentication on without configuring it refuses
every credential rather than accepting one
(`Auth.checkCredential_no_keys`).
-/
import L4Factoidal.JOSE.DPoP

namespace L4Factoidal.Solid.Server

open L4Factoidal.JOSE

/-- Whether the deployment treats its issuer as authoritative for the
`sub` claim when the Solid-OIDC `webid` claim is absent. Solid-OIDC
permits it; it is not the default, because it makes every subject
identifier the issuer mints into a WebID. -/
structure AuthConfig where
  /-- Off unless a deployment turns it on, like `ServerConfig.enforceWac`. -/
  enforceAuth : Bool := false
  /-- The identity provider's public keys, fetched by the host. Which
  one verifies a token is decided here, not there. -/
  idpKeys : List Jwk := []
  /-- The claims policy: the pinned issuer, this server as the audience,
  the current time and the skew tolerance. -/
  policy : Policy := { now := 0, leeway := 60, issuer := "", audience := "" }
  /-- The DPoP policy: the same instant, the `iat` window, and the
  replay oracle the host supplies. -/
  proofPolicy : ProofPolicy := { now := 0, iatWindow := 60, jtiFresh := fun _ => true }
  /-- Accept `sub` as the WebID when the `webid` claim is absent. -/
  subjectIsWebId : Bool := false
deriving Inhabited

end L4Factoidal.Solid.Server
