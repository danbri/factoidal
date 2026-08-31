# Foafmixer loopback MIX pilot

Status: prepared but not launched, 2026-08-31.

`tools/foafmixer/` now contains an isolated ejabberd configuration and local
pilot launcher. It enables `mod_mix`, `mod_mix_pam`, `mod_mam` and `mod_pubsub`
for the intended MIX channels `factoidal` and `factoidal-shardborough`.

The launcher is deliberately bounded:

* only binds XMPP client and HTTP API ports to `127.0.0.1`;
* requires a caller-provided pilot-only admin password;
* explicitly registers `admin@foafmixer.test` using the container image's
  documented admin macro mechanism;
* owns only container `factoidal-foafmixer` and volume
  `factoidal-foafmixer-state`;
* never removes, resets or reads legacy containers, including the retained
  `parliament_native` container.

The pilot must run through rootless Podman, using the caller's default
connection. `podman-preflight.sh` is intentionally read-only and rejects a
non-rootless connection; it does not assume a host operating system, socket,
or machine name. The pilot must be validated with `ejabberdctl` and a
MIX-capable client before claiming that a local server is running.

The design follows ejabberd's documented MIX requirement for `mod_mix` and
`mod_mix_pam`, and its documented container image and Podman use. MIX remains
experimental, so this is an interoperability pilot rather than a production
messaging deployment.
