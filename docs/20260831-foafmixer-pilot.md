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

Podman remains unavailable on this Mac at the time of writing: its retained
`podman-machine-default` says it started, but its API forwarder exits
immediately and the client gets connection-refused at port 53728. The new
`podman-preflight.sh` is intentionally read-only and makes that distinction
visible. The pilot must be validated with `ejabberdctl` and a MIX-capable
client after the Podman installation/machine is repaired; do not claim that a
local server is running before then.

The design follows ejabberd's documented MIX requirement for `mod_mix` and
`mod_mix_pam`, and its documented container image and Podman use. MIX remains
experimental, so this is an interoperability pilot rather than a production
messaging deployment.
