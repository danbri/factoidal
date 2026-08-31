# Factoidal agent collaboration: local MIX pilot

The intended social collaboration protocol is XMPP MIX, not a quiet fallback
to MUC. MIX's PubSub and archive model is a good fit for durable, inspectable
Factoidal discussion streams that can later include humans, coding agents and
social-web bridges.

For a local macOS pilot, the current candidate is **ejabberd** with its
experimental `mod_mix` support and the required PubSub/MAM pieces. GitHub,
commit messages, and dated repository worknotes remain the durable fallback
and audit trail; they are not a substitute for the planned MIX collaboration
surface.

The operational bridge/home is [`tools/foafmixer`](../tools/foafmixer/).
The eventual Lean semantics work is intentionally a later, separately named
`formal/lean4` effort; it must not make XMPP a dependency of block execution.

The pilot is intentionally deferred until the current storage correctness
increment is committed. It should begin loopback-only, with separate
`factoidal` and `factoidal-shardborough` channels, explicit service-account
credentials for agents, and no public federation. Tailscale exposure, TLS,
and bridge policy are separate security decisions.

## Local pilot status (2026-08-31)

The storage increment has now been committed. The official arm64-capable
`ghcr.io/processone/ejabberd` image was selected. Podman's AppleHV guest
boots to its API socket, but this managed coding environment reaps vfkit once
an individual `podman machine start` command ends; a start plus API queries in
one shell succeeds. Its legacy overlay stores are presently unusable; a fresh,
separate rootless `factoidal-containers` machine briefly pulled and ran
PostgreSQL, but later entered emergency mode during a managed startup, so it
was removed and is not a project-script default. No ejabberd image, container,
account, port listener, or network exposure was left running. Keep container
operations in one script shell here, while an ordinary user Terminal should
retain the VM normally; do not substitute MUC for MIX merely to obtain a
working demo.
