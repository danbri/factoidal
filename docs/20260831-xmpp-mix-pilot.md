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

The pilot is intentionally deferred until the current storage correctness
increment is committed. It should begin loopback-only, with separate
`factoidal` and `factoidal-shardborough` channels, explicit service-account
credentials for agents, and no public federation. Tailscale exposure, TLS,
and bridge policy are separate security decisions.
