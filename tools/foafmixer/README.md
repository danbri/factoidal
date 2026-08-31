# foafmixer

`foafmixer` is the working home for Factoidal's future XMPP MIX bridge and
agent/human social collaboration tools. It deliberately sits in `tools/` for
now: it is operational glue around standard XMPP and is not yet part of the
Lean SPARQL kernel.

The later formal counterpart belongs under `formal/lean4/`, where it can model
the SPARQL-over-MIX channel semantics, messages, artifact references and
provenance claims without making the hot RDF block path depend on an XMPP
client.

The initial operational target is a loopback-only ejabberd pilot using MIX
channels `factoidal` and `factoidal-shardborough`. Git commits and dated
worknotes remain the audit fallback. Do not substitute MUC merely because a
client has incomplete MIX support.

## Local pilot

`ejabberd.yml` enables the experimental ejabberd MIX modules, MIX participant
support, MAM and the PubSub support MIX needs. `pilot.sh` deliberately exports
only XMPP client and HTTP API ports on `127.0.0.1`; it owns only the disposable
container named `factoidal-foafmixer` and a separate
`factoidal-foafmixer-state` volume. It never removes or reuses any older
Podman container. Factoidal container tooling requires the caller's default
Podman connection to be rootless. It never hard-codes a connection, socket,
machine name, or host-platform assumption.

Once `tools/foafmixer/podman-preflight.sh` reports that Podman is ready, start
the pilot with a pilot-only password:

```sh
FOAFMIXER_ADMIN_PASSWORD='choose-a-pilot-only-password' \
  tools/foafmixer/pilot.sh start
```

The pilot virtual host is `foafmixer.test`, with MIX service
`mix.foafmixer.test`. The server comes up without creating public channels;
create `factoidal` and `factoidal-shardborough` through a MIX-capable client
or the documented XMPP stream calls, then record the channel/JID identities in
the project worknotes. `tools/foafmixer/pilot.sh stop` removes only the pilot
container and intentionally retains its named state volume for a later local
restart.

This is a development pilot, not an exposed or production service. Do not add
Tailscale, public DNS, federation, or production credentials to it until the
local lifecycle and client interoperability are tested.

## Historical context

The name acknowledges FOAFtown/JQBus experiments in social, RDF-aware message
exchange. The archived [JQBus introduction](https://web.archive.org/web/20071212235303/http://svn.foaf-project.org/foaftown/jqbus/intro.html)
is historical context, not an implementation dependency or protocol
specification.
