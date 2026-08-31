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

## Historical context

The name acknowledges FOAFtown/JQBus experiments in social, RDF-aware message
exchange. The archived [JQBus introduction](https://web.archive.org/web/20071212235303/http://svn.foaf-project.org/foaftown/jqbus/intro.html)
is historical context, not an implementation dependency or protocol
specification.
