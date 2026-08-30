# Block engine worknote: host adapter audit

Date: 2026-08-30

## Current host evidence

The repository contains no PostgreSQL or TiKV client, server, extension, or
adapter implementation. Its checked PostgreSQL material is RML test data, and
the block-engine design documents specify a future thin host boundary.

The development machine has `docker` and `podman` command-line tools, but the
Docker daemon was unavailable during this audit:

```text
docker image inspect postgres:16-alpine
-> failed to connect to unix:///var/run/docker.sock
```

No PostgreSQL smoke was therefore claimed or added.

## PostgreSQL `bytea` smoke (landed)

The host fallback installed Homebrew PostgreSQL 16.15 and ran
`tools/blockengine-postgres-smoke.sh` against its local cluster.  The smoke
packed the 486-triple `active_site.ttl` fixture to a 27,256-byte `IBK1` file,
inserted those opaque bytes into a PostgreSQL `bytea` column, retrieved a
base64 representation, decoded it back to bytes, and checked exact byte
equality.  It then executed `l4block-id-file-query` on the retrieved file.

The parsed predicate-and-object-bound SELECT returned 132 rows.  Before the
database write, the same script runs `l4block-id-diff`, which establishes exact
solution-sequence equality between the ordinary graph evaluator and direct
decoded `IBK1`.  Byte equality then makes the PostgreSQL-retrieved execution
the same direct-byte path. PostgreSQL therefore acted only as byte persistence;
the decoded `IndexedBlock.readOps` and SPARQL evaluation remained the Lean
executable path. This is a local development smoke, not yet a parameterized
production client or a PostgreSQL extension.

## PostgreSQL Shardborough `bytea` smoke (landed)

`tools/blockengine-postgres-shard-smoke.sh` exercises the next object shape:
the Lean packer turns the 77-triple music fixture into seven predicate-local
IBK2 objects, their Merkle leaf sidecars, and both compatibility SBM0 and
current SBM1 Shardborough manifests. The local PostgreSQL smoke stores every
opaque object in a dedicated `bytea` test table, retrieves each one as base64,
and establishes byte-for-byte equality before opening the retrieved directory.

The resulting ordinary parsed SPARQL query contains two predicate-bound triple
patterns, a filter and `ORDER BY`; it returns the expected three Radiohead
albums through both the compatibility SBM0 reader and the SBM1 Merkle range
reader. Child length/SHA-256 commitments in SBM0, and range-level Merkle
commitments in SBM1, are checked by Lean after retrieval. This is still an
integration smoke rather than a PostgreSQL extension, transaction/snapshot
model, or server-side pushdown implementation.

## Podman follow-up

The development machine also has Podman 5.8.2 and an Apple Hypervisor
(`applehv`) machine configured.  On 2026-08-30, `podman machine start` reached
the VM-ready stage, but the forwarded rootless API on port 53728 immediately
refused connections and a subsequent inspection reported the machine as
`stopped`.  The guest boot log reached `multi-user.target` and enabled its
Podman socket, so the observed failure is specifically between the host
forwarder and the guest API / lifecycle.  Thus this is a local Podman VM
lifecycle problem, not evidence about PostgreSQL or the `IBK1` format.  No
container, image pull, or database claim has been made from it.

## Consequence

The direct `IBK1` file path is the currently executable host realization:

```text
file bytes -> IndexedBlockWireV1.decode -> Lean IndexedBlock -> SPARQL
```

It gives the byte payload and process boundary a later PostgreSQL adapter must
use, but it is not evidence for PostgreSQL transaction, snapshot, `bytea`, or
extension behavior.

The next database-host vertical requires a running PostgreSQL instance and a
thin client/worker that reads and writes opaque `IBK1` bytes only. Its
differential test must compare the direct-file and PostgreSQL-retrieved bytes,
then execute the same Lean query kernel over both.  It can be run with Podman
once the local machine remains reachable.
