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
differential test must compare the direct-file and PostgreSQL retrieved bytes,
then execute the same Lean query kernel over both.
