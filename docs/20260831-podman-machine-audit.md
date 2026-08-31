# Podman machine audit

## Findings

The existing `podman-machine-default` AppleHV VM is not a reliable container
host in its current state. Its rootful and rootless stores both fail after an
image pull with:

```text
readlink .../containers/storage/overlay: invalid argument
```

The guest itself can boot and its Podman API answers while the calling shell
remains live. In this managed coding environment, vfkit is reaped after an
individual `podman machine start` invocation returns, which explains the
brief visible vfkit GUI and the apparently vanishing API socket. That lifecycle
effect is separate from the overlay-store failure.

A new, isolated rootless `factoidal-containers` VM did pull and run
PostgreSQL 16.15 once, but a later managed startup entered emergency mode with
Ignition/filesystem failure. It was removed; it contained no user data. This
was a diagnostic experiment, not a working project backend.

Homebrew reports Podman **5.8.2** installed and **6.1.0** available. Upgrade
is the next non-destructive repair candidate; do not reset the legacy machine
before checking whether its contents are worth retaining.

## Legacy store inventory

The legacy VM has:

- no named volumes;
- six never-started GraphDB containers with `0 B` writable data;
- one four-month-old exited `parliament_native` GraphDB container with only
  `53.2 kB` writable data;
- approximately **6.8 GiB** actual disk use under the AppleHV machine path.

Its contents are therefore almost entirely re-downloadable image/cache layers
(GraphDB, Debian, and prior Factoidal images). Removing the VM should be safe
for RDF project data based on this inspection, but `parliament_native` is
explicitly retained for now. Do not remove the legacy VM or its image store;
this remains a destructive host action requiring later explicit approval.

## Consequence

Do not claim a container-backed PostgreSQL or ejabberd test as landed yet.
The already-verified Homebrew PostgreSQL `bytea` smoke remains the current
database-host evidence. A repaired Podman install will unlock reproducible
PostgreSQL and then the loopback-only ejabberd MIX pilot in `tools/foafmixer`.
