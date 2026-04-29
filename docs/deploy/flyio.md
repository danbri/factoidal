# Fly.io deployment notes

This is the first-pass packaging plan for running factoidal on Fly.io
with the Parliament corpus. It aims to preserve the current repo layout
and runtime assumptions rather than redesign them.

## Deployment unit

Deploy a **CI-built Linux HTTP binary** plus a **dataset bundle**.

The dataset bundle should contain:

- `data.cottas`
- the companion dictionary / presence / offsets files
- any additional mmap-able binary indexes defined outside core COTTAS
- optional provenance files such as `data.nq`, `data.factbin`,
  `source-info.ttl`, `summary.json`

For the current Parliament corpus on this laptop, that bundle lives at:

- `tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas`

alongside files such as:

- `data.cottas.p.dict`
- `data.cottas.p.presence`
- `data.cottas.p.offsets`
- `data.cottas.po.presence`

## Binary source of truth

The repo currently ships:

- `bin/linux-x86_64/factoidal`
- `bin/linux-x86_64/w3c_runner`

However, the intended deployment source of truth is the CI shadow build
directory, not the local-build directory:

- `bin/ci-linux-x86_64/`

That separation is deliberate:

- local Linux builds can continue to populate `bin/linux-x86_64/`
- cloud CI builds can populate `bin/ci-linux-x86_64/`
- neither side needs to clobber the other

The Fly image therefore expects:

- `bin/ci-linux-x86_64/factoidal-http`

If that file is missing, the container exits immediately with a clear
error.

Because that binary is an ELF Linux x86_64 executable, local container
builds on Apple Silicon should also target `linux/amd64`. The provided
`Dockerfile` now pins that explicitly so local `podman` / `docker`
smoke builds match the artifact we actually ship to Fly.

For now, target **Linux x86_64** on Fly.io, because that is the Linux CI
machine type currently wired in `.github/workflows/w3c-tests.yml`.
Support for a separate Fly ARM deployment can come later if CI starts
publishing a corresponding Linux ARM shadow build too.

## Runtime shape

The intended container command is:

```sh
/app/bin/ci-linux-x86_64/factoidal-http \
  --host 0.0.0.0 \
  --port 8080 \
  --read-only \
  --cors='*' \
  --query-timeout 30 \
  --max-rows 50000 \
  --data-cottas /data/ukparliament/v1/data.cottas \
  --web-demo ukparliament
```

The image entrypoint wraps that command and reads the key values from
environment variables.

## Why a Fly volume first

For the first deployment, prefer a mounted Fly volume at `/data` rather
than baking the Parliament corpus into the image.

Reasons:

- corpus and index files are larger and change on a different cadence
  from the binary
- mmap-oriented artifacts fit naturally on a stable filesystem path
- it avoids rebuilding and pushing a large image for every corpus update
- it keeps the packaging model close to local development

The provided `fly.toml` therefore mounts:

- volume name: `factoidal_data`
- mountpoint: `/data`

## Suggested first deployment flow

1. Ensure CI has populated `bin/ci-linux-x86_64/factoidal-http`.
2. Create a Fly app and volume.
3. Copy the corpus bundle into the volume under:
   - `/data/ukparliament/v1/`
4. Deploy with the included `Dockerfile` and `fly.toml`.
5. Smoke-test:
   - `/`
   - `/query`
   - a simple `COUNT(*)` query against the Parliament corpus

## Commands

Typical Fly commands will look like:

```sh
fly launch --no-deploy
fly volumes create factoidal_data --region lhr --size 20
fly deploy
```

For local container smoke tests with the real Parliament corpus:

```sh
tools/podman-fly-smoke.sh
```

That helper:

- builds the image with `podman`
- mounts `tmp/ukparliament/CorpusCOTTAS/` at `/data`
- publishes the service on `http://127.0.0.1:18080/query`
- tails the first startup logs so you can see COTTAS open / prewarm

Then populate the volume, for example with `fly ssh console` plus `scp`
or a one-off machine that stages the dataset bundle into `/data`.

## Current local serving path

The standard documented local Parliament COTTAS path in this repo is:

- `tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas`

That is the path referenced in current debug and deployment notes. I did
not confirm a live running laptop daemon from inside the sandbox; this
document records the repo's current expected corpus path, not a runtime
guarantee about an active process.

## Next packaging step

Once CI reliably commits the Linux HTTP binary, the next iteration should add:

- a smoke-test in CI that boots the image against a tiny mounted corpus
- a short script for staging a dataset bundle into the Fly volume
- a decision on whether a separate debug/trace Fly app should exist on a
  second internal port or as a separate app entirely
