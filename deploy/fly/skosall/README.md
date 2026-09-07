# factoidal-skosall: every fetchable skosdex vocabulary, packed on Fly.io, stored in R2

Owner decision, 2026-09-06: the XMPP bot's store should cover "everything
fetchable" from <https://github.com/danbri/skosdex>, and the build runs on
Fly.io with the result in Cloudflare R2, because it does not fit on the
laptop (718 `canonical.nq.gz` files, 3,859 MB compressed, about 65 GB as
N-Quads and about 42 GB as a wire-version-10 generation, against 8 GB free).

## Engine: the native Lean packer

The image carries the NATIVE Lean tools `l4block-shard-pack` and
`l4block-shard-activate`, compiled from this repository in the Dockerfile's
first stage. Steps 4 and 5 use them when the binaries are present and log
`route=native`; `@factoidal/core` stays in the image for the `factoidal`
CLI (the version line, and the `route=wasm` fallback if a binary is
missing).

The WebAssembly module is not an option at this size. It stops with
`INTERNAL PANIC: out of memory` at 1.99 GB of linear memory, 436 MB into a
700 MB ingest, because Emscripten's allocator holds pages the native
process returns; the same operations run natively cost 195 MB. The
measurements are in
[`docs/designissues/2026-09-07-wasm-packer-memory.md`](../../../docs/designissues/2026-09-07-wasm-packer-memory.md)
(<https://github.com/danbri/factoidal/issues/658>).

| route | peak memory, 256 MiB batches | throughput |
|---|---|---|
| native `l4block-shard-pack` | about 400 MB (397 MB measured on 1.5 GB of source) | 2.47 MB/s |
| `@factoidal/core` (WebAssembly) | grows without bound; stops at 1.99 GB | 1.06 MB/s |

At 2.47 MB/s the 65 GB of N-Quads is roughly 7.3 hours of packing, plus
activation.

### Building the image

The first stage installs elan, fetches this repository at `FACTOIDAL_REF`
(build arg, default `claude/main`) and runs
`lake build l4block-shard-pack l4block-shard-activate` from `formal/lean4/`.
The clone is `git fetch --depth 1 --filter=blob:none` into a sparse cone of
`formal/lean4` and `third_party/hacl` — the repository's `.git` history is
about 20 GB and is never cloned whole. The Lean version is the one in
`formal/lean4/lean-toolchain`. `LEAN_NUM_THREADS` is set from the builder's
`nproc` and is the job count: Lake 5.0.0 has no `-j` flag, and passing one
fails the build with `unknown short option '-j'`.

Cost, and how firm the figure is:

| step | measured | where |
|---|---|---|
| base image, elan, toolchain v4.33.1 | about 7 minutes | measured 2026-09-07 in this image, 4 cores |
| sparse clone | 15 MB of `.git`, 62 MB checked out | same run |
| `lake build` of the two executables | **not measured in this image** | estimated below |

The Lean work is most of the image build and is the figure that is an
estimate. `lake build L4Factoidal` — object files only, no cache — takes
about 7 minutes of the 9-minute `verify-lean4.yml` run on a 4-core GitHub
runner. The two executables add C code generation, native compilation and
linking over the same import closure, which is the larger half. Budget
**30 to 60 minutes** for the whole image on Fly's remote builder, and read
the real figure off the first `fly deploy`. The cost is paid once per
`FACTOIDAL_REF`; Fly caches the layers between deploys of the same ref.

Pin the deploy to a commit:

```
fly deploy -c deploy/fly/skosall/fly.toml --build-arg FACTOIDAL_REF=<sha>
```

### What has and has not been run

Verified 2026-09-07 by building this image locally as far as the Lean step:
the sparse clone, the elan install of the pinned toolchain, and the
argument forms of both native binaries (`l4block-shard-pack INPUT OUT ibk5
--batch-bytes N`, `l4block-shard-activate ROOT GEN`, run against the macOS
build of the same commit).

NOT run: `lake build` inside the image, and the two-vocabulary dry run. The
local build was stopped because it filled the laptop's disk. **A local
`docker build` of this image needs about 25 GB of free disk** — the elan
toolchain, the Lean object files and the generated C together — and on
Docker Desktop or a `podman machine` the virtual disk does not shrink when
the layers are pruned: reclaim it with `podman machine ssh 'sudo fstrim -av'`
(or the Docker Desktop equivalent) after `podman system prune -af`. The
first `fly deploy` is what proves the Lean step.

## One-time setup (owner)

1. R2: a bucket (`skosdex001`) and an API token with Object Read & Write on
   it. The account ID is on the R2 overview page.
2. `fly volumes create skosall_data -a factoidal-skosall -r lhr -s 150`
   (about $22 per month while it exists; delete it after the sync).
3. `fly secrets set -a factoidal-skosall R2_ACCOUNT_ID=… R2_ACCESS_KEY_ID=… R2_SECRET_ACCESS_KEY=… R2_BUCKET=skosdex001`

## Run

```
fly deploy -c deploy/fly/skosall/fly.toml --build-arg FACTOIDAL_REF=<sha>
fly logs -a factoidal-skosall
```

The machine runs `build-skosall.sh` once and stops (`restart = never`).
Each step leaves a stamp in `/data/state`, so a second deploy resumes after
the last finished step. Logs are under `/data/logs`.

Dry run on two small vocabularies: `fly deploy … --env ONLY="iptc-colorspace iptc-signal"`
(or set `ONLY` in `[env]`). It walks the same six steps end to end.

The same dry run against a locally built image (see the disk figure under
"Building the image" first):

```
podman build --build-arg FACTOIDAL_REF=claude/main -t factoidal-skosall:local \
  deploy/fly/skosall
mkdir -p /tmp/skosall-data/state
# Steps 1 to 5 need no secrets. Step 6 needs the R2 credentials, so a local
# run pre-stamps the sync step rather than reaching for them.
date -u +%FT%TZ > /tmp/skosall-data/state/sync.done
podman run --rm -e ONLY="iptc-colorspace iptc-signal" \
  -v /tmp/skosall-data:/data factoidal-skosall:local
cat /tmp/skosall-data/store/CURRENT
```

The pack and activate lines in the log read `route=native`. A `route=wasm`
line means the binaries did not reach `/opt/factoidal/bin/`, and the pack
will not finish at full size.

## After the sync

The generation is at `r2:skosdex001/skosall/gen-1` plus `CURRENT`. A reader
needs the store-over-HTTP path
(`docs/designissues/2026-09-04-store-over-http.md`), which is designed and
not yet built; until then the generation is downloaded to a machine with the
disk for it and opened locally.

## Cost sheet

| item | figure |
|---|---|
| volume, 150 GB | about $22 per month, deleted after the sync |
| machine, performance-2x 8 GB, about 8 hours | a few dollars |
| image build, Lean toolchain plus the two executables | once per `FACTOIDAL_REF`, on Fly's remote builder |
| R2 endpoint | EU jurisdiction: `<account>.eu.r2.cloudflarestorage.com` (`R2_JURISDICTION=eu`) |
| R2 storage, 42 GB | about $0.60 per month; no egress charge |
| GitHub LFS bandwidth, 3.9 GB | metered on the repository owner's account |
