# factoidal-skosall: every fetchable skosdex vocabulary, packed on Fly.io, stored in R2

Owner decision, 2026-09-06: the XMPP bot's store should cover "everything
fetchable" from <https://github.com/danbri/skosdex>, and the build runs on
Fly.io with the result in Cloudflare R2, because it does not fit on the
laptop (718 `canonical.nq.gz` files, 3,859 MB compressed, about 65 GB as
N-Quads and about 42 GB as a wire-version-10 generation, against 8 GB free).

Engine: `@factoidal/core` 0.7.0 from the npm registry (the WebAssembly
build), so the machine needs no Lean toolchain. It packs at about 1.06 MB/s
against the native tool's 2.47 MB/s (measured 2026-09-05), which puts the
full source at roughly 17 hours of packing plus activation.

## One-time setup (owner)

1. R2: a bucket (`skosdex001`) and an API token with Object Read & Write on
   it. The account ID is on the R2 overview page.
2. `fly volumes create skosall_data -a factoidal-skosall -r lhr -s 150`
   (about $22 per month while it exists; delete it after the sync).
3. `fly secrets set -a factoidal-skosall R2_ACCOUNT_ID=… R2_ACCESS_KEY_ID=… R2_SECRET_ACCESS_KEY=… R2_BUCKET=skosdex001`

## Run

```
fly deploy -c deploy/fly/skosall/fly.toml
fly logs -a factoidal-skosall
```

The machine runs `build-skosall.sh` once and stops (`restart = never`).
Each step leaves a stamp in `/data/state`, so a second deploy resumes after
the last finished step. Logs are under `/data/logs`.

Dry run on two small vocabularies: `fly deploy … --env ONLY="iptc-colorspace iptc-signal"`
(or set `ONLY` in `[env]`). It walks the same six steps end to end.

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
| machine, performance-2x 8 GB, about 30 hours | a few dollars |
| R2 endpoint | EU jurisdiction: `<account>.eu.r2.cloudflarestorage.com` (`R2_JURISDICTION=eu`) |
| R2 storage, 42 GB | about $0.60 per month; no egress charge |
| GitHub LFS bandwidth, 3.9 GB | metered on the repository owner's account |
