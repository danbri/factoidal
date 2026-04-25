# Cloudflare Tunnel deployment

Companion docs to `tools/cloudflare-tunnel-setup.sh` and the launchd plist
template at `tools/launchd/com.factoidal.cloudflared.plist`.

## What this gives you

- Public HTTPS URL (e.g. `https://factoidal.example.com`) backed by your
  local `factoidal serve` process. No public IP, no firewall rules, no
  open inbound port. Cloudflare terminates TLS and tunnels the request
  back over an outbound-only connection from your laptop.
- Optional gating via **Cloudflare Access** — only allow specific email
  addresses, identity providers, or service tokens through to your
  endpoint. Free for ≤50 users.
- Pairs with your existing tailscale endpoint — same `factoidal serve`
  process is reachable on both surfaces. Cloudflare for the public
  internet, tailscale for your own devices.

## What this does NOT give you

- A managed runtime. Your laptop must be on, the tunnel daemon must be
  running, and `factoidal serve` must be bound to localhost on the
  configured ports. If your laptop sleeps or restarts, the tunnel reconnects
  automatically (launchd KeepAlive) but `factoidal serve` does not — that
  needs its own autostart, separately.
- A scalable load-balanced deployment. One tunnel = one backend.
- A way to receive WebSocket connections without `--protocol http2` on
  the tunnel + matching server. Factoidal doesn't currently use WS.

## Prerequisites

1. **Cloudflare account** with a domain on Cloudflare's nameservers.
   Cloudflare must control DNS for the domain so that `cloudflared
   tunnel route dns` can write the routing record.
2. **Homebrew on macOS** (or `dpkg` on Linux) to install `cloudflared`.
3. **Local factoidal endpoints running.** The tunnel proxies to them; if
   nothing's listening on `localhost:3030` or `localhost:3032`, the
   public URL returns 502. Recommended commands:
   ```bash
   ./bin/darwin-arm64/factoidal serve \
     --port 3030 --host 127.0.0.1 \
     --read-only --cors='*' \
     --dataset /tmp/ukpar_corpus/ukparliament-2019/v1/data.nq \
     --web-demo ukparliament

   ./bin/darwin-arm64/factoidal serve \
     --port 3032 --host 127.0.0.1 \
     --read-only --cors='*' \
     --data-cottas tmp/ukparliament/CorpusCOTTAS/ukparliament/v1/data.cottas \
     --web-demo ukparliament
   ```
   Note `--host 127.0.0.1` — local-only — because the tunnel handles
   public exposure. You don't want both tailscale (`100.107.116.70`) and
   cloudflare on the same process unless you've thought about the
   policy.

## Quick path: run the setup script

```bash
bash tools/cloudflare-tunnel-setup.sh
```

The script is idempotent and prompts before each mutation. It will:

1. Install `cloudflared` via Homebrew if missing.
2. Run `cloudflared tunnel login` (opens browser; one-time per machine).
3. Ask for your public hostname(s).
4. Create or reuse a tunnel named `factoidal` (configurable via
   `--tunnel-name`).
5. Write `~/.cloudflared/config-factoidal.yml` mapping
   `<hostname>` → `localhost:3030` and `<api-hostname>` → `localhost:3032`.
6. Add DNS routes via the Cloudflare API (`cloudflared tunnel route dns`).
7. Optionally install the launchd plist for autostart on login.

After the script finishes you can test with:

```bash
curl -I https://<your-hostname>
```

DNS propagation usually takes 10-60 seconds.

## Manual path: if you'd rather see every step

```bash
# 1. Install
brew install cloudflare/cloudflare/cloudflared

# 2. Auth (browser flow)
cloudflared tunnel login

# 3. Create tunnel
cloudflared tunnel create factoidal
TUNNEL_ID=$(cloudflared tunnel list | awk '/factoidal/ {print $1}')

# 4. Route DNS
cloudflared tunnel route dns factoidal factoidal.example.com
cloudflared tunnel route dns factoidal api.factoidal.example.com

# 5. Write config (~/.cloudflared/config-factoidal.yml)
cat > ~/.cloudflared/config-factoidal.yml <<EOF
tunnel: $TUNNEL_ID
credentials-file: $HOME/.cloudflared/$TUNNEL_ID.json

ingress:
  - hostname: factoidal.example.com
    service: http://localhost:3030
  - hostname: api.factoidal.example.com
    service: http://localhost:3032
  - service: http_status:404
EOF

# 6. Run (foreground, for testing)
cloudflared tunnel --config ~/.cloudflared/config-factoidal.yml run factoidal
```

## Auth — gate the endpoint with Cloudflare Access

By default the public URL is open to the world (read-only because of
`--read-only`, but anyone can submit queries). To restrict access:

1. In Cloudflare dashboard, go to **Zero Trust → Access → Applications**.
2. **Add an application** of type "Self-hosted".
3. Application domain: your `factoidal.example.com` hostname.
4. Add an Access **policy** — e.g. allow only a specific email,
   GitHub-org membership, or a Google Workspace domain.
5. Save.

Once Access is enabled, every request to `factoidal.example.com` first
hits the Access login flow. After authentication, Cloudflare passes the
identity in the `Cf-Access-Authenticated-User-Email` header. Factoidal
already reads this header by default — start the server with:

```bash
./bin/darwin-arm64/factoidal serve \
  --port 3030 --host 127.0.0.1 \
  --read-only \
  --auth-header=Cf-Access-Authenticated-User-Email \
  --dataset ...
```

The endpoint then has the authenticated user's identity available for
logging or per-user authorisation logic, without exposing the
authentication infrastructure to the open internet.

## Autostart — launchd (macOS)

The setup script offers to install the plist at
`~/Library/LaunchAgents/com.factoidal.cloudflared.plist`. Manual control:

```bash
launchctl load   ~/Library/LaunchAgents/com.factoidal.cloudflared.plist
launchctl unload ~/Library/LaunchAgents/com.factoidal.cloudflared.plist
launchctl list | grep com.factoidal
```

Logs at `/tmp/cloudflared.factoidal.{out,err}.log`.

The template is at `tools/launchd/com.factoidal.cloudflared.plist`; the
setup script substitutes the `cloudflared` binary path and config path
before installing.

## Autostart — systemd (Linux)

For Linux deployments, write `/etc/systemd/system/cloudflared-factoidal.service`:

```ini
[Unit]
Description=Cloudflare Tunnel for factoidal
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
User=YOUR_USERNAME
ExecStart=/usr/local/bin/cloudflared tunnel \
  --config /home/YOUR_USERNAME/.cloudflared/config-factoidal.yml \
  --no-autoupdate run
Restart=on-failure
RestartSec=5s

[Install]
WantedBy=multi-user.target
```

Then:

```bash
sudo systemctl daemon-reload
sudo systemctl enable --now cloudflared-factoidal.service
journalctl -u cloudflared-factoidal -f
```

## Troubleshooting

**Public URL returns 502 Bad Gateway**
- Local `factoidal serve` isn't running, or it's bound to a different
  port than the tunnel config expects. Verify with `lsof -nP -iTCP:3030
  -sTCP:LISTEN`.

**Public URL returns 530**
- Cloudflare's "tunnel down" code. Means `cloudflared` daemon isn't
  running or isn't connected. Check with `launchctl list | grep
  com.factoidal` and the log files.

**`cloudflared tunnel route dns` fails with "domain not found in any
zone"**
- The domain you're trying to route isn't on Cloudflare's nameservers.
  Move it (or a subdomain you own) to Cloudflare DNS first.

**`Cf-Access-Authenticated-User-Email` header is empty in factoidal logs**
- Cloudflare Access policy isn't applied to this hostname. Verify in
  the Access dashboard that the application domain matches exactly.

**Tunnel works locally but not from another network**
- DNS hasn't propagated yet (give it a minute), or your DNS resolver is
  caching an old NXDOMAIN. Try `dig +short factoidal.example.com` and
  expect a `cfargotunnel.com` CNAME.

## See also

- `tools/cloudflare-tunnel-setup.sh` — the helper that runs the steps
- `tools/launchd/com.factoidal.cloudflared.plist` — autostart template
- Cloudflare official docs: <https://developers.cloudflare.com/cloudflare-one/connections/connect-networks/>
