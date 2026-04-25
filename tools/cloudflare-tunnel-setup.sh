#!/bin/bash
#
# Cloudflare Tunnel setup helper for factoidal endpoints.
#
# Companion to docs/deploy/cloudflare-tunnel.md (read that first for the
# what / why / threat-model context).
#
# Idempotent: re-running re-prints state. Each step pauses for confirmation
# before mutating. No destructive actions without explicit prompt.
#
# Default mapping:
#   https://<hostname>           -> http://localhost:3030  (in-memory TriG)
#   https://api.<hostname>       -> http://localhost:3032  (COTTAS / disk)
#
# To customise the hostname / port, edit the CONFIG block below before
# running, or pass them as args:
#   bash tools/cloudflare-tunnel-setup.sh \
#     --hostname factoidal.example.com \
#     --api-hostname api.factoidal.example.com \
#     --tunnel-name factoidal-prod
#
# Prerequisites:
#   - macOS or Linux with Homebrew (Linux can also use the official .deb)
#   - A Cloudflare account with a domain you control (the domain itself
#     must be on Cloudflare's nameservers — Cloudflare needs to manage DNS
#     for the routing step to work).
#
# After running, see docs/deploy/cloudflare-tunnel.md §"Troubleshooting"
# for common issues + the launchd plist for autostart on login.

set -euo pipefail

# ---------------------------------------------------------------------------
# CONFIG — edit if you know what you want before running, or pass --flags
# ---------------------------------------------------------------------------
TUNNEL_NAME="factoidal"
HOSTNAME=""              # e.g. factoidal.example.com — required
API_HOSTNAME=""          # e.g. api.factoidal.example.com — optional
PORT_INMEM=3030
PORT_COTTAS=3032

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
while [[ $# -gt 0 ]]; do
  case "$1" in
    --tunnel-name)   TUNNEL_NAME="$2";   shift 2 ;;
    --hostname)      HOSTNAME="$2";      shift 2 ;;
    --api-hostname)  API_HOSTNAME="$2";  shift 2 ;;
    --port-inmem)    PORT_INMEM="$2";    shift 2 ;;
    --port-cottas)   PORT_COTTAS="$2";   shift 2 ;;
    -h|--help)
      sed -n '3,30p' "$0"
      exit 0
      ;;
    *)
      echo "Unknown arg: $1" >&2
      echo "Run with --help for usage."
      exit 2
      ;;
  esac
done

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
say()  { printf '\033[1;34m==>\033[0m %s\n' "$*"; }
warn() { printf '\033[1;33m!!  \033[0m %s\n' "$*" >&2; }
die()  { printf '\033[1;31mxx  \033[0m %s\n' "$*" >&2; exit 1; }
prompt() {
  # prompt "Continue?" "y" — default y
  local msg="$1" default="${2:-y}"
  read -r -p "$msg [$default] " answer
  answer="${answer:-$default}"
  [[ "$answer" =~ ^[Yy]$ ]]
}

# ---------------------------------------------------------------------------
# Step 1 — Ensure cloudflared is installed
# ---------------------------------------------------------------------------
say "Step 1/6 — checking for cloudflared"
if command -v cloudflared >/dev/null 2>&1; then
  say "cloudflared already installed: $(cloudflared --version 2>&1 | head -1)"
else
  if [[ "$(uname -s)" == "Darwin" ]]; then
    if ! command -v brew >/dev/null 2>&1; then
      die "Homebrew not found. Install from https://brew.sh, then re-run."
    fi
    if prompt "Install cloudflared via 'brew install cloudflare/cloudflare/cloudflared'?"; then
      brew install cloudflare/cloudflare/cloudflared
    else
      die "cloudflared required. Aborting."
    fi
  else
    warn "Linux detected. Recommended install:"
    warn "  curl -L https://github.com/cloudflare/cloudflared/releases/latest/download/cloudflared-linux-amd64.deb -o /tmp/cloudflared.deb"
    warn "  sudo dpkg -i /tmp/cloudflared.deb"
    die "Run the above commands then re-run this script."
  fi
fi

# ---------------------------------------------------------------------------
# Step 2 — Authenticate to Cloudflare (browser flow, one-time)
# ---------------------------------------------------------------------------
say "Step 2/6 — Cloudflare auth"
CERT_PATH="$HOME/.cloudflared/cert.pem"
if [[ -f "$CERT_PATH" ]]; then
  say "Auth cert already at $CERT_PATH (skipping login)"
else
  warn "About to open a browser. Sign in to Cloudflare and authorize the"
  warn "domain you want to use for tunnel routing."
  if prompt "Run 'cloudflared tunnel login' now?"; then
    cloudflared tunnel login
  else
    die "Auth required for tunnel + DNS routing. Aborting."
  fi
fi

# ---------------------------------------------------------------------------
# Step 3 — Hostname (prompt if not given)
# ---------------------------------------------------------------------------
say "Step 3/6 — hostname"
if [[ -z "$HOSTNAME" ]]; then
  read -r -p "Public hostname for the in-memory endpoint (e.g. factoidal.example.com): " HOSTNAME
fi
[[ -z "$HOSTNAME" ]] && die "HOSTNAME required."
if [[ -z "$API_HOSTNAME" ]]; then
  read -r -p "Hostname for the COTTAS/disk endpoint [skip with empty]: " API_HOSTNAME
fi
say "in-memory  : https://$HOSTNAME           -> http://localhost:$PORT_INMEM"
[[ -n "$API_HOSTNAME" ]] && say "cottas/disk: https://$API_HOSTNAME -> http://localhost:$PORT_COTTAS"

# ---------------------------------------------------------------------------
# Step 4 — Create or reuse a tunnel
# ---------------------------------------------------------------------------
say "Step 4/6 — tunnel"
TUNNEL_ID="$(cloudflared tunnel list 2>/dev/null | awk -v n="$TUNNEL_NAME" '$2 == n { print $1 }' | head -1 || true)"
if [[ -n "$TUNNEL_ID" ]]; then
  say "Tunnel '$TUNNEL_NAME' already exists (ID $TUNNEL_ID); reusing."
else
  if prompt "Create new tunnel '$TUNNEL_NAME'?"; then
    cloudflared tunnel create "$TUNNEL_NAME"
    TUNNEL_ID="$(cloudflared tunnel list | awk -v n="$TUNNEL_NAME" '$2 == n { print $1 }' | head -1)"
  else
    die "Tunnel required. Aborting."
  fi
fi

# ---------------------------------------------------------------------------
# Step 5 — Generate config.yml + DNS routes
# ---------------------------------------------------------------------------
say "Step 5/6 — config.yml + DNS routes"
CONFIG_DIR="$HOME/.cloudflared"
CONFIG_PATH="$CONFIG_DIR/config-$TUNNEL_NAME.yml"
CRED_PATH="$CONFIG_DIR/$TUNNEL_ID.json"

mkdir -p "$CONFIG_DIR"
{
  echo "# Generated by tools/cloudflare-tunnel-setup.sh"
  echo "# Companion docs: docs/deploy/cloudflare-tunnel.md"
  echo "tunnel: $TUNNEL_ID"
  echo "credentials-file: $CRED_PATH"
  echo ""
  echo "ingress:"
  echo "  - hostname: $HOSTNAME"
  echo "    service: http://localhost:$PORT_INMEM"
  if [[ -n "$API_HOSTNAME" ]]; then
    echo "  - hostname: $API_HOSTNAME"
    echo "    service: http://localhost:$PORT_COTTAS"
  fi
  echo "  - service: http_status:404"
} > "$CONFIG_PATH"
say "Wrote $CONFIG_PATH"

if prompt "Add DNS route for $HOSTNAME?"; then
  cloudflared tunnel route dns "$TUNNEL_NAME" "$HOSTNAME" || \
    warn "Route may already exist — that's fine."
fi
if [[ -n "$API_HOSTNAME" ]]; then
  if prompt "Add DNS route for $API_HOSTNAME?"; then
    cloudflared tunnel route dns "$TUNNEL_NAME" "$API_HOSTNAME" || \
      warn "Route may already exist — that's fine."
  fi
fi

# ---------------------------------------------------------------------------
# Step 6 — Optional autostart via launchd (macOS) / systemd (Linux)
# ---------------------------------------------------------------------------
say "Step 6/6 — autostart (optional)"
if [[ "$(uname -s)" == "Darwin" ]]; then
  PLIST_SRC="$(cd "$(dirname "$0")"/.. && pwd)/tools/launchd/com.factoidal.cloudflared.plist"
  PLIST_DEST="$HOME/Library/LaunchAgents/com.factoidal.cloudflared.plist"
  if [[ -f "$PLIST_SRC" ]]; then
    if prompt "Install launchd plist for autostart on login?"; then
      # Substitute the config path into the plist before installing
      sed "s|__CONFIG_PATH__|$CONFIG_PATH|g; s|__CLOUDFLARED__|$(command -v cloudflared)|g" "$PLIST_SRC" > "$PLIST_DEST"
      launchctl unload "$PLIST_DEST" 2>/dev/null || true
      launchctl load "$PLIST_DEST"
      say "Autostart installed. Tunnel will start on login."
      say "Manage with:"
      say "  launchctl unload $PLIST_DEST   # stop"
      say "  launchctl load   $PLIST_DEST   # start"
      say "Logs at /tmp/cloudflared.factoidal.{out,err}.log"
    else
      say "Skipped autostart. To run manually:"
      say "  cloudflared tunnel --config $CONFIG_PATH run $TUNNEL_NAME"
    fi
  else
    warn "Plist template missing at $PLIST_SRC — autostart skipped."
    say "Manual run:"
    say "  cloudflared tunnel --config $CONFIG_PATH run $TUNNEL_NAME"
  fi
else
  say "Linux autostart: see docs/deploy/cloudflare-tunnel.md §systemd."
  say "Manual run:"
  say "  cloudflared tunnel --config $CONFIG_PATH run $TUNNEL_NAME"
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo
say "Setup complete."
say "Tunnel ID:    $TUNNEL_ID"
say "Tunnel name:  $TUNNEL_NAME"
say "Config:       $CONFIG_PATH"
say ""
say "Local endpoints to keep running:"
say "  factoidal serve --port $PORT_INMEM  --host 127.0.0.1 --read-only --cors='*' --dataset <trig-or-nq-file>"
[[ -n "$API_HOSTNAME" ]] && say "  factoidal serve --port $PORT_COTTAS --host 127.0.0.1 --read-only --cors='*' --data-cottas <cottas-file>"
say ""
say "Public URLs (after DNS propagates ~10-60s):"
say "  https://$HOSTNAME"
[[ -n "$API_HOSTNAME" ]] && say "  https://$API_HOSTNAME"
say ""
say "Lock down with Cloudflare Access — see docs/deploy/cloudflare-tunnel.md §Auth."
