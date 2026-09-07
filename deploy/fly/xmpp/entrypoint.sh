#!/bin/sh
# The carrier. This file and the Dockerfile are the only non-Lean parts
# of the deployment; the two socat lines below are the whole of it.
#
# socat listens on a socket, terminates TLS, and forks one
# `l4xmpp-serve` per connection with the socket on that process's
# standard input and output (`EXEC:...,pipes`). Nothing about XMPP is
# decided here: socat does not read the stream, and this script chooses
# no protocol behaviour, only which port and which certificate.
set -eu

DOMAIN="${XMPP_DOMAIN:-localhost}"
STATE="${XMPP_STATE:-/data/xmpp}"
CERT="${XMPP_CERT:-/certs/fullchain.pem}"
KEY="${XMPP_KEY:-/certs/privkey.pem}"
SERVE=/opt/factoidal/bin/l4xmpp-serve

mkdir -p "$STATE"

if [ "${XMPP_PLAINTEXT:-0}" = "1" ]; then
  # Local tests only: no TLS at all, so `--plaintext` records in the
  # session that the carrier did not provide confidentiality.
  echo "l4xmpp: plaintext listener on 5222, domain $DOMAIN" >&2
  exec socat -d TCP-LISTEN:5222,reuseaddr,fork \
    "EXEC:$SERVE --domain $DOMAIN --state $STATE --plaintext,pipes"
fi

if [ ! -r "$CERT" ] || [ ! -r "$KEY" ]; then
  echo "l4xmpp: no certificate at $CERT / $KEY; set XMPP_PLAINTEXT=1 for a" >&2
  echo "        plaintext test listener, or mount the certificate." >&2
  exit 2
fi

# XEP-0368 direct TLS on 5223. `verify=0` is server-side only: it means
# no CLIENT certificate is demanded. The server still presents its own.
echo "l4xmpp: direct TLS listener on 5223, domain $DOMAIN" >&2
exec socat -d "OPENSSL-LISTEN:5223,reuseaddr,fork,cert=$CERT,key=$KEY,verify=0" \
  "EXEC:$SERVE --domain $DOMAIN --state $STATE,pipes"
