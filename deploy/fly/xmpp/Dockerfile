# The Factoidal XMPP server image.
#
# Two files in this directory are not Lean, and they are the only two:
# this Dockerfile and the socat command in the CMD below. Everything the
# server DECIDES — stream negotiation, SASL, resource binding, roster,
# presence, routing, stream errors — is in
# formal/lean4/L4Factoidal/XMPP/. See README.md beside this file for the
# exact line count and the reasoning.
#
# Shape: socat listens, terminates TLS, and forks one `l4xmpp-serve`
# process per connection with the socket on that process's standard
# input and output. XEP-0368 (direct TLS on port 5223) is what makes
# this possible: with direct TLS there is no STARTTLS step for the
# application to perform, so the Lean process never has to see a TLS
# record and no TLS library is linked into it.

# ---------------------------------------------------------------------------
# Stage 1: build l4xmpp-serve
# ---------------------------------------------------------------------------
FROM debian:bookworm-slim AS lean

RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      git ca-certificates curl build-essential \
 && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH
RUN curl -fsSL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh \
 && sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path \
 && rm /tmp/elan-init.sh

ARG FACTOIDAL_REF=claude/main
ARG FACTOIDAL_REPO=https://github.com/danbri/factoidal

# The same sparse, blobless fetch deploy/fly/skosall/Dockerfile uses: the
# repository's history is about 20 GB and the Lake package reads only
# formal/lean4 (with its lean-toolchain and ffi/ shims) and
# third_party/hacl (compiled into libl4hacl.a as ../../third_party/hacl).
RUN git init -q /src \
 && git -C /src remote add origin "$FACTOIDAL_REPO" \
 && git -C /src config core.sparseCheckout true \
 && git -C /src sparse-checkout set --cone formal/lean4 third_party/hacl \
 && GIT_LFS_SKIP_SMUDGE=1 git -C /src fetch --depth 1 --filter=blob:none origin "$FACTOIDAL_REF" \
 && GIT_LFS_SKIP_SMUDGE=1 git -C /src checkout --detach FETCH_HEAD \
 && git -C /src log -1 --format='factoidal ref %H %ci'

RUN elan toolchain install "$(cat /src/formal/lean4/lean-toolchain)" \
 && elan default "$(cat /src/formal/lean4/lean-toolchain)" \
 && lean --version && lake --version

# Naming the one target builds it and nothing else. A bare `lake build`
# would build every default target: about forty executables plus the
# wasm library. LEAN_NUM_THREADS is the job count; Lake 5.0.0 has no -j.
WORKDIR /src/formal/lean4
RUN set -e; \
    LEAN_NUM_THREADS="$(nproc)" lake build l4xmpp-serve; \
    test -x .lake/build/bin/l4xmpp-serve; \
    { ldd .lake/build/bin/l4xmpp-serve || echo "not a dynamic executable"; }

# ---------------------------------------------------------------------------
# Stage 2: the runtime image — socat and one binary
# ---------------------------------------------------------------------------
FROM debian:bookworm-slim

# socat is the entire carrier. libgmp10 is insurance against a toolchain
# that links GMP dynamically; the `ldd` line above records which it was.
RUN apt-get update \
 && apt-get install -y --no-install-recommends socat ca-certificates libgmp10 \
 && rm -rf /var/lib/apt/lists/* \
 && socat -V | head -1

COPY --from=lean /src/formal/lean4/.lake/build/bin/l4xmpp-serve /opt/factoidal/bin/
COPY entrypoint.sh /opt/factoidal/entrypoint.sh
RUN chmod 0755 /opt/factoidal/bin/l4xmpp-serve /opt/factoidal/entrypoint.sh \
 && /opt/factoidal/bin/l4xmpp-serve --nonsense 2>&1 | grep -q '^usage: l4xmpp-serve'

# 5223: direct TLS (XEP-0368). 5222: plaintext, for local tests only.
EXPOSE 5223 5222
ENV XMPP_DOMAIN=localhost
ENV XMPP_STATE=/data/xmpp
ENV XMPP_CERT=/certs/fullchain.pem
ENV XMPP_KEY=/certs/privkey.pem
ENV XMPP_PLAINTEXT=0

CMD ["/opt/factoidal/entrypoint.sh"]
