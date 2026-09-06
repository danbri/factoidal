# The all-skosdex build machine: packs every fetchable skosdex vocabulary
# into one wire-version-10 generation with the npm engine, activates it,
# and syncs it to an R2 bucket. See README.md beside this file.
#
# The engine is the published package, not a Lean toolchain: everything
# the machine runs is `factoidal pack`, `factoidal activate` and rclone.
FROM node:22-bookworm-slim

RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      git git-lfs rclone gzip gawk ca-certificates procps curl \
 && rm -rf /var/lib/apt/lists/* \
 && git lfs install --system

# The newest 0.7.x at image build time; 0.7.1 adds --batch-bytes and the
# script falls back to the engine default under 0.7.0.
ARG FACTOIDAL_CORE_VERSION=^0.7.0
RUN npm install -g "@factoidal/core@${FACTOIDAL_CORE_VERSION}" \
 && factoidal version

COPY build-skosall.sh /opt/build-skosall.sh
RUN chmod 0755 /opt/build-skosall.sh

WORKDIR /data
CMD ["bash", "/opt/build-skosall.sh"]
