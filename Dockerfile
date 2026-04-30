# The shipped CI server binary is Linux x86_64, so keep the image target
# explicit rather than inheriting the local builder architecture.
FROM --platform=linux/amd64 debian:bookworm-slim

RUN apt-get -o Acquire::Check-Valid-Until=false -o Acquire::Check-Date=false update \
 && apt-get install -y --no-install-recommends ca-certificates libgmp10 libev4 libpcre3 zlib1g \
 && rm -rf /var/lib/apt/lists/*

WORKDIR /app

# Keep the repo layout intact for now. Prefer CI-built Linux binaries so
# local machine builds and cloud builds do not clobber each other.
COPY bin/ci-linux-x86_64/ /app/bin/ci-linux-x86_64/
COPY docs/web/ /app/docs/web/
COPY docs/fstar-extracted/ /app/docs/fstar-extracted/
COPY tools/docker-entrypoint.sh /app/tools/docker-entrypoint.sh

ENV PORT=8080
ENV HOST=0.0.0.0
ENV DATA_COTTAS=/data/ukparliament/v1/data.cottas
ENV WEB_DEMO=ukparliament
ENV QUERY_TIMEOUT=30
ENV MAX_ROWS=50000
ENV READ_ONLY=1
ENV CORS=*

EXPOSE 8080

ENTRYPOINT ["/app/tools/docker-entrypoint.sh"]
