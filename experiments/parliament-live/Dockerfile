# fpkg — Forgetmeknot Palace, prototype proxy + static page.
# Zero-dep Node app: server.mjs serves /web statics and proxies a small
# whitelist of UK Parliament APIs with a TTL policy and OPL attribution.

FROM node:22-alpine AS runtime

WORKDIR /app
COPY server.mjs ./
COPY web/ ./web/
COPY CLAUDE.md ./

ENV HOST=0.0.0.0
ENV PORT=8080
EXPOSE 8080

# Run as the built-in non-root `node` user.
RUN chown -R node /app
USER node

CMD ["node", "server.mjs"]
