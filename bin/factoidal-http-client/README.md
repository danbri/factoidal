# bin/factoidal-http-client

Pure-OCaml HTTP/1.1 client I/O glue around the F\*-extracted
`SPARQL.HTTP.Client` module. Sole job: open a TCP connection,
write the bytes produced by `SPARQL_HTTP_Client.format_request`,
read the response into a buffer, hand it to
`SPARQL_HTTP_Client.parse_http_response`.

Per CLAUDE.md rule #10 / anti-pattern #15: zero RDF/SPARQL
semantics live here. Sockets only.

## Why this lives in `bin/<consumer>/`

Has a module-init hook (`let () = ...`) that runs a smoke test
when `FACTOIDAL_HTTP_CLIENT_SMOKE=1` is set in the environment.
That makes it a consumer (executable behavior at link time), not
a pure assume-val realisation. Per CLAUDE.md rule #11, consumers
belong in `bin/<consumer>/`, not in `formal/fstar/ocaml-output/`.

Relocated 2026-05-08 (#200 PR5 — allowlist retirement track).

## Phase 0 limitations (deliberate)

- HTTP/1.1 only, no HTTPS / TLS.
- No chunked transfer encoding (honours `Content-Length`,
  otherwise reads until EOF).
- No keep-alive: one request per connection.
- No redirect following.
- No socket-read timeout (the GP\_Service main thread will likely
  want `SO_RCVTIMEO`; parked).
- IPv4 + IPv6 via `Unix.getaddrinfo`; first address wins.

## Build

`./build-ocaml.sh compile` builds the binary at
`bin/<platform>/factoidal_http_client`.

## Smoke test

```
FACTOIDAL_HTTP_CLIENT_SMOKE=1 ./bin/linux-x86_64/factoidal_http_client
```

Performs a GET of `http://example.org/` and prints the response
status + a short body prefix. Normal builds do not phone home.
