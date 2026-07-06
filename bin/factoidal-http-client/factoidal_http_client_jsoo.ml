(* factoidal_http_client_jsoo — JS-build stub for the `query --endpoint`
   remote-client path.

   Provides the one function factoidal_cli.ml calls from the native
   Factoidal_http_client module ([perform_request]), but without
   linking factoidal_http_client.ml's Unix socket I/O (js_of_ocaml has
   no raw-TCP-socket primitive a browser bundle could use). A browser
   bundle has no business opening a bare TCP connection to an arbitrary
   SPARQL endpoint, so we simply error out — same pattern as
   bin/factoidal-serve/factoidal_serve_jsoo.ml for the `serve`
   subcommand.

   The build script picks ONE of factoidal_http_client.ml (native) or
   this file (JS) at compile time. They must NOT both be linked into
   the same artifact. *)

let perform_request ~host:(_ : string) ~port:(_ : int) ~req_bytes:(_ : string) : string =
  failwith
    "factoidal: `query --endpoint` is not available in the browser/JS build \
     (no raw TCP sockets in js_of_ocaml). Run the native binary \
     (bin/<platform>/factoidal query --endpoint ...) instead."
