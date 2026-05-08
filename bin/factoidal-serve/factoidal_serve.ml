(* factoidal_serve — adapter that lets factoidal_cli's `serve` subcommand
   start the SPARQL 1.1 Protocol HTTP server in-process.

   Native build: this file is compiled in addition to factoidal_http.ml,
   and [start_with_args] forwards the post-`serve` argv tail to
   Factoidal_http.parse_args + run_server.

   JS build: factoidal_http.ml is NOT linked (it pulls in the Unix
   module which js_of_ocaml can't lower without per-call stubs, and a
   SPARQL HTTP server makes no sense in a browser anyway). The JS
   build instead compiles factoidal_serve_jsoo.ml in this file's
   place, keeping the same module name Factoidal_serve but errors out
   at runtime.

   See docs/designissues/2026-04-25-cli-http-unification-phase2.md. *)

let start_with_args (args : string list) : unit =
  let cfg = Factoidal_http.parse_args ~args () in
  if cfg.help_mode then (Factoidal_http.usage (); exit 0);
  Factoidal_http.run_server cfg
