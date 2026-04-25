(* factoidal_http_main — entry point for the standalone [factoidal-http]
   binary. All argv parsing + server logic lives in [factoidal_http.ml]
   (now linkable as a library); this file just wires the [let () = ...]
   so the standalone binary keeps the same surface as before.

   See docs/designissues/2026-04-25-cli-http-unification-phase2.md for
   why factoidal_http.ml was split: factoidal_cli.ml's `serve`
   subcommand calls Factoidal_http.parse_args + run_server in-process
   instead of execing this binary. Both entry points end up running the
   same code. *)

let () =
  let cfg = Factoidal_http.parse_args () in
  if cfg.help_mode then (Factoidal_http.usage (); exit 0);
  Factoidal_http.run_server cfg
