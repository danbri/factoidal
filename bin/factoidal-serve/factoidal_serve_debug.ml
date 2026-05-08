(* factoidal_serve_debug — debug-build stub for the serve subcommand.

   The reversible-debug path should focus on the query engine and the
   COTTAS-backed storage path, not on the HTTP daemon. This file provides
   the same top-level module shape as factoidal_serve.ml once copied into
   place by build-ocaml-debug.sh, but intentionally refuses to start the
   server.

   This keeps the debug bytecode target small and avoids dragging
   factoidal_http.ml into the default ocamldebug workflow. *)

let start_with_args (_args : string list) : unit =
  prerr_endline
    "factoidal: `serve` is disabled in the debug bytecode build.\n\
     Use the native HTTP server for daemon work, or build the explicit\n\
     factoidal-http debug target if you need to debug request handling.";
  exit 2
