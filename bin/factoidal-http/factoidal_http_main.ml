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
  (* Qof3 defensive instrumentation: enable backtraces for every uncaught
     exception in the server / cottas-ondisk runtime.  See
     docs/designissues/2026-04-25-qof3-3032-defensive-debug.md. *)
  Printexc.record_backtrace true;
  (* Pe4 instrumentation: best-effort SIGABRT / SIGPIPE handler so a
     C-stub abort or broken-pipe doesn't disappear silently.  macOS
     restricts catching SIGSEGV so we don't try.  See
     docs/designissues/2026-04-25-pe4-mim2-daemon-crash-investigation.md. *)
  let log_signal sname signo =
    Printf.eprintf "[pe4-SIGNAL] caught %s (signo=%d) — printing backtrace and exiting\n%!"
      sname signo;
    Printexc.print_backtrace stderr;
    Printf.eprintf "[pe4-SIGNAL] (note: backtrace may be empty if not raised via OCaml exception)\n%!";
    exit 137
  in
  (try Sys.set_signal Sys.sigabrt (Sys.Signal_handle (log_signal "SIGABRT")) with _ -> ());
  (try Sys.set_signal Sys.sigpipe (Sys.Signal_handle (log_signal "SIGPIPE")) with _ -> ());
  (try Sys.set_signal Sys.sigterm (Sys.Signal_handle (log_signal "SIGTERM")) with _ -> ());
  let cfg = Factoidal_http.parse_args () in
  if cfg.help_mode then (Factoidal_http.usage (); exit 0);
  Factoidal_http.run_server cfg
