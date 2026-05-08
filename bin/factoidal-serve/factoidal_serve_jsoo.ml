(* factoidal_serve_jsoo — JS-build stub for the serve subcommand.

   Provides the same Factoidal_serve module signature as
   factoidal_serve.ml (native), but without linking factoidal_http.ml
   (which pulls in Unix module + friends). A browser bundle has no
   business starting an HTTP server, so we simply error out.

   The build script picks ONE of these two files at compile time. They
   must NOT both be linked into the same artifact. *)

let start_with_args (_args : string list) : unit =
  prerr_endline
    "factoidal: `serve` is not available in the browser/JS build.\n\
     Run the native binary (bin/<platform>/factoidal serve …) instead.";
  exit 2
