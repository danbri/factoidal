open Prims

module Util_Log_runtime = struct
  (* Industry-conventional log levels. Numeric ordering: smaller =
     more verbose. Threshold semantics: emit iff level <= threshold.
     NB: the surrounding file does `open Prims`, which rebinds `int`
     to `Prims.int = Z.t`. We use Stdlib.Int.t explicitly for the
     compact integer comparisons. *)
  type lvl = Error | Warn | Info | Debug | Trace

  let int_of_level : lvl -> Stdlib.Int.t = function
    | Error -> 0 | Warn -> 1 | Info -> 2 | Debug -> 3 | Trace -> 4

  let string_of_level : lvl -> string = function
    | Error -> "ERROR" | Warn -> "WARN" | Info -> "INFO"
    | Debug -> "DEBUG" | Trace -> "TRACE"

  let parse_level (s : string) : lvl option =
    match String.lowercase_ascii (String.trim s) with
    | "error" -> Some Error
    | "warn" | "warning" -> Some Warn
    | "info" -> Some Info
    | "debug" -> Some Debug
    | "trace" -> Some Trace
    | _ -> None

  (* Concurrency note: we don't use Mutex here. Some build targets
     (e.g. w3c_runner) don't link the `threads` package, so Mutex
     would be unbound. For the single-threaded daemon and CLI
     callers this is fine: threshold is a single-cell ref (atomic on
     all platforms factoidal targets) and sink-channel append-write
     is thread-safe enough at the OS level (occasional interleaved
     lines are acceptable for a logger). When we later add
     concurrency-aware threading, gate the Mutex code with a
     `Sys.os_type`-style check or factor into a separate
     thread-safe variant. *)

  (* Threshold: only emit calls with level <= threshold. Default Warn
     matches Unix tool norms; queries are silent unless something is
     wrong. Override via FACTOIDAL_LOG_LEVEL or set_level. *)
  let threshold : lvl ref = ref Warn

  (* Sink: None = stderr; Some oc = file already opened for append. *)
  let sink : out_channel option ref = ref None

  let initialised = ref false

  let init_from_env () =
    (match Sys.getenv_opt "FACTOIDAL_LOG_LEVEL" with
     | Some s -> (match parse_level s with
                  | Some l -> threshold := l
                  | None -> ())
     | None -> ());
    (match Sys.getenv_opt "FACTOIDAL_LOG_FILE" with
     | Some path when path <> "" ->
       (try
          let oc = open_out_gen [Open_append; Open_creat; Open_wronly] 0o644 path in
          sink := Some oc
        with _ -> ())
     | _ -> ());
    initialised := true

  let ensure_init () =
    if not !initialised then init_from_env ()

  let set_level (l : lvl) : unit = threshold := l

  let set_level_str (s : string) : unit =
    match parse_level s with Some l -> set_level l | None -> ()

  let set_file (path : string) : unit =
    (match !sink with Some oc -> (try close_out oc with _ -> ()) | None -> ());
    (try
       let oc = open_out_gen [Open_append; Open_creat; Open_wronly] 0o644 path in
       sink := Some oc
     with _ -> ())

  (* ISO-8601 UTC with millisecond precision.
     `open Prims` at the top of Util_Log.ml rebinds (+) to Z.add and
     `int` to Z.t, but Unix tm fields are plain Stdlib.Int.t. Use
     Stdlib.(+) explicitly to avoid type-mismatch on the arithmetic. *)
  let iso8601_now () : string =
    let t = Unix.gettimeofday () in
    let tm = Unix.gmtime t in
    let ms = int_of_float ((t -. floor t) *. 1000.0) in
    Printf.sprintf "%04d-%02d-%02dT%02d:%02d:%02d.%03dZ"
      (Stdlib.(+) tm.Unix.tm_year 1900)
      (Stdlib.(+) tm.Unix.tm_mon 1)
      tm.Unix.tm_mday
      tm.Unix.tm_hour tm.Unix.tm_min tm.Unix.tm_sec ms

  let do_emit (l : lvl) (modname : string) (msg : string) : unit =
    ensure_init ();
    (* Stdlib.(<=) explicitly: open Prims rebinds comparison ops
       to Z.t arithmetic, but int_of_level returns Stdlib.Int.t. *)
    if Stdlib.(<=) (int_of_level l) (int_of_level !threshold) then begin
      let line = Printf.sprintf "%s %-5s %s: %s\n"
        (iso8601_now ()) (string_of_level l) modname msg in
      (match !sink with
       | Some oc -> output_string oc line; flush oc
       | None -> output_string stderr line; flush stderr)
    end
end

(* Realise the F* assume vals — one per level. Each level is its own
   F* `assume val` (not a convenience alias around a single emit) so
   F*'s extraction can't inline the dispatch and erase the unit-typed
   result. See Util.Log.fst header for why this matters. *)

let error (modname : Prims.string) (msg : Prims.string) : unit =
  Util_Log_runtime.do_emit Util_Log_runtime.Error modname msg

let warn (modname : Prims.string) (msg : Prims.string) : unit =
  Util_Log_runtime.do_emit Util_Log_runtime.Warn modname msg

let info (modname : Prims.string) (msg : Prims.string) : unit =
  Util_Log_runtime.do_emit Util_Log_runtime.Info modname msg

let debug (modname : Prims.string) (msg : Prims.string) : unit =
  Util_Log_runtime.do_emit Util_Log_runtime.Debug modname msg

let trace (modname : Prims.string) (msg : Prims.string) : unit =
  Util_Log_runtime.do_emit Util_Log_runtime.Trace modname msg
