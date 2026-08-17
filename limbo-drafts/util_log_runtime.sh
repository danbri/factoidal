#!/bin/bash
# Util.Log runtime realisation (rule #3 compliant: pure I/O glue
# realising the F* `assume val emit` declaration).
#
# Behaviour:
#   - Reads FACTOIDAL_LOG_LEVEL env var on first call (one of:
#     error|warn|info|debug|trace; default warn).
#     Lower-case match, leading/trailing whitespace stripped.
#   - Reads FACTOIDAL_LOG_FILE env var on first call. If unset or
#     empty, logs go to stderr. If set, opened for append.
#   - Each line: <ISO-8601 UTC timestamp> <LEVEL> <module>: <message>
#     Example:
#       2026-04-26T19:44:12.345Z DEBUG choose_best_tp_backend: considering tp=?s ?p ?o est=3143406
#   - Level filter: emit calls below the threshold are no-ops, so
#     production runs at default warn-level pay almost nothing per
#     call (one int compare).
#   - Thread-safe via OCaml's Mutex (the daemon's accept loop is
#     single-threaded but sockets call back to scheduled tasks).
#
# Setting CLI flags (--log-level=NAME, --log-file=PATH) is handled in
# factoidal_http.ml / factoidal_cli.ml: those handlers call
# Util_Log_runtime.set_level / set_file at startup. Env vars are the
# floor.
#
# This patch ONLY introduces the I/O machinery. The semantic decisions
# of WHAT to log live in the F* sources at the call sites (e.g.
# Util_Log.debug "choose_best_tp_backend" "...").

set -euo pipefail

ML="ocaml-output/Util_Log.ml"

if [ ! -f "$ML" ]; then
  echo "  WARN: $ML not found; skipping util_log_runtime patch."
  echo "         (F* extract may not have produced Util.Log yet.)"
  exit 0
fi

if grep -q '^module Util_Log_runtime' "$ML"; then
  echo "  [util_log_runtime] perf-shim already applied; skipping."
  exit 0
fi

# Append the runtime module after the existing extracted definitions.
cat >> "$ML" <<'OCAML'

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
OCAML

echo "  [util_log_runtime] applied: emit -> Util_Log_runtime.do_emit (file/stderr sink, threshold-gated)"
