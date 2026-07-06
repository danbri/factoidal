(* service_wrap_http.ml -- ASSUME-IO glue realising the wrap+http(s)
   half of the SERVICE endpoint resolver (issue #57 family; virtual-
   sources design doc, Part A Stages 1-2:
   docs/designissues/2026-07-06-virtual-sources-design.md).

   Hand-written, no corresponding .fst source -- same footing as
   ocaml-output/fstar_pure_hashes.ml and this file's own sibling
   service_wrap_hook.ml (see that file's banner for why the hook cell
   is split out). Per skills/ocaml-boundary/SKILL.md's ASSUME-IO class
   and CLAUDE.md rule #11 ("pure I/O: file/clock/socket"): every
   decision about IRI-scheme recognition, control-fragment parsing,
   format detection, the default Facade-X-equivalent mapping, and the
   rml= override lives in SPARQL.Service.Wrap.fst (extracted to
   SPARQL_Service_Wrap.ml). This file does exactly four things, none of
   them RDF/SPARQL semantics:

     1. Read the opt-in env flag + host allowlist (deployment policy,
        rule #11's CONSUMER classification -- same shape as
        bin/factoidal-http's existing CORS-origin-allowlist parsing).
     2. Socket I/O: connect, send the F*-built request bytes, read the
        response (same minimal shape as
        bin/factoidal-http-client/factoidal_http_client.ml's
        perform_request, duplicated rather than shared because that
        file is not linked into every binary this glue must work in --
        see this file's own placement note below).
     3. File I/O: read the `rml=` mapping file's raw bytes, if present.
     4. Wire the result into service_wrap_hook.ml's ref cell.

   Placement note: this file is intentionally NOT under bin/<consumer>/
   even though it does I/O with a module-init side effect (the ref-cell
   wiring at the bottom) -- unlike factoidal_http_client.ml's smoke
   test, that side effect is inert (just stores a function pointer, no
   network access at load time) and must run in every binary that
   links the patched SPARQL11_Algebra.ml, not just the CLI. It is
   placed at the very end of build-ocaml.sh's COMMON_MODULES /
   NATIVE_SOURCES lists (native builds ONLY -- deliberately absent from
   FSTAR_MODULES, since Unix.* has no JS/WASM realisation; a
   `wrap+http(s):` IRI in a JS/WASM build falls through
   service_wrap_hook.ml's default "always None", identical to the
   design doc's own "no realisation -> None, never a crash" precedent
   for wrap+exec:/stdio wrap+mcp: in that same environment).
*)

let opt_env (name : string) : string option =
  match Sys.getenv_opt name with
  | Some "" -> None
  | v -> v

let is_opted_in () : bool =
  opt_env "FACTOIDAL_SERVICE_HTTP" = Some "1"

(* Host allowlist: empty/unset = nothing allowed (never a wildcard
   default), same shape as bin/factoidal-http's CORS-origin allowlist
   (factoidal_http.ml, "off (explicit opt-in ...) or a comma-separated
   allowlist of exact ... origin"). Exact-match only, case-sensitive on
   the host string as given -- no DNS/case-folding games. *)
let allowed_hosts () : string list =
  match opt_env "FACTOIDAL_SERVICE_HTTP_ALLOWED_HOSTS" with
  | None -> []
  | Some s ->
    String.split_on_char ',' s
    |> List.map String.trim
    |> List.filter (fun x -> x <> "")

let host_allowed (host : string) : bool =
  List.mem host (allowed_hosts ())

(* ------------------------------------------------------------------
   Socket I/O (deliberately re-derived, not shared -- see banner: this
   file must link into every native binary, factoidal_http_client.ml
   only links into a subset). Same minimal shape: connect, write,
   half-close, read until EOF. A receive timeout is added (anti-pattern
   #17's "never let an ad-hoc call hang" discipline extended to network
   I/O run mid-query, not just foreground shell commands) since a wrap+
   target that accepts a connection but never answers must not hang a
   SPARQL query forever.
   ------------------------------------------------------------------ *)

let socket_connect ~(host : string) ~(port : int) : Unix.file_descr =
  let opts = [ Unix.AI_SOCKTYPE Unix.SOCK_STREAM ] in
  let addr =
    match Unix.getaddrinfo host (string_of_int port) opts with
    | [] -> failwith (Printf.sprintf "service_wrap_http: cannot resolve %s:%d" host port)
    | ai :: _ -> ai.Unix.ai_addr
  in
  let domain =
    match addr with
    | Unix.ADDR_INET (ip, _) -> if Unix.is_inet6_addr ip then Unix.PF_INET6 else Unix.PF_INET
    | Unix.ADDR_UNIX _ -> Unix.PF_UNIX
  in
  let fd = Unix.socket domain Unix.SOCK_STREAM 0 in
  (try
     Unix.setsockopt_float fd Unix.SO_RCVTIMEO 10.0;
     Unix.setsockopt_float fd Unix.SO_SNDTIMEO 10.0
   with _ -> ());
  (try Unix.connect fd addr with e -> (try Unix.close fd with _ -> ()); raise e);
  fd

let send_all (fd : Unix.file_descr) (buf : string) : unit =
  let total = String.length buf in
  let written = ref 0 in
  while !written < total do
    let n = Unix.write_substring fd buf !written (total - !written) in
    if n = 0 then failwith "service_wrap_http: write returned 0";
    written := !written + n
  done

let read_until_eof (fd : Unix.file_descr) : string =
  let buf = Buffer.create 4096 in
  let chunk = Bytes.create 4096 in
  let rec loop () =
    let n = Unix.read fd chunk 0 (Bytes.length chunk) in
    if n = 0 then () else (Buffer.add_subbytes buf chunk 0 n; loop ())
  in
  loop ();
  Buffer.contents buf

let perform_request ~(host : string) ~(port : int) ~(req_bytes : string) : string =
  let fd = socket_connect ~host ~port in
  let finish () = try Unix.close fd with _ -> () in
  (try
     send_all fd req_bytes;
     (try Unix.shutdown fd Unix.SHUTDOWN_SEND with _ -> ());
     let resp = read_until_eof fd in
     finish (); resp
   with e -> finish (); raise e)

(* ------------------------------------------------------------------
   rml= file read (Stage 2). `rml=`'s decoded value is treated as a
   local file path, resolved against FACTOIDAL_SERVICE_RML_BASE (default
   the current working directory) -- per this task's own brief ("local
   file path in CLI context; vendored fixture in tests"), not a lookup
   into the query's own already-loaded graphs (service_endpoint_lookup's
   fixed wf_iri -> option graph_store signature has no dataset parameter
   to reach that data through -- see SPARQL.Service.Wrap.fst Part 6's
   banner for the full reasoning).
   ------------------------------------------------------------------ *)

let read_file_opt (path : string) : string option =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let b = Bytes.create n in
    really_input ic b 0 n;
    close_in ic;
    Some (Bytes.to_string b)
  with _ -> None

let resolve_rml_path (name : string) : string =
  if Filename.is_relative name then
    match opt_env "FACTOIDAL_SERVICE_RML_BASE" with
    | Some base -> Filename.concat base name
    | None -> name
  else name

(* ------------------------------------------------------------------
   FStar_Pervasives_Native.option <-> OCaml option, mirroring
   bin/rml-runner/rml_runner.ml's own opt_of_fs/fs_of_opt convention.
   ------------------------------------------------------------------ *)

let opt_of_fs = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let fs_of_opt = function
  | Some x -> FStar_Pervasives_Native.Some x
  | None -> FStar_Pervasives_Native.None

(* ------------------------------------------------------------------
   Top-level: try to resolve a wrap+ IRI. None means "endpoint not
   resolved at all" (opt-out, wrap+ prefix unrecognized, host not
   allowlisted, or the fetch itself failed) -- the SAME outcome an
   unregistered SERVICE endpoint already has today, so no new failure
   shape exists at the SPARQL-semantics layer (design doc §2.6's own
   framing). Every exception (DNS failure, connection refused, socket
   timeout, malformed HTTP response) is caught here and turned into
   None -- "fetch failure -> clean SERVICE error, not a crash."
   ------------------------------------------------------------------ *)

let try_resolve (iri : string) : RDF_Graph_Executable.rdf_graph option =
  if not (is_opted_in ()) then None
  else
    try
      match opt_of_fs (SPARQL_Service_Wrap.parse_wrap_iri iri) with
      | None -> None
      | Some wt ->
        let req = SPARQL_Service_Wrap.build_wrap_get_request wt in
        let host = req.SPARQL_Service_Wrap.wr_host in
        let port = Z.to_int req.SPARQL_Service_Wrap.wr_port in
        if not (host_allowed host) then None
        else begin
          let req_bytes = SPARQL_HTTP_Client.format_request req.SPARQL_Service_Wrap.wr_msg in
          let raw = perform_request ~host ~port ~req_bytes in
          match SPARQL_HTTP_Client.parse_http_response raw (Z.of_int 16384) (Z.of_int (16 * 1024 * 1024)) with
          | FStar_Pervasives.Inr _ -> None
          | FStar_Pervasives.Inl resp ->
            let rml_ttl_text =
              match opt_of_fs (SPARQL_Service_Wrap.wrap_target_rml_name wt) with
              | None -> None
              | Some name -> read_file_opt (resolve_rml_path name)
            in
            let triples =
              SPARQL_Service_Wrap.resolve_wrap_response
                iri
                resp.SPARQL_HTTP_Client.rsp_status
                resp.SPARQL_HTTP_Client.rsp_headers
                resp.SPARQL_HTTP_Client.rsp_body
                (fs_of_opt rml_ttl_text)
            in
            Some triples
        end
    with _ -> None

let () = Service_wrap_hook.resolver := try_resolve
