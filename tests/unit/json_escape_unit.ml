(* json_escape_unit.ml — pins the escape ORDER of
   SPARQL.JSON.Escape.json_escape.

   2026-07-04: push_escape2 / push_u_escape prepended their characters
   in the wrong order relative to json_escape's final List.Tot.rev, so
   every generated escape came out mirrored ("n\\" instead of "\\n",
   "\\"" as ""\\"). The main SPARQL-results-JSON path has its own
   escaper, so the W3C suites never saw it; the first strict-JSON
   consumer of this function (the npm-entry bundle's dataset envelope)
   crashed on its own output. These cases assert the exact escaped
   strings so a future accumulator-order change fails here first. *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if String.equal expected actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %S got %S\n" name expected actual
  end

let () =
  let e = SPARQL_JSON_Escape.json_escape in
  check ~name:"plain passthrough" "abc" (e "abc");
  check ~name:"quote" "\\\"x\\\"" (e "\"x\"");
  check ~name:"backslash" "a\\\\b" (e "a\\b");
  check ~name:"newline" "l1\\nl2" (e "l1\nl2");
  check ~name:"cr-tab" "a\\r\\tb" (e "a\r\tb");
  check ~name:"backspace-formfeed" "\\b\\f" (e "\b\012");
  (* Control byte below 0x20 without a short form: \u escape, lowercase
     hex, digits in high-to-low order. *)
  check ~name:"u-escape 0x01" "\\u0001" (e "\001");
  check ~name:"u-escape 0x1f" "\\u001f" (e "\031");
  (* Non-ASCII passes through as raw UTF-8 bytes, unescaped. *)
  check ~name:"utf8 passthrough" "caf\xc3\xa9" (e "caf\xc3\xa9");
  (* Round-trip through OCaml's own strict JSON idea of the world: the
     escaped form embedded in quotes must be exactly what a JSON writer
     would emit for the raw string. *)
  check ~name:"mixed"
    "{\\\"k\\\":\\\"v\\nw\\\"}"
    (e "{\"k\":\"v\nw\"}");
  Printf.printf "json_escape_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
