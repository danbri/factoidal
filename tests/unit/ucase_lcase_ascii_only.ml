(* ucase_lcase_ascii_only.ml — documents that SPARQL UCASE/LCASE are
   currently ASCII-only (per CLAUDE.md anti-pattern #10 and the demo
   review's finding #2 dated 2026-04-20).

   We exercise the underlying primitive the evaluator uses
   (SPARQL11_Algebra.string_upper / string_lower). The goals:

   1. Confirm ASCII upper/lower still works — baseline invariant.
   2. Confirm that a UTF-8 multi-byte character (German ü / U+00FC)
      passes through uppercase UNCHANGED rather than corrupting into
      invalid-UTF-8 replacement bytes. Clean passthrough is the
      documented ASCII-only limitation; byte corruption would be a
      NEW and more serious bug than #91 and needs to surface loudly.
   3. Same for lowercase of a multi-byte character.

   If any of the ASCII-only behaviour asserts start FAILING, that
   means UTF-8 casing got silently introduced somewhere and needs
   confirmation against rfc3629 + the SPARQL 1.1 test suite. *)

let passed = ref 0
let failed = ref 0
let expected_failures = ref 0

let check ~name ~expected_pass ok_bool =
  if ok_bool then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else if not expected_pass then begin
    incr expected_failures;
    Printf.printf "  XFAIL %s  (documented limitation)\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

let hex_of_string s =
  let b = Buffer.create (String.length s * 3) in
  String.iter (fun c ->
    Buffer.add_string b (Printf.sprintf "%02x " (Char.code c))
  ) s;
  String.trim (Buffer.contents b)

let () =
  Printf.printf "== ucase_lcase_ascii_only ==\n";

  (* 1. Plain ASCII round-trip — baseline. *)
  let u_hello = SPARQL11_Algebra.string_upper "hello" in
  check ~name:"ucase ascii 'hello' -> 'HELLO'" ~expected_pass:true
    (u_hello = "HELLO");

  let l_hello = SPARQL11_Algebra.string_lower "HELLO" in
  check ~name:"lcase ascii 'HELLO' -> 'hello'" ~expected_pass:true
    (l_hello = "hello");

  (* 2. Mixed ASCII + multi-byte. The "ü" (U+00FC, UTF-8 bytes c3 bc) is
     expected to pass through unchanged under both directions of casing.
     The ASCII portion should still get cased.

     Documented limitation: "ü" would ideally uppercase to "Ü" (U+00DC,
     UTF-8 bytes c3 9c) under Unicode casing rules, but Factoidal's
     FStar_String.uppercase is ASCII-only, so it leaves the bytes alone.
     That is fine (byte-preserving); if instead the function were to
     operate on the individual UTF-8 bytes (treat c3 as a letter and
     uppercase some of them), we'd get invalid UTF-8. This assertion
     specifically checks for clean passthrough. *)
  let input_muller = "Eve M\xc3\xbcller" in  (* "Eve Müller" *)
  let u_muller = SPARQL11_Algebra.string_upper input_muller in
  let expected_u = "EVE M\xc3\xbcLLER" in
  check ~name:"ucase 'Eve Müller' preserves UTF-8 bytes of ü, cases ASCII"
    ~expected_pass:true
    (u_muller = expected_u);
  if u_muller <> expected_u then
    Printf.printf "      got:      %s\n      got hex:  %s\n      want hex: %s\n"
      u_muller (hex_of_string u_muller) (hex_of_string expected_u);

  let l_muller = SPARQL11_Algebra.string_lower input_muller in
  let expected_l = "eve m\xc3\xbcller" in
  check ~name:"lcase 'Eve Müller' preserves UTF-8 bytes of ü, cases ASCII"
    ~expected_pass:true
    (l_muller = expected_l);
  if l_muller <> expected_l then
    Printf.printf "      got:      %s\n      got hex:  %s\n      want hex: %s\n"
      l_muller (hex_of_string l_muller) (hex_of_string expected_l);

  (* 3. Unicode-aware casing would turn 'ü' into 'Ü'. Our implementation
     DOES NOT do this; this is the documented limitation. Assert the
     would-be Unicode-aware outcome is NOT what we produce, so that if
     someone wires in a Unicode casing library and accidentally leaves
     this unit-test suite alone, the documented-limitation marker flips
     and they know to update this file. *)
  let unicode_aware_would_be = "EVE M\xc3\x9cLLER" in  (* Ü *)
  check ~name:"ucase does NOT do Unicode-aware ü -> Ü (documented limitation)"
    ~expected_pass:false
    (u_muller = unicode_aware_would_be);

  Printf.printf "summary: %d pass, %d expected-fail, %d unexpected fail\n"
    !passed !expected_failures !failed;
  if !failed > 0 then exit 1
