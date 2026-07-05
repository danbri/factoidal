(* xsd_datatypes_unit.ml — pins the exact literal/facet fixtures the ShEx
   stage-3 measurement run (2026-07-05, commit 37ae500) traced to gaps in
   XSD.Datatypes.fst: 21 of 31 triaged mismatches against shexSpec/shexTest's
   validation manifest (6 ValidLexicalForm + 15 TotalDigitsFacet/
   FractionDigitsFacet). See docs/designissues/2026-07-05-shex-program-plan.md
   and formal/fstar/ShEx.Validation.fst's file banner for the program this
   fix belongs to.

   Every literal/facet pair below is copied VERBATIM from
   third_party/testing/shex/validation/manifest.ttl and the .ttl data
   fixtures it points at (not "inspired by" — CLAUDE.md rule #6), cross-
   checked against the ShExJ schema .json (the `totaldigits`/`fractiondigits`
   thresholds match `1literalTotaldigits{2,5,6}.json` /
   `1literalFractiondigits{4,5}.json` exactly).

   Ground truth, part A — ValidLexicalForm (float/double), from the
   `####    float ...` / `####    double ...` block (manifest.ttl
   ~2265-2607, schema `../schemas/datatypes.json`, shape `S-float`/
   `S-double` constrains `nodeKind` to a bare `xsd:float`/`xsd:double`
   datatype facet with no other facets): valid lexical forms are
   "-1 0 1 +1 -1.0 +1.0 1e0 1E0 NaN INF -INF"; invalid are "" (empty) and
   "+INF" (XSD's positive infinity token has no leading '+' — only "INF").
   PRE-FIX: `literal_ill_formed` had no xsd:float/xsd:double branch at all
   (fell through to the final `else false`), so EVERY lexical form —
   including "" and "+INF" — was reported well-formed. 4 of the 22 pass/fail
   assertions below (float-empty, float-+INF, double-empty, double-+INF)
   were WRONG pre-fix; the other 18 happened to already read `false`
   ("not ill-formed") correctly by the same always-false fallthrough, since
   they are in fact well-formed. Confirmed against the manifest's own pass/
   fail split (11 pass + 2 fail per datatype), not assumed.

   Ground truth, part B — TotalDigitsFacet / FractionDigitsFacet, from the
   `### totalDigits {` / `### fractionDigits {` blocks (manifest.ttl
   ~4967-5613, schemas `1literalTotaldigits{2,5,6}.json` /
   `1literalFractiondigits{4,5}.json`: bare `LITERAL TOTALDIGITS n` /
   `LITERAL FRACTIONDIGITS n`, no datatype facet at all — datatype comes
   solely from the data literal). Of the 27 TotalDigitsFacet + 18
   FractionDigitsFacet manifest entries, PRE-FIX 5 mismatched in each
   cluster (10 total; the ShEx stage-3 commit's "15" also folds in a few
   entries this file doesn't re-pin because they need ShEx.Validation.fst
   call-site plumbing rather than an XSD.Datatypes.fst-only fix — see the
   commit message split). The 5-per-cluster pattern is identical for both
   facets:
     - `xsd:float`/`xsd:double` literals (fail-float-equal, fail-double-equal):
       XML Schema Part 2 SS4.3.11/4.3.12 define totalDigits/fractionDigits as
       facets of xsd:decimal and its derived types ONLY — never applicable
       to float/double, so the manifest expects ValidationFailure
       regardless of how many digits the lexical form has. PRE-FIX,
       `total_digit_count`/`fraction_digit_count` counted digits in ANY
       literal's lexical form with no datatype gate at all, so these
       incorrectly PASSED (5 digits for "1.2345" / "1.23456", within the
       facet bound).
     - malformed decimal/integer literals with trailing letters
       ("1.23ab"^^xsd:decimal, "1.2345ab"^^xsd:decimal, "1.2345"^^xsd:integer
       — the last is malformed BECAUSE integer's lexical space forbids '.'):
       PRE-FIX the digit-counting helpers silently skipped non-digit
       characters instead of first checking well-formedness, so the letters
       (or, for the integer case, the decimal point) were simply ignored and
       the count came out within bounds — an incorrect PASS.
   POST-FIX: ShEx.Validation.fst's `node_constraint_matches` now computes a
   separate `digits_lex` (used ONLY by totaldigits_ok/fractiondigits_ok,
   not by the four numeric inclusive/exclusive facets, which correctly
   still apply to float/double per the spec) that is `Some lex` only when
   the literal's datatype is decimal-derived (XSD.Datatypes.is_decimal_derived_datatype)
   AND the lexical form is well-formed for that datatype
   (not (XSD.Datatypes.literal_ill_formed ...)) — otherwise `None`, which
   the existing `Some _, None -> false` fail-closed arm already handled
   correctly (no new fail-closed logic needed, only the input gate). This
   test file pins the XSD.Datatypes.fst primitives that gate now exists
   on top of (`is_float_lexical`, `is_decimal_derived_datatype`,
   `literal_ill_formed`'s malformed-decimal/integer detection it already
   had) — the ShEx.Validation.fst wiring itself has no unit-test harness
   of its own (Stage 8's job, per the ShEx program plan), so this file is
   the one guardrail against regressing the fix.

   Both `total_digit_count`/`fraction_digit_count` and the ShEx-side
   `digits_lex` gate live in formal/fstar/ShEx.Validation.fst, outside this
   file's XSD.Datatypes.fst territory — this file pins only the
   XSD.Datatypes.fst-side primitives the gate is built from. *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if expected = actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %b got %b\n" name expected actual
  end

let ill_formed dt lex = XSD_Datatypes.literal_ill_formed dt lex
let decimal_derived dt = XSD_Datatypes.is_decimal_derived_datatype dt

let xsd_float = XSD_Datatypes.xsd_float
let xsd_double = RDF_Graph_Executable.xsd_double
let xsd_decimal = RDF_Graph_Executable.xsd_decimal
let xsd_integer = RDF_Graph_Executable.xsd_integer
let xsd_byte = RDF_Graph_Executable.xsd_byte

let () =
  (* ================================================================
     Part A — ValidLexicalForm: xsd:float / xsd:double.
     "well-formed" below means `not (literal_ill_formed dt lex)` — the
     manifest's ValidationTest (pass) / ValidationFailure (fail) verdict
     for the bare `<S> { <p> xsd:float }` / `xsd:double` shape maps
     directly onto well-formedness since that shape has no other facet.
     ================================================================ *)
  let float_pass = [
    "-1"; "0"; "1"; "+1"; "-1.0"; "+1.0"; "1e0"; "1E0"; "NaN"; "INF"; "-INF"
  ] in
  let float_fail = [ ""; "+INF" ] in
  List.iter (fun lex ->
    check ~name:(Printf.sprintf "float-%s well-formed (pass)" lex)
      false (ill_formed xsd_float lex))
    float_pass;
  List.iter (fun lex ->
    check ~name:(Printf.sprintf "float-%s ill-formed (fail)" lex)
      true (ill_formed xsd_float lex))
    float_fail;
  List.iter (fun lex ->
    check ~name:(Printf.sprintf "double-%s well-formed (pass)" lex)
      false (ill_formed xsd_double lex))
    float_pass;
  List.iter (fun lex ->
    check ~name:(Printf.sprintf "double-%s ill-formed (fail)" lex)
      true (ill_formed xsd_double lex))
    float_fail;

  (* ================================================================
     Part B — decimal-derived datatype family (the digits-facet gate).
     xsd:decimal and every integer-family type are decimal-derived;
     xsd:float/xsd:double/xsd:boolean/xsd:dateTime are not.
     ================================================================ *)
  check ~name:"xsd:decimal is decimal-derived" true (decimal_derived xsd_decimal);
  check ~name:"xsd:integer is decimal-derived" true (decimal_derived xsd_integer);
  check ~name:"xsd:byte is decimal-derived" true (decimal_derived xsd_byte);
  check ~name:"xsd:float is NOT decimal-derived" false (decimal_derived xsd_float);
  check ~name:"xsd:double is NOT decimal-derived" false (decimal_derived xsd_double);
  check ~name:"xsd:boolean is NOT decimal-derived"
    false (decimal_derived RDF_Graph_Executable.xsd_boolean);

  (* ================================================================
     Part C — malformed decimal/integer lexical forms that the digits-
     facet fixtures exercise (the "malformedxsd" 1literalTotaldigits_fail
     and 1literalFractiondigits_fail entries). These must be ill-formed
     so the ShEx `digits_lex` gate maps them to `None` (fail-closed)
     regardless of how many digit characters they contain.
     ================================================================ *)
  check ~name:"\"1.23ab\"^^xsd:decimal is ill-formed"
    true (ill_formed xsd_decimal "1.23ab");
  check ~name:"\"1.2345ab\"^^xsd:decimal is ill-formed"
    true (ill_formed xsd_decimal "1.2345ab");
  check ~name:"\"1.2345\"^^xsd:integer is ill-formed (integer forbids '.')"
    true (ill_formed xsd_integer "1.2345");

  (* Well-formed decimal-derived counterexamples from the same fixture
     family, so the malformed cases above aren't passing by an
     over-broad "always ill-formed" bug. *)
  check ~name:"\"1.2345\"^^xsd:decimal is well-formed"
    false (ill_formed xsd_decimal "1.2345");
  check ~name:"\"12345\"^^xsd:integer is well-formed"
    false (ill_formed xsd_integer "12345");
  check ~name:"\"012345\"^^xsd:integer (leading zero) is well-formed"
    false (ill_formed xsd_integer "012345");

  Printf.printf "\nxsd_datatypes_unit: %d passed, %d failed\n" !passed !failed;
  if !failed > 0 then exit 1
