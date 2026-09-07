(* owl_dt_range_clash_unit.ml -- pins OWL.Closure's is_inconsistent
   check (10), "dt-range-clash", after the 2026-09-07 soundness repair
   recorded in
   docs/designissues/2026-09-07-fstar-owl-soundness-audit.md.

   The check used to decide "the literal's datatype is outside the
   declared range's value space" by asking whether the literal's
   datatype REACHES the range datatype in `xsd_hierarchy_edges`. That
   table is a TREE, so two datatypes can have overlapping value spaces
   with neither an ancestor of the other: xsd:int and
   xsd:nonNegativeInteger both reach xsd:integer and neither reaches the
   other. On the old test, `p rdfs:range xsd:nonNegativeInteger` with
   `x p "5"^^xsd:int` was reported INCONSISTENT, and 5 is a non-negative
   integer (XSD 1.1 Datatypes 3.4.20). That was an unsound
   inconsistency verdict.

   The repaired check asks whether the two datatypes' VALUE SPACES are
   disjoint, which for the recognised set means: are they in different
   families among {character strings, booleans, numbers} (XSD 1.1
   Datatypes 3.3). Cases 1-4 below pin what must still fire; cases 5-8
   pin what must no longer fire.

   Rule anchors: #25 (pass/fail counts spelled out), #3 (labelled). *)

let passed = ref 0
let failed = ref 0

let check ~name (cond : bool) =
  if cond then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

open RDF_Graph_Executable

let xsd n = "http://www.w3.org/2001/XMLSchema#" ^ n
let ex n = "http://example.org/" ^ n

let lit value dt : rdf_term =
  T_Literal { lexical_form = value; datatype = dt;
              lang_tag = None; direction = None }

(* A minimal graph: `p rdfs:range <range_dt>` and `s p "lex"^^<lit_dt>`. *)
let range_graph range_dt lex lit_dt : rdf_graph =
  [ { s = S_IRI (ex "p"); p = rdfs_range; o = T_IRI range_dt };
    { s = S_IRI (ex "s"); p = ex "p";     o = lit lex lit_dt } ]

let clashes range_dt lex lit_dt =
  is_inconsistent (range_graph range_dt lex lit_dt)

let () =
  Printf.printf "owl_dt_range_clash_unit\n";

  (* --- Must STILL fire: the value spaces are genuinely disjoint. --- *)

  (* 1. string literal against a numeric range. This is the
        `string-integer-clash` InconsistencyTest's shape. *)
  check ~name:"string-literal-vs-integer-range clashes"
    (clashes (xsd "integer") "aString" (xsd "string"));

  (* 2. numeric literal against a string range. *)
  check ~name:"integer-literal-vs-string-range clashes"
    (clashes (xsd "string") "5" (xsd "integer"));

  (* 3. boolean literal against a numeric range. *)
  check ~name:"boolean-literal-vs-decimal-range clashes"
    (clashes (xsd "decimal") "true" (xsd "boolean"));

  (* 4. string literal against a boolean range. *)
  check ~name:"string-literal-vs-boolean-range clashes"
    (clashes (xsd "boolean") "yes" (xsd "string"));

  (* --- Must NOT fire: the value spaces overlap or coincide. --- *)

  (* 5. THE REGRESSION. xsd:int and xsd:nonNegativeInteger overlap;
        neither reaches the other in xsd_hierarchy_edges. 5 IS a
        non-negative integer. *)
  check ~name:"int-literal-vs-nonNegativeInteger-range does NOT clash"
    (not (clashes (xsd "nonNegativeInteger") "5" (xsd "int")));

  (* 6. The mirror direction, also an overlap and also not a clash. *)
  check ~name:"nonNegativeInteger-literal-vs-int-range does NOT clash"
    (not (clashes (xsd "int") "5" (xsd "nonNegativeInteger")));

  (* 7. A genuine subtype pair, which the old check already allowed. *)
  check ~name:"byte-literal-vs-integer-range does NOT clash"
    (not (clashes (xsd "integer") "5" (xsd "byte")));

  (* 8. Identical datatypes. *)
  check ~name:"integer-literal-vs-integer-range does NOT clash"
    (not (clashes (xsd "integer") "5" (xsd "integer")));

  (* 9. An unrecognised datatype gets no verdict, never a clash. *)
  check ~name:"unrecognised-datatype does NOT clash"
    (not (clashes (xsd "integer") "x" (ex "MyType")));

  (* --- Why case 5 is a regression and not a hypothetical. ---
     `xsd_is_subtype` is the predicate the old check used and is still
     defined in OWL.Closure. Cases 10 and 11 pin the two facts that
     made the old check fire on case 5: neither of the two overlapping
     datatypes reaches the other in `xsd_hierarchy_edges`, so the old
     test `not (lit.datatype = d_range) && not (xsd_is_subtype ...)`
     was true in both directions. Case 12 pins that a genuine subtype
     pair DOES reach, so the predicate itself is not simply broken --
     the tree is correct as a subtype tree and wrong as a
     disjointness test. Without these three the suite would not show
     that case 5 ever failed, only that it passes now. *)
  check ~name:"old predicate: int does not reach nonNegativeInteger"
    (not (xsd_is_subtype (xsd "int") (xsd "nonNegativeInteger")));
  check ~name:"old predicate: nonNegativeInteger does not reach int"
    (not (xsd_is_subtype (xsd "nonNegativeInteger") (xsd "int")));
  check ~name:"old predicate: byte does reach integer"
    (xsd_is_subtype (xsd "byte") (xsd "integer"));

  Printf.printf "owl_dt_range_clash_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed <> 0 then exit 1
