(* shexc_parser_unit.ml — pins Parser.ShExC.fst's (Stage 9) ShExC compact-
   syntax parser against a battery of small in-repo schemas, independent
   of the vendored shexTest submodule (that corpus's own acceptance gate
   is bin/shex-runner --differential: 433/433 schemas/ pairs structurally
   equal as of this parser's landing -- see docs/designissues/
   2026-07-05-shex-program-plan.md). This file exercises the constructs
   individually (so a future regression names exactly which grammar
   piece broke) plus two end-to-end ShExC-vs-hand-written-ShExJ
   equality checks via the same ShEx.SchemaEq.fst comparator the
   differential runner uses.

   CLAUDE.md rule #25: the summary line spells out "N pass, N fail". *)

let passed = ref 0
let failed = ref 0

let check_bool ~name (b : bool) =
  if b then begin incr passed; Printf.printf "  PASS  %s\n" name end
  else begin incr failed; Printf.printf "  FAIL  %s\n" name end

let opt_is_some ~name (o : 'a FStar_Pervasives_Native.option) =
  match o with
  | FStar_Pervasives_Native.Some _ -> incr passed; Printf.printf "  PASS  %s (parsed)\n" name
  | FStar_Pervasives_Native.None -> incr failed; Printf.printf "  FAIL  %s (Parser_ShExC returned None)\n" name

let opt_is_none ~name (o : 'a FStar_Pervasives_Native.option) =
  match o with
  | FStar_Pervasives_Native.None -> incr passed; Printf.printf "  PASS  %s (correctly rejected)\n" name
  | FStar_Pervasives_Native.Some _ -> incr failed; Printf.printf "  FAIL  %s (expected rejection, but parsed)\n" name

let parse (text : string) = Parser_ShExC.parse_shexc_schema text ""

(* Structural-equality check against a hand-written ShExJ twin, via the
   same ShEx_SchemaEq.shex_schema_equal comparator bin/shex-runner
   --differential uses -- so this file's pins can never silently drift
   from what the differential oracle actually checks. *)
let check_equiv ~name (shexc_text : string) (shexj_text : string) =
  match parse shexc_text, ShEx_Schema.decode_shex_schema shexj_text "" with
  | FStar_Pervasives_Native.Some a, FStar_Pervasives_Native.Some b ->
    check_bool ~name (ShEx_SchemaEq.shex_schema_equal a b)
  | FStar_Pervasives_Native.None, _ ->
    incr failed; Printf.printf "  FAIL  %s (ShExC side returned None)\n" name
  | _, FStar_Pervasives_Native.None ->
    incr failed; Printf.printf "  FAIL  %s (hand-written ShExJ twin failed to decode -- test bug)\n" name

let () =
  (* --- directives --- *)
  opt_is_some ~name:"PREFIX + BASE directives, named prefix"
    (parse {|
      BASE <http://a.example/>
      PREFIX ex: <http://a.example/>
      <S1> { ex:p1 . }
    |});
  opt_is_some ~name:"PREFIX directive, DEFAULT (empty) prefix"
    (parse {|
      PREFIX : <http://a.example/>
      :S1 { :p1 . }
    |});
  opt_is_some ~name:"case-insensitive directive keywords (BaSe / prefix)"
    (parse {|
      BaSe <http://a.example/>
      prefix ex: <http://a.example/>
      <S1> { ex:p1 . }
    |});
  opt_is_some ~name:"IMPORT directive"
    (parse {|
      IMPORT <other-schema>
      <http://a.example/S1> { <http://a.example/p1> . }
    |});

  (* --- shapeExpr algebra: AND/OR/NOT, flat n-ary chains --- *)
  check_equiv ~name:"bare 3-way AND flattens to one ShapeAnd"
    {|<http://a.example/S1> {
        <http://a.example/p1> .
      } AND {
        <http://a.example/p2> .
      } AND {
        <http://a.example/p3> .
      }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"ShapeAnd","shapeExprs":[
          {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p1"}},
          {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p2"}},
          {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p3"}}
        ]}}]}|};
  check_equiv ~name:"parenthesized AND stays nested, does not flatten with outer AND"
    {|<http://a.example/S1> ({
        <http://a.example/p1> .
      } AND {
        <http://a.example/p2> .
      }
      ) AND {
        <http://a.example/p3> .
      }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"ShapeAnd","shapeExprs":[
          {"type":"ShapeAnd","shapeExprs":[
            {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p1"}},
            {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p2"}}
          ]},
          {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p3"}}
        ]}}]}|};
  check_equiv ~name:"NOT . reifies the wildcard as an empty Shape, not an empty NodeConstraint"
    {|<http://a.example/S1> {
        <http://a.example/p1> NOT .
      }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1",
          "valueExpr":{"type":"ShapeNot","shapeExpr":{"type":"Shape"}}}}}]}|};
  check_equiv ~name:"bare (uncombined) . omits valueExpr entirely"
    {|<http://a.example/S1> { <http://a.example/p1> . }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1"}}}]}|};

  (* --- nonLitNodeConstraint + shapeOrRef implicit AND (all facet shapes) --- *)
  check_equiv ~name:"IRI {} implicit-AND flattens with a following explicit AND"
    {|<http://a.example/S1> IRI {
        <http://a.example/p1> .
      } AND CLOSED {
        <http://a.example/p1> .
      }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"ShapeAnd","shapeExprs":[
          {"type":"NodeConstraint","nodeKind":"iri"},
          {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p1"}},
          {"type":"Shape","closed":true,"expression":{"type":"TripleConstraint","predicate":"http://a.example/p1"}}
        ]}}]}|};
  check_equiv ~name:"bare facet (LENGTH) + shapeDefinition suffix"
    {|<http://a.example/S1> LENGTH 19 { <http://a.example/p1> . }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"ShapeAnd","shapeExprs":[
          {"type":"NodeConstraint","length":19},
          {"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p1"}}
        ]}}]}|};

  (* --- cardinality: *, +, ?, {m,n}, {m,}, {m,*} --- *)
  check_equiv ~name:"cardinality {2,*} (explicit-star unbounded)"
    {|<http://a.example/S1> { <http://a.example/p1> .{2,*} }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1","min":2,"max":-1}}}]}|};
  check_equiv ~name:"cardinality {2,} (comma-then-brace unbounded)"
    {|<http://a.example/S1> { <http://a.example/p1> .{2,} }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1","min":2,"max":-1}}}]}|};
  check_equiv ~name:"cardinality ? on a bracketed group carries onto the group itself"
    {|<http://a.example/S1> {
        ( <http://a.example/p1> . ; <http://a.example/p2> . )?
      }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"EachOf","min":0,"max":1,
          "expressions":[
            {"type":"TripleConstraint","predicate":"http://a.example/p1"},
            {"type":"TripleConstraint","predicate":"http://a.example/p2"}
          ]}}}]}|};

  (* --- value sets: stems, stem ranges, wildcard-with-exclusions --- *)
  check_equiv ~name:"IRI stem (no exclusions) decodes to IriStem, not an empty-exclusion IriStemRange"
    {|<http://a.example/S1> { <http://a.example/p1> [<http://a.example/v>~] }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1","valueExpr":{"type":"NodeConstraint","values":[
            {"type":"IriStem","stem":"http://a.example/v"}]}}}}]}|};
  check_equiv ~name:"IRI stem range with exclusions"
    {|<http://a.example/S1> { <http://a.example/p1> [<http://a.example/v>~ - <http://a.example/v1>] }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1","valueExpr":{"type":"NodeConstraint","values":[
            {"type":"IriStemRange","stem":"http://a.example/v","exclusions":["http://a.example/v1"]}]}}}}]}|};
  check_equiv ~name:"wildcard stem range ('.' + typed exclusions)"
    {|<http://a.example/S1> { <http://a.example/p1> [. - <http://a.example/v1> - <http://a.example/v2>] }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1","valueExpr":{"type":"NodeConstraint","values":[
            {"type":"IriStemRange","stem":{"type":"Wildcard"},
             "exclusions":["http://a.example/v1","http://a.example/v2"]}]}}}}]}|};

  (* --- numeric facet lexeme normalization (ShEx.SchemaEq's decimal-value
     comparison, not string equality -- "5.5E0" vs "5.5" are the same
     xsd:decimal value) --- *)
  check_bool ~name:"numeric_lexeme_eq: 5.5E0 == 5.5"
    (ShEx_SchemaEq.numeric_lexeme_eq "5.5E0" "5.5");
  check_bool ~name:"numeric_lexeme_eq: 0E0 == 0.0"
    (ShEx_SchemaEq.numeric_lexeme_eq "0E0" "0.0");
  check_bool ~name:"numeric_lexeme_eq: distinguishes genuinely different values"
    (not (ShEx_SchemaEq.numeric_lexeme_eq "5.5" "5.6"));

  (* --- EXTRA / CLOSED / EXTENDS --- *)
  check_equiv ~name:"EXTRA with multiple predicates + CLOSED"
    {|<http://a.example/S1> CLOSED EXTRA <http://a.example/p1> <http://a.example/p2> {
        <http://a.example/p1> .
      }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","closed":true,
          "extra":["http://a.example/p1","http://a.example/p2"],
          "expression":{"type":"TripleConstraint","predicate":"http://a.example/p1"}}}]}|};
  check_equiv ~name:"EXTENDS (shapeExprRef target)"
    {|<http://a.example/S1> { <http://a.example/p1> . }
      <http://a.example/S2> EXTENDS @<http://a.example/S1> { }|}
    {|{"type":"Schema","shapes":[
        {"type":"ShapeDecl","id":"http://a.example/S1",
         "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p1"}}},
        {"type":"ShapeDecl","id":"http://a.example/S2",
         "shapeExpr":{"type":"Shape","extends":["http://a.example/S1"]}}
      ]}|};

  (* --- 'a' keyword (rdf:type shorthand), inverse '^', EACHOF/ONEOF --- *)
  check_equiv ~name:"bare 'a' predicate shorthand for rdf:type"
    {|<http://a.example/S1> { a . }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://www.w3.org/1999/02/22-rdf-syntax-ns#type"}}}]}|};
  check_equiv ~name:"inverse '^' senseFlags"
    {|<http://a.example/S1> { ^<http://a.example/p1> . }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "inverse":true,"predicate":"http://a.example/p1"}}}]}|};
  check_equiv ~name:"OneOf ('|') grouping"
    {|<http://a.example/S1> { <http://a.example/p1> .| <http://a.example/p2> . }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"OneOf","expressions":[
          {"type":"TripleConstraint","predicate":"http://a.example/p1"},
          {"type":"TripleConstraint","predicate":"http://a.example/p2"}
        ]}}}]}|};

  (* --- shapeRef whitespace-tolerant form, START --- *)
  check_equiv ~name:"'@ ex:Label' (whitespace between '@' and the shapeRef label)"
    {|PREFIX ex: <http://a.example/>
      <http://a.example/S1> { <http://a.example/p1> @ ex:S2 }
      <http://a.example/S2> { <http://a.example/p2> . }|}
    {|{"type":"Schema","shapes":[
        {"type":"ShapeDecl","id":"http://a.example/S1",
         "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
           "predicate":"http://a.example/p1","valueExpr":"http://a.example/S2"}}},
        {"type":"ShapeDecl","id":"http://a.example/S2",
         "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint","predicate":"http://a.example/p2"}}}
      ]}|};
  opt_is_some ~name:"START = shapeExpression"
    (parse {|
      PREFIX ex: <http://a.example/>
      START = @ex:S1
      ex:S1 { ex:p1 . }
    |});

  (* --- comments, annotations, semActs --- *)
  opt_is_some ~name:"line comment (#) and block comment (/* */)"
    (parse {|
      # a line comment
      <http://a.example/S1> /* a block comment */ {
        <http://a.example/p1> . # trailing comment
      }
    |});
  check_equiv ~name:"annotation (// pred obj)"
    {|<http://a.example/S1> {
        <http://a.example/p1> . //  <http://a.example/annot1> "v1"
      }|}
    {|{"type":"Schema","shapes":[{"type":"ShapeDecl","id":"http://a.example/S1",
        "shapeExpr":{"type":"Shape","expression":{"type":"TripleConstraint",
          "predicate":"http://a.example/p1",
          "annotations":[{"type":"Annotation","predicate":"http://a.example/annot1",
            "object":{"value":"v1"}}]}}}]}|};
  opt_is_some ~name:"semAct with code body (%iri{ code %})"
    (parse {|<http://a.example/S1> {
        <http://a.example/p1> . %<http://shex.io/extensions/Test/>{ print(o) %}
      }|});
  opt_is_some ~name:"semAct with no code (bare %iri%)"
    (parse {|<http://a.example/S1> {
        <http://a.example/p1> . %<http://shex.io/extensions/Test/>%
      }|});

  (* --- EXTERNAL, ABSTRACT --- *)
  opt_is_some ~name:"EXTERNAL shape" (parse {|<http://a.example/S1> EXTERNAL|});
  opt_is_some ~name:"ABSTRACT shape"
    (parse {|ABSTRACT <http://a.example/S1> { <http://a.example/p1> . }|});

  Printf.printf "shexc_parser_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
