/-
ShEx/CompactTests — what the ShExC reader got WRONG, pinned.

Every guard below is a schema the differential runner
(`Harness/ShExCRun.lean`, `lake exe l4shexc`) reported as a
disagreement between the compact reader and the ShExJ twin of the
same schema. Each names the corpus fixture that paid for it and the
answer the defect produced, because a rule without its war story does
not stick.

The corpus is `third_party/testing/shex/schemas/`: 442 `.shex` files,
each with a `.json` twin. Score after these fixes: 442 match, 0
mismatch, 0 declined (out of 442).
-/
import L4Factoidal.ShEx.Compact

namespace L4Factoidal.ShEx.Compact

/-! ## Reaching into a parsed schema

Every fixture below is one shape whose expression is one triple
constraint, so these three accessors reach everything the guards
look at. -/

def firstTc? (text : String) : Option TripleConstraint :=
  match parseShExC text with
  | .error _ => none
  | .ok sch  =>
    match sch.shapes with
    | d :: _ =>
        (match d.expr with
         | .shape sh =>
             (match sh.expression with
              | some (.tripleConstraint tc) => some tc
              | _                           => none)
         | _ => none)
    | [] => none

def firstNc? (text : String) : Option NodeConstraint :=
  (firstTc? text).bind (fun tc =>
    match tc with
    | .mk _ _ _ (some (.nodeConstraint nc)) _ _ _ _ => some nc
    | _ => none)

def firstValues (text : String) : List ValueSetValue :=
  match firstNc? text with
  | some nc => nc.values
  | none    => []

def cardOf (text : String) : Option (Int × Int) :=
  (firstTc? text).map (fun tc => match tc with | .mk _ _ _ _ mn mx _ _ => (mn, mx))

def parsed (text : String) : Bool :=
  match parseShExC text with | .ok _ => true | .error _ => false

/-! ## `//` opens an annotation; it is not an empty regular expression

The regex scanner reached `/` first and read `//` as a PATTERN with
no characters, leaving the annotation's predicate and object as loose
tokens. Every annotated schema then died at the closing brace with
"expected '}', found //" — 1inversedotAnnot3, kitchenSink, _all and
11 more. -/

#guard (tokenize "//".toList.toArray).toOption == some [Tok.punct "//"]

#guard parsed "<http://a.example/S1> {
   ^<http://a.example/p1> . //
      <http://a.example/annot1> \"1\" //
      <http://a.example/annot2> \"2\"
}"

/-! A shape definition carries its own annotations AFTER the closing
    brace. Leaving them made the statement reader see a loose `//`
    where the next shape label belonged (1dotShapeAnnotIRIREF). -/

#guard parsed "<http://a.example/S1> {
   <http://a.example/p1> .
} // <http://a.example/annot> <http://a.example/IRIREF>"

/-! ## `@` is a shape reference OR a language tag

`@fr` has no colon and no angle brackets, so it cannot be a shape
label. Reading it as one refused nine fixtures with "expected an IRI,
found @". -/

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [@fr] }"
       == [.language "fr"]

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [@fr~] }"
       == [.stem .language (.plain "fr")]

/-! `@~` is EVERY language: a language stem whose stem is empty. -/

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [@~] }"
       == [.stem .language (.plain "")]

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [@fr~ - @fr-be~] }"
       == [.stemRange .language (.plain "fr") [.stem "fr-be"]]

/-! A shape reference still reads as one: `@` then a label. -/

#guard (match firstTc? "<http://a.example/S1> { <http://a.example/p1> @<http://a.example/S2> }" with
        | some (.mk _ _ _ (some (.ref r)) _ _ _ _) => r == "http://a.example/S2"
        | _ => false)

/-! ## A wildcard stem range takes its KIND from its exclusions

`[. - "v1"]` is a `LiteralStemRange` and `[. - @fr-be]` a
`LanguageStemRange`; only the exclusions say which. Assuming an
`IriStemRange` disagreed with the ShExJ twin on every wildcard range
whose exclusions were not IRIs (1val1dotMinusliteral3,
1val1dotMinuslanguage3, 1val1dotMinusliteralStem3). -/

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [. - \"v1\"] }"
       == [.stemRange .literal .wildcard [.value (.literal "v1" none none)]]

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [. - @fr-be] }"
       == [.stemRange .language .wildcard [.lang "fr-be"]]

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [. - \"v1\"~] }"
       == [.stemRange .literal .wildcard [.stem "v1"]]

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [. - <http://a.example/v1>] }"
       == [.stemRange .iri .wildcard [.value (.iri "http://a.example/v1")]]

/-! ## `{` after a node constraint is a repeat range when a number follows

Reading `["a" "b"]{2,3}` as a shape definition made `2` a predicate
and refused the whole schema (kitchenSink). -/

#guard cardOf "<http://a.example/S1> { <http://a.example/p1> [\"a\" \"b\"]{2,3} }"
       == some (2, 3)

/-! A real shape definition after a node constraint still reads as
    one, so the guard above is not a licence to drop `{`. -/

#guard (match firstTc? "<http://a.example/S1> { <http://a.example/p1> IRI { <http://a.example/p2> . } }" with
        | some (.mk _ _ _ (some (.shapeAnd xs)) _ _ _ _) => xs.length == 2
        | _ => false)

/-! ## A numeric facet keeps its VALUE, not its spelling

`MININCLUSIVE 05`, `5`, `5.0` and `05.00E0` all denote five, and the
ShExJ twin writes whichever form its serialiser chose. Comparing
lexemes made ten fixtures differ over leading zeros, a trailing `.0`
or an `E0` — a disagreement about spelling reported as a
disagreement about the schema. -/

#guard canonNumericLexeme "05" == "5"
#guard canonNumericLexeme "5.0" == "5"
#guard canonNumericLexeme "05.00E0" == "5"
#guard canonNumericLexeme "04.50E0" == "4.5"
#guard canonNumericLexeme "4.5" == "4.5"
#guard canonNumericLexeme "-04.50" == "-4.5"
#guard canonNumericLexeme "+5" == "5"
#guard canonNumericLexeme "5E2" == "500"
#guard canonNumericLexeme "5E-2" == "0.05"
#guard canonNumericLexeme "0.0" == "0"
#guard canonNumericLexeme "-0.0" == "0"

#guard (firstNc? "<http://a.example/S1> {
   <http://a.example/p1> <http://www.w3.org/2001/XMLSchema#integer> MININCLUSIVE 05
}").bind (fun nc => nc.minInclusive) == some "5"

/-! ## A UCHAR is a way of WRITING a character

`<http://a.example/p1>` names `.../p1`. Carrying the escape
through verbatim built a DIFFERENT predicate, so a different schema
(1IRI_with_UCHAR.1dot). -/

#guard (match firstTc? "<http://a.example/S1> { <http://a.example/p\\u0031> . }" with
        | some (.mk _ _ p _ _ _ _ _) => p == "http://a.example/p1"
        | _ => false)

/-! In a regular expression a UCHAR is decoded and every OTHER
    backslash escape is carried through untouched: decoding `\t` and
    `\-` too would change what the pattern matches, decoding none of
    them left `a` where the twin has `a`
    (1literalPattern_with_REGEXP_escapes). -/

#guard (firstNc? "<http://a.example/S1> { <http://a.example/p1> LITERAL /^\\t\\-\\u0061$/ }").bind
         (fun nc => nc.pattern) == some "^\\t\\-a$"

/-! ## A language tag's value is its lowercase form

RDF 1.1 Concepts §3.3. `"x"@en-UK` and `"x"@en-uk` are one literal,
and the ShExJ twins write the lowercase form
(1val1STRING_LITERAL2_with_subtag). -/

#guard firstValues "<http://a.example/S1> { <http://a.example/p1> [\"L\"@en-UK] }"
       == [.object (.literal "L" (some "en-uk") none)]

/-! ## An ABSENT cardinality leaves a group unwrapped

Supplying `min: 1, max: 1` instead is a different document: the
ShExJ twins omit both (open2dotclose and 40 more). A bracketed
SINGLE member takes the cardinality itself rather than gaining a
wrapper (open1dotclosecardOpt). -/

#guard (match parseShExC "<http://a.example/S1> { ( <http://a.example/p1> . )? }" with
        | .ok sch =>
            (match sch.shapes with
             | d :: _ =>
                 (match d.expr with
                  | .shape sh =>
                      (match sh.expression with
                       | some (.tripleConstraint (.mk _ _ _ _ mn mx _ _)) => mn == 0 && mx == 1
                       | _ => false)
                  | _ => false)
             | [] => false)
        | .error _ => false)

end L4Factoidal.ShEx.Compact
