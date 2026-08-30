/-
L4Factoidal.Syntax.TurtleTests — build-time `#guard`s for the Turtle
and TriG parsers.

Every `#guard` here evaluates during elaboration, so a wrong answer is
a BUILD failure, not a silent regression. The suite is organised by
grammar production, one section per production cited in
`Syntax.Turtle`'s header, and closes with round-trips through the
landed N-Triples serialiser (`Graph.toNTriples`) and parser.

These are UNIT tests over hand-written fragments; the CONFORMANCE
measurement is `Harness/TurtleProbe.lean` running the real W3C files
(iron rule #6). Neither substitutes for the other: the probe says how
much of the suite passes, these say which grammar clause broke when it
stops passing.

The RFC 3986 §5.4 reference-resolution battery lives in
`Syntax.IriResolve` next to the code it checks.
-/

import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Test helpers

Turtle answers are compared as N-Triples TEXT wherever blank nodes are
absent (an exact, readable expectation) and by triple COUNT plus
`Graph.isomorphic?` where they are not. -/

/-- Parse Turtle and render the result as N-Triples, or return a
marker string. Used as the expectation shape for ground fragments. -/
def ttlToNT (s : String) (base : Option String := none) : String :=
  match parseTurtle s base with
  | .error e => s!"PARSE-ERROR: {e.msg}"
  | .ok g    => match Graph.toNTriples g with
                | .error e => s!"SERIALISE-ERROR: {e}"
                | .ok t    => t

/-- Did this fragment parse at all? -/
def ttlOk (s : String) (base : Option String := none) : Bool :=
  (parseTurtle s base).toOption.isSome

/-- Was this fragment REJECTED? (negative-syntax expectation) -/
def ttlRejects (s : String) (base : Option String := none) : Bool :=
  !(ttlOk s base)

/-- Triple count of a successful parse; `0` on failure (every negative
case is stated with `ttlRejects` instead, so a 0 here always means an
empty graph). -/
def ttlCount (s : String) (base : Option String := none) : Nat :=
  match parseTurtle s base with
  | .error _ => 0
  | .ok g    => g.length

/-- The fold entry point is allowed to choose its accumulator representation,
but must retain the ordinary parser's exact source graph order. -/
def ttlFold (s : String) (base : Option String := none) : Except ParseError Graph := do
  let reversed ← parseTurtleFold
    (fun accRev triples => triples.reverse ++ accRev) [] s base
  pure reversed.reverse

/-- The fold parser and ordinary parser produce the same successful graph.
This deliberately avoids comparing parser-error payloads, which are diagnostics
rather than part of RDF graph semantics. -/
def ttlFoldMatches (s : String) (base : Option String := none) : Bool :=
  match ttlFold s base, parseTurtle s base with
  | .ok folded, .ok ordinary => folded == ordinary
  | .error _, .error _ => true
  | _, _ => false

/-- Parse Turtle, serialise to N-Triples, parse THAT, and check the two
graphs are isomorphic — the round-trip the W3C eval tests perform. -/
def ttlRoundTrips (s : String) (base : Option String := none) : Bool :=
  match parseTurtle s base with
  | .error _ => false
  | .ok g =>
      match Graph.toNTriples g with
      | .error _ => false
      | .ok text =>
          match parseNTriples text with
          | .error _ => false
          | .ok g2   => Graph.isomorphic? g g2

/-- The example base every fragment below resolves against. -/
def exBase : String := "http://example.org/dir/doc.ttl"

/-! ## [4] prefixID and [5s] sparqlPrefix -/

#guard ttlToNT "@prefix p: <http://a/> . p:s p:p p:o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n"
#guard ttlFoldMatches "@prefix p: <http://a/> . p:s p:p p:o .\n@prefix p: <http://b/> . p:s p:p p:o ."
#guard ttlToNT "PREFIX p: <http://a/>\np:s p:p p:o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n"
-- `PREFIX` is case-insensitive; `@prefix` is not.
#guard ttlToNT "prefix p: <http://a/>\np:s p:p p:o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n"
#guard ttlRejects "@PREFIX p: <http://a/> . p:s p:p p:o ."
-- The empty prefix, and re-binding a prefix mid-document (§6.3).
#guard ttlToNT "@prefix : <http://a/> . :s :p :o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n"
#guard ttlToNT "@prefix p: <http://a/> . p:s p:p p:o .\n@prefix p: <http://b/> . p:s p:p p:o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n<http://b/s> <http://b/p> <http://b/o> .\n"
-- `@prefix` REQUIRES its trailing dot; `PREFIX` must not have one.
#guard ttlRejects "@prefix p: <http://a/> p:s p:p p:o ."
#guard ttlRejects "undefined:s <http://a/p> <http://a/o> ."

/-! ## [5] base and [6s] sparqlBase, and relative-IRI resolution -/

#guard ttlToNT "<s> <p> <o> ." (some exBase) ==
  "<http://example.org/dir/s> <http://example.org/dir/p> <http://example.org/dir/o> .\n"
#guard ttlToNT "@base <http://b/x/> . <s> <p> <o> ." ==
  "<http://b/x/s> <http://b/x/p> <http://b/x/o> .\n"
#guard ttlToNT "BASE <http://b/x/>\n<s> <p> <o> ." ==
  "<http://b/x/s> <http://b/x/p> <http://b/x/o> .\n"
#guard ttlRejects "@base <http://b/> <s> <p> <o> ."
-- The base may CHANGE mid-document, and each `@base` is itself
-- relative to the previous one (Turtle §6.4).
#guard ttlToNT "@base <http://b/x/> . <s1> <p> <o> .\n@base <y/> . <s2> <p> <o> ." ==
  "<http://b/x/s1> <http://b/x/p> <http://b/x/o> .\n<http://b/x/y/s2> <http://b/x/y/p> <http://b/x/y/o> .\n"
-- `<>` is the base itself; `<#f>` a fragment of it; `<../up>` ascends.
#guard ttlToNT "<> <#p> <../up> ." (some exBase) ==
  "<http://example.org/dir/doc.ttl> <http://example.org/dir/doc.ttl#p> <http://example.org/up> .\n"
-- A prefix namespace is resolved against the base in force too.
#guard ttlToNT "@prefix p: <sub/> . p:s p:p p:o ." (some exBase) ==
  "<http://example.org/dir/sub/s> <http://example.org/dir/sub/p> <http://example.org/dir/sub/o> .\n"
-- With no base at all, a relative reference cannot become an IRI.
#guard ttlRejects "<s> <p> <o> ."

/-! ## [6] triples, [7] predicateObjectList, [8] objectList, [9] verb -/

#guard ttlToNT "@prefix p: <http://a/> . p:s p:p p:o1 , p:o2 ." ==
  "<http://a/s> <http://a/p> <http://a/o1> .\n<http://a/s> <http://a/p> <http://a/o2> .\n"
#guard ttlToNT "@prefix p: <http://a/> . p:s p:p1 p:o1 ; p:p2 p:o2 ." ==
  "<http://a/s> <http://a/p1> <http://a/o1> .\n<http://a/s> <http://a/p2> <http://a/o2> .\n"
-- Trailing and repeated `;` are legal ([7]'s optional tail).
#guard ttlCount "@prefix p: <http://a/> . p:s p:p p:o ; ." == 1
#guard ttlCount "@prefix p: <http://a/> . p:s p:p p:o ;;; ." == 1
#guard ttlCount "@prefix p: <http://a/> . p:s p:p1 p:o ;; p:p2 p:o ." == 2
-- [9] verb's `a` abbreviates rdf:type, and only when a delimiter follows.
#guard ttlToNT "@prefix p: <http://a/> . p:s a p:C ." ==
  "<http://a/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://a/C> .\n"
#guard ttlToNT "@prefix a: <http://a/> . a:s a:p a:o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n"
-- A missing final `.` is a syntax error.
#guard ttlRejects "@prefix p: <http://a/> . p:s p:p p:o"
#guard ttlRejects "@prefix p: <http://a/> . p:s p:p ."
-- A literal may not be a subject.
#guard ttlRejects "\"lit\" <http://a/p> <http://a/o> ."

/-! ## [137s] BlankNode — BLANK_NODE_LABEL and ANON -/

#guard ttlCount "_:a <http://a/p> _:b ." == 1
#guard ttlToNT "_:a <http://a/p> _:b ." == "_:a <http://a/p> _:b .\n"
-- ANON `[]` in subject and object position.
#guard ttlCount "[] <http://a/p> [] ." == 1
#guard ttlFoldMatches "[] <http://a/p> [] ."
-- `[]` alone is not a statement; `[ … ]` alone is ([6] triples).
#guard ttlRejects "[] ."
#guard ttlCount "[ <http://a/p> <http://a/o> ] ." == 1
-- A label may contain internal dots but never end on one.
#guard ttlCount "_:a.b <http://a/p> <http://a/o> ." == 1
#guard ttlToNT "_:a.b <http://a/p> <http://a/o> ." == "_:a.b <http://a/p> <http://a/o> .\n"
-- Generated labels cannot collide with a document's own labels.
#guard freshBnodePrefix "_:a _:b" == "anon__"
#guard freshBnodePrefix "_:x__y" == "anon___"
#guard (TurtleState.init "_:a" none .rdf11).freshBnode.1 == "anon__0"

/-! ## [14] blankNodePropertyList -/

#guard ttlCount "@prefix p: <http://a/> . p:s p:p [ p:q p:r ] ." == 2
#guard ttlCount "@prefix p: <http://a/> . [ p:p p:o ] p:q p:r ." == 2
-- Nested property lists.
#guard ttlCount "@prefix p: <http://a/> . p:s p:p [ p:q [ p:r p:t ] ] ." == 3
#guard ttlRejects "@prefix p: <http://a/> . p:s p:p [ p:q p:r ."
#guard ttlRoundTrips "@prefix p: <http://a/> . p:s p:p [ p:q [ p:r p:t ] ] ."

/-! ## [15] collection — rdf:first / rdf:rest / rdf:nil -/

-- The empty collection IS rdf:nil, and emits no chain triples.
#guard ttlToNT "@prefix p: <http://a/> . p:s p:p () ." ==
  "<http://a/s> <http://a/p> <http://www.w3.org/1999/02/22-rdf-syntax-ns#nil> .\n"
-- A one-element collection: one statement triple + first + rest.
#guard ttlCount "@prefix p: <http://a/> . p:s p:p ( p:x ) ." == 3
-- Three elements: 1 + 3 * 2.
#guard ttlCount "@prefix p: <http://a/> . p:s p:p ( p:x p:y p:z ) ." == 7
-- Nesting: outer list of two, whose first element is a list of two.
#guard ttlCount "@prefix p: <http://a/> . p:s p:p ( ( p:x p:y ) p:z ) ." == 9
-- A collection may be a subject.
#guard ttlCount "@prefix p: <http://a/> . ( p:x p:y ) p:p p:o ." == 5
-- but not a whole statement on its own.
#guard ttlRejects "@prefix p: <http://a/> . ( p:x p:y ) ."
#guard ttlRejects "@prefix p: <http://a/> . p:s p:p ( p:x ."
#guard ttlRoundTrips "@prefix p: <http://a/> . p:s p:p ( ( p:x p:y ) p:z ) ."

/-! ## [16] NumericLiteral — INTEGER / DECIMAL / DOUBLE

The lexical form is preserved exactly as written; only the datatype is
inferred. -/

#guard ttlToNT "<http://a/s> <http://a/p> 1 ." ==
  "<http://a/s> <http://a/p> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> -3 ." ==
  "<http://a/s> <http://a/p> \"-3\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> +7 ." ==
  "<http://a/s> <http://a/p> \"+7\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> 1.5 ." ==
  "<http://a/s> <http://a/p> \"1.5\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> .5 ." ==
  "<http://a/s> <http://a/p> \".5\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> -.2 ." ==
  "<http://a/s> <http://a/p> \"-.2\"^^<http://www.w3.org/2001/XMLSchema#decimal> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> 1e3 ." ==
  "<http://a/s> <http://a/p> \"1e3\"^^<http://www.w3.org/2001/XMLSchema#double> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> 1.0E-3 ." ==
  "<http://a/s> <http://a/p> \"1.0E-3\"^^<http://www.w3.org/2001/XMLSchema#double> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> -.2e3 ." ==
  "<http://a/s> <http://a/p> \"-.2e3\"^^<http://www.w3.org/2001/XMLSchema#double> .\n"
-- `123.` is INTEGER `123` followed by the statement terminator, not a
-- DECIMAL with an empty fraction.
#guard ttlToNT "<http://a/s> <http://a/p> 123." ==
  "<http://a/s> <http://a/p> \"123\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"
-- but `123.E+1` IS a DOUBLE (zero fraction digits before an exponent).
#guard ttlToNT "<http://a/s> <http://a/p> 123.E+1 ." ==
  "<http://a/s> <http://a/p> \"123.E+1\"^^<http://www.w3.org/2001/XMLSchema#double> .\n"
#guard ttlRejects "<http://a/s> <http://a/p> . ."

/-! ## [133s] BooleanLiteral -/

#guard ttlToNT "<http://a/s> <http://a/p> true ." ==
  "<http://a/s> <http://a/p> \"true\"^^<http://www.w3.org/2001/XMLSchema#boolean> .\n"
#guard ttlToNT "<http://a/s> <http://a/p> false ." ==
  "<http://a/s> <http://a/p> \"false\"^^<http://www.w3.org/2001/XMLSchema#boolean> .\n"
-- `true` is a keyword only when nothing can continue it as a name.
#guard ttlToNT "@prefix p: <http://a/> . <http://a/s> <http://a/p> p:trueish ." ==
  "<http://a/s> <http://a/p> <http://a/trueish> .\n"

/-! ## [17] String — all four forms, and [128s] RDFLiteral -/

#guard ttlToNT "<http://a/s> <http://a/p> \"x\" ." ==
  "<http://a/s> <http://a/p> \"x\" .\n"
#guard ttlToNT "<http://a/s> <http://a/p> 'x' ." ==
  "<http://a/s> <http://a/p> \"x\" .\n"
#guard ttlToNT "<http://a/s> <http://a/p> \"\"\"x\"\"\" ." ==
  "<http://a/s> <http://a/p> \"x\" .\n"
#guard ttlToNT "<http://a/s> <http://a/p> '''x''' ." ==
  "<http://a/s> <http://a/p> \"x\" .\n"
-- A long string may contain raw newlines and up to two quote characters.
#guard ttlToNT "<http://a/s> <http://a/p> \"\"\"a\nb\"\"\" ." ==
  "<http://a/s> <http://a/p> \"a\\nb\" .\n"
#guard ttlToNT "<http://a/s> <http://a/p> \"\"\"a\"\"b\"\"\" ." ==
  "<http://a/s> <http://a/p> \"a\\\"\\\"b\" .\n"
-- A short string may not.
#guard ttlRejects "<http://a/s> <http://a/p> \"a\nb\" ."
#guard ttlRejects "<http://a/s> <http://a/p> \"unterminated ."
#guard ttlRejects "<http://a/s> <http://a/p> '''unterminated ."
-- A single quote inside a double-quoted string needs no escape, and
-- vice versa.
#guard ttlToNT "<http://a/s> <http://a/p> \"it's\" ." ==
  "<http://a/s> <http://a/p> \"it's\" .\n"
#guard ttlToNT "<http://a/s> <http://a/p> 'say \"hi\"' ." ==
  "<http://a/s> <http://a/p> \"say \\\"hi\\\"\" .\n"
-- [159s] ECHAR and [26] UCHAR.
#guard ttlToNT "<http://a/s> <http://a/p> \"a\\tb\" ." ==
  "<http://a/s> <http://a/p> \"a\\tb\" .\n"
#guard ttlToNT "<http://a/s> <http://a/p> \"\\u0041\" ." ==
  "<http://a/s> <http://a/p> \"A\" .\n"
#guard ttlToNT "<http://a/s> <http://a/p> \"\\U00000041\" ." ==
  "<http://a/s> <http://a/p> \"A\" .\n"
#guard ttlRejects "<http://a/s> <http://a/p> \"\\q\" ."
#guard ttlRejects "<http://a/s> <http://a/p> \"\\uD800\" ."
-- Language tag and explicit datatype.
#guard ttlToNT "<http://a/s> <http://a/p> \"x\"@en ." ==
  "<http://a/s> <http://a/p> \"x\"@en .\n"
#guard ttlToNT "<http://a/s> <http://a/p> \"x\"^^<http://d/t> ." ==
  "<http://a/s> <http://a/p> \"x\"^^<http://d/t> .\n"
#guard ttlToNT "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> . <http://a/s> <http://a/p> \"1\"^^xsd:integer ." ==
  "<http://a/s> <http://a/p> \"1\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"

/-! ## [136s] PrefixedName — PNAME_NS / PNAME_LN and PN_LOCAL escapes -/

-- A bare `prefix:` with an empty local part.
#guard ttlToNT "@prefix p: <http://a/x> . p: <http://a/q> p: ." ==
  "<http://a/x> <http://a/q> <http://a/x> .\n"
-- PN_LOCAL may contain `:` and internal `.`, but not a trailing `.`.
#guard ttlToNT "@prefix p: <http://a/> . p:a:b <http://a/q> <http://a/o> ." ==
  "<http://a/a:b> <http://a/q> <http://a/o> .\n"
#guard ttlToNT "@prefix p: <http://a/> . p:a.b <http://a/q> <http://a/o> ." ==
  "<http://a/a.b> <http://a/q> <http://a/o> .\n"
#guard ttlToNT "@prefix p: <http://a/> . p:o. " ==
  "PARSE-ERROR: expected predicate after subject"
-- PN_LOCAL_ESC: the backslash goes, the escaped character stays.
#guard ttlToNT "@prefix p: <http://a/> . p:a\\-b <http://a/q> <http://a/o> ." ==
  "<http://a/a-b> <http://a/q> <http://a/o> .\n"
#guard ttlToNT "@prefix p: <http://a/> . p:a\\,b <http://a/q> <http://a/o> ." ==
  "<http://a/a,b> <http://a/q> <http://a/o> .\n"
#guard ttlToNT "@prefix p: <http://a/> . p:a\\#b <http://a/q> <http://a/o> ." ==
  "<http://a/a#b> <http://a/q> <http://a/o> .\n"
#guard ttlToNT "@prefix p: <http://a/> . p:a\\~b <http://a/q> <http://a/o> ." ==
  "<http://a/a~b> <http://a/q> <http://a/o> .\n"
-- `%XX` PERCENT is passed through UNCHANGED (it is the IRI's own
-- percent-encoding, not a Turtle escape).
#guard ttlToNT "@prefix p: <http://a/> . p:a%20b <http://a/q> <http://a/o> ." ==
  "<http://a/a%20b> <http://a/q> <http://a/o> .\n"
#guard ttlRejects "@prefix p: <http://a/> . p:a%2 <http://a/q> <http://a/o> ."
#guard ttlRejects "@prefix p: <http://a/> . p:a\\ب <http://a/q> <http://a/o> ."
-- Non-ASCII PN_CHARS_BASE in a name (Turtle §6.5's Unicode ranges).
#guard ttlToNT "@prefix p: <http://a/> . p:日本 <http://a/q> <http://a/o> ." ==
  "<http://a/日本> <http://a/q> <http://a/o> .\n"
#guard ttlToNT "@prefix 日: <http://a/> . 日:x <http://a/q> <http://a/o> ." ==
  "<http://a/x> <http://a/q> <http://a/o> .\n"

/-! ## Comments and whitespace (Turtle §2.1) -/

#guard ttlCount "# leading comment\n@prefix p: <http://a/> . # trailing\np:s p:p p:o . # after\n" == 1
#guard ttlCount "" == 0
#guard ttlCount "   \n\t\n# only a comment\n" == 0
-- A `#` inside an IRI or a string is NOT a comment.
#guard ttlToNT "<http://a/s#f> <http://a/p> \"a # b\" ." ==
  "<http://a/s#f> <http://a/p> \"a # b\" .\n"

/-! ## IRIREF well-formedness (production [18], N-Triples §"IRIs") -/

#guard ttlRejects "<http://a/ b> <http://a/p> <http://a/o> ."
#guard ttlRejects "<http://a/s <http://a/p> <http://a/o> ."
-- A UCHAR escape that decodes to a forbidden character is as bad as
-- the raw character (the F* source's turtle-eval-bad-01/02/03).
#guard ttlRejects "<http://a/\\u0020b> <http://a/p> <http://a/o> ."

/-! ## Serialise / parse round-trips through the landed N-Triples pair -/

#guard ttlRoundTrips "@prefix p: <http://a/> . p:s p:p p:o1 , p:o2 ; p:q p:r ."
#guard ttlRoundTrips "_:a <http://a/p> _:b . _:b <http://a/p> _:a ."
#guard ttlRoundTrips "<http://a/s> <http://a/p> \"x\"@en , \"1\"^^<http://d/t> , 2 , true ."
#guard ttlRoundTrips "@prefix p: <http://a/> . [ p:p ( 1 2 3 ) ] p:q [ p:r [] ] ."
#guard ttlRoundTrips "<s> <p> <o> ." (some exBase)

/-! ## TriG — [1g]–[7g]

TriG reuses every Turtle production, so these check only what TriG
ADDS: graph blocks, the `GRAPH` keyword, graph names, and the
directive/nesting restrictions inside a block. -/

def trigOk (s : String) (base : Option String := none) : Bool :=
  (parseTriG s base).toOption.isSome

def trigRejects (s : String) (base : Option String := none) : Bool := !(trigOk s base)

/-- `(default-graph triples, number of named graphs, total named
triples)` — enough to pin every case below without naming blank nodes. -/
def trigShape (s : String) (base : Option String := none) : Nat × Nat × Nat :=
  match parseTriG s base with
  | .error _ => (0, 0, 0)
  | .ok ds   => (ds.default.length, ds.named.length,
                 ds.named.foldl (fun n g => n + g.graph.length) 0)

-- A bare Turtle statement goes to the default graph.
#guard trigShape "@prefix p: <http://a/> . p:s p:p p:o ." == (1, 0, 0)
-- [5g] a bare wrappedGraph is also the default graph.
#guard trigShape "@prefix p: <http://a/> . { p:s p:p p:o . }" == (1, 0, 0)
-- [3g] labelOrSubject followed by `{` is a NAMED graph.
#guard trigShape "@prefix p: <http://a/> . p:g { p:s p:p p:o . }" == (0, 1, 1)
-- [2g] the `GRAPH` keyword form, case-insensitive.
#guard trigShape "@prefix p: <http://a/> . GRAPH p:g { p:s p:p p:o . }" == (0, 1, 1)
#guard trigShape "@prefix p: <http://a/> . graph p:g { p:s p:p p:o . }" == (0, 1, 1)
-- `GRAPH` needs a name.
#guard trigRejects "@prefix p: <http://a/> . GRAPH { p:s p:p p:o . }"
-- [7g] a blank node may name a graph, written `_:g` or `[]`.
#guard trigShape "@prefix p: <http://a/> . _:g { p:s p:p p:o . }" == (0, 1, 1)
#guard trigShape "@prefix p: <http://a/> . [] { p:s p:p p:o . }" == (0, 1, 1)
-- Two blocks with the same name merge into one named graph.
#guard trigShape "@prefix p: <http://a/> . p:g { p:s p:p p:o1 . } p:g { p:s p:p p:o2 . }" == (0, 1, 2)
-- Default and named together.
#guard trigShape "@prefix p: <http://a/> . p:s p:p p:o . p:g { p:s p:p p:o . }" == (1, 1, 1)
-- [6g] the last statement of a block may omit its `.`.
#guard trigShape "@prefix p: <http://a/> . { p:s p:p p:o }" == (1, 0, 0)
#guard trigShape "@prefix p: <http://a/> . { p:s p:p p:o1 . p:s p:p p:o2 }" == (2, 0, 0)
-- An empty block is legal and contributes nothing.
#guard trigShape "@prefix p: <http://a/> . p:g { }" == (0, 0, 0)
-- A directive inside a block, and a nested GRAPH, are syntax errors.
#guard trigRejects "@prefix p: <http://a/> . { @prefix q: <http://b/> . p:s p:p p:o . }"
#guard trigRejects "@prefix p: <http://a/> . { GRAPH p:g { p:s p:p p:o . } }"
#guard trigRejects "@prefix p: <http://a/> . p:g { p:s p:p p:o . "
-- A collection cannot name a graph, but is fine as a subject ([4g]).
#guard trigRejects "@prefix p: <http://a/> . ( 1 2 3 ) { p:s p:p p:o . }"
#guard trigShape "@prefix p: <http://a/> . ( 1 2 3 ) p:p ( 4 5 6 ) ." == (13, 0, 0)
-- Relative IRIs inside a block resolve against the document base.
#guard trigShape "<g> { <s> <p> <o> . }" (some exBase) == (0, 1, 1)

/-! ## RDF 1.2 Turtle and TriG

https://www.w3.org/TR/rdf12-turtle/ — the productions `.rdf12` adds over
`.rdf11`, one guard per production, each also stated in its NEGATIVE
form: `.rdf11` must still REJECT every one of them, or the mode
parameter would be decoration.

  [30] tripleTerm      `<<( s p o )>>`, object position only
  [27] reifiedTriple   `<< s p o >>` (subject or object)
  [33] reifier         `~` / `~ <label>` after an object
  [34] annotation      `(reifier | annotationBlock)*`
  [35] annotationBlock `{| predicateObjectList |}`
  [4a] version         `@version "…" .` / `VERSION "…"`
  base direction       `"chat"@en--ltr` (RDF 1.2 Concepts §3.3)

The expectations are written as N-Triples TEXT wherever the answer is
ground; where the shorthand mints a blank-node reifier they are stated
as a triple COUNT plus the parse succeeding, since the label is the
parser's to choose. -/

/-- Parse in RDF 1.2 mode and render as RDF 1.2 N-Triples. -/
def ttl12ToNT (s : String) (base : Option String := none) : String :=
  match parseTurtle s base .rdf12 with
  | .error e => s!"PARSE-ERROR: {e.msg}"
  | .ok g    => match Graph.toNTriples g .rdf12 with
                | .error e => s!"SERIALISE-ERROR: {e}"
                | .ok t    => t

/-- Triple count of a successful RDF 1.2 parse; `0` on failure. -/
def ttl12Count (s : String) (base : Option String := none) : Nat :=
  match parseTurtle s base .rdf12 with
  | .error _ => 0
  | .ok g    => g.length

/-- Was this fragment rejected under RDF 1.1? -/
def ttl11Rejects (s : String) (base : Option String := none) : Bool :=
  (parseTurtle s base .rdf11).toOption.isNone

-- [30] tripleTerm: the object is a TRIPLE TERM, not a new statement.
#guard ttl12ToNT "@prefix p: <http://a/> . p:s p:p <<( p:s2 p:p2 p:o2 )>> ." ==
  "<http://a/s> <http://a/p> <<( <http://a/s2> <http://a/p2> <http://a/o2> )>> .\n"
#guard ttl11Rejects "@prefix p: <http://a/> . p:s p:p <<( p:s2 p:p2 p:o2 )>> ."
-- …and it nests.
#guard ttl12Count "@prefix p: <http://a/> . p:s p:p <<( p:s2 p:p2 <<( p:a p:b p:c )>> )>> ." == 1

-- [27] reifiedTriple in object position: the base triple, plus the
-- reifier's `rdf:reifies` triple. `<< >>` alone mints a blank node.
#guard ttl12ToNT "@prefix p: <http://a/> . p:s p:p << p:s2 p:p2 p:o2 ~ p:r >> ." ==
  ("<http://a/r> <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> "
    ++ "<<( <http://a/s2> <http://a/p2> <http://a/o2> )>> .\n"
    ++ "<http://a/s> <http://a/p> <http://a/r> .\n")
#guard ttl11Rejects "@prefix p: <http://a/> . p:s p:p << p:s2 p:p2 p:o2 ~ p:r >> ."
-- …and in SUBJECT position.
#guard ttl12Count "@prefix p: <http://a/> . << p:s2 p:p2 p:o2 ~ p:r >> p:p p:o ." == 2

-- [33] reifier after an object: one extra `rdf:reifies` triple naming
-- the statement just made.
#guard ttl12ToNT "@prefix p: <http://a/> . p:s p:p p:o ~ p:r ." ==
  ("<http://a/s> <http://a/p> <http://a/o> .\n"
    ++ "<http://a/r> <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> "
    ++ "<<( <http://a/s> <http://a/p> <http://a/o> )>> .\n")
#guard ttl11Rejects "@prefix p: <http://a/> . p:s p:p p:o ~ p:r ."
-- A bare `~` mints the reifier: still exactly two triples.
#guard ttl12Count "@prefix p: <http://a/> . p:s p:p p:o ~ ." == 2

-- [34]/[35] annotationBlock: the block's predicateObjectList hangs off
-- the reifier — base triple + rdf:reifies + one annotation triple.
#guard ttl12ToNT "@prefix p: <http://a/> . p:s p:p p:o ~ p:r {| p:src p:doc |} ." ==
  ("<http://a/s> <http://a/p> <http://a/o> .\n"
    ++ "<http://a/r> <http://www.w3.org/1999/02/22-rdf-syntax-ns#reifies> "
    ++ "<<( <http://a/s> <http://a/p> <http://a/o> )>> .\n"
    ++ "<http://a/r> <http://a/src> <http://a/doc> .\n")
#guard ttl11Rejects "@prefix p: <http://a/> . p:s p:p p:o {| p:src p:doc |} ."
-- A block with no explicit reifier mints one: still three triples.
#guard ttl12Count "@prefix p: <http://a/> . p:s p:p p:o {| p:src p:doc |} ." == 3
-- An EMPTY annotation block is a syntax error.
#guard (parseTurtle "@prefix p: <http://a/> . p:s p:p p:o {| |} ." none .rdf12).toOption.isNone

-- [4a] version directive, both spellings, top level only, and
-- state-neutral (it licenses no triple of its own).
#guard ttl12ToNT "@version \"1.2\" . @prefix p: <http://a/> . p:s p:p p:o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n"
#guard ttl12ToNT "VERSION \"1.2\" PREFIX p: <http://a/> p:s p:p p:o ." ==
  "<http://a/s> <http://a/p> <http://a/o> .\n"
#guard ttl11Rejects "@version \"1.2\" . @prefix p: <http://a/> . p:s p:p p:o ."

-- Base direction (RDF 1.2 Concepts §3.3): `@lang--ltr` / `@lang--rtl`
-- make an `rdf:dirLangString`, and RDF 1.1 rejects the suffix.
#guard ttl12ToNT "@prefix p: <http://a/> . p:s p:p \"chat\"@en--ltr ." ==
  "<http://a/s> <http://a/p> \"chat\"@en--ltr .\n"
#guard ttl12ToNT "@prefix p: <http://a/> . p:s p:p \"chat\"@he--rtl ." ==
  "<http://a/s> <http://a/p> \"chat\"@he--rtl .\n"
-- …and RDF 1.1 does NOT reject the `--ltr` spelling: it reads the whole
-- run as ONE language tag, `en--ltr`, with no direction. Both trees are
-- lax here — neither `Parser.NTriples.fst`'s `parse_lang_tag`
-- (line 514) nor this port's `readLangTag` applies the BCP47 subtag
-- check `valid_lang_subtags` / `validLangSubtags` that the RDF 1.2 path
-- does, so an empty subtag passes. The guard PINS the current answer so
-- a future tightening is a deliberate change, not a surprise.
#guard (match parseTurtle "@prefix p: <http://a/> . p:s p:p \"chat\"@en--ltr ." none .rdf11 with
        | .ok [t] =>
            (match t.o with
             | .literal l => l.val.langTag == some "en--ltr" && l.val.direction == none
             | _ => false)
        | _ => false)
-- A plain language tag is unaffected in BOTH modes.
#guard ttlToNT "@prefix p: <http://a/> . p:s p:p \"chat\"@en ." ==
  "<http://a/s> <http://a/p> \"chat\"@en .\n"

-- [10] triples admits `reifiedTriple predicateObjectList?`, so a
-- reified triple ALONE is a statement: it makes only the reifier's
-- `rdf:reifies` triple. RDF 1.1 rejects the whole form.
#guard ttl12Count "@prefix p: <http://a/> . << p:s p:p p:o >> ." == 1
#guard ttl11Rejects "@prefix p: <http://a/> . << p:s p:p p:o >> ."

/-! ### TriG 1.2

The same productions inside a `GRAPH` block, plus the `VERSION`
directive at TriG's own top level ([3] directive). -/

#guard (match parseTriG "@prefix p: <http://a/> . p:g { p:s p:p p:o ~ p:r . }" none .rdf12 with
        | .ok ds => ds.named.foldl (fun n g => n + g.graph.length) 0
        | .error _ => 0) == 2
#guard (parseTriG "@prefix p: <http://a/> . p:g { p:s p:p p:o ~ p:r . }" none .rdf11).toOption.isNone
#guard (parseTriG "VERSION \"1.2\" PREFIX p: <http://a/> p:g { p:s p:p p:o }" none .rdf12).toOption.isSome
#guard (parseTriG "VERSION \"1.2\" PREFIX p: <http://a/> p:g { p:s p:p p:o }" none .rdf11).toOption.isNone

/-! ## Axiom audit

Every `#guard` above is a kernel computation, so nothing here can
depend on an axiom; the audit lines name the definitions the whole
suite rests on. -/

#print axioms parseTurtle
#print axioms parseTriG
#print axioms resolveIri

end L4Factoidal.Syntax
