/-
L4Factoidal.Solid.Server.N3Patch — parsing the `text/n3` patch subset the
Solid Protocol requires, and applying it.

Wraps: `L4Factoidal.LWS.Patch` — the three formulae, their constraints and
`applyPatch` live there, because the LWS draft states the blank-node
refusal. Also `L4Factoidal.Syntax.Turtle.parseTurtle`, which parses the
triples inside `{ }`; no new RDF parser is written here.
Adds: the N3 surface syntax of §5.3.1 and the mapping from it to a
`LWS.Patch`.

Source: https://solidproject.org/TR/protocol §5.3.1 Modifying Resources
Using N3 Patches, verbatim:

  "Servers MUST accept a PATCH request with an N3 Patch body when the target
  of the request is an RDF document [RDF11-CONCEPTS]. Servers MUST indicate
  support of N3 Patch by listing text/n3 as a field value of the
  Accept-Patch header field [RFC5789] of relevant responses."

  "A patch document MUST contain one or more patch resources."
  "A patch resource MUST be identified by a URI or blank node, which we
  refer to as ?patch in the remainder of this section."
  "A patch resource MAY contain a triple ?patch rdf:type solid:Patch."
  "A patch resource MUST contain at most one triple of the form ?patch
  solid:deletes ?deletions."
  "A patch resource MUST contain at most one triple of the form ?patch
  solid:inserts ?insertions."
  "A patch resource MUST contain at most one triple of the form ?patch
  solid:where ?conditions."
  "When present, ?deletions, ?insertions, and ?conditions MUST be non-nested
  cited formulae [N3] consisting only of triples and/or triple patterns
  [SPARQL11-QUERY]. When not present, they are presumed to be the empty
  formula {}."
  "The patch document MUST contain exactly one patch resource, identified by
  one or more of the triple patterns described above, which all share the
  same ?patch subject."
  "A patch resource MUST contain a triple ?patch rdf:type
  solid:InsertDeletePatch."
  "The ?insertions and ?deletions formulae MUST NOT contain variables that
  do not occur in the ?conditions formula."
  "The ?insertions and ?deletions formulae MUST NOT contain blank nodes."
  "Servers MUST respond with a 422 status code [RFC4918] if a patch document
  does not satisfy all of the above constraints."

The specification's own example:

    @prefix solid: <http://www.w3.org/ns/solid/terms#>.
    @prefix ex: <http://www.example.org/terms#>.
    _:rename a solid:InsertDeletePatch;
      solid:where   { ?person ex:familyName "Garcia". };
      solid:inserts { ?person ex:givenName "Alex". };
      solid:deletes { ?person ex:givenName "Claudia". }.

## How the Turtle parser is reused

A cited formula `{ … }` is not Turtle, and `?person` is not a Turtle term.
The parse therefore does two textual steps before handing the formula to
`parseTurtle`:

1. the brace-delimited text of each formula is cut out, refusing a nested
   `{` — the specification requires non-nested formulae;
2. inside that text, every `?name` becomes the IRI
   `<urn:x-n3patch-var:name>`, and every such IRI becomes a
   `SPARQL.PatternTerm.var` again after parsing.

The prefix declarations of the document are prepended to each formula, so
`ex:givenName` resolves exactly as the document declares it. This is a
TEXTUAL transformation with no RDF logic in it: the triples themselves are
parsed by the Turtle parser and by nothing else.

Two limits of the transformation, stated rather than hidden: a `?` inside a
string literal that contains an escaped quote can be rewritten, because the
scanner tracks string state but not backslash escapes; and N3 syntax outside
this subset (nested formulae, `=>`, paths, lists of formulae) is refused
rather than parsed.
-/
import L4Factoidal.LWS.Patch
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.LWS
open L4Factoidal.Syntax

/-- The IRI prefix a patch variable is parsed as. Chosen inside `urn:` so it
can never collide with a resolvable IRI in a patch document. -/
def patchVarPrefix : String := "urn:x-n3patch-var:"

/-! ## Scanning -/

private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-'

/-- Where `needle` first occurs in `hay`, counting from `i`. -/
def indexOfSub (needle : List Char) : List Char → Nat → Option Nat
  | [], i => if needle.isEmpty then some i else none
  | c :: rest, i =>
      if needle.isPrefixOf (c :: rest) then some i
      else indexOfSub needle rest (i + 1)

/-- The characters up to the closing `}`. A nested `{` is refused, because
the specification requires "non-nested cited formulae". -/
def takeToBrace : List Char → List Char → Option (List Char)
  | [], _ => none
  | '}' :: _, acc => some acc.reverse
  | '{' :: _, _ => none
  | c :: rest, acc => takeToBrace rest (c :: acc)

/-- Skip spaces, tabs and line breaks. -/
def skipSpace : List Char → List Char
  | c :: rest => if c == ' ' || c == '\t' || c == '\n' || c == '\r'
                 then skipSpace rest else c :: rest
  | [] => []

/-- The formula text that follows the FIRST occurrence of `kw`. The
characters between the keyword and the `{` must be whitespace, so a keyword
that appears in a comment or a literal does not steal the next formula. -/
def formulaFor (doc : List Char) (kw : String) : Option (List Char) :=
  match indexOfSub kw.toList doc 0 with
  | none => none
  | some i =>
      match skipSpace (doc.drop (i + kw.length)) with
      | '{' :: rest => takeToBrace rest []
      | _ => none

/-- The formula text for a predicate written either with the `solid:` prefix
or as a full IRI. -/
def formulaForPredicate (doc : List Char) (local_ : String) : Option (List Char) :=
  match formulaFor doc ("solid:" ++ local_) with
  | some f => some f
  | none   => formulaFor doc ("<http://www.w3.org/ns/solid/terms#" ++ local_ ++ ">")

/-! ## Variable rewriting -/

private inductive ScanState where
  | normal | inVar | inString

private def varOpen : List Char := ("<" ++ patchVarPrefix).toList

private def substVarsGo : ScanState → List Char → List Char
  | .normal, [] => []
  | .inVar, [] => ['>']
  | .inString, [] => []
  | .normal, c :: rest =>
      if c == '?' then varOpen ++ substVarsGo .inVar rest
      else if c == '"' then '"' :: substVarsGo .inString rest
      else c :: substVarsGo .normal rest
  | .inVar, c :: rest =>
      if isNameChar c then c :: substVarsGo .inVar rest
      else if c == '"' then '>' :: '"' :: substVarsGo .inString rest
      else '>' :: c :: substVarsGo .normal rest
  | .inString, c :: rest =>
      if c == '"' then '"' :: substVarsGo .normal rest
      else c :: substVarsGo .inString rest

/-- Rewrite `?name` into `<urn:x-n3patch-var:name>` outside string
literals. -/
def substituteVariables (s : String) : String :=
  String.ofList (substVarsGo .normal s.toList)

/-- The `@prefix` and `@base` declarations of the document, which every
formula is parsed with. -/
def prefixLines (doc : String) : String :=
  String.intercalate "\n"
    ((doc.splitOn "\n").filter (fun line =>
      let t := String.ofList (line.toList.dropWhile (fun c => c == ' ' || c == '\t'))
      t.startsWith "@prefix" || t.startsWith "@base" ||
      t.startsWith "PREFIX" || t.startsWith "BASE"))

/-! ## From triples back to patterns -/

private def stripVar? (s : String) : Option String :=
  if s.startsWith patchVarPrefix
  then some (String.ofList (s.toList.drop patchVarPrefix.length))
  else none

def unvarTerm : Term → PatternTerm
  | .iri i => match stripVar? i.val with
              | some n => .var n
              | none   => .iri i
  | .bnode b => .bnode b
  | .literal l => .literal l
  | .tripleTerm s p o =>
      let sp : PatternTerm := match s with
        | .iri i => match stripVar? i.val with
                    | some n => .var n
                    | none   => .iri i
        | .bnode b => .bnode b
      let pp : PatternTerm := match stripVar? p.val with
        | some n => .var n
        | none   => .iri p
      .tripleTerm sp pp (unvarTerm o)

def unvarSubject : Subject → PatternSubject
  | .iri i => match stripVar? i.val with
              | some n => .var n
              | none   => .iri i
  | .bnode b => .bnode b

def unvarPredicate (p : WfIri) : PatternTerm :=
  match stripVar? p.val with
  | some n => .var n
  | none   => .iri p

def patternOfTriple (t : Triple) : TriplePattern :=
  { s := unvarSubject t.s, p := unvarPredicate t.p, o := unvarTerm t.o }

/-! ## Parsing -/

/-- Why a patch document is refused. Every one of these is a 422 —
"Servers MUST respond with a 422 status code if a patch document does not
satisfy all of the above constraints." -/
inductive N3PatchError where
  | notInsertDeletePatch
  | severalPatchResources
  | nestedFormula (which : String)
  | formulaNotTurtle (which : String) (why : String)
  | constraint (e : LWS.PatchError)
deriving Repr

def N3PatchError.status : N3PatchError → Nat
  | .constraint e => e.status
  | _ => 422

def N3PatchError.message : N3PatchError → String
  | .notInsertDeletePatch =>
      "the patch resource has no rdf:type solid:InsertDeletePatch triple"
  | .severalPatchResources =>
      "the patch document contains more than one patch resource"
  | .nestedFormula w =>
      "the ?" ++ w ++ " formula is nested or is not closed"
  | .formulaNotTurtle w why =>
      "the ?" ++ w ++ " formula does not parse: " ++ why
  | .constraint e => e.message

/-- How many patch resources the document declares. -/
def insertDeletePatchCount (doc : String) : Nat :=
  (doc.splitOn "InsertDeletePatch").length - 1

/-- Parse one formula into a Basic Graph Pattern. An absent formula is the
empty one: "When not present, they are presumed to be the empty formula
{}." -/
def parseFormula (prefixes : String) (doc : List Char) (which : String) :
    Except N3PatchError Bgp :=
  match formulaForPredicate doc which with
  | none => .ok []
  | some body =>
      let text := prefixes ++ "\n" ++ substituteVariables (String.ofList body)
      match parseTurtle text none .rdf11 with
      | .error e => .error (.formulaNotTurtle which (toString e))
      | .ok g    => .ok (g.map patternOfTriple)

/-- Parse an N3 Patch document into a `LWS.Patch`, applying every constraint
of §5.3.1. -/
def parseN3Patch (doc : String) : Except N3PatchError LWS.Patch := do
  let cs := doc.toList
  let n := insertDeletePatchCount doc
  if n == 0 then .error .notInsertDeletePatch
  else if n > 1 then .error .severalPatchResources
  else
    let prefixes := prefixLines doc
    -- A formula whose keyword is present but whose braces do not close (or
    -- nest) parses as absent above, so the presence of the keyword is
    -- checked separately to tell "no formula" from "bad formula".
    let check (which : String) : Except N3PatchError Unit :=
      if (indexOfSub ("solid:" ++ which).toList cs 0).isSome &&
         (formulaForPredicate cs which).isNone
      then .error (.nestedFormula which) else .ok ()
    do
      check "where"
      check "inserts"
      check "deletes"
      let conditions ← parseFormula prefixes cs "where"
      let insertions ← parseFormula prefixes cs "inserts"
      let deletions  ← parseFormula prefixes cs "deletes"
      let p : LWS.Patch := { conditions, insertions, deletions }
      match LWS.wellFormed p with
      | some e => .error (.constraint e)
      | none   => .ok p

/-- Parse and apply, in one step: the whole of "Servers MUST process a patch
resource against the target document as follows". -/
def applyN3Patch (doc : String) (g : List Triple) :
    Except N3PatchError (List Triple) :=
  match parseN3Patch doc with
  | .error e => .error e
  | .ok p =>
      match LWS.applyPatch p g with
      | .error e => .error (.constraint e)
      | .ok g'   => .ok g'

end L4Factoidal.Solid.Server
