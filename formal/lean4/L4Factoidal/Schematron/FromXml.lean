/-
L4Factoidal.Schematron.FromXml — read an ISO Schematron `.sch`
document into the `Schematron.Schema` model.

Spec: ISO/IEC 19757-3:2016. The elements this reads are §5.4.1
`schema`, §5.4.9 `ns`, §5.4.11 `let`, §5.4.6 `pattern`, §5.4.5 `rule`,
§5.4.3 `assert` and §5.4.4 `report`.

## Names are matched on the LOCAL part

The project's XML parser is deliberately NON-NAMESPACE: it keeps a
`[5] Name` exactly as written, so a Schematron document writes
`sch:pattern` and an unprefixed one writes `pattern`, and both must
read the same. This module therefore strips everything up to the last
`:` before matching. That is weaker than a namespace check — it would
accept `other:pattern` — and the weakness is stated rather than
hidden: a namespace-aware reader belongs with `XML.Namespaces`, and
the corpus here declares the ISO namespace on every schema it uses.

## An element this module does not know is SKIPPED, not guessed

`abstract` patterns, `extends`, `include`, `phase`, `diagnostics` and
`value-of` are outside this reader. They are dropped, and a schema
that needed them therefore validates against LESS than it should —
never against something invented. The runner counts what it read, so
a dropped construct shows up as a missing finding rather than as a
silent pass.
-/
import L4Factoidal.Schematron.Validate
import L4Factoidal.XML.Parser

namespace L4Factoidal.Schematron

open L4Factoidal.XML

/-- The part of a `[5] Name` after the last `:`. -/
def localOf (n : String) : String :=
  match (n.splitOn ":").getLast? with
  | some l => l
  | none   => n

/-- Element children whose LOCAL name is `nm`. -/
def childrenNamed (nm : String) : Node → List Node
  | .element _ _ cs =>
      cs.filter (fun c => match c with
        | .element t _ _ => localOf t == nm
        | _              => false)
  | _ => []

def attrOf (nm : String) : Node → Option String
  | .element _ attrs _ => (attrs.find? (fun a => localOf a.name == nm)).map (·.value)
  | _                  => none

/-- The character content of an element, descendants included. This is
    the assertion MESSAGE. `value-of` and `name` inside a message are
    not expanded — their text contribution is empty — so a message
    that used them reads short rather than wrong. -/
partial def textOf : Node → String
  | .element _ _ cs => cs.foldl (fun acc c => acc ++ textOf c) ""
  | .text t         => t
  | .cdata t        => t
  | _               => ""

/-- Collapse runs of whitespace, and trim. Schematron messages are
    written across source lines; comparing them raw would make an
    indent part of the message. -/
def normalizeSpace (s : String) : String :=
  let ws := (s.toList.foldl (fun (acc, gap) c =>
      if c.isWhitespace then (acc, true)
      else (if gap && !acc.isEmpty then acc ++ [' ', c] else acc ++ [c], false))
    (([] : List Char), false)).1
  String.ofList ws

/-- `<sch:let name="…" value="…"/>` — §5.4.11. A `let` missing either
    attribute is dropped: a variable with no name cannot be referred
    to, and one with no value has nothing to bind. -/
def letOf (n : Node) : Option Let :=
  match attrOf "name" n, attrOf "value" n with
  | some nm, some v => some { name := nm, value := v }
  | _, _            => none

/-- `<sch:assert>` / `<sch:report>` — §5.4.3 / §5.4.4. `isAssert`
    records WHICH one, because the two fire on opposite truth values
    and `Validate.applyAssertion` needs the distinction. -/
def assertionOf (n : Node) : Option Assertion :=
  match n with
  | .element t _ _ =>
      let l := localOf t
      if l != "assert" && l != "report" then none
      else match attrOf "test" n with
        | none      => none    -- @test is REQUIRED; no test, no assertion
        | some test => some { isAssert := l == "assert", test := test,
                              message := normalizeSpace (textOf n) }
  | _ => none

/-- `<sch:rule context="…">` — §5.4.5. A rule with no `@context` is an
    ABSTRACT rule (it exists to be `extends`-ed) and this reader drops
    it, since `extends` is outside the slice. -/
def ruleOf (n : Node) : Option Rule :=
  match attrOf "context" n with
  | none     => none
  | some ctx =>
      let kids := match n with
        | .element _ _ cs => cs
        | _               => []
      some { context := ctx,
             lets := (childrenNamed "let" n).filterMap letOf,
             assertions := kids.filterMap assertionOf }

/-- `<sch:pattern>` — §5.4.6. An `@abstract="true"` pattern is a
    TEMPLATE, never fired directly, so it is dropped rather than run. -/
def patternOf (n : Node) : Option Pattern :=
  if attrOf "abstract" n == some "true" then none
  else some { id := (attrOf "id" n).getD "",
              rules := (childrenNamed "rule" n).filterMap ruleOf }

/-- `<sch:schema>` — §5.4.1. -/
def schemaOf (root : Node) : Option Schema :=
  match root with
  | .element t _ _ =>
      if localOf t != "schema" then none
      else some {
        namespaces := (childrenNamed "ns" root).filterMap (fun n =>
          match attrOf "prefix" n, attrOf "uri" n with
          | some p, some u => some (p, u)
          | _, _           => none),
        lets := (childrenNamed "let" root).filterMap letOf,
        patterns := (childrenNamed "pattern" root).filterMap patternOf }
  | _ => none

/-- Read a `.sch` source. The XML failure and the not-a-schema failure
    are kept apart: one says the file is not XML, the other says it is
    XML that is not Schematron. -/
def parseSchematron (src : String) : Except String Schema :=
  match parseXML src with
  | .error e => .error s!"the schema is not well-formed XML: {e.message} at {e.position}"
  | .ok doc  =>
      match schemaOf doc.root with
      | none   => .error "the document element is not a Schematron <schema>"
      | some s => .ok s

end L4Factoidal.Schematron
