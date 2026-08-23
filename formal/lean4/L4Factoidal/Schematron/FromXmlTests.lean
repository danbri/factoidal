/-
L4Factoidal.Schematron.FromXmlTests — build-time checks for the `.sch`
reader.
-/
import L4Factoidal.Schematron.FromXml

namespace L4Factoidal.Schematron

-- The parser is non-namespace, so a name is matched on its LOCAL part.
#guard localOf "sch:pattern" == "pattern"
#guard localOf "pattern" == "pattern"

-- A message written across source lines reads as one line.
#guard normalizeSpace "  A library must\n     contain a book.  " ==
       "A library must contain a book."
#guard normalizeSpace "" == ""

private def libSrc : String :=
  "<sch:schema xmlns:sch=\"http://purl.oclc.org/dsdl/schematron\">" ++
  "<sch:pattern id=\"p1\"><sch:rule context=\"library\">" ++
  "<sch:assert test=\"count(book) &gt;= 1\">Need a book.</sch:assert>" ++
  "<sch:report test=\"@draft\">Draft.</sch:report>" ++
  "</sch:rule></sch:pattern></sch:schema>"

private def libSchema : Schema :=
  match parseSchematron libSrc with
  | .ok s    => s
  | .error _ => {}

#guard libSchema.patterns.length == 1
#guard (libSchema.patterns.head?.map (·.id)) == some "p1"
#guard (libSchema.patterns.head?.map (·.rules.length)) == some 1

private def libRule : Rule :=
  ((libSchema.patterns.head?.bind (·.rules.head?))).getD { context := "" }

#guard libRule.context == "library"
#guard libRule.assertions.length == 2
-- THE INVERSION is carried across the read: `assert` and `report` are
-- distinguished, so `Validate.applyAssertion` can fire them on
-- opposite truth values.
#guard (libRule.assertions[0]?.map (·.isAssert)) == some true
#guard (libRule.assertions[1]?.map (·.isAssert)) == some false
#guard (libRule.assertions[0]?.map (·.test)) == some "count(book) >= 1"
#guard (libRule.assertions[0]?.map (·.message)) == some "Need a book."

-- An UNPREFIXED schematron document reads identically.
#guard (match parseSchematron
          ("<schema><pattern id=\"q\"><rule context=\"a\">" ++
           "<assert test=\"b\">m</assert></rule></pattern></schema>") with
        | .ok s => s.patterns.length == 1
        | .error _ => false)

-- An ABSTRACT pattern is a template, never fired, so it is dropped
-- rather than run against the document.
#guard (match parseSchematron
          ("<schema><pattern abstract=\"true\" id=\"t\"><rule context=\"a\">" ++
           "<assert test=\"b\">m</assert></rule></pattern></schema>") with
        | .ok s => s.patterns.isEmpty
        | .error _ => false)

-- A rule with no @context is abstract (it exists to be extended), and
-- `extends` is outside this reader, so it is dropped.
#guard (match parseSchematron
          ("<schema><pattern id=\"t\"><rule id=\"r\">" ++
           "<assert test=\"b\">m</assert></rule></pattern></schema>") with
        | .ok s => (s.patterns.head?.map (·.rules.isEmpty)) == some true
        | .error _ => false)

-- The two failures are kept apart: not XML, versus XML that is not
-- Schematron.
#guard (match parseSchematron "<schema>" with | .error _ => true | .ok _ => false)
#guard (match parseSchematron "<html/>" with | .error _ => true | .ok _ => false)

-- Namespace declarations and top-level variables are read.
#guard (match parseSchematron
          ("<schema><ns prefix=\"ex\" uri=\"http://ex/\"/>" ++
           "<let name=\"n\" value=\"1\"/></schema>") with
        | .ok s => s.namespaces == [("ex", "http://ex/")] &&
                   (s.lets.map (·.name)) == ["n"]
        | .error _ => false)

end L4Factoidal.Schematron
