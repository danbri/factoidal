/-
L4Factoidal.RML.Tests — build-time checks for RML term generation.
-/
import L4Factoidal.RML.Mapping

namespace L4Factoidal.RML
open L4Factoidal.RDF

private def rec1 : String → Option String
  | "id"   => some "7"
  | "name" => some "Zoë Krüger"
  | "bad"  => some "not an iri"
  | _      => none

-- Template parsing, including RML's backslash escape (which the CSVW
-- RFC 6570 templates deliberately do NOT have).
#guard parseTemplate "http://ex/{id}" ==
       [.literal "http://ex/", .reference "id"]
#guard parseTemplate "a\\{b}" == [.literal "a{b}"]
#guard parseTemplate "plain" == [.literal "plain"]

-- The rml:IRI vs rml:URI distinction: URI-safe is ASCII-only, so
-- non-ASCII is percent-encoded; IRI-safe keeps it.
#guard encodeUriSafe "Zoë" == "Zo%C3%AB"
#guard encodeIriSafe "Zoë" == "Zoë"
#guard encodeUriSafe "a b" == "a%20b"
#guard encodeIriSafe "a b" == "a%20b"     -- space is encoded either way

-- Template expansion under each term type.
#guard expandTemplate (parseTemplate "http://ex/{name}") .uri rec1
       == some "http://ex/Zo%C3%AB%20Kr%C3%BCger"
#guard expandTemplate (parseTemplate "http://ex/{name}") .iri rec1
       == some "http://ex/Zoë%20Krüger"

-- An ABSENT field makes the WHOLE template produce nothing — not an
-- empty string, which would silently emit a wrong term.
#guard expandTemplate (parseTemplate "http://ex/{missing}") .iri rec1 == none
#guard expandTemplate (parseTemplate "http://ex/{id}/{missing}") .iri rec1 == none

-- Constant maps pass their term through.
private def constMap : TermMap := { form := .constant (.literal (Literal.string "k")) }
#guard (generateTerm none constMap rec1).isSome

-- A reference defaults to a LITERAL; a template defaults to an IRI.
#guard defaultTermType (.reference "id") == .literal
#guard defaultTermType (.template "x") == .iri

#guard match generateTerm none { form := .reference "id" } rec1 with
       | some (.literal l) => l.val.lexicalForm == "7"
       | _ => false
#guard match generateTerm none { form := .template "http://ex/{id}" } rec1 with
       | some (.iri i) => i.val == "http://ex/7"
       | _ => false

-- An unresolved reference generates NO TERM.
#guard generateTerm none { form := .reference "missing" } rec1 == none
#guard generateTerm none { form := .unknown } rec1 == none

-- A value that is not a valid IRI where one is required generates no
-- term rather than a malformed one.
#guard generateTerm none { form := .reference "bad", termType := some .iri } rec1 == none

-- Datatype and language on a literal-producing map; a language tag
-- wins, per RDF 1.1.
#guard match generateTerm none
         { form := .reference "id",
           datatype := some "http://www.w3.org/2001/XMLSchema#integer" } rec1 with
       | some (.literal l) => l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#integer"
       | _ => false
#guard match generateTerm none
         { form := .reference "name", language := some "de",
           datatype := some "http://www.w3.org/2001/XMLSchema#integer" } rec1 with
       | some (.literal l) => l.val.langTag == some "de"
       | _ => false

-- A blank-node term type uses the value as the label.
#guard match generateTerm none
         { form := .reference "id", termType := some .blankNode } rec1 with
       | some (.bnode b) => b == "7"
       | _ => false

end L4Factoidal.RML
