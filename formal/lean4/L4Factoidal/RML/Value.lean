/-
L4Factoidal.RML.Value — a source value and the datatype it carries by
itself.

A JSON source is TYPED, and RML says so: a reference to a number
produces `"10"^^xsd:integer`, not `"10"`. The corpus states it in its
own expected output (`RMLTC0002a-JSON` expects
`<http://example.com/id> "10"^^xsd:integer`), so a record cannot be a
`String → Option String` lookup — the type would already be gone by
the time the term is built.

`natural` is the datatype the SOURCE gives. A `rml:datatype` on the
term map overrides it, and a `rml:language` overrides both, which is
RDF 1.1's rule that every language-tagged literal is an
`rdf:langString`.
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.RML

open L4Factoidal.JSON

/-- One source value: its lexical form, and the datatype the source
    gives it (`none` for a plain string). -/
structure RVal where
  lexical : String
  natural : Option String := none
deriving Repr, DecidableEq, Inhabited

def xsdNs : String := "http://www.w3.org/2001/XMLSchema#"

/-- Does a JSON number's lexical form have a fraction or an exponent?
    XSD calls the first an `xsd:integer` and the second an
    `xsd:double`, and the two are different values as well as
    different types. -/
def numberIsInteger (n : String) : Bool :=
  !(n.toList.any (fun c => c == '.' || c == 'e' || c == 'E'))

/-- The value a JSON node denotes as a source value. `none` for a
    container or for `null`: RML has no term for either, and inventing
    one would put a value in the output that the source does not
    hold. -/
def rvalOf : Json → Option RVal
  | .string s => some { lexical := s }
  | .number n => some { lexical := n,
                        natural := some (xsdNs ++ (if numberIsInteger n then "integer" else "double")) }
  | .bool b   => some { lexical := (if b then "true" else "false"),
                        natural := some (xsdNs ++ "boolean") }
  | _         => none

end L4Factoidal.RML
