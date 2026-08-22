/-
L4Factoidal.CSVW.UriTemplateTests — build-time checks for the RFC 6570
subset, including the fragment-prefix regression.
-/
import L4Factoidal.CSVW.UriTemplate

namespace L4Factoidal.CSVW
open UriTemplate

private def look : String → Option String
  | "countryCode" => some "AD"
  | "name"        => some "Andorra la Vella"
  | "_row"        => some "1"
  | "slash"       => some "a/b"
  | _             => none

#guard parse "a{b}c" == [.literal "a", .var "b", .literal "c"]
#guard parse "plain" == [.literal "plain"]
#guard parse "{v}" == [.var "v"]

-- Simple expansion percent-encodes everything but unreserved.
#guard expand look "{countryCode}" == "AD"
#guard expand look "{name}" == "Andorra%20la%20Vella"
#guard expand look "{slash}" == "a%2Fb"

-- REGRESSION, from the F* module's own war story: `{#var}` on a
-- DEFINED variable keeps the literal '#'. Losing it turned
-- countries.csv#AD into countries.csvAD and broke every fragment
-- template in the csv2rdf corpus.
#guard expand look "countries.csv{#countryCode}" == "countries.csv#AD"

-- An UNDEFINED variable under `{#var}` produces NO output — not even
-- a stray '#'.
#guard expand look "countries.csv{#missing}" == "countries.csv"
#guard expand look "{missing}" == ""

-- Fragment expansion passes reserved characters through.
#guard expand look "{#slash}" == "#a/b"

-- CSVW's underscore variables are ordinary lookups here.
#guard expand look "row-{_row}" == "row-1"

-- Literal text around and between references survives.
#guard expand look "x{countryCode}y{_row}z" == "xADy1z"

end L4Factoidal.CSVW
