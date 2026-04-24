module XSD.Vocabulary

open RDF.CoreSpec

// XSD datatype IRIs commonly referenced by RDF and SPARQL specs.
//
// Bucket: CORE SPEC.

let xsd_ns : string = "http://www.w3.org/2001/XMLSchema#"

let xsd_string : iri = "http://www.w3.org/2001/XMLSchema#string"
let xsd_integer : iri = "http://www.w3.org/2001/XMLSchema#integer"
let xsd_decimal : iri = "http://www.w3.org/2001/XMLSchema#decimal"
let xsd_double : iri = "http://www.w3.org/2001/XMLSchema#double"
let xsd_float : iri = "http://www.w3.org/2001/XMLSchema#float"
let xsd_boolean : iri = "http://www.w3.org/2001/XMLSchema#boolean"
let xsd_dateTime : iri = "http://www.w3.org/2001/XMLSchema#dateTime"
let xsd_date : iri = "http://www.w3.org/2001/XMLSchema#date"
let xsd_time : iri = "http://www.w3.org/2001/XMLSchema#time"
let xsd_duration : iri = "http://www.w3.org/2001/XMLSchema#duration"
let xsd_dayTimeDuration : iri = "http://www.w3.org/2001/XMLSchema#dayTimeDuration"
let xsd_yearMonthDuration : iri = "http://www.w3.org/2001/XMLSchema#yearMonthDuration"
