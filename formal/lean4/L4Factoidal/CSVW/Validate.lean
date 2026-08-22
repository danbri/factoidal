/-
L4Factoidal.CSVW.Validate — metadata validation, ported from
`formal/fstar/CSVW.Validate.fst`.

Spec: tabular-metadata §6 "Validation" and the W3C csvw test suite's
`ValidationTest` / `WarningValidationTest` split.

THE DISTINCTION THIS MODULE EXISTS TO PRESERVE: the W3C suite has two
kinds of negative test. A `ValidationTest` must produce an ERROR; a
`WarningValidationTest` must produce a WARNING and still convert. A
port that flagged warnings as errors would fail every warning test
while looking stricter and more correct. Several of the F* module's
comments exist only to record which side of that line a rule falls
on, and those are carried here.
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.CSVW

open L4Factoidal.JSON

/-- A validation finding. Severity is part of the finding, not a
    caller's interpretation of it. -/
inductive Severity where
  | error | warning
deriving Repr, DecidableEq, Inhabited

structure Finding where
  severity : Severity
  message  : String
deriving Repr, DecidableEq, Inhabited

def err (m : String) : Finding := ⟨.error, m⟩
def warn (m : String) : Finding := ⟨.warning, m⟩

/-- Did validation pass? Warnings do NOT fail a document. -/
def passes (fs : List Finding) : Bool := !(fs.any (·.severity == .error))

private def field? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def stringField? (k : String) (v : Json) : Option String :=
  match field? k v with
  | some (.string s) => some s
  | _                => none

private def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- A BCP 47 primary subtag: 2–8 alphabetic characters. -/
def langValid (tag : String) : Bool :=
  let prim := tag.toList.takeWhile (· != '-')
  prim.length ≥ 2 && prim.length ≤ 8 && prim.all isAlpha

/-- `@id` must not be a blank-node reference.

    A NON-STRING `@id` is a WARNING-level graceful degradation, not an
    error, so it is deliberately not flagged here — the F* module
    records the same, against the suite's own classification. -/
def checkId (role : String) (v : Json) : List Finding :=
  match field? "@id" v with
  | some (.string s) =>
      if s.startsWith "_:" then [err (role ++ " @id must not be a blank node")] else []
  | _ => []

/-- `@type`, when present, must match the object's role class. A
    MISSING `@type` is fine — it is inferred. -/
def checkType (role : String) (v : Json) : List Finding :=
  match stringField? "@type" v with
  | some t => if t == role then [] else [err ("@type " ++ t ++ " invalid for a " ++ role)]
  | none   => []

/-- A `titles` object keys its values by language tag; each key must
    be a well-formed tag. -/
def checkTitles (v : Json) : List Finding :=
  match field? "titles" v with
  | some (.object ms) =>
      ms.filterMap (fun (k, _) =>
        if langValid k then none else some (err ("invalid language tag in titles: " ++ k)))
  | _ => []

/-- The built-in datatype names.

    NOTE, carried from the F* module because it is the kind of thing a
    later reader "fixes" into a bug: a datatype string that is NOT a
    built-in name is a WARNING, not an error — the suite classifies
    both the non-builtin case and the absolute-URL case as
    `WarningValidationTest`. So this list drives a warning, never a
    rejection. -/
def knownDatatype (n : String) : Bool :=
  ["anyAtomicType", "anyURI", "base64Binary", "boolean", "date", "dateTime",
   "dateTimeStamp", "decimal", "integer", "long", "int", "short", "byte",
   "nonNegativeInteger", "positiveInteger", "unsignedLong", "unsignedInt",
   "unsignedShort", "unsignedByte", "nonPositiveInteger", "negativeInteger",
   "double", "duration", "dayTimeDuration", "yearMonthDuration", "float",
   "gDay", "gMonth", "gMonthDay", "gYear", "gYearMonth", "hexBinary",
   "QName", "string", "normalizedString", "token", "language", "Name",
   "NMTOKEN", "xml", "html", "json", "time",
   -- csvw aliases
   "number", "binary", "datetime", "any"].contains n

/-- Datatype check: an unknown NAME warns; it never rejects. -/
def checkDatatype (v : Json) : List Finding :=
  match field? "datatype" v with
  | some (.string d) =>
      if knownDatatype d then []
      else [warn ("datatype " ++ d ++ " is not a built-in name")]
  | _ => []

/-- A column object. -/
def checkColumn (v : Json) : List Finding :=
  checkId "column" v ++ checkType "Column" v ++ checkTitles v ++ checkDatatype v

/-- A table schema, including its columns. -/
def checkSchema (v : Json) : List Finding :=
  checkId "schema" v ++ checkType "Schema" v ++
  (match field? "columns" v with
   | some (.array cs) => cs.flatMap checkColumn
   | _ => [])

/-- A table, including its schema. -/
def checkTable (v : Json) : List Finding :=
  checkId "table" v ++ checkType "Table" v ++
  (match field? "tableSchema" v with
   | some s => checkSchema s
   | none   => [])

/-- A table group — the document root. -/
def checkTableGroup (v : Json) : List Finding :=
  checkId "table group" v ++ checkType "TableGroup" v ++
  (match field? "tables" v with
   | some (.array ts) => ts.flatMap checkTable
   | _ => [])

/-- Validate a metadata document from its root. A bare table object
    (no `tables` member) is a valid root too. -/
def validate (v : Json) : List Finding :=
  if (field? "tables" v).isSome then checkTableGroup v else checkTable v

end L4Factoidal.CSVW
