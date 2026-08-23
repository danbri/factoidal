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
import L4Factoidal.CSVW.Formats

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
        -- A WARNING, not an error: the suite classifies
        -- `titles with invalid language` as
        -- `ToRdfTestWithWarnings` (test109), so the document still
        -- converts and the title is simply unusable for that
        -- language.
        if langValid k then none else some (warn ("invalid language tag in titles: " ++ k)))
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

/-! ## Common properties (§5.8) — the JSON-LD subset a metadata
document may use, and the keywords it may not

Every rule below names the suite test that states it. These are all
`NegativeRdfTest`s: the document must be REJECTED, not converted with
a warning. -/

/-- Is this a legal `@type` value? §5.8: a term defined in the CSVW
    context, a prefixed name whose prefix is such a term, or an
    absolute URL — and never a blank node.

    `"not a link"` is none of the three, which is what test139 checks;
    an integer is not even a string (test140); and `_:bar` is a blank
    node (test137/test138). -/
def typeValueValid (t : String) : Bool :=
  if t.startsWith "_:" then false
  else if t.toList.any (fun c => c == ' ' || c == '\t') then false
  else if t.toList.contains ':' then true       -- prefixed name or URL
  else t.toList.all (fun c => c.isAlphanum || c == '_')

/-- The JSON-LD keywords a common property may carry. Anything else
    beginning with `@` is a "faux keyword" and rejects the document
    (test146). -/
def allowedKeywords : List String :=
  ["@id", "@type", "@value", "@language"]

private def isKeyword (k : String) : Bool := k.startsWith "@"

/-- `@type` inside a common property must be a STRING — a term, a
    prefixed name or an IRI. An array, an object or a number rejects
    (test137–test140). `@id` likewise, and it must not be a blank node
    (test141). -/
def checkCommonValue : Nat → Json → List Finding
  | 0,        _ => []
  | fuel + 1, .array vs => vs.flatMap (checkCommonValue fuel)
  | fuel + 1, .object ms =>
      let has := fun (k : String) => (ms.find? (fun (k2, _) => k2 == k)).isSome
      let get := fun (k : String) => (ms.find? (fun (k2, _) => k2 == k)).map (·.2)
      let keywordFindings :=
        ms.flatMap (fun (k, v) =>
          if !isKeyword k then []
          else if k == "@context" then
            [err "a common property must not carry @context (test134)"]
          else if k == "@list" then [err "@list is not allowed in a common property"]
          else if k == "@set" then [err "@set is not allowed in a common property"]
          else if !allowedKeywords.contains k then
            [err ("invalid faux-keyword " ++ k ++ " in a common property")]
          else match k, v with
            | "@type", .string t =>
                if typeValueValid t then []
                else [err ("@type value out of range: " ++ t)]
            | "@type", _ => [err "@type in a common property must be a string"]
            | "@id", .string i =>
                if i.startsWith "_:" then
                  [err "@id in a common property must not be a blank node"]
                else []
            | "@id", _ => [err "@id in a common property must be a string"]
            | "@language", .string l =>
                if langValid l then [] else [err ("invalid @language " ++ l)]
            | "@language", _ => [err "@language must be a string"]
            | _, _ => [])
      -- `@value` is exclusive: with it, only ONE of `@type` /
      -- `@language` may appear, and no other member at all
      -- (test142/test143). Without it, `@language` has nothing to tag
      -- (test144).
      let valueFindings :=
        if has "@value" then
          (if has "@type" && has "@language" then
             [err "@value must not carry both @type and @language"] else [])
          ++ (if ms.any (fun (k, _) =>
                 k != "@value" && k != "@type" && k != "@language") then
                [err "@value must not appear beside other properties"] else [])
        else if has "@language" then
          [err "@language outside of @value"]
        else []
      let _ := get
      keywordFindings ++ valueFindings
        ++ ms.flatMap (fun (k, v) => if isKeyword k then [] else checkCommonValue fuel v)
  | _ + 1,    _ => []

/-- Every member of `v` that the specification does not define is a
    common property, and is checked as one. -/
def checkCommonProps (structural : List String) (v : Json) : List Finding :=
  match v with
  | .object ms =>
      ms.flatMap (fun (k, w) =>
        if isKeyword k || structural.contains k then [] else checkCommonValue 12 w)
  | _ => []

/-! ## Datatype value constraints (§5.11.2) -/

private def numOf : Json → Option String
  | .number n => some n
  | .string s => some s
  | _         => none

-- The bounds are not always numbers: a `date` column states
-- `minExclusive: "2015-06-06"`. `facetCompare` falls back to a plain
-- string comparison, which is the right order for the canonical XSD
-- date and time forms because they are fixed-width and big-endian. A
-- numeric-only comparison answered "no opinion" and let an empty range
-- through (test220).
private def numLe (a b : String) : Bool := facetCompare a b != .gt
private def numLt (a b : String) : Bool := facetCompare a b == .lt

/-- The bases on which a LENGTH facet is meaningful, and the bases on
    which a value RANGE is. §5.11.2 makes each a MUST, and the suite
    tests both directions: `length` on a date rejects (test201), and
    `minimum` on a string rejects (test222–test227). -/
def lengthApplies (base : String) : Bool :=
  base == "string" || base == "normalizedString" || base == "token" ||
  base == "language" || base == "Name" || base == "NMTOKEN" ||
  base == "xml" || base == "html" || base == "json" ||
  base == "anyAtomicType" || base == "anyURI" ||
  base == "hexBinary" || base == "base64Binary" || base == "binary"

def rangeApplies (base : String) : Bool :=
  isNumericBase base || isDateBase base || isDurationBase base

/-- The datatype OBJECT's own consistency. -/
def checkDatatypeObject (v : Json) : List Finding :=
  match field? "datatype" v with
  | some (.object ms) =>
      let dv : Json := .object ms
      let get := fun (k : String) => (field? k dv).bind numOf
      let base := (stringField? "base" dv).getD "string"
      let len := get "length"
      let minL := get "minLength"
      let maxL := get "maxLength"
      let mn := get "minimum"
      let mx := get "maximum"
      let mnI := get "minInclusive"
      let mxI := get "maxInclusive"
      let mnE := get "minExclusive"
      let mxE := get "maxExclusive"
      -- A datatype `@id` names a NEW datatype. It must not be a blank
      -- node (test267) and it must not be the URL of a BUILT-IN one
      -- (test243/test244) — redefining `xsd:string` is not a
      -- definition, it is a contradiction.
      let idFinding := match stringField? "@id" dv with
        | some i =>
            if i.startsWith "_:" then [err "datatype @id must not be a blank node"]
            else if i.startsWith "http://www.w3.org/2001/XMLSchema#"
                 || i.startsWith "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
                 || i.startsWith "http://www.w3.org/ns/csvw#" then
              [err ("datatype @id must not be a built-in datatype: " ++ i)]
            else if !(i.toList.contains ':') then
              [err ("invalid datatype @id " ++ i)]
            else []
        | none => []
      -- A stated `length` must sit inside a stated min/max
      -- (test199/test200), and the bounds must not cross (test261).
      let lengthFindings :=
        (match len, minL with
         | some l, some m => if numLe m l then [] else [err "length < minLength"]
         | _, _ => [])
        ++ (match len, maxL with
            | some l, some m => if numLe l m then [] else [err "length > maxLength"]
            | _, _ => [])
        ++ (match minL, maxL with
            | some a, some b => if numLe a b then [] else [err "maxLength < minLength"]
            | _, _ => [])
      -- Inclusive and exclusive bounds on the same side are mutually
      -- exclusive (test216/test217), and the two sides must leave a
      -- non-empty range (test218–test221).
      let rangeFindings :=
        (if mnI.isSome && mnE.isSome then
           [err "minInclusive and minExclusive are mutually exclusive"] else [])
        ++ (if mxI.isSome && mxE.isSome then
              [err "maxInclusive and maxExclusive are mutually exclusive"] else [])
        ++ (match mnI.orElse (fun _ => mn), mxI.orElse (fun _ => mx) with
            | some a, some b => if numLe a b then [] else [err "maxInclusive < minInclusive"]
            | _, _ => [])
        ++ (match mnI, mxE with
            | some a, some b => if numLt a b then [] else [err "maxExclusive ≤ minInclusive"]
            | _, _ => [])
        ++ (match mnE, mxE with
            | some a, some b => if numLe a b then [] else [err "maxExclusive < minExclusive"]
            | _, _ => [])
        ++ (match mnE, mxI with
            | some a, some b => if numLt a b then [] else [err "maxInclusive ≤ minExclusive"]
            | _, _ => [])
      -- A facet must be meaningful for the base it constrains.
      let applicability :=
        (if (len.isSome || minL.isSome || maxL.isSome) && !lengthApplies base then
           [err ("a length facet does not apply to " ++ base)] else [])
        ++ (if (mn.isSome || mx.isSome || mnI.isSome || mxI.isSome ||
                mnE.isSome || mxE.isSome) && !rangeApplies base then
              [err ("a value range does not apply to " ++ base)] else [])
      idFinding ++ lengthFindings ++ rangeFindings ++ applicability
  | some (.string _) => []
  | some _ => [err "datatype must be a string or an object"]
  | none => []

/-! ## Structure -/

def columnKeywords : List String :=
  ["name", "titles", "virtual", "suppressOutput", "aboutUrl", "datatype",
   "default", "lang", "null", "ordered", "propertyUrl", "required",
   "separator", "textDirection"]

/-- A column object. -/
def checkColumn (v : Json) : List Finding :=
  checkId "column" v ++ checkType "Column" v ++ checkTitles v ++ checkDatatype v
    ++ checkDatatypeObject v ++ checkCommonProps columnKeywords v

/-- A foreign key: only `columnReference` and `reference` are allowed,
    and the reference itself takes only `resource` / `schemaReference`
    / `columnReference` (test271/test272). -/
def checkForeignKey (colNames : List String) (v : Json) : List Finding :=
  let refFindings := match field? "reference" v with
    | some (.object rs) =>
        rs.filterMap (fun (k, _) =>
          if ["resource", "schemaReference", "columnReference"].contains k then none
          else some (err ("invalid property " ++ k ++ " in a foreign-key reference")))
        ++ (match (rs.find? (fun (k, _) => k == "resource")).isSome,
                  (rs.find? (fun (k, _) => k == "schemaReference")).isSome with
            | false, false => [err "a foreign-key reference names no resource"]
            | _, _ => [])
    | some _ => [err "a foreign-key reference must be an object"]
    | none   => [err "a foreign key must have a reference"]
  let ownFindings := match v with
    | .object ms =>
        ms.filterMap (fun (k, _) =>
          if ["columnReference", "reference"].contains k then none
          else some (err ("invalid property " ++ k ++ " in a foreign key")))
    | _ => []
  -- Every named source column must exist (test104/test251).
  let srcFindings := match field? "columnReference" v with
    | some (.string c) =>
        if colNames.contains c then [] else [err ("columnReference names no column: " ++ c)]
    | some (.array cs) =>
        cs.filterMap (fun c => match c with
          | .string cn =>
              if colNames.contains cn then none
              else some (err ("columnReference names no column: " ++ cn))
          | _ => some (err "columnReference must hold strings"))
    | some _ => [err "columnReference must be a string or an array of strings"]
    | none   => [err "a foreign key must have a columnReference"]
  ownFindings ++ srcFindings ++ refFindings

def schemaKeywords : List String :=
  ["columns", "primaryKey", "foreignKeys", "rowTitles", "aboutUrl",
   "datatype", "default", "lang", "null", "ordered", "propertyUrl",
   "required", "separator", "textDirection"]

/-- A table schema, including its columns. -/
def checkSchema (v : Json) : List Finding :=
  let cols := match field? "columns" v with
    | some (.array cs) => cs
    | _ => []
  let names := cols.filterMap (stringField? "name")
  -- Column names are unique (test128), and every virtual column comes
  -- after every real one (test133).
  let dupFindings :=
    (names.foldl (fun (seen, acc) n =>
        if seen.contains n then (seen, acc ++ [err ("duplicate column name " ++ n)])
        else (seen ++ [n], acc)) ([], [])).2
  let virtuals := cols.map (fun c =>
    match field? "virtual" c with | some (.bool b) => b | _ => false)
  let orderFindings :=
    if (virtuals.zip (virtuals.drop 1)).any (fun (a, b) => a && !b)
    then [err "a virtual column precedes a non-virtual one"] else []
  checkId "schema" v ++ checkType "Schema" v ++ cols.flatMap checkColumn
    ++ dupFindings ++ orderFindings
    -- `foreignKeys` given as a non-array, or holding a non-object
    -- member, is a WARNING and the offending value is ignored — the
    -- suite classifies both as `ToRdfTestWithWarnings` (test097,
    -- test101). Raising an error there rejected two documents the
    -- suite expects converted, which is what the validator
    -- cross-check below the positive score caught.
    ++ (match field? "foreignKeys" v with
        | some (.array fks) =>
            fks.flatMap (fun fk => match fk with
              | .object _ => checkForeignKey names fk
              | _         => [warn "a foreignKeys member is not an object"])
        | some _ => [warn "foreignKeys is not an array"]
        | none => [])
    ++ checkCommonProps schemaKeywords v

def tableKeywords : List String :=
  ["url", "tableSchema", "dialect", "notes", "suppressOutput",
   "tableDirection", "transformations", "aboutUrl", "datatype", "default",
   "lang", "null", "ordered", "propertyUrl", "required", "separator",
   "textDirection"]

/-- A table, including its schema. `url` is REQUIRED (test090), and a
    `url` that is not a string is a link-value error (test103). -/
def checkTable (v : Json) : List Finding :=
  let urlFindings := match field? "url" v with
    | some (.string _) => []
    | some _           => [err "table url must be a string"]
    | none             => [err "a table must have a url"]
  checkId "table" v ++ checkType "Table" v ++ urlFindings
    ++ (match field? "tableSchema" v with
        | some s => checkSchema s
        | none   => [])
    ++ (match field? "dialect" v with
        | some d => checkId "dialect" d ++ checkType "Dialect" d
        | none   => [])
    ++ (match field? "transformations" v with
        | some (.array ts) =>
            ts.flatMap (fun t => checkId "template" t ++ checkType "Template" t)
        | _ => [])
    ++ checkCommonProps tableKeywords v

def groupKeywords : List String :=
  ["tables", "dialect", "notes", "tableDirection", "transformations",
   "tableSchema", "aboutUrl", "datatype", "default", "lang", "null",
   "ordered", "propertyUrl", "required", "separator", "textDirection"]

/-- Every table's URL and the column names its schema declares — what
    a foreign-key REFERENCE has to resolve against. -/
def tableIndex (v : Json) : List (String × List String) :=
  match field? "tables" v with
  | some (.array ts) =>
      ts.filterMap (fun t =>
        (stringField? "url" t).map (fun u =>
          (u, match (field? "tableSchema" t).bind (field? "columns") with
              | some (.array cs) => cs.filterMap (stringField? "name")
              | _ => [])))
  | _ => []

/-- A foreign key's DESTINATION must exist: the named resource must be
    a table of this document, and every referenced column a column of
    that table (test252/test253). Checking only the source side let a
    reference to a table that is not there pass. -/
def checkForeignKeyTarget (idx : List (String × List String)) (v : Json)
    : List Finding :=
  match field? "reference" v with
  | some r =>
      match stringField? "resource" r with
      | none => []   -- a `schemaReference` target; not resolved here
      | some res =>
          match (idx.find? (fun (u, _) => u == res)).map (·.2) with
          | none => [err ("foreign key references no such table: " ++ res)]
          | some cols =>
              match field? "columnReference" r with
              | some (.string c) =>
                  if cols.contains c then []
                  else [err ("foreign key references no such column: " ++ c)]
              | some (.array cs) =>
                  cs.filterMap (fun c => match c with
                    | .string cn =>
                        if cols.contains cn then none
                        else some (err ("foreign key references no such column: " ++ cn))
                    | _ => none)
              | _ => []
  | none => []

/-- Walk a document's foreign keys against its table index. -/
def checkForeignKeyTargets (v : Json) : List Finding :=
  let idx := tableIndex v
  match field? "tables" v with
  | some (.array ts) =>
      ts.flatMap (fun t =>
        match (field? "tableSchema" t).bind (field? "foreignKeys") with
        | some (.array fks) =>
            fks.flatMap (fun fk => match fk with
              | .object _ => checkForeignKeyTarget idx fk
              | _         => [])
        | _ => [])
  | _ => []

/-- A table group — the document root. `tables` is REQUIRED and must
    be a NON-EMPTY array of objects (test074/test089/test098). -/
def checkTableGroup (v : Json) : List Finding :=
  let tablesFindings := match field? "tables" v with
    | some (.array []) => [err "tables must not be empty"]
    | some (.array ts) =>
        ts.flatMap (fun t => match t with
          | .object _ => checkTable t
          | _         => [err "tables must hold table objects"])
    | some _ => [err "tables must be an array"]
    | none   => [err "a table group must have tables"]
  checkId "table group" v ++ checkType "TableGroup" v ++ tablesFindings
    ++ checkForeignKeyTargets v
    ++ (match field? "dialect" v with
        | some d => checkId "dialect" d ++ checkType "Dialect" d
        | none   => [])
    ++ (match field? "transformations" v with
        | some (.array ts) =>
            ts.flatMap (fun t => checkId "template" t ++ checkType "Template" t)
        | _ => [])
    ++ checkCommonProps groupKeywords v

/-- The document `@context`: an array whose second member, or a bare
    object, may carry ONLY `@base` and `@language` (test274). -/
def checkContext (v : Json) : List Finding :=
  let checkObj := fun (o : Json) => match o with
    | .object ms =>
        ms.filterMap (fun (k, _) =>
          if k == "@base" || k == "@language" then none
          else some (err ("@context may not carry " ++ k)))
    | _ => []
  match field? "@context" v with
  | some (.array items) => items.flatMap checkObj
  | some o              => checkObj o
  | none                => []

/-- Validate a metadata document from its root. A bare table object
    (no `tables` member) is a valid root too. -/
def validate (v : Json) : List Finding :=
  checkContext v
    ++ (if (field? "tables" v).isSome then checkTableGroup v
        else if (field? "url" v).isSome then checkTable v
        else [err "a metadata document must describe a table or a table group"])

end L4Factoidal.CSVW
