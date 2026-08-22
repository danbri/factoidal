/-
L4Factoidal.CSVW.MetadataParse — reading a metadata DOCUMENT into the
model `Metadata.lean` defines.

Spec: "Metadata Vocabulary for Tabular Data"
(https://www.w3.org/TR/tabular-metadata/) §5 (metadata objects),
§5.8 (common properties), §6 (normalization).

Why this module exists: without it the csv2rdf conformance runner can
only attempt the 9 manifest entries that carry NO metadata. 261 of the
270 entries reference a metadata file, so the whole remaining
denominator is behind this parse.

## What is parsed, and what is not

PARSED: `@context` (default language and base), table groups and
single-table documents, `tableSchema` inline, `columns` with `name` /
`titles` in all four shapes / `virtual` / `suppressOutput`, every
inherited property except `textDirection`, `datatype` in both its
string and object forms, `dialect`, `primaryKey`, `rowTitles`, and
COMMON PROPERTIES with prefix expansion.

NOT parsed, and each would be a silent wrong answer if pretended:
`foreignKeys` (needs cross-table reference checking), `transformations`,
and a `tableSchema` given as a URL rather than inline (metadata
DISCOVERY — fetching a second document — which is I/O and belongs to
the caller, not to a pure parse). A document using those still parses;
the parts this module does not model are simply absent from the
result, and the runner reports what that costs rather than scoring it
as a pass.

## Prefix expansion

§5.8 says a common property name may be a prefixed name against the
RDFa Core Initial Context. Rather than vendor that whole table, this
carries the prefixes the CSVW test corpus actually uses, and leaves an
unrecognised prefix ALONE (the name stays as written, and the emitter
then declines to build an IRI from it) — the alternative, guessing a
namespace, would mint triples the document never stated.
-/
import L4Factoidal.CSVW.Metadata
import L4Factoidal.JSON.Parser

namespace L4Factoidal.CSVW

open L4Factoidal.JSON

/-! ## JSON accessors

Small and local rather than a general-purpose JSON query layer: every
one of them is total and returns `none` on a shape mismatch, which is
what keeps the whole parse total. -/

def jField? (k : String) (j : Json) : Option Json :=
  match j with
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

def jStr? (j : Json) : Option String :=
  match j with | .string s => some s | _ => none

def jBool? (j : Json) : Option Bool :=
  match j with | .bool b => some b | _ => none

def jArr? (j : Json) : Option (List Json) :=
  match j with | .array a => some a | _ => none

/-- Keep a value only if it is an OBJECT. `tableSchema` is allowed as
    either an inline object or a URL string; the string form means
    metadata discovery (fetch another document), which is I/O and not
    this module's job, so it must not be mistaken for an empty inline
    schema. -/
def asObject? (j : Json) : Option Json :=
  match j with | .object _ => some j | _ => none

def jStrField? (k : String) (j : Json) : Option String :=
  (jField? k j).bind jStr?

def jBoolField? (k : String) (j : Json) : Option Bool :=
  (jField? k j).bind jBool?

/-- A NUMERIC field. JSON numbers arrive as their source text, so this
    is a decimal-int read, not a float round trip.

    A string is NOT accepted, even one that reads as a number. The
    corpus supplies `"headerRowCount": "0"`, which is invalid, so the
    default of one header row applies — and honouring the string
    instead turned the header into a data row, adding a whole extra
    row of triples to every such test (measured 2026-08-22). -/
def jIntField? (k : String) (j : Json) : Option Int :=
  match jField? k j with
  | some (.number n) => n.toInt?
  | _                => none

/-- A field whose value the spec allows as a bare string OR an object
    with `@value` / `@id` (the atomic-property shapes of §5.1). -/
def jAtomField? (k : String) (j : Json) : Option String :=
  match jField? k j with
  | some (.string s) => some s
  | some (.number n) => some n
  | some v           => (jStrField? "@value" v).orElse (fun _ => jStrField? "@id" v)
  | none             => none

/-! ## The prefix table (§5.8) -/

/-- The prefixes the CSVW test corpus uses, with their RDFa Core
    Initial Context bindings. NOT the whole initial context — see the
    module header for why a partial table with an inert fallback beats
    a guessed namespace. -/
def wellKnownPrefixes : List (String × String) :=
  [ ("csvw",    "http://www.w3.org/ns/csvw#"),
    ("dc",      "http://purl.org/dc/terms/"),
    ("dcterms", "http://purl.org/dc/terms/"),
    ("dcat",    "http://www.w3.org/ns/dcat#"),
    ("foaf",    "http://xmlns.com/foaf/0.1/"),
    ("oa",      "http://www.w3.org/ns/oa#"),
    ("org",     "http://www.w3.org/ns/org#"),
    ("owl",     "http://www.w3.org/2002/07/owl#"),
    ("prov",    "http://www.w3.org/ns/prov#"),
    ("rdf",     "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
    ("rdfs",    "http://www.w3.org/2000/01/rdf-schema#"),
    ("schema",  "http://schema.org/"),
    ("skos",    "http://www.w3.org/2004/02/skos/core#"),
    ("time",    "http://www.w3.org/2006/time#"),
    ("xsd",     "http://www.w3.org/2001/XMLSchema#") ]

/-- Expand a prefixed name. An absolute IRI (one whose prefix is not
    in the table but which already has a scheme and a slash-or-hash
    body) passes through; an unrecognised prefix is returned
    unchanged, so the emitter declines it rather than inventing a
    namespace. -/
def expandPrefixed (s : String) : String :=
  match s.splitOn ":" with
  | pre :: rest =>
      if rest.isEmpty then s
      else
        let local' := String.intercalate ":" rest
        match wellKnownPrefixes.find? (fun (p, _) => p == pre) with
        | some (_, ns) => if local'.startsWith "//" then s else ns ++ local'
        | none         => s
  | [] => s

/-! ## `@context` (§5.2 / §6) -/

/-- The two things a CSVW `@context` can set that change how the rest
    of the document reads: a default language and a base IRI. The
    context array's first member is the CSVW namespace itself and
    carries nothing else. -/
structure Ctx where
  lang : Option String := none
  base : Option String := none
deriving Repr, Inhabited

def readCtxObject (c : Ctx) (j : Json) : Ctx :=
  { lang := (jStrField? "@language" j).orElse (fun _ => c.lang),
    base := (jStrField? "@base" j).orElse (fun _ => c.base) }

def readContext (j : Json) : Ctx :=
  match jField? "@context" j with
  | some (.array items) => items.foldl readCtxObject {}
  | some v              => readCtxObject {} v
  | none                => {}

/-! ## Datatype (§5.11) -/

/-- `format` is a string for most datatypes, but §5.11.3 also allows an
    OBJECT for the numeric ones, carrying `pattern` / `groupChar` /
    `decimalChar`. Reading only the string form left `groupChar`
    unset, so a `decimal` column with `{"groupChar": ","}` never had
    its separators stripped. -/
def parseDatatype (j : Json) : Option Datatype :=
  let fmtObj := (jField? "format" j).bind asObject?
  let sub := fun (k : String) =>
    (jStrField? k j).orElse (fun _ => fmtObj.bind (jStrField? k))
  match j with
  | .string s => some (.named s)
  | .object _ =>
      some (.object
        (jStrField? "base" j) (jStrField? "format" j)
        (sub "pattern") (sub "groupChar")
        (sub "decimalChar") (jStrField? "@id" j)
        (jIntField? "length" j) (jIntField? "minLength" j)
        (jIntField? "maxLength" j) (jAtomField? "minimum" j)
        (jAtomField? "maximum" j) (jAtomField? "minInclusive" j)
        (jAtomField? "maxInclusive" j) (jAtomField? "minExclusive" j)
        (jAtomField? "maxExclusive" j))
  | _ => none

/-! ## Inherited properties (§5.1.1) -/

/-- The member names §5.1.1 defines. Everything else at an object's
    top level is either a structural property of that object type or a
    common property, which is how `commonProps` below decides. -/
def inheritedKeys : List String :=
  ["aboutUrl", "datatype", "default", "lang", "null", "ordered",
   "propertyUrl", "required", "separator", "textDirection"]

/-- `null` is allowed as a string or an array of strings; this slice
    keeps the first, matching `Inherited.null`'s single-string
    shape. -/
def parseNull? (j : Json) : Option String :=
  match jField? "null" j with
  | some (.string s) => some s
  | some (.array (a :: _)) => jStr? a
  | _ => none

/-- A LINK property (`aboutUrl` / `propertyUrl` / `valueUrl`), which
    §5.1.2 requires to be a URI-template string.

    A value of the wrong type normalises to the EMPTY template rather
    than disappearing. That is what the corpus expects: with
    `"aboutUrl": true` the subject is the TABLE URL — the empty
    template expanded and resolved against the table — not a fresh
    blank node (tests 047 / 048 / 049, all
    `ToRdfTestWithWarnings`). Dropping the property instead produces a
    graph with the right shape and the wrong subject on every row. -/
def jLinkField? (k : String) (j : Json) : Option String :=
  match jField? k j with
  | some (.string s) => some s
  | some .null       => none
  | some _           => some ""
  | none             => none

def parseInherited (j : Json) : Inherited :=
  { aboutUrl    := jLinkField? "aboutUrl" j
    propertyUrl := jLinkField? "propertyUrl" j
    valueUrl    := jLinkField? "valueUrl" j
    datatype    := (jField? "datatype" j).bind parseDatatype
    lang        := jStrField? "lang" j
    null        := parseNull? j
    «default»   := jStrField? "default" j
    ordered     := jBoolField? "ordered" j
    required    := jBoolField? "required" j
    separator   := jStrField? "separator" j }

/-! ## Common properties (§5.8) -/

/-- Members that are NOT common properties: the JSON-LD keywords, the
    inherited properties, and the structural members of whichever
    object type is being read (passed in as `structural`). -/
def commonProps (structural : List String) (j : Json) : List CommonProp :=
  match j with
  | .object ms =>
      ms.filterMap (fun (k, v) =>
        if k.startsWith "@" then none
        else if inheritedKeys.contains k then none
        else if structural.contains k then none
        else some { prop := expandPrefixed k, value := v })
  | _ => []

/-! ## Titles (§5.6)

`titles` has four shapes: a string, an array of strings, an object
mapping a language tag to a string, and an object mapping a language
tag to an array. All four reach `titlesLang`, because column-name
derivation is language-aware and flattening them into bare strings
would lose the tag it needs. -/

def titlesOf (defaultLang : Option String) (j : Json) : List (String × Option String) :=
  match j with
  | .string s  => [(s, defaultLang)]
  | .array a   => a.filterMap (fun v => (jStr? v).map (fun s => (s, defaultLang)))
  | .object ms =>
      ms.flatMap (fun (lang, v) =>
        let tag := if lang == "und" then none else some lang
        match v with
        | .string s => [(s, tag)]
        | .array a  => a.filterMap (fun x => (jStr? x).map (fun s => (s, tag)))
        | _         => [])
  | _ => []

/-! ## Dialect (§5.9) -/

def parseDialect (j : Json) : Dialect :=
  { delimiter        := jStrField? "delimiter" j
    quoteChar        := jStrField? "quoteChar" j
    doubleQuote      := jBoolField? "doubleQuote" j
    header           := jBoolField? "header" j
    headerRowCount   := jIntField? "headerRowCount" j
    skipRows         := jIntField? "skipRows" j
    skipColumns      := jIntField? "skipColumns" j
    skipBlankRows    := jBoolField? "skipBlankRows" j
    skipInitialSpace := jBoolField? "skipInitialSpace" j
    commentPrefix    := jStrField? "commentPrefix" j
    encoding         := jStrField? "encoding" j
    trim             := match jField? "trim" j with
      | some (.string s) => some s
      | some (.bool b)   => some (if b then "true" else "false")
      | _                => none }

/-! ## Columns, schema, table, group -/

def columnKeys : List String :=
  ["name", "titles", "virtual", "suppressOutput"]

/-- Is this a usable column `name`? §5.6 restricts it to the variable
    syntax of RFC 6570 — letters, digits, underscore and percent
    escapes — and reserves names beginning with `_` for the
    specification's own (`_row`, `_name`, …).

    An invalid name is IGNORED, and the column falls back to its
    title. The corpus pins this: `"name": "G I D"` with
    `"titles": "GID"` must produce `#GID`, and taking the name
    verbatim produced `#G%20I%20D` — a predicate no query would find
    (measured 2026-08-22). -/
def validColumnName (s : String) : Bool :=
  !s.isEmpty && !s.startsWith "_" &&
  s.all (fun c => c.isAlphanum || c == '_' || c == '%')

def parseColumn (ctx : Ctx) (j : Json) : Column :=
  let tl := match jField? "titles" j with
    | some v => titlesOf ctx.lang v
    | none   => []
  { name           := (jStrField? "name" j).filter validColumnName
    titles         := tl.map (·.1)
    titlesLang     := tl
    virtual        := jBoolField? "virtual" j
    suppressOutput := jBoolField? "suppressOutput" j
    inherited      := parseInherited j
    common         := commonProps columnKeys j }

def schemaKeys : List String :=
  ["columns", "primaryKey", "foreignKeys", "rowTitles"]

/-- A member the spec allows as a string or an array of strings
    (`primaryKey`, `rowTitles`). -/
def strList (j : Json) : List String :=
  match j with
  | .string s => [s]
  | .array a  => a.filterMap jStr?
  | _         => []

def parseSchema (ctx : Ctx) (j : Json) : TableSchema :=
  { columns := match jField? "columns" j with
      | some (.array cs) => cs.map (parseColumn ctx)
      | _                => []
    primaryKey := (jField? "primaryKey" j).map strList |>.getD []
    rowTitles  := (jField? "rowTitles" j).map strList |>.getD []
    aboutUrlBase := jLinkField? "aboutUrl" j
    inherited  := parseInherited j
    common     := commonProps schemaKeys j }

def tableKeys : List String :=
  ["url", "tableSchema", "dialect", "notes", "suppressOutput",
   "tableDirection", "transformations"]

def parseTable (ctx : Ctx) (j : Json) : Option TableDesc :=
  match jStrField? "url" j with
  | none     => none
  | some url =>
      some
        { url       := url
          schema    := match jField? "tableSchema" j with
            | some (.object _) =>
                ((jField? "tableSchema" j).bind asObject?).map (parseSchema ctx)
            -- A STRING is a link to another document: metadata
            -- discovery, which is I/O and not modelled here.
            | some (.string _) => none
            -- Any other value is INVALID and, per the corpus, acts as
            -- an EMPTY OBJECT: the table has a schema with no columns,
            -- so its columns are `_col.1`, `_col.2`, … rather than the
            -- file's headings. Treating it as "no schema" instead
            -- brings the header titles back and changes every
            -- predicate (test107).
            | some _           => some ({} : TableSchema)
            | none             => none
          dialect   := (jField? "dialect" j).map parseDialect
          suppress  := jBoolField? "suppressOutput" j
          inherited := parseInherited j
          common    := commonProps tableKeys j }

def groupKeys : List String :=
  ["tables", "dialect", "notes", "tableDirection", "transformations",
   "tableSchema"]

/-- Read a metadata document. Both shapes §5 allows are accepted: a
    TABLE GROUP (`tables` is an array) and a bare TABLE description
    (`url` at the top level), which is lifted into a one-table group
    so downstream code sees one shape.

    A single-table document's own common properties belong to the
    TABLE, not to the group — putting them on the group would move
    `dc:title` off the `csvw:Table` node and produce a graph that is
    not isomorphic to the expected one for a reason no error message
    would explain. -/
def parseMetadata (j : Json) : Option (TableGroup × Ctx) :=
  let ctx := readContext j
  match jField? "tables" j with
  | some (.array ts) =>
      let groupSchema := ((jField? "tableSchema" j).bind asObject?).map (parseSchema ctx)
      -- §5.3: a schema stated on the GROUP applies to every table that
      -- does not state its own.
      let tables := (ts.filterMap (parseTable ctx)).map (fun t =>
        match t.schema, groupSchema with
        | none, some gs => { t with schema := some gs }
        | _, _          => t)
      some ({ id        := jStrField? "@id" j
              tables    := tables
              dialect   := (jField? "dialect" j).map parseDialect
              inherited := parseInherited j
              common    := commonProps groupKeys j }, ctx)
  | _ =>
      match parseTable ctx j with
      | some t => some ({ tables := [t] }, ctx)
      | none   => none

/-- Parse a metadata document from its source text. -/
def parseMetadataText (src : String) : Option (TableGroup × Ctx) :=
  (parseJson? src).bind parseMetadata

end L4Factoidal.CSVW
