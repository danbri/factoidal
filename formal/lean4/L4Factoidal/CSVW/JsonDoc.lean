/-
L4Factoidal.CSVW.JsonDoc — the csv2json DOCUMENT, built from the same
annotated table the RDF pipeline uses.

Spec: "Generating JSON from Tabular Data on the Web"
(https://www.w3.org/TR/csv2json/) §5 minimal mode and §6 standard
mode.

`Json.lean` has the row and document SHAPES. This module is what joins
them to a metadata document and a CSV file, exactly as `Pipeline.lean`
does for RDF — and it is a separate output rather than a rendering of
the triples, for the reason `Json.lean` states: the two suites check
different distinctions.

## Keys are not always column names

csv2json keys a cell by its COLUMN NAME when the column has the
default `propertyUrl`, and by the property URL otherwise — COMPACTED
against the standard prefixes, so a `propertyUrl` of
`http://schema.org/latitude` becomes the member `schema:latitude`
while `http://www.geonames.org/ontology#countryCode`, which no prefix
covers, is written out in full. Both forms appear in one object in
`test031`, which is what makes the rule visible.

## Values are not always strings

A numeric column's value is a JSON NUMBER and a boolean column's is a
JSON BOOLEAN — `42.546245`, not `"42.546245"`. A value that failed its
datatype stays a string, because the string is what the file said and
the number is a claim about it.
-/
import L4Factoidal.CSVW.Pipeline
import L4Factoidal.CSVW.Json

namespace L4Factoidal.CSVW

open L4Factoidal.JSON
open L4Factoidal.RDF

/-- Compact an absolute IRI against the standard prefixes: the reverse
    of `expandPrefixed`. An IRI no prefix covers is left whole. -/
def compactIri (iri : String) : String :=
  match wellKnownPrefixes.find? (fun (_, ns) => iri.startsWith ns) with
  | some (pre, ns) => pre ++ ":" ++ String.ofList (iri.toList.drop ns.length)
  | none           => iri

/-- The member name a cell takes. -/
def jsonKeyFor (tableUrl colName : String) (propertyRef : Option String) : String :=
  match propertyRef with
  | none     => colName
  | some ref => if ref == defaultPropertyRef tableUrl colName then colName
                else compactIri ref

/-- One value, as JSON. `ok` is whether the column's datatype applied;
    a value that failed it stays a string. -/
def jsonValueOf (base : Option String) (ok : Bool) (lex : String) : Json :=
  let b := base.getD "string"
  if !ok then .string lex
  else if b == "boolean" then
    (if lex == "true" || lex == "1" then .bool true
     else if lex == "false" || lex == "0" then .bool false
     else .string lex)
  else if isNumericBase b then
    -- `NaN`, `INF` and `-INF` are NOT JSON numbers, so csv2json writes
    -- them as STRINGS (test155). Emitting them bare produced output
    -- that was not JSON at all — the runner's own comparison could not
    -- parse it, which is the only reason the defect was visible
    -- rather than a quiet mismatch.
    if isSpecialDouble lex then .string lex
    else
      let plain := resolveExponent lex
      -- The DOUBLE family is written with a fractional part, matching
      -- the corpus: `10.10e1` becomes `101.0`, not `101`.
      if (b == "double" || b == "float" || b == "number") &&
         !(plain.toList.contains '.')
      then .number (plain ++ ".0")
      else .number plain
  else .string lex

/-- `rdf:type` is written `@type` in csv2json, and its value is
    COMPACTED — `"@type": "schema:MusicEvent"`, not an `rdf:type`
    member holding an absolute IRI (test032). -/
def rdfTypeIriStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-- The members one cell contributes, or none when it is null. -/
def cellMembers (tableUrl colName : String) (c : CellOut) : List (String × Json) :=
  let isType := c.result.propertyRef == some rdfTypeIriStr
  let key := if isType then "@type" else jsonKeyFor tableUrl colName c.result.propertyRef
  let base := c.inh.datatype.bind Datatype.baseName
  let vals :=
    -- A `valueUrl` VALUE stays an absolute IRI. Only the KEY is
    -- compacted: `schema:about` is a member name, never a value
    -- (test038). The exception is `@type`, whose value IS compacted.
    (c.result.valueRefs.map (fun u => Json.string (if isType then compactIri u else u)))
    ++ (c.result.literals.map (fun (lex, ok) => jsonValueOf base ok lex))
  match vals with
  | []  => []
  | [v] => if c.inh.separator.isSome then [(key, .array [v])] else [(key, v)]
  | vs  => [(key, .array vs)]

/-- A common property's value, as JSON. `@value` and `@id` objects
    FLATTEN to their contents — `{"@id": "http://example.org"}` is the
    string `"http://example.org"` in csv2json output, not an object. -/
def commonJson : Nat → Json → Option Json
  | 0,        _ => none
  | _ + 1,    .string s => some (.string s)
  | _ + 1,    .number n => some (.number n)
  | _ + 1,    .bool b   => some (.bool b)
  | _,        .null     => none
  | fuel + 1, .array vs => some (.array (vs.filterMap (commonJson fuel)))
  | fuel + 1, .object ms =>
      match (ms.find? (fun (k, _) => k == "@value")).map (·.2) with
      | some v => commonJson fuel v
      | none =>
          match (ms.find? (fun (k, _) => k == "@id")).map (·.2) with
          | some (Json.string i) => some (Json.string i)
          | _ =>
              some (.object (ms.filterMap (fun (k, v) =>
                if k.startsWith "@" && k != "@type" then none
                else (commonJson fuel v).map (fun j => (compactIri (expandPrefixed k), j)))))

/-- A common property's name must be an ABSOLUTE IRI here for the same
    reason it must in the RDF output: a bare `foo` or `titles` is not a
    property, and writing it out as a member states something the
    document did not (test093, test275). -/
def commonMembers (ps : List CommonProp) : List (String × Json) :=
  ps.filterMap (fun cp =>
    match absoluteIri? cp.prop with
    | none   => none
    | some _ => (commonJson 16 cp.value).map (fun j => (compactIri cp.prop, j)))

/-- Does `j` mention the IRI `id` anywhere but in its own `@id`? -/
def jsonMentions : Nat → String → Json → Bool
  | 0,        _,  _ => false
  | _ + 1,    id, .string s => s == id
  | fuel + 1, id, .array vs => vs.any (jsonMentions fuel id)
  | fuel + 1, id, .object ms =>
      ms.any (fun (k, v) => k != "@id" && jsonMentions fuel id v)
  | _ + 1,    _,  _ => false

/-- Merge members that share a KEY into one array member, keeping
    first-appearance order.

    Two columns may carry the same `propertyUrl`, and csv2json puts
    their values in ONE member — "multiple values with same subject
    and property … kept in proper relative order" (test305/306/307).
    Emitting a second member with the same name produces an object
    that is not even well formed as a mapping. -/
def mergeMembers (ms : List (String × Json)) : List (String × Json) :=
  let keys := ms.foldl (fun acc (k, _) => if acc.contains k then acc else acc ++ [k]) []
  keys.map (fun k =>
    let vals := (ms.filter (fun (k2, _) => k2 == k)).map (·.2)
    match vals with
    | [v] => (k, v)
    | vs  => (k, .array (vs.flatMap (fun v =>
                match v with | .array xs => xs | x => [x]))))

/-- Substitute a nested object for a reference to it. Bounded by
    `fuel`; a reference chain deeper than that is left as the plain
    IRI rather than looped over. -/
def substituteRefs (subs : List (String × Json)) : Nat → Json → Json
  | 0,        j => j
  | fuel + 1, j =>
      match j with
      | .string s =>
          match (subs.find? (fun (k, _) => k == s)).map (·.2) with
          | some o => substituteRefs subs fuel o
          | none   => .string s
      | .array vs => .array (vs.map (substituteRefs subs fuel))
      | .object ms =>
          .object (ms.map (fun (k, v) =>
            (k, if k == "@id" then v else substituteRefs subs fuel v)))
      | other => other

/-- One row's `describes` array: one object per DISTINCT subject, in
    first-appearance order, each carrying `@id` when its subject is an
    IRI.

    An object whose `@id` is REFERENCED by another object of the same
    row is NESTED inside it rather than listed alongside. csv2json §6
    inlines a `valueUrl` that names another cell's `aboutUrl`, so the
    event in test032 carries its place and its offer as nested
    objects; listing all three side by side gives an array of the
    right length with the structure flattened out of it. -/
def describesOf (tableUrl : String) (r : RowInput) : List Json :=
  let objs := r.subjects.map (fun s =>
    let idStr := match s with
      | .iri i   => some i.val
      | .bnode _ => none
    let idPair := match idStr with
      | some v => [("@id", Json.string v)]
      | none   => []
    let members := (r.cells.filter (fun c => c.subject == s)).flatMap
      (fun c => cellMembers tableUrl c.name c)
    (idStr, Json.object (idPair ++ mergeMembers members)))
  -- Which ids does some OTHER object mention?
  let mentions : List String := objs.flatMap (fun (own, o) =>
    (objs.filterMap (·.1)).filter (fun id =>
      own != some id && jsonMentions 8 id o))
  let subs : List (String × Json) := objs.filterMap (fun (id, o) =>
    id.bind (fun i => if mentions.contains i then some (i, o) else none))
  objs.filterMap (fun (id, o) =>
    match id with
    | some i => if mentions.contains i then none else some (substituteRefs subs 8 o)
    | none   => some (substituteRefs subs 8 o))

/-- Standard mode, one row. -/
def rowJsonOf (tableUrl : String) (r : RowInput) : Json :=
  -- ONE title is a bare string, not a one-element array. csv2json
  -- writes `"titles": "Andorra"`, and wrapping it changed the TYPE of
  -- a value while leaving the document the right shape everywhere
  -- else (test235, test236).
  let titlePairs := match r.titles with
    | []  => []
    | [t] => [("titles", Json.string t)]
    | ts  => [("titles", Json.array (ts.map Json.string))]
  .object (
    [ ("url", .string (tableUrl ++ "#row=" ++ toString r.sourceRow)),
      ("rownum", .number (toString r.rowNum)) ]
    ++ titlePairs ++ [ ("describes", .array (describesOf tableUrl r)) ])

/-- The whole csv2json document, both modes. -/
def convertJson (base : String) (ctx : Ctx) (g : TableGroup) (minimal : Bool)
    (tables : List (TableDesc × Table)) : Json :=
  let per := tables.map (fun (t, tbl) =>
    let tableUrl := L4Factoidal.Syntax.resolveIri base t.url
    (t, tableUrl, tableRowInputs base ctx g t tbl))
  if minimal then
    .array (per.flatMap (fun (t, tableUrl, rows) =>
      if t.suppress == some true then []
      else rows.flatMap (describesOf tableUrl)))
  else
    -- §5.4 `suppressOutput` applies in STANDARD mode too: the
    -- minimal branch above filtered suppressed tables and this one
    -- did not, so a document with a suppressed table emitted a table
    -- object for it.
    let kept := (per.zipIdx).filter (fun ((t, _, _), _) => t.suppress != some true)
    .object ([("tables", .array (kept.map (fun ((t, tableUrl, rows), i) =>
      -- A table with an IDENTITY carries it as `@id`. `tableNodeOf`
      -- is the same function the RDF path uses for the table's
      -- subject, so the two outputs cannot disagree about which
      -- table is which (test102).
      let idPairs := match tableNodeOf base i t with
        | .iri iri => [("@id", Json.string iri.val)]
        | _        => []
      -- `notes` is carried through as a member of the same name, its
      -- values read the way a common property's value is read — the
      -- `@value` and `@id` wrappers flatten, so test036's
      -- `{"@id": "http://example.org/tree-ops-ext"}` becomes the bare
      -- string the corpus writes.
      let notePairs := match t.notes.filterMap (commonJson 16) with
        | []  => []
        | ns  => [("notes", Json.array ns)]
      .object (idPairs ++ [("url", Json.string tableUrl)]
        ++ commonMembers t.common ++ notePairs
        ++ [("row", .array (rows.map (rowJsonOf tableUrl)))]))))]
      ++ commonMembers g.common)

end L4Factoidal.CSVW
