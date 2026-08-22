/-
L4Factoidal.CSVW.Pipeline — metadata + CSV in, RDF out.

Spec: csv2rdf (https://www.w3.org/TR/csv2rdf/) §5 minimal mode and §6
standard mode, over the annotated table the tabular-data-model builds
from a metadata document and a CSV file.

This is the piece that turns the parts into a conversion. `Dialect`
reads the file, `MetadataParse` reads the description, `Conversion`
handles one cell, `Emit` builds the scaffolding and `Common` handles
annotations; nothing before this module joins them.

## Column matching

Columns are matched to CSV fields BY POSITION, which is what
tabular-data-model §8 says: `titles` are used to DERIVE a name and to
validate the header, never to reorder. A file with more fields than
the schema describes keeps the extra fields under their default
`_col.N` names rather than dropping them, because dropping data is
worse than emitting a predicate the metadata did not mention.

VIRTUAL columns (§5.6) have no field at all. They come after the real
ones and carry only a `valueUrl`, so they see an empty cell — that is
not a null cell being skipped, it is a column whose value never comes
from the file.

## What is NOT here

Foreign keys, transformations, and metadata DISCOVERY (locating a
metadata document by convention when none is given) are absent —
discovery is I/O, and the other two are checks rather than conversion.
The runner states what that costs instead of scoring around it.
-/
import L4Factoidal.CSVW.Common

namespace L4Factoidal.CSVW

open L4Factoidal.RDF

/-- The columns to convert: the schema's own, extended with default
    columns for any extra CSV field. -/
def effectiveColumns (s : Option TableSchema) (fieldCount : Nat) : List Column :=
  let declared := match s with | some sch => sch.columns | none => []
  let realCount := (declared.filter (fun c => c.virtual != some true)).length
  if realCount ≥ fieldCount then declared
  else declared ++ (List.range (fieldCount - realCount)).map (fun _ => ({} : Column))

/-- The default `propertyUrl` for a column with none stated: the table
    URL with the column name as a fragment (csv2rdf §5.1). -/
def columnProperty (tableUrl : String) (inh : Inherited) (name : String) : Inherited :=
  match inh.propertyUrl with
  | some _ => inh
  | none   => { inh with propertyUrl := some (defaultPropertyRef tableUrl name) }

/-- One table's rows, converted. `base` resolves the table URL and any
    `aboutUrl` the schema states. -/
def tableRowInputs (base : String) (ctx : Ctx) (g : TableGroup) (t : TableDesc)
    (tbl : Table) : List RowInput :=
  let tableUrl := L4Factoidal.Syntax.resolveIri base t.url
  let fieldCount := match tbl.header.head? with
    | some h => h.cells.length
    | none   => match tbl.rows.head? with
      | some r => r.cells.length
      | none   => 0
  let cols := effectiveColumns t.schema fieldCount
  -- The HEADER ROW supplies each column's title when the metadata
  -- does not (tabular-data-model §8, step 4.6). Without this a table
  -- with no metadata gets `_col.1`, `_col.2`, … as its predicates
  -- instead of its own column headings — the whole graph is then
  -- structurally right and semantically wrong, which is exactly the
  -- shape of failure that survives a triple-count check.
  let headers := match tbl.header.head? with
    | some h => h.cells
    | none   => []
  let nameOf : Column → Nat → String := fun c i =>
    match c.name with
    | some nm => nm
    | none =>
        if !c.titlesLang.isEmpty then columnName c (i + 1) ctx.lang
        else match headers.getD i "" with
          | "" => "_col." ++ toString (i + 1)
          | h  => h
  let named := (cols.zipIdx).map (fun (c, i) =>
    (c, nameOf c i,
     columnProperty tableUrl (effectiveInherited g t t.schema c) (nameOf c i)))
  -- The row-level `aboutUrl`: stated once on the schema (or inherited),
  -- expanded per row. Reading it back off the cells instead would make
  -- a row with a suppressed first column lose its subject.
  let rowAbout := (t.schema.bind (fun s => s.aboutUrlBase)).orElse (fun _ =>
    (effectiveInherited g t t.schema {}).aboutUrl)
  (tbl.rows.zipIdx).map (fun (row, i) =>
    let rowNum := i + 1
    let binds := (named.map (·.2.1)).zip row.cells
    let look := rowLookup binds rowNum row.num
    let subject := rowAbout.bind (fun tmpl =>
      (refIri? tableUrl (UriTemplate.expand look tmpl)).map Subject.iri)
    { rowNum := rowNum, sourceRow := row.num, subject := subject,
      cells := (named.zipIdx).filterMap (fun ((c, nm, inh), k) =>
        if c.suppressOutput == some true then none
        else
          let cell := row.cells.getD k ""
          let look' := cellLookup look nm (k + 1) (k + 1)
          some (inh, convertCell inh nm look' cell)) })

/-- Everything one table contributes in STANDARD mode: the
    `csvw:Table` node with its common properties, and the rows. -/
def tableStandard (base : String) (ctx : Ctx) (g : TableGroup) (idx : Nat)
    (t : TableDesc) (tbl : Table) : List Triple :=
  let tableUrl := L4Factoidal.Syntax.resolveIri base t.url
  let tag := toString idx
  tableTriplesStandard tag ("table" ++ tag) tableUrl
    (tableRowInputs base ctx g t tbl)
    (fun node => commonPropsTriples tableUrl ctx.lang ("t" ++ tag) node t.common)

/-- The whole conversion, both modes. `tables` pairs each table
    DESCRIPTION with the rows read from its file. -/
def convert (base : String) (ctx : Ctx) (g : TableGroup) (minimal : Bool)
    (tables : List (TableDesc × Table)) : List Triple :=
  if minimal then
    (tables.zipIdx).flatMap (fun ((t, tbl), _) =>
      (tableRowInputs base ctx g t tbl).flatMap rowTriplesMinimalOf)
  else
    let group : Subject := .bnode "tablegroup"
    let links := (tables.zipIdx).map (fun (_, i) =>
      (⟨group, csvwTableProp, (Subject.bnode ("table" ++ toString i)).toTerm⟩ : Triple))
    (⟨group, rdfTypeIri, .iri csvwTableGroup⟩ : Triple)
      :: (commonPropsTriples base ctx.lang "g" group g.common
          ++ links
          ++ (tables.zipIdx).flatMap (fun ((t, tbl), i) =>
                tableStandard base ctx g i t tbl))

end L4Factoidal.CSVW
