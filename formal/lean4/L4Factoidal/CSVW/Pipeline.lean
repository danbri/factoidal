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

/-- A link property (`aboutUrl` / `propertyUrl` / `valueUrl`) after
    template expansion: a PREFIXED NAME is expanded, then the result is
    resolved against the table's URL.

    Prefix expansion belongs here rather than in the parse because the
    template is expanded first: `schema:{_name}` is not a prefixed name
    until `{_name}` is filled in. Skipping it leaves `rdf:type` and
    `schema:MusicEvent` as opaque strings that pass the `isIri` check
    (they have a colon) and produce triples on made-up IRIs. -/
def linkIri? (base : String) (s : String) : Option WfIri :=
  refIri? base (expandPrefixed s)

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
  -- ...but ONLY when the table description carries no schema. A
  -- metadata document's schema REPLACES the embedded one, so a
  -- schema that describes no usable column leaves the columns
  -- unnamed — `_col.1`, `_col.2`, … — rather than falling back to the
  -- file's headings. The corpus pins this: `test100` supplies
  -- `"columns"` as an object instead of an array, and expects
  -- `#_col.1` … `#_col.5`, not the header titles.
  let headers := match t.schema, tbl.header.head? with
    | none, some h => h.cells
    | _, _         => []
  let nameOf : Column → Nat → String := fun c i =>
    match c.name with
    | some nm => nm
    | none =>
        if !c.titlesLang.isEmpty then columnName c (i + 1) ctx.lang
        else match headers.getD i "" with
          | "" => "_col." ++ toString (i + 1)
          | h  => h
  -- VIRTUAL columns (§5.6) have no field in the file. They are
  -- numbered after the real ones and read an empty cell, so a
  -- `valueUrl` still produces its triple while a literal column would
  -- produce nothing.
  let named := (cols.zipIdx).map (fun (c, i) =>
    let nm := nameOf c i
    (c, nm, columnProperty tableUrl (effectiveInherited g t t.schema c) nm))
  (tbl.rows.zipIdx).map (fun (row, i) =>
    let rowNum := i + 1
    let binds := (named.map (·.2.1)).zip row.cells
    let look := rowLookup binds rowNum row.num
    { rowNum := rowNum, sourceRow := row.num,
      -- §5.5 `rowTitles` names the columns whose values title the ROW.
      titles := match t.schema with
        | some sch =>
            named.zipIdx.filterMap (fun ((_, nm, _), k) =>
              if sch.rowTitles.contains nm then some (row.cells.getD k "") else none)
        | none => [],
      cells := (named.zipIdx).filterMap (fun ((c, nm, inh), k) =>
        if c.suppressOutput == some true then none
        else
          let isVirtual := c.virtual == some true
          -- A virtual column with no `valueUrl` has nothing to say.
          if isVirtual && inh.valueUrl.isNone then none
          else
            let look' := cellLookup look nm (k + 1) (k + 1)
            let r0 :=
              if isVirtual then
                -- A VIRTUAL column has no field, so it must not go
                -- through the cell rules: an empty cell IS the null
                -- value, and `convertCell` would correctly drop it.
                -- Its value comes from `valueUrl` alone.
                ({ propertyRef := inh.propertyUrl.map (UriTemplate.expand look'),
                   aboutRef    := inh.aboutUrl.map (UriTemplate.expand look'),
                   valueRefs   := (inh.valueUrl.map (UriTemplate.expand look')).toList,
                   literals    := [] } : CellResult)
              else convertCell inh nm look' (row.cells.getD k "")
            -- Resolve the link properties HERE, where the table URL is
            -- in scope: `Emit` only checks that a reference is a
            -- well-formed IRI, and a prefixed name like `rdf:type`
            -- passes that check while denoting nothing.
            let resolve := fun (u : String) =>
              match linkIri? tableUrl u with
              | some i => i.val
              | none   => u
            let r := { r0 with
              propertyRef := r0.propertyRef.map resolve,
              valueRefs   := r0.valueRefs.map resolve }
            -- The subject is this CELL's `aboutUrl`, not the row's:
            -- one row can describe several things, each under its own
            -- `aboutUrl`, and a row-level subject merges them.
            let subj := match r.aboutRef.bind (linkIri? tableUrl) with
              | some iri => Subject.iri iri
              | none     => Subject.bnode ("row" ++ toString rowNum)
            some { subject := subj, inh := inh, result := r }) })

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
