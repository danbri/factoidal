/-
L4Factoidal.CSVW.Metadata — the CSVW metadata model and the
inherited-property rules, ported from `formal/fstar/CSVW.Metadata.fst`.

Spec: "Metadata Vocabulary for Tabular Data"
(https://www.w3.org/TR/tabular-metadata/), §5 metadata objects and
§5.1.1 inherited properties.

Scope, stated as the F* module states it — a slice, not a claim of
completeness. Of the eleven inherited properties (aboutUrl, datatype,
default, lang, null, ordered, propertyUrl, required, separator,
textDirection, valueUrl) this carries all but `textDirection`.
-/
import L4Factoidal.CSVW.Dialect
import L4Factoidal.CSVW.Formats
import L4Factoidal.JSON.Value

namespace L4Factoidal.CSVW

/-- A COMMON PROPERTY (tabular-metadata §5.8): any member of a
    metadata object whose name is not one of the properties the
    specification defines. It carries an expanded property IRI and a
    JSON-LD-shaped value, and csv2rdf §6 emits it as a triple on the
    object it annotates.

    The value is kept as raw `Json` rather than decoded here on
    purpose: §5.8 defers to JSON-LD's value shapes (`@value`/`@type`/
    `@language`/`@id`, arrays, nested nodes), and decoding is the
    emitter's job. Keeping the parse total and the interpretation
    separate is what lets an unrecognised shape drop one triple
    instead of failing the document. -/
structure CommonProp where
  prop  : String
  value : L4Factoidal.JSON.Json
deriving Repr

/-- §5.11.1/§5.11.2 datatype: a named XSD/CSVW datatype, or an object
    with a base plus format and facet constraints. -/
inductive Datatype where
  | named (name : String)
  | object
      (base         : Option String) (format       : Option String)
      (pattern      : Option String) (groupChar    : Option String)
      (decimalChar  : Option String) (id           : Option String)
      (length       : Option Int)    (minLength    : Option Int)
      (maxLength    : Option Int)    (minimum      : Option String)
      (maximum      : Option String) (minInclusive : Option String)
      (maxInclusive : Option String) (minExclusive : Option String)
      (maxExclusive : Option String)
deriving Repr, Inhabited

/-- The base datatype name, whichever form was used. -/
def Datatype.baseName : Datatype → Option String
  | .named n => some n
  | .object b _ _ _ _ _ _ _ _ _ _ _ _ _ _ => b

/-- The `format` facet, absent on the bare named form. -/
def Datatype.formatOf : Datatype → Option String
  | .named _ => none
  | .object _ f _ _ _ _ _ _ _ _ _ _ _ _ _ => f

def Datatype.patternOf : Datatype → Option String
  | .named _ => none
  | .object _ _ p _ _ _ _ _ _ _ _ _ _ _ _ => p

def Datatype.groupCharOf : Datatype → Option String
  | .named _ => none
  | .object _ _ _ g _ _ _ _ _ _ _ _ _ _ _ => g

def Datatype.decimalCharOf : Datatype → Option String
  | .named _ => none
  | .object _ _ _ _ d _ _ _ _ _ _ _ _ _ _ => d

/-- An explicit `@id` on a datatype object: the IRI the literal takes,
    overriding the one its `base` would give. -/
def Datatype.idOf : Datatype → Option String
  | .named _ => none
  | .object _ _ _ _ _ i _ _ _ _ _ _ _ _ _ => i

/-- The §5.11.2 value constraints, in the shape `Formats` checks. -/
def Datatype.facets : Datatype → Facets
  | .named _ => {}
  | .object _ _ _ _ _ _ len minL maxL mn mx mnI mxI mnE mxE =>
      { length := len, minLength := minL, maxLength := maxL,
        minimum := mn, maximum := mx,
        minInclusive := mnI, maxInclusive := mxI,
        minExclusive := mnE, maxExclusive := mxE }

/-- §5.1.1 inherited properties, carried at every level above a
    column (schema / table / table-group) as well as on the column
    itself. One record shared by all levels so the merge is one
    function rather than three. -/
structure Inherited where
  aboutUrl    : Option String   := none
  propertyUrl : Option String   := none
  valueUrl    : Option String   := none
  datatype    : Option Datatype := none
  lang        : Option String   := none
  null        : Option String   := none
  «default»   : Option String   := none
  ordered     : Option Bool     := none
  required    : Option Bool     := none
  separator   : Option String   := none
deriving Repr, Inhabited

/-- §5.1.1 inheritance: a value set on the CHILD wins; otherwise the
    parent's value shows through. Applied parent-to-child down the
    table-group → table → schema → column chain.

    This is exactly why `Dialect` and these records keep `Option`
    rather than resolving defaults early: `none` here means "inherit",
    and a prematurely defaulted field would shadow the parent value
    it was supposed to inherit. -/
def Inherited.override (parent child : Inherited) : Inherited :=
  { aboutUrl    := child.aboutUrl.orElse    (fun _ => parent.aboutUrl)
    propertyUrl := child.propertyUrl.orElse (fun _ => parent.propertyUrl)
    valueUrl    := child.valueUrl.orElse    (fun _ => parent.valueUrl)
    datatype    := child.datatype.orElse    (fun _ => parent.datatype)
    lang        := child.lang.orElse        (fun _ => parent.lang)
    null        := child.null.orElse        (fun _ => parent.null)
    «default»   := child.default.orElse     (fun _ => parent.default)
    ordered     := child.ordered.orElse     (fun _ => parent.ordered)
    required    := child.required.orElse    (fun _ => parent.required)
    separator   := child.separator.orElse   (fun _ => parent.separator) }

/-- §5.6 column description. `titlesLang` keeps each title with its
    explicit language tag (`none` = untagged) for language-aware
    column-name derivation; `titles` is the flattened list. -/
structure Column where
  name           : Option String := none
  titles         : List String := []
  titlesLang     : List (String × Option String) := []
  virtual        : Option Bool := none
  suppressOutput : Option Bool := none
  inherited      : Inherited := {}
  common         : List CommonProp := []
deriving Repr, Inhabited

/-- §5.5 table schema. -/
structure TableSchema where
  columns      : List Column := []
  primaryKey   : List String := []
  rowTitles    : List String := []
  aboutUrlBase : Option String := none
  inherited    : Inherited := {}
  common       : List CommonProp := []
deriving Repr, Inhabited

/-- §5.4 table DESCRIPTION. Named `TableDesc` because `Table` is
    already the reader's parsed-content type in `Dialect.lean`; these
    are different things (metadata about a table vs the rows read from
    one) and conflating them would be a real bug, not a naming nit. -/
structure TableDesc where
  url       : String
  schema    : Option TableSchema := none
  dialect   : Option Dialect := none
  suppress  : Option Bool := none
  inherited : Inherited := {}
  common    : List CommonProp := []
deriving Repr, Inhabited

/-- §5.3 table group — the top of the metadata document. -/
structure TableGroup where
  id        : Option String := none
  tables    : List TableDesc := []
  dialect   : Option Dialect := none
  inherited : Inherited := {}
  common    : List CommonProp := []
deriving Repr, Inhabited

/-- The inherited properties in force at a column, after the full
    table-group → table → schema → column chain. -/
def effectiveInherited (g : TableGroup) (t : TableDesc)
    (s : Option TableSchema) (c : Column) : Inherited :=
  let afterTable  := Inherited.override g.inherited t.inherited
  let afterSchema := match s with
    | some sch => Inherited.override afterTable sch.inherited
    | none     => afterTable
  Inherited.override afterSchema c.inherited

/-- §5.9: a table's dialect falls back to the group's. -/
def effectiveDialect (g : TableGroup) (t : TableDesc) : Dialect :=
  match t.dialect, g.dialect with
  | some d, _      => d
  | none,   some d => d
  | none,   none   => {}

/-- Do two language tags match? BCP 47, truncated to the shorter: `de`
    matches `de-AT`, and `und` matches anything. -/
def langCompatible (want have' : Option String) : Bool :=
  match want, have' with
  | _, none        => true
  | _, some "und"  => true
  | none, _        => true
  | some w, some h =>
      let k := Nat.min w.length h.length
      String.ofList (w.toList.take k) == String.ofList (h.toList.take k)

/-- §5.6 column-name derivation: an explicit `name`, else the first
    title whose LANGUAGE is compatible with the document's, else the
    positional `_col.N` form the spec mandates. `n` is the 1-based
    column position.

    The language check is not optional. A document with `"lang": "de"`
    whose column states `"titles": {"en": "On Street"}` has no usable
    title for that column, so it is `_col.2` — taking the English
    title anyway names the column after a title the document does not
    offer in its own language (test148). -/
def columnName (c : Column) (n : Nat) (preferLang : Option String) : String :=
  match c.name with
  | some nm => nm
  | none =>
      match c.titlesLang.find? (fun (_, l) => langCompatible preferLang l) with
      | some (t, _) => t
      | none        => "_col." ++ toString n

end L4Factoidal.CSVW
