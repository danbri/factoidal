/-
Harness/ShExRun — the ShEx validation suite, run end to end.

`third_party/testing/shex/validation/manifest.jsonld` lists 1182
entries: `sht:ValidationTest` (the focus node MUST satisfy the shape)
and `sht:ValidationFailure` (it must NOT). Each names a schema, a data
graph, a shape label and a focus node.

The schema is read from the ShExJ (`.json`) beside each `.shex`. A
ShExC parser is separate work; ShExJ is the specification's own
abstract syntax written down, and reading it is what lets the
validator be MEASURED today.

## Three outcomes

  * **pass / fail** — the verdict matched, or it did not;
  * **not read** — the schema JSON, the data graph, or the focus node
    could not be read. That is a gap in the READER, not a validation
    result, and folding it into either column would report a parser
    gap as an engine verdict.

## Schema IMPORTs

A ShExJ schema may carry `"imports": ["2RefS1"]`, naming another
schema document RELATIVE to its own retrieval IRI. The imported
document's shape declarations join the importing schema's, and the
importing schema's own `start` wins when both have one (ShEx 2.1 §5.2:
imports contribute declarations, not a start shape). Resolution is
here, in the reader, because it is a document-retrieval step and not a
satisfaction rule.

Usage: `lake exe l4shex [validation-dir] [--verbose] [--only SUBSTR]`
-/
import L4Factoidal.ShEx.FromJson
import L4Factoidal.ShEx.Satisfies
import L4Factoidal.Syntax.Turtle
import L4Factoidal.JSON.Parser
import L4Factoidal.CSVW.Emit

open L4Factoidal.JSON
open L4Factoidal.ShEx
open L4Factoidal.RDF
open L4Factoidal.Syntax

private def fld? (k : String) : Json → Option Json
  | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
  | _          => none

private def str? (k : String) (v : Json) : Option String :=
  match fld? k v with
  | some (.string s) => some s
  | _                => none

/-- The manifest's entries, whatever wrapper it uses. -/
def entriesOf (j : Json) : List Json :=
  let direct := match fld? "entries" j with
    | some (.array es) => es
    | _ => []
  if !direct.isEmpty then direct
  else match fld? "@graph" j with
    | some (.array gs) => gs.flatMap (fun g => match fld? "entries" g with
        | some (.array es) => es
        | _ => [])
    | _ => []

/-- The retrieval URL the suite's own `@context` gives its manifest.
    Everything the manifest names is relative to it, and the DATA
    FILES use that too: `p1.ttl` writes `<x> :p1 "p1-0"`, and the
    entry's focus is the bare string `"x"`. Parsing the graph with no
    base rejected the document outright — 41 entries came back "data
    Turtle not read", which is a reader gap reported as a reader gap
    but a reader gap all the same. -/
def suiteBase : String :=
  "https://raw.githubusercontent.com/shexSpec/shexTest/master/validation/manifest"

/-- A focus node, written as an IRI or as a Turtle literal. The suite
    writes a bare string for an IRI and an object for a literal. -/
def focusOf (base : String) (j : Json) : Option Term :=
  match j with
  | .string s =>
      -- A TOLD BLANK NODE focus is written `_:abcd`. Reading only
      -- IRIs here made `0focusBNODE` and its neighbours read the
      -- focus as nothing, and a `BNODE` node kind then had no node to
      -- hold of.
      if s.startsWith "_:" then some (.bnode (String.ofList (s.toList.drop 2)))
      else
        -- A focus written RELATIVE resolves against the data file,
        -- exactly as the IRIs inside it do.
        let abs := L4Factoidal.Syntax.resolveIri base s
        if h : isIri abs then some (.iri ⟨abs, h⟩) else none
  | .object _ =>
      match str? "@value" j with
      -- The focus literal carries its DATATYPE and its LANGUAGE, and
      -- dropping them made `'ab'^^my:bloodType` read as a plain
      -- string — a different term, which then matched nothing in the
      -- graph (focusdatatype).
      | some v =>
          (match str? "@type" j, str? "@language" j with
           | some d, _ => (if h : isIri d
                           then some (Term.literal (L4Factoidal.CSVW.typedLiteral ⟨d, h⟩ v))
                           else some (Term.literal (Literal.string v)))
           | _, some g => some (Term.literal (Literal.langString v g))
           | _, _      => some (Term.literal (Literal.string v)))
      | none   => (str? "@id" j).bind (fun s =>
          if s.startsWith "_:" then some (Term.bnode (String.ofList (s.toList.drop 2)))
          else
            let abs := L4Factoidal.Syntax.resolveIri base s
            if h : isIri abs then some (Term.iri ⟨abs, h⟩) else none)
  | _ => none

/-- The ShExJ file beside a `.shex`. -/
def jsonBeside (p : String) : String :=
  if p.endsWith ".shex" then String.ofList (p.toList.take (p.length - 5)) ++ ".json" else p

/-- Resolve a manifest-relative path, collapsing one `../`. -/
def resolveRel (dir rel : String) : String :=
  if rel.startsWith "../" then
    let up := match (dir.splitOn "/").reverse with
      | _ :: rest => String.intercalate "/" rest.reverse
      | []        => dir
    up ++ "/" ++ String.ofList (rel.toList.drop 3)
  else dir ++ "/" ++ rel

/-- Merge an imported schema's declarations into the importer's. The
    importer's own `start` wins; its declarations come first, so a
    label it declares itself shadows an imported one. -/
def mergeSchema (outer inner : Schema) : Schema :=
  { start := outer.start.orElse (fun _ => inner.start)
    startActs := outer.startActs
    shapes := outer.shapes ++ inner.shapes.filter (fun d =>
      !(outer.shapes.any (fun o => o.id == d.id)))
    imports := [] }

/-- Read a ShExJ document and resolve its `imports` against the
    directory it was read from. `depth` bounds an import cycle; the
    corpus nests at most two deep. -/
partial def loadSchema (path : String) (depth : Nat) : IO (Option Schema) := do
  if !(← System.FilePath.pathExists path) then return none
  let src ← IO.FS.readFile path
  match (parseJson? src).bind schemaOf with
  | none => return none
  | some sch =>
      if depth == 0 || sch.imports.isEmpty then return some sch
      let dir := match (path.splitOn "/").reverse with
        | _ :: rest => String.intercalate "/" rest.reverse
        | []        => "."
      let mut acc := sch
      for imp in sch.imports do
        let ip := dir ++ "/" ++ imp ++ ".json"
        match ← loadSchema ip (depth - 1) with
        | some inner => acc := mergeSchema acc inner
        | none       => pure ()
      return some { acc with imports := [] }

/-! ## Relative IRIs in the schema document

A ShExJ document may be written with RELATIVE IRIs, and they resolve
against the document's own retrieval IRI — the shape labels, the
predicates, the datatypes and the value-set members alike. The corpus
writes one such schema, `1dot-relative`, whose shape is `"S1"` and
whose predicate is `"p1"`; the data file's IRIs resolve against the
DATA file, so the two sides only meet once both are made absolute.

Resolution is here rather than in `FromJson.lean` because it is a
property of where the document was FETCHED FROM, which the reader of
its bytes does not know.
-/

/-- Does this string already carry a scheme? Only a relative reference
    is resolved; an absolute IRI must come through untouched. -/
def hasScheme (s : String) : Bool :=
  match s.toList.findIdx? (· == ':') with
  | none   => false
  | some i =>
      i > 0 && (s.toList.take i).all (fun c =>
        c.isAlpha || c.isDigit || c == '+' || c == '-' || c == '.')

/-- A BLANK NODE label is not a relative IRI. ShExJ writes a
    bnode-labelled shape as `"_:S1"`, and resolving it against the
    document turned it into `.../validation/_:S1`, which the manifest's
    own `_:S1` then failed to find. -/
def absolutise (base s : String) : String :=
  if hasScheme s || s.isEmpty || s.startsWith "_:" then s
  else L4Factoidal.Syntax.resolveIri base s

def absObjectValue (base : String) : ObjectValue → ObjectValue
  | .iri v => .iri (absolutise base v)
  | .literal v lang dt => .literal v lang (dt.map (absolutise base))

def absStem (base : String) (k : VsvKind) : Stem → Stem
  | .plain p => if k == .iri then .plain (absolutise base p) else .plain p
  | .wildcard => .wildcard

def absExclusion (base : String) (k : VsvKind) : Exclusion → Exclusion
  | .value ov => .value (absObjectValue base ov)
  | .lang t   => .lang t
  | .stem p   => if k == .iri then .stem (absolutise base p) else .stem p

def absVsv (base : String) : ValueSetValue → ValueSetValue
  | .object v            => .object (absObjectValue base v)
  | .stem k st           => .stem k (absStem base k st)
  | .stemRange k st excl => .stemRange k (absStem base k st) (excl.map (absExclusion base k))
  | .language t          => .language t

def absNodeConstraint (base : String) (nc : NodeConstraint) : NodeConstraint :=
  { nc with datatype := nc.datatype.map (absolutise base)
            values := nc.values.map (absVsv base) }

mutual

partial def absShapeExpr (base : String) : ShapeExpr → ShapeExpr
  | .ref id            => .ref (absolutise base id)
  | .shapeAnd es       => .shapeAnd (es.map (absShapeExpr base))
  | .shapeOr es        => .shapeOr (es.map (absShapeExpr base))
  | .shapeNot e        => .shapeNot (absShapeExpr base e)
  | .nodeConstraint nc => .nodeConstraint (absNodeConstraint base nc)
  | .shape sh          => .shape (absShape base sh)
  | .external          => .external

partial def absShape (base : String) : Shape → Shape
  | .mk closed extra expr acts anns exts =>
      .mk closed (extra.map (absolutise base)) (expr.map (absTripleExpr base))
          acts anns (exts.map (absolutise base))

partial def absTripleExpr (base : String) : TripleExpr → TripleExpr
  | .ref id              => .ref (absolutise base id)
  | .tripleConstraint tc => .tripleConstraint (absTc base tc)
  | .eachOf g            => .eachOf (absGroup base g)
  | .oneOf g             => .oneOf (absGroup base g)

partial def absGroup (base : String) : Group → Group
  | .mk id es mn mx acts anns =>
      .mk (id.map (absolutise base)) (es.map (absTripleExpr base)) mn mx acts anns

partial def absTc (base : String) : TripleConstraint → TripleConstraint
  | .mk id inv pred ve mn mx acts anns =>
      .mk (id.map (absolutise base)) inv (absolutise base pred)
          (ve.map (absShapeExpr base)) mn mx acts anns

end

/-- Make every IRI in a schema absolute against its retrieval IRI. -/
def absSchema (base : String) (sch : Schema) : Schema :=
  { sch with start := sch.start.map (absShapeExpr base)
             shapes := sch.shapes.map (fun d =>
               { d with id := absolutise base d.id, expr := absShapeExpr base d.expr }) }

/-- Resolve `ShapeExpr.external` declarations against an EXTERNAL
    schema the manifest entry supplies.

    ShEx 2.1 §5.3 leaves an `EXTERNAL` shape to be decided by a
    mechanism outside the schema. The corpus supplies that mechanism
    per entry, as `"shapeExterns": "../schemas/shapeExtern.shextern"`,
    whose ShExJ twin is the `.jsontern` file beside it. A declaration
    whose whole expression is `EXTERNAL` takes the external schema's
    declaration of the same label. -/
def substituteExternals (sch ext : Schema) : Schema :=
  { sch with shapes := sch.shapes.map (fun d =>
      match d.expr with
      | .external => (ext.lookup d.id).getD d
      | _         => d) }

/-- The ShExJ twin of a `.shextern` file. -/
def jsonternBeside (p : String) : String :=
  if p.endsWith ".shextern"
  then String.ofList (p.toList.take (p.length - 9)) ++ ".jsontern" else p

structure Tally where
  pass    : Nat := 0
  fail    : Nat := 0
  notRead : Nat := 0
deriving Inhabited

/-- Does `hay` contain `needle`? -/
def hasSub (hay needle : String) : Bool :=
  needle.isEmpty || (hay.splitOn needle).length > 1

def main (args : List String) : IO UInt32 := do
  -- `--only SUBSTR` runs just the entries whose name contains SUBSTR.
  -- Diagnosing one family out of 1182 by re-running all of them is how
  -- a ten-second question costs four minutes.
  let only := match args.dropWhile (· != "--only") with
    | _ :: v :: _ => some v
    | _           => none
  let positional := (args.filter (fun a => !a.startsWith "--")).filter
    (fun a => only != some a)
  let dir := positional.head?.getD "third_party/testing/shex/validation"
  let verbose := args.contains "--verbose"
  let manifestPath := dir ++ "/manifest.jsonld"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"shex runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match parseJson? mtext with
  | none =>
      IO.println "shex runner: manifest did not parse"
      return 1
  | some mj =>
      let entries := entriesOf mj
      let mut t : Tally := {}
      -- Each not-read reason with its COUNT. A bare list of reasons
      -- said which gaps exist and not how much of the suite each one
      -- costs, so there was no way to tell a one-file quirk from the
      -- reason forty entries went unanswered.
      let mut readGaps : List (String × Nat) := []
      let bump : List (String × Nat) → String → List (String × Nat) := fun gs r =>
        if gs.any (fun (k, _) => k == r)
        then gs.map (fun (k, n) => if k == r then (k, n + 1) else (k, n))
        else gs ++ [(r, 1)]
      let mut seen := 0
      let _ := seen
      for e in entries do
        seen := seen + 1
        let ty := (str? "@type" e).getD ""
        let name := (str? "name" e).getD "?"
        if !(only.all (hasSub name)) then
          pure ()
        else
        match fld? "action" e with
        | none => t := { t with notRead := t.notRead + 1 }
        | some act =>
            let schemaRel := (str? "schema" act).getD ""
            let dataRel := (str? "data" act).getD ""
            let schemaUrl := L4Factoidal.Syntax.resolveIri suiteBase schemaRel
            -- A manifest `shape` may itself be relative, and resolves
            -- against the manifest, exactly as the schema's own labels
            -- resolve against the schema (`1dot-relative`).
            let label := (str? "shape" act).map (absolutise suiteBase) |>.getD ""
            let dataUrl := L4Factoidal.Syntax.resolveIri suiteBase dataRel
            let focus := (fld? "focus" act).bind (focusOf dataUrl)
            let sp := jsonBeside (resolveRel dir schemaRel)
            let dp := resolveRel dir dataRel
            if !(← System.FilePath.pathExists sp) then
              t := { t with notRead := t.notRead + 1 }
              readGaps := bump readGaps "schema json missing"
            else if !(← System.FilePath.pathExists dp) then
              t := { t with notRead := t.notRead + 1 }
              readGaps := bump readGaps "data graph missing"
            else
              let schema0? ← loadSchema sp 4
              let externs? ← (match (str? "shapeExterns" act).map
                    (fun r => jsonternBeside (resolveRel dir r)) with
                | some ep => loadSchema ep 4
                | none    => pure none)
              let schema? := (match schema0?, externs? with
                | some sc, some ex => some (substituteExternals sc ex)
                | other,   _       => other).map (absSchema schemaUrl)
              let dsrc ← IO.FS.readFile dp
              match schema?, parseTurtle dsrc (some dataUrl), focus with
              | some sch, .ok g, some n =>
                  -- No `shape` in the entry means the schema's START
                  -- shape, not a shape whose label is the empty string.
                  let got := if label.isEmpty then validateStart sch g n
                             else validateNode sch g label n
                  let want := ty == "sht:ValidationTest"
                  if got == want then t := { t with pass := t.pass + 1 }
                  else
                    t := { t with fail := t.fail + 1 }
                    if verbose then
                      IO.println s!"FAIL {name} ({ty}): got {got}"
              | none, _, _ =>
                  t := { t with notRead := t.notRead + 1 }
                  readGaps := bump readGaps "schema JSON not read"
              | _, .error msg, _ =>
                  t := { t with notRead := t.notRead + 1 }
                  readGaps := bump readGaps "data Turtle not read"
                  if verbose then IO.println s!"TURTLE {name}: {msg} ({dataRel})"
              | _, _, none =>
                  t := { t with notRead := t.notRead + 1 }
                  readGaps := bump readGaps "focus node not read"
      IO.println ""
      IO.println s!"shex validation: {t.pass} pass, {t.fail} fail (out of {t.pass + t.fail} decided)"
      IO.println s!"NOT READ: {t.notRead} entries (out of {entries.length})"
      if !readGaps.isEmpty then
        for (r, n) in readGaps do
          IO.println s!"  {n} — {r}"
      IO.println ""
      IO.println "A NOT-READ entry is a gap in the reader, not a validation"
      IO.println "result: folding it into either column would report a parser"
      IO.println "gap as an engine verdict."
      return 0
