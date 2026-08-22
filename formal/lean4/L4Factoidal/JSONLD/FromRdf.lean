/-
L4Factoidal.JSONLD.FromRdf — JSON-LD 1.1 "Serialize RDF as JSON-LD".

Port of `formal/fstar/JSONLD.FromRdf.fst`.

Specification implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §8.5 Serialize RDF as JSON-LD Algorithm — node-map construction per
    graph, `rdf:type` folding into `@type`, graph-name nodes carrying
    `@graph`, and node ordering by `@id`;
  * §8.6 RDF to Object Conversion — `useNativeTypes`, `rdf:JSON`
    literals, `xsd:string` unwrapping, language-tagged strings;
  * §8.7 List Conversion — an `rdf:first`/`rdf:rest` chain of
    referenced-once blank nodes terminating at `rdf:nil` collapses to
    `{"@list": [...]}`;
  * the `rdfDirection` API option in both its modes — `i18n-datatype`
    (decode `https://www.w3.org/ns/i18n#<lang>_<dir>` back into
    `@direction`/`@language`) and `compound-literal` (collapse a blank
    node bearing `rdf:value`/`rdf:direction` into a value object).

The output is an EXPANDED-FORM `Json` tree; the consumer compares it
against the suite's `-out.jsonld` fixture through
`JSONLD.ToRdf.expandedEqual` (RFC 8785 canonical equality), which is the
same comparison `bin/jsonld-fromrdf-runner` makes.

## Scoped out

  * RDF 1.2 triple terms have no settled JSON-LD serialisation; a
    dataset containing one is reported as an error (`.ok none` never
    hides it) rather than serialised wrongly. Same choice as the F*
    source.
  * Framing, and the `@embed`-family options, are a separate
    specification.

## Termination

The list/compound-literal resolution walks a `rdf:rest` chain that the
dataset may make cyclic, so — exactly as the F* source does — every such
walk carries an explicit fuel `Nat` derived from the graph's node count
and decreases it on each step. No `partial`, no well-founded recursion.
-/
import L4Factoidal.JSONLD.ToRdf

namespace L4Factoidal.JSONLD.FromRdf

open L4Factoidal.JSON
open L4Factoidal.RDF

/-! ## Options

The subset of the fromRdf option surface the W3C manifest exercises
(JSON-LD 1.1 API §8.5, the `useNativeTypes` / `useRdfType` /
`rdfDirection` parameters). -/

/-- `rdfDirection` is `none`, `some "i18n-datatype"`, or
`some "compound-literal"`; the two transforms are mutually exclusive —
the suite's cross-paired fixtures (di07/di08 feed a compound literal to
an `i18n-datatype` run; di09/di10 the reverse) pin that each is gated
strictly on its own mode. -/
structure Options where
  useNativeTypes : Bool := false
  useRdfType     : Bool := false
  rdfDirection   : Option String := none
  deriving Repr

def defaultOptions : Options := {}

/-! ## Fixed vocabulary IRIs (compared as plain strings) -/

def rdfTypeIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfFirstIri     : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
def rdfRestIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
def rdfNilIri       : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"
def rdfJsonIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"
def rdfListIri      : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#List"
def rdfValueIri     : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#value"
def rdfDirectionIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#direction"
def rdfLanguageIri  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#language"
def i18nPrefix      : String := "https://www.w3.org/ns/i18n#"

def sXsdString  : String := "http://www.w3.org/2001/XMLSchema#string"
def sXsdInteger : String := "http://www.w3.org/2001/XMLSchema#integer"
def sXsdDouble  : String := "http://www.w3.org/2001/XMLSchema#double"
def sXsdBoolean : String := "http://www.w3.org/2001/XMLSchema#boolean"

/-! ## The intermediate object-value tree

`Ov` is the F* source's `ov`: a node reference, a fully-built value
object, or an RDF collection converted to `@list`. Structural equality
is needed for the spec's "if the value is not already in the array"
duplicate check (fixture 0017); `Json` is a NESTED inductive whose
`DecidableEq` is hand-written, so `Ov` likewise gets a hand-written
mutual `eqb` rather than a derived instance (pitfall #1: never
`deriving BEq`). -/
inductive Ov where
  | ref  : String → Ov
  | val  : Json → Ov
  | lst  : List Ov → Ov
  deriving Repr

mutual

/-- Structural equality on `Ov` (port of F*'s eqtype `=` on `ov`). -/
def Ov.eqb : Ov → Ov → Bool
  | .ref a, .ref b => a == b
  | .val a, .val b => a == b
  | .lst a, .lst b => Ov.eqbList a b
  | _, _ => false

def Ov.eqbList : List Ov → List Ov → Bool
  | [], []           => true
  | x :: xs, y :: ys => Ov.eqb x y && Ov.eqbList xs ys
  | _, _             => false

end

instance : BEq Ov := ⟨Ov.eqb⟩

/-- A node object under construction (F*: `fr_node`). `types` and each
property's value list keep insertion order and are deduplicated. -/
structure FrNode where
  id    : String
  blank : Bool
  types : List String
  props : List (String × List Ov)
  deriving Repr

/-- One named graph's node map plus its display name (F*: `named_nm`). -/
structure NamedNm where
  name  : String
  blank : Bool
  map   : List FrNode
  deriving Repr

/-! ## Display identifiers

The F* `named_graph.ng_name` is a bare IRI string that packs a
blank-node label as `"_:label"`; this port's `RDF.NamedGraph.name` is a
`Subject`, so the packing happens here instead. -/

def subjId : Subject → String
  | .iri i   => i.val
  | .bnode b => "_:" ++ b

def subjIsBlank : Subject → Bool
  | .bnode _ => true
  | _        => false

/-- `some (display-id, isBlank)` when the object is a node; `none` for a
literal or a triple term (which is not a node identifier). -/
def termNodeId : Term → Option (String × Bool)
  | .iri i   => some (i.val, false)
  | .bnode b => some ("_:" ++ b, true)
  | _        => none

def startsWithUnderscoreColon (s : String) : Bool :=
  s.startsWith "_:"

/-! ## Node-map primitives -/

def findNode (nm : List FrNode) (id : String) : Option FrNode :=
  nm.find? (fun n => n.id == id)

def nodeExists (nm : List FrNode) (id : String) : Bool := (findNode nm id).isSome

def ensureNode (nm : List FrNode) (id : String) (blank : Bool) : List FrNode :=
  if nodeExists nm id then nm
  else nm ++ [{ id := id, blank := blank, types := [], props := [] }]

/-- Append preserving order, dropping structural duplicates (F*:
`snoc_unique`). -/
def snocUniqueStr : List String → String → List String
  | [],      x => [x]
  | h :: tl, x => if h == x then h :: tl else h :: snocUniqueStr tl x

def snocUniqueOv : List Ov → Ov → List Ov
  | [],      x => [x]
  | h :: tl, x => if Ov.eqb h x then h :: tl else h :: snocUniqueOv tl x

def findProp (props : List (String × List Ov)) (p : String) : Option (List Ov) :=
  (props.find? (fun kv => kv.1 == p)).map Prod.snd

/-- The single value of a property, when it has exactly one. -/
def nodePropSingle (n : FrNode) (p : String) : Option Ov :=
  match findProp n.props p with
  | some [v] => some v
  | _        => none

def propAdd : List (String × List Ov) → String → Ov → List (String × List Ov)
  | [],             p, v => [(p, [v])]
  | (k, vals) :: tl, p, v =>
    if k == p then (k, snocUniqueOv vals v) :: tl
    else (k, vals) :: propAdd tl p v

def nodeUpdateProp (nm : List FrNode) (id p : String) (v : Ov) : List FrNode :=
  nm.map (fun n => if n.id == id then { n with props := propAdd n.props p v } else n)

def nodeUpdateType (nm : List FrNode) (id t : String) : List FrNode :=
  nm.map (fun n => if n.id == id then { n with types := snocUniqueStr n.types t } else n)

/-! ## RDF to Object Conversion — JSON-LD 1.1 API §8.6 -/

def isDecDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `xsd:integer` lexical space (approximated as the spec's canonical
form requires): optional sign then one or more digits. -/
def isIntLexeme (s : String) : Bool :=
  let cs := s.toList
  let cs := match cs with
            | c :: rest => if c == '+' || c == '-' then rest else cs
            | []        => cs
  !cs.isEmpty && cs.all isDecDigit

/-- A double lexeme is "natively serializable" iff it is a syntactically
valid JSON number AND finite. Non-JSON forms (`+INF`, `NaN`) and
astronomically large exponents (which overflow to infinity, e.g.
`"0.1e999999999999999"` in fixture 0027) are NOT native; the
exponent-digit bound (at most 3 digits) is the F* source's heuristic and
is reproduced exactly. -/
def isFiniteDouble (s : String) : Bool :=
  match parseJson s with
  | .ok (.number _) =>
    match s.toList.findIdx? (fun c => c == 'e' || c == 'E') with
    | none    => true
    | some ei => ((s.toList.drop (ei + 1)).filter isDecDigit).length ≤ 3
  | _ => false

/-- §8.6 step 8: `useNativeTypes` conversion of a typed literal. -/
def nativeValue (lex dt : String) : Ov :=
  if dt == sXsdBoolean then
    -- xsd:boolean lexical space is {true, false, 1, 0}; "True"/"notnative"
    -- stay typed strings (fixture 0027).
    if lex == "true" || lex == "1" then .val (.object [("@value", .bool true)])
    else if lex == "false" || lex == "0" then .val (.object [("@value", .bool false)])
    else .val (.object [("@value", .string lex), ("@type", .string dt)])
  else if dt == sXsdInteger then
    if isIntLexeme lex then .val (.object [("@value", .number lex)])
    else .val (.object [("@value", .string lex), ("@type", .string dt)])
  else if dt == sXsdDouble then
    if isFiniteDouble lex then .val (.object [("@value", .number lex)])
    else .val (.object [("@value", .string lex), ("@type", .string dt)])
  else
    .val (.object [("@value", .string lex), ("@type", .string dt)])

/-- `rdfDirection="i18n-datatype"` reverse mapping: a literal typed
`https://www.w3.org/ns/i18n#<lang>_<dir>` becomes a value object with
`@direction`, plus `@language` only when `<lang>` is non-empty (di05:
`#_rtl` gives no `@language`; di06: `#en-us_rtl` gives `"en-us"`). The
fragment splits on its LAST `_` so a hyphenated subtag stays intact. -/
def i18nValueObject (lex dt : String) : Ov :=
  let frag := (dt.toList.drop i18nPrefix.toList.length)
  -- index of the last '_' in frag, or frag.length when absent
  let up := frag.foldl (fun (acc : Nat × Nat) c =>
              (acc.1 + 1, if c == '_' then acc.1 else acc.2)) (0, frag.length)
  let upPos := up.2
  let lang := if upPos ≥ frag.length then "" else String.ofList (frag.take upPos)
  let dir  := if upPos ≥ frag.length then String.ofList frag
              else String.ofList (frag.drop (upPos + 1))
  let base := [("@value", Json.string lex)]
  let withLang := if lang.isEmpty then base else base ++ [("@language", Json.string lang)]
  .val (.object (withLang ++ [("@direction", Json.string dir)]))

/-- §8.6. `none` signals the fatal "invalid JSON literal" error the
negative fixtures js08/js09 expect. -/
def rdfToObject (opts : Options) : Term → Option Ov
  | .iri i     => some (.ref i.val)
  | .bnode b   => some (.ref ("_:" ++ b))
  -- RDF 1.2 triple terms have no from-RDF JSON-LD representation; report
  -- unsupported rather than emit a wrong value object.
  | .tripleTerm _ _ _ => none
  | .literal l =>
    let lex := l.val.lexicalForm
    let dt  := l.val.datatype.val
    match l.val.langTag with
    | some tag => some (.val (.object [("@value", .string lex), ("@language", .string tag)]))
    | none =>
      if opts.rdfDirection == some "i18n-datatype" && dt.startsWith i18nPrefix then
        some (i18nValueObject lex dt)
      else if dt == rdfJsonIri then
        match parseJson lex with
        | .ok j    => some (.val (.object [("@value", j), ("@type", .string "@json")]))
        | .error _ => none
      else if dt == sXsdString then
        some (.val (.object [("@value", .string lex)]))
      else if opts.useNativeTypes then
        some (nativeValue lex dt)
      else
        some (.val (.object [("@value", .string lex), ("@type", .string dt)]))

/-! ## Node-map construction (per graph) — §8.5 steps 3-5 -/

def processTriple (opts : Options) (nm : List FrNode) (t : Triple)
    : Option (List FrNode) :=
  let sId := subjId t.s
  let nm1 := ensureNode nm sId (subjIsBlank t.s)
  let nm2 := match termNodeId t.o with
             | some (oid, ob) => ensureNode nm1 oid ob
             | none           => nm1
  let p := t.p.val
  let objIsNode := match t.o with | .iri _ => true | .bnode _ => true | _ => false
  if p == rdfTypeIri && !opts.useRdfType && objIsNode then
    match termNodeId t.o with
    | some (oid, _) => some (nodeUpdateType nm2 sId oid)
    | none          => some nm2
  else
    match rdfToObject opts t.o with
    | none   => none
    | some v => some (nodeUpdateProp nm2 sId p v)

def buildNodemap (opts : Options) : List FrNode → List Triple → Option (List FrNode)
  | nm, []      => some nm
  | nm, t :: tl =>
    match processTriple opts nm t with
    | none     => none
    | some nm' => buildNodemap opts nm' tl

def buildNamed (opts : Options) : List NamedGraph → Option (List NamedNm)
  | []        => some []
  | ng :: tl  =>
    match buildNodemap opts [] ng.graph with
    | none   => none
    | some m =>
      match buildNamed opts tl with
      | none        => none
      | some others =>
        let nm := subjId ng.name
        some ({ name := nm, blank := startsWithUnderscoreColon nm, map := m } :: others)

def addGraphNames : List FrNode → List NamedNm → List FrNode
  | nm, []      => nm
  | nm, g :: tl => addGraphNames (ensureNode nm g.name g.blank) tl

def isGraphName (named : List NamedNm) (id : String) : Bool :=
  named.any (fun g => g.name == id)

def lookupGraphMap (named : List NamedNm) (id : String) : Option (List FrNode) :=
  (named.find? (fun g => g.name == id)).map NamedNm.map

/-! ## Global "referenced exactly once" count

Counted across ALL graphs: fixtures 0020/0021 pin that a blank list node
referenced from a second graph is NOT collapsed. -/

def ovsRefids : List Ov → List String
  | []             => []
  | .ref x :: tl   => x :: ovsRefids tl
  | _ :: tl        => ovsRefids tl

def propsRefids : List (String × List Ov) → List String
  | []              => []
  | (_, vals) :: tl => ovsRefids vals ++ propsRefids tl

def nodesRefids : List FrNode → List String
  | []      => []
  | n :: tl => propsRefids n.props ++ nodesRefids tl

def mapsRefids : List (List FrNode) → List String
  | []      => []
  | m :: tl => nodesRefids m ++ mapsRefids tl

def referencedOnce (refids : List String) (id : String) : Bool :=
  (refids.filter (fun y => y == id)).length == 1

/-! ## Compound-literal collapse (`rdfDirection = "compound-literal"`)

A blank node bearing `rdf:value` / `rdf:direction` (/ `rdf:language`) is
folded into a value object and every referenced-once reference to it is
replaced by that object — the exact reverse of the toRdf side's
compound-literal term (di11, di12). Gated on the mode so an
`i18n-datatype` run leaves the same blank node untouched (di07/di08). -/

def objLookup (fields : List (String × Json)) (k : String) : Option Json :=
  (fields.find? (fun kv => kv.1 == k)).map Prod.snd

/-- The `@value` payload of a sub-literal reached through property `p`. -/
def clField (n : FrNode) (p : String) : Option Json :=
  match nodePropSingle n p with
  | some (.val (.object fields)) => objLookup fields "@value"
  | _                            => none

def isClShape (n : FrNode) : Bool :=
  n.blank
  && (nodePropSingle n rdfValueIri).isSome
  && (nodePropSingle n rdfDirectionIri).isSome

def clValueObject (n : FrNode) : Option Json :=
  match clField n rdfValueIri, clField n rdfDirectionIri with
  | some v, some d =>
    let lang := clField n rdfLanguageIri
    some (.object ([("@value", v)]
                   ++ (match lang with | some l => [("@language", l)] | none => [])
                   ++ [("@direction", d)]))
  | _, _ => none

def isClCollapsible (g : List FrNode) (refids : List String) (id : String) : Bool :=
  match findNode g id with
  | none   => false
  | some n => isClShape n && referencedOnce refids id

/-! ## List Conversion — JSON-LD 1.1 API §8.7 -/

/-- The shape a list cell must have: a blank node whose ONLY properties
are exactly one `rdf:first` and one `rdf:rest` (optionally typed
`rdf:List`). -/
def isListShape (n : FrNode) : Bool :=
  n.blank
  && (n.types.isEmpty || n.types == [rdfListIri])
  && n.props.length == 2
  && (nodePropSingle n rdfFirstIri).isSome
  && (nodePropSingle n rdfRestIri).isSome

/-- A node id is collapsible iff it is a referenced-once blank list cell
whose `rest` chain terminates at `rdf:nil`. A cycle never reaches nil,
so it is not collapsible (fixture 0012) — which is also why the walk
carries fuel. -/
def isCollapsible (g : List FrNode) (refids : List String) : String → Nat → Bool
  | _,  0        => false
  | id, fuel + 1 =>
    match findNode g id with
    | none   => false
    | some n =>
      if !isListShape n then false
      else if !referencedOnce refids id then false
      else
        match nodePropSingle n rdfRestIri with
        | some (.ref rt) =>
          if rt == rdfNilIri then true else isCollapsible g refids rt fuel
        | _ => false

mutual

/-- The ordered element list of a collapsible chain starting at `id`. -/
def listFrom (g : List FrNode) (refids : List String) (clMode : Bool)
    : String → Nat → List Ov
  | _,  0        => []
  | id, fuel + 1 =>
    match findNode g id with
    | none   => []
    | some n =>
      match nodePropSingle n rdfFirstIri, nodePropSingle n rdfRestIri with
      | some fv, some (.ref rt) =>
        let elem := resolveOv g refids clMode fv fuel
        if rt == rdfNilIri then [elem]
        else elem :: listFrom g refids clMode rt fuel
      | _, _ => []

/-- Rewrite one value: a reference to a collapsible list head (or to
`rdf:nil`) becomes a nested `@list`; under compound-literal mode a
reference to a collapsible compound literal becomes its value object. -/
def resolveOv (g : List FrNode) (refids : List String) (clMode : Bool)
    : Ov → Nat → Ov
  | v, 0        => v
  | v, fuel + 1 =>
    match v with
    | .ref x =>
      if x == rdfNilIri then .lst []
      else if isCollapsible g refids x (fuel + 1) then
        .lst (listFrom g refids clMode x fuel)
      else if clMode && isClCollapsible g refids x then
        match findNode g x with
        | some n => match clValueObject n with
                    | some j => .val j
                    | none   => .ref x
        | none   => .ref x
      else .ref x
    | .val j  => .val j
    | .lst l  => .lst l

end

def rewriteNode (g : List FrNode) (refids : List String) (clMode : Bool) (fuel : Nat)
    (n : FrNode) : FrNode :=
  { n with props := n.props.map (fun pv =>
      (pv.1, pv.2.map (fun v => resolveOv g refids clMode v fuel))) }

/-! ## JSON emission -/

mutual

def ovToJson : Ov → Json
  | .ref id => .object [("@id", .string id)]
  | .val j  => j
  | .lst l  => .object [("@list", .array (ovListToJson l))]

def ovListToJson : List Ov → List Json
  | []      => []
  | v :: tl => ovToJson v :: ovListToJson tl

end

def typesField (types : List String) : List (String × Json) :=
  if types.isEmpty then [] else [("@type", .array (types.map Json.string))]

def graphField : Option (List Json) → List (String × Json)
  | some gs => [("@graph", .array gs)]
  | none    => []

def propsFields (props : List (String × List Ov)) : List (String × Json) :=
  props.map (fun pv => (pv.1, .array (pv.2.map ovToJson)))

def nodeToJson (n : FrNode) (gj : Option (List Json)) : Json :=
  .object ([("@id", .string n.id)] ++ typesField n.types ++ graphField gj
           ++ propsFields n.props)

/-! ## Node ordering — byte order on `@id`, as the fixtures are written -/

def insertSortedNode (n : FrNode) : List FrNode → List FrNode
  | []      => [n]
  | h :: tl => if strLt n.id h.id then n :: h :: tl else h :: insertSortedNode n tl

def sortNodes : List FrNode → List FrNode
  | []      => []
  | h :: tl => insertSortedNode h (sortNodes tl)

/-! ## Per-graph node emission -/

def graphFuel (g : List FrNode) : Nat := 4 * g.length + 16

/-- A named graph's contents. Under compound-literal mode the collapsed
blank nodes drop out of the survivors (their references were rewritten
into inline value objects). -/
def emitNamedNodes (g : List FrNode) (refids : List String) (clMode : Bool) : List Json :=
  let fuel := graphFuel g
  let survivors := g.filter (fun n =>
    !isCollapsible g refids n.id fuel
    && !(clMode && isClCollapsible g refids n.id)
    && (!n.types.isEmpty || !n.props.isEmpty))
  let rewritten := survivors.map (rewriteNode g refids clMode fuel)
  (sortNodes rewritten).map (fun n => nodeToJson n none)

/-- The default graph: same survivorship, plus graph-name nodes carry
their graph's contents under `@graph`. -/
def emitDefaultNodes (dm : List FrNode) (named : List NamedNm) (refids : List String)
    (clMode : Bool) : List Json :=
  let fuel := graphFuel dm
  let survivors := dm.filter (fun n =>
    !isCollapsible dm refids n.id fuel
    && !(clMode && isClCollapsible dm refids n.id)
    && (!n.types.isEmpty || !n.props.isEmpty || isGraphName named n.id))
  let rewritten := survivors.map (rewriteNode dm refids clMode fuel)
  (sortNodes rewritten).map (fun n =>
    let gj := if isGraphName named n.id then
                match lookupGraphMap named n.id with
                | some gm => some (emitNamedNodes gm refids clMode)
                | none    => some []
              else none
    nodeToJson n gj)

/-! ## Entry point — §8.5 -/

/-- Serialize an RDF dataset as an expanded-form JSON-LD document.
`none` is the fatal "invalid JSON literal" / unsupported-term error. -/
def fromRdf (ds : Dataset) (opts : Options) : Option Json :=
  match buildNodemap opts [] ds.default with
  | none     => none
  | some dm0 =>
    match buildNamed opts ds.named with
    | none       => none
    | some named =>
      let dm := addGraphNames dm0 named
      let allMaps := dm :: named.map NamedNm.map
      let refids := mapsRefids allMaps
      let clMode := opts.rdfDirection == some "compound-literal"
      some (.array (emitDefaultNodes dm named refids clMode))

end L4Factoidal.JSONLD.FromRdf
