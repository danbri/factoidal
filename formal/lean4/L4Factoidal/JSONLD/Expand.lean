/-
L4Factoidal.JSONLD.Expand — JSON-LD 1.1 Expansion.

Port of `formal/fstar/JSONLD.Expand.fst`.

Specifications implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §5.1 Expansion Algorithm — `expandNode` / `expandFieldsList` /
    `expandOneField` and the container-mapping steps;
  * §5.2 Value Expansion Algorithm — `expandItem`'s scalar branches and
    `expandValueObject`;
  * §5.2.2 IRI Expansion — inherited from `JSONLD.Context.expandIri`;
  * the `@container` steps for `@list`, `@set`, `@index`, `@language`,
    `@id`, `@type`, `@graph`, `@graph`+`@id`, `@graph`+`@index`;
  * `@reverse` (both a reverse-defined term used forward and an inline
    `@reverse` block), `@nest`, `@included`, `@json` literals.

Output is an EXPANDED-FORM `Json` tree: node objects keyed by absolute
IRI or keyword, property values array-wrapped, value objects using
`@value`. `JSONLD.ToRdf` consumes exactly that shape.

## Scoped in

Everything the toRdf path needs, matching the F* source function for
function.

## Scoped out (deliberately, and stated)

  * **Frame expansion.** `JSONLD.Context.ContextCore.frameExpansion`
    exists (so the record matches the F* `active_context`), but the
    JSON-LD Framing relaxations the F* source gates on it — the five
    framing keywords passing through, Value Pattern shapes (`{}` / `[]`
    / arrays) surviving value-object validation, and array-shaped `@id`
    — are NOT ported. JSON-LD Framing is a separate specification and a
    separate suite; this module targets §5.1/§5.2 and the toRdf
    manifest. A document that needs them fails honestly.
  * Compaction, flattening, and framing themselves
    (`JSONLD.Compact.fst`, `JSONLD.Flatten.fst`, `JSONLD.Frame.fst`).

## Fuel

Mutual recursion over the document tree is bounded by an explicit fuel
parameter derived from `Json.size`, exactly as the F* source does; every
recursive call decrements it, so every function is total.
-/
import L4Factoidal.JSONLD.Context

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## Small helpers — no recursion into the document tree -/

/-- Expanded form wraps property values in arrays; be lenient about a
bare value where an array is required. -/
def asArray (v : Json) : List Json :=
  match v with
  | .array items => items
  | _            => [v]

def hasField (name : String) (fields : List (String × Json)) : Bool :=
  fields.any (fun kv => kv.1 == name)

/-- Alias-aware field lookup used throughout expansion's object-SHAPE
dispatch (is this JSON object a value object? a list object? …).
JSON-LD 1.1 lets a scoped or ordinary context alias any keyword to an
arbitrary term name, and a value/list object in property-value position
must be recognised through that alias or it is misrouted into ordinary
node-object expansion. Keys resolve vocab-relative — object keys are
always property/keyword names, never document-relative values. A
literal keyword spelling is unaffected, since `expandIriGen` returns any
actual keyword before consulting the term table. -/
def findAliasedField (ac : ActiveContext) (kw : String)
    : List (String × Json) → Option (String × Json)
  | [] => none
  | (k, v) :: rest =>
    match expandIri ac k true with
    | some e => if e == kw then some (k, v) else findAliasedField ac kw rest
    | none   => findAliasedField ac kw rest

def hasAliasedField (ac : ActiveContext) (kw : String) (fields : List (String × Json)) : Bool :=
  (findAliasedField ac kw fields).isSome

/-- True when EVERY member is `@graph` — the document-wrapper shape,
whose contents belong to the DEFAULT graph rather than a fresh named
graph. -/
def onlyGraphKeys (fields : List (String × Json)) : Bool :=
  fields.all (fun kv => kv.1 == "@graph")

def collectGraphValues (fields : List (String × Json)) : List Json :=
  fields.flatMap (fun kv => asArray kv.2)

/-- Wrap a bare boolean/number scalar as a value object, applying a
term's `@type` coercion. `@id`/`@vocab` coercion is meaningless for a
non-string scalar; `@none` means "suppress this term's own coercion",
leaving the scalar's native type alone. -/
def wrapScalar (typeMap : Option String) (v : Json) : Json :=
  match typeMap with
  | some dt =>
    if dt == "@id" || dt == "@vocab" || dt == "@none" then .object [("@value", v)]
    else .object [("@value", v), ("@type", .string dt)]
  | none => .object [("@value", v)]

/-- The five keys a value object may carry (JSON-LD 1.1 §9.5 / §5.1's
"invalid value object" error), checked through their ALIAS-RESOLVED
IRI. -/
def valueObjectKeysValid (ac : ActiveContext) (fields : List (String × Json)) : Bool :=
  fields.all (fun kv =>
    match expandIri ac kv.1 true with
    | some e => e == "@value" || e == "@language" || e == "@type"
                || e == "@direction" || e == "@index"
    | none => false)

/-- A bare ASCII space is never legal, unencoded, inside an IRI (RFC
3986 §2). `isIri` only checks for a colon, so a value-object `@type`
that expands with an embedded space needs this extra check to be
rejected as an "invalid typed value". Not a full RFC 3986 validator. -/
def stringHasSpace (s : String) : Bool := s.toList.contains ' '

def isBnodeShaped (s : String) : Bool := slen s ≥ 2 && charAtD s 0 == '_' && charAtD s 1 == ':'

/-! ## Frame expansion

JSON-LD Framing expands the FRAME document under a different grammar
from an ordinary document: a frame may write `"@id": ["A", "B"]` or
`"@id": {}` as a matching pattern, and it carries five directives that
ordinary expansion does not know. `ActiveContext.frameExpansion` selects
that grammar; it is `false` for every input document, and `true` only for
the frame `JSONLD.Frame` expands.

Without these branches the frame's directives are dropped as keyword
LOOKALIKES — they are not ordinary Expansion vocabulary — and never
reach the framing algorithm at all. -/

/-- The five JSON-LD Framing directives. -/
def isFramingKeyword (k : String) : Bool :=
  k == "@explicit" || k == "@default" || k == "@omitDefault"
    || k == "@requireAll" || k == "@embed"

/-- The framing grammar for an ARRAY `@id`: every entry is an IRI string
or the empty object (the wildcard). Anything else is not a frame
pattern and falls through to the ordinary "invalid `@id` value". -/
def idFrameEntriesValid : List Json → Bool
  | [] => true
  | .string _ :: rest => idFrameEntriesValid rest
  | .object [] :: rest => idFrameEntriesValid rest
  | _ => false

/-- JSON-LD 1.1 API §5.2 Value Expansion, the already-`@value`-form
case: pull out `@value` / `@language` / `@type` / `@direction` /
`@index`, expanding a compact-IRI `@type`. `@direction` is orthogonal to
`@type` (mutually exclusive) but MAY coexist with `@language`. What the
emitted direction becomes at the RDF layer is `JSONLD.ToRdf`'s
`rdfDirection` concern; here it is just another expanded-form field. -/
def expandValueObject (ac : ActiveContext) (fields : List (String × Json)) : Res Json :=
  match findAliasedField ac "@value" fields with
  | none => .error .invalidValueObject
  | some (_, v) =>
    -- Validation battery: only the five value-object keys; `@index` a
    -- string; `@language` a string or null; `@type` a SINGLE string and
    -- not a blank node label; a structured `@value` only under
    -- `@type: @json`; `@language` only on a string `@value`.
    if !valueObjectKeysValid ac fields then .error .invalidValueObject
    else if (match findAliasedField ac "@index" fields with
             | some (_, .string _) => false | some _ => true | none => false) then
      .error .invalidIndexValue
    else if (match findAliasedField ac "@language" fields with
             | some (_, .string _) => false | some (_, .null) => false
             | some _ => true | none => false) then
      .error .invalidLanguageTaggedString
    else if (match findAliasedField ac "@type" fields with
             | some (_, .string _) => false | some _ => true | none => false) then
      .error .invalidTypedValue
    else
      let lang := match findAliasedField ac "@language" fields with
                  | some (_, .string s) => some s | _ => none
      let typ := match findAliasedField ac "@type" fields with
                 | some (_, .string s) => some s | _ => none
      -- `@type`'s RAW string is what a term definition WROTE, not
      -- necessarily the keyword: a context-aliased `"json": "@json"`
      -- must still be recognised as `@json` here.
      let typExpanded := typ.bind (fun t => expandIri ac t true)
      if (match typ with | some t => isBnodeShaped t | none => false) then .error .invalidTypedValue
      else if (match v with
               | .array _ | .object _ => typExpanded != some "@json"
               | _ => false) then .error .invalidValueObjectValue
      else if lang.isSome && (match v with
                              | .string _ => false | .null => false | _ => true) then
        .error .invalidLanguageTaggedValue
      else
        -- `some none`: no `@direction`; `some (some d)`: a valid value;
        -- `none`: present but invalid.
        let dir : Option (Option String) :=
          match findAliasedField ac "@direction" fields with
          | none            => some none
          | some (_, .null) => some none
          | some (_, .string d) => if d == "ltr" || d == "rtl" then some (some d) else none
          | some _ => none
        -- Expanded value objects RETAIN their own `@index` member.
        let idx : List (String × Json) :=
          match findAliasedField ac "@index" fields with
          | some (_, .string s) => [("@index", .string s)]
          | _ => []
        match dir with
        | none => .error .invalidBaseDirection
        | some (some d) =>
          if typ.isSome then .error .invalidValueObject
          else
            match lang with
            | some lg => .ok (.object (("@value", v) :: ("@language", .string lg)
                                        :: ("@direction", .string d) :: idx))
            | none    => .ok (.object (("@value", v) :: ("@direction", .string d) :: idx))
        | some none =>
          match lang, typ with
          | some _, some _ => .error .invalidValueObject
          | some lg, none  => .ok (.object (("@value", v) :: ("@language", .string lg) :: idx))
          | none, some t =>
            match expandIri ac t true with
            | none => .error .invalidTypedValue
            | some iri =>
              if stringHasSpace iri then .error .invalidTypedValue
              else .ok (.object (("@value", v) :: ("@type", .string iri) :: idx))
          | none, none => .ok (.object (("@value", v) :: idx))

/-- Split a node object's members into its (at most one) `@context`
value and the rest. -/
def extractContext (fields : List (String × Json)) : Option Json × List (String × Json) :=
  ((fields.find? (fun kv => kv.1 == "@context")).map Prod.snd,
   fields.filter (fun kv => kv.1 != "@context"))

/-- A node object's `@type` value must be a string or an array of
strings (§5.1's "invalid type value"). -/
def typeEntriesAllStrings (items : List Json) : Bool :=
  items.all (fun it => match it with | .string _ => true | _ => false)

/-- Every produced reverse-property item must be a node object or node
reference — a value object or list object in reverse position is an
"invalid reverse property value". -/
def itemsAllNodeLike (items : List Json) : Bool :=
  items.all (fun it =>
    match it with
    | .object fields => !hasField "@value" fields && !hasField "@list" fields
    | _ => false)

/-- A language map's entry values must be strings, null, or arrays of
those. -/
def languageEntryValuesValid (items : List Json) : Bool :=
  items.all (fun it => match it with | .string _ => true | .null => true | _ => false)

def languageMapValid (entries : List (String × Json)) : Bool :=
  entries.all (fun kv => languageEntryValuesValid (asArray kv.2))

/-- A list object may carry only `@list` and `@index` (§5.1's "invalid
set or list object"). Alias-resolved. -/
def listObjectKeysValid (ac : ActiveContext) (fields : List (String × Json)) : Bool :=
  fields.all (fun kv =>
    match expandIri ac kv.1 true with
    | some e => e == "@list" || e == "@index"
    | none   => false)

/-- `@type` values: vocab-relative IRI expansion with a DOCUMENT-relative
fallback (§5.1 expands `@type` with both `vocab` and `documentRelative`
true). A relative `@type` resolving against neither stays as its literal
string (§5.2.2's final "return value as is"); a keyword lookalike is
dropped with a warning. Downstream triple generation filters non-IRI
`@type` entries. -/
def expandTypeItems (ac : ActiveContext) : List Json → List Json
  | [] => []
  | .string t :: rest =>
    (match expandIri ac t true with
     | some iri => .string iri :: expandTypeItems ac rest
     | none =>
       match expandIri ac t false with
       | some iri => .string iri :: expandTypeItems ac rest
       | none => if keywordLookalike t then expandTypeItems ac rest
                 else .string t :: expandTypeItems ac rest)
  | _ :: rest => expandTypeItems ac rest

def expandTypeValues (ac : ActiveContext) (value : Json) : List Json :=
  expandTypeItems ac (asArray value)

/-! ## Scoped-context application — JSON-LD 1.1 API §5.1 -/

/-- Apply the term's own scoped `@context` for a PROPERTY use: propagate
defaults to TRUE and override-protected is TRUE (a term's own scoped
context, being scoped to uses of that term, may touch protected terms).

The pop target is decided HERE rather than inherited from
`applyContextWithPropagate`: an explicit `"@propagate": false` pops back
to exactly `ac` (the state right before THIS application), while the
propagate-true default has NO pop point for the immediate value — the
scope is meant to persist, not revert one call later. Trusting whatever
pop target survived the context-processing call instead lets a stale
type-scope pointer discard the property's own redefinitions. -/
def applyPropertyScopedContext (loader : Loader) (ac : ActiveContext) (termOpt : Option TermDef)
    : Res ActiveContext :=
  match termOpt with
  | some td =>
    match td.scopedContext with
    | some (sc, defDocUrl) =>
      -- `defDocUrl`: the document THIS scoped context was written in,
      -- captured at term-definition time.
      match applyContextWithPropagate loader (ac.upd (fun c => { c with docUrl := defDocUrl }))
              sc true true with
      | .error e => .error e
      | .ok acEff =>
        if scanPropagate sc true then .ok acEff.clearPrev
        -- A non-propagating property-scoped context must not be popped
        -- away by the very value it was computed for; the suppression is
        -- one-shot and consumed on the next node entry.
        else .ok ((acEff.setPrev ac).upd (fun c => { c with suppressPop := true }))
    | none => .ok ac
  | none => .ok ac

def rawTypeStringsOfItems : List Json → List String
  | [] => []
  | .string s :: rest => s :: rawTypeStringsOfItems rest
  | _ :: rest => rawTypeStringsOfItems rest

/-- The RAW (as-written) string entries of a node object's `@type`
member(s), used to look up type-scoped contexts by term NAME. The member
need not be the literal `@type` key: a keyword-ALIAS term names it just
as well, and missing that case silently skips the type-scoped context
even though the `rdf:type` triple still comes out right. -/
def rawTypeStrings (ac0 : ActiveContext) : List (String × Json) → List String
  | [] => []
  | (k, v) :: rest =>
    let isTypeKey := k == "@type" ||
      (match expandIri ac0 k true with | some e => e == "@type" | none => false)
    if isTypeKey then rawTypeStringsOfItems (asArray v) ++ rawTypeStrings ac0 rest
    else rawTypeStrings ac0 rest

/-- Apply every type-scoped context named by this node object's own
`@type` member(s), on top of `ac0` (the context after this node's own
inline `@context`, before any type-scoped modification). -/
def expandTypedAc (loader : Loader) (ac0 : ActiveContext) (fields : List (String × Json))
    : Res ActiveContext :=
  match rawTypeStrings ac0 fields with
  | []    => .ok ac0
  | types => applyTypeScopedContexts loader ac0 types

/-! ## Map-shaped container helpers -/

/-- `@index` containers, the toRdf-relevant half: the entry values,
flattened. -/
def flattenMapEntries (entries : List (String × Json)) : List Json :=
  entries.flatMap (fun kv => asArray kv.2)

/-- One `@language` map entry value. `isNone` is whether the KEY
resolves to `@none` (possibly through an alias); otherwise `key` IS the
language tag. `dir` is the effective direction for this map's items. -/
def languageMapItem (key : String) (isNone : Bool) (dir : Option String) (v : Json)
    : Option Json :=
  match v with
  | .string s =>
    if isNone then some (.object [("@value", .string s)])
    else
      match dir with
      | some d => some (.object [("@value", .string s), ("@language", .string key),
                                  ("@direction", .string d)])
      | none   => some (.object [("@value", .string s), ("@language", .string key)])
  | _ => none

def languageMapEntryItems (key : String) (isNone : Bool) (dir : Option String)
    : List Json → List Json
  | [] => []
  | v :: rest =>
    match languageMapItem key isNone dir v with
    | some it => it :: languageMapEntryItems key isNone dir rest
    | none    => languageMapEntryItems key isNone dir rest

def expandLanguageMap (ac : ActiveContext) (dir : Option String)
    : List (String × Json) → List Json
  | [] => []
  | (k, v) :: rest =>
    -- A key that is a term ALIASED to `@none` counts as `@none` even
    -- when the raw key text is not literally "@none".
    let isNone := (k == "@none") ||
      (match expandIri ac k true with | some "@none" => true | _ => false)
    languageMapEntryItems k isNone dir (asArray v) ++ expandLanguageMap ac dir rest

/-- Inject an `@id`-map key (already IRI-expanded) into an expanded
item, unless it is a value object or already carries `@id`. -/
def setIdIfAbsent (iri : String) (item : Json) : Json :=
  match item with
  | .object fields =>
    if hasField "@value" fields then item
    else if hasField "@id" fields then item
    else .object (("@id", .string iri) :: fields)
  | _ => item

/-- When the expanded item already carries its own `@type` array, the
map key PREPENDS into that array rather than adding a duplicate field. -/
def prependTypeExisting (kiri : String) : List (String × Json) → Option (List (String × Json))
  | [] => none
  | ("@type", .array ts) :: rest => some (("@type", .array (.string kiri :: ts)) :: rest)
  | kv :: rest =>
    match prependTypeExisting kiri rest with
    | none   => none
    | some r => some (kv :: r)

def addTypeToItem (kiri : String) (item : Json) : Json :=
  match item with
  | .object fields =>
    if hasField "@value" fields then item
    else
      match prependTypeExisting kiri fields with
      | some fields1 => .object fields1
      | none         => .object (("@type", .array [.string kiri]) :: fields)
  | _ => item

/-- A container-map key resolved to either "no override" (the literal
`@none`, or a term whose own mapping IS `@none`) or the IRI to apply.
The `@none`-ALIAS probe is always VOCAB-relative even when the key IRI
itself expands document-relative, because term substitution is
vocab-gated — without it an aliased `@none` key in an `@id` map would
base-resolve into a spurious graph/id name. -/
def mapKeyIri (ac : ActiveContext) (k : String) (vocab : Bool) : Option String :=
  if k == "@none" then none
  else
    let noneAlias := match expandIri ac k true with | some i => i == "@none" | none => false
    if noneAlias then none
    else
      match expandIri ac k vocab with
      | some iri => if iri == "@none" then none else some iri
      | none     => none

def isGraphObject (v : Json) : Bool :=
  match v with
  | .object fields => hasField "@graph" fields
  | _              => false

def ensureGraphObject (nodeObj : Json) : Json :=
  if isGraphObject nodeObj then nodeObj else .object [("@graph", .array [nodeObj])]

/-- Property-valued index post-processing: inject an extra
`(indexIri, [keyVal])` field onto one already-expanded item. An error
(not a silent drop) when the target already carries `@value` — §5.1's
"attempting to add a property to a value object". PREPENDED, not
appended: §5.1's property-valued index step adds the index value BEFORE
existing values of the same property. -/
def injectIndexField (indexIri : String) (keyVal : Json) (item : Json) : Res Json :=
  match item with
  | .object fields =>
    if hasField "@value" fields then .error .invalidIndexValue
    else .ok (.object ((indexIri, .array [keyVal]) :: fields))
  | _ => .error .invalidIndexValue

def injectIndexItems (indexIri : String) (keyVal : Json) : List Json → Res (List Json)
  | [] => .ok []
  | it :: rest =>
    match injectIndexField indexIri keyVal it with
    | .error e => .error e
    | .ok it1 =>
      match injectIndexItems indexIri keyVal rest with
      | .error e => .error e
      | .ok restOut => .ok (it1 :: restOut)

/-! ## Node-entry pop-check helpers -/

/-- §5.1's node-object pop-check exempts two shapes, tested against keys
as IRI-expanded through the INCOMING (not-yet-popped) context: a bare
node REFERENCE (exactly one entry expanding to `@id`), and a VALUE
object (any entry expanding to `@value` — the alias for it exists only
in the un-popped context). -/
def anyKeyExpandsTo (ac : ActiveContext) (fields : List (String × Json)) (kw : String) : Bool :=
  fields.any (fun kv => match expandIri ac kv.1 true with | some e => e == kw | none => false)

def isSingleIdObject (ac : ActiveContext) (fields : List (String × Json)) : Bool :=
  match fields with
  | [(k, _)] => match expandIri ac k true with | some e => e == "@id" | none => false
  | _ => false

/-- §5.1's "colliding keywords" error, NARROWLY for `@id` only: `@id` is
single-valued, so two different keys aliasing to it cannot be
reconciled. `@type`, `@included`, and `@nest` are explicitly designed to
MERGE contributions from multiple aliased keys, so they are exempt. -/
def keywordAliasesOf (ac : ActiveContext) : List (String × Json) → List String
  | [] => []
  | (k, _) :: rest =>
    match expandIri ac k true with
    | some e => if e == "@id" then e :: keywordAliasesOf ac rest else keywordAliasesOf ac rest
    | none   => keywordAliasesOf ac rest

def hasDupString : List String → Bool
  | [] => false
  | x :: rest => rest.contains x || hasDupString rest

def hasCollidingKeywords (ac : ActiveContext) (fields : List (String × Json)) : Bool :=
  hasDupString (keywordAliasesOf ac fields)

/-! ## Ordering, duplicate merging, and the free-floating drop

Each realises a step of §5.1 that the toRdf path never OBSERVABLY needs
(a free-floating node yields no triples; duplicate expanded keys yield
the same triple set as one merged key; map-entry order washes out in an
unordered RDF graph) but that the expansion suite's JSON comparison pins
exactly. Kept for parity with the F* source. -/

def mapEntryInsert (kv : String × Json) : List (String × Json) → List (String × Json)
  | [] => [kv]
  | y :: rest => if strLt kv.1 y.1 then kv :: y :: rest else y :: mapEntryInsert kv rest

def sortMapEntries : List (String × Json) → List (String × Json)
  | [] => []
  | kv :: rest => mapEntryInsert kv (sortMapEntries rest)

/-- The main node-object loop processes members "ordered
lexicographically by key" (§5.1 step 13), and every `@nest` member (or
alias of one) is DEFERRED to after all ordinary members (step 14's
`nests` list). -/
def partitionNest (ac : ActiveContext) (fields : List (String × Json))
    : List (String × Json) × List (String × Json) :=
  let isNest (k : String) : Bool :=
    k == "@nest" || (match expandIri ac k true with | some "@nest" => true | _ => false)
  (fields.filter (fun kv => !isNest kv.1), fields.filter (fun kv => isNest kv.1))

def orderNodeFields (ac : ActiveContext) (fields : List (String × Json))
    : List (String × Json) :=
  let sorted := sortMapEntries fields
  let (others, nests) := partitionNest ac sorted
  others ++ nests

/-- Plain `@index` containers in EXPANDED form: the map key is not
dropped — every item gains `"@index": <key>` unless it already carries
its own or the key expands to `@none`. (toRdf-neutral: the dataset
conversion ignores `@index`.) -/
def addIndexToItem (k : String) (item : Json) : Json :=
  match item with
  | .object fields => if hasField "@index" fields then item
                      else .object (("@index", .string k) :: fields)
  | _ => item

def addIndexItems (k : String) (items : List Json) : List Json :=
  items.map (addIndexToItem k)

/-- Collect every later value of key `k`, and the remaining fields. -/
def collectDupKey (k : String) : List (String × Json) → List Json × List (String × Json)
  | [] => ([], [])
  | (k2, v) :: rest =>
    let (vs, others) := collectDupKey k rest
    if k2 == k then (v :: vs, others) else (vs, (k2, v) :: others)

def mergeDupValues (v : Json) : List Json → Json
  | [] => v
  | v2 :: rest =>
    let m := match v, v2 with
             | .array xs, .array ys   => Json.array (xs ++ ys)
             | .object xs, .object ys => Json.object (xs ++ ys)
             | _, _ => v
    mergeDupValues m rest

/-- Duplicate expanded keys merge into ONE entry whose values are
appended in first-occurrence order (§5.1's "add value" helper).
`@reverse` merges as an OBJECT of per-property arrays, so after the
shallow append the same reverse property appearing in both duplicates is
merged again one level down. -/
def mergeDupFields : List (String × Json) → Nat → List (String × Json)
  | fields, 0 => fields
  | [], _ => []
  | (k, v) :: rest, fuel + 1 =>
    let (vs, others) := collectDupKey k rest
    let merged := mergeDupValues v vs
    let merged1 := match merged with
                   | .object inner => if k == "@reverse" then Json.object (mergeDupFields inner fuel)
                                      else merged
                   | _ => merged
    (k, merged1) :: mergeDupFields others fuel

/-- Merge duplicate keys INSIDE each already-expanded item — the
injected index property must APPEND to an existing property of the same
IRI, not sit alongside it as a duplicate key. -/
def mergeItemFields : List Json → List Json
  | [] => []
  | .object fs :: rest => Json.object (mergeDupFields fs (Json.size (.object fs) + 8))
                          :: mergeItemFields rest
  | v :: rest => v :: mergeItemFields rest

/-- §5.1's free-floating drop (active property null or `@graph`): a
result map that is empty, carries `@value` or `@list`, or whose ONLY
entry is `@id`, becomes null. Applied to POST-EXPANSION items, so keys
are literal keywords. -/
def freeFloating (v : Json) : Bool :=
  match v with
  | .object [] => true
  | .object fields =>
    hasField "@value" fields || hasField "@list" fields ||
    (match fields with | [(k, _)] => k == "@id" | _ => false)
  | _ => false

mutual

/-- Drop free-floating entries in a list where the active property was
null or `@graph`. -/
def dropFfItems : List Json → Nat → List Json
  | items, 0 => items
  | [], _ => []
  | v :: rest, fuel + 1 =>
    let v1 := dropFfNode v fuel
    if freeFloating v1 then dropFfItems rest fuel else v1 :: dropFfItems rest fuel
termination_by _ fuel => fuel

def dropFfNode : Json → Nat → Json
  | v, 0 => v
  | .object fields, fuel + 1 => .object (dropFfFields fields fuel)
  | v, _ + 1 => v
termination_by _ fuel => fuel

/-- Items under ORDINARY property keys are walked only to find nested
`@graph` keys; they are never dropped themselves. -/
def dropFfFields : List (String × Json) → Nat → List (String × Json)
  | fields, 0 => fields
  | [], _ => []
  | (k, .array items) :: rest, fuel + 1 =>
    if k == "@graph" then (k, .array (dropFfItems items fuel)) :: dropFfFields rest fuel
    else (k, .array (dropFfWalkItems items fuel)) :: dropFfFields rest fuel
  | kv :: rest, fuel + 1 => kv :: dropFfFields rest fuel
termination_by _ fuel => fuel

def dropFfWalkItems : List Json → Nat → List Json
  | items, 0 => items
  | [], _ => []
  | v :: rest, fuel + 1 => dropFfNode v fuel :: dropFfWalkItems rest fuel
termination_by _ fuel => fuel

end

/-! ## The fuel-threaded expansion group

Result shapes, matching the F* source:
  * `Res Json` — expand this required sub-tree; an error propagates up.
  * `Res (Option Json)` — expand this property value; `ok none` means
    valid-but-empty (drop silently).
  * `Res (Option (List (String × Json)))` — expand this node object's
    ONE member; `ok none` means drop, `ok (some kvs)` means zero or more
    output fields (`@nest` merges its contents in as MULTIPLE fields).
-/

mutual

/-- §5.1, the "element is a map" branch: a node object. -/
def expandNode (loader : Loader) (ac : ActiveContext) (v : Json) (fuel : Nat) : Res Json :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match v with
    | .object fields =>
      -- Pop back to the pre-scope context if the INCOMING context is the
      -- result of a non-propagating application — UNLESS this object is a
      -- single-`@id` node reference or contains a `@value`-expanding
      -- entry (both exempt), or the one-shot suppression is set.
      let acPopped :=
        if isSingleIdObject ac fields || anyKeyExpandsTo ac fields "@value" || ac.suppressPop
        then ac else ac.pop
      let acPopped := acPopped.upd (fun c => { c with suppressPop := false })
      let (ctxVal, fields1) := extractContext fields
      match (match ctxVal with
             | none => Except.ok acPopped
             | some cv => applyContextWithPropagate loader acPopped cv true false) with
      | .error e => .error e
      | .ok ac0 =>
        match expandTypedAc loader ac0 fields1 with
        | .error e => .error e
        | .ok acTyped =>
          if hasCollidingKeywords acTyped fields1 then .error .collidingKeywords
          else
            match expandFieldsList loader acTyped ac0 (orderNodeFields acTyped fields1) fuel with
            | .error e => .error e
            | .ok outFields =>
              .ok (.object (mergeDupFields outFields (Json.size (.object outFields) + 8)))
    | _ => .error .invalidLocalContext
termination_by fuel

/-- A `@container: @type` / `@id` map's flattened value: the map KEY
supplies an implicit type/id, added by the caller AFTER this returns,
and that caller has ALREADY applied the key's own scoped context. The
ordinary pop must NOT run here — it would immediately discard the very
scope just folded in. Same body as `expandNode` minus the pop step. -/
def expandNodeFromMap (loader : Loader) (ac : ActiveContext) (v : Json) (fuel : Nat) : Res Json :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match v with
    | .object fields =>
      let ac := ac.upd (fun c => { c with suppressPop := false })
      let (ctxVal, fields1) := extractContext fields
      match (match ctxVal with
             | none => Except.ok ac
             | some cv => applyContextWithPropagate loader ac cv true false) with
      | .error e => .error e
      | .ok ac0 =>
        match expandTypedAc loader ac0 fields1 with
        | .error e => .error e
        | .ok acTyped =>
          if hasCollidingKeywords acTyped fields1 then .error .collidingKeywords
          else
            match expandFieldsList loader acTyped ac0 (orderNodeFields acTyped fields1) fuel with
            | .error e => .error e
            | .ok outFields =>
              .ok (.object (mergeDupFields outFields (Json.size (.object outFields) + 8)))
    | _ => .error .invalidLocalContext
termination_by fuel

/-- `ac0` is this node's FIXED pre-type-scope context, threaded alongside
the effective `ac` so `@type`'s own VALUES expand against the snapshot
(§5.1 expands `@type` values using "type-scoped context"), never against
the context as updated by folding this node's own type-scoped contexts. -/
def expandFieldsList (loader : Loader) (ac ac0 : ActiveContext)
    (fields : List (String × Json)) (fuel : Nat) : Res (List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match fields with
    | [] => .ok []
    | (key, value) :: rest =>
      match expandOneField loader ac ac0 key value fuel with
      | .error e => .error e
      | .ok none => expandFieldsList loader ac ac0 rest fuel
      | .ok (some outKvs) =>
        match expandFieldsList loader ac ac0 rest fuel with
        | .error e => .error e
        | .ok restOut => .ok (outKvs ++ restOut)
termination_by fuel

/-- One member of a node object. -/
def expandOneField (loader : Loader) (ac ac0 : ActiveContext) (key : String) (value : Json)
    (fuel : Nat) : Res (Option (List (String × Json))) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
  if key == "@id" then
    match value with
    | .string s =>
      -- An `@id` VALUE that is a keyword lookalike expands to null,
      -- retained literally as `{"@id": null}`. When `expandIri` cannot
      -- resolve a relative `@id` (no `@base`), RETAIN the unresolved
      -- string rather than dropping the member: dropping would mint a
      -- FRESH BLANK NODE, so the node's other fields would attach to a
      -- subject nobody references. Downstream triple filtering drops the
      -- resulting invalid-IRI triples.
      if keywordLookalike s then .ok (some [("@id", .null)])
      else
        match expandIri ac s false with
        | none     => .ok (some [("@id", .string s)])
        | some iri => .ok (some [("@id", .string iri)])
    -- Framing grammar: `"@id": [IRI...]` is a set of ids to match and
    -- `"@id": {}` is the wildcard. Each string entry resolves the same
    -- way the single-IRI case above does; the wildcard is kept as
    -- written, because matching it is the framing algorithm's job.
    | .array items =>
      if ac.cur.frameExpansion && idFrameEntriesValid items then
        .ok (some [("@id", .array (items.map (fun it =>
          match it with
          | .string s =>
              if keywordLookalike s then .null
              else match expandIri ac s false with
                   | none     => .string s
                   | some iri => .string iri
          | other => other)))])
      else .error .invalidIdValue
    | .object [] =>
      if ac.cur.frameExpansion then .ok (some [("@id", .object [])])
      else .error .invalidIdValue
    | _ => .error .invalidIdValue
  else if key == "@type" then
    -- `ac0`, not `ac`: see `expandFieldsList`'s doc comment.
    if typeEntriesAllStrings (asArray value)
    then .ok (some [("@type", .array (expandTypeValues ac0 value))])
    else .error .invalidTypeValue
  else if key == "@graph" then
    match expandGraphItems loader ac (asArray value) fuel with
    | .error e => .error e
    | .ok items => .ok (some [("@graph", .array items)])
  else if key == "@reverse" then
    match value with
    | .object rfields =>
      match expandReverseBlockFields loader ac rfields fuel with
      | .error e => .error e
      | .ok (ordEntries, revEntries) =>
        -- A term whose own reverse-ness CANCELLED the block's reversal
        -- contributes ORDINARY entries, folded alongside — not instead
        -- of — a (possibly empty) `@reverse` wrapper.
        .ok (some (ordEntries ++
          (if revEntries.isEmpty then [] else [("@reverse", .object revEntries)])))
    | _ => .error .invalidReversePropertyMap
  else if key == "@index" then
    match value with
    | .string s => .ok (some [("@index", .string s)])
    | _         => .error .invalidIndexValue
  else if key == "@included" then
    -- Unlike `@graph`'s lenient drop, a non-node-object `@included`
    -- entry is a spec error.
    match expandIncludedItems loader ac (asArray value) fuel with
    | .error e => .error e
    | .ok items => .ok (some [("@included", .array items)])
  else if key == "@nest" then
    match value with
    | .object nfields =>
      match expandFieldsList loader ac ac0 (orderNodeFields ac nfields) fuel with
      | .error e => .error e
      | .ok outs => .ok (some outs)
    | .array items =>
      match expandNestArray loader ac ac0 items fuel with
      | .error e => .error e
      | .ok outs => .ok (some outs)
    | _ => .error .invalidNestValue
  -- An ACTUAL keyword not handled above is an error; a keyword LOOKALIKE
  -- key is dropped with a warning; an at-prefixed key WITHOUT keyword
  -- form is an ordinary term key.
  -- A framing directive is a keyword LOOKALIKE to ordinary expansion,
  -- so without this branch the frame's own `@explicit` / `@embed` /
  -- ... would be dropped silently, exactly like `@ignoreMe`, and the
  -- framing algorithm would never see them. Passed through RAW: these
  -- are booleans, strings and default-node payloads, not property
  -- values with coercion rules of their own, and matching them is the
  -- framing algorithm's job. Checked on the literal spelling only,
  -- since a frame document always writes these keywords out.
  else if ac.cur.frameExpansion && isFramingKeyword key then
    .ok (some [(key, value)])
  else if actualKeyword key then .error .invalidLocalContext
  else if keywordLookalike key then .ok none
  else
    match expandIri ac key true with
    | none => .ok none
    | some propIri =>
      let termOpt := findTerm ac.terms key
      if actualKeyword propIri then
        expandAliasedField loader ac ac0 termOpt propIri value fuel
      else if keywordForm propIri then
        -- A term whose mapping RESOLVED to a keyword lookalike (only via
        -- a prefix/vocab concatenation) is dropped, like a lookalike key.
        .ok none
      else
        match termOpt with
        | some td =>
          if td.reverse then expandReverseProperty loader ac (some td) propIri value fuel
          else expandOrdinaryProperty loader ac (some td) propIri value fuel
        | none => expandOrdinaryProperty loader ac none propIri value fuel
termination_by fuel

/-- `"@nest": [ {...}, {...} ]` — every array entry's fields merge into
the enclosing node object in turn. -/
def expandNestArray (loader : Loader) (ac ac0 : ActiveContext) (items : List Json) (fuel : Nat)
    : Res (List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => .ok []
    | .object nfields :: rest =>
      match expandFieldsList loader ac ac0 (orderNodeFields ac nfields) fuel with
      | .error e => .error e
      | .ok outs =>
        match expandNestArray loader ac ac0 rest fuel with
        | .error e => .error e
        | .ok restOuts => .ok (outs ++ restOuts)
    | _ => .error .invalidNestValue
termination_by fuel

/-- A property whose key already resolved to an absolute IRI, whose term
definition supplies `@type` coercion / `@language` override /
`@container` mapping / a property-scoped `@context`. -/
def expandOrdinaryProperty (loader : Loader) (ac : ActiveContext) (termOpt : Option TermDef)
    (propIri : String) (value : Json) (fuel : Nat) : Res (Option (List (String × Json))) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match applyPropertyScopedContext loader ac termOpt with
    | .error e => .error e
    | .ok acEff =>
      let isList := match termOpt with | some td => td.container.isList | none => false
      -- A value that is ALREADY an explicit list object must not be
      -- wrapped in a SECOND, outer list — that produces a length-1 list
      -- whose sole item is the inner list object.
      let alreadyListObj := match value with
                            | .object fs => hasAliasedField acEff "@list" fs
                            | _ => false
      -- §5.1 "If expanded value is null, continue with the next entry"
      -- (before list-container wrapping): a JSON null, or a SINGLE
      -- non-array, non-`@set`, non-container-map object that expanded
      -- away entirely, drops the whole KEY. An array (or explicit `@set`
      -- / container map) whose items all dropped keeps an EMPTY array.
      let isMapCk := match termOpt with
                     | some td => match td.container with
                                  | .index | .language | .id | .type
                                  | .graphId | .graphIndex => true
                                  | _ => false
                     | none => false
      let valueNullish := match value with
                          | .null => true
                          | .object fs => !hasAliasedField acEff "@set" fs && !isMapCk
                          | _ => false
      match expandPropertyItems loader acEff termOpt value fuel with
      | .error e => .error e
      | .ok items =>
        if items.isEmpty && valueNullish then .ok none
        else if isList && !alreadyListObj then
          .ok (some [(propIri, .array [.object [("@list", .array items)]])])
        else .ok (some [(propIri, .array items)])
termination_by fuel

/-- A term defined with `@reverse` and used FORWARD: folds its values
into a single-predicate `@reverse` map entry rather than a plain
property. -/
def expandReverseProperty (loader : Loader) (ac : ActiveContext) (termOpt : Option TermDef)
    (propIri : String) (value : Json) (fuel : Nat) : Res (Option (List (String × Json))) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match applyPropertyScopedContext loader ac termOpt with
    | .error e => .error e
    | .ok acEff =>
      let valueNullish := match value with
                          | .null => true
                          | .object fs => !hasAliasedField acEff "@set" fs
                          | _ => false
      match expandPropertyItems loader acEff termOpt value fuel with
      | .error e => .error e
      | .ok items =>
        if items.isEmpty && valueNullish then .ok none
        else if itemsAllNodeLike items then
          .ok (some [("@reverse", .object [(propIri, .array items)])])
        else .error .invalidReversePropertyValue
termination_by fuel

/-- An inline `"@reverse": {...}` member. Every key inside is normally an
ORDINARY (forward) term whose meaning is reversed purely by appearing in
this block — EXCEPT a key whose own term definition is ITSELF a
`@reverse` property, where the two reversals cancel. Returns (ordinary
entries, reverse-bucket entries) so the caller can fold the cancelled
ones back into the node's plain property list. -/
def expandReverseBlockFields (loader : Loader) (ac : ActiveContext)
    (fields : List (String × Json)) (fuel : Nat)
    : Res (List (String × Json) × List (String × Json)) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match fields with
    | [] => .ok ([], [])
    | (key, value) :: rest =>
      if isKeywordChar key then .error .invalidReversePropertyMap
      -- A key with no term definition and no colon/`@vocab` fallback is
      -- silently SKIPPED, not a parse failure.
      else
        match expandIri ac key true with
        | none => expandReverseBlockFields loader ac rest fuel
        | some propIri =>
          if isKeywordChar propIri then .error .invalidReversePropertyMap
          else
            let termOpt := findTerm ac.terms key
            match expandPropertyItems loader ac termOpt value fuel with
            | .error e => .error e
            | .ok items =>
              if !itemsAllNodeLike items then .error .invalidReversePropertyValue
              else
                match expandReverseBlockFields loader ac rest fuel with
                | .error e => .error e
                | .ok (ordRest, revRest) =>
                  let isRevTerm := match termOpt with | some td => td.reverse | none => false
                  if isRevTerm then .ok ((propIri, .array items) :: ordRest, revRest)
                  else .ok (ordRest, (propIri, .array items) :: revRest)
termination_by fuel

/-- The item list for one property's value, honouring the term's
container mapping. Map-shaped containers apply ONLY when the actual
value is a JSON object; a term whose value is a plain array falls back to
ordinary array processing. `@list` containers are handled by the caller,
not here — this always returns the flat item list. -/
def expandPropertyItems (loader : Loader) (ac : ActiveContext) (termOpt : Option TermDef)
    (value : Json) (fuel : Nat) : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    let typeMap := match termOpt with | some td => td.typeMapping | none => none
    let langOvr := match termOpt with | some td => td.language | none => none
    let dirOvr  := match termOpt with | some td => td.direction | none => none
    let idxProp := match termOpt with | some td => td.index | none => none
    let ck      := match termOpt with | some td => td.container | none => ContainerKind.none
    -- A term coerced `"@type": "@json"` turns its ENTIRE raw value —
    -- even a JSON array — into ONE value object carrying the value
    -- VERBATIM (§5.2's `@json` case, which happens BEFORE the ordinary
    -- array-flattening rule would split it).
    if typeMap == some "@json" then
      .ok [.object [("@value", value), ("@type", .string "@json")]]
    else
      match ck, value with
      | .index, .object entries0 =>
        let entries := sortMapEntries entries0
        match idxProp with
        | some name => expandPropertyIndexMap loader ac name typeMap langOvr dirOvr entries fuel
        | none      => expandPlainIndexMap loader ac typeMap langOvr dirOvr entries fuel
      | .language, .object entries0 =>
        let entries := sortMapEntries entries0
        -- The term's own `@direction` override wins over the context
        -- default.
        let effDir := match dirOvr with | some d => d | none => ac.direction
        if languageMapValid entries then .ok (expandLanguageMap ac effDir entries)
        else .error .invalidLanguageMapValue
      | .id, .object entries => expandIdMap loader ac (sortMapEntries entries) fuel
      | .type, .object entries => expandTypeMap loader ac typeMap (sortMapEntries entries) fuel
      | .graph, _ => .ok (expandGraphContainerItemsPlain loader ac (asArray value) fuel)
      | .graphIndex, .object entries0 =>
        let entries := sortMapEntries entries0
        match idxProp with
        | some name => expandGraphIndexMap loader ac name entries fuel
        | none      => .ok (expandGraphIndexKwMap loader ac entries fuel)
      | .graphIndex, _ => .ok (expandGraphContainerItems loader ac (asArray value) fuel)
      | .graphId, .object entries => .ok (expandGraphIdMap loader ac (sortMapEntries entries) fuel)
      | .graphId, _ => .ok (expandGraphContainerItems loader ac (asArray value) fuel)
      | _, _ =>
        -- This arm matches only `.list` or `.none`. `inList` is exactly
        -- "am I a `@list`-mapped property": whether a bare array nested
        -- one level down becomes ANOTHER list-of-lists item, or splices
        -- transparently.
        expandProperty loader ac typeMap langOvr dirOvr ck.isList (asArray value) fuel
termination_by fuel

/-- Resolve a property-valued index's map KEY into (the index property's
IRI, the key coerced exactly as an ordinary use of that property would
coerce a bare string — the context may define it with its own
`"@type": "@vocab"`, which must turn the key into a node reference). -/
def indexKeyField (loader : Loader) (ac : ActiveContext) (indexName k : String) (fuel : Nat)
    : Res (String × Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match expandIri ac indexName true with
    | none => .error .invalidIndexValue
    | some indexIri =>
      if isKeywordChar indexIri then .error .invalidIndexValue
      else
        let termOpt2 := findTerm ac.terms indexName
        let typeMap2 := match termOpt2 with | some td => td.typeMapping | none => none
        let langOvr2 := match termOpt2 with | some td => td.language | none => none
        let dirOvr2  := match termOpt2 with | some td => td.direction | none => none
        match expandItem loader ac typeMap2 langOvr2 dirOvr2 false (.string k) fuel with
        | .error e => .error e
        | .ok none => .error .invalidIndexValue
        | .ok (some kv) => .ok (indexIri, kv)
termination_by fuel

/-- `@index` containers with a property-valued index: each entry's key
is kept and injected as an extra property onto every item that entry's
value expands to — unless the key is `@none`. -/
def expandPropertyIndexMap (loader : Loader) (ac : ActiveContext) (indexName : String)
    (typeMap : Option String) (langOvr dirOvr : Option (Option String))
    (entries : List (String × Json)) (fuel : Nat) : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => .ok []
    | (k, v) :: rest =>
      match expandProperty loader ac typeMap langOvr dirOvr false (asArray v) fuel with
      | .error e => .error e
      | .ok items =>
        match expandPropertyIndexMap loader ac indexName typeMap langOvr dirOvr rest fuel with
        | .error e => .error e
        | .ok restOut =>
          if k == "@none" then .ok (items ++ restOut)
          else
            match indexKeyField loader ac indexName k fuel with
            | .error e => .error e
            | .ok (indexIri, keyVal) =>
              match injectIndexItems indexIri keyVal items with
              | .error e => .error e
              | .ok items1 => .ok (mergeItemFields items1 ++ restOut)
termination_by fuel

/-- Plain `@index` containers: each entry's items gain `"@index": <key>`
unless the key expands to `@none` or the item carries its own. -/
def expandPlainIndexMap (loader : Loader) (ac : ActiveContext) (typeMap : Option String)
    (langOvr dirOvr : Option (Option String)) (entries : List (String × Json)) (fuel : Nat)
    : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => .ok []
    | (k, v) :: rest =>
      match expandProperty loader ac typeMap langOvr dirOvr false (asArray v) fuel with
      | .error e => .error e
      | .ok items =>
        let isNone := (k == "@none") ||
          (match expandIri ac k true with | some "@none" => true | _ => false)
        let items1 := if isNone then items else addIndexItems k items
        match expandPlainIndexMap loader ac typeMap langOvr dirOvr rest fuel with
        | .error e => .error e
        | .ok restOut => .ok (items1 ++ restOut)
termination_by fuel

/-- Plain `@graph`+`@index` containers: each entry's values wrap as
graph objects, and the WRAPPER gains `"@index": <key>` unless the key
expands to `@none`. -/
def expandGraphIndexKwMap (loader : Loader) (ac : ActiveContext)
    (entries : List (String × Json)) (fuel : Nat) : List Json :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match entries with
    | [] => []
    | (k, v) :: rest =>
      let items := expandGraphContainerItems loader ac (asArray v) fuel
      let isNone := (k == "@none") ||
        (match expandIri ac k true with | some "@none" => true | _ => false)
      let items1 := if isNone then items else addIndexItems k items
      items1 ++ expandGraphIndexKwMap loader ac rest fuel
termination_by fuel

/-- `@graph`+`@index` with a property-valued index: the index property
is injected onto each WRAPPER object (the graph object itself, which is
what carries the graph's own properties in the enclosing graph). -/
def expandGraphIndexMap (loader : Loader) (ac : ActiveContext) (indexName : String)
    (entries : List (String × Json)) (fuel : Nat) : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => .ok []
    | (k, v) :: rest =>
      let items := expandGraphContainerItems loader ac (asArray v) fuel
      match expandGraphIndexMap loader ac indexName rest fuel with
      | .error e => .error e
      | .ok restOut =>
        if k == "@none" then .ok (items ++ restOut)
        else
          match indexKeyField loader ac indexName k fuel with
          | .error e => .error e
          | .ok (indexIri, keyVal) =>
            match injectIndexItems indexIri keyVal items with
            | .error e => .error e
            | .ok items1 => .ok (items1 ++ restOut)
termination_by fuel

/-- `@id` containers: each entry's value expands as an ordinary item,
then the map key becomes its `@id` unless the key is `@none` or the item
already has one. §5.1's Container Mapping step first pops `ac` back to
its own previous (undoing whatever non-propagating scope is in effect
over this container, exactly like entering any new node), THEN applies
the map key's own term-scoped context on top of that popped base, and
only then expands the value — WITHOUT popping a second time. The key
itself is still looked up in the UNPOPPED term table. -/
def expandIdMap (loader : Loader) (ac : ActiveContext) (entries : List (String × Json))
    (fuel : Nat) : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => .ok []
    | (k, v) :: rest =>
      let acPopped := ac.pop
      match applyPropertyScopedContext loader acPopped (findTerm ac.terms k) with
      | .error e => .error e
      | .ok acForValue =>
        match expandItem loader acForValue none none none true v fuel with
        | .error e => .error e
        | .ok none => expandIdMap loader ac rest fuel
        | .ok (some item) =>
          let item1 := match mapKeyIri ac k false with
                       | none => item
                       | some iri => setIdIfAbsent iri item
          match expandIdMap loader ac rest fuel with
          | .error e => .error e
          | .ok restOut => .ok (item1 :: restOut)
termination_by fuel

/-- `@type` containers: each entry's value expands with `@id` coercion
(§4.2's `@container: @type` step sets an undefined type mapping to
`@id`; an EXPLICIT `"@type": "@vocab"` on the map's own term is still
honoured), then the map key is added as an extra `@type` unless it is
`@none`. Same pop-then-scope discipline as `expandIdMap`. -/
def expandTypeMap (loader : Loader) (ac : ActiveContext) (typeMap : Option String)
    (entries : List (String × Json)) (fuel : Nat) : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match entries with
    | [] => .ok []
    | (k, v) :: rest =>
      let acPopped := ac.pop
      match applyPropertyScopedContext loader acPopped (findTerm ac.terms k) with
      | .error e => .error e
      | .ok acForValue =>
        let mapValueType := typeMap.getD "@id"
        match expandItem loader acForValue (some mapValueType) none none true v fuel with
        | .error e => .error e
        | .ok none => expandTypeMap loader ac typeMap rest fuel
        | .ok (some item) =>
          let item1 := match mapKeyIri ac k true with
                       | none => item
                       | some kiri => addTypeToItem kiri item
          match expandTypeMap loader ac typeMap rest fuel with
          | .error e => .error e
          | .ok restOut => .ok (item1 :: restOut)
termination_by fuel

/-- Graph containers: each value item expands as an ordinary NODE object
(a graph's contents are always nodes), wrapped in a fresh `@id`-less
`{"@graph": [<node>]}`. Non-conforming entries are dropped.

This CONDITIONAL variant ("skip the wrap if the node already carries its
own `@graph`") is for `@graph`+`@id` / `@graph`+`@index` ONLY: §5.1's
Container Mapping `@graph` step reads "if the expanded item is not
already a graph object, wrap it in one" only for the branch that also
includes `@id` or `@index`. -/
def expandGraphContainerItems (loader : Loader) (ac : ActiveContext) (items : List Json)
    (fuel : Nat) : List Json :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match items with
    | [] => []
    | v :: rest =>
      match expandNode loader ac v fuel with
      | .error _ => expandGraphContainerItems loader ac rest fuel
      | .ok nodeObj => ensureGraphObject nodeObj :: expandGraphContainerItems loader ac rest fuel
termination_by fuel

/-- Plain `"@container": "@graph"` (no `@id`/`@index`): every item is
wrapped in a FRESH graph object UNCONDITIONALLY, even when the node
already carries its own `@graph` member — §5.1's Container Mapping step
for this case omits the other branch's "not already a graph object"
guard, so a user-supplied graph object gets wrapped a SECOND time. The
doubled wrap produces an intermediate node whose only member is
`@graph`, which the RDF conversion recurses through generically. -/
def expandGraphContainerItemsPlain (loader : Loader) (ac : ActiveContext) (items : List Json)
    (fuel : Nat) : List Json :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match items with
    | [] => []
    | v :: rest =>
      match expandNode loader ac v fuel with
      | .error _ => expandGraphContainerItemsPlain loader ac rest fuel
      | .ok nodeObj => Json.object [("@graph", .array [nodeObj])]
                       :: expandGraphContainerItemsPlain loader ac rest fuel
termination_by fuel

/-- `@graph`+`@id` containers: the map key becomes the WRAPPER's `@id`
(the graph's own name), not the inner node's — a graph name and its
content's subject are independent. -/
def expandGraphIdMap (loader : Loader) (ac : ActiveContext) (entries : List (String × Json))
    (fuel : Nat) : List Json :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match entries with
    | [] => []
    | (k, v) :: rest =>
      expandGraphIdMapOne loader ac k (asArray v) fuel ++ expandGraphIdMap loader ac rest fuel
termination_by fuel

def expandGraphIdMapOne (loader : Loader) (ac : ActiveContext) (k : String) (items : List Json)
    (fuel : Nat) : List Json :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match items with
    | [] => []
    | v :: rest =>
      match expandNode loader ac v fuel with
      | .error _ => expandGraphIdMapOne loader ac k rest fuel
      | .ok nodeObj =>
        let graphObj := ensureGraphObject nodeObj
        let wrapped := match mapKeyIri ac k false with
                       | none => graphObj
                       | some iri => setIdIfAbsent iri graphObj
        wrapped :: expandGraphIdMapOne loader ac k rest fuel
termination_by fuel

/-- A term whose IRI mapping is itself a keyword applies to its value
exactly as that keyword would. The ALIASING term's own property-scoped
`@context` is applied FIRST. `ac0` passes through unchanged so a keyword
alias of `@type` gets the same snapshot-based value expansion as a
literal `@type` key. -/
def expandAliasedField (loader : Loader) (ac ac0 : ActiveContext) (termOpt : Option TermDef)
    (canonKey : String) (value : Json) (fuel : Nat) : Res (Option (List (String × Json))) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match applyPropertyScopedContext loader ac termOpt with
    | .error e => .error e
    | .ok acEff => expandOneField loader acEff ac0 canonKey value fuel
termination_by fuel

/-- The array of raw values for one property. `inList` is true iff we are
ALREADY expanding the contents of a `@list`. -/
def expandProperty (loader : Loader) (ac : ActiveContext) (typeMap : Option String)
    (langOvr dirOvr : Option (Option String)) (inList : Bool) (items : List Json) (fuel : Nat)
    : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => .ok []
    | v :: rest =>
      -- An explicit set object is TRANSPARENT: its contents splice
      -- directly into this property's item list, recursively.
      let setContents := match v with
        | .object fields => (findAliasedField ac "@set" fields).map Prod.snd
        | _ => none
      match setContents with
      | some setVal =>
        match expandProperty loader ac typeMap langOvr dirOvr inList (asArray setVal) fuel with
        | .error e => .error e
        | .ok setItems =>
          match expandProperty loader ac typeMap langOvr dirOvr inList rest fuel with
          | .error e => .error e
          | .ok restOut => .ok (setItems ++ restOut)
      | none =>
        match v with
        | .array inner =>
          -- A bare array item found OUTSIDE a `@list` context flattens
          -- transparently, exactly like an explicit `@set`: an empty
          -- nested array must contribute ZERO items, not a spurious
          -- `rdf:nil`. Only `inList` treats it as a genuine nested list —
          -- which under JSON-LD 1.0 is the "list of lists" error.
          if !inList then
            match expandProperty loader ac typeMap langOvr dirOvr false inner fuel with
            | .error e => .error e
            | .ok innerOut =>
              match expandProperty loader ac typeMap langOvr dirOvr inList rest fuel with
              | .error e => .error e
              | .ok restOut => .ok (innerOut ++ restOut)
          else if ac.mode10 then .error .listOfLists
          else
            match expandItem loader ac typeMap langOvr dirOvr false v fuel with
            | .error e => .error e
            | .ok none => expandProperty loader ac typeMap langOvr dirOvr inList rest fuel
            | .ok (some one) =>
              match expandProperty loader ac typeMap langOvr dirOvr inList rest fuel with
              | .error e => .error e
              | .ok restOut => .ok (one :: restOut)
        | _ =>
          match expandItem loader ac typeMap langOvr dirOvr false v fuel with
          | .error e => .error e
          | .ok none => expandProperty loader ac typeMap langOvr dirOvr inList rest fuel
          | .ok (some one) =>
            -- An explicit `{"@list": ...}` item nested in another `@list`
            -- is the same JSON-LD 1.0 "list of lists" error the bare-array
            -- short-circuit above catches for the raw-array shape.
            if inList && ac.mode10 && (match one with
                                       | .object fs => hasField "@list" fs
                                       | _ => false) then .error .listOfLists
            else
              match expandProperty loader ac typeMap langOvr dirOvr inList rest fuel with
              | .error e => .error e
              | .ok restOut => .ok (one :: restOut)
termination_by fuel

/-- One property value: an explicit value object, a list object, a nested
node object, a node reference, or a bare scalar coerced per
`typeMap` / `langOvr` / `dirOvr`. JSON null produces nothing.

`fromMap` is true only when this item is one VALUE of a
`@container: @type`/`@id` map, meaning the node-object fallback must use
`expandNodeFromMap` (no pop-back). -/
def expandItem (loader : Loader) (ac : ActiveContext) (typeMap : Option String)
    (langOvr dirOvr : Option (Option String)) (fromMap : Bool) (v : Json) (fuel : Nat)
    : Res (Option Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match v with
    | .null => .ok none
    | .object fields =>
      -- Dispatch on each key's ALIAS-RESOLVED keyword, not its literal
      -- spelling: a scoped context may rename any keyword, and that alias
      -- is only visible in THIS context.
      if hasAliasedField ac "@value" fields then
        -- `{"@value": null}` is syntactically a value object but carries
        -- no information: drop it silently, exactly like a bare JSON null
        -- item. EXCEPTION: under `"@type": "@json"` the JSON value null
        -- IS the payload — the `rdf:JSON` literal `null`.
        let jsonTyped := match findAliasedField ac "@type" fields with
                         | some (_, .string t) => expandIri ac t true == some "@json"
                         | _ => false
        match findAliasedField ac "@value" fields with
        | some (_, .null) =>
          if jsonTyped then
            match expandValueObject ac fields with
            | .error e => .error e
            | .ok vo => .ok (some vo)
          else if valueObjectKeysValid ac fields then .ok none
          else .error .invalidValueObject
        | _ =>
          match expandValueObject ac fields with
          | .error e => .error e
          | .ok vo => .ok (some vo)
      else if hasAliasedField ac "@list" fields then
        if !listObjectKeysValid ac fields then .error .invalidSetOrListObject
        else
          match findAliasedField ac "@list" fields with
          | none => .error .invalidSetOrListObject
          | some (_, lstVal) =>
            match expandProperty loader ac typeMap langOvr dirOvr true (asArray lstVal) fuel with
            | .error e => .error e
            | .ok items =>
              -- An `@index` sibling on a list object is RETAINED in the
              -- expanded list object (§5.1: the value of `@index` "is
              -- retained"); the dataset conversion ignores it.
              let idxFields := match findAliasedField ac "@index" fields with
                               | some (_, .string ix) => [("@index", Json.string ix)]
                               | _ => []
              .ok (some (.object (("@list", .array items) :: idxFields)))
      else if hasAliasedField ac "@reverse" fields then .error .invalidReversePropertyValue
      else if hasAliasedField ac "@language" fields then
        -- An object carrying `@language` but NO `@value` expands to a
        -- value object whose only member is `@language`, which §5.1 drops
        -- entirely — `@language` cannot appear on a node object.
        .ok none
      else
        match (if fromMap then expandNodeFromMap loader ac v fuel else expandNode loader ac v fuel) with
        | .error e => .error e
        | .ok nodeObj => .ok (some nodeObj)
    | .string s =>
      match typeMap with
      | none =>
        let effLang := match langOvr with | some l => l | none => ac.language
        let effDir  := match dirOvr with | some d => d | none => ac.direction
        let baseFields := ("@value", Json.string s) ::
          (match effLang with | some lg => [("@language", Json.string lg)] | none => [])
        match effDir with
        | some d => .ok (some (.object (baseFields ++ [("@direction", .string d)])))
        | none   => .ok (some (.object baseFields))
      | some dt =>
        if dt == "@id" then
          -- An unresolvable `@id` coercion must RETAIN a placeholder
          -- rather than dropping the item: dropping it splices the item
          -- OUT of the array, silently SHORTENING a `@list` by one cell.
          -- Downstream drops the invalid `rdf:first` while still emitting
          -- the cell's `rdf:rest` link.
          match expandIri ac s false with
          | none     => .ok (some (.object [("@id", .string s)]))
          | some iri => .ok (some (.object [("@id", .string iri)]))
        else if dt == "@vocab" then
          -- `@vocab` coercion falls back document-relative (§5.2 pairs
          -- `vocab` with `documentRelative`).
          match expandIri ac s true with
          | some iri => .ok (some (.object [("@id", .string iri)]))
          | none =>
            match expandIri ac s false with
            | some iri => .ok (some (.object [("@id", .string iri)]))
            | none     => .ok none
        else if dt == "@none" then
          -- `"@type": "@none"` suppresses this term's coercion AND the
          -- ordinary language/direction inheritance: a term opting out of
          -- coercion opts out of default lang/dir too.
          .ok (some (.object [("@value", .string s)]))
        else .ok (some (.object [("@value", .string s), ("@type", .string dt)]))
    | .bool _ => .ok (some (wrapScalar typeMap v))
    | .number _ => .ok (some (wrapScalar typeMap v))
    | .array items =>
      -- JSON-LD 1.1's "Lists of Lists": an array item nested inside a
      -- `@list`-coerced value is expanded like a list object's contents
      -- and wrapped as a NESTED list object.
      match expandProperty loader ac typeMap langOvr dirOvr true items fuel with
      | .error e => .error e
      | .ok outItems => .ok (some (.object [("@list", .array outItems)]))
termination_by fuel

/-- The contents of a `@graph` array: each entry is expanded as a node
object; a malformed entry is DROPPED rather than failing the whole
graph. Free-floating entries (a bare scalar, a value object, a list
object — none can produce triples with no enclosing property) are
dropped; a `@set` object at this level is transparent. -/
def expandGraphItems (loader : Loader) (ac : ActiveContext) (items : List Json) (fuel : Nat)
    : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => .ok []
    | .object fields :: rest =>
      if hasAliasedField ac "@value" fields || hasAliasedField ac "@list" fields then
        expandGraphItems loader ac rest fuel
      else
        match fields.find? (fun kv => kv.1 == "@set") with
        | some (_, setVal) =>
          match expandGraphItems loader ac (asArray setVal) fuel with
          | .error e => .error e
          | .ok a =>
            match expandGraphItems loader ac rest fuel with
            | .error e => .error e
            | .ok b => .ok (a ++ b)
        | none =>
          match expandNode loader ac (.object fields) fuel with
          | .error _ => expandGraphItems loader ac rest fuel
          | .ok nodeObj =>
            match expandGraphItems loader ac rest fuel with
            | .error e => .error e
            | .ok restOut => .ok (nodeObj :: restOut)
    | _ :: rest => expandGraphItems loader ac rest fuel
termination_by fuel

/-- `@included` contents: STRICT, unlike `@graph`. Every entry must be a
node object (§5.1's "invalid @included value"), and a node-object entry
that fails to expand fails the whole document. -/
def expandIncludedItems (loader : Loader) (ac : ActiveContext) (items : List Json) (fuel : Nat)
    : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => .ok []
    | .object fields :: rest =>
      if hasAliasedField ac "@value" fields || hasAliasedField ac "@list" fields then
        .error .invalidIncludedValue
      else
        match expandNode loader ac (.object fields) fuel with
        | .error e => .error e
        | .ok nodeObj =>
          match expandIncludedItems loader ac rest fuel with
          | .error e => .error e
          | .ok restOut => .ok (nodeObj :: restOut)
    | _ => .error .invalidIncludedValue
termination_by fuel

/-- The TOP-LEVEL document array is STRICT, unlike a nested `@graph`
member's contents: a top-level entry whose own context processing fails
(an unloadable remote context, an `@import` cycle, …) must fail the
WHOLE document. Silently dropping it would turn a negative test
expecting "loading remote context failed" into a spuriously-passing
EMPTY dataset. Free-floating value/list objects still drop. -/
def expandTopItems (loader : Loader) (ac : ActiveContext) (items : List Json) (fuel : Nat)
    : Res (List Json) :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => .ok []
    | .object fields :: rest =>
      if hasAliasedField ac "@value" fields || hasAliasedField ac "@list" fields then
        expandTopItems loader ac rest fuel
      else
        match expandNode loader ac (.object fields) fuel with
        | .error e => .error e
        | .ok nodeObj =>
          match expandTopItems loader ac rest fuel with
          | .error e => .error e
          | .ok restOut => .ok (nodeObj :: restOut)
    -- A bare scalar at the top level is free-floating: dropped.
    | _ :: rest => expandTopItems loader ac rest fuel
termination_by fuel

end

/-! ## Public API -/

/-- §5.1 Expansion: expand a parsed document against an active context,
producing an EXPANDED-FORM tree suitable for `JSONLD.ToRdf`.

`docUrl` and `originalBase` are seeded from `base` HERE, at the single
entry point, before this document's own inline `@context` has had a
chance to rewrite `base`. Only when unset, so a caller that pre-applied
an `expandContext` keeps whatever it populated. -/
def expand (loader : Loader) (ac : ActiveContext) (doc : Json) : Res Json :=
  let ac := if ac.docUrl.isNone && ac.originalBase.isNone
            then ac.upd (fun c => { c with docUrl := c.base, originalBase := c.base })
            else ac
  let fuel := 4 * Json.size doc + 48
  match doc with
  | .object fields0 =>
    -- A top-level value or list object is free-floating (a value object
    -- cannot carry `@context`, so no extraction is needed first).
    if hasField "@value" fields0 || hasField "@list" fields0 then .ok (.array [])
    else
      match expandNode loader ac doc fuel with
      | .error e => .error e
      | .ok (.object []) => .ok (.array [])
      | .ok (.object fields1) =>
        -- Free-floating drop at the top level and in every `@graph` value
        -- array. Fuel is sized from the INPUT document and expansion can
        -- grow the tree by a small constant factor, so over-provision the
        -- walk: exhaustion degrades to "no drop", never to failure.
        if onlyGraphKeys fields1
        then .ok (.array (dropFfItems (collectGraphValues fields1) (4 * fuel)))
        else .ok (.array (dropFfItems [.object fields1] (4 * fuel)))
      | .ok nodeObj => .ok (.array (dropFfItems [nodeObj] (4 * fuel)))
  | .array items =>
    match expandTopItems loader ac items fuel with
    | .error e => .error e
    | .ok outs => .ok (.array (dropFfItems outs (4 * fuel)))
  | _ => .error .notJsonLd

end L4Factoidal.JSONLD
