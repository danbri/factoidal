/-
L4Factoidal.JSONLD.Context — JSON-LD 1.1 Context Processing.

Port of `formal/fstar/JSONLD.Context.fst`.

Specifications implemented (JSON-LD 1.1 API,
https://www.w3.org/TR/json-ld11-api/):
  * §4.1 Context Processing Algorithm — `contextProcess`;
  * §4.2 Create Term Definition Algorithm — `processTermDefObj` and
    `termObjFields`;
  * §5.2.2 IRI Expansion Algorithm — `expandIriGen` / `expandIri`;
  * the term-definition `@protected` / `@propagate` / `@version` rules
    (§4.1.5, §4.1.6, §4.1.8) and the `@import` merge (§4.1);
  * JSON-LD 1.1 §9 Syntax Tokens and Keywords (`actualKeyword`).

Two departures from the F* original, both deliberate:

1. **The loader is a parameter, not an ambient call.**
   `JSONLD.Loader.fst`'s `assume val jsonld_load_document` becomes the
   `loader : Loader` argument threaded through this module. See
   `L4Factoidal/JSONLD/Loader.lean`.

2. **Errors are values carrying the spec's error code.** The F* source
   returns `option`, so every failure is indistinguishable. Here every
   failure is an `Except JsonLdError`, and `JsonLdError.code` gives the
   exact string the W3C manifest's `expectErrorCode` uses ("protected
   term redefinition", "cyclic IRI mapping", ...). Nothing else about
   the control flow changes: the F* `None` sites map one-to-one onto
   `.error` sites here.

The active context is represented as a CURRENT record plus a STACK of
enclosing ones, rather than the F* record's self-referential
`ac_previous : option active_context` field (Lean structures are not
recursive). `pop` / `setPrev` / `clearPrev` below reproduce that
field's three uses exactly.
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Parser
import L4Factoidal.RDF.Core
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.JSONLD.Loader

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## Errors — JSON-LD 1.1 API §5 error codes, as values

Every constructor is one of the spec's named error conditions; `code`
returns the exact string the W3C test manifests put in
`expectErrorCode`. -/

inductive JsonLdError where
  | invalidLocalContext
  | invalidContextEntry
  | invalidContextNullification
  | keywordRedefinition
  | protectedTermRedefinition
  | cyclicIriMapping
  | invalidTermDefinition
  | invalidIriMapping
  | invalidTypeMapping
  | invalidVocabMapping
  | invalidBaseIri
  | invalidBaseDirection
  | invalidDefaultLanguage
  | invalidKeywordAlias
  | invalidContainerMapping
  | invalidReverseProperty
  | invalidReversePropertyMap
  | invalidReversePropertyValue
  | invalidPrefixValue
  | invalidPropagateValue
  | invalidImportValue
  | invalidVersionValue
  | processingModeConflict
  | invalidRemoteContext
  | loadingRemoteContextFailed
  | recursiveContextInclusion
  | contextOverflow
  | invalidScopedContext
  | invalidNestValue
  | invalidIdValue
  | invalidIndexValue
  | invalidTypeValue
  | invalidValueObject
  | invalidValueObjectValue
  | invalidTypedValue
  | invalidLanguageTaggedString
  | invalidLanguageTaggedValue
  | invalidLanguageMapping
  | invalidLanguageMapValue
  | invalidSetOrListObject
  | invalidIncludedValue
  | collidingKeywords
  | listOfLists
  | invalidJsonLiteral
  | notJsonLd
  deriving DecidableEq, Repr

namespace JsonLdError

/-- The manifest-visible error string (JSON-LD 1.1 API §5). -/
def code : JsonLdError → String
  | invalidLocalContext         => "invalid local context"
  | invalidContextEntry         => "invalid context entry"
  | invalidContextNullification => "invalid context nullification"
  | keywordRedefinition         => "keyword redefinition"
  | protectedTermRedefinition   => "protected term redefinition"
  | cyclicIriMapping            => "cyclic IRI mapping"
  | invalidTermDefinition       => "invalid term definition"
  | invalidIriMapping           => "invalid IRI mapping"
  | invalidTypeMapping          => "invalid type mapping"
  | invalidVocabMapping         => "invalid vocab mapping"
  | invalidBaseIri              => "invalid base IRI"
  | invalidBaseDirection        => "invalid base direction"
  | invalidDefaultLanguage      => "invalid default language"
  | invalidKeywordAlias         => "invalid keyword alias"
  | invalidContainerMapping     => "invalid container mapping"
  | invalidReverseProperty      => "invalid reverse property"
  | invalidReversePropertyMap   => "invalid reverse property map"
  | invalidReversePropertyValue => "invalid reverse property value"
  | invalidPrefixValue          => "invalid @prefix value"
  | invalidPropagateValue       => "invalid @propagate value"
  | invalidImportValue          => "invalid @import value"
  | invalidVersionValue         => "invalid @version value"
  | processingModeConflict      => "processing mode conflict"
  | invalidRemoteContext        => "invalid remote context"
  | loadingRemoteContextFailed  => "loading remote context failed"
  | recursiveContextInclusion   => "recursive context inclusion"
  | contextOverflow             => "context overflow"
  | invalidScopedContext        => "invalid scoped context"
  | invalidNestValue            => "invalid @nest value"
  | invalidIdValue              => "invalid @id value"
  | invalidIndexValue           => "invalid @index value"
  | invalidTypeValue            => "invalid type value"
  | invalidValueObject          => "invalid value object"
  | invalidValueObjectValue     => "invalid value object value"
  | invalidTypedValue           => "invalid typed value"
  | invalidLanguageTaggedString => "invalid language-tagged string"
  | invalidLanguageTaggedValue  => "invalid language-tagged value"
  | invalidLanguageMapping      => "invalid language mapping"
  | invalidLanguageMapValue     => "invalid language map value"
  | invalidSetOrListObject      => "invalid set or list object"
  | invalidIncludedValue        => "invalid @included value"
  | collidingKeywords           => "colliding keywords"
  | listOfLists                 => "list of lists"
  | invalidJsonLiteral          => "invalid JSON literal"
  | notJsonLd                   => "not JSON-LD"

instance : ToString JsonLdError := ⟨code⟩

end JsonLdError

/-- Result of a fallible JSON-LD step. -/
abbrev Res (α : Type) := Except JsonLdError α

/-! ## String helpers

The F* source indexes UTF-8 BYTES (`fs_byte_length` / `jbyte_at` /
`fs_byte_sub`). Every byte it ever tests for is ASCII (`:` `/` `@` `_`
`#` `.`), and splitting a UTF-8 string at an ASCII position gives the
same substring whether the index counts bytes or code points, so this
port indexes code points (`String` is `List Char` in Lean) with no
change in behaviour. -/

/-- Length in code points. -/
def slen (s : String) : Nat := s.toList.length

/-- Character at a position, or `'\x00'` past the end — the F* source
reads `jbyte_at` past the end in two guards (`selfCyclic`,
`isBnodeLabel`), where an out-of-range read must simply not match. -/
def charAtD (s : String) (i : Nat) : Char := s.toList[i]?.getD '\x00'

/-- `s[start ..< start+len]`. Port of `fs_byte_sub`. -/
def substr (s : String) (start len : Nat) : String := ((s.toList.drop start).take len) |> String.ofList

/-- Lexicographic comparison by code point — the byte order
`RDF.Graph.Executable.string_lt` implements, which for valid UTF-8
agrees with code-point order. -/
def charListLt : List Char → List Char → Bool
  | [],      []      => false
  | [],      _ :: _  => true
  | _ :: _,  []      => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else charListLt as bs

def strLt (a b : String) : Bool := charListLt a.toList b.toList

/-! ## Term definitions — JSON-LD 1.1 API §4.2 Create Term Definition -/

/-- A term's `@container` mapping (JSON-LD 1.1 API §4.2, the
`@container` step). `none` also covers a bare `@set` marker: array-
versus-single leniency is handled uniformly by the expansion side, so
`@set` needs no distinct kind (the `set` flag on `TermDef` records that
it was written, which compaction — not ported here — would need).
`graphId` / `graphIndex` are the two legal `@graph` combinations. -/
inductive ContainerKind where
  | none | list | index | language | id | type | graph | graphId | graphIndex
  deriving DecidableEq, Repr

def ContainerKind.isList : ContainerKind → Bool
  | .list => true
  | _     => false

/-- One term definition (JSON-LD 1.1 API §4.2). `iri` is either an
absolute IRI, a keyword (when the term is a keyword ALIAS, as in
`{"id": "@id"}`), or the sentinel `"@null"` for a term explicitly
undefined by `"term": null`.

`scopedContext` keeps the term's own `@context` RAW, paired with the
document URL in effect when the term was DEFINED — resolving a relative
remote-context reference inside it later, at the point of use, must use
the document it was written in (JSON-LD 1.1 API §4.1, "base URL"). -/
structure TermDef where
  iri           : String
  typeMapping   : Option String
  container     : ContainerKind
  reverse       : Bool
  /-- `none` = no per-term override; `some none` = `"@language": null`;
  `some (some lg)` = an explicit tag. -/
  language      : Option (Option String)
  /-- Same three-way shape, for `@direction` (`"ltr"` / `"rtl"`). -/
  direction     : Option (Option String)
  /-- A property-valued `@index` (JSON-LD 1.1 API §4.2, the `@index`
  step), stored RAW: the property it names is resolved at the point of
  use, like an ordinary property key. -/
  index         : Option String
  scopedContext : Option (Json × Option String)
  protected_    : Bool
  /-- The prefix flag (JSON-LD 1.1 API §4.2 step 24): only a term whose
  flag is true may be the prefix half of a compact IRI. -/
  prefix_       : Bool
  /-- Whether the `@container` mapping included `@set`. -/
  set_          : Bool
  /-- The term's `@nest` member (JSON-LD 1.1 API §4.2, the `@nest`
  step), validated at definition time. -/
  nest          : Option String
  deriving DecidableEq, Repr

/-! ## The active context — JSON-LD 1.1 API §4.1 -/

/-- Everything an active context holds EXCEPT the pop target. -/
structure ContextCore where
  terms          : List (String × TermDef)
  vocab          : Option String
  base           : Option String
  language       : Option String
  direction      : Option String
  /-- JSON-LD 1.0 processing mode (`option.processingMode`), which makes
  the 1.1-only constructs below fail rather than be accepted. -/
  mode10         : Bool
  /-- The URL of the document whose CONTENT is currently being read as
  context material — distinct from `base`, which an in-content `@base`
  may rewrite. A remote-context reference resolves against this (RFC
  3986 §5.1.3: the base of a retrieved representation is its own URI). -/
  docUrl         : Option String
  /-- The document's own base IRI, fixed at the start and never
  rewritten; `"@context": null` restores `base` to it (JSON-LD 1.1 API
  §4.1: "setting both base IRI and original base URL to the value of
  original base URL in active context"). -/
  originalBase   : Option String
  /-- One-shot marker: the value a non-propagating PROPERTY-scoped
  context was computed for must not immediately pop that scope away. -/
  suppressPop    : Bool
  /-- JSON-LD Framing's frame-expansion flag (not exercised by the toRdf
  path; carried so the expansion port's shape matches the F* source). -/
  frameExpansion : Bool
  deriving Repr

/-- The active context: the current record plus the stack of enclosing
ones. The F* source spells the stack as a self-referential
`ac_previous : option active_context` field; Lean structures are not
recursive, so the chain is an explicit list. The three operations the
F* source performs on that field are `pop`, `setPrev`, `clearPrev`
below, and they agree with it exactly (setting `ac_previous` to `Some
ac` makes the WHOLE of `ac`'s own chain the new tail; setting it to
`None` discards the tail, which is likewise unreachable in F*). -/
structure ActiveContext where
  cur  : ContextCore
  prev : List ContextCore
  deriving Repr

namespace ActiveContext

def terms          (ac : ActiveContext) : List (String × TermDef) := ac.cur.terms
def vocab          (ac : ActiveContext) : Option String := ac.cur.vocab
def base           (ac : ActiveContext) : Option String := ac.cur.base
def language       (ac : ActiveContext) : Option String := ac.cur.language
def direction      (ac : ActiveContext) : Option String := ac.cur.direction
def mode10         (ac : ActiveContext) : Bool := ac.cur.mode10
def docUrl         (ac : ActiveContext) : Option String := ac.cur.docUrl
def originalBase   (ac : ActiveContext) : Option String := ac.cur.originalBase
def suppressPop    (ac : ActiveContext) : Bool := ac.cur.suppressPop
def frameExpansion (ac : ActiveContext) : Bool := ac.cur.frameExpansion

/-- Update the current record, leaving the pop chain alone. -/
def upd (ac : ActiveContext) (f : ContextCore → ContextCore) : ActiveContext :=
  { ac with cur := f ac.cur }

/-- Pop to the enclosing context (F*: `match ac_previous with Some prev
-> prev | None -> ac`). -/
def pop (ac : ActiveContext) : ActiveContext :=
  match ac.prev with
  | p :: rest => { cur := p, prev := rest }
  | []        => ac

/-- Make `target` this context's pop destination (F*: `{ ac with
ac_previous = Some target }`). -/
def setPrev (ac target : ActiveContext) : ActiveContext :=
  { cur := ac.cur, prev := target.cur :: target.prev }

/-- Drop the pop destination (F*: `{ ac with ac_previous = None }`). -/
def clearPrev (ac : ActiveContext) : ActiveContext :=
  { cur := ac.cur, prev := [] }

end ActiveContext

def emptyContextCore : ContextCore :=
  { terms := [], vocab := none, base := none, language := none, direction := none,
    mode10 := false, docUrl := none, originalBase := none,
    suppressPop := false, frameExpansion := false }

def emptyActiveContext : ActiveContext := { cur := emptyContextCore, prev := [] }

/-! ## Keywords — JSON-LD 1.1 §9 Syntax Tokens and Keywords -/

/-- Starts with `@` (F*: `jldctx_is_keyword`). -/
def isKeywordChar (s : String) : Bool := slen s > 0 && charAtD s 0 == '@'

/-- The 23 ACTUAL JSON-LD 1.1 keywords (JSON-LD 1.1 §9). Distinct from
"has the form of a keyword": a non-keyword string that merely LOOKS like
one (`@ignoreMe`) is ignorable-with-a-warning, while an at-prefixed
string that does NOT look like one (`@`, `@foo.bar`) is ordinary
term/IRI material. -/
def actualKeyword (s : String) : Bool :=
  s == "@base" || s == "@container" || s == "@context" || s == "@direction"
  || s == "@graph" || s == "@id" || s == "@import" || s == "@included"
  || s == "@index" || s == "@json" || s == "@language" || s == "@list"
  || s == "@nest" || s == "@none" || s == "@prefix" || s == "@propagate"
  || s == "@protected" || s == "@reverse" || s == "@set" || s == "@type"
  || s == "@value" || s == "@version" || s == "@vocab"

def isAlphaChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

/-- RFC 3986 §3.1 scheme character: ALPHA / DIGIT / `+` / `-` / `.` -/
def isSchemeChar (c : Char) : Bool :=
  isAlphaChar c || ('0' ≤ c && c ≤ '9') || c == '+' || c == '-' || c == '.'

/-- "Has the form of a keyword" (JSON-LD 1.1 API §4.2): `@` followed by
one or more ALPHA characters only. -/
def keywordForm (s : String) : Bool :=
  slen s ≥ 2 && charAtD s 0 == '@' && (s.toList.drop 1).all isAlphaChar

/-- Keyword-SHAPED but not a real keyword — ignorable with a warning. -/
def keywordLookalike (s : String) : Bool := keywordForm s && !actualKeyword s

/-! ## Term-table helpers -/

def findTerm (terms : List (String × TermDef)) (name : String) : Option TermDef :=
  (terms.find? (fun kv => kv.1 == name)).map Prod.snd

def anyProtected (terms : List (String × TermDef)) : Bool :=
  terms.any (fun kv => kv.2.protected_)

def removeTerm (terms : List (String × TermDef)) (name : String) : List (String × TermDef) :=
  terms.filter (fun kv => kv.1 != name)

/-- Last boolean value of `key` among a context object's OWN members
(not recursing into term-definition objects), or `dflt`. Used for the
context-level `@protected` default and, by the expansion side, for
`@propagate`. -/
def scanBoolKey (fields : List (String × Json)) (key : String) (dflt : Bool) : Bool :=
  fields.foldl (fun acc kv =>
    match kv.2 with
    | .bool b => if kv.1 == key then b else acc
    | _       => acc) dflt

/-- `@propagate` over a whole context VALUE (object, or array of such,
folded left to right so a later entry wins). -/
def scanPropagate (ctx : Json) (dflt : Bool) : Bool :=
  match ctx with
  | .object fields => scanBoolKey fields "@propagate" dflt
  | .array items   => items.foldl (fun acc it =>
      match it with
      | .object fields => scanBoolKey fields "@propagate" acc
      | _              => acc) dflt
  | _ => dflt

/-- Two term definitions are "the same" for protected-redefinition
purposes when every observable part matches (JSON-LD 1.1 API §4.2, the
protected-term-redefinition step). `protected_` itself is NOT compared:
a protected term may be re-declared protected-or-not as long as what it
MAPS TO is unchanged. -/
def termDefsCompatible (a b : TermDef) : Bool :=
  a.iri == b.iri && a.typeMapping == b.typeMapping &&
  a.container == b.container && a.reverse == b.reverse &&
  a.language == b.language && a.direction == b.direction &&
  a.index == b.index && a.scopedContext == b.scopedContext &&
  a.prefix_ == b.prefix_ && a.set_ == b.set_ && a.nest == b.nest

def keyHasSlash (s : String) : Bool := s.toList.contains '/'

/-- Last character is an RFC 3986 gen-delim (`:` `/` `?` `#` `[` `]`
`@`) — the JSON-LD 1.1 test for whether a simple string-form term
definition is usable as a compact-IRI prefix. -/
def endsGenDelim (s : String) : Bool :=
  match s.toList.getLast? with
  | some c => c == ':' || c == '/' || c == '?' || c == '#' || c == '[' || c == ']' || c == '@'
  | none   => false

/-- The definition to actually STORE at a redefinition site. JSON-LD
1.1 API §4.2: a compatible redefinition of a protected term keeps the
PREVIOUS definition ("Set definition to previous definition to retain
the value of protected"), so a later compatible redefinition that omits
`@protected` cannot silently unprotect the term. -/
def resolveRedefine (ac : ActiveContext) (key : String) (newTd : TermDef)
    (overrideProtected : Bool) : Res TermDef :=
  match findTerm ac.terms key with
  | none => .ok newTd
  | some existing =>
    if existing.protected_ && !overrideProtected then
      if termDefsCompatible existing newTd then .ok existing
      else .error .protectedTermRedefinition
    else .ok newTd

/-- Index of the first `:`, or `none`. -/
def findColon (s : String) : Option Nat := s.toList.findIdx? (· == ':')

/-- A colon at neither the first nor the last position. -/
def colonNotAtEdges (s : String) : Bool :=
  match findColon s with
  | some c => c > 0 && c + 1 < slen s
  | none   => false

/-- A term NAME that is compact-IRI- / absolute-IRI-shaped, or contains
a slash, triggers JSON-LD 1.1 API §4.2's self-consistency check when it
also carries an explicit `@id`. -/
def termNeedsSelfCheck (s : String) : Bool := colonNotAtEdges s || keyHasSlash s

/-- A blank node identifier — legal as an `@id`/`@reverse` mapping, but
not as a `@type` mapping (JSON-LD 1.1 API §4.2: the expanded type must
be `@id`, `@json`, `@none`, `@vocab`, or an IRI). -/
def isBnodeId (s : String) : Bool := charAtD s 0 == '_' && charAtD s 1 == ':'

/-- A cyclic IRI mapping (JSON-LD 1.1 API §4.2's `defined` map: "If
defined contains the entry term and the associated value is false, a
cyclic IRI mapping error"): an `@id`/`@reverse` value that is a compact
IRI whose PREFIX is the very term being defined, when that term has no
definition yet. Mirrors `expandIriGen`'s own guard order — a colon that
`expandIriGen` would shortcut (`_:`, a non-scheme-shaped prefix, `//`
authority) is not a prefix dependency at all. -/
def selfCyclic (ac : ActiveContext) (key raw : String) : Bool :=
  match findColon raw with
  | some c =>
    c > 0 &&
    (let pre := substr raw 0 c
     pre != "_" &&
     (pre.toList.all isSchemeChar) &&
     !(charAtD raw (c + 1) == '/' && charAtD raw (c + 2) == '/') &&
     pre == key &&
     (findTerm ac.terms key).isNone)
  | none => false

/-- RFC 3986 reference resolution against a base string, with the F*
source's safe fallback when the base is not IRI-shaped. -/
def resolveRel (base relative : String) : String :=
  if L4Factoidal.RDF.isIri base then L4Factoidal.Syntax.resolveIri base relative else base

/-! ## Remote contexts — JSON-LD 1.1 API §4.1, the dereference step -/

/-- Depth budget for remote-context / `@import` chains. Spent only on an
actual fetch, so a large inline context never exhausts it. -/
def remoteContextFuel : Nat := 32

/-- Resolve a context reference against the URL of the document whose
CONTENT is being read (RFC 3986 §5.1.3), falling back to `@base` when
that is unset. -/
def resolveContextIri (ac : ActiveContext) (raw : String) : Option String :=
  match ac.docUrl with
  | some d => some (resolveRel d raw)
  | none =>
    match ac.base with
    | some b => some (resolveRel b raw)
    | none   => if L4Factoidal.RDF.isIri raw then some raw else none

/-- Split a context object's members into its (at most one) `@import`
value and the rest. -/
def extractImport (fields : List (String × Json)) : Option String × List (String × Json) :=
  let importVal :=
    match fields.find? (fun kv => kv.1 == "@import") with
    | some (_, .string s) => some s
    | _                   => none
  (importVal, fields.filter (fun kv => kv.1 != "@import"))

/-- Fetch, parse, and return the document's top-level `@context` member.
The two failure modes are the spec's own: the fetch failed (`loading
remote context failed`) or the document is not a usable remote context
(`invalid remote context`). NEVER an empty-context fallback — see
`Loader.lean`. -/
def fetchRemoteContext (loader : Loader) (resolved : String) : Res Json :=
  match loader resolved with
  | none => .error .loadingRemoteContextFailed
  | some raw =>
    match parseJson raw with
    | .error _ => .error .invalidRemoteContext
    | .ok doc =>
      match doc.field? "@context" with
      | some c => .ok c
      | none   => .error .invalidRemoteContext

/-! ## IRI expansion — JSON-LD 1.1 API §5.2.2 -/

/-- The `@vocab`- or `@base`-relative fallback. A vocab-relative value
is a plain concatenation onto the vocabulary mapping (the spec's
vocab-mapping expansion, not a reference resolution); a
document-relative value gets full RFC 3986 resolution. -/
def expandFallback (ac : ActiveContext) (value : String) (vocab : Bool) : Option String :=
  if vocab then ac.vocab.map (fun v => v ++ value)
  else ac.base.map (fun b => resolveRel b value)

/-- JSON-LD 1.1 API §5.2.2 IRI Expansion.

`inCtx` is true when called DURING context processing (the spec's "local
context is not null" condition), where compact-IRI prefix lookup applies
regardless of the prefix flag; at expansion time the flag gates prefix
use. JSON-LD 1.0 had no prefix flag at all, so `mode10` bypasses the
gate the same way. -/
def expandIriGen (ac : ActiveContext) (value : String) (vocab inCtx : Bool) : Option String :=
  let n := slen value
  if n == 0 then
    -- RFC 3986 §5.4: the EMPTY reference resolves to the base itself.
    -- Only meaningful document-relative.
    (if vocab then none else expandFallback ac value false)
  else if actualKeyword value then some value
  else
    -- Full-term substitution applies only vocab-relative (an `@id` value
    -- equal to a defined term's name still resolves document-relative).
    let termHit := if vocab then findTerm ac.terms value else none
    match termHit with
    | some td => some td.iri
    | none =>
      -- A keyword LOOKALIKE expands to itself: the spec says "null with
      -- a warning", but every consumer already drops a colonless non-IRI
      -- at the RDF layer, whereas returning `none` here would DROP the
      -- `@id` member and mint a fresh blank node — observably wrong.
      if keywordForm value then some value
      else
        match findColon value with
        | none => expandFallback ac value vocab
        | some c =>
          if c == 0 then expandFallback ac value vocab
          else
            let pre := substr value 0 c
            if pre == "_" then some value
            -- RFC 3986 §3.1: every character before the colon must be
            -- scheme-legal for that colon to delimit a scheme (or a
            -- compact-IRI prefix). `#Test:2` has its colon inside a
            -- fragment, so it can never be an absolute-or-compact IRI.
            else if !(pre.toList.all isSchemeChar) then expandFallback ac value vocab
            else if charAtD value (c + 1) == '/' && charAtD value (c + 2) == '/' then some value
            else
              match findTerm ac.terms pre with
              | none => some value
              | some ptd =>
                if isKeywordChar ptd.iri then none
                else if !(inCtx || ptd.prefix_ || ac.mode10) then some value
                else some (ptd.iri ++ substr value (c + 1) (n - c - 1))

/-- Expansion-time IRI expansion (pre flag honoured). -/
def expandIri (ac : ActiveContext) (value : String) (vocab : Bool) : Option String :=
  expandIriGen ac value vocab false

/-- Context-processing IRI expansion (pre flag bypassed). -/
def expandIriCtx (ac : ActiveContext) (value : String) (vocab : Bool) : Option String :=
  expandIriGen ac value vocab true

/-! ## `@container` parsing — JSON-LD 1.1 API §4.2 -/

def containerKindOfString (s : String) : Option ContainerKind :=
  if s == "@list" then some .list
  else if s == "@set" then some .none
  else if s == "@index" then some .index
  else if s == "@language" then some .language
  else if s == "@id" then some .id
  else if s == "@type" then some .type
  else if s == "@graph" then some .graph
  else Option.none

/-- Which combinable flags an `@container` ARRAY carries, or `none` for
an entry that is not a container keyword. -/
def containerFlags : List Json → Option (Bool × Bool × Bool × Bool × Bool × Bool)
  | [] => some (false, false, false, false, false, false)
  | .string s :: rest =>
    match containerFlags rest with
    | Option.none => Option.none
    | some (g, i, ix, lg, ty, ls) =>
      if s == "@set" then some (g, i, ix, lg, ty, ls)
      else if s == "@graph" then some (true, i, ix, lg, ty, ls)
      else if s == "@id" then some (g, true, ix, lg, ty, ls)
      else if s == "@index" then some (g, i, true, lg, ty, ls)
      else if s == "@language" then some (g, i, ix, true, ty, ls)
      else if s == "@type" then some (g, i, ix, lg, true, ls)
      else if s == "@list" then some (g, i, ix, lg, ty, true)
      else Option.none
  | _ => Option.none

/-- `@list` may not combine with any other container keyword. -/
def containerKindOfFlags (g i ix lg ty ls : Bool) : Option ContainerKind :=
  if ls then (if g || i || ix || lg || ty then Option.none else some .list)
  else if g then (if i then some .graphId else if ix then some .graphIndex else some .graph)
  else if i then some .id
  else if ix then some .index
  else if lg then some .language
  else if ty then some .type
  else some .none

def containerKindOfItems (items : List Json) : Option ContainerKind :=
  match containerFlags items with
  | Option.none => Option.none
  | some (g, i, ix, lg, ty, ls) =>
    -- `@set` is transparent to the KIND, but still participates in
    -- `@list`'s may-not-combine rule: `["@list", "@set"]` is invalid.
    if ls && items.any (fun it => match it with | .string s => s == "@set" | _ => false)
    then Option.none
    else containerKindOfFlags g i ix lg ty ls

/-! ## Object-form term definitions — JSON-LD 1.1 API §4.2 -/

/-- The accumulator threaded through one term-definition object's
members: `@id`, `@reverse`, `@type`, the container kind, `@language`,
`@direction`, `@index`, the raw scoped `@context`, and an explicit
`@protected` override. -/
structure TermObjAcc where
  id        : Option String
  reverse   : Option String
  type_     : Option String
  container : ContainerKind
  language  : Option (Option String)
  direction : Option (Option String)
  index     : Option String
  ctx       : Option Json
  protected_ : Option Bool

def emptyTermObjAcc : TermObjAcc :=
  { id := none, reverse := none, type_ := none, container := .none,
    language := none, direction := none, index := none, ctx := none, protected_ := none }

/-- One left-to-right pass over a term-definition object's members
(JSON-LD 1.1 API §4.2). Any unrecognised member is an invalid term
definition rather than a silently incomplete term. -/
def termObjFields (ac : ActiveContext) (acc : TermObjAcc)
    : List (String × Json) → Res TermObjAcc
  | [] => .ok acc
  | (k, v) :: rest =>
    if k == "@id" then
      match v with
      | .string s =>
        -- An `@id` value that LOOKS like a keyword is ignored: the entry
        -- is skipped and the mapping falls back to `@vocab` + term name.
        if keywordLookalike s then termObjFields ac acc rest
        else
          match expandIriCtx ac s true with
          -- §4.2: "if it equals @context, an invalid keyword alias error".
          | some e => if e == "@context" then .error .invalidKeywordAlias
                      else termObjFields ac { acc with id := some e } rest
          | none => .error .invalidIriMapping
      | _ => .error .invalidIriMapping
    else if k == "@reverse" then
      match v with
      | .string s =>
        match expandIriCtx ac s true with
        | some e => termObjFields ac { acc with reverse := some e } rest
        | none   => .error .invalidIriMapping
      | _ => .error .invalidIriMapping
    else if k == "@type" then
      match v with
      | .string s =>
        match expandIriCtx ac s true with
        | some e =>
          -- §4.2: `@json` / `@none` are invalid type mappings in 1.0;
          -- otherwise the expanded type must be `@id`, `@json`, `@none`,
          -- `@vocab`, or an IRI — a blank node identifier is none of
          -- those.
          if ac.mode10 && (e == "@json" || e == "@none") then .error .invalidTypeMapping
          else if e == "@id" || e == "@json" || e == "@none" || e == "@vocab" then
            termObjFields ac { acc with type_ := some e } rest
          else if isBnodeId e then .error .invalidTypeMapping
          else termObjFields ac { acc with type_ := some e } rest
        | none => .error .invalidTypeMapping
      | _ => .error .invalidTypeMapping
    else if k == "@container" then
      match v with
      | .string s =>
        match containerKindOfString s with
        | some ck =>
          -- §4.2: `@graph`/`@id`/`@type` containers, and every ARRAY-
          -- shaped `@container`, are 1.1-only.
          if ac.mode10 && (ck == .graph || ck == .id || ck == .type)
          then .error .invalidContainerMapping
          else termObjFields ac { acc with container := ck } rest
        | none => .error .invalidContainerMapping
      | .array items =>
        if ac.mode10 then .error .invalidContainerMapping
        else
          match containerKindOfItems items with
          | some ck => termObjFields ac { acc with container := ck } rest
          | none    => .error .invalidContainerMapping
      | _ => .error .invalidContainerMapping
    else if k == "@language" then
      match v with
      | .string s => termObjFields ac { acc with language := some (some s) } rest
      | .null     => termObjFields ac { acc with language := some none } rest
      | _         => .error .invalidLanguageMapping
    else if k == "@direction" then
      match v with
      | .string s =>
        if s == "ltr" || s == "rtl"
        then termObjFields ac { acc with direction := some (some s) } rest
        else .error .invalidBaseDirection
      | .null => termObjFields ac { acc with direction := some none } rest
      | _     => .error .invalidBaseDirection
    else if k == "@index" then
      -- Stored RAW: the property this names is resolved at the point of
      -- use, like an ordinary property key. A keyword value can never
      -- name a property. 1.1-only.
      if ac.mode10 then .error .invalidTermDefinition
      else
        match v with
        | .string s => if isKeywordChar s then .error .invalidTermDefinition
                       else termObjFields ac { acc with index := some s } rest
        | _ => .error .invalidTermDefinition
    else if k == "@context" then
      -- A property- or type-scoped context, stored RAW: any failure
      -- surfaces at the point of use. 1.1-only.
      if ac.mode10 then .error .invalidTermDefinition
      else termObjFields ac { acc with ctx := some v } rest
    else if k == "@protected" then
      if ac.mode10 then .error .invalidTermDefinition
      else
        match v with
        | .bool b => termObjFields ac { acc with protected_ := some b } rest
        | _       => .error .invalidTermDefinition
    else if k == "@prefix" then
      -- Validated here (boolean, 1.1-only); CONSUMED by a separate scan
      -- in `processTermDefObj`.
      if ac.mode10 then .error .invalidTermDefinition
      else
        match v with
        | .bool _ => termObjFields ac acc rest
        | _       => .error .invalidPrefixValue
    else if k == "@nest" then
      -- §4.2, the `@nest` step: "If nest value is not a string, or is a
      -- keyword other than @nest, an invalid @nest value error".
      if ac.mode10 then .error .invalidTermDefinition
      else
        match v with
        | .string s =>
          if s == "@nest" || !actualKeyword s then termObjFields ac acc rest
          else .error .invalidNestValue
        | _ => .error .invalidNestValue
    else .error .invalidTermDefinition

/-- Pair a term's raw scoped `@context` with the document URL in effect
when the term was defined. -/
def wrapScoped (ac : ActiveContext) (ctx : Option Json) : Option (Json × Option String) :=
  ctx.map (fun c => (c, ac.docUrl))

/-- Did the term's `@container` include `@set`? -/
def containerIncludesSet (fields : List (String × Json)) : Bool :=
  match fields.find? (fun kv => kv.1 == "@container") with
  | some (_, .string s) => s == "@set"
  | some (_, .array items) =>
    items.any (fun it => match it with | .string s => s == "@set" | _ => false)
  | _ => false

def scanNest (fields : List (String × Json)) : Option String :=
  match fields.find? (fun kv => kv.1 == "@nest") with
  | some (_, .string s) => some s
  | _                   => none

/-- True when an object-form definition's `@id` (or, absent that,
`@reverse`) STRING value names the very term being defined. -/
def termObjSelfId (key : String) (fields : List (String × Json)) : Bool :=
  match fields.find? (fun kv => kv.1 == "@id") with
  | some (_, .string s) => s == key
  | _ =>
    match fields.find? (fun kv => kv.1 == "@reverse") with
    | some (_, .string s) => s == key
    | _                   => false

/-- JSON-LD 1.1 API §4.2 Create Term Definition, object form. -/
def processTermDefObj (ac : ActiveContext) (key : String) (fields : List (String × Json))
    (defaultProtected overrideProtected : Bool) : Res ActiveContext :=
  -- Cyclic IRI mapping pre-check, against the RAW `@id`/`@reverse`
  -- strings, before any of them is IRI-expanded.
  let selfRef :=
    (match fields.find? (fun kv => kv.1 == "@id") with
     | some (_, .string s) => selfCyclic ac key s
     | _ => false) ||
    (match fields.find? (fun kv => kv.1 == "@reverse") with
     | some (_, .string s) => selfCyclic ac key s
     | _ => false)
  if selfRef then .error .cyclicIriMapping else
  -- §4.2 marks `defined[term] = false` for the whole of a term's own
  -- processing, so IRI expansion of that term's own `@id`/`@reverse`
  -- must not resolve `term` through its own stale mapping.
  let acFields :=
    if termObjSelfId key fields then ac.upd (fun c => { c with terms := removeTerm c.terms key })
    else ac
  match termObjFields acFields emptyTermObjAcc fields with
  | .error e => .error e
  | .ok a =>
    -- A term's `@index` is only meaningful when its own `@container`
    -- includes `@index`.
    if a.index.isSome && !(a.container == .index || a.container == .graphIndex) then
      .error .invalidTermDefinition
    -- §4.2, the `@container: @type` step: an explicit type mapping must
    -- then be `@id` or `@vocab`.
    else if a.container == .type && a.type_.isSome
            && a.type_ != some "@id" && a.type_ != some "@vocab" then
      .error .invalidTypeMapping
    else
      let setFlag := containerIncludesSet fields
      let nestVal := scanNest fields
      let prot := a.protected_.getD defaultProtected
      let hasPrefixMember := fields.any (fun kv => kv.1 == "@prefix")
      let prefixFlag := scanBoolKey fields "@prefix" false
      -- §4.2 step 24: an explicit `@prefix` may not sit on a term name
      -- containing a colon or a slash.
      if hasPrefixMember && (findColon key).isSome then .error .invalidTermDefinition
      else if hasPrefixMember && keyHasSlash key then .error .invalidTermDefinition
      else
        let mk (iri : String) (rev : Bool) : TermDef :=
          { iri := iri, typeMapping := a.type_, container := a.container,
            reverse := rev, language := a.language, direction := a.direction,
            index := a.index, scopedContext := wrapScoped ac a.ctx,
            protected_ := prot, prefix_ := prefixFlag, set_ := setFlag, nest := nestVal }
        let store (td : TermDef) : Res ActiveContext :=
          match resolveRedefine ac key td overrideProtected with
          | .error e => .error e
          | .ok final => .ok (ac.upd (fun c => { c with terms := (key, final) :: c.terms }))
        match a.id, a.reverse with
        | some _, some _ => .error .invalidReverseProperty
        | some iri, none =>
          if prefixFlag && isKeywordChar iri then .error .invalidTermDefinition
          -- §4.2 self-consistency: a colon-/slash-bearing term name must
          -- IRI-expand to the SAME mapping its explicit `@id` produced.
          -- The whole step is 1.1-only. Expanded with its own entry
          -- stripped, so a preview registration cannot make it vacuous.
          else if (!ac.mode10) && termNeedsSelfCheck key
                  && expandIriCtx (ac.upd (fun c => { c with terms := removeTerm c.terms key })) key true
                     != some iri then
            .error .invalidIriMapping
          else store (mk iri false)
        | none, some iri =>
          -- §4.2, the `@reverse` step: reverse properties support only
          -- set- and index-containers, and carry no `@nest`.
          if !(a.container == .none || a.container == .index) then .error .invalidReverseProperty
          else if nestVal.isSome then .error .invalidReverseProperty
          else store (mk iri true)
        | none, none =>
          -- No explicit `@id`/`@reverse`: the mapping is derived from the
          -- term NAME via the colon-prefix / `@vocab` fallback chain only,
          -- never through the term's own stale entry.
          match expandIriCtx (ac.upd (fun c => { c with terms := removeTerm c.terms key })) key true with
          | none => .error .invalidIriMapping
          | some iri => store (mk iri false)

/-! ## Top level — JSON-LD 1.1 API §4.1 Context Processing -/

/-- The six keywords §4.1 updates BEFORE any ordinary term definition
("because they affect how the other entries are processed"). Used only
by the `@import` merge: an ordinary context object is processed in
literal JSON order, which matches every fixture, whereas `@import` can
introduce a term definition textually before a keyword that must still
take effect first. -/
def isSpecialContextKey (k : String) : Bool :=
  k == "@base" || k == "@vocab" || k == "@language" || k == "@direction" ||
  k == "@propagate" || k == "@version"

def partitionSpecial (fields : List (String × Json))
    : List (String × Json) × List (String × Json) :=
  (fields.filter (fun kv => isSpecialContextKey kv.1),
   fields.filter (fun kv => !isSpecialContextKey kv.1))

/-- §4.1 `@import`: "Set context to the result of merging context into
import context, replacing common entries with those from context" — a
key-level union where the CONTAINING context's entry wins. -/
def mergeImport (imported local_ : List (String × Json)) : List (String × Json) :=
  imported.filter (fun kv => !local_.any (fun lv => lv.1 == kv.1)) ++ local_

/-- Forward-reference pre-pass (§4.2's `defined` map: "If the prefix is
an entry in local context, then its term definition must first be
created, through recursion"). This is the narrow, common case: a plain
SIMPLE-STRING-FORM prefix declaration is pre-registered so an EARLIER
field of the same context object can use it. Only NEW keys are
previewed, never shadowing an existing (possibly protected) entry; the
main pass overwrites each preview at its own textual position with the
fully-validated definition. Object-form definitions are not previewed —
the general recursive case remains an open gap, matching the F* source. -/
def previewPrefixes (ac : ActiveContext) : List (String × Json) → ActiveContext
  | [] => ac
  | (k, .string s) :: rest =>
    if actualKeyword k || keywordLookalike k || keywordLookalike s
       || isKeywordChar k || k == "" || (findTerm ac.terms k).isSome then
      previewPrefixes ac rest
    else
      match expandIriCtx ac s true with
      | none => previewPrefixes ac rest
      | some iri =>
        if isKeywordChar iri then previewPrefixes ac rest
        else
          let td : TermDef :=
            { iri := iri, typeMapping := none, container := .none, reverse := false,
              language := none, direction := none, index := none, scopedContext := none,
              protected_ := false, prefix_ := endsGenDelim iri, set_ := false, nest := none }
          previewPrefixes (ac.upd (fun c => { c with terms := (k, td) :: c.terms })) rest
  | _ :: rest => previewPrefixes ac rest

/-- Fuel for the context-processing recursion. Contexts are small
relative to documents; this is a generous over-provision so the
`fuel = 0` safety net is never the reason a real fixture fails. -/
def contextFuel : Nat := 20000

mutual

/-- JSON-LD 1.1 API §4.1 Context Processing Algorithm.

`fuel` bounds the recursion structurally; `rfuel` is the remote-fetch
DEPTH budget (spent only on an actual fetch, so a large inline context
never exhausts it); `visited` is the cycle guard over absolute IRIs
already fetched on this chain. -/
def contextProcess (loader : Loader) (ac : ActiveContext) (ctx : Json)
    (overrideProtected : Bool) (fuel rfuel : Nat) (visited : List String) : Res ActiveContext :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match ctx with
    | .null =>
      -- §4.1, resetting the active context: "initialize result ...
      -- setting both base IRI and original base URL to the value of
      -- original base URL in active context". The reset RESTORES the
      -- document's base; it does not merely clear it. (Contrast an
      -- ordinary `"@base": null` member, which is a plain clear.)
      if (!overrideProtected) && anyProtected ac.terms then .error .invalidContextNullification
      else .ok (ac.upd (fun c =>
        { c with terms := [], vocab := none, language := none, base := c.originalBase }))
    | .string s =>
      -- A remote context reference (§4.1's dereference step).
      if rfuel == 0 then .error .contextOverflow
      else
        match resolveContextIri ac s with
        | none => .error .loadingRemoteContextFailed
        | some resolved =>
          if visited.contains resolved then .error .recursiveContextInclusion
          else
            match fetchRemoteContext loader resolved with
            | .error e => .error e
            | .ok inner =>
              -- The fetched document's content is read with `docUrl` set
              -- to its OWN resolved URL, then RESTORED on the result so
              -- sibling entries keep resolving against their own
              -- document.
              match contextProcess loader (ac.upd (fun c => { c with docUrl := some resolved }))
                      inner overrideProtected fuel (rfuel - 1) (resolved :: visited) with
              | .error e => .error e
              | .ok ac' => .ok (ac'.upd (fun c => { c with docUrl := ac.docUrl }))
    | .array items => contextProcessArray loader ac items overrideProtected fuel rfuel visited
    | .object fields =>
      match extractImport fields with
      | (none, _) =>
        let acPreview := previewPrefixes ac fields
        contextProcessFields loader acPreview fields
          (scanBoolKey fields "@protected" false) overrideProtected fuel rfuel visited
      | (some importRef, restFields) =>
        -- §4.1 `@import`: fetch the imported context, MERGE its fields
        -- with this object's remaining members (local wins on collision),
        -- then process the merged set as ONE context object — special
        -- keywords first, ordinary term definitions second. 1.1-only.
        if ac.mode10 then .error .invalidContextEntry
        else if rfuel == 0 then .error .contextOverflow
        else
          match resolveContextIri ac importRef with
          | none => .error .loadingRemoteContextFailed
          | some resolved =>
            if visited.contains resolved then .error .recursiveContextInclusion
            else
              match fetchRemoteContext loader resolved with
              | .error e => .error e
              | .ok importedCtx =>
                -- `@import` must reference a document whose `@context` is
                -- a single context OBJECT.
                match importedCtx with
                | .object importedFields =>
                  let merged := mergeImport importedFields restFields
                  let acPreview := previewPrefixes ac merged
                  let (special, ordinary) := partitionSpecial merged
                  let defProt := scanBoolKey merged "@protected" false
                  match contextProcessFields loader acPreview special defProt overrideProtected
                          fuel (rfuel - 1) (resolved :: visited) with
                  | .error e => .error e
                  | .ok acSpecial =>
                    contextProcessFields loader acSpecial ordinary defProt overrideProtected
                      fuel (rfuel - 1) (resolved :: visited)
                | _ => .error .invalidRemoteContext
    | _ => .error .invalidLocalContext
termination_by fuel

/-- An array of contexts, folded left to right. -/
def contextProcessArray (loader : Loader) (ac : ActiveContext) (items : List Json)
    (overrideProtected : Bool) (fuel rfuel : Nat) (visited : List String) : Res ActiveContext :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match items with
    | [] => .ok ac
    | hd :: tl =>
      match contextProcess loader ac hd overrideProtected fuel rfuel visited with
      | .error e => .error e
      | .ok ac1 => contextProcessArray loader ac1 tl overrideProtected fuel rfuel visited
termination_by fuel

/-- One context object's members, left to right. -/
def contextProcessFields (loader : Loader) (ac : ActiveContext) (fields : List (String × Json))
    (defaultProtected overrideProtected : Bool) (fuel rfuel : Nat) (visited : List String)
    : Res ActiveContext :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
    match fields with
    | [] => .ok ac
    | (key, value) :: rest =>
      match contextProcessOneField loader ac key value defaultProtected overrideProtected
              fuel rfuel visited with
      | .error e => .error e
      | .ok ac1 =>
        contextProcessFields loader ac1 rest defaultProtected overrideProtected fuel rfuel visited
termination_by fuel

/-- One context-object member: `@base` / `@vocab` / `@language` /
`@direction` / `@version` / `@protected` / `@propagate` / `@type`, or an
ordinary term definition (simple string, expanded object, or null). -/
def contextProcessOneField (loader : Loader) (ac : ActiveContext) (key : String) (value : Json)
    (defaultProtected overrideProtected : Bool) (fuel rfuel : Nat) (visited : List String)
    : Res ActiveContext :=
  match fuel with
  | 0 => .error .contextOverflow
  | fuel + 1 =>
  if key == "@base" then
    match value with
    | .string s =>
      -- An ALREADY-ABSOLUTE `@base` is adopted VERBATIM, not merged via
      -- full RFC 3986 reference resolution — running it through
      -- `resolveIri` would apply remove_dot_segments even though the new
      -- value carries its own scheme, silently stripping a deliberate
      -- `./`. Only a genuinely relative value is resolved.
      let resolved :=
        if L4Factoidal.RDF.isIri s then s
        else match ac.base with
             | some b => resolveRel b s
             | none   => s
      .ok (ac.upd (fun c => { c with base := some resolved }))
    | .null => .ok (ac.upd (fun c => { c with base := none }))
    | _ => .error .invalidBaseIri
  else if key == "@vocab" then
    match value with
    | .string s =>
      -- §4.1: the vocabulary mapping value is itself IRI-expanded
      -- vocab-relative with a document-relative fallback. JSON-LD 1.0 had
      -- no relative-`@vocab` resolution: anything not an absolute IRI or
      -- blank node identifier is an invalid vocab mapping.
      let abs10 :=
        isBnodeId s ||
        (match findColon s with
         | none => false
         | some c => c > 0 && (substr s 0 c).toList.all isSchemeChar)
      if ac.mode10 && !abs10 then .error .invalidVocabMapping
      else
        match expandIriCtx ac s true with
        | some iri => .ok (ac.upd (fun c => { c with vocab := some iri }))
        | none =>
          match ac.base with
          | some b => .ok (ac.upd (fun c => { c with vocab := some (resolveRel b s) }))
          | none   => .error .invalidVocabMapping
    | .null => .ok (ac.upd (fun c => { c with vocab := none }))
    | _ => .error .invalidVocabMapping
  else if key == "@language" then
    match value with
    | .string s => .ok (ac.upd (fun c => { c with language := some s }))
    | .null     => .ok (ac.upd (fun c => { c with language := none }))
    | _         => .error .invalidDefaultLanguage
  else if key == "@direction" then
    match value with
    | .string s =>
      if s == "ltr" || s == "rtl" then .ok (ac.upd (fun c => { c with direction := some s }))
      else .error .invalidBaseDirection
    | .null => .ok (ac.upd (fun c => { c with direction := none }))
    | _ => .error .invalidBaseDirection
  else if key == "@version" then
    -- §4.1.8: the value MUST be the number 1.1 exactly; and `"@version":
    -- 1.1` under an explicit json-ld-1.0 processing mode is its own
    -- (distinct) processing mode conflict.
    match value with
    | .number lex =>
      if lex != "1.1" then .error .invalidVersionValue
      else if ac.mode10 then .error .processingModeConflict
      else .ok ac
    | _ => .error .invalidVersionValue
  else if key == "@protected" then
    match value with
    | .bool _ => .ok ac
    | _       => .error .invalidContextEntry
  else if key == "@propagate" then
    -- 1.1-only (§4.1).
    if ac.mode10 then .error .invalidContextEntry
    else match value with
    | .bool _ => .ok ac
    | _       => .error .invalidPropagateValue
  else if key == "@type" then
    -- §4.2: redefining the KEYWORD `@type` is illegal in 1.0 outright,
    -- and in 1.1 the value must be a map containing at least one of —
    -- and only — `"@container": "@set"` and `"@protected"`. The
    -- keyword's own set-ness and protected-ness ARE tracked, as an
    -- ordinary term definition stored under the literal key "@type", so
    -- a later redefinition faces the same protected-term rule as any
    -- term. (Safe: `expandIriGen` returns any actual keyword before ever
    -- consulting the term table, so this pseudo-entry is only ever read
    -- back here.)
    if ac.mode10 then .error .keywordRedefinition
    else
      match value with
      | .object tfields =>
        let shapeOk :=
          !tfields.isEmpty &&
          tfields.all (fun kv =>
            (kv.1 == "@container" && (match kv.2 with | .string "@set" => true | _ => false)) ||
            (kv.1 == "@protected" && (match kv.2 with | .bool _ => true | _ => false)))
        if !shapeOk then .error .keywordRedefinition
        else
          let hasSet := tfields.any (fun kv => kv.1 == "@container")
          let prot := scanBoolKey tfields "@protected" false
          let td : TermDef :=
            { iri := "@type", typeMapping := none,
              container := (if hasSet then .type else .none), reverse := false,
              language := none, direction := none, index := none, scopedContext := none,
              protected_ := prot, prefix_ := false, set_ := hasSet, nest := none }
          match resolveRedefine ac "@type" td overrideProtected with
          | .error e => .error e
          | .ok final => .ok (ac.upd (fun c => { c with terms := ("@type", final) :: c.terms }))
      | _ => .error .keywordRedefinition
  -- A term NAME that is an actual keyword may not be redefined; one that
  -- merely LOOKS like a keyword is ignored with a warning; an
  -- at-prefixed name WITHOUT keyword form is an ordinary term.
  else if actualKeyword key then .error .keywordRedefinition
  else if keywordLookalike key then .ok ac
  -- §4.2: "If term is the empty string, an invalid term definition
  -- error".
  else if key == "" then .error .invalidTermDefinition
  else
    match value with
    | .null =>
      -- `"term": null` DECOUPLES the term from `@vocab`: the term is not
      -- merely removed (which would re-expose the `@vocab` fallback) but
      -- pinned to the `"@null"` sentinel, which the expansion side drops.
      -- §4.2 still runs Create Term Definition, so the ambient
      -- `@protected` default sticks to a null entry too.
      let td : TermDef :=
        { iri := "@null", typeMapping := none, container := .none, reverse := false,
          language := none, direction := none, index := none, scopedContext := none,
          protected_ := defaultProtected, prefix_ := false, set_ := false, nest := none }
      match findTerm ac.terms key with
      | some existing =>
        if existing.protected_ && !overrideProtected then .error .protectedTermRedefinition
        else .ok (ac.upd (fun c => { c with terms := (key, td) :: removeTerm c.terms key }))
      | none => .ok (ac.upd (fun c => { c with terms := (key, td) :: c.terms }))
    | .string s =>
      -- A simple-form definition whose VALUE looks like a keyword is
      -- ignored entirely; the term stays undefined.
      if keywordLookalike s then .ok ac
      -- Simple string form is sugar for `{"@id": s}`, so the same cyclic
      -- and self-consistency checks apply.
      else if selfCyclic ac key s then .error .cyclicIriMapping
      else
        -- §4.2 skips the id-expansion machinery when the string value
        -- EQUALS the term's own name: `"term": "term"` falls straight to
        -- the colon/`@vocab` fallback and must not resolve through its
        -- own stale mapping.
        let acLookup :=
          if s == key then ac.upd (fun c => { c with terms := removeTerm c.terms key }) else ac
        match expandIriCtx acLookup s true with
        | none => .error .invalidIriMapping
        | some iri =>
          if (!ac.mode10) && termNeedsSelfCheck key
             && expandIriCtx (ac.upd (fun c => { c with terms := removeTerm c.terms key })) key true
                != some iri then
            .error .invalidIriMapping
          else
            let td : TermDef :=
              { iri := iri, typeMapping := none, container := .none, reverse := false,
                language := none, direction := none, index := none, scopedContext := none,
                protected_ := defaultProtected, prefix_ := endsGenDelim iri,
                set_ := false, nest := none }
            match resolveRedefine ac key td overrideProtected with
            | .error e => .error e
            | .ok final => .ok (ac.upd (fun c => { c with terms := (key, final) :: c.terms }))
    | .object termFields =>
      -- §4.2's `@reverse` step: a definition whose `@reverse` member has
      -- keyword FORM is ignored entirely (warning, no term created).
      let revKw := termFields.any (fun kv =>
        kv.1 == "@reverse" && (match kv.2 with | .string rs => keywordForm rs | _ => false))
      -- `{"@id": null}` pins the term to the `"@null"` sentinel, exactly
      -- like a bare `"term": null`.
      let idNull := termFields.any (fun kv =>
        kv.1 == "@id" && (match kv.2 with | .null => true | _ => false))
      if revKw then .ok ac
      else if idNull then
        let td : TermDef :=
          { iri := "@null", typeMapping := none, container := .none, reverse := false,
            language := none, direction := none, index := none, scopedContext := none,
            protected_ := defaultProtected, prefix_ := false, set_ := false, nest := none }
        match findTerm ac.terms key with
        | some existing =>
          if existing.protected_ && !overrideProtected then .error .protectedTermRedefinition
          else .ok (ac.upd (fun c => { c with terms := (key, td) :: removeTerm c.terms key }))
        | none => .ok (ac.upd (fun c => { c with terms := (key, td) :: c.terms }))
      else
        -- §4.1 validates a term's own scoped `@context` EAGERLY, at
        -- definition time, even when the term is never used. The
        -- validation RESULT is discarded (the raw value is what gets
        -- stored and re-processed at each point of use); only a FAILURE
        -- is load-bearing. `overrideProtected = true` here because this
        -- pass exists to catch STRUCTURAL failures, not to re-enforce
        -- protected-term rules ahead of the real point of use.
        --
        -- A REMOTE (string) scoped-context reference is deliberately NOT
        -- chased here: a scoped context may legally include itself
        -- recursively, which only terminates because the DOCUMENT's own
        -- nesting bounds how often the term is actually used.
        if rfuel == 0 then .error .contextOverflow
        else
          match processTermDefObj ac key termFields defaultProtected overrideProtected with
          | .error e => .error e
          | .ok ac' =>
            match findTerm ac'.terms key with
            | some td =>
              match td.scopedContext with
              | some (.string _, _) => .ok ac'
              | some (raw, defDocUrl) =>
                match contextProcess loader (ac'.upd (fun c => { c with docUrl := defDocUrl }))
                        raw true fuel (rfuel - 1) visited with
                | .error _ => .error .invalidScopedContext
                | .ok _    => .ok ac'
              | none => .ok ac'
            | none => .ok ac'
    | _ => .error .invalidTermDefinition
termination_by fuel

end

/-! ## Entry points -/

/-- Build an active context from a bare `@context` value. -/
def activeContextFromJson (loader : Loader) (ctx : Json) : Res ActiveContext :=
  contextProcess loader emptyActiveContext ctx false contextFuel remoteContextFuel []

/-- A property-KEY term resolves (JSON-LD 1.1 API §5.2.2: node-object
member keys are always vocab-relative). -/
def termResolvesAsProperty (ac : ActiveContext) (term : String) : Bool :=
  (expandIri ac term true).isSome

/-- A `@type` VALUE resolves: vocab-relative first, document-relative
fallback. -/
def termResolvesAsType (ac : ActiveContext) (term : String) : Bool :=
  (expandIri ac term true).isSome || (expandIri ac term false).isSome

/-! ## `@propagate`-aware application — JSON-LD 1.1 API §4.1 / §5.1 -/

/-- Apply a context, honouring `@propagate`. `defaultPropagate` is true
for a node object's own inline `@context` and for a property-scoped
context; type-scoped application has its own combining rule below. -/
def applyContextWithPropagate (loader : Loader) (ac : ActiveContext) (ctxVal : Json)
    (defaultPropagate overrideProtected : Bool) : Res ActiveContext :=
  match contextProcess loader ac ctxVal overrideProtected contextFuel remoteContextFuel [] with
  | .error e => .error e
  | .ok ac1 =>
    let propagate := scanPropagate ctxVal defaultPropagate
    .ok (if propagate then ac1 else ac1.setPrev ac)

/-! ## Type-scoped contexts — JSON-LD 1.1 API §5.1, the `@type` step -/

def insertSorted (x : String) : List String → List String
  | []      => [x]
  | y :: rest => if strLt x y then x :: y :: rest else y :: insertSorted x rest

def sortStrings : List String → List String
  | []        => []
  | x :: rest => insertSorted x (sortStrings rest)

/-- Fold each named type's scoped context onto `acc`, in ascending
lexicographic order of the type names.

`ac0` is the FIXED snapshot of the active context as it stood before any
type-scoped modification (the spec's "type-scoped context"). Every type
NAME's own term definition is looked up against `ac0`, never against the
evolving accumulator — otherwise an earlier type's scoped context can
nullify the entries a later type's name needs to resolve through.

`overrideProtected` is FALSE here: §5.1's `@type` loop invokes Context
Processing without mentioning override protected, so it takes the
algorithm's default. Only PROPERTY-scoped application passes true. -/
def applyTypeScoped (loader : Loader) (ac0 acc : ActiveContext)
    : List String → Bool → Res (ActiveContext × Bool)
  | [], anyNonPropagating => .ok (acc, anyNonPropagating)
  | t :: rest, anyNonPropagating =>
    match findTerm ac0.terms t with
    | some td =>
      match td.scopedContext with
      | some (sc, defDocUrl) =>
        match contextProcess loader (acc.upd (fun c => { c with docUrl := defDocUrl }))
                sc false contextFuel remoteContextFuel [] with
        | .error e => .error e
        | .ok ac1 =>
          let propagate := scanPropagate sc false
          applyTypeScoped loader ac0 ac1 rest (anyNonPropagating || !propagate)
      | none => applyTypeScoped loader ac0 acc rest anyNonPropagating
    | none => applyTypeScoped loader ac0 acc rest anyNonPropagating

/-- `rawTypes` are the `@type` value's string entries AS WRITTEN (term
lookup for type-scoped contexts happens by term NAME). Default propagate
is FALSE, so a non-propagating result pops back to `ac0` — and every
step must point at the SAME `ac0`, so that two non-propagating type
contexts un-apply together. -/
def applyTypeScopedContexts (loader : Loader) (ac0 : ActiveContext) (rawTypes : List String)
    : Res ActiveContext :=
  match applyTypeScoped loader ac0 ac0 (sortStrings rawTypes) false with
  | .error e => .error e
  | .ok (ac1, anyNonPropagating) =>
    .ok (if anyNonPropagating then ac1.setPrev ac0 else ac1)

end L4Factoidal.JSONLD
