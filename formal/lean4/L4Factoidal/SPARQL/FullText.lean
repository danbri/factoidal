/-
L4Factoidal.SPARQL.FullText — the `text:query` extension, slice 1.

Port of `formal/fstar/SPARQL.FullText.fst` (223 lines). Design:
`docs/designissues/2026-07-05-fulltext-sparql-design.md`.

Slice 1 is exact token match with no scoring: the `text:query` AST, a
pure default tokeniser, and the match predicate over token lists. There
is no `score_bm25` and no `rank_results` — this module makes **no
ranking claim**. A caller applies `limit` in dataset order only.

`SPARQL/Parser.lean` records this module as absent ("whose encoding
lives in `SPARQL.FullText.fst` — no Lean"). It is no longer.

## The tokeniser floor, stated

Lowercase and split on anything that is not ASCII alphanumeric. Non-ASCII
bytes act as word separators. That is the documented floor, not a defect:
Unicode-aware analysis is the design doc's slice-3 `analyze_text` seam.

The F\* module folds case with a self-contained ASCII fold rather than
reusing `SPARQL11.Algebra`'s `string_lowercase_unicode` `assume val`,
because that module ends up depending on this one and reusing it would
cycle the graph.

This port keeps an explicit ASCII fold too, and the reason is NOT the
one I first wrote here. I assumed Lean's `String.toLower` was
Unicode-aware and would widen the floor. **Measured: it is not.**
`"ÉCOLE".toLower` is `"École"` — `Char.toLower` maps `A`–`Z` and
nothing else, so on this input it agrees with the F\* fold exactly.

The fold stays explicit anyway, for a smaller reason: the tokeniser's
floor is a documented part of the slice-1 contract, and it should not be
able to move because a standard-library function's case-folding scope
widened in a later toolchain. A `#guard` pins the current agreement
rather than asserting a difference that does not exist.

## Why the object argument is encoded into a literal

jena-text's list form `(property "term" limit)` is ordinary SPARQL
collection syntax, which the parser desugars into an
`rdf:first`/`rdf:rest` chain in a SIBLING group graph pattern joined to
the main triple — not a second triple pattern in the same BGP that a
per-triple evaluation hook sees. Resolving that generically needs a
pattern-level rewrite pass, and it is not what real magic-property
engines do either: Jena's ARQ intercepts the argument list during
algebra compilation, before it could become literal `rdf:first` matching
against data that has no such triples.

So the parser recognises `text:query` directly, before the generic
collection desugaring runs, and encodes the resolved query into a single
internally-tagged literal that the evaluation hooks decode back out of
the object position. User-visible SPARQL syntax is unaffected.
-/
import L4Factoidal.RDF.Graph

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Vocabulary — jena-text's namespace, reused verbatim for tool
compatibility. -/

def fulltextQueryPred : WfIri := ⟨"http://jena.apache.org/text#query", rfl⟩

/-- The internal marker datatype carrying the parsed `(field, term,
    limit)` tuple through the ordinary literal AST. It never appears in
    user-visible RDF data: the parser is the only producer and the two
    evaluation hooks the only consumers. -/
def fulltextArgsDatatype : WfIri := ⟨"http://jena.apache.org/text#query-args", rfl⟩

/-- `field = none` is jena-text's bare-string two-arity form. -/
structure FulltextQuery where
  field : Option WfIri
  terms : String
  limit : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-! ## The default tokeniser -/

def isAsciiDigitC (c : Char) : Bool := c.toNat ≥ 0x30 && c.toNat ≤ 0x39
def isAsciiUpper (c : Char) : Bool := c.toNat ≥ 0x41 && c.toNat ≤ 0x5A
def isAsciiLowerC (c : Char) : Bool := c.toNat ≥ 0x61 && c.toNat ≤ 0x7A
def isAsciiAlnum (c : Char) : Bool := isAsciiDigitC c || isAsciiUpper c || isAsciiLowerC c

/-- ASCII-only case fold. NOT `String.toLower`, which is Unicode-aware —
    see the module header on why the floor is deliberate. -/
def asciiFoldChar (c : Char) : Char :=
  if isAsciiUpper c then Char.ofNat (c.toNat + 32) else c

def asciiLowercase (s : String) : String :=
  String.ofList (s.toList.map asciiFoldChar)

def splitWordsAcc : List Char → List Char → List String → List String
  | [],      cur, acc =>
      if cur.isEmpty then acc.reverse
      else (String.ofList cur.reverse :: acc).reverse
  | c :: rest, cur, acc =>
      if isAsciiAlnum c then splitWordsAcc rest (c :: cur) acc
      else if cur.isEmpty then splitWordsAcc rest [] acc
      else splitWordsAcc rest [] (String.ofList cur.reverse :: acc)

def defaultTokenizer (s : String) : List String :=
  splitWordsAcc (asciiLowercase s).toList [] []

/-! ## Match semantics — all tokens (AND), the design doc's slice-1
recommendation. -/

def matchTokens (queryTokens candidateTokens : List String) : Bool :=
  queryTokens.all (fun qt => candidateTokens.contains qt)

def literalMatchesQuery (ftq : FulltextQuery) (l : WfLiteral) : Bool :=
  matchTokens (defaultTokenizer ftq.terms) (defaultTokenizer l.val.lexicalForm)

/-! ## The object-argument codec

`unitSep` (ASCII Unit Separator, 0x1F) is a control byte no realistic
search term or field IRI contains. The field and limit ride in the
LEXICAL FORM rather than the datatype IRI, so the user's raw search term
is never itself parsed or escaped — only split out of its two
delimiter-bounded neighbours. -/

def unitSep : Char := Char.ofNat 31
def unitSepStr : String := String.ofList [unitSep]

def splitOnCharAcc (delim : Char) : List Char → List Char → List String → List String
  | [],        cur, acc => (String.ofList cur.reverse :: acc).reverse
  | c :: rest, cur, acc =>
      if c == delim then splitOnCharAcc delim rest [] (String.ofList cur.reverse :: acc)
      else splitOnCharAcc delim rest (c :: cur) acc

def splitOnChar (delim : Char) (s : String) : List String :=
  splitOnCharAcc delim s.toList [] []

def chartsToNatDigits : List Char → Nat → Nat
  | [],        acc => acc
  | c :: rest, acc => chartsToNatDigits rest (acc * 10 + (c.toNat - 0x30))

def stringToNat (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty then none
  else if cs.all isAsciiDigitC then some (chartsToNatDigits cs 0)
  else none

def encodeFulltextLiteral (ftq : FulltextQuery) : WfLiteral :=
  let fieldPart := match ftq.field with | none => "" | some f => f.val
  let limitPart := match ftq.limit with | none => "" | some n => toString n
  ⟨{ lexicalForm := fieldPart ++ unitSepStr ++ ftq.terms ++ unitSepStr ++ limitPart,
     datatype := fulltextArgsDatatype, langTag := none, direction := none }, rfl⟩

def decodeFulltextLiteral (l : WfLiteral) : Option FulltextQuery :=
  if l.val.datatype != fulltextArgsDatatype then none
  else
    match splitOnChar unitSep l.val.lexicalForm with
    | [fieldPart, term, limitPart] =>
        let field : Option WfIri :=
          if fieldPart.isEmpty then none
          else if h : isIri fieldPart then some ⟨fieldPart, h⟩ else none
        let limit := if limitPart.isEmpty then none else stringToNat limitPart
        some { field := field, terms := term, limit := limit }
    | _ => none

/-- The per-candidate filter both evaluation hooks apply after fetching
    the candidate set from the backend. Takes the object as a `Term`
    because that is what a triple's object position holds. -/
def objectMatchesQuery (ftq : FulltextQuery) : Term → Bool
  | .literal l => literalMatchesQuery ftq l
  | _          => false

/-! ## Build-time checks

### The tokeniser -/

#guard defaultTokenizer "Hello, World!" == ["hello", "world"]
#guard defaultTokenizer "" == []
#guard defaultTokenizer "   " == []
#guard defaultTokenizer "a1 B2" == ["a1", "b2"]
#guard defaultTokenizer "one--two__three" == ["one", "two", "three"]

/-! Punctuation at both ends must not produce empty tokens. -/

#guard defaultTokenizer ",hello," == ["hello"]
#guard !(defaultTokenizer ",hello,").contains ""

/-! ### The fold is ASCII, and the floor is deliberate

`É` is uppercase and this fold does NOT touch it; the tokeniser then
treats it as a separator, so `"ÉCOLE"` yields `["cole"]`. That is the
documented slice-1 floor.

Lean's `String.toLower` currently agrees — MEASURED, not assumed:
`"ÉCOLE".toLower` is `"École"`, because `Char.toLower` maps `A`–`Z` and
nothing else. The guard pins that agreement. If a later toolchain widens
`toLower`, this fold does not move with it and the guard says so. -/

#guard asciiLowercase "ÉCOLE" == "École"
#guard "ÉCOLE".toLower == asciiLowercase "ÉCOLE"
#guard defaultTokenizer "ÉCOLE" == ["cole"]

/-! ### Match is AND over tokens, and it is a SUBSET test -/

#guard matchTokens ["a"] ["a", "b"]
#guard matchTokens ["a", "b"] ["a", "b", "c"]
#guard !matchTokens ["a", "z"] ["a", "b"]
#guard matchTokens [] ["a"]          -- an empty query matches anything
#guard !matchTokens ["a"] []

/-! Order does not matter and repetition does not matter — the property
    that makes it a token-set test rather than a substring test. -/

#guard matchTokens ["b", "a"] ["a", "b"]
#guard matchTokens ["a", "a"] ["a"]

/-! ### The codec round-trips, including the empty-field and
    empty-limit forms — those are the two-arity and three-arity jena
    shapes, and a codec that lost them would still round-trip the full
    form. -/

private def rt (q : FulltextQuery) : Bool :=
  decodeFulltextLiteral (encodeFulltextLiteral q) == some q

#guard rt { field := none, terms := "hello", limit := none }
#guard rt { field := none, terms := "hello", limit := some 10 }
#guard rt { field := some ⟨"http://www.w3.org/2000/01/rdf-schema#label", by rfl⟩,
            terms := "hello", limit := none }
#guard rt { field := some ⟨"http://www.w3.org/2000/01/rdf-schema#label", by rfl⟩,
            terms := "hello world", limit := some 5 }

/-! A term containing SPACES and PUNCTUATION survives the codec
    untouched — the whole reason the metadata rides in delimited slots
    rather than being escaped into the datatype IRI. -/

#guard rt { field := none, terms := "a, b; c \"d\"", limit := none }
#guard rt { field := none, terms := "", limit := none }

/-! ### A literal of any other datatype decodes to nothing

The marker datatype is the gate. Without this check the codec would
happily read a user's ordinary string literal as a query. -/

#guard (decodeFulltextLiteral (Literal.string "anything")).isNone
#guard (decodeFulltextLiteral (Literal.langString "x" "en")).isNone

/-! ### Only a literal object can match -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

#guard objectMatchesQuery { field := none, terms := "hello", limit := none }
        (.literal (Literal.string "Hello there"))
#guard !objectMatchesQuery { field := none, terms := "hello", limit := none }
        (.iri ⟨"http://e/hello", exIri "hello"⟩)
#guard !objectMatchesQuery { field := none, terms := "hello", limit := none }
        (.bnode "hello")
#guard !objectMatchesQuery { field := none, terms := "missing", limit := none }
        (.literal (Literal.string "Hello there"))

/-! Matching is on TOKENS, not substrings: `"ell"` must not match
    `"Hello"`. That is the difference between this and a `CONTAINS`
    filter, and it is what "exact token match" in slice 1 means. -/

#guard !objectMatchesQuery { field := none, terms := "ell", limit := none }
        (.literal (Literal.string "Hello there"))

end L4Factoidal.SPARQL
