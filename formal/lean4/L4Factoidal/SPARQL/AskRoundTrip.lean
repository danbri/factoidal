/-
L4Factoidal.SPARQL.AskRoundTrip — printing an ASK query and getting the
same tokens back.

This is the stage `formal/fstar/SPARQL11.Parser.AskBgpRoundTrip.fst`
reports as IMPOSSIBLE. Its banner names the cause: `FStar.String.sub`
exposes only a length refinement in that ulib snapshot, so no lemma can
be STATED connecting a printed payload string back to the token the
scanner extracts through `substring`.

`TokenizerLemmas.lean` removes the obstruction — the Lean scanner works
on `List Char` end to end — and `TokenizeChain.lean` removes the fuel
bookkeeping. What is left is an induction over the basic graph pattern,
and that is this file:

    theorem tokenize_printAsk (b : FragBgp) (h : FragBgpOk b) :
        tokensOf (tokenize (printAsk b)) = expectedTokens b

## The fragment

The same one the F\* module scopes to: `ASK { s p o . … }` with every
position an IRI or a variable — no `PREFIX`, no `BASE`, no `FROM`, no
`VALUES`, no blank nodes, no property paths beyond a bare predicate.

`FragTerm` carries the payload as characters rather than as a `WfIri` or
a variable name, because what the theorem is about is exactly the
relationship between those characters and the token. `FragTermOk` states
the printer's obligations:

* an IRI body is non-empty, holds no `>` (it would close the token
  early) and no `\` (it would start an escape), and its FIRST character
  is one the `<` disambiguation reads as an IRIREF rather than as
  less-than;
* a variable name is non-empty and drawn from the characters
  `scanVarName` accepts.

Those are not incidental. Drop the `>` condition and the printed text
tokenizes to something shorter; drop the lead condition and `<` scans as
the less-than operator. Both are pinned below.

## No whitespace

The printer emits no separators at all: `ASK{<a><b><c>.}`. Every token
boundary in the fragment is unambiguous without one — `>` ends an IRI, a
non-alphanumeric ends a variable name, and `{` is not a name character —
so the theorem needs no reasoning about `skipWs` beyond "the next
character is not whitespace". A printer that inserted spaces would be
just as correct and would make every step carry an extra offset.
-/
import L4Factoidal.SPARQL.TokenizeChain
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL

/-! ## The fragment -/

inductive FragTerm where
  /-- `<body>` — the characters between the angle brackets. -/
  | iri (body : List Char)
  /-- `?name`. -/
  | var (name : List Char)
deriving DecidableEq, Repr

def FragTermOk : FragTerm → Prop
  | .iri body =>
      ∃ d rest, body = d :: rest ∧ iriLeadOk d = true
        ∧ ∀ c ∈ body, c ≠ '>' ∧ c ≠ '\\'
  | .var name => name ≠ [] ∧ ∀ c ∈ name, (isAlnum c || c == '_') = true

structure FragTriple where
  s : FragTerm
  p : FragTerm
  o : FragTerm
deriving DecidableEq, Repr

abbrev FragBgp := List FragTriple

def FragTripleOk (t : FragTriple) : Prop :=
  FragTermOk t.s ∧ FragTermOk t.p ∧ FragTermOk t.o

def FragBgpOk (b : FragBgp) : Prop := ∀ t ∈ b, FragTripleOk t

/-! ## The printer -/

def printTerm : FragTerm → List Char
  | .iri body => '<' :: (body ++ ['>'])
  | .var name => '?' :: name

def printTriple (t : FragTriple) : List Char :=
  printTerm t.s ++ printTerm t.p ++ printTerm t.o ++ ['.']

def printBgpChars : FragBgp → List Char
  | [] => []
  | t :: rest => printTriple t ++ printBgpChars rest

def printAskChars (b : FragBgp) : List Char :=
  'A' :: 'S' :: 'K' :: '{' :: (printBgpChars b ++ ['}'])

def printAsk (b : FragBgp) : String := String.ofList (printAskChars b)

/-! ## The expected tokens -/

def termToken : FragTerm → Token
  | .iri body => .iri (String.ofList body)
  | .var name => .var (String.ofList name)

def tripleTokens (t : FragTriple) : List Token :=
  [termToken t.s, termToken t.p, termToken t.o, .dot]

def bgpTokens : FragBgp → List Token
  | [] => []
  | t :: rest => tripleTokens t ++ bgpTokens rest

def expectedTokens (b : FragBgp) : List Token :=
  Token.ask :: Token.lbrace :: (bgpTokens b ++ [Token.rbrace, Token.eof])

/-! ## Each printed piece scans as one token

`printTerm_next` is the payload step, and it is where
`TokenizerLemmas`' two lemmas are used. The residue is stated because
the walk needs it. -/

theorem printTerm_next (t : FragTerm) (h : FragTermOk t) (pos : Nat)
    (tail : List Char)
    (htail : ∀ c, tail.head? = some c → (isAlnum c || c == '_') = false) :
    ∃ pos', nextToken false pos (printTerm t ++ tail)
              = (termToken t, pos, pos', tail)
            ∧ (printTerm t).length ≥ 1 := by
  cases t with
  | iri body =>
      obtain ⟨d, rest, hb, hlead, hno⟩ := h
      subst hb
      refine ⟨pos + rest.length + 3, ?_, by simp [printTerm]⟩
      have := nextToken_iri pos d rest tail hlead hno
      simpa [printTerm, termToken] using this
  | var name =>
      obtain ⟨hne, hok⟩ := h
      refine ⟨pos + 1 + name.length, ?_, by simp [printTerm]⟩
      have := nextToken_var pos name tail hne hok htail
      simpa [printTerm, termToken] using this

theorem nextToken_dot (pos : Nat) (rest : List Char) :
    nextToken false pos ('.' :: rest) = (Token.dot, pos, pos + 1, rest) := by
  have hskip : skipWs pos ('.' :: rest) = (pos, '.' :: rest) :=
    skipWs_of_ne_ws pos '.' _ (by decide) (by decide)
  conv => lhs; unfold nextToken
  simp [hskip]

theorem nextToken_rbrace (pos : Nat) (rest : List Char) :
    nextToken false pos ('}' :: rest) = (Token.rbrace, pos, pos + 1, rest) := by
  have hskip : skipWs pos ('}' :: rest) = (pos, '}' :: rest) :=
    skipWs_of_ne_ws pos '}' _ (by decide) (by decide)
  conv => lhs; unfold nextToken
  simp [hskip]

theorem nextToken_lbrace (pos : Nat) (rest : List Char) :
    nextToken false pos ('{' :: rest) = (Token.lbrace, pos, pos + 1, rest) := by
  have hskip : skipWs pos ('{' :: rest) = (pos, '{' :: rest) :=
    skipWs_of_ne_ws pos '{' _ (by decide) (by decide)
  conv => lhs; unfold nextToken
  simp only [hskip]
  cases rest with
  | nil => simp
  | cons r rs =>
      by_cases hr : r = '|'
      · subst hr; simp
      · simp [hr]

/-- `ASK` is the KEYWORD path, which the F\* banner names as blocked for
the same reason as the IRI and variable payloads.

Two side conditions, and both are real. The character after the keyword
may not be a name character, or the keyword would be longer; and it may
not be `:`, or the whole thing is a prefixed name rather than a keyword.
`hrest` alone does not give the second, because `:` is not a name
character. -/
theorem nextToken_ask (pos : Nat) (rest : List Char)
    (hrest : ∀ c, rest.head? = some c → isPnChar c = false)
    (hcolon : ∀ c, rest.head? = some c → c ≠ ':') :
    nextToken false pos ('A' :: 'S' :: 'K' :: rest)
      = (Token.ask, pos, pos + 3, rest) := by
  have hscan : scanWhile isPnChar pos ('A' :: 'S' :: 'K' :: rest) []
      = (['A', 'S', 'K'], pos + 3, rest) := by
    have := scanWhile_append isPnChar ['A', 'S', 'K'] pos [] rest (by decide) hrest
    simpa using this
  have hskip : skipWs pos ('A' :: 'S' :: 'K' :: rest)
      = (pos, 'A' :: 'S' :: 'K' :: rest) :=
    skipWs_of_ne_ws pos 'A' _ (by decide) (by decide)
  conv => lhs; unfold nextToken
  simp only [hskip, scanPnameOrKeyword, hscan]
  cases rest with
  | nil => simp [isAlpha, isDigitC, keywordOfUpper, charsUpper, charUpper]
  | cons r rs =>
      have hr : r ≠ ':' := hcolon r rfl
      simp [isAlpha, isDigitC, keywordOfUpper, charsUpper, charUpper, hr]

/-- Every printed term starts with `<` or `?`, and neither is a name
character. That is what discharges the "next character ends the token"
side condition at every step of the walk without a case analysis. -/
theorem printTerm_head_notName (t : FragTerm) (l : List Char) :
    ∀ c, (printTerm t ++ l).head? = some c → (isAlnum c || c == '_') = false := by
  cases t <;> intro c hc <;> simp only [printTerm, List.cons_append,
    List.head?_cons, Option.some.injEq] at hc <;> subst hc <;> decide

theorem printTerm_length_pos (t : FragTerm) : 0 < (printTerm t).length := by
  cases t <;> simp [printTerm]

/-! ## The walk

An induction over the basic graph pattern. `tokensOf` drops positions,
which is what the F\* theorem compares too, and it keeps the statement
about tokens rather than about offsets. -/

theorem tokensOf_bgp : ∀ (b : FragBgp), FragBgpOk b →
    ∀ (f pos : Nat) (acc : List PosToken),
      (printBgpChars b ++ ['}']).length < f →
      tokensOf (tokenizeLoop false f pos (printBgpChars b ++ ['}']) acc)
        = (acc.map PosToken.tok).reverse ++ bgpTokens b ++ [Token.rbrace, Token.eof] := by
  intro b
  induction b with
  | nil =>
      intro _ f pos acc hf
      simp only [printBgpChars, List.nil_append] at hf ⊢
      rw [tokenizeLoop_cons f pos ['}'] [] Token.rbrace pos (pos + 1) acc
            (nextToken_rbrace pos []) (by simp) (by simp) (by omega)]
      rw [tokenizeLoop_nil (f - 1) (pos + 1) _ (by simp at hf; omega)]
      simp [tokensOf, bgpTokens]
  | cons t restB ih =>
      intro hok f pos acc hf
      obtain ⟨hs, hp, ho⟩ := hok t (by simp)
      have hrestOk : FragBgpOk restB := fun u hu => hok u (by simp [hu])
      have hinput : printBgpChars (t :: restB) ++ ['}']
          = printTerm t.s ++ (printTerm t.p ++ (printTerm t.o ++
              ('.' :: (printBgpChars restB ++ ['}'])))) := by
        simp [printBgpChars, printTriple, List.append_assoc]
      rw [hinput] at hf ⊢
      obtain ⟨ps, hns, _⟩ := printTerm_next t.s hs pos _ (printTerm_head_notName t.p _)
      rw [tokenizeLoop_cons f pos _ _ (termToken t.s) pos ps acc hns
            (by cases t.s <;> simp [termToken]) (by simp [printTerm_length_pos])
            (by omega)]
      obtain ⟨pp, hnp, _⟩ := printTerm_next t.p hp ps _ (printTerm_head_notName t.o _)
      rw [tokenizeLoop_cons (f - 1) ps _ _ (termToken t.p) ps pp _ hnp
            (by cases t.p <;> simp [termToken]) (by simp [printTerm_length_pos])
            (by simp only [List.length_append] at hf; omega)]
      obtain ⟨po, hno, _⟩ := printTerm_next t.o ho pp
        ('.' :: (printBgpChars restB ++ ['}']))
        (by intro c hc
            simp only [List.head?_cons, Option.some.injEq] at hc
            subst hc; decide)
      rw [tokenizeLoop_cons (f - 1 - 1) pp _ _ (termToken t.o) pp po _ hno
            (by cases t.o <;> simp [termToken]) (by simp [printTerm_length_pos])
            (by simp only [List.length_append] at hf; omega)]
      rw [tokenizeLoop_cons (f - 1 - 1 - 1) po _ _ Token.dot po (po + 1) _
            (nextToken_dot po _) (by simp) (by simp) (by
              simp only [List.length_append] at hf; omega)]
      rw [ih hrestOk (f - 1 - 1 - 1 - 1) (po + 1) _ (by
        simp only [List.length_append, List.length_cons] at hf ⊢; omega)]
      simp [tokensOf, bgpTokens, tripleTokens, List.append_assoc]

/-! ## The theorem

Printing a fragment `ASK` query and tokenizing the result gives back the
tokens it was printed from. This is the stage the F\* module reports as
IMPOSSIBLE. -/

theorem toList_printAsk (b : FragBgp) : (printAsk b).toList = printAskChars b := by
  simp [printAsk]

theorem tokenize_printAsk (b : FragBgp) (h : FragBgpOk b) :
    tokensOf (tokenize (printAsk b)) = expectedTokens b := by
  simp only [tokenize, toList_printAsk, printAskChars]
  have hlen : ('A' :: 'S' :: 'K' :: '{' :: (printBgpChars b ++ ['}'])).length
      = (printBgpChars b ++ ['}']).length + 4 := by simp
  rw [tokenizeLoop_cons _ 0 _ ('{' :: (printBgpChars b ++ ['}'])) Token.ask 0 3 []
        (nextToken_ask 0 ('{' :: (printBgpChars b ++ ['}']))
          (by intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc
              subst hc; decide)
          (by intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc
              subst hc; decide))
        (by simp) (by simp [hlen]) (by simp [hlen])]
  rw [tokenizeLoop_cons _ 3 _ (printBgpChars b ++ ['}']) Token.lbrace 3 4 _
        (nextToken_lbrace 3 _) (by simp) (by simp) (by simp [hlen])]
  rw [tokensOf_bgp b h _ 4 _ (by simp [hlen])]
  simp [tokensOf, expectedTokens]

/-! ## The parser direction — pinned, and the chain that would prove it

`tokenize_printAsk` above is the TEXT to TOKENS half. The F\* module's
top-level result, `lemma_parse_select_query_ask_bgp`, is the whole
thing: parsing the printed query recovers `GP_BGP b`. It is general,
quantified over any fragment BGP with a trailing token stream and
enough fuel — the same trailing-remainder shape
`Syntax/NTriplesRoundTrip.lean` needed.

That half is NOT proved here. What is pinned below is that it HOLDS on
a concrete instance, run through the shipping `parseSparql`, so the
statement to be proved is known to be true rather than merely hoped
for.

**The chain a proof needs**, in call order, each layer conditional on
the next — this is what the F\* module spends fifteen lemmas on:

1. `pPrologue` returns its input unchanged on a stream whose head is
   `.ask` (the catch-all arm). Small.
2. `resolveIriTokens none ts = ts` when every fragment IRI is already
   absolute. The F\* side carries this as an explicit hypothesis,
   `resolve_relative_iri_tokens None after_eof == after_eof`.
3. `pAskBody` builds the query record around `pGroupGraphPattern`.
4. `pGroupGraphPattern` on `{ … }` delegates to `pTriplesBlock`.
5. `pTriplesBlock` recovers the BGP. This is the hard layer, and where
   the F\* module's `lemma_parse_subject_with_extras_1`,
   `lemma_parse_pred_obj_list_1`, `lemma_parse_object_list_simple_1`,
   `lemma_parse_object_with_extras_1`, `lemma_parse_annotations_dot`,
   `lemma_ggp_add_triple_acc` and `lemma_ggp_join_acc_empty` all live.
   The Lean `pTriplesBlock` calls `pSubjectWithExtras` and
   `pPredObjList`, each of which fans out into property paths,
   collections, blank-node property lists and annotations.
6. Fuel accounting: `ask_bgp_fuel_cost` and
   `lemma_ask_bgp_fuel_cost_n5_fits_entry_fuel` on the F\* side.

So `SPARQL11.Parser.AskBgpRoundTrip` stays on the not-covered list and
no alias was added.

-/

private def probeBgp : FragBgp :=
  [{ s := .iri "http://a/s".toList, p := .iri "http://a/p".toList,
     o := .var "x".toList }]

/-! The printed form, its token stream, and the parse — all three run
on every build. -/
#guard printAsk probeBgp == "ASK{<http://a/s><http://a/p>?x.}"

#guard (match parseSparql (printAsk probeBgp) with
        | .ok q => match q.pattern with
                   | .bgp ts => ts.length == 1
                   | _ => false
        | .error _ => false)

/-! The parse also reports the ASK form, not merely a pattern. -/
#guard (match parseSparql (printAsk probeBgp) with
        | .ok q => match q.form with
                   | .ask => true
                   | _ => false
        | .error _ => false)

/-! ## Pinned behaviour

The theorem is universally quantified over the fragment; these show it
on concrete input, and show what its side conditions are FOR. -/

section Pins

private def iriA : FragTerm := .iri "http://example/a".toList
private def iriP : FragTerm := .iri "http://example/p".toList
private def varX : FragTerm := .var "x".toList

private def oneTriple : FragBgp := [{ s := iriA, p := iriP, o := varX }]

/-! The printed text, in full. -/
#guard printAsk oneTriple == "ASK{<http://example/a><http://example/p>?x.}"

/-! And it tokenizes to the expected tokens — the theorem, on this
input. -/
#guard tokensOf (tokenize (printAsk oneTriple)) == expectedTokens oneTriple

/-! Non-vacuity: the token list is not empty and not just `[eof]`. -/
#guard (expectedTokens oneTriple).length == 8

/-! Two triples chain, which is what the induction step is about. -/
private def twoTriples : FragBgp :=
  [{ s := iriA, p := iriP, o := varX }, { s := varX, p := iriP, o := iriA }]

#guard tokensOf (tokenize (printAsk twoTriples)) == expectedTokens twoTriples
#guard (expectedTokens twoTriples).length == 12

/-! An empty pattern still round-trips: `ASK{}`. -/
#guard printAsk [] == "ASK{}"
#guard tokensOf (tokenize (printAsk [])) == expectedTokens []

/-! ### What the side conditions are for

`FragTermOk` demands an IRI body with no `>`. Printing one that has a
`>` produces text that tokenizes to something SHORTER than the expected
tokens — the IRI closes early. The pin records the failure, so the
hypothesis cannot be mistaken for bookkeeping. -/
private def badIri : FragBgp := [{ s := .iri "a>b".toList, p := iriP, o := varX }]

#guard tokensOf (tokenize (printAsk badIri)) != expectedTokens badIri

/-! And `iriLeadOk`: a body starting with a digit is not read as an
IRIREF at all, because `<` then scans as the less-than operator. -/
private def badLead : FragBgp := [{ s := .iri "1a".toList, p := iriP, o := varX }]

#guard (tokensOf (tokenize (printAsk badLead))).head? == some Token.ask
#guard tokensOf (tokenize (printAsk badLead)) != expectedTokens badLead

end Pins

end L4Factoidal.SPARQL