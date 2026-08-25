/-
L4Factoidal.SPARQL.TokenRoundTrip — printing a token list and lexing it
back.

Port of `formal/fstar/SPARQL11.Parser.TokenRoundTrip.fst` (1,391 lines):
print a token list from a defined fragment, re-tokenize the text, and
recover the original list plus the tokenizer's trailing end-of-input.

## The fragment, and how it compares to the F\* one

The F\* module's fragment is the single-character delimiters, the
single- and two-character operators, and nothing else. Its FINDING
records why the keyword tokens were left out:

> Adding payload-free keywords needs a DIFFERENT print/round-trip
> argument than the delimiter fragment: the lexer reaches those tokens
> via `scan_word` + `keyword_of_word` … so the combinator lemmas below
> … do not transfer.

and the companion `AskBgpRoundTrip.fst` later reports that the real
obstruction is one level lower, in `FStar.String.sub`'s interface, and
blocks every PAYLOAD-carrying token as well.

Neither obstruction exists here — `TokenizerLemmas.lean` says why — so
this fragment is WIDER than the F\* one in both directions the F\*
module names: it includes the payload-carrying `iri` and `var` tokens
and the `a` and `ASK` keywords alongside the delimiters and operators.

## Separators

Every token is printed followed by ONE space, which is the same
disambiguation the F\* module uses ("a terminating space after the
candidate rules out any longer lexeme"). `SkipWsLemmas.nextToken_cons_ws`
is what lets the walk step over that space, and it needed a fuel
argument of its own because `skipWs` seeds its fuel from the remaining
input length.

## What the theorem does NOT say

It says the tokenizer recovers a printed token list. It does not say the
PARSER recovers an AST — that is `AskBgpRoundTrip.lean`'s question, and
`ParserTheorems.lean`'s header explains why the general form of it is
not available.
-/
import L4Factoidal.SPARQL.SkipWsLemmas
import L4Factoidal.SPARQL.AskRoundTrip

namespace L4Factoidal.SPARQL

/-! ## The single-character tokens

One table, so the case analysis below is over the table rather than over
the tokenizer's if-chain. -/

def tokChar : Token → Option Char
  | .lbrace   => some '{'
  | .rbrace   => some '}'
  | .lparen   => some '('
  | .rparen   => some ')'
  | .lbracket => some '['
  | .rbracket => some ']'
  | .dot      => some '.'
  | .semi     => some ';'
  | .comma    => some ','
  | .star     => some '*'
  | .slash    => some '/'
  | .pipe     => some '|'
  | .caret    => some '^'
  | .bang     => some '!'
  | .qmark    => some '?'
  | .plus     => some '+'
  | .minusOp  => some '-'
  | .eq       => some '='
  | .lt       => some '<'
  | .gt       => some '>'
  | _         => none

/-- Every single-character token scans as itself when a space follows.
The space is what rules out the longer lexemes: `<` is the less-than
operator rather than an IRIREF, `?` is a bare question mark rather than
a variable, `!` is negation rather than `!=`, and so on. -/
theorem nextToken_tokChar : ∀ (t : Token) (c : Char), tokChar t = some c →
    ∀ (pos : Nat) (rest : List Char),
      nextToken false pos (c :: ' ' :: rest) = (t, pos, pos + 1, ' ' :: rest) := by
  intro t c h pos rest
  cases t <;> simp only [tokChar, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;>
    (conv => lhs; unfold nextToken) <;>
    simp [skipWs, skipWsComments, isWsC, nextToken.ltCase, isAlpha, scanVarName,
          scanWhile, isAlnum, isDigitC]

/-! ## The payload tokens and two keywords -/

theorem nextToken_iri_tok (pos : Nat) (d : Char) (body tail : List Char)
    (hlead : iriLeadOk d = true) (hbody : ∀ c ∈ d :: body, c ≠ '>' ∧ c ≠ '\\') :
    nextToken false pos ('<' :: ((d :: body) ++ ['>']) ++ tail)
      = (Token.iri (String.ofList (d :: body)), pos, pos + body.length + 3, tail) := by
  have := nextToken_iri pos d body tail hlead hbody
  simpa [List.append_assoc] using this

theorem nextToken_a (pos : Nat) (rest : List Char) :
    nextToken false pos ('a' :: ' ' :: rest) = (Token.a, pos, pos + 1, ' ' :: rest) := by
  have hscan : scanWhile isPnChar pos ('a' :: ' ' :: rest) []
      = (['a'], pos + 1, ' ' :: rest) := by
    have := scanWhile_append isPnChar ['a'] pos [] (' ' :: rest) (by decide)
      (by intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc
          subst hc; decide)
    simpa using this
  have hskip : skipWs pos ('a' :: ' ' :: rest) = (pos, 'a' :: ' ' :: rest) :=
    skipWs_of_ne_ws pos 'a' _ (by decide) (by decide)
  conv => lhs; unfold nextToken
  simp [hskip, scanPnameOrKeyword, hscan, isAlpha, isDigitC, keywordOfUpper,
        charsUpper, charUpper]

/-! ## The printed form -/

def printTok : Token → List Char
  | .iri s => '<' :: (s.toList ++ ['>'])
  | .var s => '?' :: s.toList
  | .a     => ['a']
  | .ask   => ['A', 'S', 'K']
  | t      => match tokChar t with
              | some c => [c]
              | none   => []

/-- The fragment, written as a DISJUNCTION rather than as a match on
the token. A match would not reduce for a token that is still a
variable, which is exactly the position every case of the lemma below
starts from. -/
def TokOk (t : Token) : Prop :=
  (∃ c, tokChar t = some c)
  ∨ (∃ s d body, t = .iri s ∧ s.toList = d :: body ∧ iriLeadOk d = true
        ∧ ∀ c ∈ s.toList, c ≠ '>' ∧ c ≠ '\\')
  ∨ (∃ s, t = .var s ∧ s.toList ≠ []
        ∧ ∀ c ∈ s.toList, (isAlnum c || c == '_') = true)
  ∨ t = .a ∨ t = .ask

/-- A leading space, one after every token, and one at the end. The
space is the disambiguation: it rules out the longer lexeme at every
boundary, the same device the F\* module uses. -/
def printTokens : List Token → List Char
  | []      => [' ']
  | t :: ts => ' ' :: (printTok t ++ printTokens ts)

theorem printTokens_head (ts : List Token) : (printTokens ts).head? = some ' ' := by
  cases ts <;> rfl

theorem printTokens_length_pos (ts : List Token) : 0 < (printTokens ts).length := by
  cases ts <;> simp [printTokens]

/-! ## One printed token scans back to itself -/

theorem nextToken_printTok_single (t : Token) (c : Char) (hc : tokChar t = some c)
    (pos : Nat) (sp : List Char) :
    nextToken false pos (printTok t ++ (' ' :: sp)) = (t, pos, pos + 1, ' ' :: sp) := by
  have hp : printTok t = [c] := by
    cases t <;> simp only [tokChar, Option.some.injEq, reduceCtorEq] at hc <;>
      subst hc <;> rfl
  rw [hp]
  simpa using nextToken_tokChar t c hc pos sp

theorem nextToken_printTok (t : Token) (h : TokOk t) (pos : Nat) (ts : List Token) :
    ∃ pos', nextToken false pos (printTok t ++ printTokens ts)
              = (t, pos, pos', printTokens ts) := by
  obtain ⟨sp, hsp⟩ : ∃ sp, printTokens ts = ' ' :: sp := by
    cases ts with
    | nil => exact ⟨[], rfl⟩
    | cons u us => exact ⟨printTok u ++ printTokens us, rfl⟩
  rcases h with ⟨c, hc⟩ | ⟨s, d, body, ht, hs, hlead, hno⟩ | ⟨s, ht, hne, hok⟩ | ht | ht
  · exact ⟨pos + 1, by rw [hsp]; exact nextToken_printTok_single t c hc pos sp⟩
  · subst ht
    refine ⟨pos + body.length + 3, ?_⟩
    have hp : printTok (Token.iri s) = '<' :: ((d :: body) ++ ['>']) := by
      simp [printTok, hs]
    rw [hp]
    have hsl : String.ofList (d :: body) = s := by rw [← hs]; simp
    have := nextToken_iri_tok pos d body (printTokens ts) hlead (by rw [← hs]; exact hno)
    rw [hsl] at this
    simpa [hs, List.append_assoc] using this
  · subst ht
    refine ⟨pos + 1 + s.toList.length, ?_⟩
    have := nextToken_var pos s.toList (printTokens ts) hne hok
      (by intro c hc; rw [printTokens_head ts] at hc
          simp only [Option.some.injEq] at hc; subst hc; decide)
    simpa [printTok] using this
  · subst ht
    exact ⟨pos + 1, by rw [hsp]; simpa [printTok] using nextToken_a pos sp⟩
  · subst ht
    refine ⟨pos + 3, ?_⟩
    rw [hsp]
    have := nextToken_ask pos (' ' :: sp)
      (by intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc
          subst hc; decide)
      (by intro c hc; simp only [List.head?_cons, Option.some.injEq] at hc
          subst hc; decide)
    simpa [printTok] using this

/-! ## The walk, and the theorem -/

theorem TokOk_ne_eof (t : Token) (h : TokOk t) : t ≠ Token.eof := by
  rcases h with ⟨c, hc⟩ | ⟨s, d, body, ht, _⟩ | ⟨s, ht, _⟩ | ht | ht
  · intro he; subst he; simp [tokChar] at hc
  · intro he; subst he; simp at ht
  · intro he; subst he; simp at ht
  · intro he; rw [he] at ht; simp at ht
  · intro he; rw [he] at ht; simp at ht

theorem nextToken_lastSpace (pos : Nat) :
    nextToken false pos [' '] = (Token.eof, pos + 1, pos + 1, []) := by
  rw [nextToken_cons_ws pos ' ' [] (by decide)]
  simp [nextToken, skipWs, skipWsComments]

theorem tokensOf_printTokens_loop : ∀ (ts : List Token), (∀ t ∈ ts, TokOk t) →
    ∀ (f pos : Nat) (acc : List PosToken),
      (printTokens ts).length < f →
      tokensOf (tokenizeLoop false f pos (printTokens ts) acc)
        = (acc.map PosToken.tok).reverse ++ ts ++ [Token.eof] := by
  intro ts
  induction ts with
  | nil =>
      intro _ f pos acc hf
      cases f with
      | zero => simp [printTokens] at hf
      | succ g =>
          conv => lhs; unfold tokenizeLoop
          simp only [printTokens, nextToken_lastSpace]
          simp [tokensOf]
  | cons t ts ih =>
      intro hok f pos acc hf
      have htok : TokOk t := hok t (by simp)
      have hrest : ∀ u ∈ ts, TokOk u := fun u hu => hok u (by simp [hu])
      obtain ⟨pos', hnext⟩ := nextToken_printTok t htok (pos + 1) ts
      have hstep : nextToken false pos (printTokens (t :: ts))
          = (t, pos + 1, pos', printTokens ts) := by
        simp only [printTokens]
        rw [nextToken_cons_ws pos ' ' _ (by decide)]
        exact hnext
      rw [tokenizeLoop_cons f pos _ (printTokens ts) t (pos + 1) pos' acc hstep
            (TokOk_ne_eof t htok)
            (by simp only [printTokens, List.length_cons, List.length_append]; omega)
            (by simp only [printTokens, List.length_cons] at hf; omega)]
      rw [ih hrest (f - 1) pos' _
            (by simp only [printTokens, List.length_cons, List.length_append] at hf ⊢
                omega)]
      simp [tokensOf]

/-- **The round trip.** Printing a token list from the fragment and
tokenizing the text recovers the list, plus the tokenizer's own trailing
end-of-input sentinel. -/
theorem tokenize_printTokens (ts : List Token) (h : ∀ t ∈ ts, TokOk t) :
    tokensOf (tokenize (String.ofList (printTokens ts))) = ts ++ [Token.eof] := by
  have hlist : (String.ofList (printTokens ts)).toList = printTokens ts := by simp
  simp only [tokenize, hlist]
  rw [tokensOf_printTokens_loop ts h _ 0 [] (by omega)]
  simp

/-! ## Pinned behaviour -/

section Pins

private def sampleIri : Token := .iri "http://example/p"
private def sampleVar : Token := .var "x"

private def sample : List Token :=
  [Token.ask, Token.lbrace, sampleVar, sampleIri, sampleVar, Token.dot,
   Token.rbrace]

/-! The printed text, in full — a leading space, one after every token,
and one at the end. -/
#guard String.ofList (printTokens sample)
      == " ASK { ?x <http://example/p> ?x . } "

/-! And it lexes back to the list plus the sentinel — the theorem, on
this input. -/
#guard tokensOf (tokenize (String.ofList (printTokens sample)))
      == sample ++ [Token.eof]

/-! Non-vacuity: the list is not empty, and the round trip is not the
identity on an empty list only. -/
#guard sample.length == 7

/-! Every single-character token in the table round-trips. This is the
fragment the F\* module covers; the four above it are the widening. -/
#guard
  let singles : List Token :=
    [.lbrace, .rbrace, .lparen, .rparen, .lbracket, .rbracket, .dot, .semi,
     .comma, .star, .slash, .pipe, .caret, .bang, .qmark, .plus, .minusOp,
     .eq, .lt, .gt]
  tokensOf (tokenize (String.ofList (printTokens singles))) == singles ++ [Token.eof]

/-! The space really is load-bearing: `<` with no space after it starts
an IRIREF, and `!` with `=` after it is a single `!=` token. Printing
without separators would not round-trip. -/
#guard tokensOf (tokenize "<a>") == [Token.iri "a", Token.eof]
#guard tokensOf (tokenize "!=") == [Token.ne, Token.eof]
#guard tokensOf (tokenize "! =") == [Token.bang, Token.eq, Token.eof]

/-! The empty list prints to one space and lexes to just the sentinel. -/
#guard String.ofList (printTokens []) == " "
#guard tokensOf (tokenize (String.ofList (printTokens []))) == [Token.eof]

end Pins

end L4Factoidal.SPARQL
