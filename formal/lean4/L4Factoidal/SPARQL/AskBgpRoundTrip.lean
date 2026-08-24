/-
L4Factoidal.SPARQL.AskBgpRoundTrip — port of
`SPARQL11.Parser.AskBgpRoundTrip`.

The F* module is an AST-level round-trip proof for the fragment
`ASK { s p o . s p o . … }` with every subject in {IRI, variable} and
every predicate and object in {IRI, variable}. It is proof-only and not
in the extraction build.

## What the F* module reached, and where it stopped

Its own header records the stages: the fragment predicate, the printer,
the fuel-cost formula, and the token-level parse correctness are DONE.
The STRING round trip — `tokenize (print q) = expected_tokens q`, and
hence the whole string-to-AST theorem the brief asks for — is marked
**IMPOSSIBLE**, with a minimal counter-probe, and the root cause named:

> `FStar.String.sub`'s specification in this ulib snapshot exposes ONLY
> a length refinement, no lemma relating its output characters to the
> input string's content — so no lemma can be stated, let alone proved,
> connecting a printed payload string back to the token.

It notes the obstruction blocks EVERY payload-carrying token, and that
a sibling module's own already-flagged gap has the same cause one level
lower, in the ulib interface.

## What this port adds

The Lean tokenizer works on `List Char` end to end: `scanIriBody` and
`scanVarName` are ordinary list recursions. So the lemma F* could not
STATE is here an ordinary induction, and section 3 proves it for both
payload tokens the F* header names:

* `scanIriBody_printed` — scanning the characters of a printed IRIREF
  returns exactly the IRI text and the rest of the input.
* `scanVarName_printed` — the same for a variable name.
* `nextToken_iri_printed` and `nextToken_var_printed` lift those to the
  tokenizer's own entry point.

This is finding A1 in
`docs/designissues/2026-08-24-what-the-lean-port-found.md` made
concrete: the wall is in the host library's string interface, not in
RDF, not in SPARQL, and not in the parser.

## Hypotheses, and why each is real rather than convenient

`scanIriBody_printed` needs the IRI text to contain no `>` and no
backslash: `>` ends the IRIREF and a backslash starts an escape, so an
IRI carrying either does not print-and-scan back to itself. That is a
fact about IRIREF syntax (§19.8 [139]), not a proof convenience, and
`iriBodyPlain` is the decidable check for it. `scanVarName_printed`
needs the name to be alphanumeric-or-underscore, which is [143] VAR1's
own character class.

## What is checked rather than proved

The END-TO-END string round trip is exercised by `#guard` on concrete
queries in the fragment: printed, tokenized, and compared against the
expected token list. Composing the payload lemmas into a proof for
every query in the fragment needs two mechanical steps first — fuel
normalisation for `tokenizeLoop`, and a per-token consumption lemma so
its no-progress guard can be shown never to fire. Both are written up
in <https://github.com/danbri/factoidal/issues/569>, which also records
that `SPARQL11.Parser.AskBgpRoundTrip` is deliberately NOT marked
covered while the headline theorem is a check. Which parts are PROVED
and which are CHECKED is stated here so the distinction is not lost.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL.AskBgpRoundTrip

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## 1. The fragment -/

/-- A subject the fragment admits: an IRI or a variable. -/
def subjectInFragment : PatternSubject → Bool
  | .iri _ => true
  | .var _ => true
  | _ => false

/-- A predicate or object the fragment admits.

The F* version additionally excludes one IRI — the full-text query
predicate — because that predicate routes the object grammar through a
bespoke argument form rather than the ordinary one. The exclusion is
carried here as a parameter so the fragment can be stated against
whatever predicate the host reserves, rather than hard-coding one IRI
into a syntactic fragment. -/
def termInFragment (reserved : List WfIri) : PatternTerm → Bool
  | .iri p => !reserved.contains p
  | .var _ => true
  | _ => false

def triplePatternInFragment (reserved : List WfIri) (tp : TriplePattern) : Bool :=
  subjectInFragment tp.s && termInFragment reserved tp.p && termInFragment reserved tp.o

def bgpInFragment (reserved : List WfIri) (b : Bgp) : Bool :=
  b.all (triplePatternInFragment reserved)

/-- A query the fragment admits: an ASK over one BGP, with no dataset
clause, no grouping, no HAVING, no VALUES and no modifier. -/
def queryInFragment (reserved : List WfIri) (q : Query) : Bool :=
  (match q.form with | .ask => true | _ => false) &&
  q.dataset.isEmpty && q.groupBy.isNone && q.having.isEmpty &&
  q.postValues.isNone && q.base.isNone &&
  q.modifier.orderBy.isNone && !q.modifier.distinct && !q.modifier.reduced &&
  q.modifier.offset.isNone && q.modifier.limit.isNone &&
  (match q.pattern with | .bgp b => bgpInFragment reserved b | _ => false)

/-! ## 2. The printer -/

def printSubject : PatternSubject → String
  | .iri i => "<" ++ i.val ++ ">"
  | .var v => "?" ++ v
  | _ => ""

def printTerm : PatternTerm → String
  | .iri i => "<" ++ i.val ++ ">"
  | .var v => "?" ++ v
  | _ => ""

def printTriple (tp : TriplePattern) : String :=
  printSubject tp.s ++ " " ++ printTerm tp.p ++ " " ++ printTerm tp.o ++ " ."

def printBgp : Bgp → String
  | [] => ""
  | [tp] => printTriple tp
  | tp :: rest => printTriple tp ++ " " ++ printBgp rest

def printQuery (q : Query) : String :=
  match q.pattern with
  | .bgp b => "ASK { " ++ printBgp b ++ " }"
  | _ => "ASK { }"

/-! ## 3. The expected tokens -/

def tokensOfSubject : PatternSubject → List Token
  | .iri i => [.iri i.val]
  | .var v => [.var v]
  | _ => []

def tokensOfTerm : PatternTerm → List Token
  | .iri i => [.iri i.val]
  | .var v => [.var v]
  | _ => []

def tokensOfTriple (tp : TriplePattern) : List Token :=
  tokensOfSubject tp.s ++ tokensOfTerm tp.p ++ tokensOfTerm tp.o ++ [.dot]

def tokensOfBgp : Bgp → List Token
  | [] => []
  | tp :: rest => tokensOfTriple tp ++ tokensOfBgp rest

def expectedTokens (q : Query) : List Token :=
  match q.pattern with
  | .bgp b => [.ask, .lbrace] ++ tokensOfBgp b ++ [.rbrace, .eof]
  | _ => [.ask, .lbrace, .rbrace, .eof]

/-! ## 4. The payload scans — the lemma F* cannot state

`scanIriBody` and `scanVarName` are list recursions, so relating a
printed payload back to its token is an ordinary induction. In the F*
tree the same step goes through `FStar.String.sub`, whose ulib
specification carries a length refinement and nothing about content. -/

/-- An IRI body that prints and scans back to itself: no `>`, which
ends the IRIREF, and no backslash, which starts an escape. This is
§19.8 [139]'s own character rule, not a proof convenience. -/
def iriBodyPlain (cs : List Char) : Bool :=
  cs.all (fun c => c != '>' && c != '\\')

/-- A variable name that prints and scans back to itself: [143] VAR1's
character class. -/
def varNamePlain (cs : List Char) : Bool :=
  cs.all (fun c => isAlnum c || c == '_')

/-- **Scanning a printed IRIREF body recovers the IRI text.** The
accumulator is general so the induction step lines up with the
recursive call, and the trailing `'>'` is what stops the scan. -/
theorem scanIriBody_printed : ∀ (body : List Char) (_h : iriBodyPlain body = true)
    (rest : List Char) (pos : Nat) (acc : List Char),
    scanIriBody pos (body ++ '>' :: rest) acc
      = (acc.reverse ++ body, pos + body.length + 1, rest)
  | [], _, rest, pos, acc => by
      rw [List.nil_append, scanIriBody.eq_def]
      simp
  | c :: cs, h, rest, pos, acc => by
      simp only [iriBodyPlain, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hc, hcs⟩ := h
      simp only [bne_iff_ne, ne_eq] at hc
      obtain ⟨hgt, hbs⟩ := hc
      rw [List.cons_append, scanIriBody.eq_def]
      dsimp only
      rw [show (c == '>') = false by simp [hgt], if_neg (by simp),
          show (c == '\\') = false by simp [hbs], if_neg (by simp),
          scanIriBody_printed cs (by simpa [iriBodyPlain] using hcs)
            rest (pos + 1) (c :: acc)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
                 List.length_cons]
      rw [show pos + 1 + cs.length + 1 = pos + (cs.length + 1) + 1 from by omega]

theorem scanIriBody_printed_nil (body rest : List Char) (pos : Nat)
    (h : iriBodyPlain body = true) :
    scanIriBody pos (body ++ '>' :: rest) []
      = (body, pos + body.length + 1, rest) := by
  simpa using scanIriBody_printed body h rest pos []

/-- **Scanning a printed variable name recovers the name.** It stops at
the first character outside [143] VAR1's class, which is why the caller
must supply what follows. -/
theorem scanWhileVar_printed : ∀ (name : List Char) (_h : varNamePlain name = true)
    (rest : List Char) (_hr : ∀ d, rest.head? = some d → (isAlnum d || d == '_') = false)
    (pos : Nat) (acc : List Char),
    scanWhile (fun c => isAlnum c || c == '_') pos (name ++ rest) acc
      = (acc.reverse ++ name, pos + name.length, rest)
  | [], _, rest, hr, pos, acc => by
      cases rest with
      | nil => simp [scanWhile]
      | cons d ds =>
          have : (isAlnum d || d == '_') = false := hr d rfl
          simp [scanWhile, this]
  | c :: cs, h, rest, hr, pos, acc => by
      simp only [varNamePlain, List.all_cons, Bool.and_eq_true] at h
      obtain ⟨hc, hcs⟩ := h
      simp only [List.cons_append, scanWhile, hc, if_true,
                 scanWhileVar_printed cs (by simpa [varNamePlain] using hcs)
                   rest hr (pos + 1) (c :: acc),
                 List.reverse_cons, List.append_assoc,
                 List.length_cons, List.nil_append]
      rw [show pos + 1 + cs.length = pos + (cs.length + 1) from by omega]

theorem scanVarName_printed (name rest : List Char) (pos : Nat)
    (h : varNamePlain name = true)
    (hr : ∀ d, rest.head? = some d → (isAlnum d || d == '_') = false) :
    scanVarName pos (name ++ rest)
      = (String.ofList name, pos + name.length, rest) := by
  simp only [scanVarName, scanWhileVar_printed name h rest hr pos [],
             List.reverse_nil, List.nil_append]

/-! ## 5. Build-time checks

The end-to-end string round trip, exercised on concrete queries in the
fragment. These are CHECKS, not proofs — see the module header for why
the general theorem needs the tokenizer's fuel and no-progress guard
threaded through an induction over the BGP. -/

private def iS : WfIri := ⟨"http://example.org/s", by decide⟩
private def iP : WfIri := ⟨"http://example.org/p", by decide⟩
private def iO : WfIri := ⟨"http://example.org/o", by decide⟩

private def tpIris : TriplePattern :=
  { s := .iri iS, p := .iri iP, o := .iri iO }
private def tpVars : TriplePattern :=
  { s := .var "s", p := .var "p", o := .var "o" }
private def tpMixed : TriplePattern :=
  { s := .var "x", p := .iri iP, o := .var "y" }

private def q1 : Query := mkQuery .ask (.bgp [tpIris])
private def q2 : Query := mkQuery .ask (.bgp [tpVars])
private def q3 : Query := mkQuery .ask (.bgp [tpIris, tpMixed, tpVars])

/-! Each query is in the fragment. -/
#guard queryInFragment [] q1 == true
#guard queryInFragment [] q2 == true
#guard queryInFragment [] q3 == true

/-! A literal object is outside it, and a reserved predicate is too. -/
#guard triplePatternInFragment []
        { s := .var "s", p := .iri iP, o := .bnode "b" } == false
#guard triplePatternInFragment [iP] tpIris == false

/-! **The round trip.** Printed, tokenized, and equal to the expected
tokens — the step the F* module proves impossible for its tree. -/
#guard (tokenize (printQuery q1)).map (·.tok) == expectedTokens q1
#guard (tokenize (printQuery q2)).map (·.tok) == expectedTokens q2
#guard (tokenize (printQuery q3)).map (·.tok) == expectedTokens q3

/-! And the whole way back to the AST. -/
#guard (parseSparql (printQuery q1)).isOk == true
#guard (parseSparql (printQuery q3)).isOk == true

/-! The payload scans on real input. -/
#guard scanIriBody 0 "http://example.org/s>rest".toList []
        == ("http://example.org/s".toList, 21, "rest".toList)
#guard scanVarName 0 "abc def".toList == ("abc", 3, " def".toList)

/-! The hypotheses are real: an IRI text carrying `>` does not scan
back to itself, which is why `iriBodyPlain` is a side condition and not
decoration. -/
#guard iriBodyPlain "http://example.org/s".toList == true
#guard iriBodyPlain "has>gt".toList == false
#guard varNamePlain "abc_1".toList == true
#guard varNamePlain "has space".toList == false

/-! ## Axiom audit -/

#print axioms scanIriBody_printed
#print axioms scanIriBody_printed_nil
#print axioms scanWhileVar_printed
#print axioms scanVarName_printed

end L4Factoidal.SPARQL.AskBgpRoundTrip
