/-
L4Factoidal.SPARQL.ParserTheorems — kernel-checked facts about the
SPARQL 1.1 tokenizer and the parser's top-level contract.

SCOPE, stated up front so nothing here reads as more than it is. A
parser's interesting property is a round trip — `parseSparql
(printQuery q) = .ok q` — and this port ships no printer for a GENERAL
query, so that theorem is not stated here. Stating it against
`Query.toSse` would be FALSE: SSE is an ALGEBRA notation, not SPARQL
surface syntax, and it is deliberately lossy (`sse_expr`'s aggregate
arm drops the function name and the DISTINCT flag; `sse_ggp`'s VALUES
arm drops every row). The `#guard`s in `ParserTests.lean` and the
corpus run in `Harness/SparqlSyntaxProbe.lean` are what establish the
parser's behaviour; what follows are the properties provable without a
printer.

UPDATED 2026-08-23: two FRAGMENT printers and their round trips DO now
exist, and a reader who stopped at the paragraph above would miss them.

* `SPARQL/TokenRoundTrip.lean` — `tokenize_printTokens`: printing a
  token list from a defined fragment and lexing the text recovers the
  list plus the trailing end-of-input.
* `SPARQL/AskRoundTrip.lean` — `tokenize_printAsk`: printing a fragment
  `ASK { s p o . … }` query and lexing it recovers the expected tokens.

Both stop at the TOKENS. Neither says the parser recovers an AST, so
the sentence above still holds for the statement it is about.

WHY SO FEW `decide` PROOFS — a measurement, not a preference, and one
the next session should not have to repeat. `decide` discharges a goal
by KERNEL evaluation. The tokenizer is structurally recursive through
`Nat`-fuel and `List Char`, so the kernel evaluates it through
`brecOn`, and the cost explodes with input length:

  | goal | kernel cost |
  |---|---|
  | `tokensOf (tokenize "SELECT") = [.select, .eof]` | 0.3 s, 0.43 GB |
  | `tokensOf (tokenize "<http://a/b>") = [.iri …, .eof]` | 72 s, 10.0 GB |
  | ten such theorems in one file | out of memory (`lean` killed, signal 9) |

Twelve characters cost 10 GB. So: concrete-input facts about the
tokenizer are checked with `#guard`, which evaluates through the
COMPILER at build time and costs nothing; a `decide` PROOF is kept
only for the shortest goal, to show the technique is available and to
pin the cost figure above to something the build re-measures. The
general facts below are structural inductions, which the kernel checks
symbolically and cheaply.

Nothing here uses `sorry`, a user `axiom`, `native_decide`, or
`partial`.
-/
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL

/-! ## §19.8: keywords are matched case-insensitively

`keywordOfUpper` sees only the UPPER-CASED lexeme, so case cannot
reach it by construction. What is checkable is the composition
`tokenize`, on concrete inputs. -/

/-- `SELECT` in any case is the same token stream. The one `decide`
PROOF in this file — see the header on why the others are `#guard`s. -/
theorem tokenize_select_case_insensitive :
    tokensOf (tokenize "select") = tokensOf (tokenize "SELECT") := by decide

#guard tokensOf (tokenize "Select") == tokensOf (tokenize "sELEct")
#guard tokensOf (tokenize "select distinct where") ==
       tokensOf (tokenize "SELECT DISTINCT WHERE")
#guard tokensOf (tokenize "order by asc") == tokensOf (tokenize "ORDER BY ASC")
#guard tokensOf (tokenize "optional") == tokensOf (tokenize "OpTiOnAl")

-- The 1.2-only keywords are case-insensitive too, and are NOT keywords
-- in 1.1 mode — which is what keeps 1.1 documents parsing identically
-- under both.
#guard tokensOf (tokenize12 "triple") == tokensOf (tokenize12 "TRIPLE")
#guard tokensOf (tokenize "TRIPLE") == [Token.pname "TRIPLE", Token.eof]
#guard tokensOf (tokenize12 "TRIPLE") == [Token.tripleKw, Token.eof]

/-! ## [139] IRIREF is ONE token

An IRIREF lexeme, however much punctuation it carries, produces a
single `Token.iri`: the `<` disambiguation and the escape expansion
happen INSIDE the terminal, never by splitting it. -/

#guard tokensOf (tokenize "<http://a/b>") == [Token.iri "http://a/b", Token.eof]
#guard (tokensOf (tokenize "<http://a/b?c=d&e#f>")).length == 2
#guard tokensOf (tokenize "<http://a/b?c=d&e#f>") ==
       [Token.iri "http://a/b?c=d&e#f", Token.eof]
#guard tokensOf (tokenize "<>") == [Token.iri "", Token.eof]
-- A `\u` escape inside an IRIREF is expanded in the terminal, so the
-- result is still exactly one token.
#guard tokensOf (tokenize "<http://a/\u0042>") == [Token.iri "http://a/B", Token.eof]
-- The counterexample that makes the five above mean something: a bare
-- `<` that is NOT an IRIREF stays the less-than operator.
#guard tokensOf (tokenize "?a < ?b") ==
       [Token.var "a", Token.lt, Token.var "b", Token.eof]

/-! ## Every token stream ends with `eof`

A general fact, by induction on the tokenizer's fuel: whatever the
input, `tokenize` terminates the stream with an `eof` token, so
`peekTok` past the end and `peekTok` at the end agree and no consumer
has to special-case an empty stream. -/

/-- The loop always appends `eof` last. Induction on `fuel`; every
base case builds `(⟨.eof, _⟩ :: acc).reverse`, whose last element is
that `eof`. -/
theorem tokenizeLoop_ends_with_eof (v12 : Bool) :
    ∀ (fuel pos : Nat) (cs : List Char) (acc : List PosToken),
      ((tokenizeLoop v12 fuel pos cs acc).getLast?).map PosToken.tok = some Token.eof := by
  intro fuel
  induction fuel with
  | zero =>
    intro pos cs acc
    simp [tokenizeLoop, List.reverse_cons]
  | succ f ih =>
    intro pos cs acc
    unfold tokenizeLoop
    repeat' split
    all_goals first
      | exact ih _ _ _
      | simp [List.reverse_cons]

/-- `tokenize` therefore ends with `eof` for every input. -/
theorem tokenize_ends_with_eof (s : String) :
    ((tokenize s).getLast?).map PosToken.tok = some Token.eof :=
  tokenizeLoop_ends_with_eof false _ _ _ _

/-- And so does the SPARQL 1.2 tokenizer. -/
theorem tokenize12_ends_with_eof (s : String) :
    ((tokenize12 s).getLast?).map PosToken.tok = some Token.eof :=
  tokenizeLoop_ends_with_eof true _ _ _ _

/-- A corollary: no token stream this tokenizer produces is empty. -/
theorem tokenize_nonempty (s : String) : tokenize s ≠ [] := by
  intro h
  have := tokenize_ends_with_eof s
  rw [h] at this
  simp at this

/-! ## Stream primitives -/

/-- `peekTok` reads `eof` past the end, so the F* `parse_peek`'s
total-function shape carries over. -/
theorem peekTok_nil : peekTok [] = Token.eof := rfl

/-- `advTok` never grows the stream — the property that makes every
`fuel`-bounded loop below actually make progress. -/
theorem advTok_length_le (ts : TStream) : (advTok ts).length ≤ ts.length := by
  cases ts <;> simp [advTok]

/-- On a non-empty stream `advTok` consumes exactly one token. -/
theorem advTok_length_succ (pt : PosToken) (rest : TStream) :
    (advTok (pt :: rest)).length + 1 = (pt :: rest).length := by
  simp [advTok]

/-- `expectTok` succeeds exactly when the head matches, and then
consumes it. -/
theorem expectTok_ok_iff (t : Token) (ts : TStream) :
    (∃ r, expectTok t ts = .ok ((), r)) ↔ peekTok ts == t := by
  constructor
  · rintro ⟨r, h⟩
    unfold expectTok at h
    split at h
    · assumption
    · simp [pErr] at h
  · intro h
    refine ⟨advTok ts, ?_⟩
    unfold expectTok
    rw [if_pos h]

/-- `tokensOnlyEof` holds of the empty stream. -/
theorem tokensOnlyEof_nil : tokensOnlyEof [] = true := rfl

/-! ## The top-level contract

Two properties `parseSparql` establishes for every query it ACCEPTS.

A note on tactic choice, because it cost a build here. `split at h`
takes the scrutinee to weak head normal form, and the scrutinee
contains `pSelectQuery topFuel …` with `topFuel = 10000` — the F*'s
own seed. Weak-head-normalising that unfolds ten thousand fuel levels
of a mutual block and exhausted memory (`lean` killed with signal 9).
The proofs below therefore use `cases h : e`, which cases on the
`Except` CONSTRUCTOR and never evaluates `e`, plus `simp only` with
the resulting equation as a rewrite. Same shape, no evaluation. -/

/-- Every accepted query passes the §19.6 blank-node scope check
(`validate_bnode_scope_top`), so nothing downstream re-checks it. -/
theorem parseSparql_bnodeScope_valid
    (fuel : Nat) (text : String) (base : Option String) (v : SparqlVersion) (q : Query)
    (h : parseSparqlWith fuel text base v = .ok q) : validateBnodeScopeTop q = true := by
  rw [parseSparqlWith] at h
  cases hf : firstInvalidToken (tokenizeAt v text) with
  | some e => simp only [hf] at h; exact absurd h (by simp)
  | none =>
    simp only [hf] at h
    cases hp : pSelectQuery fuel { v12 := v.is12 } base (tokenizeAt v text) with
    | error e => simp only [hp] at h; exact absurd h (by simp)
    | ok r =>
      obtain ⟨q', rest⟩ := r
      simp only [hp] at h
      by_cases h1 : tokensOnlyEof rest = true
      · by_cases h2 : validateBnodeScopeTop q' = true
        · simp only [h1, h2] at h
          simp at h
          subst h; exact h2
        · simp only [Bool.not_eq_true] at h2
          simp only [h1, h2] at h
          simp at h
      · simp only [Bool.not_eq_true] at h1
        simp only [h1] at h
        simp at h

/-- Every accepted query consumed its whole token stream: what is left
is `eof` padding only. A trailing second query is the F*'s "unexpected
tokens after query", never a silently ignored suffix. -/
theorem parseSparql_consumes_stream
    (fuel : Nat) (text : String) (base : Option String) (v : SparqlVersion) (q : Query)
    (h : parseSparqlWith fuel text base v = .ok q) :
    ∃ q' rest, pSelectQuery fuel { v12 := v.is12 } base (tokenizeAt v text)
                 = .ok (q', rest) ∧ tokensOnlyEof rest = true := by
  rw [parseSparqlWith] at h
  cases hf : firstInvalidToken (tokenizeAt v text) with
  | some e => simp only [hf] at h; exact absurd h (by simp)
  | none =>
    simp only [hf] at h
    cases hp : pSelectQuery fuel { v12 := v.is12 } base (tokenizeAt v text) with
    | error e => simp only [hp] at h; exact absurd h (by simp)
    | ok r =>
      obtain ⟨q', rest⟩ := r
      simp only [hp] at h
      by_cases h1 : tokensOnlyEof rest = true
      · exact ⟨q', rest, rfl, h1⟩
      · simp only [Bool.not_eq_true] at h1
        simp only [h1] at h
        simp at h

/-! ## Rejections are rejections

Concrete witnesses that the well-formedness gates are load-bearing.
These are `#guard`s, NOT `theorem … := by decide`, and the reason is
worth recording: `decide` discharges a goal by KERNEL evaluation, and
`parseSparql` runs its recursive-descent block at `topFuel = 10000`
(the F*'s own seed). Kernel-unfolding ten thousand fuel levels of a
mutual block exhausted memory here — `lean` was killed with signal 9.
`#guard` evaluates through the compiler instead, so it checks the
same fact at build time for no cost. The parser's real corpus
evidence is `Harness/SparqlSyntaxProbe.lean`. -/

-- §18.2.4.1: `SELECT *` with GROUP BY.
#guard errMsg "SELECT * { ?s ?p ?o } GROUP BY ?s" == "SELECT * not allowed with GROUP BY"

-- §18.5.1: an aggregate may not nest inside an aggregate.
#guard errMsg "SELECT (COUNT(SUM(?o)) AS ?c) { ?s ?p ?o }" ==
  "nested aggregate in aggregate argument"

-- Jena's LATERAL rule, with the message text the repo's tests grep for.
#guard errMsg "SELECT * { ?s ?p ?o LATERAL { BIND(1 AS ?o) } }" ==
  "LATERAL: right-hand side reassigns a variable already bound by the left-hand pattern"

-- §19.6: a blank-node label may not span two UNION scopes.
#guard errMsg "SELECT * { { ?s <http://a/p> _:b } UNION { _:b <http://a/q> ?o } }" ==
  "blank node label reused across graph-pattern scope"

-- The trailing-junk gate.
#guard errMsg "ASK { } ASK { }" == "unexpected tokens after query"

/-! ## Axiom audit

Every theorem above should rest on Lean's standard foundations only —
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no user
axiom, no `Lean.ofReduceBool` (which `native_decide` would introduce).
These lines print in the build log. -/

#print axioms tokenize_ends_with_eof
#print axioms tokenize_select_case_insensitive
#print axioms expectTok_ok_iff
#print axioms parseSparql_bnodeScope_valid
#print axioms parseSparql_consumes_stream

end L4Factoidal.SPARQL
