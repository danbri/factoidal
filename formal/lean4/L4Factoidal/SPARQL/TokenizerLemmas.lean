/-
L4Factoidal.SPARQL.TokenizerLemmas — the payload-token lemmas.

Groundwork for the SPARQL round-trip theorems, and the place where an
F\*-side IMPOSSIBILITY becomes an ordinary induction.

## The impossibility, and why it is not one here

`formal/fstar/SPARQL11.Parser.AskBgpRoundTrip.fst` sets out to prove
that printing an `ASK { s p o . … }` query and tokenizing the result
gives back the expected tokens. Its own banner reports that stage as
IMPOSSIBLE, with the root cause named precisely:

> `FStar.String.sub`'s specification in this ulib snapshot exposes ONLY
> a length refinement, no lemma relating its output characters to the
> input string's content — so no lemma can be stated, let alone proved,
> connecting a printed payload string back to the `Tok_IRI` / `Tok_VAR`
> / keyword token extract via `substring`.

The module adds that this blocks EVERY payload-carrying token, and that
the companion `TokenRoundTrip` module's own flagged gap has the same
cause one level lower — in the library interface rather than in the
proof technique.

The Lean tokenizer never goes through an opaque substring. It scans over
`List Char` from end to end: `scanIriBody`, `scanWhile` and `scanVarName`
consume a list and return a list, and `String.ofList` is applied once at
the very end. So the relationship between a printed payload and the
scanned token is an equation about `List.append`, and the lemmas below
are proved by induction on the payload with no library obligation at
all.

This is the same shape of difference as the closure length test
(<https://github.com/danbri/factoidal/issues/560>) and the index keys
(<https://github.com/danbri/factoidal/issues/559>): an F\* obligation
that is absent under a different representation. What is new here is
that the F\* module had declared the goal unreachable rather than merely
hard.

## What is proved

* `scanWhile_append` — a run of accepted characters followed by a
  rejected one is scanned exactly, in order.
* `scanIriBody_append` — the body of an IRIREF up to its closing `>`.
* `skipWs_of_ne_ws` — whitespace skipping is the identity in front of a
  character that is neither whitespace nor `#`.
* `nextToken_iri`, `nextToken_var` — the two payload-carrying tokens the
  `ASK` fragment needs, each returning the payload it was printed from.

Every lemma states the RESIDUE too — the character list left for the
next token — because a lemma that only pinned the token would not
compose into a walk over a whole query.
-/
import L4Factoidal.SPARQL.Tokenizer

namespace L4Factoidal.SPARQL

/-! ## `scanWhile` -/

theorem scanWhile_append (p : Char → Bool) :
    ∀ (body : List Char) (pos : Nat) (acc rest : List Char),
      (∀ c ∈ body, p c = true) →
      (∀ c, rest.head? = some c → p c = false) →
      scanWhile p pos (body ++ rest) acc
        = (acc.reverse ++ body, pos + body.length, rest) := by
  intro body
  induction body with
  | nil =>
      intro pos acc rest _ hrest
      cases rest with
      | nil =>
          conv => lhs; unfold scanWhile
          simp
      | cons r rs =>
          have hr : p r = false := hrest r rfl
          conv => lhs; unfold scanWhile
          simp [hr]
  | cons b bs ih =>
      intro pos acc rest hbody hrest
      have hb : p b = true := hbody b (by simp)
      have step : scanWhile p pos ((b :: bs) ++ rest) acc
          = scanWhile p (pos + 1) (bs ++ rest) (b :: acc) := by
        conv => lhs; unfold scanWhile
        simp [hb]
      rw [step, ih (pos + 1) (b :: acc) rest (fun c hc => hbody c (by simp [hc])) hrest]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
                 List.length_cons, Prod.mk.injEq]
      refine ⟨trivial, ?_, trivial⟩
      omega

/-! ## `scanIriBody` -/

theorem scanIriBody_append :
    ∀ (body : List Char) (pos : Nat) (acc rest : List Char),
      (∀ c ∈ body, c ≠ '>' ∧ c ≠ '\\') →
      scanIriBody pos (body ++ '>' :: rest) acc
        = (acc.reverse ++ body, pos + body.length + 1, rest) := by
  intro body
  induction body with
  | nil =>
      intro pos acc rest _
      conv => lhs; unfold scanIriBody
      simp
  | cons b bs ih =>
      intro pos acc rest hbody
      obtain ⟨hgt, hbs⟩ := hbody b (by simp)
      have step : scanIriBody pos ((b :: bs) ++ '>' :: rest) acc
          = scanIriBody (pos + 1) (bs ++ '>' :: rest) (b :: acc) := by
        conv => lhs; unfold scanIriBody
        simp [hgt, hbs]
      rw [step, ih (pos + 1) (b :: acc) rest (fun c hc => hbody c (by simp [hc]))]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
                 List.length_cons, Prod.mk.injEq]
      refine ⟨trivial, ?_, trivial⟩
      omega

/-! ## `skipWs`

In front of a character that is neither whitespace nor a comment start,
whitespace skipping does nothing. This is what lets a payload lemma
begin at the payload's first character rather than at some unknown
offset. -/

theorem skipWsComments_of_ne_ws (f pos : Nat) (c : Char) (rest : List Char)
    (hws : isWsC c = false) (hc : c ≠ '#') :
    skipWsComments (f + 1) pos (c :: rest) = (pos, c :: rest) := by
  simp [skipWsComments, hws, hc]

theorem skipWs_of_ne_ws (pos : Nat) (c : Char) (rest : List Char)
    (hws : isWsC c = false) (hc : c ≠ '#') :
    skipWs pos (c :: rest) = (pos, c :: rest) := by
  simp only [skipWs, List.length_cons]
  exact skipWsComments_of_ne_ws _ pos c rest hws hc

/-! ## Escape processing is the identity on a backslash-free body

The IRI token applies `processIriEscapes` to whatever `scanIriBody`
collected. On a body with no backslash it changes nothing, which is what
lets a printed IRI come back as itself. -/

theorem processIriEscapesRec_id : ∀ (f : Nat) (cs acc : List Char),
    cs.length ≤ f → (∀ c ∈ cs, c ≠ '\\') →
    processIriEscapesRec f cs acc = acc.reverse ++ cs := by
  intro f
  induction f with
  | zero =>
      intro cs acc hf _
      have : cs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hf)
      subst this; simp [processIriEscapesRec]
  | succ k ih =>
      intro cs acc hf hno
      cases cs with
      | nil => simp [processIriEscapesRec]
      | cons c1 r1 =>
          have hc1 : c1 ≠ '\\' := hno c1 (by simp)
          have step : processIriEscapesRec (k + 1) (c1 :: r1) acc
              = processIriEscapesRec k r1 (c1 :: acc) := by
            conv => lhs; unfold processIriEscapesRec
            simp [hc1]
          rw [step, ih r1 (c1 :: acc) (by simp at hf; omega)
                (fun c hc => hno c (by simp [hc]))]
          simp

theorem processIriEscapes_id (cs : List Char) (h : ∀ c ∈ cs, c ≠ '\\') :
    processIriEscapes cs = cs := by
  have hf : cs.length ≤ cs.length + 1 := by omega
  simpa [processIriEscapes] using processIriEscapesRec_id (cs.length + 1) cs [] hf h

/-! ## The two payload tokens

An IRI printed as `<body>` and a variable printed as `?name` each come
back carrying exactly what was printed. These are the statements the F\*
module reports as unstatable; here each is an induction over the payload
and nothing more.

The side conditions are the printer's obligations, and they are the real
content: an IRI body may hold no `>` (it would close the token early) and
no `\\` (it would start an escape); its FIRST character has to be one the
`<` disambiguation reads as an IRIREF rather than as less-than; and a
variable name is drawn from the characters `scanVarName` accepts. -/

/-! The `<` disambiguation accepts a body whose first character is a
letter, `>`, `_`, `/` or `#`. -/
def iriLeadOk (d : Char) : Bool :=
  isAlpha d || d == '>' || d == '_' || d == '/' || d == '#'

theorem nextToken_iri (pos : Nat) (d : Char) (body rest : List Char)
    (hlead : iriLeadOk d = true)
    (hbody : ∀ c ∈ d :: body, c ≠ '>' ∧ c ≠ '\\') :
    nextToken false pos ('<' :: (d :: body) ++ '>' :: rest)
      = (.iri (String.ofList (d :: body)), pos, pos + body.length + 3, rest) := by
  have hne : ∀ c ∈ d :: body, c ≠ '\\' := fun c hc => (hbody c hc).2
  have hd1 : d ≠ '<' := by
    intro h; rw [h] at hlead; simp [iriLeadOk, isAlpha] at hlead
  have hd2 : d ≠ '=' := by
    intro h; rw [h] at hlead; simp [iriLeadOk, isAlpha] at hlead
  have hscan : scanIriBody (pos + 1) (d :: (body ++ '>' :: rest)) []
      = (d :: body, pos + 1 + (d :: body).length + 1, rest) := by
    have := scanIriBody_append (d :: body) (pos + 1) [] rest hbody
    simpa using this
  have hskip : skipWs pos ('<' :: (d :: (body ++ '>' :: rest)))
      = (pos, '<' :: (d :: (body ++ '>' :: rest))) :=
    skipWs_of_ne_ws pos '<' _ (by decide) (by decide)
  simp only [List.cons_append]
  conv => lhs; unfold nextToken
  simp only [hskip, hd1, hd2, reduceIte, beq_self_eq_true, if_true]
  conv => lhs; unfold nextToken.ltCase
  simp only [hlead, if_pos, hscan, processIriEscapes_id _ hne]
  have hlead' : (isAlpha d || d == '>' || d == '_' || d == '/' || d == '#' ||
                 (d == '?' || d == '$') && hasGtBeforeTerminator (d :: (body ++ '>' :: rest)))
                 = true := by
    simp only [iriLeadOk, Bool.or_eq_true] at hlead
    simp only [Bool.or_eq_true]
    exact Or.inl hlead
  split
  · rename_i r h
    exact absurd (List.head_eq_of_cons_eq h) hd1
  · rename_i r h
    exact absurd (List.head_eq_of_cons_eq h) hd1
  · rename_i r h
    exact absurd (List.head_eq_of_cons_eq h) hd2
  · simp only [hlead', if_pos]
    have harith : pos + 1 + (d :: body).length + 1 = pos + body.length + 3 := by
      simp only [List.length_cons]; omega
    rw [harith]

theorem nextToken_var (pos : Nat) (name rest : List Char)
    (hname : name ≠ []) (hok : ∀ c ∈ name, (isAlnum c || c == '_') = true)
    (hrest : ∀ c, rest.head? = some c → (isAlnum c || c == '_') = false) :
    nextToken false pos ('?' :: name ++ rest)
      = (.var (String.ofList name), pos, pos + 1 + name.length, rest) := by
  have hscan : scanVarName (pos + 1) (name ++ rest)
      = (String.ofList name, pos + 1 + name.length, rest) := by
    simp only [scanVarName]
    rw [scanWhile_append _ name (pos + 1) [] rest hok hrest]
    simp
  have hskip : skipWs pos ('?' :: (name ++ rest))
      = (pos, '?' :: (name ++ rest)) :=
    skipWs_of_ne_ws pos '?' _ (by decide) (by decide)
  simp only [List.cons_append]
  conv => lhs; unfold nextToken
  simp only [hskip]
  simp only [hscan, String.length_ofList]
  simp [hname, List.length_eq_zero_iff]

/-! ## Pinned behaviour

The lemmas are universally quantified; these pin the same facts on
concrete input, so a reader can see what the statements say. -/

section Pins

/-! `<http://example/p>` scans as one IRI token carrying its own text,
and leaves the rest of the input alone. -/
#guard
  nextToken false 0 ("<http://example/p> ?x".toList)
    == (Token.iri "http://example/p", 0, 18, " ?x".toList)

/-! `?x` scans as a variable token carrying its name. -/
#guard nextToken false 0 ("?x .".toList) == (Token.var "x", 0, 2, " .".toList)

/-! The `<` disambiguation is real: `< 3` is the less-than operator,
not an unterminated IRI. Without this pin `iriLeadOk` could be read as
decoration. -/
#guard (nextToken false 0 ("< 3".toList)).1 == Token.lt

/-! And a body may not contain `>`: the token ends at the FIRST one.
This is the side condition `nextToken_iri` carries, shown failing. -/
#guard nextToken false 0 ("<a>b>".toList) == (Token.iri "a", 0, 3, "b>".toList)

end Pins

end L4Factoidal.SPARQL
