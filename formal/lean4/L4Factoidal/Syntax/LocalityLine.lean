/-
L4Factoidal.Syntax.LocalityLine — locality for the line-level N-Triples
and N-Quads readers.

Continues `Syntax.Locality` (IRIREF, blank node) and
`Syntax.LocalityLiteral` (string literal, language-tag run) up to the
readers a whole statement is built from.

⚠️ Three of these carry side conditions, and each one is a real
divergence, not bookkeeping:

* `skipWs_local` — a whitespace run that reached the end of the input
  keeps running into whatever is appended.
* `readLangTag_local` — same, for the language-tag run.
* `readLiteral11_local` — in RDF 1.1 the reader branches on what follows
  the closing quote: `@` starts a language tag, `^^` starts a datatype,
  anything else ends the literal as `xsd:string`. A remainder of `[]` or
  of exactly `['^']` therefore has its branch DECIDED by what comes
  next, so both are excluded.

Every one of those is satisfied when the reader is looking at a line
that still has its terminator, which is the case the streaming N-Quads
fold needs.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Syntax.LocalityLiteral
import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.Syntax
open L4Factoidal.RDF

/-! ## Whitespace runs -/

/-- ⚠️ A run that stopped inside the input. A run that reached the end
keeps going into whatever is appended. -/
theorem skipWs_local (pos : Nat) (cs extra : List Char)
    (hne : (skipWs pos cs).2 ≠ []) :
    skipWs pos (cs ++ extra) = ((skipWs pos cs).1, (skipWs pos cs).2 ++ extra) := by
  simp only [skipWs] at hne ⊢
  cases hsp : cs.span isNtWs with
  | mk taken dropped =>
      rw [hsp] at hne
      simp only at hne
      cases hd : dropped with
      | nil => rw [hd] at hne; simp at hne
      | cons a t =>
          rw [span_append_of_stopped isNtWs cs taken a t extra (by rw [hsp, hd])]
          simp [hsp, hd]

/-! ## Language tags -/

/-- ⚠️ Same side condition as `readLangTagRun_local`, in the form the
callers have: a non-empty remainder. -/
theorem readLangTag_local (pos : Nat) (cs extra : List Char) (s : String)
    (p' : Nat) (rest : List Char)
    (h : readLangTag pos cs = .ok (s, p', rest)) (hne : rest ≠ []) :
    readLangTag pos (cs ++ extra) = .ok (s, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readLangTag] at h
  | cons c0 t =>
    by_cases ha : c0 = '@'
    · subst ha
      cases t with
      | nil => simp [readLangTag] at h
      | cons c1 t2 =>
        simp only [readLangTag, List.cons_append] at h ⊢
        cases hst : isLangStart c1 with
        | false => simp [hst] at h
        | true =>
          simp only [hst, Bool.not_true, Bool.false_eq_true, if_neg,
                     not_false_eq_true] at h ⊢
          have hEq : readLangTagRun (pos + 1) (c1 :: t2) = (s, p', rest) := by
            simpa using h
          have hspan : ((c1 :: t2).span isLangChar).2 = rest := by
            have : (readLangTagRun (pos + 1) (c1 :: t2)).2.2 = rest := by rw [hEq]
            simpa [readLangTagRun] using this
          cases hd : rest with
          | nil => exact absurd hd hne
          | cons a t3 =>
              have hloc := readLangTagRun_local (pos + 1) (c1 :: t2) extra a t3
                (by rw [hspan, hd])
              rw [← List.cons_append, hloc, hEq]
              simp [hd]
    · simp [readLangTag, ha] at h

/-! ## Datatype IRIs

Unconditional: `^^` is two literal characters and the IRI that follows
is closed by `>`. -/

theorem readDatatype_local (pos : Nat) (cs extra : List Char) (wi : WfIri)
    (p' : Nat) (rest : List Char)
    (h : readDatatype pos cs = .ok (wi, p', rest)) :
    readDatatype pos (cs ++ extra) = .ok (wi, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readDatatype] at h
  | cons c0 t =>
    by_cases h0 : c0 = '^'
    · subst h0
      cases t with
      | nil => simp [readDatatype] at h
      | cons c1 t2 =>
        by_cases h1 : c1 = '^'
        · subst h1
          simp only [readDatatype, List.cons_append] at h ⊢
          cases hr : readIriRef (pos + 2) t2 with
          | error e => rw [hr] at h; simp at h
          | ok v =>
              obtain ⟨iriStr, pos2, rest2⟩ := v
              rw [hr] at h
              rw [readIriRef_local (pos + 2) t2 extra iriStr pos2 rest2 hr]
              simp only at h ⊢
              cases hm : mkIri pos iriStr with
              | error e => simp_all
              | ok wi2 => simp_all
        · simp [readDatatype, h1] at h
    · simp [readDatatype, h0] at h

/-! ## Literals (RDF 1.1)

⚠️ Two exclusions, both real. A remainder of `[]` gets its branch from
whatever is appended; a remainder of exactly `['^']` becomes a `^^`
datatype as soon as one more `^` arrives. -/

theorem readLiteral11_local (pos : Nat) (cs extra : List Char) (wl : WfLiteral)
    (p' : Nat) (rest : List Char)
    (h : readLiteral .rdf11 pos cs = .ok (wl, p', rest))
    (hne : rest ≠ []) (hnc : rest ≠ ['^']) :
    readLiteral .rdf11 pos (cs ++ extra) = .ok (wl, p', rest ++ extra) := by
  simp only [readLiteral] at h ⊢
  cases hq : readStringLiteralQuoted pos cs with
  | error e => simp_all
  | ok v =>
      obtain ⟨lex, pos1, r1⟩ := v
      rw [readStringLiteralQuoted_local pos cs extra lex pos1 r1 hq]
      rw [hq] at h
      simp only at h ⊢
      cases hr1 : r1 with
      | nil =>
          rw [hr1] at h
          simp only at h
          split at h <;> simp_all
      | cons a t =>
          by_cases hat : a = '@'
          · subst hat
            rw [hr1] at h
            simp only [List.cons_append] at h ⊢
            split at h
            · simp_all
            · rename_i tag pos2 rest2 he
              have hloc := readLangTag_local pos1 ('@' :: t) extra tag pos2 rest2 he
                (by intro hc; subst hc; split at h <;> simp_all)
              rw [List.cons_append] at hloc
              rw [hloc]
              split at h <;> simp_all
          · by_cases hac : a = '^'
            · subst hac
              cases t with
              | nil =>
                  rw [hr1] at h
                  split at h <;> (try split at h) <;> simp_all
              | cons b t2 =>
                  by_cases hbc : b = '^'
                  · subst hbc
                    rw [hr1] at h
                    simp only [List.cons_append] at h ⊢
                    split at h
                    · simp_all
                    · rename_i dt pos2 rest2 he
                      have hloc := readDatatype_local pos1 ('^' :: '^' :: t2) extra dt
                        pos2 rest2 he
                      rw [List.cons_append, List.cons_append] at hloc
                      rw [hloc]
                      split at h <;> simp_all
                  · rw [hr1] at h
                    simp only [List.cons_append] at h ⊢
                    split at h <;> (try split at h) <;> grind
            · rw [hr1] at h
              simp only [List.cons_append] at h ⊢
              split at h <;> (try split at h) <;> grind

/-! ## Blank-node labels, in the form the statement readers have

⚠️ The dot exclusion is a real divergence, not bookkeeping: `_:ab.`
reads the label `ab` and leaves `['.']`, while `_:ab.c` reads the label
`ab.c` and leaves nothing. -/

theorem readBlankNodeLabel_local' (pos : Nat) (cs extra : List Char) (s : String)
    (p' : Nat) (rest : List Char)
    (h : readBlankNodeLabel pos cs = .ok (s, p', rest))
    (hne : rest ≠ []) (hnd : rest ≠ ['.']) :
    readBlankNodeLabel pos (cs ++ extra) = .ok (s, p', rest ++ extra) := by
  refine readBlankNodeLabel_local pos cs extra s p' rest h ?_
  intro c2 t hcs
  subst hcs
  simp only [readBlankNodeLabel] at h
  split at h
  · simp at h
  · cases hsp : t.span isBnodeChar with
    | mk taken dropped =>
        rw [hsp] at h
        simp only at h
        intro hdrop
        simp only at hdrop
        subst hdrop
        split at h <;> simp_all

/-! ## Subject, predicate, object, graph label -/

theorem readSubject_local (pos : Nat) (cs extra : List Char) (subj : Subject)
    (p' : Nat) (rest : List Char)
    (h : readSubject pos cs = .ok (subj, p', rest))
    (hne : rest ≠ []) (hnd : rest ≠ ['.']) :
    readSubject pos (cs ++ extra) = .ok (subj, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readSubject] at h
  | cons c0 t =>
    by_cases hlt : c0 = '<'
    · subst hlt
      simp only [readSubject, List.cons_append] at h ⊢
      cases hr : readIriRef pos ('<' :: t) with
      | error e => simp_all
      | ok v =>
          obtain ⟨str, pos2, rest2⟩ := v
          have hloc := readIriRef_local pos ('<' :: t) extra str pos2 rest2 hr
          rw [List.cons_append] at hloc
          rw [hloc]
          rw [hr] at h
          simp only at h ⊢
          cases hm : mkIri pos str with
          | error e => simp_all
          | ok wi => simp_all
    · by_cases hus : c0 = '_'
      · subst hus
        cases t with
        | nil => simp [readSubject] at h
        | cons c1 t2 =>
          by_cases hco : c1 = ':'
          · subst hco
            simp only [readSubject, List.cons_append] at h ⊢
            cases hr : readBlankNodeLabel pos ('_' :: ':' :: t2) with
            | error e => simp_all
            | ok v =>
                obtain ⟨lab, pos2, rest2⟩ := v
                rw [hr] at h
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                have hr2 : rest2 = rest := by grind
                subst hr2
                have hloc := readBlankNodeLabel_local' pos ('_' :: ':' :: t2) extra lab
                  pos2 rest2 hr hne hnd
                rw [List.cons_append, List.cons_append] at hloc
                rw [hloc]
                grind
          · simp [readSubject, hco] at h
      · simp [readSubject, hlt, hus] at h

theorem readPredicate_local (pos : Nat) (cs extra : List Char) (pred : WfIri)
    (p' : Nat) (rest : List Char)
    (h : readPredicate pos cs = .ok (pred, p', rest)) :
    readPredicate pos (cs ++ extra) = .ok (pred, p', rest ++ extra) := by
  simp only [readPredicate] at h ⊢
  cases hr : readIriRef pos cs with
  | error e => simp_all
  | ok v =>
      obtain ⟨str, pos2, rest2⟩ := v
      rw [readIriRef_local pos cs extra str pos2 rest2 hr]
      rw [hr] at h
      simp only at h ⊢
      cases hm : mkIri pos str with
      | error e => simp_all
      | ok wi => simp_all

theorem readObject11_local (pos : Nat) (cs extra : List Char) (obj : Term)
    (p' : Nat) (rest : List Char)
    (h : readObject11 pos cs = .ok (obj, p', rest))
    (hne : rest ≠ []) (hnd : rest ≠ ['.']) (hnc : rest ≠ ['^']) :
    readObject11 pos (cs ++ extra) = .ok (obj, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readObject11] at h
  | cons c0 t =>
    by_cases hlt : c0 = '<'
    · subst hlt
      simp only [readObject11, List.cons_append] at h ⊢
      cases hr : readIriRef pos ('<' :: t) with
      | error e => simp_all
      | ok v =>
          obtain ⟨str, pos2, rest2⟩ := v
          have hloc := readIriRef_local pos ('<' :: t) extra str pos2 rest2 hr
          rw [List.cons_append] at hloc
          rw [hloc]
          rw [hr] at h
          simp only at h ⊢
          cases hm : mkIri pos str with
          | error e => simp_all
          | ok wi => simp_all
    · by_cases hus : c0 = '_'
      · subst hus
        cases t with
        | nil => simp [readObject11] at h
        | cons c1 t2 =>
          by_cases hco : c1 = ':'
          · subst hco
            simp only [readObject11, List.cons_append] at h ⊢
            cases hr : readBlankNodeLabel pos ('_' :: ':' :: t2) with
            | error e => simp_all
            | ok v =>
                obtain ⟨lab, pos2, rest2⟩ := v
                rw [hr] at h
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                have hr2 : rest2 = rest := by grind
                subst hr2
                have hloc := readBlankNodeLabel_local' pos ('_' :: ':' :: t2) extra lab
                  pos2 rest2 hr hne hnd
                rw [List.cons_append, List.cons_append] at hloc
                rw [hloc]
                grind
          · simp [readObject11, hco] at h
      · by_cases hdq : c0 = '"'
        · subst hdq
          simp only [readObject11, List.cons_append] at h ⊢
          cases hr : readLiteral .rdf11 pos ('"' :: t) with
          | error e => simp_all
          | ok v =>
              obtain ⟨lit, pos2, rest2⟩ := v
              rw [hr] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              have hr2 : rest2 = rest := by grind
              subst hr2
              have hloc := readLiteral11_local pos ('"' :: t) extra lit pos2 rest2 hr
                hne hnc
              rw [List.cons_append] at hloc
              rw [hloc]
              grind
        · simp [readObject11, hlt, hus, hdq] at h

theorem readGraphLabel_local (pos : Nat) (cs extra : List Char) (g : Subject)
    (p' : Nat) (rest : List Char)
    (h : readGraphLabel pos cs = .ok (g, p', rest))
    (hne : rest ≠ []) (hnd : rest ≠ ['.']) :
    readGraphLabel pos (cs ++ extra) = .ok (g, p', rest ++ extra) := by
  cases cs with
  | nil => simp [readGraphLabel] at h
  | cons c0 t =>
    by_cases hlt : c0 = '<'
    · subst hlt
      simp only [readGraphLabel, List.cons_append] at h ⊢
      cases hr : readIriRef pos ('<' :: t) with
      | error e => simp_all
      | ok v =>
          obtain ⟨str, pos2, rest2⟩ := v
          have hloc := readIriRef_local pos ('<' :: t) extra str pos2 rest2 hr
          rw [List.cons_append] at hloc
          rw [hloc]
          rw [hr] at h
          simp only at h ⊢
          cases hm : mkIri pos str with
          | error e => simp_all
          | ok wi => simp_all
    · by_cases hus : c0 = '_'
      · subst hus
        cases t with
        | nil => simp [readGraphLabel] at h
        | cons c1 t2 =>
          by_cases hco : c1 = ':'
          · subst hco
            simp only [readGraphLabel, List.cons_append] at h ⊢
            cases hr : readBlankNodeLabel pos ('_' :: ':' :: t2) with
            | error e => simp_all
            | ok v =>
                obtain ⟨lab, pos2, rest2⟩ := v
                rw [hr] at h
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                have hr2 : rest2 = rest := by grind
                subst hr2
                have hloc := readBlankNodeLabel_local' pos ('_' :: ':' :: t2) extra lab
                  pos2 rest2 hr hne hnd
                rw [List.cons_append, List.cons_append] at hloc
                rw [hloc]
                grind
          · simp [readGraphLabel, hco] at h
      · by_cases hdq : c0 = '"'
        · subst hdq; simp [readGraphLabel] at h
        · simp [readGraphLabel, hlt, hus, hdq] at h

private theorem skipWs_nil (pos : Nat) : skipWs pos ([] : List Char) = (pos, []) := rfl

private theorem skipWs_dot (pos : Nat) : skipWs pos ['.'] = (pos, ['.']) := rfl

private theorem skipWs_underscore (pos : Nat) : skipWs pos ['_'] = (pos, ['_']) := rfl

private theorem skipWs_hat (pos : Nat) : skipWs pos ['^'] = (pos, ['^']) := rfl

private theorem readOptGraphLabel_nil (pos : Nat) :
    readOptGraphLabel pos [] = .ok (none, pos, []) := rfl

private theorem readOptGraphLabel_dot (pos : Nat) :
    readOptGraphLabel pos ['.'] = .ok (none, pos, ['.']) := rfl

private theorem readOptGraphLabel_hat (pos : Nat) :
    readOptGraphLabel pos ['^'] = .ok (none, pos, ['^']) := rfl

theorem readOptGraphLabel_local (pos : Nat) (cs extra : List Char)
    (gopt : Option Subject) (p' : Nat) (rest : List Char)
    (h : readOptGraphLabel pos cs = .ok (gopt, p', rest))
    (hne : rest ≠ []) (hnd : rest ≠ ['.']) (hnu : rest ≠ ['_']) :
    readOptGraphLabel pos (cs ++ extra) = .ok (gopt, p', rest ++ extra) := by
  simp only [readOptGraphLabel] at h ⊢
  cases hw : skipWs pos cs with
  | mk pos1 cs1 =>
    rw [hw] at h
    simp only at h
    have hcs1 : cs1 ≠ [] := by
      intro hc; rw [hc] at h; simp at h; grind
    have hskip : skipWs pos (cs ++ extra) = (pos1, cs1 ++ extra) := by
      have hs := skipWs_local pos cs extra (by rw [hw]; exact hcs1)
      rw [hw] at hs; simpa using hs
    rw [hskip]
    simp only
    cases hc1 : cs1 with
    | nil => exact absurd hc1 hcs1
    | cons a t =>
      rw [hc1] at h
      by_cases hdot : a = '.'
      · subst hdot
        simp only [List.cons_append] at h ⊢
        grind
      · by_cases hlt : a = '<'
        · subst hlt
          simp only [List.cons_append] at h ⊢
          cases hg : readGraphLabel pos1 ('<' :: t) with
          | error e => rw [hg] at h; simp at h
          | ok v =>
              obtain ⟨g, pos2, rest2⟩ := v
              rw [hg] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              have hr2 : rest2 = rest := by grind
              subst hr2
              have hloc := readGraphLabel_local pos1 ('<' :: t) extra g pos2 rest2 hg
                hne hnd
              rw [List.cons_append] at hloc
              rw [hloc]
              grind
        · by_cases hus : a = '_'
          · subst hus
            cases t with
            | nil => first | grind | (simp at h; grind)
            | cons b t2 =>
              by_cases hco : b = ':'
              · subst hco
                simp only [List.cons_append] at h ⊢
                cases hg : readGraphLabel pos1 ('_' :: ':' :: t2) with
                | error e => rw [hg] at h; simp at h
                | ok v =>
                    obtain ⟨g, pos2, rest2⟩ := v
                    rw [hg] at h
                    simp only [Except.ok.injEq, Prod.mk.injEq] at h
                    have hr2 : rest2 = rest := by grind
                    subst hr2
                    have hloc := readGraphLabel_local pos1 ('_' :: ':' :: t2) extra g
                      pos2 rest2 hg hne hnd
                    rw [List.cons_append, List.cons_append] at hloc
                    rw [hloc]
                    grind
              · simp only [List.cons_append] at h ⊢
                grind
          · by_cases hdq : a = '"'
            · subst hdq
              simp only [List.cons_append] at h
              simp at h
            · simp only [List.cons_append] at h ⊢
              grind

/-! ## A whole N-Quads statement

⚠️ One side condition, `rest ≠ []`, and it is the line terminator doing
the work. A statement ends at `.`, so if anything at all follows that
dot then every earlier remainder still holds it, and each of the three
exclusions the readers above carry is met. Without it the statement
`<a> <b> <c> _:g.` is a counterexample: the graph label reads as `g`
with `['.']` left over, but on `<a> <b> <c> _:g.x` the label reads as
`g.x` and the statement has no terminator at all. -/

theorem readNQuad11_local (pos : Nat) (cs extra : List Char) (tr : Triple)
    (g : Option Subject) (p' : Nat) (rest : List Char)
    (h : readNQuad11 pos cs = .ok (tr, g, p', rest)) (hne : rest ≠ []) :
    readNQuad11 pos (cs ++ extra) = .ok (tr, g, p', rest ++ extra) := by
  simp only [readNQuad11] at h ⊢
  cases hw1 : skipWs pos cs with
  | mk pos1 cs1 =>
    rw [hw1] at h; simp only at h
    cases hs : readSubject pos1 cs1 with
    | error e => rw [hs] at h; simp at h
    | ok v1 =>
      obtain ⟨subj, pos2, cs2⟩ := v1
      rw [hs] at h; simp only at h
      cases hw2 : skipWs pos2 cs2 with
      | mk pos3 cs3 =>
        rw [hw2] at h; simp only at h
        cases hp : readPredicate pos3 cs3 with
        | error e => rw [hp] at h; simp at h
        | ok v2 =>
          obtain ⟨pred, pos4, cs4⟩ := v2
          rw [hp] at h; simp only at h
          cases hw3 : skipWs pos4 cs4 with
          | mk pos5 cs5 =>
            rw [hw3] at h; simp only at h
            cases ho : readObject11 pos5 cs5 with
            | error e => rw [ho] at h; simp at h
            | ok v3 =>
              obtain ⟨obj, pos6, cs6⟩ := v3
              rw [ho] at h; simp only at h
              cases hgl : readOptGraphLabel pos6 cs6 with
              | error e => rw [hgl] at h; simp at h
              | ok v4 =>
                obtain ⟨gopt, pos7, cs7⟩ := v4
                rw [hgl] at h; simp only at h
                cases hw4 : skipWs pos7 cs7 with
                | mk pos8 cs8 =>
                  rw [hw4] at h; simp only at h
                  cases hc8 : cs8 with
                  | nil => rw [hc8] at h; simp at h
                  | cons d cs9 =>
                    rw [hc8] at h
                    by_cases hd : d = '.'
                    · subst hd
                      simp only [Except.ok.injEq, Prod.mk.injEq] at h
                      have hrest : cs9 = rest := by grind
                      subst hrest
                      -- Every remainder still holds the terminator.
                      have h7ne : cs7 ≠ [] := by
                        intro hc; rw [hc, skipWs_nil] at hw4; grind
                      have h7dot : cs7 ≠ ['.'] := by
                        intro hc; rw [hc, skipWs_dot] at hw4; grind
                      have h7us : cs7 ≠ ['_'] := by
                        intro hc; rw [hc, skipWs_underscore] at hw4; grind
                      have h7hat : cs7 ≠ ['^'] := by
                        intro hc; rw [hc, skipWs_hat] at hw4; grind
                      have h6ne : cs6 ≠ [] := by
                        intro hc; rw [hc, readOptGraphLabel_nil] at hgl; grind
                      have h6dot : cs6 ≠ ['.'] := by
                        intro hc; rw [hc, readOptGraphLabel_dot] at hgl; grind
                      have h6hat : cs6 ≠ ['^'] := by
                        intro hc; rw [hc, readOptGraphLabel_hat] at hgl; grind
                      have h5ne : cs5 ≠ [] := by
                        intro hc; rw [hc] at ho
                        simp [readObject11] at ho
                      have h4ne : cs4 ≠ [] := by
                        intro hc; rw [hc, skipWs_nil] at hw3; grind
                      have h3ne : cs3 ≠ [] := by
                        intro hc; rw [hc] at hp
                        simp [readPredicate, readIriRef] at hp
                      have h2ne : cs2 ≠ [] := by
                        intro hc; rw [hc, skipWs_nil] at hw2
                        have hc3 : cs3 = [] := by grind
                        rw [hc3] at hp
                        simp [readPredicate, readIriRef] at hp
                      have h2dot : cs2 ≠ ['.'] := by
                        intro hc; rw [hc, skipWs_dot] at hw2
                        have hc3 : cs3 = ['.'] := by grind
                        rw [hc3] at hp
                        simp [readPredicate, readIriRef] at hp
                      have h1ne : cs1 ≠ [] := by
                        intro hc; rw [hc] at hs
                        simp [readSubject] at hs
                      -- Rewrite the longer run, stage by stage.
                      have k1 : skipWs pos (cs ++ extra) = (pos1, cs1 ++ extra) := by
                        have := skipWs_local pos cs extra (by rw [hw1]; exact h1ne)
                        rw [hw1] at this; simpa using this
                      rw [k1]; simp only
                      rw [readSubject_local pos1 cs1 extra subj pos2 cs2 hs h2ne h2dot]
                      simp only
                      have k2 : skipWs pos2 (cs2 ++ extra) = (pos3, cs3 ++ extra) := by
                        have := skipWs_local pos2 cs2 extra (by rw [hw2]; exact h3ne)
                        rw [hw2] at this; simpa using this
                      rw [k2]; simp only
                      rw [readPredicate_local pos3 cs3 extra pred pos4 cs4 hp]
                      simp only
                      have k3 : skipWs pos4 (cs4 ++ extra) = (pos5, cs5 ++ extra) := by
                        have := skipWs_local pos4 cs4 extra (by rw [hw3]; exact h5ne)
                        rw [hw3] at this; simpa using this
                      rw [k3]; simp only
                      rw [readObject11_local pos5 cs5 extra obj pos6 cs6 ho h6ne h6dot
                            h6hat]
                      simp only
                      rw [readOptGraphLabel_local pos6 cs6 extra gopt pos7 cs7 hgl h7ne
                            h7dot h7us]
                      simp only
                      have k4 : skipWs pos7 (cs7 ++ extra) = (pos8, ('.' :: cs9) ++ extra) := by
                        have := skipWs_local pos7 cs7 extra (by rw [hw4, hc8]; simp)
                        rw [hw4, hc8] at this; simpa using this
                      rw [k4]; simp only [List.cons_append]
                      grind
                    · simp [hd] at h

/-! ## The quad-line side condition is doing real work

Measured, not reasoned out. `<http://a/s> <http://a/p> <http://a/o> _:g.`
parses, with the graph name `_:g` and NOTHING left over. Add one
character and the blank-node label swallows the dot, so the statement
has no terminator and the read FAILS. That guard pair is the refutation
of `readNQuad11_local` without `rest ≠ []`. -/

private def quadRemainder
    (r : Except ParseError (Triple × Option Subject × Nat × List Char)) :
    Option (List Char) :=
  match r with
  | .ok (_, _, _, rest) => some rest
  | .error _ => none

private def demoLine : List Char :=
  "<http://a/s> <http://a/p> <http://a/o> .\n".toList
private def demoNoTail : List Char :=
  "<http://a/s> <http://a/p> <http://a/o> _:g.".toList

-- With a terminator: the remainder is non-empty and grows by exactly
-- what was appended.
#guard quadRemainder (readNQuad11 0 demoLine) = some ['\n']
#guard quadRemainder (readNQuad11 0 (demoLine ++ demoLine))
         = some (['\n'] ++ demoLine)

-- Without one: the remainder is empty, and one more character turns a
-- successful read into a failure.
#guard quadRemainder (readNQuad11 0 demoNoTail) = some []
#guard quadRemainder (readNQuad11 0 (demoNoTail ++ ['x'])) = none

/-! ## The side conditions are satisfiable

A hypothesis nothing can meet proves nothing. These run at build time
and show the exclusions above are met by an ordinary N-Quads object
slot that still has its line terminator, and that the conclusion holds
on it: the same term, the same end position, and a remainder longer by
exactly what was appended. -/

private def demoTail : List Char := " .\n".toList
private def demoObj : List Char := "\"x\"".toList ++ demoTail
private def demoExtra : List Char := "<http://a/g> .\n".toList

private def objRemainder (r : Except ParseError (Term × Nat × List Char)) :
    Option (List Char) :=
  match r with
  | .ok (_, _, rest) => some rest
  | .error _ => none

private def objEnd (r : Except ParseError (Term × Nat × List Char)) : Option Nat :=
  match r with
  | .ok (_, p, _) => some p
  | .error _ => none

-- The remainder is non-empty, is not `['.']`, and is not `['^']`.
#guard objRemainder (readObject11 0 demoObj) = some demoTail
#guard demoTail ≠ []
#guard demoTail ≠ ['.']
#guard demoTail ≠ ['^']

-- And the reader answers the same on the longer input.
#guard objRemainder (readObject11 0 (demoObj ++ demoExtra))
         = some (demoTail ++ demoExtra)
#guard objEnd (readObject11 0 (demoObj ++ demoExtra)) = objEnd (readObject11 0 demoObj)

/-! ## Axiom audit -/

#print axioms skipWs_local
#print axioms readLangTag_local
#print axioms readDatatype_local
#print axioms readLiteral11_local
#print axioms readBlankNodeLabel_local'
#print axioms readSubject_local
#print axioms readPredicate_local
#print axioms readObject11_local
#print axioms readGraphLabel_local
#print axioms readOptGraphLabel_local
#print axioms readNQuad11_local

end L4Factoidal.Syntax
