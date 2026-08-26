/-
L4Factoidal.CL.Alpha — alpha-normalization of CL/IKL sentences.

IKL individuates propositions up to bound-variable renaming: the IKL
guide (Hayes/Menzel, Appendix B,
https://www.ihmc.us/users/phayes/IKL/GUIDE/GUIDE.html) treats
`(that (exists (x)(loves Jim x)))` and
`(that (exists (y)(loves Jim y)))` as names of ONE proposition.
`Sentence.alphaNorm` computes a canonical representative of a
sentence's alpha-equivalence class, so a downstream identity keyed on
the canonical CLIF text —
https://github.com/danbri/factoidal/issues/589 — meets that condition
exactly. Referential transparency (the guide's other individuation
condition — a proposition depends on the things named, not on the
names) is not syntactically decidable and is NOT attempted here; the
stronger defined relation `=p` (conjunct sorting, de Morgan
identities, ...) is a deliberate follow-up, tracked in issue 589.

## The renaming scheme, and why it cannot capture

Bound variables are renamed to `v1`, `v2`, ... in binder order — the
order binders are met in one left-to-right traversal of the sentence
(a de Bruijn-level labelling spelled as names). Two alpha-variants
have the same binder structure, so the same traversal meets their
binders in the same order and produces the same result. Free names
are never touched, and bound sequence markers are renamed the same
way in their own lexical space (`...v1` can never collide with the
name `v1` — a marker occurrence and a name occurrence are distinct
syntax).

Any string can be a CL name (the `"..."` enclosed-name form puts the
whole of Unicode in play), so NO fixed scheme is fresh by spelling
alone. Freshness is therefore checked, not assumed: the canonical
name for a binder is the first `v<i>` (counting up from the running
index) that is not a FREE name of the whole sentence. That set is
alpha-invariant, so the normal form still is; and capture is
impossible because

* a canonical binder name never equals any free name of the sentence
  (skipped by construction), so no free occurrence is captured, and
* distinct binders always get distinct indices (the index counter
  only moves forward), so no two binders merge.

Scoping follows `CL/Semantics.lean` exactly: bindings of one
boundlist extend the environment sequentially, and a restricted
binding's guard term is renamed in the environment BEFORE its own
name is added (`SatForall`/`SatExists` evaluate the guard under the
outer assignment). Renaming descends through `that` — quantifying-in
(`(exists (x) (believes K (that (P x))))`) renames the occurrence
inside the proposition term under the outer binder.

Style: mutual structural recursion with explicit list helpers, the
`Syntax.isPureCL` pattern, for mechanical F* transcription
(issue 580).
-/

import L4Factoidal.CL.Clif

namespace L4Factoidal.CL

/-! ## Free names and free sequence markers

One traversal returning both sets (names, markers) as lists with
possible duplicates — only membership is consumed. `bnames`/`bmarks`
are the names/markers bound by enclosing binders. -/

mutual

/-- Free (name, sequence-marker) occurrences of a term. -/
def Term.freeVars (bnames bmarks : List String) : Term → List String × List String
  | .name n => (if bnames.contains n then [] else [n], [])
  | .str _ => ([], [])
  | .funapp op args =>
      let (n1, s1) := op.freeVars bnames bmarks
      let (n2, s2) := seqItemsFreeVars bnames bmarks args
      (n1 ++ n2, s1 ++ s2)
  | .that s => s.freeVars bnames bmarks

/-- Free variables of an argument sequence. -/
def seqItemsFreeVars (bnames bmarks : List String) :
    List SeqItem → List String × List String
  | [] => ([], [])
  | .term t :: r =>
      let (n1, s1) := t.freeVars bnames bmarks
      let (n2, s2) := seqItemsFreeVars bnames bmarks r
      (n1 ++ n2, s1 ++ s2)
  | .seqmark m :: r =>
      let (n2, s2) := seqItemsFreeVars bnames bmarks r
      (n2, (if bmarks.contains m then [] else [m]) ++ s2)

/-- Free variables contributed by a boundlist's guard terms, plus the
extended bound sets for the body. Sequential extension, guard before
its own name — the `Semantics.SatForall` scoping. -/
def bindingsFreeVars (bnames bmarks : List String) :
    List Binding → List String × List String × List String × List String
  | [] => ([], [], bnames, bmarks)
  | .plain n :: r => bindingsFreeVars (n :: bnames) bmarks r
  | .seqmark m :: r => bindingsFreeVars bnames (m :: bmarks) r
  | .restricted n g :: r =>
      let (gn, gs) := g.freeVars bnames bmarks
      let (rn, rs, bnames', bmarks') := bindingsFreeVars (n :: bnames) bmarks r
      (gn ++ rn, gs ++ rs, bnames', bmarks')

/-- Free (name, sequence-marker) occurrences of a sentence. -/
def Sentence.freeVars (bnames bmarks : List String) :
    Sentence → List String × List String
  | .atom p args =>
      let (n1, s1) := p.freeVars bnames bmarks
      let (n2, s2) := seqItemsFreeVars bnames bmarks args
      (n1 ++ n2, s1 ++ s2)
  | .eq a b =>
      let (n1, s1) := a.freeVars bnames bmarks
      let (n2, s2) := b.freeVars bnames bmarks
      (n1 ++ n2, s1 ++ s2)
  | .conj ss => sentencesFreeVars bnames bmarks ss
  | .disj ss => sentencesFreeVars bnames bmarks ss
  | .neg s => s.freeVars bnames bmarks
  | .impl a b =>
      let (n1, s1) := a.freeVars bnames bmarks
      let (n2, s2) := b.freeVars bnames bmarks
      (n1 ++ n2, s1 ++ s2)
  | .iff a b =>
      let (n1, s1) := a.freeVars bnames bmarks
      let (n2, s2) := b.freeVars bnames bmarks
      (n1 ++ n2, s1 ++ s2)
  | .all bs body =>
      let (n1, s1, bnames', bmarks') := bindingsFreeVars bnames bmarks bs
      let (n2, s2) := body.freeVars bnames' bmarks'
      (n1 ++ n2, s1 ++ s2)
  | .ex bs body =>
      let (n1, s1, bnames', bmarks') := bindingsFreeVars bnames bmarks bs
      let (n2, s2) := body.freeVars bnames' bmarks'
      (n1 ++ n2, s1 ++ s2)

/-- Free variables of a sentence list. -/
def sentencesFreeVars (bnames bmarks : List String) :
    List Sentence → List String × List String
  | [] => ([], [])
  | s :: r =>
      let (n1, s1) := s.freeVars bnames bmarks
      let (n2, s2) := sentencesFreeVars bnames bmarks r
      (n1 ++ n2, s1 ++ s2)

end

/-! ## Canonical names -/

/-- The canonical bound-variable spelling for index `i`. -/
def canonName (i : Nat) : String := "v" ++ toString i

/-- Rename-environment lookup: the canonical name a bound source name
maps to, or the name itself when free (no entry). Shadowing = most
recent entry first. -/
def renameLookup (env : List (String × String)) (n : String) : String :=
  match env.find? (fun p => p.1 == n) with
  | some p => p.2
  | none => n

/-- First canonical name at index ≥ `k` that avoids `avoid`, plus the
next index. Fuel-bounded scan: at most `avoid.length` indices can be
rejected in total, so `avoid.length + 1` fuel never runs out before a
fresh index is found (the fuel-0 fallback is unreachable). -/
def freshCanonFrom (avoid : List String) : Nat → Nat → String × Nat
  | 0, k => (canonName k, k + 1)
  | fuel + 1, k =>
      if avoid.contains (canonName k) then freshCanonFrom avoid fuel (k + 1)
      else (canonName k, k + 1)

/-- `freshCanonFrom` with its sufficient fuel. -/
def freshCanon (avoid : List String) (k : Nat) : String × Nat :=
  freshCanonFrom avoid (avoid.length + 1) k

/-! ## The renaming traversal

`avN`/`avS` are the free names/markers of the WHOLE sentence (the
avoid sets); `envN`/`envS` map in-scope source names/markers to their
canonical names; the `Nat` is the next binder index, threaded through
the traversal so nested and sibling binders keep distinct indices. -/

mutual

/-- Rename bound-variable occurrences in a term. -/
def Term.alphaRen (avN avS : List String) (envN envS : List (String × String)) :
    Nat → Term → Term × Nat
  | k, .name n => (.name (renameLookup envN n), k)
  | k, .str s => (.str s, k)
  | k, .funapp op args =>
      let (op', k1) := op.alphaRen avN avS envN envS k
      let (args', k2) := seqItemsAlphaRen avN avS envN envS k1 args
      (.funapp op' args', k2)
  | k, .that s =>
      let (s', k') := s.alphaRen avN avS envN envS k
      (.that s', k')

/-- Rename an argument sequence. -/
def seqItemsAlphaRen (avN avS : List String) (envN envS : List (String × String)) :
    Nat → List SeqItem → List SeqItem × Nat
  | k, [] => ([], k)
  | k, .term t :: r =>
      let (t', k1) := t.alphaRen avN avS envN envS k
      let (r', k2) := seqItemsAlphaRen avN avS envN envS k1 r
      (.term t' :: r', k2)
  | k, .seqmark m :: r =>
      let (r', k') := seqItemsAlphaRen avN avS envN envS k r
      (.seqmark (renameLookup envS m) :: r', k')

/-- Rename a boundlist: each binder gets the next fresh canonical
name; a restricted binding's guard is renamed BEFORE the binding's
own name enters the environment (the `Semantics.SatForall` scoping),
though its index is allocated first — the bound name precedes the
guard in the CLIF spelling. Returns the renamed boundlist and the
environments for the body. -/
def bindingsAlphaRen (avN avS : List String) (envN envS : List (String × String)) :
    Nat → List Binding →
    List Binding × List (String × String) × List (String × String) × Nat
  | k, [] => ([], envN, envS, k)
  | k, .plain n :: r =>
      let (c, k1) := freshCanon avN k
      let (r', envN', envS', k2) :=
        bindingsAlphaRen avN avS ((n, c) :: envN) envS k1 r
      (.plain c :: r', envN', envS', k2)
  | k, .seqmark m :: r =>
      let (c, k1) := freshCanon avS k
      let (r', envN', envS', k2) :=
        bindingsAlphaRen avN avS envN ((m, c) :: envS) k1 r
      (.seqmark c :: r', envN', envS', k2)
  | k, .restricted n g :: r =>
      let (c, k1) := freshCanon avN k
      let (g', k2) := g.alphaRen avN avS envN envS k1
      let (r', envN', envS', k3) :=
        bindingsAlphaRen avN avS ((n, c) :: envN) envS k2 r
      (.restricted c g' :: r', envN', envS', k3)

/-- Rename bound-variable occurrences in a sentence. -/
def Sentence.alphaRen (avN avS : List String) (envN envS : List (String × String)) :
    Nat → Sentence → Sentence × Nat
  | k, .atom p args =>
      let (p', k1) := p.alphaRen avN avS envN envS k
      let (args', k2) := seqItemsAlphaRen avN avS envN envS k1 args
      (.atom p' args', k2)
  | k, .eq a b =>
      let (a', k1) := a.alphaRen avN avS envN envS k
      let (b', k2) := b.alphaRen avN avS envN envS k1
      (.eq a' b', k2)
  | k, .conj ss =>
      let (ss', k') := sentencesAlphaRen avN avS envN envS k ss
      (.conj ss', k')
  | k, .disj ss =>
      let (ss', k') := sentencesAlphaRen avN avS envN envS k ss
      (.disj ss', k')
  | k, .neg s =>
      let (s', k') := s.alphaRen avN avS envN envS k
      (.neg s', k')
  | k, .impl a b =>
      let (a', k1) := a.alphaRen avN avS envN envS k
      let (b', k2) := b.alphaRen avN avS envN envS k1
      (.impl a' b', k2)
  | k, .iff a b =>
      let (a', k1) := a.alphaRen avN avS envN envS k
      let (b', k2) := b.alphaRen avN avS envN envS k1
      (.iff a' b', k2)
  | k, .all bs body =>
      let (bs', envN', envS', k1) := bindingsAlphaRen avN avS envN envS k bs
      let (body', k2) := body.alphaRen avN avS envN' envS' k1
      (.all bs' body', k2)
  | k, .ex bs body =>
      let (bs', envN', envS', k1) := bindingsAlphaRen avN avS envN envS k bs
      let (body', k2) := body.alphaRen avN avS envN' envS' k1
      (.ex bs' body', k2)

/-- Rename a sentence list. -/
def sentencesAlphaRen (avN avS : List String) (envN envS : List (String × String)) :
    Nat → List Sentence → List Sentence × Nat
  | k, [] => ([], k)
  | k, s :: r =>
      let (s', k1) := s.alphaRen avN avS envN envS k
      let (r', k2) := sentencesAlphaRen avN avS envN envS k1 r
      (s' :: r', k2)

end

/-- Alpha-normalize: rename every bound variable to the canonical
scheme (module header). The canonical representative of the
sentence's alpha-equivalence class: alpha-variants normalize equal,
non-variants stay distinct, free names are untouched. -/
def Sentence.alphaNorm (s : Sentence) : Sentence :=
  let (fn, fs) := s.freeVars [] []
  (s.alphaRen fn fs [] [] 1).1

/-! ## Guards

`Sentence` has no `DecidableEq` (mutual family), so normal forms are
compared through the canonical CLIF serialisation. -/

/-- Parse one sentence, alpha-normalize, serialise (test entry;
`none` on a parse error). -/
def alphaCanon (input : String) : Option String :=
  match parseClifSentence input with
  | .ok s => some s.alphaNorm.toClif
  | .error _ => none

-- The guide's Appendix B pair: alpha-variants are ONE proposition,
-- and their normal forms are one string. Free names (Jim, loves)
-- untouched.
#guard alphaCanon "(exists (x)(loves Jim x))" == some "(exists (v1) (loves Jim v1))"
#guard alphaCanon "(exists (x)(loves Jim x))" == alphaCanon "(exists (y)(loves Jim y))"

-- Distinct propositions stay distinct.
#guard (alphaCanon "(exists (x)(loves Jim x))"
        == alphaCanon "(exists (x)(loves x Jim))") == false

-- No capture of a free name spelled like the scheme: the binder
-- skips `v1` because `v1` is free, and the two sentences do NOT
-- merge.
#guard alphaCanon "(forall (x) (P x v1))" == some "(forall (v2) (P v2 v1))"
#guard alphaCanon "(forall (v1) (P v1 v1))" == some "(forall (v1) (P v1 v1))"
#guard (alphaCanon "(forall (x) (P x v1))"
        == alphaCanon "(forall (v1) (P v1 v1))") == false

-- A bound source name already in the scheme is renamed like any
-- other bound name.
#guard alphaCanon "(forall (v7) (P v7))" == alphaCanon "(forall (x) (P x))"

-- Shadowing: inner binders get fresh indices, and both spellings of
-- the shadowed sentence normalize equal.
#guard alphaCanon "(forall (x) (and (P x) (forall (x) (Q x))))"
       == some "(forall (v1) (and (P v1) (forall (v2) (Q v2))))"
#guard alphaCanon "(forall (x) (and (P x) (forall (x) (Q x))))"
       == alphaCanon "(forall (x) (and (P x) (forall (y) (Q y))))"

-- Bound sequence markers rename in their own lexical space.
#guard alphaCanon "(forall (...xs) (P ...xs))" == some "(forall (...v1) (P ...v1))"
#guard alphaCanon "(forall (...xs) (P ...xs))" == alphaCanon "(forall (...ys) (P ...ys))"

-- Restricted bindings: the guard survives, the bound name renames.
#guard alphaCanon "(forall ((x isHuman)) (isMammal x))"
       == some "(forall ((v1 isHuman)) (isMammal v1))"
#guard alphaCanon "(forall ((x isHuman)) (isMammal x))"
       == alphaCanon "(forall ((z isHuman)) (isMammal z))"

-- Quantifying-in: renaming descends through `that`.
#guard alphaCanon "(exists (x) (believes K (that (P x))))"
       == alphaCanon "(exists (y) (believes K (that (P y))))"
#guard alphaCanon "(exists (x) (believes K (that (P x))))"
       == some "(exists (v1) (believes K (that (P v1))))"

-- A binder-free sentence is a fixed point.
#guard alphaCanon "(believes Zeno (that (Dead OBL)))"
       == some "(believes Zeno (that (Dead OBL)))"

end L4Factoidal.CL
