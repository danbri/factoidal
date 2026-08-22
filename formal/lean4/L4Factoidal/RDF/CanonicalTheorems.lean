/-
L4Factoidal.RDF.CanonicalTheorems — what is PROVED about RDFC-1.0.

Three groups, and one honest gap.

  1. OUTPUT ORDER (proved). RDFC-1.0 §3 requires the canonical N-Quads
     document to list its quads in code point order. `canonicalLines_
     sorted` proves that every adjacent pair of the emitted lines is in
     that order, for every dataset and every hash algorithm.

  2. IDENTIFIER ISSUANCE (proved). §4.8 mints `c14n0`, `c14n1`, … .
     `issuerLabelsWf_*` prove that every label an issuer ever holds has
     that shape with a counter value below the current counter;
     `mkLabel_inj` proves the shape is injective in the counter; and
     the step lemma `issueFresh_label_fresh` proves the next label
     always differs from every label already issued. Injectivity of the
     whole issued map (`IssuerLabelsInjective`) is stated and PROVED
     to be preserved by both issuing operations from the empty issuer.

  3. RELABELLING INVARIANCE (sub-lemmas proved, main theorem STATED
     ONLY). This is the point of RDFC-1.0: isomorphic datasets must
     canonicalise to the same bytes. What is proved here is the layer
     the whole result rests on — that §4.5's first-degree machinery
     cannot see the input labels: rewriting, mention-testing, quad
     rendering, and finally `hashFirstDegreeQuads` itself are all
     invariant under any injective relabelling. What is NOT proved is
     the top-level theorem; it is stated as `RelabellingInvariance`
     with the remaining obligations spelled out at that definition.

No `sorry`, no `axiom`, no `native_decide`, no `partial`: the stated-
but-unproved theorem is a `Prop`-valued DEFINITION, so nothing here
claims a proof that does not exist. `#print axioms` lines at the end
of the file show the base every proof actually uses.
-/
import L4Factoidal.RDF.Canonical
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.RDF.Canonical

open L4Factoidal.Crypto

/-! ## 1. The output is sorted (RDFC-1.0 §3)

`sortedB` is stated head-first (`headOk a l` relates `a` to the head of
`l`) so that `sortedB (a :: l)` unfolds to a conjunction with no
three-way case split — which is what keeps the insertion proof short. -/

/-- Does `a` compare ≤ the head of `l` (vacuously true if `l` is
empty)? -/
def headOk (le : α → α → Bool) (a : α) : List α → Bool
  | []     => true
  | b :: _ => le a b

/-- Every adjacent pair is in order. -/
def sortedB (le : α → α → Bool) : List α → Bool
  | []     => true
  | a :: l => headOk le a l && sortedB le l

/-- `sortedB` on a cons, as a definitional rewrite (stated so proofs
can peel exactly one layer instead of unfolding the whole list). -/
theorem sortedB_cons (le : α → α → Bool) (a : α) (l : List α) :
    sortedB le (a :: l) = (headOk le a l && sortedB le l) := rfl

theorem headOk_of_head? {le : String → String → Bool} {a y : String} {l : List String}
    (h : l.head? = some y) (hy : le a y = true) : headOk le a l = true := by
  cases l with
  | nil => simp at h
  | cons z zs =>
      simp only [List.head?, Option.some.injEq] at h
      subst h
      simpa [headOk] using hy

/-- `charsLe` is total: any two code-point lists are comparable. -/
theorem charsLe_total (a b : List Char) : charsLe a b = true ∨ charsLe b a = true := by
  induction a generalizing b with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      cases b with
      | nil => exact Or.inr rfl
      | cons y ys =>
          simp only [charsLe]
          by_cases h1 : x.val < y.val
          · simp [h1]
          · by_cases h2 : y.val < x.val
            · simp [h1, h2]
            · simp only [h1, h2, if_false]
              exact ih ys

/-- `strLe` is total — the only property the sortedness proof needs of
it (transitivity is not required to show insertion sort produces an
adjacent-ordered list). -/
theorem strLe_total (a b : String) : strLe a b = true ∨ strLe b a = true :=
  charsLe_total a.toList b.toList

/-- Inserting `x` into `l` cannot put anything smaller than `l`'s head
in front, provided `a` already dominates both `l`'s head and `x`. -/
theorem headOk_insertSortedBy (le : α → α → Bool) (a x : α) (l : List α)
    (hl : headOk le a l = true) (hx : le a x = true) :
    headOk le a (insertSortedBy le x l) = true := by
  cases l with
  | nil => simpa [insertSortedBy, headOk] using hx
  | cons b bs =>
      by_cases h : le b x = true
      · simpa [insertSortedBy, headOk, h] using hl
      · simp [insertSortedBy, headOk, h, hx]

/-- Insertion into a sorted list keeps it sorted. -/
theorem sortedB_insertSortedBy (le : α → α → Bool)
    (htot : ∀ p q : α, le p q = true ∨ le q p = true) (x : α) :
    ∀ l : List α, sortedB le l = true → sortedB le (insertSortedBy le x l) = true := by
  intro l
  induction l with
  | nil => intro _; simp [insertSortedBy, sortedB, headOk]
  | cons b bs ih =>
      intro h
      simp only [sortedB, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      by_cases hb : le b x = true
      · simp only [insertSortedBy, hb, if_pos]
        simp only [sortedB, Bool.and_eq_true]
        exact ⟨headOk_insertSortedBy le b x bs hhead hb, ih htail⟩
      · have hxb : le x b = true := (htot b x).resolve_left hb
        have hins : insertSortedBy le x (b :: bs) = x :: b :: bs := by
          simp [insertSortedBy, hb]
        rw [hins, sortedB_cons, sortedB_cons]
        simp only [headOk, Bool.and_eq_true]
        exact ⟨hxb, hhead, htail⟩

/-- Folding insertion over any list, from any sorted accumulator,
yields a sorted list. -/
theorem sortedB_foldl_insert (le : α → α → Bool)
    (htot : ∀ p q : α, le p q = true ∨ le q p = true) :
    ∀ (xs acc : List α), sortedB le acc = true →
      sortedB le (xs.foldl (fun a x => insertSortedBy le x a) acc) = true := by
  intro xs
  induction xs with
  | nil => intro acc h; simpa using h
  | cons x xs ih =>
      intro acc h
      exact ih _ (sortedB_insertSortedBy le htot x acc h)

/-- **`sortBy` really sorts** (under any total comparator). -/
theorem sortedB_sortBy (le : α → α → Bool)
    (htot : ∀ p q : α, le p q = true ∨ le q p = true) (xs : List α) :
    sortedB le (sortBy le xs) = true :=
  sortedB_foldl_insert le htot xs [] rfl

theorem sortedB_sortStrings (xs : List String) : sortedB strLe (sortStrings xs) = true :=
  sortedB_sortBy strLe strLe_total xs

/-- Dropping adjacent duplicates does not move the head. -/
theorem dedupAdj_head? (x : String) (xs : List String) :
    (dedupAdj (x :: xs)).head? = some x := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : (x == y) = true
      · have hxy : x = y := by simpa using h
        subst hxy
        simpa [dedupAdj, h] using ih x
      · simp [dedupAdj, h]

/-- Dropping adjacent duplicates keeps a sorted list sorted. -/
theorem sortedB_dedupAdj :
    ∀ xs : List String, sortedB strLe xs = true → sortedB strLe (dedupAdj xs) = true := by
  intro xs
  induction xs using dedupAdj.induct with
  | case1 => intro _; rfl
  | case2 x => intro _; rfl
  | case3 x y rest h ih =>
      intro hs
      rw [sortedB_cons, Bool.and_eq_true] at hs
      simp only [dedupAdj, h, if_pos]
      exact ih hs.2
  | case4 x y rest h ih =>
      intro hs
      rw [sortedB_cons, Bool.and_eq_true] at hs
      obtain ⟨hhead, htail⟩ := hs
      have hne : (x == y) = false := by simpa using h
      have hdedup : dedupAdj (x :: y :: rest) = x :: dedupAdj (y :: rest) := by
        simp [dedupAdj, hne]
      rw [hdedup, sortedB_cons, Bool.and_eq_true]
      refine ⟨headOk_of_head? (dedupAdj_head? y rest) ?_, ih htail⟩
      simpa [headOk] using hhead

/-- **RDFC-1.0 §3 output order.** Every adjacent pair of lines in the
canonical N-Quads document is in code point order, for every dataset
and every hash algorithm. -/
theorem canonicalLines_sorted (ds : Dataset) (alg : HashAlgorithm) :
    sortedB strLe (ds.canonicalLines alg) = true := by
  unfold L4Factoidal.RDF.Dataset.canonicalLines
  split <;> exact sortedB_dedupAdj _ (sortedB_sortStrings _)

/-! ## 2. Identifier issuance (RDFC-1.0 §4.8) -/

/-- Digit value of a decimal character, `0` for anything else — the
inverse of `digitChar` on `0..9`. -/
def digitVal : Char → Nat
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9
  | _   => 0

/-- Read a digit list back as a number, most significant first. -/
def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + digitVal c) 0

theorem digitVal_digitChar {d : Nat} (h : d < 10) : digitVal (digitChar d) = d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | (k + 10) => exact absurd h (by omega)

theorem digitsToNat_append_one (l : List Char) (c : Char) :
    digitsToNat (l ++ [c]) = digitsToNat l * 10 + digitVal c := by
  simp [digitsToNat, List.foldl_append]

/-- `natToDigits` is a faithful decimal rendering: reading it back
gives the original number. -/
theorem digitsToNat_natToDigits (n : Nat) : digitsToNat (natToDigits n) = n := by
  induction n using natToDigits.induct with
  | case1 n h =>
      have hn : natToDigits n = [digitChar n] := by rw [natToDigits]; simp [h]
      rw [hn]
      simp [digitsToNat, digitVal_digitChar h]
  | case2 n h ih =>
      have hn : natToDigits n = natToDigits (n / 10) ++ [digitChar (n % 10)] := by
        rw [natToDigits]; simp [h]
      rw [hn, digitsToNat_append_one, ih, digitVal_digitChar (Nat.mod_lt n (by omega))]
      omega

/-- Therefore decimal rendering is injective. -/
theorem natToDigits_inj {m n : Nat} (h : natToDigits m = natToDigits n) : m = n := by
  have hm := digitsToNat_natToDigits m
  rw [h, digitsToNat_natToDigits] at hm
  exact hm.symm

/-- **The issued-label shape is injective in the counter.** Two
different counter values under the same prefix can never produce the
same label. -/
theorem mkLabel_inj {pfx : String} {m n : Nat} (h : mkLabel pfx m = mkLabel pfx n) : m = n := by
  unfold mkLabel at h
  have h2 : pfx.toList ++ natToDigits m = pfx.toList ++ natToDigits n := by
    have := congrArg String.toList h
    simpa using this
  exact natToDigits_inj (List.append_cancel_left h2)

/-! ### The issuer invariant -/

/-- Every `(blank node, label)` pair the issuer holds carries a label
of the form `<prefix><decimal>` with a counter value strictly below
the issuer's current counter. (The `_:` itself is added at RENDER
time; this covers the part §4.8 actually controls.) -/
def IssuerLabelsWf (st : IssuerState) : Prop :=
  ∀ b l, (b, l) ∈ st.issued → ∃ k, k < st.counter ∧ l = mkLabel st.labelPrefix k

/-- Distinct blank nodes never share a canonical identifier. -/
def IssuerLabelsInjective (st : IssuerState) : Prop :=
  ∀ b₁ l₁ b₂ l₂, (b₁, l₁) ∈ st.issued → (b₂, l₂) ∈ st.issued → l₁ = l₂ → b₁ = b₂

theorem emptyIssuer_wf : IssuerLabelsWf emptyIssuer := by
  intro b l h; simp [emptyIssuer] at h

theorem emptyTempIssuer_wf : IssuerLabelsWf emptyTempIssuer := by
  intro b l h; simp [emptyTempIssuer] at h

theorem emptyIssuer_injective : IssuerLabelsInjective emptyIssuer := by
  intro _ _ _ _ h _ _; simp [emptyIssuer] at h

theorem emptyTempIssuer_injective : IssuerLabelsInjective emptyTempIssuer := by
  intro _ _ _ _ h _ _; simp [emptyTempIssuer] at h

theorem issueFresh_wf {st : IssuerState} (h : IssuerLabelsWf st) (b : BNodeId) :
    IssuerLabelsWf (issueFresh st b) := by
  intro b' l' hmem
  simp only [issueFresh, List.mem_cons, Prod.mk.injEq] at hmem ⊢
  rcases hmem with ⟨_, hl⟩ | hmem
  · exact ⟨st.counter, by omega, hl⟩
  · obtain ⟨k, hk, hl⟩ := h b' l' hmem
    exact ⟨k, by omega, hl⟩

theorem issueIdentifier_wf {st : IssuerState} (h : IssuerLabelsWf st) (b : BNodeId) :
    IssuerLabelsWf (issueIdentifier st b).1 := by
  unfold issueIdentifier
  split
  · exact h
  · intro b' l' hmem
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hmem ⊢
    rcases hmem with hmem | ⟨_, hl⟩
    · obtain ⟨k, hk, hl⟩ := h b' l' hmem
      exact ⟨k, by omega, hl⟩
    · exact ⟨st.counter, by omega, hl⟩

/-- **The issuer step lemma.** The label §4.8 is about to mint differs
from every label already issued — because every issued label carries a
counter value strictly below the current one, and `mkLabel` is
injective in that value. This is what makes issuance injective. -/
theorem issueFresh_label_fresh {st : IssuerState} (h : IssuerLabelsWf st)
    {b' l' : String} (hmem : (b', l') ∈ st.issued) :
    l' ≠ mkLabel st.labelPrefix st.counter := by
  intro heq
  obtain ⟨k, hk, hl⟩ := h b' l' hmem
  rw [hl] at heq
  exact absurd (mkLabel_inj heq) (by omega)

/-- Issuing preserves injectivity: the new label collides with nothing
already present (step lemma above), so no two blank nodes can end up
sharing one. -/
theorem issueFresh_injective {st : IssuerState} (hwf : IssuerLabelsWf st)
    (hinj : IssuerLabelsInjective st) (b : BNodeId) :
    IssuerLabelsInjective (issueFresh st b) := by
  intro b₁ l₁ b₂ l₂ h₁ h₂ hl
  simp only [issueFresh, List.mem_cons, Prod.mk.injEq] at h₁ h₂ ⊢
  rcases h₁ with ⟨hb₁, hlab₁⟩ | h₁ <;> rcases h₂ with ⟨hb₂, hlab₂⟩ | h₂
  · exact hb₁.trans hb₂.symm
  · exact absurd (hl.symm.trans hlab₁) (issueFresh_label_fresh hwf h₂)
  · exact absurd (hl.trans hlab₂) (issueFresh_label_fresh hwf h₁)
  · exact hinj b₁ l₁ b₂ l₂ h₁ h₂ hl

theorem issueIdentifier_injective {st : IssuerState} (hwf : IssuerLabelsWf st)
    (hinj : IssuerLabelsInjective st) (b : BNodeId) :
    IssuerLabelsInjective (issueIdentifier st b).1 := by
  unfold issueIdentifier
  split
  · exact hinj
  · intro b₁ l₁ b₂ l₂ h₁ h₂ hl
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at h₁ h₂
    rcases h₁ with h₁ | ⟨hb₁, hlab₁⟩ <;> rcases h₂ with h₂ | ⟨hb₂, hlab₂⟩
    · exact hinj b₁ l₁ b₂ l₂ h₁ h₂ hl
    · exact absurd (hl.trans hlab₂) (issueFresh_label_fresh hwf h₁)
    · exact absurd (hl.symm.trans hlab₁) (issueFresh_label_fresh hwf h₂)
    · exact hb₁.trans hb₂.symm

/-! ## 3. Relabelling invariance (RDFC-1.0's whole purpose)

The sub-lemmas below are the reason the algorithm works at all: §4.5
replaces the target blank node by `_:a` and every other by `_:z`
BEFORE serialising, so nothing downstream of that rewrite can observe
the input labels. Each lemma states that precisely, for an arbitrary
injective relabelling. -/

/-- `f` never merges two labels. -/
def InjectiveLabels (f : BNodeId → BNodeId) : Prop := ∀ a b, f a = f b → a = b

theorem beq_map_of_injective {f : BNodeId → BNodeId} (hf : InjectiveLabels f) (a b : BNodeId) :
    (f a == f b) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have hne : f a ≠ f b := fun hfe => h (hf a b hfe)
    rw [show (f a == f b) = false from beq_eq_false_iff_ne.mpr hne,
        show (a == b) = false from beq_eq_false_iff_ne.mpr h]

/-- §4.5's subject rewrite is blind to an injective relabelling. -/
theorem rewriteSubjectForHfdq_rename {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (target : BNodeId) (s : Subject) :
    rewriteSubjectForHfdq (f target) (s.renameBnodes f) = rewriteSubjectForHfdq target s := by
  cases s with
  | iri i => rfl
  | bnode b => simp [Subject.renameBnodes, rewriteSubjectForHfdq, beq_map_of_injective hf]

/-- §4.5's term rewrite is blind to an injective relabelling —
including inside RDF 1.2 triple terms. -/
theorem rewriteTermForHfdq_rename {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (target : BNodeId) (t : Term) :
    rewriteTermForHfdq (f target) (t.renameBnodes f) = rewriteTermForHfdq target t := by
  induction t with
  | iri i => rfl
  | bnode b => simp [Term.renameBnodes, rewriteTermForHfdq, beq_map_of_injective hf]
  | literal l => rfl
  | tripleTerm s p o ih =>
      simp [Term.renameBnodes, rewriteTermForHfdq,
            rewriteSubjectForHfdq_rename hf, ih]

theorem rewriteTripleForHfdq_rename {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (target : BNodeId) (t : Triple) :
    rewriteTripleForHfdq (f target) (t.renameBnodes f) = rewriteTripleForHfdq target t := by
  simp [rewriteTripleForHfdq, Triple.renameBnodes,
        rewriteSubjectForHfdq_rename hf, rewriteTermForHfdq_rename hf]

theorem bnodesInTerm_rename (f : BNodeId → BNodeId) (t : Term) :
    bnodesInTerm (t.renameBnodes f) = (bnodesInTerm t).map f := by
  induction t with
  | iri i => rfl
  | bnode b => rfl
  | literal l => rfl
  | tripleTerm s p o ih =>
      cases s <;> simp [Term.renameBnodes, Subject.renameBnodes, bnodesInTerm, ih]

/-- Membership testing is blind to an injective relabelling. -/
theorem contains_map_of_injective {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (target : BNodeId) :
    ∀ l : List BNodeId, (l.map f).contains (f target) = l.contains target := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.contains_cons, beq_map_of_injective hf, ih]

/-- Whether a quad mentions a blank node is invariant under an
injective relabelling. Stated for quads whose graph slot is not a
blank node — see `RelabellingInvariance` for why the blank-node graph
label case is left open. -/
theorem quadMentionsBnode_rename {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (target : BNodeId) (g : Option Iri) (t : Triple)
    (hg : ∀ gi, g = some gi → isBnodeGraphLabel gi = false) :
    quadMentionsBnode (f target) (g, t.renameBnodes f) = quadMentionsBnode target (g, t) := by
  obtain ⟨sub, pred, obj⟩ := t
  cases g with
  | none =>
      cases sub with
      | iri i =>
          simp only [quadMentionsBnode, Triple.renameBnodes, Subject.renameBnodes,
                     bnodesInTerm_rename, contains_map_of_injective hf]
      | bnode b =>
          simp only [quadMentionsBnode, Triple.renameBnodes, Subject.renameBnodes,
                     bnodesInTerm_rename, contains_map_of_injective hf,
                     beq_map_of_injective hf]
  | some gi =>
      have hgi : isBnodeGraphLabel gi = false := hg gi rfl
      cases sub with
      | iri i =>
          simp only [quadMentionsBnode, Triple.renameBnodes, Subject.renameBnodes,
                     bnodesInTerm_rename, contains_map_of_injective hf, hgi,
                     Bool.false_and]
      | bnode b =>
          simp only [quadMentionsBnode, Triple.renameBnodes, Subject.renameBnodes,
                     bnodesInTerm_rename, contains_map_of_injective hf,
                     beq_map_of_injective hf, hgi, Bool.false_and]

/-- **The rendered first-degree form of a quad is blind to an
injective relabelling** — RDFC-1.0 §4.5's `_:a`/`_:z` placeholders in
action. Every later step of §4.5 (sort, concatenate, hash) is a
function of exactly these strings. -/
theorem renderForHfdq_rename {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (target : BNodeId) (g : Option Iri) (t : Triple)
    (hg : ∀ gi, g = some gi → isBnodeGraphLabel gi = false) :
    renderForHfdq (f target) (g, t.renameBnodes f) = renderForHfdq target (g, t) := by
  have hgr : rewriteGraphForHfdq (f target) g = rewriteGraphForHfdq target g := by
    cases g with
    | none => rfl
    | some gi => simp [rewriteGraphForHfdq, hg gi rfl]
  simp only [renderForHfdq, hgr, rewriteTripleForHfdq_rename hf]

/-- The §4.5 rendered-quad LIST of a blank node is unchanged by an
injective relabelling. -/
theorem hfdqRenders_rename {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (target : BNodeId) :
    ∀ qs : List QQuad,
      (∀ q ∈ qs, ∀ gi, q.1 = some gi → isBnodeGraphLabel gi = false) →
      (quadsForBnode (f target) (qs.map (fun q => (q.1, q.2.renameBnodes f)))).map
          (renderForHfdq (f target))
        = (quadsForBnode target qs).map (renderForHfdq target) := by
  intro qs
  induction qs with
  | nil => intro _; rfl
  | cons q rest ih =>
      intro hqs
      have hq : ∀ gi, q.1 = some gi → isBnodeGraphLabel gi = false := hqs q (by simp)
      have hrest : ∀ q' ∈ rest, ∀ gi, q'.1 = some gi → isBnodeGraphLabel gi = false :=
        fun q' hm => hqs q' (by simp [hm])
      have hm : quadMentionsBnode (f target) (q.1, q.2.renameBnodes f)
              = quadMentionsBnode target q :=
        quadMentionsBnode_rename hf target q.1 q.2 hq
      simp only [quadsForBnode, List.map_cons, List.filter_cons, hm]
      by_cases h : quadMentionsBnode target q = true
      · simp only [h, if_pos, List.map_cons]
        rw [show renderForHfdq (f target) (q.1, q.2.renameBnodes f) = renderForHfdq target q from
              renderForHfdq_rename hf target q.1 q.2 hq]
        exact congrArg _ (ih hrest)
      · simp only [Bool.not_eq_true] at h
        simp only [h, Bool.false_eq_true]
        exact ih hrest

/-- **Hash First Degree Quads is invariant under injective
relabelling** (RDFC-1.0 §4.5), for datasets with no blank-node graph
labels. This is the load-bearing sub-result: it is why two isomorphic
datasets produce the same §4.4 hash-to-blank-nodes map, which is where
the canonical identifiers come from. -/
theorem hashFirstDegreeQuads_rename {f : BNodeId → BNodeId} (hf : InjectiveLabels f)
    (alg : HashAlgorithm) (target : BNodeId) (qs : List QQuad)
    (hqs : ∀ q ∈ qs, ∀ gi, q.1 = some gi → isBnodeGraphLabel gi = false) :
    hashFirstDegreeQuads alg (f target) (qs.map (fun q => (q.1, q.2.renameBnodes f)))
      = hashFirstDegreeQuads alg target qs := by
  simp only [hashFirstDegreeQuads, hfdqRenders_rename hf target qs hqs]

/-- Non-vacuity check for every hypothesis above: `InjectiveLabels` is
satisfied by a genuinely label-changing function, not only by the
identity. (A lemma whose hypotheses no interesting function meets
would be true and useless; the `#guard`s in `RDF/CanonicalTests.lean`
exercise the same property on concrete relabelled datasets.) -/
theorem prefixLabels_injective (p : String) : InjectiveLabels (fun b => p ++ b) := by
  intro a b h
  have h2 : p.toList ++ a.toList = p.toList ++ b.toList := by
    simpa using congrArg String.toList h
  have h3 : a.toList = b.toList := List.append_cancel_left h2
  simpa using congrArg String.ofList h3

/-! ### The main theorem — STATED, NOT PROVED

Everything above is a lemma about §4.5. The theorem RDFC-1.0 actually
promises is the one below. It is a `Prop`-valued DEFINITION, not a
`theorem`, precisely so that nothing in this file claims a proof that
does not exist.

What still stands between the lemmas above and this statement:

  * §4.4 step 3 builds the hash-to-blank-nodes map from
    `datasetBnodes`, which SORTS the labels. `hashFirstDegreeQuads_
    rename` shows each blank node keeps its hash under relabelling,
    but the map is keyed by hash and grouped by a stable sort whose
    within-group order comes from the labels; showing the GROUPING is
    label-independent needs a permutation argument the sort lemmas
    above do not yet supply (they prove sortedness, not that sorting
    is a permutation, and not that a stable sort of a permuted input
    yields a permuted output).
  * §4.7's permutation loop threads a temporary issuer whose labels
    (`b0`, `b1`, …) depend on the order in which members are visited;
    invariance there needs the corresponding statement about
    `hndqRun`, by induction on its fuel.
  * §4.4 step 5.3's tie-break is first-explored-wins, which is a
    choice the spec leaves open; a full invariance proof has to show
    the tie can only arise between genuine automorphisms.
  * Blank-node GRAPH LABELS are excluded from the sub-lemmas above
    (the `isBnodeGraphLabel gi = false` hypotheses). The obstacle is
    not mathematical but representational: `NamedGraph.name` is an
    `Iri` string carrying a `"_:"` sentinel, so the graph-slot lemmas
    need `("_:" ++ x).startsWith "_:"`-style reasoning about `String`
    append, which the byte-backed `String` of this toolchain does not
    give up cheaply. Giving `NamedGraph.name` a sum type would remove
    the hypothesis entirely; that is a change to `RDF/Graph.lean`,
    owned elsewhere.

The corpus probe (`lake exe l4rdfc-probe`, 86 of 86) and the
`#guard`s in `RDF/CanonicalTests.lean` are the current EVIDENCE for
this property. They are tests, not a proof, and this file does not
pretend otherwise. -/
def RelabellingInvariance : Prop :=
  ∀ (g1 g2 : Graph) (alg : HashAlgorithm),
    Graph.Isomorphic g1 g2 →
      Dataset.canonicalNQuads { default := g1, named := [] } alg
        = Dataset.canonicalNQuads { default := g2, named := [] } alg

/-- The weaker, purely syntactic form the sub-lemmas above are aimed
at: canonicalization is unchanged by applying an injective relabelling
to the dataset. Also STATED ONLY. -/
def RenamingInvariance : Prop :=
  ∀ (f : BNodeId → BNodeId) (g : Graph) (alg : HashAlgorithm),
    InjectiveLabels f →
      Dataset.canonicalNQuads { default := g.renameBnodes f, named := [] } alg
        = Dataset.canonicalNQuads { default := g, named := [] } alg

/-! ## Axiom audit -/

#print axioms canonicalLines_sorted
#print axioms mkLabel_inj
#print axioms issueFresh_label_fresh
#print axioms issueFresh_injective
#print axioms hashFirstDegreeQuads_rename

end L4Factoidal.RDF.Canonical
