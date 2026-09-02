/-
L4Factoidal.SPARQL.IndexedEvalRefinement — the indexed evaluation path
returns EXACTLY what the specification evaluator returns.

`SPARQL/Algebra.lean` holds two evaluators for the same three
operations. The specification trio — `join` and `leftJoin`
(nested-loop compatible-merge, §18.5) and `evalBgp` (per-row graph
scans, §18.3) — is what every earlier theorem is stated about. The
engine trio — `hashJoin`, `hashLeftJoin` and `evalBgpIdx` — buckets one
side by a canonicalised key (`Term.joinKey`, RDF/Core.lean) in a
`Std.HashMap` and probes instead of scanning. `GraphPattern.evalIn`
runs the engine trio, and `StoreDataset.evalPatternBackend`'s
`.leftJoin` arm runs `hashLeftJoin`.

This file proves the three equalities that license that wiring:

  * `hashJoin_eq_join`   : `hashJoin o1 o2 = join o1 o2`
  * `hashLeftJoin_eq_leftJoin` :
    `hashLeftJoin o1 o2 cond = leftJoin o1 o2 cond`
  * `evalBgpIdx_eq_evalBgp` : `evalBgpIdx b g = evalBgp b g`

Both are plain LIST equalities — same rows, same order, same binding
layouts — not merely multiset agreement. Nothing downstream (DISTINCT,
ORDER BY, slicing, result serialisation) can observe the switch, and
every theorem about `join`/`evalBgp` transfers across `rw`.

Why the equalities hold, in one paragraph each:

JOIN. `joinKeyVars` only admits variables bound in EVERY row of both
sides, so each side's key (`Binding.hashKey?`) is total on its rows.
Compatibility forces eqb-equal values on shared variables
(`Binding.compatible_lookup`), and `Term.joinKey` is constant on
eqb-classes (`Term.joinKey_eq_of_eqb`), so compatible rows carry EQUAL
keys — a row in any other bucket is incompatible and would have been
filtered out by the nested loop anyway. Buckets preserve the build
side's order (`bucketOf_groupByKey`: a bucket IS `filter (key · = k)`),
so dropping the provably-incompatible rows changes nothing
(`filterMap_eq_of_none_of_filter`). `bucketProbe_filterMap_eq` states
that argument once, for any per-row map that returns `none` on
incompatible rows.

LEFT JOIN. The same core, applied to the map that also tests the
OPTIONAL condition. Because the two `filterMap`s are equal as LISTS,
the `extended.isEmpty` test that decides between the extensions and the
unextended left row sees the same list on both sides, so the
unextended rows land in the same places.

BGP. For one triple pattern, a row's probe key (`probeKey?`) covers
the positions the pattern pins under that row — constants and
already-bound variables. A successful `tpMatch` forces each pinned
position to be eqb-equal to the data triple's term at that position
(`tryBindSubject_key`, `tryBindTerm_key`; bindings made EARLIER in the
same match cannot disturb a pinned position because matching only ever
binds previously-unbound variables — the `preserves_lookup` lemmas),
so every matching triple's `tripleKey` equals the probe key: the
probed bucket loses only non-matching triples, in order.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Buckets are ordered filters -/

theorem groupByKeyAux_getD {κ α : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]
    (key : α → κ) :
    ∀ (l : List α) (m : Std.HashMap κ (List α)) (k : κ),
      (groupByKeyAux key l m).getD k []
        = (l.filter (fun a => key a == k)).reverse ++ m.getD k []
  | [], m, k => by simp [groupByKeyAux]
  | a :: rest, m, k => by
      rw [groupByKeyAux, groupByKeyAux_getD key rest _ k,
          Std.HashMap.getD_insert]
      by_cases hk : key a = k
      · subst hk
        simp
      · have hb : (key a == k) = false := by simpa using hk
        simp [hb]

/-- A bucket read back through `bucketOf` is the filter of the grouped
list at that key, in the list's own order. -/
theorem bucketOf_groupByKey {κ α : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]
    (key : α → κ) (l : List α) (k : κ) :
    bucketOf (groupByKey key l) k = l.filter (fun a => key a == k) := by
  unfold bucketOf groupByKey
  rw [groupByKeyAux_getD, Std.HashMap.getD_empty]
  simp

/-- Filtering before `filterMap` loses nothing when every row the
filter drops maps to `none` anyway. -/
theorem filterMap_eq_of_none_of_filter {α β : Type}
    (f : α → Option β) (p : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = false → f a = none) →
      (l.filter p).filterMap f = l.filterMap f
  | [], _ => rfl
  | a :: rest, h => by
      have ih := filterMap_eq_of_none_of_filter f p rest
        (fun x hx => h x (List.mem_cons_of_mem a hx))
      cases hp : p a with
      | true => simp [hp, List.filterMap_cons, ih]
      | false =>
          have hnone := h a (List.mem_cons_self ..) hp
          simp [hp, hnone, ih]

private theorem flatMap_congr {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: rest, h => by
      rw [List.flatMap_cons, List.flatMap_cons,
          h a (List.mem_cons_self ..),
          flatMap_congr (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- Destruct `(if c then some a else none) = some b`. -/
private theorem of_ite_some {α : Type} {c : Prop} [Decidable c] {a b : α}
    (h : (if c then some a else none) = some b) : c ∧ b = a := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h; exact ⟨hc, rfl⟩
  · rw [if_neg hc] at h; cases h

/-! ## The hash join equals the nested-loop join -/

/-- Compatibility (§18.3) pins the values two rows give a variable
they both bind: they are eqb-equal. -/
theorem Binding.compatible_lookup :
    ∀ {mu1 mu2 : Binding}, mu1.compatible mu2 = true →
      ∀ {v : VarName} {t1 t2 : Term},
        mu1.lookup v = some t1 → mu2.lookup v = some t2 →
        t1.eqb t2 = true := by
  intro mu1
  induction mu1 with
  | nil => intro mu2 h v t1 t2 h1 h2; simp [Binding.lookup] at h1
  | cons hd rest ih =>
      obtain ⟨w, t⟩ := hd
      intro mu2 h v t1 t2 h1 h2
      simp only [Binding.compatible, Bool.and_eq_true] at h
      obtain ⟨hhead, htail⟩ := h
      simp only [Binding.lookup] at h1
      by_cases hwv : w = v
      · subst hwv
        rw [if_pos rfl] at h1
        cases h1
        rw [h2] at hhead
        exact hhead
      · rw [if_neg hwv] at h1
        exact ih htail h1 h2

/-- A row binding every key variable has a key. -/
theorem Binding.hashKey?_isSome :
    ∀ (kvs : List VarName) (mu : Binding),
      (∀ v ∈ kvs, (mu.lookup v).isSome) →
      (Binding.hashKey? kvs mu).isSome
  | [], _, _ => rfl
  | v :: vs, mu, h => by
      have hv := h v (List.mem_cons_self ..)
      have hvs := Binding.hashKey?_isSome vs mu
        (fun x hx => h x (List.mem_cons_of_mem v hx))
      rw [Binding.hashKey?]
      cases hl : mu.lookup v with
      | none => rw [hl] at hv; simp at hv
      | some t =>
          cases hk : Binding.hashKey? vs mu with
          | none => rw [hk] at hvs; simp at hvs
          | some ts => rfl

/-- Compatible rows carry EQUAL keys: componentwise, compatibility
gives eqb-equality and `Term.joinKey` collapses eqb-classes. -/
theorem Binding.hashKey?_eq_of_compatible :
    ∀ (kvs : List VarName) {mu1 mu2 : Binding} {k1 k2 : List Term},
      mu1.compatible mu2 = true →
      Binding.hashKey? kvs mu1 = some k1 →
      Binding.hashKey? kvs mu2 = some k2 → k1 = k2
  | [], _, _, _, _, _, h1, h2 => by
      simp only [Binding.hashKey?] at h1 h2
      cases h1; cases h2; rfl
  | v :: vs, mu1, mu2, k1, k2, hc, h1, h2 => by
      simp only [Binding.hashKey?] at h1 h2
      cases hl1 : mu1.lookup v with
      | none => rw [hl1] at h1; cases h1
      | some t1 =>
          rw [hl1] at h1
          cases hk1 : Binding.hashKey? vs mu1 with
          | none => rw [hk1] at h1; cases h1
          | some ts1 =>
              rw [hk1] at h1
              cases hl2 : mu2.lookup v with
              | none => rw [hl2] at h2; cases h2
              | some t2 =>
                  rw [hl2] at h2
                  cases hk2 : Binding.hashKey? vs mu2 with
                  | none => rw [hk2] at h2; cases h2
                  | some ts2 =>
                      rw [hk2] at h2
                      cases h1; cases h2
                      have heq := Binding.compatible_lookup hc hl1 hl2
                      rw [Term.joinKey_eq_of_eqb heq,
                          Binding.hashKey?_eq_of_compatible vs hc hk1 hk2]

/-- **The bucket-probe core**, shared by the hash join and the hash
left join. Probing ONE bucket loses nothing, for any per-row map `f`
that returns `none` on rows incompatible with the probe row: every
build row the bucket drops carries a different key, and a different key
means incompatible (`Binding.hashKey?_eq_of_compatible`), so `f` maps
it to `none` anyway. `bucketOf_groupByKey` supplies the order. -/
theorem bucketProbe_filterMap_eq {β : Type} (kvs : List VarName)
    (mu1 : Binding) (o2 : SolutionSeq) (k : List Term)
    (f : Binding → Option β)
    (hb : ∀ v ∈ kvs, ∀ m ∈ o2, (Binding.lookup v m).isSome)
    (hk1 : Binding.hashKey? kvs mu1 = some k)
    (hf : ∀ mu2, mu1.compatible mu2 = false → f mu2 = none) :
    (bucketOf (groupByKey (Binding.hashKey? kvs) o2) (some k)).filterMap f
      = o2.filterMap f := by
  rw [bucketOf_groupByKey]
  apply filterMap_eq_of_none_of_filter
  intro mu2 hmu2 hp
  by_cases hc : mu1.compatible mu2 = true
  · exfalso
    have h2s : (Binding.hashKey? kvs mu2).isSome :=
      Binding.hashKey?_isSome kvs mu2 (fun v hv => hb v hv mu2 hmu2)
    cases hk2 : Binding.hashKey? kvs mu2 with
    | none => rw [hk2] at h2s; simp at h2s
    | some k2 =>
        have : k = k2 := Binding.hashKey?_eq_of_compatible kvs hc hk1 hk2
        subst this
        rw [hk2] at hp
        simp at hp
  · simp only [Bool.not_eq_true] at hc
    exact hf mu2 hc

/-- The keyed hash join equals the nested loop whenever every build
row binds every key variable. -/
theorem hashJoinKeyed_eq_join (kvs : List VarName)
    (o1 o2 : SolutionSeq)
    (hb : ∀ v ∈ kvs, ∀ m ∈ o2, (Binding.lookup v m).isSome) :
    hashJoinKeyed kvs o1 o2 = join o1 o2 := by
  unfold hashJoinKeyed join
  apply flatMap_congr
  intro mu1 _
  cases hk1 : Binding.hashKey? kvs mu1 with
  | none => rfl
  | some k =>
      show (bucketOf (groupByKey (Binding.hashKey? kvs) o2)
              (some k)).filterMap
             (fun mu2 => if mu1.compatible mu2 = true
                         then some (mu1.merge mu2) else none)
           = o2.filterMap
             (fun mu2 => if mu1.compatible mu2 = true
                         then some (mu1.merge mu2) else none)
      exact bucketProbe_filterMap_eq kvs mu1 o2 k _ hb hk1
        (fun mu2 hc => by rw [hc]; rfl)

/-- Every variable `joinKeyVars` admits is bound in every row of the
BUILD side — the hypothesis both keyed theorems take. -/
theorem joinKeyVars_bound_right (o1 o2 : SolutionSeq) :
    ∀ v ∈ joinKeyVars o1 o2, ∀ m ∈ o2, (Binding.lookup v m).isSome := by
  cases o1 with
  | nil => intro v hv; simp [joinKeyVars] at hv
  | cons mu1 rest =>
      intro v hv m hm
      simp only [joinKeyVars] at hv
      have := (List.mem_filter.mp hv).2
      simp only [Bool.and_eq_true, List.all_eq_true] at this
      exact this.2 m hm

/-- **The join theorem.** The hash join returns the same solution
sequence as §18.5's nested-loop `join` — the same LIST: same rows,
same order, same binding layouts. -/
theorem hashJoin_eq_join (o1 o2 : SolutionSeq) :
    hashJoin o1 o2 = join o1 o2 := by
  unfold hashJoin
  cases hkv : joinKeyVars o1 o2 with
  | nil => rfl
  | cons v0 vs0 =>
      apply hashJoinKeyed_eq_join
      intro v hv m hm
      exact joinKeyVars_bound_right o1 o2 v (by rw [hkv]; exact hv) m hm

/-! ## The hash left join equals the nested-loop left join -/

/-- The keyed hash left join equals the nested loop whenever every
build row binds every key variable. The per-μ1 candidate list changes
from Ω2 to Ω2's bucket at μ1's key; `bucketProbe_filterMap_eq` shows
the two `filterMap`s agree as LISTS, so the `extended.isEmpty` test
that decides between the extensions and the unextended μ1 sees the same
list on both sides. -/
theorem hashLeftJoinKeyed_eq_leftJoin (kvs : List VarName)
    (o1 o2 : SolutionSeq) (cond : Binding → Bool)
    (hb : ∀ v ∈ kvs, ∀ m ∈ o2, (Binding.lookup v m).isSome) :
    hashLeftJoinKeyed kvs o1 o2 cond = leftJoin o1 o2 cond := by
  unfold hashLeftJoinKeyed leftJoin
  apply flatMap_congr
  intro mu1 _
  cases hk1 : Binding.hashKey? kvs mu1 with
  | none => rfl
  | some k =>
      have hcore := bucketProbe_filterMap_eq kvs mu1 o2 k
        (fun mu2 =>
          if mu1.compatible mu2 = true then
            (if cond (mu1.merge mu2) = true then some (mu1.merge mu2) else none)
          else none)
        hb hk1 (fun mu2 hc => by rw [hc]; rfl)
      show (if ((bucketOf (groupByKey (Binding.hashKey? kvs) o2)
                  (some k)).filterMap
                 (fun mu2 =>
                   if mu1.compatible mu2 = true then
                     (if cond (mu1.merge mu2) = true
                      then some (mu1.merge mu2) else none)
                   else none)).isEmpty
            then [mu1]
            else (bucketOf (groupByKey (Binding.hashKey? kvs) o2)
                   (some k)).filterMap
                  (fun mu2 =>
                    if mu1.compatible mu2 = true then
                      (if cond (mu1.merge mu2) = true
                       then some (mu1.merge mu2) else none)
                    else none))
           = (if (o2.filterMap
                   (fun mu2 =>
                     if mu1.compatible mu2 = true then
                       (if cond (mu1.merge mu2) = true
                        then some (mu1.merge mu2) else none)
                     else none)).isEmpty
              then [mu1]
              else o2.filterMap
                    (fun mu2 =>
                      if mu1.compatible mu2 = true then
                        (if cond (mu1.merge mu2) = true
                         then some (mu1.merge mu2) else none)
                      else none))
      rw [hcore]

/-- **The left-join theorem.** The hash left join returns the same
solution sequence as §18.5's nested-loop `leftJoin` — the same LIST:
same rows, same order, same binding layouts, unextended left rows
included. -/
theorem hashLeftJoin_eq_leftJoin (o1 o2 : SolutionSeq)
    (cond : Binding → Bool) :
    hashLeftJoin o1 o2 cond = leftJoin o1 o2 cond := by
  unfold hashLeftJoin
  cases hkv : joinKeyVars o1 o2 with
  | nil => rfl
  | cons v0 vs0 =>
      apply hashLeftJoinKeyed_eq_leftJoin
      intro v hv m hm
      exact joinKeyVars_bound_right o1 o2 v (by rw [hkv]; exact hv) m hm

/-! ## The indexed BGP equals the specification BGP -/

/-- Matching only ever binds a previously-unbound variable, so every
binding the seed row already had survives — subject position. -/
theorem tryBindSubject_preserves_lookup {ps : PatternSubject}
    {s : Subject} {mu mu' : Binding}
    (h : tryBindSubject ps s mu = some mu')
    {x : VarName} {t0 : Term} (hx : mu.lookup x = some t0) :
    mu'.lookup x = some t0 := by
  cases ps with
  | iri i =>
      cases s with
      | iri i' =>
          simp only [tryBindSubject] at h
          obtain ⟨-, rfl⟩ := of_ite_some h
          exact hx
      | bnode b => simp [tryBindSubject] at h
  | bnode b =>
      cases s with
      | iri i' => simp [tryBindSubject] at h
      | bnode b' =>
          simp only [tryBindSubject] at h
          obtain ⟨-, rfl⟩ := of_ite_some h
          exact hx
  | tripleTerm a b c => simp [tryBindSubject] at h
  | var w =>
      simp only [tryBindSubject] at h
      cases hw : mu.lookup w with
      | some ex =>
          rw [hw] at h
          obtain ⟨-, rfl⟩ := of_ite_some h
          exact hx
      | none =>
          rw [hw] at h
          cases h
          simp only [Binding.bind, Binding.lookup]
          have hne : ¬ (w = x) := by
            intro he; rw [he, hx] at hw; cases hw
          rw [if_neg hne]
          exact hx

/-- ... and likewise through a term position (recursively through a
triple-term pattern's three sub-positions). -/
theorem tryBindTerm_preserves_lookup :
    ∀ {pt : PatternTerm} {t : Term} {mu mu' : Binding},
      tryBindTerm pt t mu = some mu' →
      ∀ {x : VarName} {t0 : Term}, mu.lookup x = some t0 →
        mu'.lookup x = some t0 := by
  intro pt
  induction pt with
  | iri i =>
      intro t mu mu' h x t0 hx
      cases t <;> simp only [tryBindTerm] at h
      case iri i' =>
        obtain ⟨-, rfl⟩ := of_ite_some h
        exact hx
      all_goals cases h
  | bnode b =>
      intro t mu mu' h x t0 hx
      cases t <;> simp only [tryBindTerm] at h
      case bnode b' =>
        obtain ⟨-, rfl⟩ := of_ite_some h
        exact hx
      all_goals cases h
  | literal l =>
      intro t mu mu' h x t0 hx
      cases t <;> simp only [tryBindTerm] at h
      case literal l' =>
        obtain ⟨-, rfl⟩ := of_ite_some h
        exact hx
      all_goals cases h
  | var w =>
      intro t mu mu' h x t0 hx
      simp only [tryBindTerm] at h
      cases hw : mu.lookup w with
      | some ex =>
          rw [hw] at h
          obtain ⟨-, rfl⟩ := of_ite_some h
          exact hx
      | none =>
          rw [hw] at h
          cases h
          simp only [Binding.bind, Binding.lookup]
          have hne : ¬ (w = x) := by
            intro he; rw [he, hx] at hw; cases hw
          rw [if_neg hne]
          exact hx
  | tripleTerm ps pp po ihs ihp iho =>
      intro t mu mu' h x t0 hx
      cases t <;> simp only [tryBindTerm] at h
      case tripleTerm s2 p2 o2 =>
        split at h
        · cases h
        · next mu1 h1 =>
            split at h
            · cases h
            · next mu2 h2 => exact iho h (ihp h2 (ihs h1 hx))
      all_goals cases h

/-- A successful subject match forces the pinned subject key: the data
subject's canonical key equals the resolved constant's. -/
theorem tryBindSubject_key {ps : PatternSubject} {s : Subject}
    {mu mu' : Binding} (h : tryBindSubject ps s mu = some mu')
    {c : Term} (hr : ps.resolveKey mu = some c) :
    s.toTerm.joinKey = c.joinKey := by
  cases ps with
  | iri i =>
      cases hr
      cases s with
      | iri i' =>
          simp only [tryBindSubject] at h
          obtain ⟨hb, -⟩ := of_ite_some h
          simp [eq_of_beq hb, Subject.toTerm, Term.joinKey]
      | bnode b => simp [tryBindSubject] at h
  | bnode b =>
      cases hr
      cases s with
      | iri i' => simp [tryBindSubject] at h
      | bnode b' =>
          simp only [tryBindSubject] at h
          obtain ⟨hb, -⟩ := of_ite_some h
          simp [eq_of_beq hb, Subject.toTerm, Term.joinKey]
  | tripleTerm a b c => cases hr
  | var w =>
      simp only [PatternSubject.resolveKey] at hr
      simp only [tryBindSubject] at h
      rw [hr] at h
      obtain ⟨hb, -⟩ := of_ite_some h
      exact (Term.joinKey_eq_of_eqb hb).symm

/-- ... and likewise for a pinned predicate or object position. -/
theorem tryBindTerm_key {pt : PatternTerm} {t : Term}
    {mu mu' : Binding} (h : tryBindTerm pt t mu = some mu')
    {c : Term} (hr : pt.resolveKey mu = some c) :
    t.joinKey = c.joinKey := by
  cases pt with
  | iri i =>
      cases hr
      cases t <;> simp only [tryBindTerm] at h
      case iri i' =>
        obtain ⟨hb, -⟩ := of_ite_some h
        simp [eq_of_beq hb, Term.joinKey]
      all_goals cases h
  | bnode b =>
      cases hr
      cases t <;> simp only [tryBindTerm] at h
      case bnode b' =>
        obtain ⟨hb, -⟩ := of_ite_some h
        simp [eq_of_beq hb, Term.joinKey]
      all_goals cases h
  | literal l =>
      cases hr
      cases t <;> simp only [tryBindTerm] at h
      case literal l' =>
        obtain ⟨hb, -⟩ := of_ite_some h
        simp only [Term.joinKey, Term.literal.injEq]
        exact Subtype.ext (Literal.joinKey_eq_of_eqb
          (by rw [Literal.eqb_symm]; exact hb))
      all_goals cases h
  | tripleTerm a b c => cases hr
  | var w =>
      simp only [PatternTerm.resolveKey] at hr
      simp only [tryBindTerm] at h
      rw [hr] at h
      obtain ⟨hb, -⟩ := of_ite_some h
      exact (Term.joinKey_eq_of_eqb hb).symm

/-- One masked probe-key component pins the corresponding data
component — subject position. -/
theorem maskedKey_subject {on : Bool} {ps : PatternSubject} {s : Subject}
    {mu mu' : Binding} (h : tryBindSubject ps s mu = some mu')
    {ks : List Term} (hk : maskedKey on (ps.resolveKey mu) = some ks) :
    (if on then [s.toTerm.joinKey] else []) = ks := by
  cases on with
  | false =>
      simp only [maskedKey] at hk
      cases hk
      rfl
  | true =>
      simp only [maskedKey, if_pos] at hk
      cases hr : ps.resolveKey mu with
      | none => rw [hr] at hk; cases hk
      | some c =>
          rw [hr] at hk
          cases hk
          simp [tryBindSubject_key h hr]

/-- ... term position, allowing the match to run under any extension
of the binding the key was resolved against. -/
theorem maskedKey_term {on : Bool} {pt : PatternTerm} {t : Term}
    {mu mub mu' : Binding}
    (hpres : ∀ {x : VarName} {t0 : Term},
      Binding.lookup x mu = some t0 → Binding.lookup x mub = some t0)
    (h : tryBindTerm pt t mub = some mu')
    {ks : List Term} (hk : maskedKey on (pt.resolveKey mu) = some ks) :
    (if on then [t.joinKey] else []) = ks := by
  cases on with
  | false =>
      simp only [maskedKey] at hk
      cases hk
      rfl
  | true =>
      simp only [maskedKey, if_pos] at hk
      cases hr : pt.resolveKey mu with
      | none => rw [hr] at hk; cases hk
      | some c =>
          rw [hr] at hk
          cases hk
          have hrb : pt.resolveKey mub = some c := by
            cases pt <;> simp only [PatternTerm.resolveKey] at hr ⊢
            case var w => exact hpres hr
            all_goals exact hr
          simp [tryBindTerm_key h hrb]

/-- A triple `tpMatch` accepts carries the probe key at the masked
positions. -/
theorem tpMatch_key {m : TpMask} {tp : TriplePattern} {t : Triple}
    {mu mu' : Binding} (h : tpMatch tp t mu = some mu')
    {k : List Term} (hk : probeKey? m tp mu = some k) :
    tripleKey m t = k := by
  unfold tpMatch at h
  split at h
  · cases h
  next mu1 h1 =>
    split at h
    · cases h
    next mu2 h2 =>
          unfold probeKey? at hk
          cases hks : maskedKey m.s (tp.s.resolveKey mu) with
          | none => rw [hks] at hk; cases hk
          | some ks =>
              rw [hks] at hk
              cases hkp : maskedKey m.p (tp.p.resolveKey mu) with
              | none => rw [hkp] at hk; cases hk
              | some kp =>
                  rw [hkp] at hk
                  cases hko : maskedKey m.o (tp.o.resolveKey mu) with
                  | none => rw [hko] at hk; cases hk
                  | some ko =>
                      rw [hko] at hk
                      cases hk
                      have pres1 : ∀ {x : VarName} {t0 : Term},
                          Binding.lookup x mu = some t0 →
                          Binding.lookup x mu1 = some t0 :=
                        fun hx => tryBindSubject_preserves_lookup h1 hx
                      have pres2 : ∀ {x : VarName} {t0 : Term},
                          Binding.lookup x mu = some t0 →
                          Binding.lookup x mu2 = some t0 :=
                        fun hx => tryBindTerm_preserves_lookup h2 (pres1 hx)
                      unfold tripleKey
                      rw [maskedKey_subject h1 hks,
                          maskedKey_term (fun hx => pres1 hx) h2 hkp,
                          maskedKey_term (fun hx => pres2 hx) h hko]

/-- `evalTP` against the bucketed graph is `evalTP` against the graph:
the probed bucket keeps, in order, every triple the pattern can match
under this row. -/
theorem evalTPIdx_eq (m : TpMask) (g : Graph) (tp : TriplePattern)
    (mu : Binding) :
    evalTPIdx m (groupByKey (tripleKey m) g) g tp mu = evalTP tp g mu := by
  unfold evalTPIdx
  cases hk : probeKey? m tp mu with
  | none => rfl
  | some k =>
      show List.filterMap (fun t => tpMatch tp t mu)
             (bucketOf (groupByKey (tripleKey m) g) k) = evalTP tp g mu
      rw [bucketOf_groupByKey]
      unfold evalTP
      apply filterMap_eq_of_none_of_filter
      intro t _ hp
      cases hm : tpMatch tp t mu with
      | none => rfl
      | some mu' =>
          rw [tpMatch_key hm hk] at hp
          simp at hp

/-- One indexed BGP step is the specification step over the same
rows. -/
theorem evalBgpStepIdx_eq (tp : TriplePattern) (g : Graph)
    (rows : SolutionSeq) :
    evalBgpStepIdx tp g rows = rows.flatMap (evalTP tp g) := by
  cases rows with
  | nil => rfl
  | cons mu0 rest =>
      simp only [evalBgpStepIdx]
      split
      · exact flatMap_congr (fun mu _ => evalTPIdx_eq _ g tp mu)
      · rfl

theorem evalBgpRowsIdx_eq (g : Graph) :
    ∀ (b : Bgp) (rows : SolutionSeq),
      evalBgpRowsIdx g b rows = rows.flatMap (evalBgpFrom g b)
  | [], rows => by
      simp only [evalBgpRowsIdx, evalBgpFrom, List.flatMap_singleton']
  | tp :: rest, rows => by
      rw [evalBgpRowsIdx, evalBgpStepIdx_eq, evalBgpRowsIdx_eq g rest,
          List.flatMap_assoc]
      rfl

/-- **The BGP theorem.** The indexed BGP evaluator returns the same
solution sequence as §18.3's `evalBgp` — the same LIST: same rows,
same order, same binding layouts. -/
theorem evalBgpIdx_eq_evalBgp (b : Bgp) (g : Graph) :
    evalBgpIdx b g = evalBgp b g := by
  unfold evalBgpIdx evalBgp
  rw [evalBgpRowsIdx_eq, List.flatMap_singleton]

/-! ## The wiring, stated

`GraphPattern.evalIn`'s `.bgp` arm runs `evalBgpIdx`; this pins that
the arm still DENOTES the specification's `evalBgp`. (The `.join`
arm's identity with `SPARQL.join` is `hashJoin_eq_join` applied to the
two recursive results; the arm itself has no unconditional equation to
state it against because of the SERVICE-variable special cases
matched before it.) -/

theorem evalIn_bgp (ds : Dataset) (active : Graph) (b : Bgp) :
    (GraphPattern.bgp b).evalIn ds active = evalBgp b active := by
  rw [GraphPattern.evalIn, evalBgpIdx_eq_evalBgp]

/-! ## Build-time differential checks

The hazardous case is the coarse engine equality: rows that agree only
up to language-tag CASE must land in one bucket and still join. -/

private def vX : VarName := "x"
private def vY : VarName := "y"
private def iriA : WfIri := ⟨"http://example.org/a", by decide⟩
private def iriB : WfIri := ⟨"http://example.org/b", by decide⟩
private def litEnUS : Term := .literal (Literal.langString "chat" "en-US")
private def litEnUSUpper : Term := .literal (Literal.langString "chat" "en-us")

/-! Tag case folds into one bucket: the eqb-compatible pair joins under
the hash join exactly as under the nested loop. -/
#guard hashJoin [[(vX, litEnUS)]] [[(vX, litEnUSUpper), (vY, .iri iriB)]]
        == join [[(vX, litEnUS)]] [[(vX, litEnUSUpper), (vY, .iri iriB)]]
#guard (hashJoin [[(vX, litEnUS)]] [[(vX, litEnUSUpper), (vY, .iri iriB)]]).length == 1

/-! Disagreeing keys drop the pair, agreeing keys keep it. -/
#guard (hashJoin [[(vX, .iri iriA)]] [[(vX, .iri iriB)]]).length == 0
#guard (hashJoin [[(vX, .iri iriA)]] [[(vX, .iri iriA)]]).length == 1

/-! No shared variable: the cross-product fallback. -/
#guard hashJoin [[(vX, .iri iriA)]] [[(vY, .iri iriB)]]
        == join [[(vX, .iri iriA)]] [[(vY, .iri iriB)]]

/-! Heterogeneous build side (an OPTIONAL-shaped Ω2): the second row
misses `x`, so `x` leaves the key and both rows still join. -/
#guard hashJoin [[(vX, .iri iriA)]] [[(vX, .iri iriA)], [(vY, .iri iriB)]]
        == join [[(vX, .iri iriA)]] [[(vX, .iri iriA)], [(vY, .iri iriB)]]

/-! ### LeftJoin

Three shapes, each against the nested loop: a left row that extends, a
left row with no compatible partner (kept unextended), and a condition
that rejects the only extension (also kept unextended). -/
private def alwaysTrue : Binding → Bool := fun _ => true
private def alwaysFalse : Binding → Bool := fun _ => false

private def ljLeft : SolutionSeq := [[(vX, .iri iriA)], [(vX, .iri iriB)]]
private def ljRight : SolutionSeq := [[(vX, .iri iriA), (vY, .iri iriB)]]

#guard hashLeftJoin ljLeft ljRight alwaysTrue == leftJoin ljLeft ljRight alwaysTrue
#guard (hashLeftJoin ljLeft ljRight alwaysTrue).length == 2
#guard hashLeftJoin ljLeft ljRight alwaysFalse == leftJoin ljLeft ljRight alwaysFalse
#guard (hashLeftJoin ljLeft ljRight alwaysFalse).length == 2

/-! Tag case folds into one bucket on the left-join path too. -/
#guard hashLeftJoin [[(vX, litEnUS)]] [[(vX, litEnUSUpper), (vY, .iri iriB)]] alwaysTrue
        == leftJoin [[(vX, litEnUS)]] [[(vX, litEnUSUpper), (vY, .iri iriB)]] alwaysTrue

/-! Heterogeneous domains — a left row missing the key variable, which
exercises the `none`-key fallback, and a build side whose second row
misses it, which keeps `x` out of the key entirely. -/
private def ljLeftHet : SolutionSeq := [[(vX, .iri iriA)], [(vY, .iri iriA)]]
private def ljRightHet : SolutionSeq :=
  [[(vX, .iri iriA), (vY, .iri iriB)], [(vY, .iri iriA)]]

#guard hashLeftJoin ljLeftHet ljRightHet alwaysTrue
        == leftJoin ljLeftHet ljRightHet alwaysTrue
#guard hashLeftJoinKeyed [vX] ljLeftHet [[(vX, .iri iriA), (vY, .iri iriB)]] alwaysTrue
        == leftJoin ljLeftHet [[(vX, .iri iriA), (vY, .iri iriB)]] alwaysTrue

/-! Empty right side: every left row survives unextended. -/
#guard hashLeftJoin ljLeft [] alwaysTrue == ljLeft

/-! ## Axiom audit -/

#print axioms hashJoin_eq_join
#print axioms hashLeftJoinKeyed_eq_leftJoin
#print axioms hashLeftJoin_eq_leftJoin
#print axioms evalBgpIdx_eq_evalBgp
#print axioms evalIn_bgp

end L4Factoidal.SPARQL
