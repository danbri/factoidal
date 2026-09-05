/-
L4Factoidal.Storage.LiteralGramIndex — the meaning of the LGI1 literal search
index.

Design record: `docs/designissues/2026-09-04-literal-token-index.md`.

`CONTAINS` is a SUBSTRING test, not a token test: "underwater" contains
"water" and is not the token "water". An index over whitespace-separated
tokens therefore cannot answer `CONTAINS(LCASE(STR(?l)), "water")`, and one
that tried would drop rows silently. This module indexes character 3-grams of
the case-folded lexical form instead, and the index is a CANDIDATE FILTER: it
returns a superset of the matching dictionary terms and the caller
re-evaluates the original SPARQL expression on the candidates. The rows are
the scan's rows by construction.

Two decisions are stated here and nothing downstream may restate them.

**The unit is a character.** `SPARQL.Expr.strContains` compares `List Char`,
so a byte n-gram index would be a second, disagreeing notion of substring.

**The fold is the engine's own `LCASE`.** `foldChars` maps `Char.toLower`
across the characters, which is exactly what `Expr.evalIn` computes for
`LCASE` through `String.toLower`. The two cannot drift because there is one
function.

## The superset theorem

`gramsSubset_of_containsSublist` is the property the whole construction rests
on: if the folded needle is a contiguous sublist of the folded lexical form,
then every 3-gram of the needle is a 3-gram of the lexical form. Composed
with `foldChars_containsSublist` (folding per character preserves the
substring relation) it gives `mem_candidatesSpec`: a dictionary term the
filter accepts is in the candidate list.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import Std.Data.HashMap
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.Storage.LiteralGramIndex

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## 1. The fold and the grams -/

/-- The gram length. A needle shorter than this has no gram to look up and
falls back to the scan. -/
def gramLength : Nat := 3

/-- The case fold, character by character. This is `String.toLower`'s
character map, which is what `LCASE` evaluates to. -/
def foldChars (cs : List Char) : List Char := cs.map Char.toLower

/-- The folded characters of a string. -/
def foldString (s : String) : List Char := foldChars s.toList

/-- The window walk: `count` windows of `n` characters, one per position,
sliding down the list. It is structural on `count`, and each step takes at
most `n` characters off the FRONT of the list it already holds.

Why it is not the obvious `(List.range k).map (fun i => (cs.drop i).take n)`:
that form calls `List.drop i` for every position, and `List.drop i` walks `i`
cons cells, so a literal of `L` characters costs about `L^2 / 2` cell steps.
Measured with `/usr/bin/sample` on a 52,428,626-byte N-Quads pack, 2026-09-05:
`List.drop` under `LiteralGramIndex.pairsOf` held 5,318 of the 14,904 samples
of a 20-second window in the publication phase, the largest single leaf in it.
`gramsOf_eq_windows` below states that this walk computes that list. -/
def gramsGo (n : Nat) : Nat → List Char → List (List Char)
  | 0, _ => []
  | _ + 1, [] => []
  | count + 1, cs@(_ :: rest) => cs.take n :: gramsGo n count rest

/-- Every contiguous window of `n` characters, left to right. When the input
is shorter than `n` there are none. -/
def gramsOf (n : Nat) (cs : List Char) : List (List Char) :=
  gramsGo n (cs.length + 1 - n) cs

/-- `gramsGo` is the positioned window list, as long as the requested window
count stays inside the input. -/
theorem gramsGo_eq_map (n : Nat) (hn : 0 < n) :
    ∀ (count : Nat) (cs : List Char), count + n ≤ cs.length + 1 →
      gramsGo n count cs = (List.range count).map (fun i => (cs.drop i).take n) := by
  intro count
  induction count with
  | zero => intro cs _; simp [gramsGo]
  | succ count ih =>
      intro cs hcount
      cases cs with
      | nil =>
          simp only [List.length_nil] at hcount
          omega
      | cons c rest =>
          have hrest : count + n ≤ rest.length + 1 := by
            simp only [List.length_cons] at hcount; omega
          simp only [gramsGo, ih rest hrest, List.range_succ_eq_map,
            List.map_cons, List.map_map, List.drop_zero, Function.comp_def,
            List.drop_succ_cons]

/-- The specification form of `gramsOf`: the map over positions. Every proof
below reasons with this equation rather than with the walk. -/
theorem gramsOf_eq_windows (n : Nat) (hn : 0 < n) (cs : List Char) :
    gramsOf n cs = (List.range (cs.length + 1 - n)).map (fun i => (cs.drop i).take n) := by
  unfold gramsOf
  by_cases h : n ≤ cs.length + 1
  · exact gramsGo_eq_map n hn _ cs (by omega)
  · have hzero : cs.length + 1 - n = 0 := by omega
    simp [hzero, gramsGo]

/-- Only literals are indexed; the folded lexical form is what is indexed. -/
def foldedOfTerm : Term → List Char
  | .literal l => foldString l.val.lexicalForm
  | _ => []

/-- The grams of one dictionary term. A non-literal has none. -/
def gramsOfTerm (t : Term) : List (List Char) := gramsOf gramLength (foldedOfTerm t)

/-- The grams a needle looks up. -/
def gramsOfNeedle (needle : String) : List (List Char) :=
  gramsOf gramLength (foldString needle)

/-! ## 2. Folding preserves the substring relation -/

theorem listIsPrefix_map (f : Char → Char) :
    ∀ (a b : List Char), listIsPrefix a b = true →
      listIsPrefix (a.map f) (b.map f) = true := by
  intro a
  induction a with
  | nil => intro b _; simp [listIsPrefix]
  | cons x xs ih =>
      intro b h
      cases b with
      | nil => simp [listIsPrefix] at h
      | cons y ys =>
          simp only [listIsPrefix, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨hxy, hrest⟩ := h
          subst hxy
          simp only [List.map_cons, listIsPrefix, Bool.and_eq_true, beq_iff_eq]
          exact ⟨trivial, ih ys hrest⟩

theorem listContainsSublist_map (f : Char → Char) :
    ∀ (needle hay : List Char), listContainsSublist needle hay = true →
      listContainsSublist (needle.map f) (hay.map f) = true := by
  intro needle hay
  induction hay with
  | nil =>
      intro h
      simp only [listContainsSublist, List.isEmpty_iff] at h
      subst h
      simp [listContainsSublist]
  | cons y ys ih =>
      intro h
      simp only [listContainsSublist, Bool.or_eq_true] at h
      simp only [List.map_cons, listContainsSublist, Bool.or_eq_true]
      cases h with
      | inl hp => exact Or.inl (by simpa using listIsPrefix_map f needle (y :: ys) hp)
      | inr hr => exact Or.inr (ih hr)

/-- Folding both sides preserves the substring relation, so a case-sensitive
`CONTAINS` match implies a match of the folded needle in the folded lexical
form. -/
theorem foldChars_containsSublist (needle hay : List Char)
    (h : listContainsSublist needle hay = true) :
    listContainsSublist (foldChars needle) (foldChars hay) = true :=
  listContainsSublist_map Char.toLower needle hay h

/-! ## 3. A window of a contiguous sublist is a window of the whole -/

theorem listIsPrefix_length :
    ∀ (a b : List Char), listIsPrefix a b = true → a.length ≤ b.length := by
  intro a
  induction a with
  | nil => intro b _; simp
  | cons x xs ih =>
      intro b h
      cases b with
      | nil => simp [listIsPrefix] at h
      | cons y ys =>
          simp only [listIsPrefix, Bool.and_eq_true] at h
          have := ih ys h.2
          simp only [List.length_cons]
          omega

theorem listIsPrefix_eq_take :
    ∀ (a b : List Char), listIsPrefix a b = true → a = b.take a.length := by
  intro a
  induction a with
  | nil => intro b _; simp
  | cons x xs ih =>
      intro b h
      cases b with
      | nil => simp [listIsPrefix] at h
      | cons y ys =>
          simp only [listIsPrefix, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨hxy, hrest⟩ := h
          subst hxy
          have := ih ys hrest
          simp only [List.length_cons, List.take_succ_cons]
          exact congrArg (List.cons x) this

/-- A contiguous sublist sits at some offset, and its whole length fits after
that offset. Both facts are needed: the offset places the windows, the length
bound keeps them inside the range the grams are taken over. -/
theorem exists_offset_of_containsSublist :
    ∀ (needle hay : List Char), listContainsSublist needle hay = true →
      ∃ d, listIsPrefix needle (hay.drop d) = true ∧ d + needle.length ≤ hay.length := by
  intro needle hay
  induction hay with
  | nil =>
      intro h
      simp only [listContainsSublist, List.isEmpty_iff] at h
      subst h
      exact ⟨0, by simp [listIsPrefix]⟩
  | cons y ys ih =>
      intro h
      simp only [listContainsSublist, Bool.or_eq_true] at h
      cases h with
      | inl hp =>
          refine ⟨0, by simpa using hp, ?_⟩
          have := listIsPrefix_length needle (y :: ys) hp
          simp only [List.length_cons] at this ⊢
          omega
      | inr hr =>
          obtain ⟨d, hd, hlen⟩ := ih hr
          refine ⟨d + 1, by simpa using hd, ?_⟩
          simp only [List.length_cons]
          omega

/-- Window `i` of a prefix of `hay.drop d` is window `d + i` of `hay`. -/
theorem window_eq (n : Nat) (needle hay : List Char) (d i : Nat)
    (hp : listIsPrefix needle (hay.drop d) = true)
    (hi : i + n ≤ needle.length) :
    (needle.drop i).take n = (hay.drop (d + i)).take n := by
  have hneedle : needle = (hay.drop d).take needle.length :=
    listIsPrefix_eq_take needle (hay.drop d) hp
  calc (needle.drop i).take n
      = ((((hay.drop d).take needle.length)).drop i).take n := by rw [← hneedle]
    _ = (((hay.drop d).drop i).take (needle.length - i)).take n := by
          rw [List.drop_take]
    _ = ((hay.drop d).drop i).take (min n (needle.length - i)) := by
          rw [List.take_take]
    _ = ((hay.drop d).drop i).take n := by
          have : min n (needle.length - i) = n := by omega
          rw [this]
    _ = (hay.drop (d + i)).take n := by rw [List.drop_drop]

/-- The superset property. Every gram of a contiguous sublist is a gram of
the whole. This is what makes the index a sound candidate filter. -/
theorem gramsSubset_of_containsSublist (n : Nat) (hn : 0 < n)
    (needle hay : List Char) (h : listContainsSublist needle hay = true) :
    ∀ g ∈ gramsOf n needle, g ∈ gramsOf n hay := by
  intro g hg
  obtain ⟨d, hd, hlen⟩ := exists_offset_of_containsSublist needle hay h
  simp only [gramsOf_eq_windows n hn, List.mem_map, List.mem_range] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hin : i + n ≤ needle.length := by omega
  simp only [gramsOf_eq_windows n hn, List.mem_map, List.mem_range]
  exact ⟨d + i, by omega, (window_eq n needle hay d i hd hin).symm⟩

/-! ## 4. The index specification and its candidate list -/

/-- The dictionary positions of a block, paired with the grams of each term.
The position is the PTD1 local ID; the same identity TLI1 uses. -/
def withIds : Nat → List Term → List (Nat × List (List Char))
  | _, [] => []
  | i, t :: rest => (i, gramsOfTerm t) :: withIds (i + 1) rest

/-- The local IDs whose term carries a gram. This is the specification of one
LGI1 posting list. -/
def idsWithGram (dict : Array Term) (gram : List Char) : List Nat :=
  (withIds 0 dict.toList).filterMap
    (fun p => if gram ∈ p.2 then some p.1 else none)

/-- Intersect the posting lists of every gram of the needle. `none` means the
index cannot serve this needle and the caller must scan: the needle folds to
fewer than `gramLength` characters, so it has no gram. -/
def candidatesSpec (dict : Array Term) (needle : String) : Option (List Nat) :=
  match gramsOfNeedle needle with
  | [] => none
  | first :: rest =>
      some (rest.foldl (fun acc g => acc.filter (fun i => i ∈ idsWithGram dict g))
              (idsWithGram dict first))

theorem mem_withIds :
    ∀ (l : List Term) (base i : Nat) (t : Term), l[i]? = some t →
      (base + i, gramsOfTerm t) ∈ withIds base l := by
  intro l
  induction l with
  | nil => intro base i t h; simp at h
  | cons x xs ih =>
      intro base i t h
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp [withIds]
      | succ i =>
          simp only [List.getElem?_cons_succ] at h
          have := ih (base + 1) i t h
          simp only [withIds, List.mem_cons]
          refine Or.inr ?_
          have hb : base + (i + 1) = base + 1 + i := by omega
          rw [hb]
          exact this

theorem mem_idsWithGram (dict : Array Term) (i : Nat) (t : Term) (g : List Char)
    (hget : dict.toList[i]? = some t) (hg : g ∈ gramsOfTerm t) :
    i ∈ idsWithGram dict g := by
  have hmem : (0 + i, gramsOfTerm t) ∈ withIds 0 dict.toList :=
    mem_withIds dict.toList 0 i t hget
  simp only [Nat.zero_add] at hmem
  simp only [idsWithGram, List.mem_filterMap]
  exact ⟨(i, gramsOfTerm t), hmem, by simp [hg]⟩

theorem mem_foldl_filter (i : Nat) (dict : Array Term) :
    ∀ (gs : List (List Char)) (acc : List Nat), i ∈ acc →
      (∀ g ∈ gs, i ∈ idsWithGram dict g) →
      i ∈ gs.foldl (fun acc g => acc.filter (fun j => j ∈ idsWithGram dict g)) acc := by
  intro gs
  induction gs with
  | nil => intro acc hacc _; simpa using hacc
  | cons g gs ih =>
      intro acc hacc hall
      simp only [List.foldl_cons]
      refine ih _ ?_ (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨hacc, hall g (List.mem_cons_self)⟩

/-- **The soundness gate.** A dictionary term whose folded lexical form
contains the folded needle is in the candidate list. The caller then
re-evaluates the original SPARQL expression on the candidates, so its rows are
exactly the rows a full scan returns. -/
theorem mem_candidatesSpec (dict : Array Term) (needle : String) (i : Nat)
    (t : Term) (ids : List Nat)
    (hget : dict.toList[i]? = some t)
    (hmatch : listContainsSublist (foldString needle) (foldedOfTerm t) = true)
    (hc : candidatesSpec dict needle = some ids) :
    i ∈ ids := by
  have hall : ∀ g ∈ gramsOfNeedle needle, i ∈ idsWithGram dict g := by
    intro g hg
    refine mem_idsWithGram dict i t g hget ?_
    exact gramsSubset_of_containsSublist gramLength (by decide) _ _ hmatch g hg
  unfold candidatesSpec at hc
  cases hgn : gramsOfNeedle needle with
  | nil => rw [hgn] at hc; simp at hc
  | cons first rest =>
      rw [hgn] at hc
      simp only [Option.some.injEq] at hc
      subst hc
      refine mem_foldl_filter i dict rest _ ?_ ?_
      · exact hall first (by rw [hgn]; exact List.mem_cons_self)
      · intro g hg
        exact hall g (by rw [hgn]; exact List.mem_cons_of_mem _ hg)

/-! ## 5. `STRSTARTS` and `STRENDS` reduce to `CONTAINS` -/

theorem containsSublist_of_isPrefix (needle hay : List Char)
    (h : listIsPrefix needle hay = true) :
    listContainsSublist needle hay = true := by
  cases hay with
  | nil =>
      cases needle with
      | nil => simp [listContainsSublist]
      | cons _ _ => simp [listIsPrefix] at h
  | cons y ys => simp only [listContainsSublist, Bool.or_eq_true]; exact Or.inl h

/-! ## 6. The runtime index

The specification above is stated over a filter across the whole dictionary.
The artifact stores the same posting lists once, sorted by gram, so a lookup
reads only the runs its needle names. `agreesWithSpec` is the contract between
the two, checked below on samples the way
`TermLocalIndex.agreesWithDictionary` is. -/

structure Posting where
  gram : List Char
  ids : List Nat
  deriving DecidableEq, Repr

structure Index where
  gramLength : Nat
  /-- The block dictionary size. Every posting is a position below it, so this
  is the bound a decoder checks; it is NOT the literal count, because a
  dictionary holds IRIs and blank nodes between its literals. -/
  dictCount : Nat
  /-- How many dictionary terms are literals. Informational. -/
  literalCount : Nat
  postings : Array Posting
  deriving DecidableEq, Repr

/-- The canonical gram order: by codepoint, shorter first on a tie. Every
gram of a given index has the same length, so the length case only arises
between an index and a malformed one. -/
def lessGram : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a.val < b.val then true else if a == b then lessGram as bs else false

private def pairsOf (dict : Array Term) : Std.HashMap (List Char) (Array Nat) := Id.run do
  let mut buckets : Std.HashMap (List Char) (Array Nat) := ∅
  for h : i in [0 : dict.size] do
    for gram in (gramsOfTerm dict[i]).eraseDups do
      buckets := buckets.insert gram ((buckets.getD gram #[]).push i)
  pure buckets

private def literalCountOf (dict : Array Term) : Nat :=
  dict.toList.countP (fun t => match t with | .literal _ => true | _ => false)

/-- Build the index of one block dictionary. Terms are visited in dictionary
order, so every posting list is ascending; only the gram directory is sorted,
and it is much smaller than the posting area. -/
def build (dict : Array Term) : Index :=
  let entries : List Posting :=
    (pairsOf dict).toList.map (fun bucket => { gram := bucket.1, ids := bucket.2.toList })
  { gramLength := gramLength
    dictCount := dict.size
    literalCount := literalCountOf dict
    postings := (entries.mergeSort (fun a b => lessGram a.gram b.gram)).toArray }

private def lowerBoundGo (postings : Array Posting) (gram : List Char)
    (low high : Nat) : Nat → Nat
  | 0 => low
  | fuel + 1 =>
      if low >= high then low
      else
        let middle := low + (high - low) / 2
        match postings[middle]? with
        | none => low
        | some posting =>
            if lessGram posting.gram gram then
              lowerBoundGo postings gram (middle + 1) high fuel
            else lowerBoundGo postings gram low middle fuel

/-- The posting list of one gram, empty when the gram is absent. An absent
gram is what makes a MISS cheap: the intersection is empty at once. -/
def postingsFor (idx : Index) (gram : List Char) : List Nat :=
  let index := lowerBoundGo idx.postings gram 0 idx.postings.size (idx.postings.size + 1)
  match idx.postings[index]? with
  | some posting => if posting.gram == gram then posting.ids else []
  | none => []

/-- Intersect two ascending ID lists in one pass. `fuel` is one more than the
combined length, so the exhausted case is unreachable. -/
private def intersectGo : Nat → List Nat → List Nat → List Nat → List Nat
  | 0, _, _, acc => acc.reverse
  | _ + 1, [], _, acc => acc.reverse
  | _ + 1, _, [], acc => acc.reverse
  | fuel + 1, a :: as, b :: bs, acc =>
      if a == b then intersectGo fuel as bs (a :: acc)
      else if a < b then intersectGo fuel as (b :: bs) acc
      else intersectGo fuel (a :: as) bs acc

def intersectSorted (xs ys : List Nat) : List Nat :=
  intersectGo (xs.length + ys.length + 1) xs ys []

/-- The candidate local IDs for a needle, or `none` when the index cannot
serve it. The rarest gram seeds the intersection, so a needle carrying one
absent or rare gram costs almost nothing. This is the runtime form of
`candidatesSpec`; `agreesWithSpec` is the contract between them. -/
def candidates? (idx : Index) (needle : String) : Option (List Nat) :=
  match gramsOfNeedle needle with
  | [] => none
  | grams =>
      let lists := grams.eraseDups.map (postingsFor idx)
      match lists.mergeSort (fun a b => decide (a.length ≤ b.length)) with
      | [] => some []
      | first :: rest => some (rest.foldl intersectSorted first)

/-- The contract between the stored index and the specification. -/
def agreesWithSpec (dict : Array Term) (needle : String) : Bool :=
  candidates? (build dict) needle == candidatesSpec dict needle

private def lit (s : String) : Term := .literal (Literal.string s)
private def ex : WfIri := ⟨"https://example.test/a", by decide⟩
private def sampleDict : Array Term :=
  #[lit "Water", lit "Underwater vehicle", lit "Glacier lagoon", .iri ex, lit "waterfall"]

#guard gramsOfNeedle "water" == [['w','a','t'],['a','t','e'],['t','e','r']]
#guard gramsOfNeedle "ab" == []
#guard candidatesSpec sampleDict "water" == some [0, 1, 4]
#guard candidatesSpec sampleDict "Water" == some [0, 1, 4]
#guard candidatesSpec sampleDict "bicycle" == some []
#guard candidatesSpec sampleDict "ab" == none
#guard candidatesSpec sampleDict "lagoon" == some [2]
#guard agreesWithSpec sampleDict "water"
#guard agreesWithSpec sampleDict "Water"
#guard agreesWithSpec sampleDict "bicycle"
#guard agreesWithSpec sampleDict "lagoon"
#guard agreesWithSpec sampleDict "ab"
#guard (build sampleDict).literalCount == 4

end L4Factoidal.Storage.LiteralGramIndex
