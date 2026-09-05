/-
L4Factoidal.Syntax.TurtleTheorems — proved properties of the RFC 3986
resolver and the Turtle collection encoding.

No `sorry`, no user `axiom`, no `native_decide`, no `partial` (the Lean
side's proof policy — see `skills/factoidal-lean-basics/SKILL.md`). The
audit lines at the bottom show the axiom base is exactly Lean's own
`propext` / `Classical.choice` / `Quot.sound`.

What is proved here, and why these:

  1. RFC 3986 §5.2.2's FIRST case — a reference that carries a scheme
     is resolved without consulting the base at all. This is the
     property the Turtle parser leans on every time it sees an absolute
     `<http://…>`: the answer must not depend on which `@base` happens
     to be in force. Proved in two forms, the general
     base-independence law and the `resolve base abs = abs` identity
     with its two side conditions made EXPLICIT rather than assumed.
  2. RFC 3986 §5.2.4's purpose — `remove_dot_segments` never leaves a
     `.` or `..` segment in its output. Proved by induction on the
     fuel with an invariant on the accumulator.
  3. Turtle §2.8's collection encoding — a concrete list produces a
     well-formed `rdf:first`/`rdf:rest` chain ending at `rdf:nil`.
     Checked by `#guard` on the actual parser output (the shape is a
     property of a specific input, so a computation is the right form).
-/

import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## 1. RFC 3986 §5.2.2, first case — a reference with a scheme

```
if defined(R.scheme) then
   T.scheme    = R.scheme;
   T.authority = R.authority;
   T.path      = remove_dot_segments(R.path);
   T.query     = R.query;
```
The base appears NOWHERE on the right-hand side. Everything in this
section is that observation, made into theorems. -/

/-- The transform's output for a reference that carries a scheme: the
reference's own components, with only its path normalised. Note the
`base` argument is discharged without ever being inspected. -/
theorem transformReferences_of_scheme (base r : IriParts) (s : String)
    (h : r.scheme = some s) :
    transformReferences base r =
      { scheme := r.scheme, authority := r.authority,
        path := removeDotSegments r.path, query := r.query, fragment := r.fragment } := by
  unfold transformReferences
  rw [h]

/-- RFC 3986 §5.2.2 applied to whole strings: resolving a reference
that has a scheme does not consult the base. -/
theorem resolveIri_of_scheme (base ref : String) (s : String)
    (h : (parseIri ref).scheme = some s) :
    resolveIri base ref =
      recompose { scheme := (parseIri ref).scheme, authority := (parseIri ref).authority,
                  path := removeDotSegments (parseIri ref).path,
                  query := (parseIri ref).query, fragment := (parseIri ref).fragment } := by
  unfold resolveIri
  rw [transformReferences_of_scheme _ _ s h]

/-- BASE-INDEPENDENCE: two different bases resolve an absolute
reference to the same IRI. This is the form the Turtle parser needs —
an absolute `<http://…>` in a document means the same thing before and
after any `@base` directive. -/
theorem resolveIri_base_irrelevant (b1 b2 ref : String) (s : String)
    (h : (parseIri ref).scheme = some s) :
    resolveIri b1 ref = resolveIri b2 ref := by
  rw [resolveIri_of_scheme b1 ref s h, resolveIri_of_scheme b2 ref s h]

/-- IDEMPOTENCE on an absolute IRI: `resolve base abs = abs`.

The two side conditions are the honest content of "absolute". A
reference with a scheme resolves to ITSELF exactly when
  * its path is already dot-free (`remove_dot_segments` is the identity
    on it — otherwise resolution legitimately NORMALISES `http://a/b/../c`
    to `http://a/c`, which is the RFC's intent, not a failure), and
  * it survives decomposition and recomposition unchanged (RFC 3986
    §5.3 recomposes to a string equivalent to the original; the two
    coincide for every reference in normal form).
Both are decidable by `rfl` at each use — see the instances below,
which turn this theorem into unconditional equalities for concrete
IRIs. -/
theorem resolveIri_eq_self (base ref : String) (s : String)
    (hscheme : (parseIri ref).scheme = some s)
    (hdots : removeDotSegments (parseIri ref).path = (parseIri ref).path)
    (hround : recompose (parseIri ref) = ref) :
    resolveIri base ref = ref := by
  rw [resolveIri_of_scheme base ref s hscheme, hdots]
  exact hround

/-- The same statement with the side conditions discharged by kernel
computation, for the IRI shapes the W3C fixtures actually use. Each is
a genuine instance of `resolveIri_eq_self`, not a fresh `rfl`. -/
theorem resolveIri_http_self (base : String) :
    resolveIri base "http://example.org/a/b" = "http://example.org/a/b" :=
  resolveIri_eq_self base _ "http" rfl rfl rfl

theorem resolveIri_http_query_fragment_self (base : String) :
    resolveIri base "http://example.org/a?q=1#f" = "http://example.org/a?q=1#f" :=
  resolveIri_eq_self base _ "http" rfl rfl rfl

theorem resolveIri_urn_self (base : String) :
    resolveIri base "urn:example:thing" = "urn:example:thing" :=
  resolveIri_eq_self base _ "urn" rfl rfl rfl

theorem resolveIri_rdfns_self (base : String) :
    resolveIri base "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
      = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" :=
  resolveIri_eq_self base _ "http" rfl rfl rfl

-- The CONTRAST the side conditions buy: an absolute reference whose
-- path is NOT dot-free does not resolve to itself — it normalises,
-- which is RFC 3986 section 5.2.2 working as specified.
#guard resolveIri "http://other/" "http://example.org/a/../b" == "http://example.org/b"

/-! ## 2. RFC 3986 §5.2.4 — no `.` or `..` survives

`remove_dot_segments`'s whole purpose. The proof is an induction on the
fuel carrying the invariant "every segment accumulated so far is
neither `.` nor `..`"; the three ways `dotSegmentStep` changes the
accumulator each preserve it:
  * the `.` branch leaves it alone,
  * the `..` branches keep a tail of it, or the single segment `"/"`,
  * the push branch pushes `segmentText seg hasSlash`, and the two
    guards have just excluded `seg = "."` and `seg = ".."` — while for
    `hasSlash = true` the pushed text ends in `/`, which neither `.`
    nor `..` does.
-/

/-- The property each accumulated segment must have. -/
def isDotSegment (s : String) : Bool := s == "." || s == ".."

/-- Invariant: no accumulated segment is `.` or `..`. -/
def noDotSegments (l : List String) : Bool := l.all (fun s => !isDotSegment s)

@[simp] theorem noDotSegments_nil : noDotSegments [] = true := rfl

theorem noDotSegments_cons (s : String) (l : List String) :
    noDotSegments (s :: l) = (!isDotSegment s && noDotSegments l) := by
  simp [noDotSegments]

@[simp] theorem noDotSegments_reverse (l : List String) :
    noDotSegments l.reverse = noDotSegments l := by
  simp [noDotSegments]

theorem noDotSegments_root : noDotSegments ["/"] = true := by
  simp [noDotSegments, isDotSegment]

/-- The root clamp preserves the invariant: it returns `[]`, the
single segment `"/"`, or a tail of the input list. -/
theorem noDotSegments_popKeepRoot {out : List String} (h : noDotSegments out = true) :
    noDotSegments (popKeepRoot out) = true := by
  match out with
  | []     => simp [popKeepRoot]
  | [x]    =>
      simp only [popKeepRoot]
      split
      · exact noDotSegments_root
      · simp
  | a :: b :: tl =>
      simp only [popKeepRoot]
      rw [noDotSegments_cons] at h
      exact (Bool.and_eq_true _ _ |>.mp h).2

/-- A segment with a trailing `/` is neither `.` nor `..` — it ends in
`/` and they do not. -/
theorem segmentText_slash_ne_dot (seg : String) : ¬ (seg ++ "/" = ".") := by
  intro h
  simp [String.ext_iff] at h
  have := congrArg List.getLast? h
  simp at this

theorem segmentText_slash_ne_dotdot (seg : String) : ¬ (seg ++ "/" = "..") := by
  intro h
  simp [String.ext_iff] at h
  have := congrArg List.getLast? h
  simp at this

/-- The pushed segment is never `.` or `..`. -/
theorem not_isDotSegment_segmentText (seg : String) (hasSlash : Bool)
    (h1 : (seg == ".") = false) (h2 : (seg == "..") = false) :
    isDotSegment (segmentText seg hasSlash) = false := by
  unfold segmentText isDotSegment
  cases hasSlash with
  | false => simp only [Bool.false_eq_true, if_false]; simp [h1, h2]
  | true  =>
      simp only [if_true]
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      exact ⟨segmentText_slash_ne_dot seg, segmentText_slash_ne_dotdot seg⟩

/-- One iteration preserves the invariant. -/
theorem noDotSegments_dotSegmentStep (seg : String) (hasSlash : Bool) (out : List String)
    (h : noDotSegments out = true) :
    noDotSegments (dotSegmentStep seg hasSlash out) = true := by
  unfold dotSegmentStep
  split
  · exact h
  · split
    · split
      · exact noDotSegments_popKeepRoot h
      · split
        · exact noDotSegments_root
        · exact noDotSegments_popKeepRoot h
    · rename_i h1 h2
      rw [noDotSegments_cons, h, Bool.and_true,
          not_isDotSegment_segmentText seg hasSlash (by simpa using h1) (by simpa using h2)]
      rfl

/-- RFC 3986 §5.2.4: the accumulated segment list never contains `.` or
`..`. Induction on the fuel; the invariant travels on the accumulator. -/
theorem removeDotSegmentsStep_noDots :
    ∀ (fuel : Nat) (cs : List Char) (out : List String),
      noDotSegments out = true → noDotSegments (removeDotSegmentsStep fuel cs out) = true
  | 0,        _,       out, h => by simpa [removeDotSegmentsStep] using h
  | _ + 1,    [],      out, h => by simpa [removeDotSegmentsStep] using h
  | fuel + 1, c :: cs, out, h => by
      rw [removeDotSegmentsStep]
      · exact removeDotSegmentsStep_noDots fuel _ _ (noDotSegments_dotSegmentStep _ _ out h)
      · simp

/-- The top-level statement: the segments `removeDotSegments`
concatenates are never `.` or `..`. -/
theorem removeDotSegments_noDots (path : String) :
    noDotSegments (removeDotSegmentsStep (path.length + 2) path.toList []) = true :=
  removeDotSegmentsStep_noDots _ _ [] rfl

-- Worked instances of the same law, on the RFC's own section 5.4 shapes.
#guard removeDotSegments "/a/b/c/./../../g" == "/a/g"
#guard removeDotSegments "/./g" == "/g"
#guard removeDotSegments "/../g" == "/g"
#guard removeDotSegments "a/./b/../c" == "a/c"
#guard removeDotSegments "/a/../../.." == "/"

/-! ## 3. Turtle §2.8 — the collection encoding

`( o1 … on )` becomes a chain of fresh blank nodes, each carrying one
`rdf:first` to its element and one `rdf:rest` to the next node, with the
last `rdf:rest` pointing at `rdf:nil`. The claims below are about the
parser's output on specific inputs, so they are computations. -/

/-- Count the triples of a parse whose predicate is `p`. -/
def predCount (s : String) (p : String) : Nat :=
  match parseTurtle s none with
  | .error _ => 0
  | .ok g    => (g.filter (fun t => t.p.val == p)).length

/-- Does the parse contain a triple whose object is `rdf:nil`? -/
def hasNilTail (s : String) : Bool :=
  match parseTurtle s none with
  | .error _ => false
  | .ok g    => g.any (fun t => t.p.val == rdfRest.val && t.o == Term.iri rdfNil)

def firstIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
def restIri  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

-- A three-element collection: three rdf:first, three rdf:rest, exactly
-- one of which is the rdf:nil terminator.
#guard predCount "<http://a/s> <http://a/p> ( 1 2 3 ) ." firstIri == 3
#guard predCount "<http://a/s> <http://a/p> ( 1 2 3 ) ." restIri == 3
#guard hasNilTail "<http://a/s> <http://a/p> ( 1 2 3 ) ." == true

-- A one-element collection.
#guard predCount "<http://a/s> <http://a/p> ( 1 ) ." firstIri == 1
#guard predCount "<http://a/s> <http://a/p> ( 1 ) ." restIri == 1
#guard hasNilTail "<http://a/s> <http://a/p> ( 1 ) ." == true

-- An EMPTY collection is the IRI rdf:nil itself — no chain at all.
#guard predCount "<http://a/s> <http://a/p> () ." firstIri == 0
#guard predCount "<http://a/s> <http://a/p> () ." restIri == 0

-- Nesting: an outer list of two whose first element is a list of two
-- gives four elements and four tails in total.
#guard predCount "<http://a/s> <http://a/p> ( ( 1 2 ) 3 ) ." firstIri == 4
#guard predCount "<http://a/s> <http://a/p> ( ( 1 2 ) 3 ) ." restIri == 4

/-! ## 4. Small proved facts about the parser itself -/

/-- An empty document is a well-formed Turtle document denoting the
empty graph ([1] `turtleDoc ::= statement*`, zero statements). -/
theorem parseTurtle_empty : parseTurtle "" = .ok [] := rfl

/-- Whitespace and comments alone are still an empty document. -/
theorem parseTurtle_comment_only : parseTurtle "# nothing here\n" = .ok [] := rfl

/-- Feeding characters cannot reduce the largest underscore run observed so
far.  This is stated over the streaming state machine, rather than its legacy
`maxUnderscoreRun` wrapper, so it remains valid when callers split input into
chunks. -/
theorem UnderscoreRun.longest_le_feedChars (cs : List Char) :
    ∀ state : UnderscoreRun, state.longest ≤ (state.feedChars cs).longest := by
  induction cs with
  | nil =>
    intro state
    simp [UnderscoreRun.feedChars]
  | cons c cs ih =>
    intro state
    have hStep : state.longest ≤ (state.feedChar c).longest := by
      unfold UnderscoreRun.feedChar
      split
      · exact Nat.le_max_right _ _
      · exact Nat.le_refl _
    exact Nat.le_trans hStep (ih (state.feedChar c))

/-- `maxUnderscoreRun` never reports less than the best seen so far —
the monotonicity that makes `freshBnodePrefix` pick a run strictly
longer than anything in the document. -/
theorem maxUnderscoreRun_ge_best (cs : List Char) :
    ∀ cur best : Nat, best ≤ maxUnderscoreRun cs cur best := by
  intro cur best
  simpa [maxUnderscoreRun] using
    (UnderscoreRun.longest_le_feedChars cs { current := cur, longest := best })

-- Concrete witnesses that a generated label cannot be written by the
-- document: the prefix carries a longer underscore run than the text.
#guard freshBnodePrefix "" == "anon_"
#guard freshBnodePrefix "_:a _:b" == "anon__"
#guard freshBnodePrefix "_:a__b" == "anon___"
#guard maxUnderscoreRun "_:a__b".toList 0 0 == 2
#guard maxUnderscoreRun (freshBnodePrefix "_:a__b").toList 0 0 == 3

/-! ## The packing accumulator agrees with the graph parser

`parseTurtle` builds its `Graph` by prepending each statement's triples in
reverse onto a reversed accumulator and reversing once at the end
(`parseStatements`). The shard packer folds statements with exactly that
step (`Storage.PackStream.ingestStep`) so that it never materialises a
second whole-document graph. The two theorems below state that this is the
SAME graph, so a packer run through the fold commits the bytes a
`parseTurtle` run would commit. This is the Turtle counterpart of
`NQuadsFold.streamConsume11_eq_batch` instantiated at the accumulator the
batch parser itself uses; it closes the accumulator half of the agreement.
The chunk-boundary half — that `TurtleChunkFold` over any chunking reaches
the same accumulator as `parseTurtleFold` over the concatenation — is NOT
proved here and is not proved anywhere; it rests on
`TurtleStatementScan` never offering a candidate that `readStatement` would
read past, and it is measured rather than proved. -/

theorem parseStatements_eq_fold :
    ∀ (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) (accRev : List Triple),
      parseStatements fuel st pos cs accRev
        = (parseStatementsFold prependReverse fuel st pos cs accRev).map
            (fun r => (r.1.reverse, r.2)) := by
  intro fuel
  induction fuel with
  | zero => intro st pos cs accRev; rfl
  | succ fuel ih =>
      intro st pos cs accRev
      simp only [parseStatements, parseStatementsFold]
      cases hr : (tws pos cs).2 with
      | nil => simp [hr, Except.map]
      | cons c rest =>
          simp only [hr]
          cases hs : readStatement fuel st (tws pos cs).1 (c :: rest) with
          | error e => simp [hs, Except.map]
          | ok v =>
              obtain ⟨ts, st', p2, r2⟩ := v
              simp only [hs, prependReverse]
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp [hp, Except.map]
              · simp only [hp, if_false]
                exact ih st' p2 r2 (ts.reverse ++ accRev)

/-- The document-level form: folding with the packer's step and reversing
once yields precisely `parseTurtle`'s graph. -/
theorem parseTurtle_eq_fold (text : String) (base : Option String) (mode : Mode) :
    parseTurtle text base mode
      = (parseTurtleFold prependReverse [] text base mode).map List.reverse := by
  simp only [parseTurtle, parseTurtleFold]
  rw [parseStatements_eq_fold]
  cases parseStatementsFold prependReverse (text.toList.length + 2)
      (TurtleState.initChars text.toList base mode) 0 text.toList [] <;> rfl

/-! ## Axiom audit -/

#print axioms transformReferences_of_scheme
#print axioms resolveIri_of_scheme
#print axioms resolveIri_base_irrelevant
#print axioms resolveIri_eq_self
#print axioms resolveIri_http_self
#print axioms removeDotSegmentsStep_noDots
#print axioms removeDotSegments_noDots
#print axioms parseTurtle_empty
#print axioms maxUnderscoreRun_ge_best
#print axioms parseStatements_eq_fold
#print axioms parseTurtle_eq_fold

end L4Factoidal.Syntax
