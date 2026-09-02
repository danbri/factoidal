/-
L4Factoidal.SPARQL.Algebra — solution mappings, triple patterns, BGP
matching, and the core SPARQL 1.1 algebra (§18.5).

Port of the corresponding sections of
`formal/fstar/SPARQL11.Algebra.fst`:
  * Part 1 solution-mapping operations (`sm_*`);
  * Part 2 pattern terms / triple patterns (including SPARQL 1.2
    triple-term patterns, epic #305);
  * §7.2 BGP evaluation (`try_bind_*`, `tp_match`, `eval_bgp`);
  * §7.3/§18.5 algebra operations (`join`, `left_join`, `union`,
    `minus`, filter).

What is deliberately NOT ported here (with why):
  * the `graph_store`/`RDF.Indexed` seam and the `choose_best_tp`
    selectivity planner — engine PERFORMANCE machinery. The
    SPECIFICATION-level evaluator is still here and still the spec:
    `evalTP` scans the graph list, the BGP evaluator takes patterns
    left-to-right, `join` is the nested-loop compatible-merge. The
    keyed hash join and the per-pattern graph bucketing ARE ported
    (2026-08-25, the "Hash-indexed evaluation" section below), each
    proved list-equal to its spec twin in
    `SPARQL/IndexedEvalRefinement.lean`; `GraphPattern.evalIn` runs
    the indexed path through those equalities.
  * the SPARQL expression language (`expr`, `eval_expr`, effective
    boolean value). `Filter`/`LeftJoin` conditions are abstracted as
    `Graph → Binding → Bool` — the shape §18.5 needs from a filter,
    plus the ACTIVE graph, because §18.6's EXISTS inside a condition
    is evaluated against the graph the enclosing GRAPH clause selected.
    The expression AST is a porting stage of its own (`Expr.lean`).

LAYERING (decided when the wider constructor set landed). `Expr.lean`
imports THIS file (an expression can contain a pattern: EXISTS), so
this file cannot import `Expr.lean`. Rather than merge the two, the
algebra stays SPEC-LEVEL and ABSTRACT in exactly the places an
expression would appear:

  | constructor      | abstract argument            | concrete AST lives in |
  |------------------|------------------------------|-----------------------|
  | `filter`         | `Graph → Binding → Bool`     | `Query.lean`          |
  | `leftJoin`       | `Graph → Binding → Bool`     | `Query.lean`          |
  | `bind`           | `Binding → Option Term`      | `Query.lean`          |
  | `lateral`        | `Binding → GraphPattern`     | `Query.lean`          |
  | `service`        | `Option Graph` (resolved)    | `Query.lean`          |
  | `modified`       | `SolutionSeq → SolutionSeq`  | `Query.lean`          |

`QueryPattern` — the concrete AST with one constructor per F*
`group_graph_pattern` case, the one a parser builds — is declared in
`Expr.lean` (in one mutual block with `Expr`, because EXISTS carries a
pattern), and `SPARQL/Query.lean` holds `QueryPattern.lower`, which
compiles it into this algebra under an `EvalEnv`. So the reviewable
§18.5/§18.6 semantics is here, and every expression-shaped detail is
one file up.

Readability contract: every definition cites the SPARQL 1.1 spec
section it implements; names track the spec's vocabulary (solution
mapping, compatibility, merge) rather than implementation jargon.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.SPARQL.PropertyPath
import Std.Data.HashMap

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Solution mappings — SPARQL 1.1 §18.1.8

"A solution mapping μ is a partial function from query variables to
RDF terms." Represented as an association list; earlier entries
shadow later ones (matching the F* representation exactly). -/

abbrev VarName := String

/-! ## The constants a triple pattern pins

Port of `triple_pattern_bound` from `formal/fstar/SPARQL11.Algebra.fst`.
A physical store answers a pattern by its BOUND positions: whichever of
subject, predicate and object the pattern fixes to a constant. Variables
are `none`.

It lives in the algebra, as in the F\* source, so that every store
reader and every planner sees the same record without importing a plan
module. `SPARQL.PlanStreamable`'s `StreamBound` is now an abbreviation
of this record — it had been a second copy of the same three fields,
written when the Lean algebra had no such type. -/
structure PatternBound where
  s : Option Subject := none
  p : Option WfIri := none
  o : Option Term := none
  deriving Repr, DecidableEq, Inhabited

/-- No position bound: the all-variables pattern. -/
def patternBoundAll : PatternBound := {}

/-- Does this triple match the bound? Each bound position compares with
the ENGINE equality of its own kind, so a bound literal object matches
by literal equality (language-tag case, XMLLiteral canonical form) and
not by exact field identity. Port of the per-position test inside
`triple_matches_bound_acc`. -/
def boundMatches (b : PatternBound) (t : Triple) : Bool :=
  (match b.s with | none => true | some s => Subject.eqb s t.s) &&
  (match b.p with | none => true | some p => p == t.p) &&
  (match b.o with | none => true | some o => Term.eqb o t.o)

/-- The bound test respects the engine equality on triples. Needed
wherever a proof crosses between "does the store hold this triple"
(`Graph.mem`, which compares two stored triples) and "does the bound
match it" (which compares a QUERY value against a stored one). -/
theorem boundMatches_congr (b : PatternBound) (a c : Triple) (h : Triple.eqb a c = true) :
    boundMatches b a = boundMatches b c := by
  simp only [Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  have hs' : a.s = c.s := Subject.eqb_eq hs
  unfold boundMatches
  rw [hs', hp]
  cases b.o with
  | none => rfl
  | some o =>
      have : Term.eqb o a.o = Term.eqb o c.o := by
        cases h1 : Term.eqb o a.o with
        | true => simp [Term.eqb_trans h1 ho]
        | false =>
            cases h2 : Term.eqb o c.o with
            | true =>
                exact absurd
                  (Term.eqb_trans h2 (by rw [Term.eqb_symm]; exact ho)) (by rw [h1]; simp)
            | false => rfl
      simp [this]

/-- The triples of `ts` that match `b`, in their original order.

The F\* source writes this as an accumulator plus a final reverse, and
its comment gives the reason: on the extracted OCaml a three-million-row
bucket overflowed the stack when the recursion built its result AFTER
the recursive call. `List.filter` has no such problem, and the two
return the same list in the same order. -/
def tripleMatchesBound (b : PatternBound) (ts : Graph) : Graph :=
  ts.filter (boundMatches b)

theorem mem_tripleMatchesBound (b : PatternBound) (g : Graph) (t : Triple) :
    Graph.mem t (tripleMatchesBound b g) = (Graph.mem t g && boundMatches b t) :=
  RDF.mem_filter_congr (boundMatches_congr b) t g

/-- A solution mapping (also called a binding row). -/
abbrev Binding := List (VarName × Term)

/-- A solution sequence: the result of evaluating a graph pattern. -/
abbrev SolutionSeq := List Binding

def Binding.empty : Binding := []

/-- μ(v) — port of `sm_lookup`. -/
def Binding.lookup (v : VarName) : Binding → Option Term
  | []             => none
  | (w, t) :: rest => if w = v then some t else Binding.lookup v rest

/-- Extend μ with v ↦ t (no shadow check; callers check first) —
port of `sm_bind`. -/
def Binding.bind (v : VarName) (t : Term) (mu : Binding) : Binding :=
  (v, t) :: mu

/-- dom(μ) — port of `sm_domain`. -/
def Binding.domain (mu : Binding) : List VarName :=
  mu.map Prod.fst

/-! ### Freshness context for BNODE() / UUID() / STRUUID()

§17.4.2.9 BNODE() and §17.4.2.12/13 UUID()/STRUUID() return a FRESH
value per solution and per call site. The F* tree threads that
freshness PURELY (no host randomness): the caller — BIND and the
SELECT projection — injects a row index and a call-site tag into the
solution mapping under two reserved keys, and the builtin derives a
deterministic-but-distinct value from them with SHA-256 (port of
`fx_key_row` / `fx_key_occ` / `fx_ctx_put`). The leading control
character keeps the keys disjoint from every parser-produced variable
name (a SPARQL VARNAME cannot contain U+0001), and callers bind the
RESULT into the pristine mapping, so the keys never surface in a
solution sequence. -/

/-- Reserved key carrying the row index (`fx_key_row`). -/
def fxKeyRow : VarName := String.singleton (Char.ofNat 1) ++ "fx_row"

/-- Reserved key carrying the call-site tag (`fx_key_occ`). -/
def fxKeyOcc : VarName := String.singleton (Char.ofNat 1) ++ "fx_occ"

/-- Augment a mapping with the freshness context for ONE expression
evaluation (port of `fx_ctx_put`); used transiently, never stored. -/
def Binding.withFreshnessCtx (row occ : String) (mu : Binding) : Binding :=
  (fxKeyRow, .literal (Literal.string row)) ::
  (fxKeyOcc, .literal (Literal.string occ)) :: mu

/-- Read one freshness key back (port of `fx_ctx_get`); `""` when the
caller injected none. -/
def Binding.freshnessCtx (key : VarName) (mu : Binding) : String :=
  match mu.lookup key with
  | some (.literal l) => l.val.lexicalForm
  | _ => ""

/-- SPARQL 1.1 §18.3: "Two solution mappings μ1 and μ2 are compatible
if, for every variable v in dom(μ1) and in dom(μ2), μ1(v) = μ2(v)."
Term comparison is the engine equality `Term.eqb` (language-tag case,
XMLLiteral c14n) — port of `sm_compatible`. -/
def Binding.compatible : Binding → Binding → Bool
  | [],             _   => true
  | (v, t) :: rest, mu2 =>
      (match mu2.lookup v with
       | none    => true
       | some t2 => t.eqb t2) && Binding.compatible rest mu2

/-- merge(μ1, μ2): μ1's bindings take priority; μ2's non-overlapping
bindings are added — port of `sm_merge`/`sm_merge_aux` (including its
accumulate-by-cons order). Callers guard with `compatible`. -/
def Binding.merge (mu1 : Binding) : Binding → Binding
  | []             => mu1
  | (v, t) :: rest =>
      match mu1.lookup v with
      | some _ => Binding.merge mu1 rest
      | none   => Binding.merge ((v, t) :: mu1) rest

/-! ## Pattern terms and triple patterns — SPARQL 1.1 §18.1.6/§18.2

SPARQL 1.2 (epic #305): `PatternTerm.tripleTerm` is a triple-term
pattern `<<( s p o )>>` whose sub-positions are themselves pattern
terms; `PatternSubject.tripleTerm` is the same shape in subject
position — matchable against no concrete data subject, which is the
RDF 1.2 "triple terms are object-only" rule surfacing at match
time. -/

inductive PatternTerm where
  | var        (v : VarName)
  | iri        (i : WfIri)
  | bnode      (b : BNodeId)
  | literal    (l : WfLiteral)
  | tripleTerm (s p o : PatternTerm)
  deriving Repr, DecidableEq

inductive PatternSubject where
  | var        (v : VarName)
  | iri        (i : WfIri)
  | bnode      (b : BNodeId)
  | tripleTerm (s p o : PatternTerm)
  deriving Repr, DecidableEq

/-- A triple pattern: subject, predicate, object — SPARQL 1.1 allows
a variable in any position (§18.1.6). -/
structure TriplePattern where
  s : PatternSubject
  p : PatternTerm
  o : PatternTerm
  deriving Repr, DecidableEq

/-- A Basic Graph Pattern (§18.1.7): a list of triple patterns. -/
abbrev Bgp := List TriplePattern

/-! ## Matching — §18.3.1, one triple at a time

`tryBindSubject`/`tryBindTerm` attempt to match one pattern position
against one concrete position under a partial solution mapping,
extending the mapping on success. Bindings thread subject →
predicate → object, exactly as in the F* source. -/

/-- Port of `try_bind_subject`. -/
def tryBindSubject (ps : PatternSubject) (s : Subject) (mu : Binding) :
    Option Binding :=
  match ps with
  | .iri i =>
      match s with
      | .iri i' => if i == i' then some mu else none
      | _       => none
  | .bnode b =>
      match s with
      | .bnode b' => if b == b' then some mu else none
      | _         => none
  -- A triple-term subject pattern never matches a concrete data
  -- subject (data subjects are IRI/bnode only).
  | .tripleTerm _ _ _ => none
  | .var v =>
      let term := s.toTerm
      match mu.lookup v with
      | some existing => if existing.eqb term then some mu else none
      | none          => some (mu.bind v term)

/-- Port of `try_bind_term`. RDF 1.2: a triple-term pattern matches a
concrete `Term.tripleTerm` by recursively binding its three
sub-positions. -/
def tryBindTerm : PatternTerm → Term → Binding → Option Binding
  | .iri i, t, mu =>
      match t with
      | .iri i' => if i == i' then some mu else none
      | _       => none
  | .bnode b, t, mu =>
      match t with
      | .bnode b' => if b == b' then some mu else none
      | _         => none
  | .literal l, t, mu =>
      match t with
      | .literal l' => if l.val.eqb l'.val then some mu else none
      | _           => none
  | .tripleTerm ps pp po, t, mu =>
      match t with
      | .tripleTerm s p o =>
          match tryBindTerm ps s.toTerm mu with
          | none     => none
          | some mu1 =>
              match tryBindTerm pp (.iri p) mu1 with
              | none     => none
              | some mu2 => tryBindTerm po o mu2
      | _ => none
  | .var v, t, mu =>
      match mu.lookup v with
      | some existing => if existing.eqb t then some mu else none
      | none          => some (mu.bind v t)

/-- Match one triple pattern against one graph triple under μ,
producing the extended mapping — port of `tp_match`. -/
def tpMatch (tp : TriplePattern) (t : Triple) (mu : Binding) :
    Option Binding :=
  match tryBindSubject tp.s t.s mu with
  | none     => none
  | some mu1 =>
      match tryBindTerm tp.p (.iri t.p) mu1 with
      | none     => none
      | some mu2 => tryBindTerm tp.o t.o mu2

/-! ## BGP evaluation — §18.3 / F* §7.2

Specification-level: one triple pattern extends each current row by
scanning the whole graph (`List.filterMap`); a BGP is the
left-to-right sequential extension. (The F* executable additionally
reorders patterns by index selectivity — `choose_best_tp` — and
probes indexes; that changes cost, not the result set.) -/

/-- All extensions of μ by matching `tp` somewhere in `g`. -/
def evalTP (tp : TriplePattern) (g : Graph) (mu : Binding) : SolutionSeq :=
  g.filterMap (fun t => tpMatch tp t mu)

/-- Sequential BGP evaluation from a seed mapping. -/
def evalBgpFrom (g : Graph) : Bgp → Binding → SolutionSeq
  | [],         mu => [mu]
  | tp :: rest, mu => (evalTP tp g mu).flatMap (evalBgpFrom g rest)

/-- eval(BGP) — §18.3: the empty BGP yields exactly the empty
mapping; otherwise each pattern extends the rows of the previous
ones. -/
def evalBgp (b : Bgp) (g : Graph) : SolutionSeq :=
  evalBgpFrom g b Binding.empty

/-! ## Core algebra operations — §18.5 -/

/-- Join(Ω1, Ω2) = { merge(μ1, μ2) | μ1 ∈ Ω1, μ2 ∈ Ω2, compatible } —
the specification nested-loop form (the F* engine's keyed hash join
computes the same set). -/
def join (omega1 omega2 : SolutionSeq) : SolutionSeq :=
  omega1.flatMap (fun mu1 =>
    omega2.filterMap (fun mu2 =>
      if mu1.compatible mu2 then some (mu1.merge mu2) else none))

/-- Union(Ω1, Ω2): multiset union — port of `union`. -/
def union (omega1 omega2 : SolutionSeq) : SolutionSeq :=
  omega1 ++ omega2

/-- dom(μ1) ∩ dom(μ2) = ∅ — port of `domains_disjoint`. -/
def domainsDisjoint : Binding → Binding → Bool
  | [],             _   => true
  | (v, _) :: rest, mu2 =>
      (mu2.lookup v).isNone && domainsDisjoint rest mu2

/-- Minus(Ω1, Ω2) = { μ1 ∈ Ω1 | ∀ μ2 ∈ Ω2 :
¬compatible(μ1, μ2) ∨ dom(μ1) ∩ dom(μ2) = ∅ } — §18.5, port of
`minus`. -/
def minus (omega1 omega2 : SolutionSeq) : SolutionSeq :=
  omega1.filter (fun mu1 =>
    !omega2.any (fun mu2 =>
      mu1.compatible mu2 && !domainsDisjoint mu1 mu2))

/-- Filter(expr, Ω) with the condition abstracted as a predicate on
rows (see the module banner for why the expression AST is not in this
stage). -/
def filterSeq (cond : Binding → Bool) (omega : SolutionSeq) : SolutionSeq :=
  omega.filter cond

/-- LeftJoin(Ω1, Ω2, expr) — §18.5: for each μ1, the
condition-passing compatible merges if any exist, else μ1 itself
(kept unextended). Equivalent to the spec's
`Filter(expr, Join) ∪ Diff(Ω1, Ω2, expr)` formulation, grouped by
left row. -/
def leftJoin (omega1 omega2 : SolutionSeq) (cond : Binding → Bool) :
    SolutionSeq :=
  omega1.flatMap (fun mu1 =>
    let extended := omega2.filterMap (fun mu2 =>
      if mu1.compatible mu2 then
        let merged := mu1.merge mu2
        if cond merged then some merged else none
      else none)
    if extended.isEmpty then [mu1] else extended)

/-! ## Hash-indexed evaluation — the performance path

The functions above (`join`, `leftJoin`, `evalBgp`) are the
§18.5/§18.3 SPECIFICATION: nested-loop join and left join, per-row
graph scans. The functions in this section are what
`GraphPattern.evalIn` actually runs: a hash join and a hash left join
keyed on the shared always-bound variables, and a BGP step that
buckets the graph once per triple pattern instead of scanning it once
per row. Each is proved EQUAL — as a list, order included — to its
specification twin in `SPARQL/IndexedEvalRefinement.lean`
(`hashJoin_eq_join`, `hashLeftJoin_eq_leftJoin`,
`evalBgpIdx_eq_evalBgp`); that equality is what licenses the wiring.
The plain functions remain the spec, and every theorem about them
transfers across the equality.

Keys are canonicalised with `Term.joinKey` (RDF/Core.lean) because row
compatibility is `Term.eqb`, which is coarser than structural
equality (language-tag case, XMLLiteral c14n);
`Term.joinKey_eq_of_eqb` is the bridge. A bucket probe still runs the
FULL compatibility (or `tpMatch`) test on every candidate, so the key
only ever has to be sound (eqb-compatible rows share a key), never
complete. -/

/-- Group a list into buckets by key. Buckets accumulate REVERSED
(cons is O(1)); `bucketOf` reads them back in original order. -/
def groupByKeyAux {κ α : Type} [BEq κ] [Hashable κ] (key : α → κ) :
    List α → Std.HashMap κ (List α) → Std.HashMap κ (List α)
  | [], m => m
  | a :: rest, m =>
      groupByKeyAux key rest (m.insert (key a) (a :: m.getD (key a) []))

def groupByKey {κ α : Type} [BEq κ] [Hashable κ] (key : α → κ)
    (l : List α) : Std.HashMap κ (List α) :=
  groupByKeyAux key l ∅

/-- The bucket for `k`, in the grouped list's original order
(`bucketOf_groupByKey`: it IS `l.filter (key · == k)`). -/
def bucketOf {κ α : Type} [BEq κ] [Hashable κ]
    (m : Std.HashMap κ (List α)) (k : κ) : List α :=
  (m.getD k []).reverse

/-- The canonicalised key of `mu` over `kvs`; `none` when `mu` leaves
one of them unbound. -/
def Binding.hashKey? : List VarName → Binding → Option (List Term)
  | [], _ => some []
  | v :: vs, mu =>
      match mu.lookup v with
      | none => none
      | some t =>
          match Binding.hashKey? vs mu with
          | none => none
          | some ts => some (t.joinKey :: ts)

/-- The variables a hash join may key on: those of the first left
row's domain that EVERY row of both sides binds. A solution sequence
with heterogeneous domains (an OPTIONAL result) keeps a variable out
of the KEY rather than out of the join — a row missing a key variable
is compatible with rows in every bucket, so such a variable cannot
partition the probe. -/
def joinKeyVars (o1 o2 : SolutionSeq) : List VarName :=
  match o1 with
  | [] => []
  | mu :: _ =>
      mu.domain.filter (fun v =>
        o1.all (fun m => (m.lookup v).isSome) &&
        o2.all (fun m => (m.lookup v).isSome))

/-- The keyed core of the hash join: bucket Ω2 on the key ONCE, probe
with each μ1's key. The per-row `none` fallback (a μ1 missing a key
variable) scans Ω2 as the nested loop would; `joinKeyVars` makes it
unreachable, but the function stays total without that argument. -/
def hashJoinKeyed (kvs : List VarName) (omega1 omega2 : SolutionSeq) :
    SolutionSeq :=
  let idx := groupByKey (Binding.hashKey? kvs) omega2
  omega1.flatMap (fun mu1 =>
    (match Binding.hashKey? kvs mu1 with
     | none => omega2
     | some k => bucketOf idx (some k)).filterMap (fun mu2 =>
      if mu1.compatible mu2 then some (mu1.merge mu2) else none))

/-- Join(Ω1, Ω2) by hash: equal to `join` as a list — same rows, same
order (`hashJoin_eq_join`). With no usable key variable (a cross
product, or heterogeneous domains throughout) it IS the nested-loop
`join`. -/
def hashJoin (omega1 omega2 : SolutionSeq) : SolutionSeq :=
  match joinKeyVars omega1 omega2 with
  | [] => join omega1 omega2
  | v :: vs => hashJoinKeyed (v :: vs) omega1 omega2

/-- The keyed core of the hash left join: bucket Ω2 on the key ONCE,
probe with each μ1's key. The per-μ1 structure is that of `leftJoin` —
the condition-passing compatible merges, or μ1 itself when there are
none — so the two agree row for row and in order. The `none` fallback
(a μ1 missing a key variable) scans Ω2 as the nested loop would. -/
def hashLeftJoinKeyed (kvs : List VarName) (omega1 omega2 : SolutionSeq)
    (cond : Binding → Bool) : SolutionSeq :=
  let idx := groupByKey (Binding.hashKey? kvs) omega2
  omega1.flatMap (fun mu1 =>
    let extended :=
      (match Binding.hashKey? kvs mu1 with
       | none => omega2
       | some k => bucketOf idx (some k)).filterMap (fun mu2 =>
        if mu1.compatible mu2 then
          let merged := mu1.merge mu2
          if cond merged then some merged else none
        else none)
    if extended.isEmpty then [mu1] else extended)

/-- LeftJoin(Ω1, Ω2, expr) by hash: equal to `leftJoin` as a list —
same rows, same order (`hashLeftJoin_eq_leftJoin`). With no usable key
variable it IS the nested-loop `leftJoin`. -/
def hashLeftJoin (omega1 omega2 : SolutionSeq) (cond : Binding → Bool) :
    SolutionSeq :=
  match joinKeyVars omega1 omega2 with
  | [] => leftJoin omega1 omega2 cond
  | v :: vs => hashLeftJoinKeyed (v :: vs) omega1 omega2 cond

/-! ### The indexed BGP step

`evalBgpFrom` scans the whole graph once per row per pattern. The
indexed twin buckets the graph once per PATTERN, keyed on the
positions the current rows pin — a constant in the pattern, or a
variable the rows already bind — and probes per row. -/

/-- The key a subject position pins under μ: a constant in the
pattern, or the value μ binds its variable to. `none` when the
position stays free. (A triple-term subject pattern matches nothing,
so it keys nothing.) -/
def PatternSubject.resolveKey (ps : PatternSubject) (mu : Binding) :
    Option Term :=
  match ps with
  | .iri i            => some (.iri i)
  | .bnode b          => some (.bnode b)
  | .tripleTerm _ _ _ => none
  | .var v            => mu.lookup v

/-- Likewise for a predicate or object position. A triple-term
PATTERN is treated as free (it recursively binds, so it pins no single
key); a constant of the wrong kind for its position (a literal
predicate, say) still yields a key, soundly — it simply names a bucket
no data triple's key equals. -/
def PatternTerm.resolveKey (pt : PatternTerm) (mu : Binding) :
    Option Term :=
  match pt with
  | .iri i            => some (.iri i)
  | .bnode b          => some (.bnode b)
  | .literal l        => some (.literal l)
  | .tripleTerm _ _ _ => none
  | .var v            => mu.lookup v

/-- Which of a pattern's three positions the index keys on. -/
structure TpMask where
  s : Bool
  p : Bool
  o : Bool

/-- A data triple's key at the masked positions (canonicalised). -/
def tripleKey (m : TpMask) (t : Triple) : List Term :=
  (if m.s then [t.s.toTerm.joinKey] else []) ++
  (if m.p then [(Term.iri t.p).joinKey] else []) ++
  (if m.o then [t.o.joinKey] else [])

/-- One masked component of a probe key: `some []` when the position
is not keyed, `some [key]` when it is keyed and μ pins it, `none` when
it is keyed but μ does not pin it (then this row must scan). -/
def maskedKey (on : Bool) (resolved : Option Term) : Option (List Term) :=
  if on then resolved.map (fun c => [c.joinKey]) else some []

/-- The key μ probes the index with; `none` sends the row to the
unindexed scan. -/
def probeKey? (m : TpMask) (tp : TriplePattern) (mu : Binding) :
    Option (List Term) :=
  match maskedKey m.s (tp.s.resolveKey mu) with
  | none => none
  | some ks =>
      match maskedKey m.p (tp.p.resolveKey mu) with
      | none => none
      | some kp =>
          match maskedKey m.o (tp.o.resolveKey mu) with
          | none => none
          | some ko => some (ks ++ kp ++ ko)

/-- `evalTP` against a pre-bucketed graph (`evalTPIdx_eq`: same list
for the index built by `groupByKey (tripleKey m) g`). -/
def evalTPIdx (m : TpMask) (idx : Std.HashMap (List Term) Graph)
    (g : Graph) (tp : TriplePattern) (mu : Binding) : SolutionSeq :=
  match probeKey? m tp mu with
  | none => evalTP tp g mu
  | some k => (bucketOf idx k).filterMap (fun t => tpMatch tp t mu)

/-- One BGP step over a whole row set: bucket the graph ONCE on the
positions the first row pins, then probe per row. Rows from a common
seed all share a domain, so the first row's mask fits every row; a row
it does not fit falls back to the scan inside `evalTPIdx`. -/
def evalBgpStepIdx (tp : TriplePattern) (g : Graph)
    (rows : SolutionSeq) : SolutionSeq :=
  match rows with
  | [] => []
  | mu0 :: _ =>
      let m : TpMask := { s := (tp.s.resolveKey mu0).isSome
                        , p := (tp.p.resolveKey mu0).isSome
                        , o := (tp.o.resolveKey mu0).isSome }
      if m.s || m.p || m.o then
        let idx := groupByKey (tripleKey m) g
        rows.flatMap (evalTPIdx m idx g tp)
      else
        rows.flatMap (evalTP tp g)

def evalBgpRowsIdx (g : Graph) : Bgp → SolutionSeq → SolutionSeq
  | [], rows => rows
  | tp :: rest, rows => evalBgpRowsIdx g rest (evalBgpStepIdx tp g rows)

/-- eval(BGP) by index — `evalBgpIdx_eq_evalBgp`: the same list
`evalBgp` returns. -/
def evalBgpIdx (b : Bgp) (g : Graph) : SolutionSeq :=
  evalBgpRowsIdx g b [Binding.empty]

/-! ## VALUES — SPARQL 1.1 §10.2 / §18.6

`VALUES (?x ?y) { (1 2) (3 UNDEF) }` is inline data: each row becomes
one solution mapping, and an UNDEF cell simply leaves that variable
unbound in that row. -/

/-- Zip a variable list against one VALUES row, skipping UNDEF cells —
port of `zip_bindings`. -/
def zipBindings : List VarName → List (Option Term) → Binding → Binding
  | v :: vs, some t :: ts, mu => zipBindings vs ts (mu.bind v t)
  | _ :: vs, _ :: ts,      mu => zipBindings vs ts mu
  | _,       _,            mu => mu

/-- eval(VALUES) — one solution mapping per data row (§18.6). Port of
`eval_values`. -/
def evalValues (vars : List VarName) (rows : List (List (Option Term))) :
    SolutionSeq :=
  rows.map (fun row => zipBindings vars row Binding.empty)

/-- Bind `v ↦ t` unless `v` already holds a DIFFERENT term — the
compatibility check GRAPH ?g needs before it can add its graph-name
binding to an inner row (§18.6). Port of `sm_bind_if_compatible`. -/
def Binding.bindIfCompatible (v : VarName) (t : Term) (mu : Binding) :
    Option Binding :=
  match mu.lookup v with
  | some existing => if existing.eqb t then some mu else none
  | none          => some (mu.bind v t)

/-! ## Property-path results as solution mappings — §18.4

A path denotes (subject, object) PAIRS; the pattern's own subject and
object positions turn each pair into a solution mapping, or reject
it. -/

/-- Port of `path_result_to_solutions`. A variable in both positions
must receive the SAME term for the pair to survive (`?x path ?x`). -/
def pathResultToSolutions (ps : PatternSubject) (pt : PatternTerm)
    (pairs : PathResult) : SolutionSeq :=
  pairs.filterMap (fun pr =>
    let s := pr.1
    let o := pr.2
    let muS : Option Binding :=
      match ps with
      | .var v            => some [(v, s)]
      | .iri i            => if (Term.iri i).eqb s then some [] else none
      | .bnode b          => if (Term.bnode b).eqb s then some [] else none
      -- A triple term never occupies a path endpoint (RDF 1.2 #305).
      | .tripleTerm _ _ _ => none
    match muS with
    | none => none
    | some bs =>
        match pt with
        | .var v =>
            match bs.lookup v with
            | some existing => if existing.eqb o then some bs else none
            | none          => some ((v, o) :: bs)
        | .iri i            => if (Term.iri i).eqb o then some bs else none
        | .bnode b          => if (Term.bnode b).eqb o then some bs else none
        | .literal l        => if (Term.literal l).eqb o then some bs else none
        | .tripleTerm _ _ _ => none)

/-- The constants a property-path pattern names in its endpoints. The
§18.2.2.5 reflexivity fix for `p*` / `p?` needs them: a query constant
that appears nowhere in the data still matches itself under a
zero-length path. -/
def pathPatternConstants (ps : PatternSubject) (pt : PatternTerm) : List Term :=
  (match ps with
   | .iri i   => [Term.iri i]
   | .bnode b => [Term.bnode b]
   | _        => []) ++
  (match pt with
   | .iri i     => [Term.iri i]
   | .bnode b   => [Term.bnode b]
   | .literal l => [Term.literal l]
   | _          => [])

/-- Add the missing `(c, c)` pairs for the pattern's own constants —
the F* tree's issue-#66 fix, applied only to the two zero-length-
admitting path forms (§18.2.2.5). -/
def addConstantReflexivity (ps : PatternSubject) (pt : PatternTerm)
    (path : PropertyPath) (pairs : PathResult) : PathResult :=
  match path with
  | .zeroOrMore _ | .zeroOrOne _ =>
      let hasReflexive (t : Term) : Bool :=
        pairs.any (fun pr => pr.1.eqb t && pr.2.eqb t)
      let missing := (pathPatternConstants ps pt).filter (fun t => !hasReflexive t)
      pairs ++ missing.map (fun n => (n, n))
  | _ => pairs

/-! ## Graph patterns — the algebra AST (§18.2.2.6 output forms)

One constructor per F* `group_graph_pattern` case, with the
expression-shaped arguments abstracted per the LAYERING table in the
module banner. -/

inductive GraphPattern where
  /-- A Basic Graph Pattern (§18.3). -/
  | bgp      (patterns : Bgp)
  /-- Join(P1, P2) — §18.5. -/
  | join     (l r : GraphPattern)
  /-- LeftJoin(P1, P2, expr) — OPTIONAL, §18.5. The condition is a
  function of the ACTIVE graph as well as the row: §18.6's EXISTS,
  which may appear inside the expression, is evaluated against the
  graph the enclosing GRAPH clause selected (the F* evaluator passes
  `gs.gs_graph` into `left_join_with_graph` for exactly this). -/
  | leftJoin (l r : GraphPattern) (cond : Graph → Binding → Bool)
  /-- Filter(expr, P) — §18.5. Same active-graph argument as
  `leftJoin` (F*: `filter_solutions_with_graph … gs.gs_graph`). -/
  | filter   (cond : Graph → Binding → Bool) (p : GraphPattern)
  /-- Union(P1, P2) — §18.5. -/
  | union    (l r : GraphPattern)
  /-- Minus(P1, P2) — §18.5. -/
  | minus    (l r : GraphPattern)
  /-- `GRAPH <iri> { P }` / `GRAPH ?g { P }` — §18.6. The name is a
  pattern term so both forms share one constructor, as in the F*
  source. -/
  | graph    (name : PatternTerm) (p : GraphPattern)
  /-- `P1 LATERAL { P2 }` — correlated evaluation. The right operand is
  a FUNCTION of the left row: the spec-level statement of "substitute
  the left row's bindings into the right pattern, then evaluate". The
  concrete substitution (`lateralSubstitute`, with the sub-SELECT
  projection-masking rule) lives in `Query.lean`.
  Jena: https://jena.apache.org/documentation/query/lateral-join.html -/
  | lateral  (l : GraphPattern) (r : Binding → GraphPattern)
  /-- `BIND(expr AS ?v)` appended to a pattern — §18.6. The binder is
  abstract: `none` is the spec's "expression error, leave unbound". -/
  | bind     (binder : Binding → Option Term) (v : VarName) (p : GraphPattern)
  /-- `VALUES (?x ?y) { (1 2) (3 UNDEF) }` — inline data, §10.2. -/
  | values   (vars : List VarName) (rows : List (List (Option Term)))
  /-- `SERVICE [SILENT] <iri> { P }` — §18.6 / SPARQL 1.1 Federated
  Query §2. The endpoint is already RESOLVED to the graph it serves
  (`none` = unknown endpoint), because endpoint resolution is a host
  service, not algebra. -/
  | service  (remote : Option Graph) (silent : Bool) (p : GraphPattern)
  /-- `SERVICE [SILENT] ?v { P }` — the endpoint IRI comes from a
  binding, so resolution has to wait until a row supplies one. -/
  | serviceVar (v : VarName) (resolve : Iri → Option Graph) (silent : Bool)
               (p : GraphPattern)
  /-- A sub-pattern whose solution sequence is post-processed — the
  algebra-level shape of a sub-SELECT (§18.2.4): evaluate the inner
  WHERE, then run the inner query's grouping / projection / DISTINCT /
  ORDER / slice pipeline over the result. `Query.lean` supplies that
  pipeline as `post`. -/
  | modified (post : SolutionSeq → SolutionSeq) (p : GraphPattern)
  /-- `?s path ?o` — a property-path pattern, §18.4. -/
  | propertyPath (s : PatternSubject) (path : PropertyPath) (o : PatternTerm)
  /-- The empty group pattern `{}` — the identity for Join (§18.2.2.6:
  it yields exactly the empty solution mapping). -/
  | empty

/-! ## Evaluation over a dataset — SPARQL 1.1 §18.5 / §18.6

`evalIn ds active P` evaluates `P` against the ACTIVE graph, with `ds`
supplying the named graphs GRAPH can switch to. Every arm threads the
same dataset; only `graph` and `service` change the active graph.

TERMINATION: structural on the pattern. The `lateral` arm's recursive
call is `evalIn ds active (r mu1)`, and `r mu1` is covered by the
recursor's induction hypothesis for the function-valued field — so
this is ordinary structural recursion, not fuel and not
well-founded. (The F* source needs a lexicographic
`%[pattern_size; phase]` measure plus
`lemma_lateral_substitute_preserves_size` for the same clique,
because there LATERAL substitutes and then re-enters the evaluator on
a pattern that is not a subterm. Making the right operand a FUNCTION
of the row moves that obligation into the type.) -/

/-- The BIND row loop (port of `fx_bind_rows`): row `i` is evaluated
with its freshness context injected, and the value (if any, and if
`v` is still unbound) is bound into the row WITHOUT the context. -/
def bindRowsFresh (binder : Binding → Option Term) (v : VarName) :
    SolutionSeq → Nat → SolutionSeq
  | [],        _ => []
  | mu :: rest, i =>
      let row := match binder (mu.withFreshnessCtx (toString i) v) with
        | some t => match mu.lookup v with
                    | some _ => mu
                    | none   => mu.bind v t
        | none   => mu
      row :: bindRowsFresh binder v rest (i + 1)

def GraphPattern.evalIn (ds : Dataset) (active : Graph) (p : GraphPattern) :
    SolutionSeq :=
  match p with
  -- Wired to the indexed twin; `evalBgpIdx_eq_evalBgp`
  -- (IndexedEvalRefinement.lean) proves it returns exactly `evalBgp
  -- b active`, so the spec-level reading of this arm is unchanged.
  | .bgp b          => evalBgpIdx b active
  -- SERVICE ?v on the RIGHT of a join: evaluate the left side first,
  -- then dispatch each row to the endpoint that row's binding names.
  -- Port of the F* `GP_Join p1 (GP_ServiceVar ...)` arm.
  | .join p1 (.serviceVar v resolve silent inner) =>
      (GraphPattern.evalIn ds active p1).flatMap (fun mu =>
        match mu.lookup v with
        | some (.iri i) =>
            match resolve i.val with
            | some remote =>
                (GraphPattern.evalIn ds remote inner).filterMap (fun mu1 =>
                  if mu.compatible mu1 then some (mu.merge mu1) else none)
            | none => if silent then [mu] else []
        | _ => if silent then [mu] else [])
  -- Symmetric: SERVICE ?v on the LEFT of a join.
  | .join (.serviceVar v resolve silent inner) p2 =>
      (GraphPattern.evalIn ds active p2).flatMap (fun mu =>
        match mu.lookup v with
        | some (.iri i) =>
            match resolve i.val with
            | some remote =>
                (GraphPattern.evalIn ds remote inner).filterMap (fun mu1 =>
                  if mu.compatible mu1 then some (mu.merge mu1) else none)
            | none => if silent then [mu] else []
        | _ => if silent then [mu] else [])
  -- Wired to the hash join; `hashJoin_eq_join`
  -- (IndexedEvalRefinement.lean) proves it returns exactly the
  -- nested-loop `SPARQL.join` of the two operands, list order
  -- included.
  | .join l r       =>
      SPARQL.hashJoin (GraphPattern.evalIn ds active l) (GraphPattern.evalIn ds active r)
  -- Wired to the hash left join; `hashLeftJoin_eq_leftJoin`
  -- (IndexedEvalRefinement.lean) proves it returns exactly the
  -- nested-loop `SPARQL.leftJoin` of the two operands, list order
  -- included.
  | .leftJoin l r c =>
      SPARQL.hashLeftJoin (GraphPattern.evalIn ds active l) (GraphPattern.evalIn ds active r)
        (c active)
  | .filter c q     => filterSeq (c active) (GraphPattern.evalIn ds active q)
  | .union l r      =>
      SPARQL.union (GraphPattern.evalIn ds active l) (GraphPattern.evalIn ds active r)
  | .minus l r      =>
      SPARQL.minus (GraphPattern.evalIn ds active l) (GraphPattern.evalIn ds active r)
  -- §18.6 GRAPH.
  | .graph name q =>
      match name with
      -- GRAPH <iri>: evaluate against that named graph; an IRI the
      -- dataset does not name contributes nothing.
      | .iri i =>
          match ds.lookupNamedIri i.val with
          | some g => GraphPattern.evalIn ds g q
          | none   => []
      -- GRAPH ?g: evaluate against EVERY named graph, binding ?g to
      -- that graph's name in each row it produces. The name is an IRI
      -- or a blank node (RDF 1.1 Concepts §4), and `?g` binds to
      -- whichever it is.
      | .var v =>
          ds.named.flatMap (fun ng =>
            (GraphPattern.evalIn ds ng.graph q).filterMap (fun mu =>
              mu.bindIfCompatible v ng.name.toTerm))
      -- Any other pattern term in the name position: the F* source
      -- falls back to the active graph.
      | _ => GraphPattern.evalIn ds active q
  -- LATERAL: per left row, evaluate the row-specialised right pattern
  -- and merge back. An empty right side drops the row (inner-join
  -- shaped, unlike OPTIONAL).
  | .lateral l r =>
      (GraphPattern.evalIn ds active l).flatMap (fun mu1 =>
        (GraphPattern.evalIn ds active (r mu1)).filterMap (fun mu2 =>
          if mu1.compatible mu2 then some (mu1.merge mu2) else none))
  -- §18.6 BIND: extend each row, unless the variable is already bound
  -- there or the expression errors. The binder sees the row with its
  -- freshness context (row index + the bound variable as call-site
  -- tag, port of `fx_bind_rows`); the result binds into the PRISTINE
  -- row.
  | .bind binder v q =>
      bindRowsFresh binder v (GraphPattern.evalIn ds active q) 0
  | .values vars rows => evalValues vars rows
  -- SERVICE with a fixed endpoint. On a miss, SILENT yields one empty
  -- solution mapping and non-SILENT yields none — the F* arm exactly.
  | .service remote silent q =>
      match remote with
      | some g => GraphPattern.evalIn ds g q
      | none   => if silent then [Binding.empty] else []
  -- SERVICE ?v outside a join has no row to read the endpoint from.
  | .serviceVar _ _ silent _  => if silent then [Binding.empty] else []
  | .modified post q => post (GraphPattern.evalIn ds active q)
  -- §18.4 property paths, with the §18.2.2.5 constant-reflexivity fix.
  | .propertyPath ps path pt =>
      pathResultToSolutions ps pt
        (addConstantReflexivity ps pt path (evalPath path active))
  | .empty => [Binding.empty]

/-- eval(P, G) — §18.5 evaluation against a single graph, the
default-graph special case of `evalIn` (no named graphs, so GRAPH
contributes nothing). Kept as the entry point every earlier theorem
uses. -/
def GraphPattern.eval (g : Graph) (p : GraphPattern) : SolutionSeq :=
  p.evalIn { default := g, named := [] } g

/-- The two entry points agree by definition, stated so it is checked
rather than assumed. -/
theorem GraphPattern.eval_eq_evalIn (g : Graph) (p : GraphPattern) :
    p.eval g = p.evalIn { default := g, named := [] } g := rfl

end L4Factoidal.SPARQL
