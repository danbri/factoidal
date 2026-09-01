/-
L4Factoidal.SPARQL.Query — SPARQL 1.1 query forms, solution modifiers,
grouping and aggregation, and the §18.2.4 evaluation pipeline.

Port of `formal/fstar/SPARQL11.Algebra.fst` Parts 5, 6, 10, 11 and 12:
`group_graph_pattern` (the full constructor set), `order_condition`,
`solution_modifier`, `select_item`, `select_clause`, `group_condition`,
`query_form`, `dataset_clause`, `query`; `sparql_order` (§15.1),
`group_by` / `eval_aggregate` / `having_filter` (§18.5.1);
`distinct_solutions` / `slice_solutions` / `project_solutions` /
`sort_solutions` (§18.4); and `eval_select_query` / `eval_ask_query` /
`eval_construct_query`.

LAYERING (the choice, recorded here as the module banner asked for).
`SPARQL/Algebra.lean` cannot import `SPARQL/Expr.lean`, because an
expression can contain a graph pattern (EXISTS) and so `Expr.lean`
already imports `Algebra.lean`. Two ways out were available:

  (a) keep the ALGEBRA spec-level and abstract — `Graph → Binding →
      Bool` conditions, `Binding → Option Term` binders, `Binding →
      GraphPattern` correlated operands — and put the concrete,
      `Expr`-carrying AST above it; or
  (b) move `GraphPattern` up into this file entirely.

**(a) was taken.** `Algebra.lean` keeps a reviewable §18.5/§18.6
semantics in which every expression-shaped detail is an opaque
argument. The concrete AST — `QueryPattern`, one constructor per F*
`group_graph_pattern` case, the AST the parser targets, together with
`Query` and the query-level pieces — is declared in `Expr.lean` in one
mutual block with `Expr` (EXISTS carries a pattern, a pattern carries
expressions; see `SPARQL/Exists.lean` for the record of that choice).
THIS file holds `QueryPattern.lower`, which compiles the AST into the
algebra under an `EvalEnv`, and the §18.2.4 pipeline. The split keeps
every theorem in `Invariants.lean` about the algebra alone, with no
expression machinery in scope.

TERMINATION. Nothing here uses fuel, `partial`, or well-founded
recursion:
  * sub-SELECT is STRUCTURAL. `QueryPattern` and `Query` are one
    mutual inductive, so a sub-SELECT's own pattern is a subterm; the
    inner query's post-pattern pipeline (`selectPost`) does not recurse
    into patterns at all, so `lower` handles the whole nest in one
    structural pass. (The F* source needs a lexicographic
    `%[query_size; phase]` measure across a four-member clique for the
    same thing.)
  * LATERAL is structural too. `lateralSubstitute` in the F* source
    returns a pattern that is NOT a subterm of the LATERAL node, which
    is why that tree needs
    `lemma_lateral_substitute_preserves_size`. Here substitution is
    FUSED into lowering (`QueryPattern.lowerWith env mu`), so the
    recursive call goes to a genuine subterm with a different `mu`,
    and composing an outer substitution with a per-row one is just
    `Binding.merge` (outer wins — the same precedence the F* source
    gets by substituting outside-in).
  * property paths bound their closure iterations by the graph's node
    count — see `SPARQL/PropertyPath.lean`.

ASSUMPTION REPORT (the F* `assume val`s the ported arms touch — all
three dissolve, none becomes a Lean `axiom`/`opaque`/`partial`):
  * `service_endpoint_lookup` → `EvalEnv.services`, an explicit
    endpoint → graph map passed into evaluation.
  * `extension_function_call` → `EvalEnv.ext`, already a parameter.
  * `eval_property_path_fwd` → an F* file-ORDERING artifact (the
    concrete `eval_property_path` sits 300 lines below its use site,
    so the F* source forward-declares it). Lean has no such
    constraint; `SPARQL.evalPath` is the definition and is called
    directly.

Readability contract: every definition cites the SPARQL 1.1 spec
section it implements.
-/
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## §15.1 ORDER BY — the SPARQL term ordering

"SPARQL 1.1 Query" §15.1 fixes the order across KINDS of value
(unbound < blank node < IRI < literal) and defers the order WITHIN
some kinds to the implementation, requiring only that it be
consistent. What follows transcribes the F* source's choice, which
matches Apache Jena. -/

/-- Literal order: datatype, then lexical form, then language tag
(port of `literal_order`). -/
def literalOrder (l1 l2 : Literal) : Int :=
  let dc := strCompare l1.datatype.val l2.datatype.val
  if dc ≠ 0 then dc
  else
    let lc := strCompare l1.lexicalForm l2.lexicalForm
    if lc ≠ 0 then lc
    else
      match l1.langTag, l2.langTag with
      | none,    none    => 0
      | none,    some _  => -1
      | some _,  none    => 1
      | some t1, some t2 => strCompare t1 t2

/-- Subject position of a triple term: blank node < IRI (port of
`subject_order`). -/
def subjectOrder : Subject → Subject → Int
  | .bnode x, .bnode y => strCompare x y
  | .iri x,   .iri y   => strCompare x.val y.val
  | .bnode _, .iri _   => -1
  | .iri _,   .bnode _ => 1

/-- The §15.1 kind hierarchy as a rank (port of `term_rank`); RDF 1.2
triple terms sort after everything else. -/
def termRank : Term → Int
  | .bnode _          => 1
  | .iri _            => 2
  | .literal _        => 7
  | .tripleTerm _ _ _ => 8

/-- Total order on RDF terms; triple terms compare by subject, then
predicate, then object (recursing into the object, a strict subterm) —
port of `term_order`. -/
def termOrder : Term → Term → Int
  | t1, t2 =>
    let r1 := termRank t1
    let r2 := termRank t2
    if r1 < r2 then -1
    else if r1 > r2 then 1
    else
      match t1, t2 with
      | .bnode x,   .bnode y   => strCompare x y
      | .iri x,     .iri y     => strCompare x.val y.val
      | .literal a, .literal b => literalOrder a.val b.val
      | .tripleTerm s1 p1 o1, .tripleTerm s2 p2 o2 =>
          let sc := subjectOrder s1 s2
          if sc ≠ 0 then sc
          else
            let pc := strCompare p1.val p2.val
            if pc ≠ 0 then pc else termOrder o1 o2
      | _, _ => 0

/-- §15.1 rank of an evaluated value: unbound/error first, then blank
nodes, IRIs, and the literal kinds (port of `er_rank`). -/
def erRank : EvalResult → Int
  | .error                   => 0
  | .term (.bnode _)         => 1
  | .term (.iri _)           => 2
  | .bool _                  => 3
  | .num _ | .dec _ | .dbl _ => 4
  | .term (.literal _)       => 7
  | .term (.tripleTerm _ _ _) => 8

/-- The raw lexical form of a numeric-ish result, used only as the
last-resort tiebreak below (port of `er_numeric_lexical`). -/
def erNumericLexical : EvalResult → String
  | .num n             => toString n
  | .dec s             => s
  | .dbl s             => s
  | .term (.literal l) => l.val.lexicalForm
  | _                  => ""

/-- Ordering on the numeric fragment. §15.1 leaves the position of
operands with no defined `<` undefined and requires only CONSISTENCY,
so "a value that parses sorts before one that does not; two
unparseable values compare lexically" is conformant — and it is what
the F* source settled on (its own note records that the earlier
"unparseable means tie" rule was NOT transitive). -/
def sparqlOrderNumeric (a b : EvalResult) : Int :=
  match numericCompare a b with
  | some cmp => cmp
  | none =>
      match a.toNumeric?, b.toNumeric? with
      | some _, none => -1
      | none, some _ => 1
      | _, _         => strCompare (erNumericLexical a) (erNumericLexical b)

/-- §15.1 ordering of two evaluated values: `-1`, `0`, `1` (port of
`sparql_order`). -/
def sparqlOrder (a b : EvalResult) : Int :=
  let ra := erRank a
  let rb := erRank b
  if ra < rb then -1
  else if ra > rb then 1
  else
    match a, b with
    | .error, .error => 0
    | .term (.bnode x), .term (.bnode y) => strCompare x y
    | .term (.iri x),   .term (.iri y)   => strCompare x.val y.val
    | .bool x, .bool y => intCompare (if x then 1 else 0) (if y then 1 else 0)
    | .num _, _ | .dec _, _ | .dbl _, _ => sparqlOrderNumeric a b
    | .term (.literal l1), .term (.literal l2) => literalOrder l1.val l2.val
    | .term t1, .term t2 => termOrder t1 t2
    | _, _ => 0

/-- Order-equality of two evaluated values (port of `er_equal`). -/
def erEqual (a b : EvalResult) : Bool := sparqlOrder a b == 0

/-! ## The query AST — SPARQL 1.1 §18.2.4

`SelectItem`, `SelectClause`, `QueryForm`, `OrderCondition`,
`SolutionModifier`, `GroupCondition`, `DatasetClause`, `QueryPattern`
and `Query` are DECLARED in `Expr.lean`, in one mutual block with
`Expr`: §18.6's EXISTS carries a `QueryPattern` inside an expression,
and a pattern carries expressions, so the two ASTs are one inductive
family (the F* `type expr … and group_graph_pattern … and query` group
is the same knot). Everything that USES them — accessors, `mkQuery`,
lowering, evaluation — lives here. -/

def Query.form : Query → QueryForm
  | .mk f _ _ _ _ _ _ _ => f

def Query.dataset : Query → List DatasetClause
  | .mk _ d _ _ _ _ _ _ => d

def Query.pattern : Query → QueryPattern
  | .mk _ _ p _ _ _ _ _ => p

def Query.groupBy : Query → Option (List GroupCondition)
  | .mk _ _ _ g _ _ _ _ => g

def Query.having : Query → List Expr
  | .mk _ _ _ _ h _ _ _ => h

def Query.modifier : Query → SolutionModifier
  | .mk _ _ _ _ _ m _ _ => m

def Query.postValues : Query → Option (List Binding)
  | .mk _ _ _ _ _ _ v _ => v

def Query.base : Query → Option String
  | .mk _ _ _ _ _ _ _ b => b

/-- Expressions whose evaluation depends only on the current solution mapping
    and `EvalEnv`, never on the active RDF graph.  This deliberately small
    subset permits backend-native FILTER evaluation without accidentally
    changing the semantics of EXISTS/NOT EXISTS, extension functions, paths,
    aggregates or graph-sensitive expression forms.  Extend it only alongside
    a corresponding backend refinement argument. -/
def Expr.backendLocal : Expr → Bool
  | .var _ | .iri _ | .lit _ | .boolLit _ | .numericLit _ | .decimalLit _
  | .doubleLit _ | .bound _ => true
  | .arith _ left right | .compare _ left right | .and left right | .or left right
  | .sameTerm left right => Expr.backendLocal left && Expr.backendLocal right
  | .unaryMinus e | .unaryPlus e | .not e => Expr.backendLocal e
  | _ => false

/-- Build a query, defaulting every optional part — the shape most
call sites (and every test below) want. -/
def mkQuery (form : QueryForm) (pattern : QueryPattern)
    (dataset : List DatasetClause := [])
    (groupBy : Option (List GroupCondition) := none)
    (having : List Expr := [])
    (modifier : SolutionModifier := {})
    (postValues : Option (List Binding) := none)
    (base : Option String := none) : Query :=
  .mk form dataset pattern groupBy having modifier postValues base

/-! ## §18.4 solution modifiers -/

/-- §18.3: a solution mapping is a partial FUNCTION, so binding ORDER
carries no meaning. `subsumes` checks that every variable this row
binds is bound to an `eqb`-equal term by the other (port of the
issue-#336 rewrite of `sm_equal`, which fixed DISTINCT collapsing the
two arms of a UNION only when they happened to build their bindings in
the same order). -/
def Binding.subsumes (mu1 mu2 : Binding) : Bool :=
  mu1.all (fun b =>
    match mu1.lookup b.1, mu2.lookup b.1 with
    | some t1, some t2 => t1.eqb t2
    | _,       _       => false)

/-- Observational equality of two solution mappings. -/
def Binding.equiv (mu1 mu2 : Binding) : Bool :=
  mu1.subsumes mu2 && mu2.subsumes mu1

/-- `Distinct(Ω)` — §18.4. Following the F* `list_deduplicate_sm`, a
row survives when no LATER row is equivalent to it, so the surviving
rows keep their relative order and each equivalence class contributes
its last occurrence. -/
def distinctSolutions : SolutionSeq → SolutionSeq
  | []       => []
  | mu :: rest =>
      if rest.any (fun x => mu.equiv x) then distinctSolutions rest
      else mu :: distinctSolutions rest

/-- All variable names seen in a solution sequence, once each.  The discovery
    order is immaterial but fixed for the whole DISTINCT invocation.  Computing
    it once avoids sorting and rebuilding a variable universe for every row. -/
def distinctVariables (omega : SolutionSeq) : List VarName :=
  omega.foldl (fun seen mu =>
    mu.foldl (fun seen pair =>
      if seen.contains pair.1 then seen else pair.1 :: seen) seen) []

/-- Canonical candidate key used by runtime DISTINCT for one fixed variable
    universe.  `none` records an unbound variable; present terms use `joinKey`,
    which is constant on RDF/SPARQL term-equivalence classes.  Association-list
    order and duplicate variable entries therefore do not affect the key.

    Callers must still check full `Binding.equiv` inside a bucket: the key is a
    sound candidate partition, not the definition of solution-map equality. -/
def Binding.distinctKeyFor (mu : Binding) (vars : List VarName) : List (Option Term) :=
  vars.map fun v => (mu.lookup v).map Term.joinKey

/-- Tail-recursive worker for `distinctSolutionsFast`.  It is deliberately
    named rather than local so `DistinctFastRefinement` can state the bucket
    invariant over exactly the compiled runtime loop.  `vars` is fixed for the
    invocation.  The full `equiv` test means a hash collision or coarser key
    cannot remove a non-duplicate. -/
def distinctSolutionsFastGo (vars : List VarName) : SolutionSeq →
    Std.HashMap (List (Option Term)) SolutionSeq → SolutionSeq → SolutionSeq
  | [], _, kept => kept
  | mu :: rest, buckets, kept =>
      let key := mu.distinctKeyFor vars
      let bucket := buckets.getD key []
      if bucket.any (fun prior => mu.equiv prior) then
        distinctSolutionsFastGo vars rest buckets kept
      else
        distinctSolutionsFastGo vars rest (buckets.insert key (mu :: bucket)) (mu :: kept)

def distinctSolutionsFast (omega : SolutionSeq) : SolutionSeq :=
  let vars := distinctVariables omega
  distinctSolutionsFastGo vars omega.reverse
    (∅ : Std.HashMap (List (Option Term)) SolutionSeq) []

/-- `Reduced(Ω)` — §18.4 permits an implementation to remove some, all,
or none of the duplicates. Keeping all of them is conformant, and is
what the F* source specifies. -/
def reducedSolutions (omega : SolutionSeq) : SolutionSeq := omega

/-- `Slice(Ω, offset, limit)` — §18.4 OFFSET / LIMIT. -/
def sliceSolutions (offset limit : Option Nat) (omega : SolutionSeq) :
    SolutionSeq :=
  let afterOffset := match offset with
    | none   => omega
    | some n => omega.drop n
  match limit with
  | none   => afterOffset
  | some n => afterOffset.take n

/-- `Project(μ, vars)` — §18.4: restrict one row to the projected
variables. -/
def projectBinding (vars : List VarName) : Binding → Binding
  | []            => []
  | (v, t) :: rest =>
      if vars.contains v then (v, t) :: projectBinding vars rest
      else projectBinding vars rest

/-- `Project(Ω, vars)` — §18.4. -/
def projectSolutions (vars : List VarName) (omega : SolutionSeq) : SolutionSeq :=
  omega.map (projectBinding vars)

/-! ### ORDER BY as a stable insertion sort

`List.sortWith` would do, but writing the sort here keeps the
permutation property provable in a few lines (`sortSolutions_perm` in
`QueryTheorems.lean`) with no dependency on a library sort's
specification. Insertion is STABLE: a row inserts ahead of the first
row it does not compare strictly after, and rows arrive in input
order, so equal rows keep their input order (§15.1 says nothing about
ties, and stability is the least surprising choice). -/

/-- Insert one row into an already ordered sequence. -/
def insertOrdered (cmp : Binding → Binding → Int) (mu : Binding) :
    SolutionSeq → SolutionSeq
  | []       => [mu]
  | x :: rest =>
      if cmp mu x ≤ 0 then mu :: x :: rest
      else x :: insertOrdered cmp mu rest

/-- `OrderBy(Ω, conds)` — §18.4, by stable insertion. -/
def sortSolutions (cmp : Binding → Binding → Int) : SolutionSeq → SolutionSeq
  | []       => []
  | mu :: rest => insertOrdered cmp mu (sortSolutions cmp rest)

/-- Runtime ORDER BY uses Lean's merge sort rather than the small insertion
    sort retained above for its existing proof exercises. The comparator keeps
    the same non-strict ordering convention: an equal pair may remain in its
    input order, while SPARQL does not prescribe an order for ties. -/
def sortSolutionsFast (cmp : Binding → Binding → Int) (omega : SolutionSeq) : SolutionSeq :=
  omega.mergeSort (fun left right => cmp left right ≤ 0)

/-- Compare two rows on one ORDER BY condition; DESC swaps the
operands (port of `compare_on_condition`). -/
def compareOnCondition (env : EvalEnv) (c : OrderCondition)
    (mu1 mu2 : Binding) : Int :=
  match c with
  | .asc e  => sparqlOrder (Expr.evalIn env mu1 e) (Expr.evalIn env mu2 e)
  | .desc e => sparqlOrder (Expr.evalIn env mu2 e) (Expr.evalIn env mu1 e)

/-- Lexicographic comparison over the ORDER BY list: the first
non-equal condition decides (port of `compare_on_conditions`). -/
def compareOnConditions (env : EvalEnv) : List OrderCondition →
    Binding → Binding → Int
  | [],      _,   _   => 0
  | c :: rest, mu1, mu2 =>
      let r := compareOnCondition env c mu1 mu2
      if r ≠ 0 then r else compareOnConditions env rest mu1 mu2

/-! ## §18.5.1 grouping and aggregation -/

/-- One GROUP BY group: the key its rows share, and those rows. -/
structure SolutionGroup where
  key       : List EvalResult
  solutions : SolutionSeq

/-- Evaluate one group condition against a row to get its key
component (port of `eval_group_condition`). -/
def evalGroupCondition (env : EvalEnv) (gc : GroupCondition) (mu : Binding) :
    EvalResult :=
  match gc with
  | .var v =>
      match mu.lookup v with
      | some t => .term t
      | none   => .error
  | .expr e _ => Expr.evalIn env mu e

/-- The full group key of a row. -/
def evalGroupKey (env : EvalEnv) (conds : List GroupCondition) (mu : Binding) :
    List EvalResult :=
  conds.map (fun gc => evalGroupCondition env gc mu)

/-- Two group keys are equal when they agree component-wise under the
§15.1 ordering (port of `keys_equal`). -/
def keysEqual : List EvalResult → List EvalResult → Bool
  | [],       []       => true
  | a :: r1,  b :: r2  => erEqual a b && keysEqual r1 r2
  | _,        _        => false

/-- Add a row to its group, creating the group if this key is new.
Group order is first-appearance order, and rows keep their input order
within a group (port of `add_to_groups`; the F* version's cons-then-
reverse is a stack-safety rewrite of exactly this). -/
def addToGroups (key : List EvalResult) (mu : Binding)
    (groups : List SolutionGroup) : List SolutionGroup :=
  if groups.any (fun g => keysEqual key g.key) then
    groups.map (fun g =>
      if keysEqual key g.key then { g with solutions := g.solutions ++ [mu] } else g)
  else groups ++ [{ key := key, solutions := [mu] }]

/-- `GROUP BY (expr AS ?v)` also BINDS `?v` in every row of the group
(port of `extend_with_group_aliases`). -/
def extendWithGroupAliases (env : EvalEnv) (conds : List GroupCondition)
    (mu : Binding) : Binding :=
  conds.foldl (fun acc gc =>
    match gc with
    | .expr e (some v) =>
        match (Expr.evalIn env acc e).toTerm? with
        | some t => acc.bind v t
        | none   => acc
    | _ => acc) mu

/-- `Group(exprlist, Ω)` — §18.5.1 (port of `group_by`). -/
def groupSolutions (env : EvalEnv) (conds : List GroupCondition)
    (omega : SolutionSeq) : List SolutionGroup :=
  omega.foldl (fun groups mu =>
    addToGroups (evalGroupKey env conds mu)
      (extendWithGroupAliases env conds mu) groups) []

/-- With no GROUP BY, the whole sequence is one group (§18.5.1: an
aggregate with no GROUP BY groups over everything). Port of
`implicit_group`. -/
def implicitGroup (omega : SolutionSeq) : List SolutionGroup :=
  [{ key := [], solutions := omega }]

/-! ### Aggregate functions — §18.5.1.x -/

/-- The expression's value at every row of a group. -/
def evalOverGroup (env : EvalEnv) (e : Expr) (g : SolutionGroup) :
    List EvalResult :=
  g.solutions.map (fun mu => Expr.evalIn env mu e)

/-- Drop type errors (an aggregate ignores rows whose expression
errors, §18.5.1.1). -/
def filterNonError (vals : List EvalResult) : List EvalResult :=
  vals.filter (fun v => v != .error)

/-- Deduplicate values under the §15.1 ordering, keeping the first
occurrence — what `COUNT(DISTINCT ?x)` and friends need (port of
`dedup_er`). -/
def dedupErAcc : List EvalResult → List EvalResult → List EvalResult
  | [],       acc => acc.reverse
  | v :: rest, acc =>
      if acc.any (fun x => erEqual v x) then dedupErAcc rest acc
      else dedupErAcc rest (v :: acc)

def dedupEr (vals : List EvalResult) : List EvalResult := dedupErAcc vals []

/-- Running sum over the numeric values, carrying the promoted type
and the count of numeric operands (port of `sum_numeric_acc`). -/
def sumNumericAcc : List EvalResult → Scaled → NumKind → Nat →
    (Scaled × NumKind × Nat)
  | [],       acc, k, c => (acc, k, c)
  | v :: rest, acc, k, c =>
      match v.toNumeric? with
      | some (s, vk) => sumNumericAcc rest (acc.add s) (promoteKind k vk) (c + 1)
      | none         => sumNumericAcc rest acc k c

/-- §18.5.1.4 SUM. The sum of no values is `0` (the spec's stated
identity). -/
def sumNumeric (vals : List EvalResult) : EvalResult :=
  let (s, k, c) := sumNumericAcc vals ⟨0, 0⟩ .int 0
  if c == 0 then .num 0 else formatNumericResult s k

/-- §18.5.1.5 AVG. The result is never an integer: an average of
integers is an `xsd:decimal`. Division carries ten extra fraction
digits, as in the F* source. -/
def avgNumeric (vals : List EvalResult) : EvalResult :=
  let (s, k, c) := sumNumericAcc vals ⟨0, 0⟩ .int 0
  if c == 0 then .num 0
  else
    let resultKind := match k with | .int => NumKind.dec | other => other
    let extra : Nat := 10
    let extended := s.mantissa * pow10 extra
    let divided := intDivT extended (Int.ofNat c)
    let resultScale := s.scale + extra
    match resultKind with
    | .dbl => .dbl (formatAsDouble divided resultScale)
    | _    => .dec (stripTrailingDecimalZeros (formatScaledValue divided resultScale))

/-- §18.5.1.6 MIN by the §15.1 ordering; MIN of nothing is an error. -/
def findMin (vals : List EvalResult) : EvalResult :=
  match vals with
  | []      => .error
  | v :: rest => rest.foldl (fun acc x => if sparqlOrder x acc ≤ 0 then x else acc) v

/-- §18.5.1.7 MAX by the §15.1 ordering. -/
def findMax (vals : List EvalResult) : EvalResult :=
  match vals with
  | []      => .error
  | v :: rest => rest.foldl (fun acc x => if sparqlOrder x acc ≥ 0 then x else acc) v

/-- The first non-error value — §18.5.1.9 SAMPLE (any one value of the
group; the spec explicitly allows an arbitrary choice). -/
def firstNonError : List EvalResult → EvalResult
  | []       => .error
  | v :: rest => if v == .error then firstNonError rest else v

/-- Evaluate an aggregate over one group — §18.5.1 (port of
`eval_aggregate`).

`COUNT(*)` is written as `Expr.var "*"` or `Expr.boolLit true`, the
same two spellings the F* source accepts. `COUNT(DISTINCT *)` counts
DISTINCT ROWS: the F* source builds a string key per row, this port
uses `distinctSolutions`, which is the §18.3 row equality — the same
count whenever the two agree, and the row equality is the one DISTINCT
itself uses. -/
def evalAggregate (env : EvalEnv) (fn : AggregateFn) (distinct : Bool)
    (e : Expr) (g : SolutionGroup) : EvalResult :=
  match fn with
  | .count =>
      match e with
      | .var "*" | .boolLit true =>
          if distinct then .num (Int.ofNat (distinctSolutions g.solutions).length)
          else .num (Int.ofNat g.solutions.length)
      | _ =>
          let vals := filterNonError (evalOverGroup env e g)
          let vals := if distinct then dedupEr vals else vals
          .num (Int.ofNat vals.length)
  | .sum =>
      let vals := filterNonError (evalOverGroup env e g)
      let vals := if distinct then dedupEr vals else vals
      -- §18.5.1.4: a non-numeric operand makes the whole sum an error.
      if vals.any (fun v => v.toNumeric?.isNone) then .error else sumNumeric vals
  | .avg =>
      let vals := filterNonError (evalOverGroup env e g)
      let vals := if distinct then dedupEr vals else vals
      if vals.any (fun v => v.toNumeric?.isNone) then .error else avgNumeric vals
  | .min =>
      let vals := filterNonError (evalOverGroup env e g)
      findMin (if distinct then dedupEr vals else vals)
  | .max =>
      let vals := filterNonError (evalOverGroup env e g)
      findMax (if distinct then dedupEr vals else vals)
  | .groupConcat sep =>
      let vals := filterNonError (evalOverGroup env e g)
      let vals := if distinct then dedupEr vals else vals
      -- §18.5.1.8: the default separator is a single space.
      let s := sep.getD " "
      erString (String.intercalate s (vals.filterMap EvalResult.toString?))
  | .sample => firstNonError (evalOverGroup env e g)

/-- Replace every aggregate sub-expression by its computed value, so
an ordinary §17 evaluation can finish the job — this is what lets
`HAVING (COUNT(?o) > 2)` and `SELECT (COUNT(?o) * 2 AS ?c)` work
(port of `rewrite_aggregates`). -/
def rewriteAggregates (env : EvalEnv) (g : SolutionGroup) : Expr → Expr
  | .aggregate fn distinct sub =>
      match evalAggregate env fn distinct sub g with
      | .num n     => .numericLit n
      | .bool b    => .boolLit b
      | .dec s     => .decimalLit s
      | .dbl d     => .doubleLit d
      | .term (.iri i)     => .iri i
      | .term (.literal l) => .lit l
      | .term _    => .boolLit false
      -- An unbound variable is exactly the §17 type error the F*
      -- source encodes here with the same sentinel name.
      | .error     => .var "_:error:"
  | .compare op e1 e2 =>
      .compare op (rewriteAggregates env g e1) (rewriteAggregates env g e2)
  | .and e1 e2 => .and (rewriteAggregates env g e1) (rewriteAggregates env g e2)
  | .or e1 e2  => .or (rewriteAggregates env g e1) (rewriteAggregates env g e2)
  | .arith op e1 e2 =>
      .arith op (rewriteAggregates env g e1) (rewriteAggregates env g e2)
  | .not e1    => .not (rewriteAggregates env g e1)
  | e          => e

/-- Evaluate an expression in GROUP context: aggregates first, then
the §17 evaluator against the group's representative row (port of
`eval_expr_in_group`). -/
def evalExprInGroup (env : EvalEnv) (e : Expr) (g : SolutionGroup) : EvalResult :=
  let rewritten := rewriteAggregates env g e
  match g.solutions with
  | mu :: _ => Expr.evalIn env mu rewritten
  | []      => Expr.evalIn env Binding.empty rewritten

/-- §18.5.1 HAVING: keep the groups whose every condition has an
effective boolean value of true (port of `having_filter`). -/
def havingFilter (env : EvalEnv) (conds : List Expr)
    (groups : List SolutionGroup) : List SolutionGroup :=
  groups.filter (fun g =>
    conds.all (fun c => ebvOrFalse (evalExprInGroup env c g)))

/-- One SELECT item's value for one group (port of
`eval_select_item_group`). -/
def evalSelectItemGroup (env : EvalEnv) (item : SelectItem) (g : SolutionGroup) :
    Option (VarName × Term) :=
  match item with
  | .var v =>
      match g.solutions with
      | mu :: _ => (mu.lookup v).map (fun t => (v, t))
      | []      => none
  | .expr e v => ((evalExprInGroup env e g).toTerm?).map (fun t => (v, t))

/-- One row per group (port of `aggregate_groups`). -/
def aggregateGroups (env : EvalEnv) (items : List SelectItem)
    (groups : List SolutionGroup) : SolutionSeq :=
  groups.map (fun g => items.filterMap (fun it => evalSelectItemGroup env it g))

/-- Does this expression contain an aggregate anywhere? An aggregate
in the SELECT clause triggers grouping even with no GROUP BY
(§18.2.4.1). Port of `expr_has_aggregate`. -/
def exprHasAggregate : Expr → Bool
  | .aggregate _ _ _ => true
  | .arith _ e1 e2   => exprHasAggregate e1 || exprHasAggregate e2
  | .compare _ e1 e2 => exprHasAggregate e1 || exprHasAggregate e2
  | .and e1 e2       => exprHasAggregate e1 || exprHasAggregate e2
  | .or e1 e2        => exprHasAggregate e1 || exprHasAggregate e2
  | .not e1          => exprHasAggregate e1
  | .unaryMinus e1   => exprHasAggregate e1
  | .unaryPlus e1    => exprHasAggregate e1
  | .cond c t f      => exprHasAggregate c || exprHasAggregate t || exprHasAggregate f
  | _                => false

/-- Does the SELECT clause use aggregation? (`SELECT *` never can.) -/
def selectHasAggregates : SelectClause → Bool
  | .all       => false
  | .vars items => items.any (fun it =>
      match it with
      | .var _    => false
      | .expr e _ => exprHasAggregate e)

/-- The variables a SELECT clause projects. -/
def selectItemVars : List SelectItem → List VarName
  | []             => []
  | .var v :: rest  => v :: selectItemVars rest
  | .expr _ v :: rest => v :: selectItemVars rest

/-- Evaluate the `(expr AS ?v)` items of a non-aggregating SELECT over
one row; each item sees the bindings the earlier items added (port of
`eval_select_items_row`). `row` is the row's index and `i` the item's
position: together they are the freshness context BNODE()/UUID()/
STRUUID() derive a distinct value from (`Binding.withFreshnessCtx`,
the F* `eval_select_item` design); the context is seen by the
expression only and never stored in the returned row. -/
def evalSelectItemsRow (env : EvalEnv) (row : String) (items : List SelectItem) (mu : Binding) :
    Binding :=
  (items.foldl (fun (st : Binding × Nat) it =>
    let (acc, i) := st
    match it with
    | .var _    => (acc, i + 1)
    | .expr e v =>
        match (Expr.evalIn env (acc.withFreshnessCtx row (toString i)) e).toTerm? with
        | some t => (acc.bind v t, i + 1)
        -- §18.2.4.2: an expression error leaves the variable unbound.
        | none   => (acc, i + 1)) (mu, 0)).1

/-- Every row, numbered from 0 (port of `eval_select_items`'s row
counter). -/
def evalSelectItemsFrom (env : EvalEnv) (items : List SelectItem) :
    SolutionSeq → Nat → SolutionSeq
  | [],        _ => []
  | mu :: rest, i => evalSelectItemsRow env (toString i) items mu :: evalSelectItemsFrom env items rest (i + 1)

def evalSelectItems (env : EvalEnv) (items : List SelectItem)
    (omega : SolutionSeq) : SolutionSeq :=
  evalSelectItemsFrom env items omega 0

/-- `is_synthetic_bnode_var`: the variables `QueryPattern.rewriteBnodes`
(below) invents for WHERE-clause blank nodes. -/
def isSyntheticBnodeVar (v : VarName) : Bool := "_bnode_".isPrefixOf v

/-- `strip_synthetic_bnode_vars`: drop the rewrite-invented variables
from every row — what `SELECT *` must do, since §18.2.4 keeps
WHERE-clause blank nodes out of the user's variable scope. Applied
BEFORE DISTINCT/REDUCED, as in the F* source, so rows that differ
only in a synthetic binding collapse to one. -/
def stripSyntheticBnodeVars (omega : SolutionSeq) : SolutionSeq :=
  omega.map (fun mu => mu.filter (fun b => !isSyntheticBnodeVar b.1))

/-! ## The §18.2.4 pipeline

`selectPost` is everything a SELECT query does AFTER its WHERE clause
has produced a solution sequence: post-VALUES join, grouping,
aggregation, HAVING, SELECT expressions, ORDER BY, projection,
DISTINCT/REDUCED, and OFFSET/LIMIT — in that order, matching
`eval_select_query`. Keeping it separate from pattern evaluation is
what makes sub-SELECT structural (see the module banner). -/

def selectPost (env : EvalEnv) (q : Query) (omega0 : SolutionSeq) : SolutionSeq :=
  -- 1b. Post-query VALUES joins onto the WHERE result (§10.2).
  let omega := match q.postValues with
    | none      => omega0
    | some vals => join omega0 vals
  match q.form with
  | .select sel =>
      let needsGrouping := q.groupBy.isSome || selectHasAggregates sel
      if needsGrouping then
        -- 2. GROUP BY (§18.5.1).
        let groups := match q.groupBy with
          | some conds => groupSolutions env conds omega
          | none       => implicitGroup omega
        -- 3. HAVING.
        let filtered := if q.having.isEmpty then groups
                        else havingFilter env q.having groups
        -- 4. Aggregation: one row per surviving group.
        let omega' := match sel with
          | .vars items => aggregateGroups env items filtered
          | .all        =>
              stripSyntheticBnodeVars (filtered.map (fun g => g.solutions.headD Binding.empty))
        -- 6. ORDER BY.
        let ordered := match q.modifier.orderBy with
          | none   => omega'
          | some o => sortSolutionsFast (compareOnConditions env o) omega'
        -- 8. DISTINCT / REDUCED.
        let deduped :=
          if q.modifier.distinct then distinctSolutionsFast ordered
          else if q.modifier.reduced then reducedSolutions ordered
          else ordered
        -- 9. OFFSET / LIMIT.
        sliceSolutions q.modifier.offset q.modifier.limit deduped
      else
        -- 5. SELECT expressions.
        let omega' := match sel with
          | .vars items => evalSelectItems env items omega
          | .all        => omega
        -- 6. ORDER BY (before projection, so ORDER BY can name a
        -- variable the projection drops — §15.1).
        let ordered := match q.modifier.orderBy with
          | none   => omega'
          | some o => sortSolutionsFast (compareOnConditions env o) omega'
        -- 7. Projection. `SELECT *` drops the rewrite-invented
        -- `_bnode_*` variables here, before DISTINCT (F* site).
        let projected := match sel with
          | .vars items => projectSolutions (selectItemVars items) ordered
          | .all        => stripSyntheticBnodeVars ordered
        let deduped :=
          if q.modifier.distinct then distinctSolutionsFast projected
          else if q.modifier.reduced then reducedSolutions projected
          else projected
        sliceSolutions q.modifier.offset q.modifier.limit deduped
  -- ASK / CONSTRUCT / DESCRIBE have their own entry points; as a
  -- SOLUTION SEQUENCE producer they contribute nothing, exactly as
  -- `eval_select_query`'s other arms return `[]`.
  | _ => []

/-! ## LATERAL — correlated evaluation

`LATERAL { P }` evaluates `P` once per left-hand row, with that row's
bindings substituted in. Two rules make it more than a plain join, and
both are ported:

  * a name the right-hand side would REASSIGN (via BIND, VALUES, or a
    sub-SELECT alias) is a fresh, deeper-scoped variable, so it is NOT
    substituted into that subtree;
  * SUB-SELECT PROJECTION MASKING: a sub-SELECT only receives
    substitutions for variables it actually projects. Jena's own
    documentation states this, and the F* source records the
    measurement against Apache Jena 5.2.0 — `LATERAL { SELECT ?label
    { ?s :label ?label } LIMIT 1 }` gives every outer row the SAME
    globally-smallest label, while `SELECT *` correlates per row.
    https://jena.apache.org/documentation/query/lateral-join.html -/

mutual

/-- Names a pattern could REASSIGN at its own top level. MINUS's right
operand never surfaces bindings, so it is excluded. Port of
`lateral_assignable_vars`. -/
def lateralAssignableVars : QueryPattern → List VarName
  | .bind _ v p        => v :: lateralAssignableVars p
  | .values vars _     => vars
  | .subSelect q       => subSelectAssignableVars q
  | .join p1 p2        => lateralAssignableVars p1 ++ lateralAssignableVars p2
  | .leftJoin p1 p2 _  => lateralAssignableVars p1 ++ lateralAssignableVars p2
  | .union p1 p2       => lateralAssignableVars p1 ++ lateralAssignableVars p2
  | .lateral p1 p2     => lateralAssignableVars p1 ++ lateralAssignableVars p2
  | .filter _ p1       => lateralAssignableVars p1
  | .graph _ p1        => lateralAssignableVars p1
  | .minus p1 _        => lateralAssignableVars p1
  | .service _ _ p1    => lateralAssignableVars p1
  | .serviceVar _ _ p1 => lateralAssignableVars p1
  | .bgp _ | .propertyPath _ _ _ | .empty => []

/-- A sub-SELECT's own non-projected variables are a deeper scope, so
`SELECT ?a ?b` contributes only its `AS` aliases; `SELECT *`
conservatively recurses. -/
def subSelectAssignableVars : Query → List VarName
  | .mk (.select (.vars items)) _ _ _ _ _ _ _ =>
      items.filterMap (fun it =>
        match it with
        | .var _    => none
        | .expr _ v => some v)
  | .mk (.select .all) _ p _ _ _ _ _ => lateralAssignableVars p
  | _ => []

end

/-- Which of a sub-SELECT's variables are even visible to LATERAL
substitution: `SELECT ?a ?b` exposes exactly those names, `SELECT *`
imposes no restriction, and a non-SELECT sub-query exposes nothing
(port of `lateral_subselect_visible_vars`). -/
def lateralVisibleVars : QueryForm → Option (List VarName)
  | .select (.vars items) =>
      some (items.map (fun it => match it with | .var v => v | .expr _ v => v))
  | .select .all => none
  | _            => some []

/-- The bindings that actually reach a sub-SELECT's WHERE clause:
masked by the projection, then with every locally-reassigned name
dropped (port of `lateral_subselect_visible_mu`). -/
def lateralVisibleMu (mu : Binding) (form : QueryForm) (inner : QueryPattern) :
    Binding :=
  let visible := match lateralVisibleVars form with
    | none     => mu
    | some vis => mu.filter (fun b => vis.contains b.1)
  let shadowed := lateralAssignableVars inner
  visible.filter (fun b => !shadowed.contains b.1)

/-! ## Substitution into pattern positions

Injecting a row's bindings replaces VARIABLE positions by the constant
the row binds them to. It is the same operation §18.6's EXISTS needs
(the F* `substitute_pattern`), and LATERAL's `lateral_substitute`
differs only in also descending into sub-SELECTs. -/

def substPatternTerm (mu : Binding) : PatternTerm → PatternTerm
  | .var v =>
      match mu.lookup v with
      | some (.iri i)     => .iri i
      | some (.bnode b)   => .bnode b
      | some (.literal l) => .literal l
      -- No triple-term PATTERN term is produced from a bound triple
      -- term (RDF 1.2, #305 in the F* tree) — leave the variable.
      | _                 => .var v
  | pt => pt

def substPatternSubject (mu : Binding) : PatternSubject → PatternSubject
  | .var v =>
      match mu.lookup v with
      | some (.iri i)   => .iri i
      | some (.bnode b) => .bnode b
      | _               => .var v
  | ps => ps

def substTriplePattern (mu : Binding) (tp : TriplePattern) : TriplePattern :=
  { s := substPatternSubject mu tp.s
    p := substPatternTerm mu tp.p
    o := substPatternTerm mu tp.o }

def substBgp (mu : Binding) (b : Bgp) : Bgp := b.map (substTriplePattern mu)

/-! ## WHERE-clause blank nodes — §18.2.4 (OutScope), §4.1.4

SPARQL 1.1 §4.1.4: "Blank node labels are scoped to the query … a
blank node in a query pattern acts as a non-distinguished variable".
The F* evaluator (`eval_select_query`, via
`rewrite_query_bnodes_pattern`) makes that literal: every `_:label`
in the WHERE clause becomes the variable `_bnode_label` before
matching, so it matches ANY term rather than only a data blank node
that happens to carry the same label — and `SELECT *` strips those
variables again (`strip_synthetic_bnode_vars`) because §18.2.4 puts
them outside the user's variable scope.

Port of `rewrite_query_bnode_term` / `rewrite_query_bnode_subject` /
`rewrite_query_bnodes_pattern`. The rewrite itself does not enter
embedded expressions, SERVICE bodies or VALUES rows.

An EXISTS body IS an embedded expression, and until 2026-08-26 that
left a blank node there matching as a constant — the residue of
https://github.com/danbri/factoidal/issues/607 that survived the
top-level rewrite. `substituteExistentials` now applies
`rewriteBnodes` to the body it is about to evaluate, which reaches
every EXISTS site at once (FILTER, an OPTIONAL condition, BIND, HAVING,
a SELECT expression, ORDER BY). The F* tree still has the residue:
`factoidal query` returned no results for
`SELECT ?x { ?x ex:b1 ?o FILTER EXISTS { ?x ex:b1 _:d } }` on
2026-08-26, where this tree now returns every row. A SERVICE body is
left alone deliberately: it is a query for a remote endpoint, which
applies §18.3.1 itself. -/

/-- `rewrite_query_bnode_term`: a blank node becomes `?_bnode_<label>`;
RDF 1.2 triple-term patterns are rewritten position by position. -/
def rewriteBnodeTerm : PatternTerm → PatternTerm
  | .bnode b          => .var ("_bnode_" ++ b)
  | .tripleTerm s p o => .tripleTerm (rewriteBnodeTerm s) (rewriteBnodeTerm p) (rewriteBnodeTerm o)
  | pt                => pt

/-- `rewrite_query_bnode_subject`. -/
def rewriteBnodeSubject : PatternSubject → PatternSubject
  | .bnode b => .var ("_bnode_" ++ b)
  | ps       => ps

/-- `rewrite_query_bnode_tp`. -/
def rewriteBnodeTriple (tp : TriplePattern) : TriplePattern :=
  { s := rewriteBnodeSubject tp.s, p := rewriteBnodeTerm tp.p, o := rewriteBnodeTerm tp.o }

mutual

/-- `rewrite_query_bnodes_pattern`, arm for arm.

The condition of a `FILTER` or an `OPTIONAL`, and a `BIND`
expression, are rewritten too: an `EXISTS { … _:b … }` body is a
graph pattern whose blank nodes are non-distinguished variables like
any other (`Expr.rewriteBnodes` below). A `SERVICE` body is left
alone — it is a query for a remote endpoint, which applies §18.3.1
itself. -/
def QueryPattern.rewriteBnodes : QueryPattern → QueryPattern
  | .bgp b            => .bgp (b.map rewriteBnodeTriple)
  | .join l r         => .join l.rewriteBnodes r.rewriteBnodes
  | .leftJoin l r c   => .leftJoin l.rewriteBnodes r.rewriteBnodes c.rewriteBnodes
  | .filter c p       => .filter c.rewriteBnodes p.rewriteBnodes
  | .union l r        => .union l.rewriteBnodes r.rewriteBnodes
  | .minus l r        => .minus l.rewriteBnodes r.rewriteBnodes
  | .graph n p        => .graph (rewriteBnodeTerm n) p.rewriteBnodes
  | .lateral l r      => .lateral l.rewriteBnodes r.rewriteBnodes
  | .bind e v p       => .bind e.rewriteBnodes v p.rewriteBnodes
  | .values vs rows   => .values vs rows
  | .service i s p    => .service i s p
  | .serviceVar v s p => .serviceVar v s p
  | .subSelect q      => .subSelect q.rewriteBnodes
  | .propertyPath s path o => .propertyPath (rewriteBnodeSubject s) path (rewriteBnodeTerm o)
  | .empty            => .empty

/-- The same rewrite inside an expression. Only `EXISTS` / `NOT
EXISTS` carry a graph pattern, so every other constructor is rebuilt
unchanged — arm for arm, no catch-all, so a new expression form
cannot silently hide an EXISTS (the discipline
`substituteExistentials` already follows). -/
def Expr.rewriteBnodes : Expr → Expr
  | .existsPat p    => .existsPat p.rewriteBnodes
  | .notExistsPat p => .notExistsPat p.rewriteBnodes
  -- Leaves.
  | .var v => .var v
  | .iri i => .iri i
  | .lit l => .lit l
  | .boolLit b => .boolLit b
  | .numericLit n => .numericLit n
  | .decimalLit s => .decimalLit s
  | .doubleLit s => .doubleLit s
  | .bound v => .bound v
  | .now => .now
  -- Recurse into sub-expressions.
  | .arith op a b => .arith op (Expr.rewriteBnodes a)
                              (Expr.rewriteBnodes b)
  | .unaryMinus a => .unaryMinus (Expr.rewriteBnodes a)
  | .unaryPlus a => .unaryPlus (Expr.rewriteBnodes a)
  | .compare op a b => .compare op (Expr.rewriteBnodes a)
                                  (Expr.rewriteBnodes b)
  | .and a b => .and (Expr.rewriteBnodes a)
                     (Expr.rewriteBnodes b)
  | .or a b => .or (Expr.rewriteBnodes a)
                   (Expr.rewriteBnodes b)
  | .not a => .not (Expr.rewriteBnodes a)
  | .isIri a => .isIri (Expr.rewriteBnodes a)
  | .isBlank a => .isBlank (Expr.rewriteBnodes a)
  | .isLiteral a => .isLiteral (Expr.rewriteBnodes a)
  | .isNumeric a => .isNumeric (Expr.rewriteBnodes a)
  | .str a => .str (Expr.rewriteBnodes a)
  | .lang a => .lang (Expr.rewriteBnodes a)
  | .datatype a => .datatype (Expr.rewriteBnodes a)
  | .iriFn a => .iriFn (Expr.rewriteBnodes a)
  | .hasLang a => .hasLang (Expr.rewriteBnodes a)
  | .hasLangDir a => .hasLangDir (Expr.rewriteBnodes a)
  | .langDir a => .langDir (Expr.rewriteBnodes a)
  | .strDt a b => .strDt (Expr.rewriteBnodes a)
                         (Expr.rewriteBnodes b)
  | .strLang a b => .strLang (Expr.rewriteBnodes a)
                             (Expr.rewriteBnodes b)
  | .strLangDir a b c => .strLangDir (Expr.rewriteBnodes a)
                                     (Expr.rewriteBnodes b)
                                     (Expr.rewriteBnodes c)
  | .cond c t e => .cond (Expr.rewriteBnodes c)
                         (Expr.rewriteBnodes t)
                         (Expr.rewriteBnodes e)
  | .coalesce es => .coalesce (Expr.rewriteBnodesList es)
  | .inList a es => .inList (Expr.rewriteBnodes a)
                            (Expr.rewriteBnodesList es)
  | .notInList a es => .notInList (Expr.rewriteBnodes a)
                                  (Expr.rewriteBnodesList es)
  | .strLen a => .strLen (Expr.rewriteBnodes a)
  | .substr a b c => .substr (Expr.rewriteBnodes a)
                             (Expr.rewriteBnodes b)
                             (Expr.rewriteBnodesOpt c)
  | .uCase a => .uCase (Expr.rewriteBnodes a)
  | .lCase a => .lCase (Expr.rewriteBnodes a)
  | .strStarts a b => .strStarts (Expr.rewriteBnodes a)
                                 (Expr.rewriteBnodes b)
  | .strEnds a b => .strEnds (Expr.rewriteBnodes a)
                             (Expr.rewriteBnodes b)
  | .contains a b => .contains (Expr.rewriteBnodes a)
                               (Expr.rewriteBnodes b)
  | .strBefore a b => .strBefore (Expr.rewriteBnodes a)
                                 (Expr.rewriteBnodes b)
  | .strAfter a b => .strAfter (Expr.rewriteBnodes a)
                               (Expr.rewriteBnodes b)
  | .concat es => .concat (Expr.rewriteBnodesList es)
  | .encodeForUri a => .encodeForUri (Expr.rewriteBnodes a)
  | .replace a b c d => .replace (Expr.rewriteBnodes a)
                                 (Expr.rewriteBnodes b)
                                 (Expr.rewriteBnodes c)
                                 (Expr.rewriteBnodesOpt d)
  | .regex a b c => .regex (Expr.rewriteBnodes a)
                           (Expr.rewriteBnodes b)
                           (Expr.rewriteBnodesOpt c)
  | .abs a => .abs (Expr.rewriteBnodes a)
  | .round a => .round (Expr.rewriteBnodes a)
  | .ceil a => .ceil (Expr.rewriteBnodes a)
  | .floor a => .floor (Expr.rewriteBnodes a)
  | .md5 a => .md5 (Expr.rewriteBnodes a)
  | .sha1 a => .sha1 (Expr.rewriteBnodes a)
  | .sha256 a => .sha256 (Expr.rewriteBnodes a)
  | .sha384 a => .sha384 (Expr.rewriteBnodes a)
  | .sha512 a => .sha512 (Expr.rewriteBnodes a)
  | .year a => .year (Expr.rewriteBnodes a)
  | .month a => .month (Expr.rewriteBnodes a)
  | .day a => .day (Expr.rewriteBnodes a)
  | .hours a => .hours (Expr.rewriteBnodes a)
  | .minutes a => .minutes (Expr.rewriteBnodes a)
  | .seconds a => .seconds (Expr.rewriteBnodes a)
  | .timezone a => .timezone (Expr.rewriteBnodes a)
  | .tz a => .tz (Expr.rewriteBnodes a)
  | .sameTerm a b => .sameTerm (Expr.rewriteBnodes a)
                               (Expr.rewriteBnodes b)
  | .aggregate fn d a => .aggregate fn d (Expr.rewriteBnodes a)
  | .functionCall i args => .functionCall i (Expr.rewriteBnodesList args)
  | .tripleTerm a b c => .tripleTerm (Expr.rewriteBnodes a)
                                     (Expr.rewriteBnodes b)
                                     (Expr.rewriteBnodes c)
  | .ttSubject a => .ttSubject (Expr.rewriteBnodes a)
  | .ttPredicate a => .ttPredicate (Expr.rewriteBnodes a)
  | .ttObject a => .ttObject (Expr.rewriteBnodes a)
  | .isTriple a => .isTriple (Expr.rewriteBnodes a)

/-- `Expr.rewriteBnodes` over an argument list. -/
def Expr.rewriteBnodesList : List Expr → List Expr
  | []      => []
  | e :: es => e.rewriteBnodes :: Expr.rewriteBnodesList es

/-- `Expr.rewriteBnodes` over an optional expression. -/
def Expr.rewriteBnodesOpt : Option Expr → Option Expr
  | none   => none
  | some e => some e.rewriteBnodes

/-- The `GP_SubSelect` arm: a sub-SELECT's own WHERE clause is rewritten
too (WHERE-clause blank nodes have to reach sub-SELECTs), and so are
the expressions its SELECT, GROUP BY, HAVING and ORDER BY clauses
carry, for the EXISTS bodies inside them. A CONSTRUCT template and a
DESCRIBE target list are NOT rewritten: §16.2 makes a template blank
node fresh per solution, which is a different rule. -/
def Query.rewriteBnodes : Query → Query
  | .mk f d p g h m v b =>
      .mk (QueryForm.rewriteBnodes f) d p.rewriteBnodes
          (match g with
           | none    => none
           | some cs => some (GroupCondition.rewriteBnodesList cs))
          (Expr.rewriteBnodesList h)
          (match m with
           | { orderBy := ob, distinct := dd, reduced := rr,
               offset := oo, limit := ll } =>
             { orderBy := (match ob with
                           | none    => none
                           | some cs => some (OrderCondition.rewriteBnodesList cs)),
               distinct := dd, reduced := rr, offset := oo, limit := ll })
          v b

/-- The SELECT clause's `(expr AS ?v)` items. -/
def QueryForm.rewriteBnodes : QueryForm → QueryForm
  | .select sel      => .select (SelectClause.rewriteBnodes sel)
  | .construct tpl   => .construct tpl
  | .ask             => .ask
  | .describe terms  => .describe terms

def SelectClause.rewriteBnodes : SelectClause → SelectClause
  | .vars items => .vars (SelectItem.rewriteBnodesList items)
  | .all        => .all

def SelectItem.rewriteBnodesList : List SelectItem → List SelectItem
  | []                  => []
  | .var v :: rest      => .var v :: SelectItem.rewriteBnodesList rest
  | .expr e v :: rest   => .expr e.rewriteBnodes v :: SelectItem.rewriteBnodesList rest

def GroupCondition.rewriteBnodesList : List GroupCondition → List GroupCondition
  | []                     => []
  | .var v :: rest         => .var v :: GroupCondition.rewriteBnodesList rest
  | .expr e a :: rest      => .expr e.rewriteBnodes a :: GroupCondition.rewriteBnodesList rest

def OrderCondition.rewriteBnodesList : List OrderCondition → List OrderCondition
  | []              => []
  | .asc e :: rest  => .asc e.rewriteBnodes :: OrderCondition.rewriteBnodesList rest
  | .desc e :: rest => .desc e.rewriteBnodes :: OrderCondition.rewriteBnodesList rest

end

/-! ## Lowering `QueryPattern` into the algebra

`lowerWith env mu p` compiles `p` into a `GraphPattern`, with `mu`'s
bindings substituted into every pattern position. `lower` is the
`mu = ∅` case, where substitution is the identity.

Fusing substitution into lowering is what makes LATERAL structural:
the recursive call goes to the genuine subterm `r` with a different
`mu`, instead of to a freshly SUBSTITUTED pattern that is no subterm
of anything (which is why the F* source needs
`lemma_lateral_substitute_preserves_size`). Composing an outer
substitution `mu` with a per-row one `mu2` is `Binding.merge mu mu2` —
the outer wins, which is exactly what substituting outside-in gives:
a variable the outer row already replaced by a constant is no longer
there for the inner row to touch.

The same fusion is what §18.6 EXISTS needs: `exists(pattern, μ)`
"evaluates substitute(pattern, μ)", and `lowerWith env μ pattern` IS
that substituted pattern. So EXISTS is handled here, in the mutual
block below, by the port of the F* `substitute_existentials`: before a
FILTER / OPTIONAL condition is evaluated on a row, every `EXISTS { P }`
/ `NOT EXISTS { P }` inside it is replaced by its boolean, obtained by
lowering `P` under the row and evaluating it against the ACTIVE graph
(the `Graph` the algebra hands the condition — `GRAPH ?g { … FILTER
EXISTS {…} }` sees the named graph, as `eval_exists … gs.gs_graph` does
in the F*) and the query's dataset (`EvalEnv.dataset`). The recursion
is structural: the EXISTS body is a subterm of the condition, which is
a subterm of the pattern — no fuel, no hook, no `partial`. With no
dataset in the environment an EXISTS is left in place and is the
expression-layer error.

Expressions are evaluated on `μ ⊕ row` (μ first): the substitution
replaces a variable the outer row bound EVERYWHERE in the pattern,
expressions included, which is the §18.6 text. (The F*
`substitute_pattern` / `lateral_substitute` leave embedded expressions
verbatim; the two agree whenever the body rebinds, or does not mention,
the outer variables — every W3C case — and this port keeps the
spec-literal reading the previous EXISTS stage chose.) -/

mutual

def QueryPattern.lowerWith (env : EvalEnv) (mu : Binding) (p : QueryPattern) :
    GraphPattern :=
  match p with
  | .bgp b       => .bgp (substBgp mu b)
  | .join l r    => .join (QueryPattern.lowerWith env mu l) (QueryPattern.lowerWith env mu r)
  | .leftJoin l r c =>
      .leftJoin (QueryPattern.lowerWith env mu l) (QueryPattern.lowerWith env mu r)
        (fun active row =>
          let mu' := mu.merge row
          ebvOrFalse (Expr.evalIn env mu' (substituteExistentials env active mu' c)))
  | .filter c q  =>
      .filter (fun active row =>
          let mu' := mu.merge row
          ebvOrFalse (Expr.evalIn env mu' (substituteExistentials env active mu' c)))
        (QueryPattern.lowerWith env mu q)
  | .union l r   => .union (QueryPattern.lowerWith env mu l) (QueryPattern.lowerWith env mu r)
  | .minus l r   => .minus (QueryPattern.lowerWith env mu l) (QueryPattern.lowerWith env mu r)
  | .graph name q =>
      .graph (substPatternTerm mu name) (QueryPattern.lowerWith env mu q)
  | .lateral l r =>
      .lateral (QueryPattern.lowerWith env mu l)
        (fun mu2 => QueryPattern.lowerWith env (mu.merge mu2) r)
  -- BIND: the F* `fx_bind_rows` evaluates the expression as is, with
  -- no existential substitution, so `BIND(EXISTS {…} AS ?v)` is an
  -- error there (and leaves ?v unbound); kept the same here.
  | .bind e v q =>
      .bind (fun row => (Expr.evalIn env (mu.merge row) e).toTerm?) v
        (QueryPattern.lowerWith env mu q)
  | .values vars rows => .values vars rows
  | .service i silent q =>
      .service (env.resolveService i.val) silent (QueryPattern.lowerWith env mu q)
  | .serviceVar v silent q =>
      -- A row that already binds the endpoint variable to an IRI
      -- resolves it here (the F* `lateral_substitute` GP_ServiceVar
      -- arm); otherwise the algebra resolves it per row inside a join.
      (match mu.lookup v with
       | some (.iri i) =>
           .service (env.resolveService i.val) silent (QueryPattern.lowerWith env mu q)
       | _ =>
           .serviceVar v env.resolveService silent (QueryPattern.lowerWith env mu q))
  | .subSelect q =>
      match q with
      | .mk form dcs inner gb hv md pv bs =>
          -- A sub-SELECT has no dataset clause in the SPARQL 1.1
          -- grammar (`SubSelect ::= SelectClause WhereClause
          -- SolutionModifier ValuesClause`), so `dcs` is carried for
          -- shape only and does not re-scope the graph here.
          .modified (selectPost env (.mk form dcs inner gb hv md pv bs))
            (QueryPattern.lowerWith env (lateralVisibleMu mu form inner) inner)
  | .propertyPath s path o =>
      .propertyPath (substPatternSubject mu s) path (substPatternTerm mu o)
  | .empty => .empty

/-- Port of the F* `substitute_existentials`: replace every
`EXISTS { P }` / `NOT EXISTS { P }` in an expression by the boolean
`exists(P, μ)` gives — §18.6: "true if `substitute(P, μ)`, evaluated
against the active graph and the dataset, has at least one solution"
(the F* `eval_exists`; named `evalExists` in `Exists.lean`) — so the
graph-free expression evaluator can finish the job. Every other
constructor is rebuilt with its sub-expressions substituted — arm for
arm with the F*, no catch-all, so a new expression form cannot
silently hide an EXISTS. -/
def substituteExistentials (env : EvalEnv) (active : Graph) (mu : Binding) :
    Expr → Expr
  | .existsPat p =>
      match env.dataset with
      | some ds => .boolLit (!((QueryPattern.lowerWith env mu p).evalIn ds active).isEmpty)
      | none    => .existsPat p
  | .notExistsPat p =>
      match env.dataset with
      | some ds => .boolLit ((QueryPattern.lowerWith env mu p).evalIn ds active).isEmpty
      | none    => .notExistsPat p
  -- Leaves.
  | .var v => .var v
  | .iri i => .iri i
  | .lit l => .lit l
  | .boolLit b => .boolLit b
  | .numericLit n => .numericLit n
  | .decimalLit s => .decimalLit s
  | .doubleLit s => .doubleLit s
  | .bound v => .bound v
  | .now => .now
  -- Recurse into sub-expressions.
  | .arith op a b => .arith op (substituteExistentials env active mu a)
                              (substituteExistentials env active mu b)
  | .unaryMinus a => .unaryMinus (substituteExistentials env active mu a)
  | .unaryPlus a => .unaryPlus (substituteExistentials env active mu a)
  | .compare op a b => .compare op (substituteExistentials env active mu a)
                                  (substituteExistentials env active mu b)
  | .and a b => .and (substituteExistentials env active mu a)
                     (substituteExistentials env active mu b)
  | .or a b => .or (substituteExistentials env active mu a)
                   (substituteExistentials env active mu b)
  | .not a => .not (substituteExistentials env active mu a)
  | .isIri a => .isIri (substituteExistentials env active mu a)
  | .isBlank a => .isBlank (substituteExistentials env active mu a)
  | .isLiteral a => .isLiteral (substituteExistentials env active mu a)
  | .isNumeric a => .isNumeric (substituteExistentials env active mu a)
  | .str a => .str (substituteExistentials env active mu a)
  | .lang a => .lang (substituteExistentials env active mu a)
  | .datatype a => .datatype (substituteExistentials env active mu a)
  | .iriFn a => .iriFn (substituteExistentials env active mu a)
  | .hasLang a => .hasLang (substituteExistentials env active mu a)
  | .hasLangDir a => .hasLangDir (substituteExistentials env active mu a)
  | .langDir a => .langDir (substituteExistentials env active mu a)
  | .strDt a b => .strDt (substituteExistentials env active mu a)
                         (substituteExistentials env active mu b)
  | .strLang a b => .strLang (substituteExistentials env active mu a)
                             (substituteExistentials env active mu b)
  | .strLangDir a b c => .strLangDir (substituteExistentials env active mu a)
                                     (substituteExistentials env active mu b)
                                     (substituteExistentials env active mu c)
  | .cond c t e => .cond (substituteExistentials env active mu c)
                         (substituteExistentials env active mu t)
                         (substituteExistentials env active mu e)
  | .coalesce es => .coalesce (substituteExistentialsList env active mu es)
  | .inList a es => .inList (substituteExistentials env active mu a)
                            (substituteExistentialsList env active mu es)
  | .notInList a es => .notInList (substituteExistentials env active mu a)
                                  (substituteExistentialsList env active mu es)
  | .strLen a => .strLen (substituteExistentials env active mu a)
  | .substr a b c => .substr (substituteExistentials env active mu a)
                             (substituteExistentials env active mu b)
                             (substituteExistentialsOpt env active mu c)
  | .uCase a => .uCase (substituteExistentials env active mu a)
  | .lCase a => .lCase (substituteExistentials env active mu a)
  | .strStarts a b => .strStarts (substituteExistentials env active mu a)
                                 (substituteExistentials env active mu b)
  | .strEnds a b => .strEnds (substituteExistentials env active mu a)
                             (substituteExistentials env active mu b)
  | .contains a b => .contains (substituteExistentials env active mu a)
                               (substituteExistentials env active mu b)
  | .strBefore a b => .strBefore (substituteExistentials env active mu a)
                                 (substituteExistentials env active mu b)
  | .strAfter a b => .strAfter (substituteExistentials env active mu a)
                               (substituteExistentials env active mu b)
  | .concat es => .concat (substituteExistentialsList env active mu es)
  | .encodeForUri a => .encodeForUri (substituteExistentials env active mu a)
  | .replace a b c d => .replace (substituteExistentials env active mu a)
                                 (substituteExistentials env active mu b)
                                 (substituteExistentials env active mu c)
                                 (substituteExistentialsOpt env active mu d)
  | .regex a b c => .regex (substituteExistentials env active mu a)
                           (substituteExistentials env active mu b)
                           (substituteExistentialsOpt env active mu c)
  | .abs a => .abs (substituteExistentials env active mu a)
  | .round a => .round (substituteExistentials env active mu a)
  | .ceil a => .ceil (substituteExistentials env active mu a)
  | .floor a => .floor (substituteExistentials env active mu a)
  | .md5 a => .md5 (substituteExistentials env active mu a)
  | .sha1 a => .sha1 (substituteExistentials env active mu a)
  | .sha256 a => .sha256 (substituteExistentials env active mu a)
  | .sha384 a => .sha384 (substituteExistentials env active mu a)
  | .sha512 a => .sha512 (substituteExistentials env active mu a)
  | .year a => .year (substituteExistentials env active mu a)
  | .month a => .month (substituteExistentials env active mu a)
  | .day a => .day (substituteExistentials env active mu a)
  | .hours a => .hours (substituteExistentials env active mu a)
  | .minutes a => .minutes (substituteExistentials env active mu a)
  | .seconds a => .seconds (substituteExistentials env active mu a)
  | .timezone a => .timezone (substituteExistentials env active mu a)
  | .tz a => .tz (substituteExistentials env active mu a)
  | .sameTerm a b => .sameTerm (substituteExistentials env active mu a)
                               (substituteExistentials env active mu b)
  | .aggregate fn d a => .aggregate fn d (substituteExistentials env active mu a)
  | .functionCall i args => .functionCall i (substituteExistentialsList env active mu args)
  | .tripleTerm a b c => .tripleTerm (substituteExistentials env active mu a)
                                     (substituteExistentials env active mu b)
                                     (substituteExistentials env active mu c)
  | .ttSubject a => .ttSubject (substituteExistentials env active mu a)
  | .ttPredicate a => .ttPredicate (substituteExistentials env active mu a)
  | .ttObject a => .ttObject (substituteExistentials env active mu a)
  | .isTriple a => .isTriple (substituteExistentials env active mu a)

/-- `substitute_existentials_list`. -/
def substituteExistentialsList (env : EvalEnv) (active : Graph) (mu : Binding) :
    List Expr → List Expr
  | []      => []
  | e :: es => substituteExistentials env active mu e ::
               substituteExistentialsList env active mu es

/-- `substitute_existentials_opt`. -/
def substituteExistentialsOpt (env : EvalEnv) (active : Graph) (mu : Binding) :
    Option Expr → Option Expr
  | none   => none
  | some e => some (substituteExistentials env active mu e)

end

/-- Compile a query pattern into the §18.5 algebra. -/
def QueryPattern.lower (env : EvalEnv) (p : QueryPattern) : GraphPattern :=
  QueryPattern.lowerWith env Binding.empty p

/-! ## §13.2 FROM / FROM NAMED -/

/-- Apply the query's dataset clauses. With no clause the dataset is
untouched; otherwise `FROM` graphs merge into a new default graph and
`FROM NAMED` graphs become the named ones (port of
`apply_query_dataset`). -/
def applyDataset (dcs : List DatasetClause) (ds : Dataset) (active : Graph) :
    Dataset × Graph :=
  if dcs.isEmpty then (ds, active)
  else
    let defaults := dcs.filterMap (fun dc =>
      match dc with
      | .default i => ds.lookupNamedIri i.val
      | .named _   => none)
    let named := dcs.filterMap (fun dc =>
      match dc with
      -- §13.2: a `FROM NAMED` clause carries an IRI, so the graph it
      -- installs is IRI-named.
      | .named i => (ds.lookupNamedIri i.val).map (fun g =>
          ({ name := .iri i, graph := g } : NamedGraph))
      | .default _ => none)
    let newDefault := defaults.foldl Graph.union Graph.empty
    ({ default := newDefault, named := named }, newDefault)


/-! ## Query evaluation — §18.2.4, §16.2 -/

/-- Every distinct variable a solution sequence binds, in first-seen
order — the projected variable list `SELECT *` denotes (port of
`collect_distinct_vars_in_order`). -/
def collectVarsFromRow : Binding → List VarName → List VarName
  | [],            acc => acc
  | (v, _) :: rest, acc =>
      if acc.contains v then collectVarsFromRow rest acc
      else collectVarsFromRow rest (acc ++ [v])

def collectVarsInOrder (omega : SolutionSeq) : List VarName :=
  omega.foldl (fun acc row => collectVarsFromRow row acc) []

/-- Evaluate a SELECT query — §18.2.4. Returns the projected variable
list (the result-set header) and the solution sequence.

Port of `eval_select_query`, including its first stage
`rewrite_query_bnodes_pattern` (WHERE-clause blank nodes become
non-distinguished variables — `QueryPattern.rewriteBnodes` above) and
the `SELECT *` strip inside `selectPost`. The one omitted stage is
`strip_rewrite_internal_vars`, which hides variables the F* tree's
`OWL.QueryRewrite` invents; that rewriter has no counterpart here. -/
def evalSelect (env : EvalEnv) (ds : Dataset) (q : Query) :
    List VarName × SolutionSeq :=
  let (ds', active) := applyDataset q.dataset ds ds.default
  -- §18.6: EXISTS inside the WHERE clause evaluates against the
  -- query's dataset (after FROM / FROM NAMED).
  let env := { env with dataset := some ds' }
  match q.form with
  | .select sel =>
      let omega := (q.pattern.rewriteBnodes.lower env).evalIn ds' active
      let rows := selectPost env q omega
      let vars := match sel with
        | .vars items => selectItemVars items
        | .all        => collectVarsInOrder rows
      (vars, rows)
  | _ => ([], [])

/-- Evaluate an ASK query — §18.2.4: true exactly when the pattern has
at least one solution (port of `eval_ask_query`). -/
def evalAsk (env : EvalEnv) (ds : Dataset) (q : Query) : Bool :=
  let (ds', active) := applyDataset q.dataset ds ds.default
  let env := { env with dataset := some ds' }
  match q.form with
  | .ask =>
      let omega0 := (q.pattern.rewriteBnodes.lower env).evalIn ds' active
      let omega := match q.postValues with
        | none      => omega0
        | some vals => join omega0 vals
      !omega.isEmpty
  | _ => false

/-! ### CONSTRUCT — §16.2

For each solution mapping the template is instantiated: variables are
replaced by their bindings, and template blank nodes get a label
scoped to (solution index, template label) — so one template label
denotes ONE node within a solution, and DIFFERENT nodes across
solutions. A template triple is emitted only when all three positions
resolve to terms of a legal kind (subject IRI or blank node,
predicate IRI); ill-formed instantiations are skipped, not errors. -/

/-- Port of `fresh_bnode_for`. -/
def freshBnodeFor (solIx : Nat) (templateLabel : String) : BNodeId :=
  "tpl_" ++ toString solIx ++ "_" ++ templateLabel

def constructSubject (ps : PatternSubject) (mu : Binding) (solIx : Nat) :
    Option Subject :=
  match ps with
  | .iri i   => some (.iri i)
  -- §16.2: a template blank node is FRESH per solution, keyed only by
  -- (solution index, template label) — never echoed from whatever the
  -- WHERE side bound the same label to.
  | .bnode b => some (.bnode (freshBnodeFor solIx b))
  -- A triple term can never be a triple's subject.
  | .tripleTerm _ _ _ => none
  | .var v =>
      match mu.lookup v with
      | some (.iri i)   => some (.iri i)
      | some (.bnode b) => some (.bnode b)
      | _               => none

def constructPredicate (pt : PatternTerm) (mu : Binding) : Option WfIri :=
  match pt with
  | .iri i => some i
  | .var v =>
      match mu.lookup v with
      | some (.iri i) => some i
      | _             => none
  -- A predicate must be an IRI.
  | _ => none

/-- RDF 1.2: a triple-term object grounds when every sub-position
does; template blank nodes inside it are freshened the same way. -/
def constructObject (pt : PatternTerm) (mu : Binding) (solIx : Nat) :
    Option Term :=
  match pt with
  | .iri i     => some (.iri i)
  | .bnode b   => some (.bnode (freshBnodeFor solIx b))
  | .literal l => some (.literal l)
  | .var v     => mu.lookup v
  | .tripleTerm ps pp po =>
      match constructObject ps mu solIx with
      | none => none
      | some sterm =>
          match sterm.toSubject? with
          | none => none
          | some ssub =>
              match constructObject pp mu solIx with
              | some (.iri ppi) =>
                  match constructObject po mu solIx with
                  | none       => none
                  | some oterm => some (.tripleTerm ssub ppi oterm)
              | _ => none

/-- Instantiate the whole template for one solution, dropping every
ill-formed triple (port of `instantiate_template`). -/
def instantiateTemplate (template : List TriplePattern) (mu : Binding)
    (solIx : Nat) : List Triple :=
  template.filterMap (fun tp =>
    match constructSubject tp.s mu solIx with
    | none   => none
    | some s =>
        match constructPredicate tp.p mu with
        | none   => none
        | some p =>
            match constructObject tp.o mu solIx with
            | none   => none
            | some o => some ({ s := s, p := p, o := o } : Triple))

def instantiateSolutions (template : List TriplePattern) :
    SolutionSeq → Nat → List Triple
  | [],       _  => []
  | mu :: rest, i => instantiateTemplate template mu i ++
                     instantiateSolutions template rest (i + 1)

/-- Evaluate a CONSTRUCT query — §16.2. The result is a GRAPH, so
duplicate triples collapse (`Graph.add` is set-based); the solution
modifiers apply to the solution sequence BEFORE the template is
instantiated (§18.2.4 builds `OrderBy` then `Slice` for every query
form; §16.2 instantiates the template over the resulting sequence), so
`ORDER BY … LIMIT n` selects the first `n` rows of the ORDERED
sequence, as in Jena / RDF4J.

Found by the differential harness (2026-08-22, generated seeds 169 and
324): this function sliced the UNORDERED sequence, and so does the F*
`eval_construct_query` — the two trees disagreed only because their
unordered evaluation orders differ. -/
def evalConstruct (env : EvalEnv) (ds : Dataset) (q : Query) : Graph :=
  let (ds', active) := applyDataset q.dataset ds ds.default
  let env := { env with dataset := some ds' }
  match q.form with
  | .construct template =>
      let omega0 := (q.pattern.rewriteBnodes.lower env).evalIn ds' active
      let omega := match q.postValues with
        | none      => omega0
        | some vals => join omega0 vals
      let ordered := match q.modifier.orderBy with
        | none   => omega
        | some o => sortSolutionsFast (compareOnConditions env o) omega
      let limited := sliceSolutions q.modifier.offset q.modifier.limit ordered
      (instantiateSolutions template limited 0).foldl (fun g t => g.add t) Graph.empty
  | _ => []

end L4Factoidal.SPARQL
