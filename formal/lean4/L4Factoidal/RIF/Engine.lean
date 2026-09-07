/-
L4Factoidal.RIF.Engine — forward chaining over RIF Core.

Spec: RIF Core §4 (semantics), read operationally: a Core rule set has
a least model, and a bounded semi-naive forward chain reaches it for a
program whose built-ins are decided.

## UNDECIDED is a third answer, and it is the one that keeps the score

A rule whose body needs a built-in this port does not decide cannot
fire. The closure is then INCOMPLETE, and an entailment question
answered from it is a guess. `entails` therefore returns
`.undecided`, not `.no`, whenever any rule was blocked that way —
`RIF-DTB` defines 197 built-ins and `RIF/Builtins.lean` decides a
named subset, so this case is not hypothetical.

The same applies to the round bound: a chain that stops at the bound
has not reached a fixed point, and reporting `no` from it would be
the same mistake.
-/
import L4Factoidal.RIF.Builtins

namespace L4Factoidal.RIF

/-- A GROUND atom — a fact. -/
inductive GAtom where
  | pos    (fn : String) (space : String) (args : List GTerm)
  | frame  (o p v : GTerm)
  | member (o c : GTerm)
  | sub    (c d : GTerm)
deriving Repr, DecidableEq, Inhabited

abbrev Facts := List GAtom

abbrev Subst := List (String × GTerm)

def lookupVar (s : Subst) (v : String) : Option GTerm :=
  (s.find? (fun (k, _) => k == v)).map (·.2)

/-- Extend a substitution, failing when the variable already stands
    for a DIFFERENT term. This is what makes a repeated variable a
    JOIN rather than two independent matches. -/
def extend (s : Subst) (v : String) (t : GTerm) : Option Subst :=
  match lookupVar s v with
  | some u => if u == t then some s else none
  | none   => some ((v, t) :: s)

/-- Whether a built-in blocked evaluation. Threaded through grounding
    and matching so a single `unknown` anywhere reaches the caller. -/
structure Res (α : Type) where
  value   : α
  blocked : Bool := false

/-- Ground a term pattern. `none` means it does not ground — an
    unbound variable — and `blocked` means a built-in was needed and
    not decided. -/
def groundTm (s : Subst) : Tm → Option GTerm × Bool
  | .var v      => (lookupVar s v, false)
  | .const l sp => (some (.const l sp), false)
  | .list xs    =>
      let rs := xs.map (groundTm s)
      let blocked := rs.any (·.2)
      match rs.foldr (fun r acc => match r.1, acc with
        | some t, some ts => some (t :: ts)
        | _, _ => none) (some []) with
      | some ts => (some (.list ts), blocked)
      | none    => (none, blocked)
  | .fapp fn sp xs =>
      let rs := xs.map (groundTm s)
      let blocked := rs.any (·.2)
      match rs.foldr (fun r acc => match r.1, acc with
        | some t, some ts => some (t :: ts)
        | _, _ => none) (some []) with
      | some ts => (some (.fapp fn sp ts), blocked)
      | none    => (none, blocked)
  | .external fn xs =>
      let rs := xs.map (groundTm s)
      let blocked := rs.any (·.2)
      match rs.foldr (fun r acc => match r.1, acc with
        | some t, some ts => some (t :: ts)
        | _, _ => none) (some []) with
      | none    => (none, blocked)
      | some ts =>
          match builtinName fn with
          | none    => (none, true)
          | some nm => (match evalFunc nm ts with
                        | some v => (some v, blocked)
                        | none   => (none, true))

/-- Match a term pattern against a ground term. -/
def matchTm (s : Subst) (pat : Tm) (t : GTerm) : Option Subst × Bool :=
  match pat with
  | .var v => (extend s v t, false)
  | _      => match groundTm s pat with
              | (some g, b) => (if g == t then some s else none, b)
              | (none, b)   => (none, b)

private def matchTms (s : Subst) : List Tm → List GTerm → Option Subst × Bool
  | [],      []      => (some s, false)
  | p :: ps, t :: ts =>
      (match matchTm s p t with
       | (none, b)    => (none, b)
       | (some s1, b) => let (r, b2) := matchTms s1 ps ts; (r, b || b2))
  | _, _ => (none, false)

/-! ## Equality in a rule body is equality of VALUES

RIF-BLD §3.5 reads `=` as equality in the domain of interpretation,
and RIF-DTB §2.4 gives the numeric datatypes one value space ordered
by `xs:decimal` containment. `2 = External(func:numeric-divide(6 3))`
is therefore true although the two sides carry different datatype
IRIs, and comparing the constants structurally made
`Builtins_Numeric` derive nothing.

The lexical-form-plus-family arm covers the string family, where
`xs:language`'s value space is contained in `xs:string`'s. -/
def gEqValue (a b : GTerm) : Bool :=
  if a == b then true
  else match numericLex a, numericLex b with
    | some x, some y => L4Factoidal.CSVW.decimalCompare x y == some .eq
    | _, _ =>
      match a, b with
      | .const l1 s1, .const l2 s2 =>
          l1 == l2 &&
          (match xsdLocal s1, xsdLocal s2 with
           | some c1, some c2 => xsdFamily c1 == xsdFamily c2
           | _, _             => false)
      | _, _ => false

/-! ## `pred:iri-string` BINDS, it does not only test

RIF-DTB §4.3 relates an IRI to the string of its characters, and
RIF Core's safeness rules give it a binding pattern in both
directions: with one side bound the other is determined.
`RIF/Engine.lean`'s `bindingBuiltins` already said so for the SAFENESS
check, but `matchAtom` only ever TESTED, so
`External(pred:iri-string(?z ?x))` with `?x` bound left `?z` unbound
and reported the built-in as blocked. -/
def iriStringBind (s : Subst) (args : List Tm) : Option (List Subst × Bool) :=
  match args with
  | [.var v, other] =>
      if (lookupVar s v).isSome then none
      else (match groundTm s other with
            | (some (.const lex sp), b) =>
                if sp == xsdNs ++ "string" then
                  some (match extend s v (gIri lex) with
                        | some s' => ([s'], b)
                        | none    => ([], b))
                else some ([], true)
            | (_, _) => none)
  | [other, .var v] =>
      if (lookupVar s v).isSome then none
      else (match groundTm s other with
            | (some (.const lex sp), b) =>
                if sp == iriSpace then
                  some (match extend s v (gStr lex) with
                        | some s' => ([s'], b)
                        | none    => ([], b))
                else some ([], true)
            | (_, _) => none)
  | _ => none

/-- Every substitution extending `s` under which the atom holds. -/
def matchAtom (facts : Facts) (s : Subst) (a : Atom) : List Subst × Bool :=
  match a with
  | .externalPred fn args =>
      (match builtinName fn with
       | none => ([], true)
       | some nm =>
           match (if nm == "iri-string" then iriStringBind s args else none) with
           | some r => r
           | none =>
           let rs := args.map (groundTm s)
           let blocked := rs.any (·.2)
           (match rs.foldr (fun r acc => match r.1, acc with
             | some t, some ts => some (t :: ts)
             | _, _ => none) (some []) with
            | none    => ([], true)
            | some ts => (match evalPred nm ts with
                          | .yes     => ([s], blocked)
                          | .no      => ([], blocked)
                          | .unknown => ([], true))))
  -- An `Equal` whose left or right side is an UNBOUND variable is a
  -- BIND, not a test: `?N = External(func:numeric-add(?N1 1))` is how
  -- `Factorial_Forward_Chaining` carries a computed value into the
  -- head. With both sides ground it is a value comparison.
  | .equal x y =>
      (match x, y with
       | .var v, _ =>
           if (lookupVar s v).isSome then
             (match groundTm s x, groundTm s y with
              | (some a', b1), (some b', b2) => (if gEqValue a' b' then [s] else [], b1 || b2)
              | (_, b1), (_, b2) => ([], b1 || b2))
           else (match groundTm s y with
                 | (some g, b) => (match extend s v g with
                                   | some s' => ([s'], b)
                                   | none    => ([], b))
                 | (none, b)   => ([], b))
       | _, .var v =>
           if (lookupVar s v).isSome then
             (match groundTm s x, groundTm s y with
              | (some a', b1), (some b', b2) => (if gEqValue a' b' then [s] else [], b1 || b2)
              | (_, b1), (_, b2) => ([], b1 || b2))
           else (match groundTm s x with
                 | (some g, b) => (match extend s v g with
                                   | some s' => ([s'], b)
                                   | none    => ([], b))
                 | (none, b)   => ([], b))
       | _, _ =>
           (match groundTm s x, groundTm s y with
            | (some a', b1), (some b', b2) => (if gEqValue a' b' then [s] else [], b1 || b2)
            | (_, b1), (_, b2) => ([], b1 || b2)))
  | .pos fn sp args =>
      facts.foldl (fun (acc, blk) f => match f with
        | .pos fn2 sp2 args2 =>
            if fn == fn2 && sp == sp2 && args.length == args2.length then
              (match matchTms s args args2 with
               | (some s', b) => (acc ++ [s'], blk || b)
               | (none, b)    => (acc, blk || b))
            else (acc, blk)
        | _ => (acc, blk)) ([], false)
  | .frame o p v =>
      facts.foldl (fun (acc, blk) f => match f with
        | .frame o2 p2 v2 =>
            (match matchTms s [o, p, v] [o2, p2, v2] with
             | (some s', b) => (acc ++ [s'], blk || b)
             | (none, b)    => (acc, blk || b))
        | _ => (acc, blk)) ([], false)
  | .member o c =>
      facts.foldl (fun (acc, blk) f => match f with
        | .member o2 c2 =>
            (match matchTms s [o, c] [o2, c2] with
             | (some s', b) => (acc ++ [s'], blk || b)
             | (none, b)    => (acc, blk || b))
        | _ => (acc, blk)) ([], false)
  | .sub c d =>
      facts.foldl (fun (acc, blk) f => match f with
        | .sub c2 d2 =>
            (match matchTms s [c, d] [c2, d2] with
             | (some s', b) => (acc ++ [s'], blk || b)
             | (none, b)    => (acc, blk || b))
        | _ => (acc, blk)) ([], false)

/-! ## A conjunction is a SET of conjuncts, not a sequence

RIF-BLD §3.2 gives `And` no order, so a built-in call or an `Equal`
may be written before the atom that binds its variables --
`Factorial_Forward_Chaining` opens its body with
`External(pred:numeric-greater-than-or-equal(?N1 0))` and binds `?N1`
two conjuncts later. Folding the conjuncts strictly left to right
called the built-in on an unground argument, got `unknown` back, and
reported the whole case UNDECIDED.

The repair evaluates the ordinary atoms first and then applies the
conditions in whatever order becomes EVALUABLE, to a fixed point. A
condition that never becomes evaluable still reports blocked, which is
the same conservative answer as before for a genuinely missing
built-in. -/

/-- Is a term ground under `s`? Used only to decide whether a
    condition can run yet, never to compute a value. -/
def tmGround (s : Subst) (t : Tm) : Bool := (groundTm s t).1.isSome

/-- Can this condition run under `s`? A built-in needs every argument
    ground, unless it is `pred:iri-string` with exactly one side an
    unbound variable. An `Equal` needs both sides ground, or one side
    ground with the other an unbound variable, which is the BIND. -/
def condEvaluable (s : Subst) : Atom → Bool
  | .externalPred fn args =>
      (match builtinName fn, args with
       | some "iri-string", [.var v, other] =>
           (lookupVar s v).isNone && tmGround s other || args.all (tmGround s)
       | some "iri-string", [other, .var v] =>
           (lookupVar s v).isNone && tmGround s other || args.all (tmGround s)
       | _, _ => args.all (tmGround s))
  | .equal x y =>
      (match x, y with
       | .var v, _ => ((lookupVar s v).isNone && tmGround s y) || (tmGround s x && tmGround s y)
       | _, .var v => ((lookupVar s v).isNone && tmGround s x) || (tmGround s x && tmGround s y)
       | _, _      => tmGround s x && tmGround s y)
  | _ => true

/-- The first evaluable condition and the rest, order otherwise kept. -/
def splitEvaluable (s : Subst) : List Atom → Option (Atom × List Atom)
  | []      => none
  | a :: rest =>
      if condEvaluable s a then some (a, rest)
      else (splitEvaluable s rest).map (fun (b, r) => (b, a :: r))

/-- Apply the pending conditions to a fixed point. Fuel is the pending
    count, since each step removes one. -/
def runConds (facts : Facts) : Nat → Subst → List Atom → List Subst × Bool
  | _,        s, []      => ([s], false)
  | 0,        _, _ :: _  => ([], true)
  | fuel + 1, s, pending =>
      match splitEvaluable s pending with
      | none          => ([], true)
      | some (a, rest) =>
          let (ss, b) := matchAtom facts s a
          let rs := ss.map (fun s' => runConds facts fuel s' rest)
          (rs.flatMap (·.1), b || rs.any (·.2))

def isCondAtom : Formula → Bool
  | .atom (.externalPred _ _) => true
  | .atom (.equal _ _)        => true
  | _                         => false

def matchFormula (facts : Facts) (s : Subst) : Formula → List Subst × Bool
  | .atom a => matchAtom facts s a
  | .and fs =>
      let conds : List Atom := fs.filterMap (fun f =>
        match f with
        | .atom (.externalPred fn args) => some (.externalPred fn args)
        | .atom (.equal x y)            => some (.equal x y)
        | _                             => none)
      -- The generator pass folds over `fs` ITSELF, skipping the
      -- conditions in place rather than filtering them out first: the
      -- recursive call must sit under a fold on the constructor's own
      -- argument for Lean to see it decrease.
      let (ss, blk) := fs.foldl (fun (acc, b) f =>
        if isCondAtom f then (acc, b)
        else
          let rs := acc.map (fun s' => matchFormula facts s' f)
          (rs.flatMap (·.1), b || rs.any (·.2))) ([s], false)
      let rs := ss.map (fun s' => runConds facts conds.length s' conds)
      (rs.flatMap (·.1), blk || rs.any (·.2))
  | .or fs =>
      let rs := fs.map (fun f => matchFormula facts s f)
      (rs.flatMap (·.1), rs.any (·.2))
  -- `Exists` binds its variables inside; a substitution that reaches
  -- the caller must not carry them, or a later conjunct would join
  -- against a variable the formula quantified away.
  | .exists vars f =>
      let (rs, b) := matchFormula facts s f
      (rs.map (fun s' => s'.filter (fun (k, _) => !(vars.contains k))), b)

/-- Instantiate a head atom into a fact. -/
def instantiate (s : Subst) (a : Atom) : Option GAtom × Bool :=
  match a with
  | .pos fn sp args =>
      let rs := args.map (groundTm s)
      let b := rs.any (·.2)
      (match rs.foldr (fun r acc => match r.1, acc with
        | some t, some ts => some (t :: ts)
        | _, _ => none) (some []) with
       | some ts => (some (.pos fn sp ts), b)
       | none    => (none, b))
  | .frame o p v =>
      (match groundTm s o, groundTm s p, groundTm s v with
       | (some a', b1), (some b', b2), (some c', b3) =>
           (some (.frame a' b' c'), b1 || b2 || b3)
       | (_, b1), (_, b2), (_, b3) => (none, b1 || b2 || b3))
  | .member o c =>
      (match groundTm s o, groundTm s c with
       | (some a', b1), (some b', b2) => (some (.member a' b'), b1 || b2)
       | (_, b1), (_, b2) => (none, b1 || b2))
  | .sub c d =>
      (match groundTm s c, groundTm s d with
       | (some a', b1), (some b', b2) => (some (.sub a' b'), b1 || b2)
       | (_, b1), (_, b2) => (none, b1 || b2))
  | .equal _ _ | .externalPred _ _ => (none, false)

/-- One round of forward chaining. -/
def step (rules : List Rule) (facts : Facts) : Facts × Bool :=
  rules.foldl (fun (acc, blk) r =>
    match r.body with
    | none =>
        (match instantiate [] r.head with
         | (some f, b) => (acc ++ [f], blk || b)
         | (none, b)   => (acc, blk || b))
    | some body =>
        let (ss, b) := matchFormula facts [] body
        let derived := ss.foldl (fun (a2, b2) s =>
          match instantiate s r.head with
          | (some f, b3) => (a2 ++ [f], b2 || b3)
          | (none, b3)   => (a2, b2 || b3)) ([], false)
        (acc ++ derived.1, blk || b || derived.2)) ([], false)

/-- Forward chain to a fixed point, bounded by `rounds`. Returns the
    facts, whether a built-in blocked any rule, and whether the bound
    was reached. Both flags travel with the answer because an
    entailment read off a closure that is missing either is a guess. -/
def closure (rules : List Rule) (facts : Facts) (rounds : Nat)
    : Facts × Bool × Bool :=
  match rounds with
  | 0     => (facts, false, true)
  | n + 1 =>
      let (new, blocked) := step rules facts
      let fresh := new.filter (fun f => !(facts.contains f))
      let fresh := fresh.foldl (fun acc f => if acc.contains f then acc else acc ++ [f]) []
      if fresh.isEmpty then (facts, blocked, false)
      else
        let (fs, b2, cap) := closure rules (facts ++ fresh) n
        (fs, blocked || b2, cap)

inductive Verdict where
  | holds | doesNotHold | undecided (why : String)
deriving Repr, DecidableEq, Inhabited

/-- Does the closure entail the goal formula? `undecided` when a
    built-in blocked a rule or the round bound was reached — a closure
    missing either is not the closure, and reading `doesNotHold` off
    it would be a guess. -/
def entails (rules : List Rule) (facts : Facts) (goal : Formula) (rounds : Nat)
    : Verdict :=
  let (fs, blocked, capped) := closure rules facts rounds
  let (ss, gblocked) := matchFormula fs [] goal
  if !ss.isEmpty then .holds
  else if blocked || gblocked then
    .undecided "a built-in outside this port's slice blocked a rule or the goal"
  else if capped then .undecided "the forward chain reached its round bound"
  else .doesNotHold

/-! ## Which built-ins a case uses

`entails` reports `undecided` when a built-in blocked a rule, but the
flag it threads is a Bool, so it cannot say WHICH one. Naming the
built-in is what makes an undecided verdict reviewable — the F\* tree's
skips name theirs — so the built-in IRIs a document MENTIONS are
collected here and printed beside the verdict.

This is the set of CANDIDATES, not the one that blocked: a case may
name several and be stopped by one of them. Reported as candidates
rather than as a cause, because claiming the cause without measuring
it would be a guess. Threading the blocking IRI itself through
`groundTm`/`matchAtom`/`step`/`closure` is the fix that would say
exactly which, and is not done here. -/

mutual

def externalIrisTm : Tm → List String
  | .var _            => []
  | .const _ _        => []
  | .list xs          => externalIrisTms xs
  | .external fn args => fn :: externalIrisTms args
  | .fapp _ _ args    => externalIrisTms args

def externalIrisTms : List Tm → List String
  | []      => []
  | x :: xs => externalIrisTm x ++ externalIrisTms xs

end

def externalIrisAtom : Atom → List String
  | .pos _ _ args        => externalIrisTms args
  | .frame o p v         => externalIrisTm o ++ externalIrisTm p ++ externalIrisTm v
  | .member o c          => externalIrisTm o ++ externalIrisTm c
  | .sub c d             => externalIrisTm c ++ externalIrisTm d
  | .equal a b           => externalIrisTm a ++ externalIrisTm b
  | .externalPred fn args => fn :: externalIrisTms args

mutual

def externalIrisFormula : Formula → List String
  | .atom a       => externalIrisAtom a
  | .and fs       => externalIrisFormulas fs
  | .or fs        => externalIrisFormulas fs
  | .exists _ f   => externalIrisFormula f

def externalIrisFormulas : List Formula → List String
  | []      => []
  | f :: fs => externalIrisFormula f ++ externalIrisFormulas fs

end

def externalIrisRule (r : Rule) : List String :=
  externalIrisAtom r.head ++ (r.body.map externalIrisFormula).getD []

/-- Every built-in IRI a rule set and a goal name, without repeats and
in first-mention order. -/
def externalIrisUsed (rules : List Rule) (goal : Formula) : List String :=
  (rules.flatMap externalIrisRule ++ externalIrisFormula goal).foldl
    (fun acc i => if acc.contains i then acc else acc ++ [i]) []

/-! An `External` in either position is collected, and a case that
names none reports none. -/
#guard externalIrisUsed [] (.atom (.frame (.var "x") (.var "p") (.var "v"))) = []

#guard externalIrisUsed []
  (.atom (.externalPred "http://www.w3.org/2007/rif-builtin-predicate#is-literal-dateTime"
            [.var "d"])) =
  ["http://www.w3.org/2007/rif-builtin-predicate#is-literal-dateTime"]

#guard externalIrisUsed
  [{ head := .frame (.var "x") (.var "p")
       (.external "http://www.w3.org/2007/rif-builtin-function#numeric-add"
          [.var "a", .var "b"]) }]
  (.atom (.externalPred "http://www.w3.org/2007/rif-builtin-predicate#numeric-equal"
            [.var "a", .var "b"])) =
  ["http://www.w3.org/2007/rif-builtin-function#numeric-add",
   "http://www.w3.org/2007/rif-builtin-predicate#numeric-equal"]

/-! ## Local constants are DOCUMENT-SCOPED (RIF-BLD 3.4)

A constant in `rif:local` means something only inside the document
that writes it: `_p` in a premise and `_p` in a conclusion are
DIFFERENT symbols. Leaving the two spelled the same made the premise
entail the conclusion, which is exactly what `Local_Predicate` and
`Local_Constant` say must not happen.

Qualifying the name with the document is the whole rule. -/

def qualifyTm (tag : String) : Tm -> Tm
  | .var v         => .var v
  | .const l sp    => if sp == localSpace then .const (tag ++ "#" ++ l) sp else .const l sp
  | .list xs       => .list (xs.map (qualifyTm tag))
  | .fapp f sp xs  =>
      .fapp (if sp == localSpace then tag ++ "#" ++ f else f) sp (xs.map (qualifyTm tag))
  | .external f xs => .external f (xs.map (qualifyTm tag))

def qualifyAtom (tag : String) : Atom -> Atom
  | .pos f sp args    =>
      .pos (if sp == localSpace then tag ++ "#" ++ f else f) sp (args.map (qualifyTm tag))
  | .frame o p v      => .frame (qualifyTm tag o) (qualifyTm tag p) (qualifyTm tag v)
  | .member o c       => .member (qualifyTm tag o) (qualifyTm tag c)
  | .sub c d          => .sub (qualifyTm tag c) (qualifyTm tag d)
  | .equal a b        => .equal (qualifyTm tag a) (qualifyTm tag b)
  | .externalPred f a => .externalPred f (a.map (qualifyTm tag))

def qualifyFormula (tag : String) : Formula -> Formula
  | .atom a       => .atom (qualifyAtom tag a)
  | .and fs       => .and (fs.map (qualifyFormula tag))
  | .or fs        => .or (fs.map (qualifyFormula tag))
  | .exists vs f  => .exists vs (qualifyFormula tag f)

def qualifyRule (tag : String) (r : Rule) : Rule :=
  { r with head := qualifyAtom tag r.head, body := r.body.map (qualifyFormula tag) }

/-! ## Safeness (RIF Core, "Safeness")

A Core rule is SAFE when every variable it uses is BOUND by a
positive, non-built-in atom in its body. A head variable the body
never binds, or a variable outside the `Forall` list, makes the
document ill-formed -- which is what the three `NegativeSyntaxTest`
cases assert, and what a parser alone cannot see. -/

def varsOfTm : Tm -> List String
  | .var v         => [v]
  | .const _ _     => []
  | .list xs       => xs.flatMap varsOfTm
  | .fapp _ _ xs   => xs.flatMap varsOfTm
  | .external _ xs => xs.flatMap varsOfTm

def varsOfAtom : Atom -> List String
  | .pos _ _ args     => args.flatMap varsOfTm
  | .frame o p v      => varsOfTm o ++ varsOfTm p ++ varsOfTm v
  | .member o c       => varsOfTm o ++ varsOfTm c
  | .sub c d          => varsOfTm c ++ varsOfTm d
  | .equal a b        => varsOfTm a ++ varsOfTm b
  | .externalPred _ a => a.flatMap varsOfTm

/-- The variables an atom BINDS. A built-in binds nothing: it TESTS
    its arguments, so a variable that occurs only there is unbound. -/
def boundByAtom : Atom -> List String
  | .externalPred _ _ => []
  | .equal _ _        => []
  | a                 => varsOfAtom a

def boundByFormula : Formula -> List String
  | .atom a      => boundByAtom a
  | .and fs      => fs.flatMap boundByFormula
  | .or []       => []
  -- A DISJUNCTION binds only what EVERY branch binds.
  | .or (f :: fs) =>
      fs.foldl (fun acc g => acc.filter (boundByFormula g).contains) (boundByFormula f)
  | .exists vs f => (boundByFormula f).filter (fun v => !(vs.contains v))

def varsOfFormula : Formula -> List String
  | .atom a      => varsOfAtom a
  | .and fs      => fs.flatMap varsOfFormula
  | .or fs       => fs.flatMap varsOfFormula
  | .exists vs f => (varsOfFormula f).filter (fun v => !(vs.contains v))

/-- The built-ins that BIND rather than only test. RIF Core's
    safeness rules give each built-in a binding pattern;
    `pred:iri-string` relates an IRI and a string and binds either
    from the other, which is what `Core_Safeness_3` relies on. A
    built-in not on this list binds nothing, so a variable occurring
    only in one stays unbound. -/
def bindingBuiltins : List String := ["iri-string"]

/-- The variables a body binds, to a FIXPOINT.

    Boundness PROPAGATES, and the first version of this missed both
    ways it does. `?x = ?y` makes `?y` bound once `?x` is
    (`Core_Safeness_2` is `ex:q(?x) ?x=?y ?y=?z` with `?z` in the
    head), and a binding built-in with one variable left binds it
    (`Core_Safeness_3`). Taking one pass over the body called both
    documents unsafe, and they are ordinary RIF Core. -/
def boundFix : Nat -> Formula -> List String -> List String
  | 0,        _, acc => acc
  | fuel + 1, b, acc =>
      let conjuncts : List Atom :=
        let rec flat : Formula -> List Atom
          | .atom a      => [a]
          | .and fs      => fs.flatMap flat
          | .exists _ f  => flat f
          | .or _        => []
        flat b
      let grown := conjuncts.foldl (fun bs a =>
        match a with
        | .equal x y =>
            let xv := varsOfTm x
            let yv := varsOfTm y
            if xv.all bs.contains then
              bs ++ yv.filter (fun v => !(bs.contains v))
            else if yv.all bs.contains then
              bs ++ xv.filter (fun v => !(bs.contains v))
            else bs
        | .externalPred fn args =>
            (match builtinName fn with
             | none => bs
             | some nm =>
                 if !(bindingBuiltins.contains nm) then bs
                 else
                   let free := (args.flatMap varsOfTm).filter (fun v => !(bs.contains v))
                   let free := free.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []
                   if free.length == 1 then bs ++ free else bs)
        | _ => bs) acc
      if grown.length == acc.length then acc else boundFix fuel b grown

def ruleSafe (r : Rule) : Bool :=
  let hv := varsOfAtom r.head
  match r.body with
  -- A FACT with a variable is not a fact.
  | none => hv.isEmpty
  | some b =>
      let bound := boundFix 16 b (boundByFormula b)
      let used := hv ++ varsOfFormula b
      hv.all bound.contains &&
      (varsOfFormula b).all bound.contains &&
      -- ...and every variable must be one the `Forall` quantifies.
      used.all (fun v => r.vars.contains v)

def documentSafe (rs : List Rule) : Bool := rs.all ruleSafe

end L4Factoidal.RIF
