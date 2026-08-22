/-
L4Factoidal.Schematron.Validate — the Schematron report model, ported
from `formal/fstar/Schematron.Validate.fst`.

Spec: ISO/IEC 19757-3 (Schematron). A schema is patterns of rules;
each rule has a `@context` selecting nodes, and each selected node is
checked against the rule's assertions.

THE INVERSION, which is the single thing Schematron implementations
get wrong: `assert` and `report` fire on OPPOSITE truth values.

* An `<assert test="X">` produces a finding when X is FALSE — it
  asserts X must hold, so a failure is news.
* A `<report test="X">` produces a finding when X is TRUE — it
  reports the presence of X.

Both are "findings"; they are not both "failures", and they are not
the same predicate negated at the call site. They are kept as
separate finding constructors here so a consumer cannot lose the
distinction.
-/

namespace L4Factoidal.Schematron

structure Assertion where
  /-- `true` for an `<assert>` element, `false` for a `<report>`. -/
  isAssert : Bool
  /-- The `@test` XPath, evaluated as a boolean. -/
  test     : String
  message  : String
deriving Repr, DecidableEq, Inhabited

structure Let where
  name  : String
  value : String
deriving Repr, DecidableEq, Inhabited

structure Rule where
  context    : String
  lets       : List Let := []
  assertions : List Assertion := []
deriving Repr, Inhabited

structure Pattern where
  id    : String
  rules : List Rule := []
deriving Repr, Inhabited

structure Schema where
  namespaces : List (String × String) := []
  lets       : List Let := []
  patterns   : List Pattern := []
deriving Repr, Inhabited

/-- A validation finding.

    `indeterminate` carries its REASON, and exists for the same
    purpose as the three-valued results elsewhere in this port: a test
    the evaluator cannot decide must not be silently reported as
    passing, nor as failing. -/
inductive Finding where
  | assertFail    (ctx test msg path : String)
  | reportHit     (ctx test msg path : String)
  | indeterminate (ctx test msg path reason : String)
deriving Repr, DecidableEq, Inhabited

def Finding.kind : Finding → String
  | .assertFail ..    => "assert-fail"
  | .reportHit ..     => "report-hit"
  | .indeterminate .. => "indeterminate"

def Finding.context : Finding → String
  | .assertFail c .. | .reportHit c .. | .indeterminate c .. => c

def Finding.test : Finding → String
  | .assertFail _ t .. | .reportHit _ t .. | .indeterminate _ t .. => t

def Finding.message : Finding → String
  | .assertFail _ _ m _ | .reportHit _ _ m _ | .indeterminate _ _ m _ _ => m

def Finding.path : Finding → String
  | .assertFail _ _ _ p | .reportHit _ _ _ p | .indeterminate _ _ _ _ p => p

/-- The outcome of evaluating one `@test`: true, false, or
    undecidable with a reason. -/
inductive TestResult where
  | true' | false' | undecided (reason : String)
deriving Repr, DecidableEq, Inhabited

/-- Apply one assertion at one node, given its test's outcome.

    THE INVERSION lives here and nowhere else: an `assert` yields a
    finding on FALSE, a `report` on TRUE. -/
def applyAssertion (a : Assertion) (ctx path : String) (r : TestResult)
    : Option Finding :=
  match r, a.isAssert with
  | .false', true  => some (.assertFail ctx a.test a.message path)
  | .true',  true  => none
  | .true',  false => some (.reportHit ctx a.test a.message path)
  | .false', false => none
  | .undecided why, _ =>
      some (.indeterminate ctx a.test a.message path why)

/-- Evaluate a rule at the nodes its context selected. `evalTest`
    supplies the host XPath evaluation; keeping it a PARAMETER rather
    than a global registry is the purity doctrine again — this module
    is a total function of explicit inputs. -/
def applyRule (r : Rule) (nodes : List String)
    (evalTest : String → String → TestResult) : List Finding :=
  nodes.flatMap (fun path =>
    r.assertions.filterMap (fun a =>
      applyAssertion a r.context path (evalTest a.test path)))

/-- Validate a schema. `select` supplies context-pattern matching.

    Schematron's rule-per-node semantics: within a PATTERN, the FIRST
    rule whose context matches a node claims it, and later rules in
    the same pattern do not fire for that node. Patterns are
    independent of each other. Getting this wrong produces duplicate
    findings that look like genuine extra violations. -/
def validate (s : Schema) (allNodes : List String)
    (select : String → String → Bool)
    (evalTest : String → String → TestResult) : List Finding :=
  s.patterns.flatMap (fun p =>
    let (findings, _) := p.rules.foldl (fun (acc, claimed) r =>
      let nodes := allNodes.filter (fun n =>
        select r.context n && !(claimed.contains n))
      (acc ++ applyRule r nodes evalTest, claimed ++ nodes)) ([], ([] : List String))
    findings)

/-- Did validation find anything that counts as a violation? An
    INDETERMINATE result is not a pass — it is reported separately so
    a caller cannot mistake "could not decide" for "fine". -/
def hasViolations (fs : List Finding) : Bool :=
  fs.any (fun f => match f with
    | .assertFail .. | .reportHit .. => true
    | .indeterminate .. => false)

def hasIndeterminate (fs : List Finding) : Bool :=
  fs.any (fun f => match f with | .indeterminate .. => true | _ => false)

end L4Factoidal.Schematron
