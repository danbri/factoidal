# Does an IKL-based proof format need an entailment regime? And does the
# Hayes reduction help?

Status: design answer, 2026-08-27. Owner questions, verbatim:

> "Ok so to check a Factoidal proof format based on ikl do we need to
> specify an entailment regime / inference system?"
> "Does the Pat Hayes rewriter to FOPC help?"

Short answers: **an inference system yes, an entailment regime no —
they are different things and the format needs them in different
places.** The Hayes reduction helps on the PRODUCER side and must not
enter the checker.

## 1. Two things that are easy to conflate

| | what it is | where the format needs it |
|---|---|---|
| **inference system** (calculus) | a finite set of rule schemas, each with a local, decidable side condition | in the GRAMMAR — the set of rule identifiers a step may name, and the check function for each |
| **entailment regime** | a specification of what follows from what, semantically | in the per-step `profile` field as metadata, and in the SOUNDNESS THEOREM that relates the calculus to it |

A checker needs the calculus. It must never be handed the regime as
something to decide. That is the `semanticConsequence` rule the FPP0
adoption bans by name: a rule whose check is "do the premises entail the
conclusion" hides theorem proving inside checking, and stops the checker
being small.

So the format does not take "an entailment regime" as a parameter the
caller selects, the way SPARQL query answering does. Each STEP names the
specification row and profile it used. Different steps in one chain may
name different regimes — that is what makes the chain heterogeneous.

Concretely, this is already how the landed RDFS layer works:

- calculus: `RuleId`, 16 rows, each with a total `rowCheck` case
  (`RDFS/DerivationCheck.lean`)
- regime: `DerivesFull`, and `unified_adequate_rdfs` carrying it to
  model-theoretic entailment
- the bridge: `checkDerivation_sound`

## 2. What this means for IKL specifically

IKL has a model theory (Hayes and Menzel) but ships **no proof theory,
no entailment procedure and no profiles**. Owner, 2026-08-26, on the
`x-ikl-*` regime identifiers: it "is incomplete since IKL doesn't ship
with profiles or entailment procedures, or a mapping from rdf datasets".

Consequence: for IKL-bearing claims there is no standard calculus to
adopt. We must DEFINE a small one. That is what IKLbase is for, and why
the handoff calls it the reference adapter — a deliberately small rule
set, checked directly in Lean, is the shortest route to a genuinely
foundational multi-step proof.

So the answer to "do we need to specify an inference system" is yes, and
the work is not selecting one but writing one: a handful of IKL rule
schemas, each locally decidable, each with a Lean soundness lemma
against the IKL model theory already in `CL/IklModels.lean`.

What we do NOT need, and should not attempt: a complete inference system
for IKL. Completeness is not required for certificate checking. A
certificate presents a derivation; the calculus only has to be able to
CHECK the derivations we can produce, and to be sound. An incomplete
calculus rejects some true claims and never accepts a false one, which
is the correct failure direction.

## 3. Does the Hayes reduction help?

Hayes 2009, "A Satisfiability-Preserving Reduction of IKL to Common
Logic" — implemented in `CL/Normalize.lean` and
`CL/NormalizeSemantics.lean`, with `tails_satisfiable` proved for the
no-intrusion fragment.

### Where it helps

**Proof SEARCH, outside the trusted kernel.** The reduction gives an
IKL sentence set an equisatisfiable first-order counterpart. That means
ordinary first-order tooling — Why3's backends, EYE, Vampire — can be
pointed at the tail. This is the same shape as the handoff's Why3
position: an untrusted producer that finds something, and a small
checker that verifies it.

It is a real benefit. Writing an IKL prover is not on the roadmap;
reusing first-order provers is close to free.

### Where it does NOT help, and the trap

**The reduction is satisfiability-preserving, not
equivalence-preserving.** Our own ABI already says so: `clNormalize`
reports `preserves: "satisfiability"`, deliberately not "equivalence".

That single fact rules out the tempting use. You cannot justify a step
"C follows from P" by normalising P and C separately and reasoning about
the results. Satisfiability preservation is a property of a SET, not a
licence to substitute inside a derivation.

The sound use is refutation-shaped and whole-set:

    normalise (P union {not C}) -> tail T
    T unsatisfiable  =>  P entails C

Three costs come with it, none of which should be hidden:

1. **The normalisation becomes a first-class node.** Per the adopted
   invariant, every semantics-changing translation is a visible step
   with a named profile and version. A chain that silently normalised
   would be misreporting where its formal certainty comes from.
2. **The side condition travels with it.** `tails_satisfiable` is proved
   for the no-intrusion fragment, decided by `CL.noIntrSs`. The general
   case is not proved, and Hayes's own conjecture that tail sentences
   cannot be CL-inconsistent is stated in the 2009 paper as unproved:
   "We have not found any such example, and believe that it is
   impossible, but do not at the time of writing have a conclusive
   proof." A certificate must carry the decided condition, not assume
   it.
3. **The foundational core moves.** After reduction, what needs checking
   is a first-order refutation, so the trusted checker is a first-order
   proof checker (resolution or LRAT shaped), not an IKL one. That is a
   larger build than IKLbase, not a smaller one.

### The ruling this respects

Owner, 2026-08-26: "don't try checking or forcing the Hayes path on
consumers." Nothing here changes that. The reduction is available to a
caller who asks for it and to a proof-search backend that wants it. It
is not in the consumer path, not in the checker, and not a prerequisite
for any certificate.

## 4. What this settles for the build order

1. **IKLbase calculus first.** Small, directly checkable, sound against
   `CL/IklModels.lean`. This is the M2 adapter that demonstrates the
   difference between proof search and proof checking.
2. **Hayes + a first-order backend later**, alongside the Why3
   experiment at M4, as an untrusted producer. Its output is either a
   certificate in a first-order calculus we can check, or an R-level
   replay record — never an unexamined "the prover said yes".
3. **No completeness claims** for either.

## 5. Open, for the owner

The IKLbase rule set is ours to choose, and the choice is not obvious.
A minimal set that supports the worked squirrel/policy examples is a
different set from one aimed at general IKL reasoning. Proposal: start
from the rules the existing examples actually need, add only on demand,
and record each rule with the example that forced it. That keeps the
calculus small and keeps every rule paid for by a use.
