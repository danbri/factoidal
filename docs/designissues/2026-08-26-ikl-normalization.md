# IKL normalization in Lean 4 — the algorithm, what is proved, what is not

**Date**: 2026-08-26 · **Tree**: `formal/lean4`, library `L4Factoidal` ·
**Tracking**: [#580](https://github.com/danbri/factoidal/issues/580)

**Source**: Pat Hayes, *A Satisfiability-Preserving Reduction of IKL to
Common Logic*, Florida IHMC, 2009 —
<https://jfsowa.com/ikl/PHnsfs09.pdf> (fetched 2026-08-26). Section
references below are to that paper.

## 1. What the transformation is for

IKL extends Common Logic with one construct: `(that <sentence>)`, a
term naming the proposition a sentence expresses, constrained
semantically so that predicating that term on the EMPTY argument
sequence has the same truth value as the sentence
(`CL.Semantics.IklRespectsThat`). Normalization removes every such
term, so a first-order CL engine can decide IKL satisfiability and
entailment. Hayes calls it "an essential basic step towards
implementing an IKL reasoning engine".

The output is a text of one HEAD sentence plus a set of TAIL
sentences. Each eliminated `(that S)` occurrence contributes one fresh
name `K`, a replacement term, and one tail

    (forall (U1 ... Un) (iff ((K U1 ... Un)) S'))

where `U1 ... Un` are the INTRUSIONS — the names free in `S` that a
quantifier outside the occurrence binds — and `S'` is `S` with its own
`that`-terms already eliminated. With no intrusions the replacement
term is the bare name `K` and the tail is `(iff ((K)) S')`, which is
the paper's base case. `((K ...))` is the cancelling-parentheses form;
its IKL reading is `CL.Semantics.sat_assert_that`.

## 2. Files

| File | Contents |
| --- | --- |
| [`formal/lean4/L4Factoidal/CL/Normalize.lean`](../../formal/lean4/L4Factoidal/CL/Normalize.lean) | free names / free markers, the `thatWeight` measure, the traversal, the four paradox pins, the purity theorems, and the decidable side conditions (`allNames*`, `noIntr*`, `assign*`) |
| [`formal/lean4/L4Factoidal/CL/IklModels.lean`](../../formal/lean4/L4Factoidal/CL/IklModels.lean) | `pSat`, the coherent interpretation `iklProp`, the free-name coincidence group, `IklPropLocal` |
| [`formal/lean4/L4Factoidal/CL/NormalizeSemantics.lean`](../../formal/lean4/L4Factoidal/CL/NormalizeSemantics.lean) | the head and tail inductions, `normalize_preserves`, `ikl_sat_to_cl_sat`, `tails_satisfiable`, and the four paradoxes semantically |

## 3. Termination — the argument Hayes leaves out

The paper states the algorithm as a loop:

```
TAIL := nil
NORMAL(E) :=
       E := Skolemize(E);
       UNTIL E contains no proposition names DO(
              Let P = (that S) be a proposition name in E;
              Let U1,.., Un = the intrusions in P;
              K := gensym( );
              E := substitute (K U1 ... Un) for P in E ;
              TAIL:= TAIL +
                     NORMAL( (forall (U1 ... Un)(iff ((K U1 ... Un)) S )) ) ;
       )
       RETURN( E + TAIL );
```

and says only that "an obvious inductive argument shows that this
process of normalization must terminate with a CL text". Lean will not
accept a `partial def`, so the argument has to be supplied.

**The loop form does need a measure, and the obvious one does not
work.** Counting proposition names does not decrease: eliminating an
OUTERMOST `that` moves the proposition names nested inside it out of
`E` and into a tail sentence. Eliminating the outer `that` of
`(that (K (that (not (D)))))` leaves `(that (not (D)))` in the tail,
and the count is unchanged.

`Sentence.thatWeight` is a measure that does work: each occurrence
weighted by two raised to the number of `that`s enclosing it, written
as the recurrence `w (that S) = 1 + 2 * w S`. A loop step replaces a
term of weight `1 + 2 * w S` by a term of weight 0 and emits a tail of
weight `w S`, so the text's weight falls by at least `1 + w S`.
`thatWeight_that` is that inequality.

**The implementation here needs no measure at all.** `normSent` is a
single traversal whose only recursive calls are on strict subterms —
the body of a `that` is a subsentence — so Lean accepts the whole
mutual group by STRUCTURAL recursion: no `partial`, no
`termination_by`, no `decreasing_by`. Structural recursion is a
stronger termination result than a well-founded measure, and it is
checked by the kernel rather than argued in prose.

The traversal visits outermost `that`s first and recurses into the
body immediately, which reproduces the paper's `gensym` numbering
exactly. The Knower's outer proposition name comes out `prop4` and the
one nested inside it `prop5`, as the paper prints them.

The other half of "terminates with a CL text" is
`normalizeFrom_pureCL`: the head and every tail satisfy
`Sentence.isPureCL`, so no proposition name survives. That half holds
for every input, intrusions or not.

## 4. Three departures from the paper

### 4.1 Per-occurrence naming

The paper's step substitutes one fresh name for EVERY occurrence of
one proposition name at once ("substitute `(K U1 ... Un)` for P in
E"). That is not well defined in general: two syntactically equal
`that`-terms under different quantifiers have different intrusion
sets, so there is no single `(K U1 ... Un)` to substitute. The
traversal gives each OCCURRENCE its own fresh name. No paradox in the
paper has a repeated proposition name, so the pins are unaffected.

### 4.2 No Skolemization

The paper Skolemizes `E` before the mapping so that every intrusion is
universal, and re-Skolemizes each tail because the biconditional
exposes a quantifier; it notes the resulting patterns "can become
quite complex". This implementation does not Skolemize.

It does not need to. The tail `(forall (U) (iff ((K U)) S'))` holds in
the constructed model whichever quantifier bound `U`, because the
functional extension given to `K` is TOTAL: it sends every argument
tuple to the proposition the body denotes at that tuple, and the
tail's universal quantifier ranges over exactly those tuples. The
Skolemization step is a step of the paper's presentation, not a step
of the satisfiability-preservation argument.

The visible consequence is on the paper's second quantifier-intrusion
example. Hayes prints `(forall ((x Human))(FredBelieves (prop1 x)))`
with tail `(forall (x)(iff ((prop1 x)) (hasFather x (sk1 x))))`,
because Skolemization replaced `y` by `(sk1 x)` before the mapping.
Here `y` is still existentially bound, so it intrudes as well and the
output is `(prop1 x y)` with tail
`(forall (x y) (iff ((prop1 x y)) (hasFather x y)))`. Both are pinned
in `Normalize.lean`.

### 4.3 Intrusion is enclosing-bound INTERSECT free-in-body

The paper defines an intrusion as a name in the proposition name that
a quantifier outside it binds. Kripke's paradox is the case that
forces the intersection with the body's free names: the `that` sits
inside `(forall (x) ...)`, `x` does not occur in the body, and the
paper's own printed output is `prop3` with no argument. Taking all
enclosing bound names instead would print `(prop3 x)`.

## 5. What is proved

All statements are in `L4Factoidal`, with no `sorry`, no user `axiom`,
no `partial` and no `native_decide`. In-source `#print axioms` on
every gate theorem reports `propext`, `Classical.choice`, `Quot.sound`
only.

### 5.1 Unconditional

* `normalizeFrom_pureCL` — head and every tail are ISO/IEC 24707 CL.
* `iklProp_respects` / `exists_ikl_interp` — a coherent IKL
  interpretation exists. Before this, `IklRespectsThat` was a
  condition with no model behind it in `CL/`, and every theorem
  quantified over coherent interpretations was empty.
* `iklProp_local` — that interpretation is LOCAL: the proposition a
  sentence expresses depends only on what its free names and free
  sequence markers denote (`IklPropLocal`).
* The four paradox pins in `Normalize.lean`, matching the paper
  verbatim including its `gensym` numbering, with the Knower's
  iteration count pinned at 2.

### 5.2 Under three decidable side conditions

The conditions are: `noIntrusion E` (no quantifier intrudes into a
proposition name); no name of `E` lies in the fresh-name space; and
the allocation list has distinct keys.

* `normalize_preserves` — for a coherent, local interpretation, the
  head read under the constructed valuation has the truth value the
  original sentence has, AND every tail holds under that valuation.
* `ikl_sat_to_cl_sat` — an IKL-satisfiable sentence has a
  CL-satisfiable normalization.
* `tails_satisfiable` — see §6.

### 5.3 The four paradoxes, semantically

`tnit_cl_unsat`, `liar_cl_unsat`, `kripke_cl_unsat`: the normalized
texts of That Nothing Is True, the Liar and Kripke's sentence are
CL-unsatisfiable, so by `ikl_sat_to_cl_sat` none of the three has a
coherent IKL model (`tnit_not_ikl_sat`, `liar_not_ikl_sat`,
`kripke_not_ikl_sat`). The Knower's fourth sentence taken ALONE is
satisfiable and `knower_cl_sat` exhibits a model; the paradox needs
the other three Knower sentences, which carry no proposition name.

## 6. Hayes's open conjecture

The paper, §"IKL Satisfiability and Entailment", verbatim:

> if the tail sentences are inconsistent in CL, then the semantic
> argument given would lead to the conclusion that the IKL semantic
> conditions cannot be satsified by any IKL interpretation of the IKL
> sentence, i.e. that the IKL sentence in this case has no
> interpretation at all. We have not found any such example, and
> believe that it is impossible, but do not at the time of writing
> have a conclusive proof.

**Result**: `tails_satisfiable` — for every sentence in the
no-intrusion fragment, the tail set is CL-satisfiable. The tail set is
never inconsistent, so the situation Hayes describes does not arise
there.

**Why it comes out.** The tail induction `normS_tails` never uses a
premise that the original sentence is satisfied. Its hypotheses are
about the valuation, not about `E`'s truth. So a model of the tail set
can be built from ANY coherent, local IKL interpretation, and
`iklProp` is one — which is the point of building it. Hayes's own
semantic argument reads as being about an interpretation of the
sentence; the observation that makes it a proof is that the
construction is indifferent to whether the sentence holds.

**Non-vacuity.** For the Liar, `liar_cl_unsat` and `liar_tails_sat`
sit side by side: the whole normalized text is CL-unsatisfiable and
its tail set is CL-satisfiable. The conjecture is not being confirmed
by a theorem that would confirm anything.

**Where it stops.** The intrusion case is not covered. See §7.1.

## 7. What is not proved

### 7.1 The intrusion case

When the intrusion list is non-empty the replacement term is
`(K U1 ... Un)`, and the model has to give the individual `K` denotes
a non-trivial FUNCTIONAL extension — one sending each argument tuple
to a different proposition. `iklProp` cannot: its universe is `Prop`
with `fn x args := x`, so the functional extension of every individual
is constant and `((K U))` denotes the same thing for every `U`.

The obstruction is not a gap in the argument but a missing
construction. A universe `D` with a surjection onto `List D → Prop` is
impossible by cardinality, so the intrusion case needs a universe
built to carry exactly the finitely many functional extensions the
tails require — a term model, or a two-stage construction that adds
the fresh individuals after fixing the base interpretation. Both the
head and the tail inductions already carry the intrusion lists
through; only the model construction is missing.

### 7.2 The converse direction

From a CL model of head-plus-tails back to an IKL model of the
original sentence. Two obstructions, both concrete:

1. Coherence forces a model to contain an individual whose zero-ary
   relation extension is empty and one whose is not — otherwise a
   sentence and its negation would both hold. A CL model of
   head-plus-tails need not contain either.
2. A `that`-term can occur in an EQUATION — the Liar,
   `(= p (that (not (p))))`, does. So the converse construction cannot
   define `iProp` to return a truth-value individual; it has to return
   the very individual the fresh name denotes, which means `iProp` has
   to be keyed by the sentence.

### 7.3 Injectivity of `propName`

`propName k = "prop" ++ toString k` is injective, and injectivity is
what makes the allocation list's keys distinct. The proof needs
injectivity of `Nat.repr`, which this toolchain's core library does
not carry (`exact?` finds nothing for
`toString a = toString b → a = b`, nor for
`(toString a).toNat? = some a`). Key-distinctness therefore stays a
hypothesis of the general theorems. It is decidable for any concrete
sentence, and the four paradox instances discharge it by `decide`, so
those results carry no such hypothesis.

## 8. Duplication to resolve

`Unified/ClBridge.lean` landed a `propModel` on 2026-08-26 — the same
construction, parameterised by `iN iS R F`, with coherence under
`∀ p, R p [] ↔ p`. `CL/IklModels.lean`'s `iklProp` is the instance
`R := fun x _ => x`, `F := fun x _ => x`, and it adds the locality
theorem, which `ClBridge` does not have.

The dependency runs `Unified` → `CL`, so `CL/IklModels.lean` cannot
import `ClBridge`. The right structure is the reverse of the current
one: the `pSat` construction belongs in `CL/`, and `Unified/ClBridge`
should import it and delete its copy. That move was not made here
because `Unified/` was another agent's working set on the same day.
