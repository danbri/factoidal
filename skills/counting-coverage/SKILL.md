---
name: counting-coverage
description: How to count what a port or a migration has covered, without the count lying. Use before you write a coverage number in a report, before you add a name to an alias table, and whenever a coverage number moves and you cannot say which commit moved it. The rules are short; each one names the wrong number that paid for it.
---

# Counting coverage without lying

A coverage tool answers one question: which items on side A have a
counterpart on side B? The answer is easy to get wrong in a way that
looks right. This skill lists the ways, and the check that stops each
one.

## The one rule

**A name is a hint. Coverage is a decision.**

Two files whose names look alike are a reason to go and look. They are
never, on their own, a reason to mark an item covered.

## Rule 1 — never match on the last name part alone

Match on the FULL name, or on at least the last TWO parts, or on an
entry you wrote by hand in an alias table. Never on the last part.

Why. `HDT/Store.lean` was added. `SPARQL11.Store` — 1,452 F* lines,
with no Lean counterpart at all — disappeared from the not-covered
list, because both names end in `Store`. The tool then reported five
more items as covered that were not. Nobody had touched them. Nobody
had written a line of the missing code.

Do this instead:

```python
# WRONG: one shared word decides it
if fstar_module.split(".")[-1] == lean_module.split(".")[-1]: covered()

# RIGHT: the full name, or two parts, or an explicit alias
if fstar_module in ALIASES: covered(ALIASES[fstar_module])
elif last_two(fstar_module) == last_two(lean_module): covered()
```

## Rule 2 — a count that moves with no cause is a bug report, and so
is a count that does not move when it should

If the number changes and you cannot name the commit that changed it,
stop and find out why. Do not write the new number down.

The converse is the same rule. If you landed a port and the number did
NOT move, that is a bug report too.

Why, both directions:

- The `Store` collision above showed up as a jump: the count rose after
  a commit that added an unrelated file. The jump was the whole
  warning, and it was easy to read as progress.
- A ported module was verified, building, and aliased — and the count
  stayed put. A `git stash` / `git stash pop` cycle between two
  measurements had dropped the edit to the tool. The Lean file was on
  disk; the tool had never heard of it. Nothing on screen looked wrong,
  because the unchanged number was the correct figure for the state
  BEFORE the landing.

So: after ANY alias edit, `grep` the tool for the entry you just added,
before you read the tool's output. One command, and it is the only
check that sees this failure.

Ask, every time the number moves:

- Which item changed state?
- Which commit changed it?
- Does that commit contain the work that item needs?

Three answers, or the number is not ready to publish.

## Rule 3 — read the file, do not count the hit

When you search for a name and find it, OPEN the file and read the
sentence around the hit. A mention is not a port.

Why, both directions:

- Four items were listed as NOT covered although their Lean files say,
  in the first line of their own header, which F* module they port.
  A name search found them; nobody read the hits.
- Three other hits were prose references, not ports. One Lean file
  names an F* module under a heading that says "what is NOT proved".
  Counting that hit would have claimed a proof that does not exist.

The same check catches both. It costs one minute per item.

## Rule 4 — an alias table cannot report its own gaps

A hand-written alias table is a list of things somebody remembered.
It says nothing about what they forgot. If a miss falls through to a
guess, the tool cannot tell you it is broken.

So: make a miss LOUD. If an alias points at a module that does not
exist, print it and exit non-zero. Two aliases in this repo pointed at
Lean modules that had never been written, and the tool stayed quiet
because the fall-through heuristic matched something else.

## Rule 5 — derive the inputs on every run

Walk the tree each time. Never read a file list from a cache, a
scratch file, or a previous run's output.

Why. A tool read its module list from a session scratchpad. It reported
a module as not covered a few minutes after that module's file landed.
On a fresh machine the same tool would have crashed, because the
scratch file was not there.

Fail loudly on an empty walk. An empty list is a broken tool, not a
finished job.

## Rule 6 — covered means the RESULT is carried, not the file exists

Ask: does the new file carry what the old one carried?

If it carries half, it is not covered. Write the half down, say what is
missing, and leave the item on the not-covered list.

Why. `RDF.NTriples.RoundTrip` got a Lean file with the same subject and
half the content — serialiser injectivity, but no round-trip theorem.
Aliasing it would have moved the count by one and made the count mean
less. It stayed on the not-covered list, with the missing half named
in an issue.

## Rule 6b — an alias covers a module, and a module is not one result

An alias says "this F* module has a Lean counterpart". It does not say
every definition in it arrived. On a large module, expect the alias to
cover the PRINCIPAL result and expect individual functions to be
missing.

Why. `SPARQL11.Algebra` is aliased and counts as covered.
`strip_rewrite_internal_vars` and its two helpers were not in the Lean
tree at all — and CLAUDE.md names that function as load-bearing, with a
constraint on where it may be applied.

The check that found it was not a tool. It was reading the project's
own list of results that matter and looking each one up. So:

**Audit against the results the project has written down as
load-bearing, not against definition names.** CLAUDE.md's rules,
`docs/theorem-registry.md`, and the findings sections of module headers
are that list.

## Rule 6c — do not try to measure this by comparing names

A tool that compares F* definition names against Lean definition names
cannot answer "how much of this module arrived", and no percentage it
prints will mean that.

Why, measured 2026-08-24. `tools/lean-port-depth.py` was written to do
exactly this. Its first version reported 73% of definitions missing,
with several fully ported modules at 100%. Two rounds of correcting the
normalisation — stripping F* domain prefixes that Lean drops under
namespaces, then searching the whole tree instead of one module — moved
it to 62% and left the same modules at 100%.

The cause is not fixable by better normalisation. The two trees share
almost no internal vocabulary, because the Lean side was written
against the W3C text rather than translated. F* has
`rho_df_closure_iter` and `lemma_dedup_pairs_memP`; Lean has
`Derives.cut` and `mem_addOne_of_mem`. Same results, different proof
architecture. A name comparison cannot tell that apart from an absence.

That difference is the point of having two trees, so the tool is
measuring the method working and calling it a deficit. It is kept as a
READING LIST — which covered module to open first — and it now refuses
to print a coverage percentage.

## Rule 6d — join the two sides on SPECIFICATION vocabulary

When implementation names cannot be compared (rule 6c), look for names
the specification fixes. Those are the same on both sides by
obligation, whatever each tree calls its own lemmas.

Why it works here. W3C OWL 2 RL rule ids — `cax-sco`, `prp-spo1`,
`eq-ref` — are fixed by the Recommendation. `docs/theorem-registry.md`
lists every one with its proof status. Matching those ids against Lean
theorem names answers a real question where the definition-name
comparison answered none: `tools/lean-registry-audit.py`, 2026-08-24,
51 rule ids, 45 named by a Lean theorem, 6 absent and every one of the
six recorded by the registry as unproved on the F\* side too. Zero
gaps, and the six are listed individually with the registry's own
words rather than excluded in bulk — a blanket exclusion would hide a
regression.

Two traps this run hit, both worth repeating:

- The first id regex matched `dt-branch`, which is a git branch name in
  the registry prose, not a rule id. It inflated the denominator by
  one. Constrain the pattern to what the Recommendation spells.
- A rule id appearing anywhere in the Lean tree is a HIT, not a result.
  The first count said "51 of 52 found" from plain text search;
  requiring the id to appear in a THEOREM name moved it to 45, and
  that second number is the one that means something.

The tool locates theorems. It does not review them: a theorem with the
right name and a weaker statement still counts. Say so next to the
number.

## Rule 6e — the residue tells you whether it is really covered

When a Lean module carries most of an F\* module's results, look at what
is LEFT OVER and ask which kind it is.

**Representation residue** — the F\*-only lemmas exist because F\*
represents a value differently. `RDF.NTriples.RoundTrip`'s dozen
leftovers are UTF-8 byte walking, because `FStar.String` is byte-indexed
and `List Char` is not. Same computation, different encoding. That is
covered.

**Engine residue** — the F\*-only content is a different program.
`RDF.Entailment.RDFS.Refinement`'s twelve licensing lemmas are stated
over an INDEXED GRAPH (`ig_wf_pred`, `bucket_lookup ig.ig_pred`); the
Lean lemmas that map onto them one for one are stated over a plain list
graph. Both prove "the engine emits only licensed triples", of different
engines. That is NOT covered, whatever the name mapping looks like.

The two are easy to confuse because both leave the headline results
matching. Ask what a reader would be told: "the Lean tree proves this"
is true in the first case and misleading in the second.

## Rule 6f — write down the pull, not only the answer

When you decline to alias, record what made aliasing attractive.

Why. On 2026-08-24 the count had just moved 192 to 193, the twelve-row
mapping for `RDF.Entailment.RDFS.Refinement` was one-to-one, and
aliasing would have made it 194. The reasoning against is a judgement
someone has to trust, so it went into
`docs/designissues/2026-08-23-lean-port-gap.md` as the eleventh
correction — with the pressure named. A decision recorded without its
temptation reads as obvious later, and the next person under the same
pressure gets no help from it.

## Rule 7 — an audit that finds nothing tells you about the audit first

When a check comes back clean, write down HOW you checked, next to the
result. Then ask whether that method could have seen the failure you
were looking for.

Why. A name-based audit reported "no other item is wrongly listed".
The method could not see a rename, and could not see one new file
covering two old ones. Both were present. Four items and 1,298 lines
were already covered; the audit's silence about exactly those cases was
read as coverage.

## Rule 8 — a prefix is not an identifier

Compare WHOLE identifiers. A matcher that stops at the first
non-word character reports gaps that do not exist and hides gaps that
do. When the identifiers come from a specification, keep the
specification's own list in the tool and report every token that is
not on it, rather than excluding a bad token by name.

Why (2026-09-03). `tools/lean-registry-audit.py` read OWL 2 RL rule
ids out of `docs/theorem-registry.md` with `\b(cax|prp|cls|eq|scm|dt)-…\b`.
`\b` ends a match at a `-`, because `-` is a non-word character. Three
consequences, all in one tool:

1. `dt-rng-intersect` — a local rule-family name, not a rule — read as
   the id `dt-rng`, which no Lean theorem names. The tool reported it
   as a real gap, and the gap went into an audit document as a finding.
2. `eq-rep-s`, `eq-rep-p` and `eq-rep-o` — three separate rules — all
   read as one id `eq-rep`. Three rules were counted as one, and the
   one hit any theorem name containing `eqRep`. That is the same defect
   pointing the other way: it HID two rules instead of inventing one.
   Five more non-rules (`cax-eqc`, `cls-int`, `prp-eqp`, `prp-inv`,
   `prp-rfl`) entered the same way.
3. An earlier session had patched the symptom by excluding the string
   `dt-branch` (a git branch name) BY NAME. A name-specific exclusion
   cannot report its own omissions — rule 4 — so the next bad token
   arrived unannounced.

Cost: the reported figure was 56 rule ids, 50 named by a Lean theorem,
1 real gap. The measured figure is **52 rule ids, 47 named by a Lean
theorem, 5 absent by agreement with the F\* side, 0 real gaps**. The
tool now reads whole hyphenated tokens, keeps only the 78 rule ids the
OWL 2 Profiles Recommendation defines, PRINTS the tokens it dropped,
and matches a Lean theorem by its camel/snake segments rather than by
substring.

## Rule 9 — two runners over one specification must each say what they cover

When two tools score the same specification and disagree, the
disagreement is a question about SELECTION before it is a question
about correctness. Find which files each one opened. Then make both
names and both report lines say what each covers, so the next reader
does not read the difference as a regression.

Why (2026-09-03). `l4w3c` scored RDF 1.1 at 1031 pass, 0 fail (out of
1031), of which rdf-xml is 166 pass, 0 fail (out of 166).
`l4rdfxml-probe` scored 130 pass, 2 fail (out of 132) on the same
directory. An audit recorded that one of the two numbers had to be
wrong about RDF/XML and could not say which.

Neither was wrong, and neither counted a skip as a pass. `l4w3c` reads
`manifest.ttl`. `l4rdfxml-probe` walks the DIRECTORY on purpose, so
that it can measure the RDF/XML parser without also depending on the
Turtle parser to read the manifest — its own header says so. The
rdf-xml suite has 173 `.rdf` files on disk and 166 manifest entries:
upstream comments out 7, and the 2 the probe fails
(`rdfms-xml-literal-namespaces/test001` and `test002`) are two of the
7. The withdrawn entries' own comment gives the reason — treatment of
namespaces that are not visibly used in an XML literal "is
implementation dependent".

So: 1031 pass, 0 fail (out of 1031) is the conformance number.
130 pass, 2 fail (out of 132) is a parser probe over the directory,
including entries the Recommendation's own suite withdrew. Both are
true; only the labels were missing.

## The checklist before you publish a number

1. Did the tool walk the tree this run?
2. Does any match rest on one shared name part?
3. Did the number move? Can you name the commit? If it did not move,
   can you say why not?
4. Is the alias you just added actually in the tool? (`grep` it.)
5. Did every alias resolve to a file that exists?
6. For each newly covered item, did you read the file?
7. For each newly covered item, does it carry the whole result?
8. If the number came from comparing names, can it tell a rename from
   an absence? (Usually it cannot — see rule 6c.)
9. Does every match compare a WHOLE identifier, not a prefix? (Rule 8.)
10. If another tool scores the same specification, do the two numbers
    agree; and if they do not, can you name the files each one opened?
    (Rule 9.)
11. Can you state the method next to the number?

Eleven yes answers, then publish.

## Related

- `skills/workflow-gotchas-debugging/SKILL.md` — hazards #28, #30 and
  #31 hold the long form of rules 7, 5 and 1.
- `docs/designissues/2026-08-23-lean-port-gap.md` — the running record
  of every time this count was wrong, and what the wrong method was.
