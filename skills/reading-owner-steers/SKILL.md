---
name: reading-owner-steers
description: How to read, record and act on the owner's instructions in this repository. Use when an owner message changes priority or scope, when you write an owner decision into a ledger, design doc or skill, when a document says "owner excluded" or "deprioritized", or when you are about to act on an instruction more than a few weeks old.
---

# Reading owner steers

The owner usually writes from a phone, between other work, and reads a
fast stream of agent output with no tool to bookmark or cross-reference
it. An instruction written under those conditions is a priority call on
a partial view. The owner has said that such calls are sometimes wrong.
Protocol work is the most likely case: a format test is files in,
triples out, but a protocol test needs a simulated or live endpoint, so
a quick scope judgement about it is easier to get wrong.

## Rules

1. "X deprioritized" sets an order. It does not remove X from scope.
   Do not let a document that inherits the steer turn it into "out of
   scope by owner directive".
   Record: a 2026-07-11 "protocols deprioritized" became, three
   documents later, "owner-excluded" labels on specific CSVW tests. The
   owner never made that call (2026-07-15 correction in the CSVW triage
   ledger). The owner's account, 2026-08-22, verbatim: "Protocols were
   not deprioritised but we needed basic sparql first - and early f\*
   was glacially slow at points where io bridged the non f\* universe."
   Both the original label and an earlier gloss in CLAUDE.md were wrong.
   The steer was a sequencing constraint plus an I/O performance
   problem.
2. Quote a steer with its date and its original words when you write
   it into a ledger or design doc. A paraphrase drifts, and each copy
   drifts further.
3. Do not invent a rationale and attribute it to the owner. Say who
   decided, or label the text as a Claude-inferred default. `git blame`
   cannot settle this, because every commit carries the owner's
   identity (iron rule 13). Only the prose can carry provenance.
   Record: 2026-08-22, a Claude-written skill bullet said the Lean
   tree's plain evaluator split was "absolute — never port performance
   machinery here", under an "owner priority" heading. It became "must
   stay that way" in a design doc, then a chat claim that the owner
   considered indexed joins destructive. Owner: "BS, I never said
   this." The question of indexed joins plus a refinement proof in the
   Lean tree was recorded as closed for a day. Corrected in
   `skills/factoidal-lean-basics`.
4. Before you record an implication with large effect ("owner excluded
   N tests", a suite dropped from a goal), ask the owner one short
   question first.
5. Write for a phone. Lead with the result or the decision needed. Keep
   it short. Label every score. No session-local names.
6. Work tracking lives in GitHub issues, not session state. Owner,
   2026-08-11, verbatim: "This is unacceptably shit for ios app users -
   you spew thousands of lines of blabber at us with no tooling to
   organize it. Use github properly." Every workstream has an issue.
   The index is https://github.com/danbri/factoidal/issues/404; update
   it at every harvest. Reports link issues; they do not restate them.
   Details: `skills/issue-management`.
7. Re-check an old steer before you act on it. "Protocols
   deprioritized" predates SPARQL Protocol at 56 pass, 0 fail (34
   protocol, 19 graph store, 3 service description, both trees).
8. There are no users. Backwards compatibility, blast radius and
   migration cost are not arguments in this repository. When a design
   is wrong, change it, and keep the old artifact only as the record of
   why. Record: 2026-08-26, the coordinator recommended the
   conservative option for item 3 of
   https://github.com/danbri/factoidal/issues/609 on blast-radius
   grounds. The owner overruled it: "The correct path is (3.)".
9. Emoji in owner messages are markers, not tone. The palette for our
   output is in `skills/markdown-style`.
