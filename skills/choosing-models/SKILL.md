---
name: choosing-models
description: How to pick the model (and effort) for every subagent you spawn — especially when the orchestrating session runs on a Fable-class (top-tier) model. Core rule, from the owner: "For all coding tasks use your judgement to decide an appropriate lower power model and run that in a subagent." Use whenever dispatching an Agent, planning a fan-out, writing a Workflow, or when a session is burning top-tier tokens on work a cheaper model executes reliably.
---

# Choosing models for agents

**The owner's core rule: "For all coding tasks use your judgement to
decide an appropriate lower power model and run that in a
subagent."** A Fable-class session is the most expensive reasoning in
the fleet; its job is judgement — decomposition, diagnosis, spec
design, gate decisions, and writing the precise briefs that make
cheaper models reliable. Execution belongs downstream.

## The division of labour

- **Top tier (the orchestrating session itself)** keeps: root-cause
  analysis, F\* proof strategy and fix *design*, adversarial review of
  agent output, gate/commit decisions, anything requiring the whole
  session's context.
- **Everything that is "write/change code to a known plan" goes to a
  subagent on a lower-power model.** The intelligence is spent
  writing the brief (anti-pattern #24: ship code sketches, exact
  file:line, signatures, gate commands, expected scores) — a mid-tier
  model executing a precise sketch outperforms a top-tier model
  executing a vague one, at a fraction of the cost.

## Tier guidance

| Task shape | Model choice |
|---|---|
| Mechanical fan-out: greps, inventories, doc-table refreshes, log triage, file moves | smallest available (e.g. `haiku`), low effort |
| Coding to a sketch: implement a specified rule/function, wire a build list, write a regression script from a stated pattern, JS/consumer code | mid tier (e.g. `sonnet`) — the default for coding tasks per the core rule |
| Coding where the plan may need local judgement (API shaping, refactors with taste, multi-file features) | mid tier first; escalate only after a failed attempt shows the brief wasn't the problem |
| F\* proof debugging, spec-level design, adversarial verification of a claimed fix, root-cause on soundness bugs | inherit the session model (omit the override) |
| Research/lit-review with synthesis | inherit; effort high |

Session inheritance note: OMITTING the model override makes the agent
inherit the session's model — on a Fable-class session that means
top-tier cost. So for coding tasks the override is not optional
polish; forgetting it is the expensive default. Decide explicitly,
every dispatch.

## Judgement heuristics (the "use your judgement" part)

- **Brief quality substitutes for model power.** If you can state the
  diff you want (files, functions, signatures, gates), drop a tier.
  If you're asking the agent to *discover* what to change, don't.
- **Verification-gated work is safe to delegate down**: F\*'s checker,
  the suites, and the parity harness catch a weaker model's mistakes
  mechanically — the gates, not the model, carry correctness. Ungated
  prose/design output has no such net; keep it up-tier or review it
  yourself.
- **Retry escalation, not retry repetition**: if a lower-tier agent
  fails twice on a good brief, escalate the model once rather than
  re-rolling; if the brief was bad, fix the brief first.
- **Effort is a second dial**: `effort: low` for mechanical work even
  on mid-tier; high effort reserved for the hardest verify/judge
  stages.

## What this skill does NOT cover

- Prompt structure for agents — `subagent-prompting`.
- When to fan out at all, token prudence — `session-economy`.
- Wall-clock discipline for long agent runs —
  `autonomous-time-discipline`.
