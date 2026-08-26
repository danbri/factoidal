---
name: issue-management
description: How to report status, plan work, and manage issue state in this repository. Use WHENEVER reporting on project status, progress, work done, or work to do — status reports, "what's next" answers, harvest summaries, plan lists, TODO lists, backlog discussion, issue creation, issue closure, and any message that cites an issue or piece of tracked work. Three rules with teeth. (1) GitHub issues are the only durable work record — session-relative references are forbidden EVERYWHERE, chat messages to the owner included; these conversations run longer than some novels, so a label defined "earlier" is a pointer guaranteed to dangle — every mention of tracked work carries its full GitHub URL, every time. (2) Every issue reference is a full clickable GitHub URL — bare #NNN renders as dead text in every markdown file. (3) Reports are written in technical Simple English, with a named list of banned filler phrases that erode reader trust. Pairs with issue-hygiene (the periodic sweep mechanics) and markdown-style (links + the no-sycophancy list).
---

# Issue management: status, references, and register

Owner directive, 2026-08-18. This skill exists because three failures
kept recurring, each found by audit:

- 2026-08-11, owner, verbatim: "This is unacceptably shit for ios app
  users - you spew thousands of lines of blabber at us with no tooling
  to organize it. Use github properly."
- 2026-08-18: 166 bare `#NNN` references in committed markdown files
  resolved to nothing. GitHub auto-links issue numbers only in issue
  bodies, pull-request bodies, and commit messages — never in a
  rendered `.md` file. Every reference the owner tried to tap on a
  phone was dead text.
- 2026-08-18: an audit of all 117 open issues found five that were
  fixed but still open, because closing the issue was treated as a
  separate chore after the merge instead of part of it.

## Rule 1 — GitHub is the only memory. No exceptions, chat included.

A work item exists when it has a GitHub issue with a human-readable
title. Nothing else counts as tracking: not a session task list, not a
plan in a chat message, not a checklist in a scratch file.

**Session-relative references are forbidden EVERYWHERE — including in
messages to the owner inside the conversation itself.** These
conversations run longer than some novels. A label defined "earlier"
is unrecoverable the moment it scrolls; nobody, owner included, can
find message 300 of 900 on a phone. Assume every message is read by
someone with NOTHING else: no scrollback, no memory of yesterday, no
this-session context. A session reference is a pointer that is
guaranteed to dangle — if not today, then for whoever reads the issue,
the commit, or the transcript next month.

The forbidden forms, with no "but the reader was just told" defense:

- Session-local labels: "task #53", "wave 2 module 3", "gap 1",
  "SR-4", "G4", "arm B", "the delete half", "the agent's branch",
  "the earlier fix". If the work matters, it has an issue; write the
  issue's full URL. Every time. Repetition of URLs is a feature, not
  clutter — a phone reader lands mid-scroll.
- Shorthands defined earlier in the same conversation. "Earlier" does
  not exist for the reader. If a report genuinely needs a shorthand,
  define it in the ISSUE BODY, then link the issue at every use.
- New project code names. The decoder for the old ones is
  [docs/code-name-glossary.md](../../docs/code-name-glossary.md);
  the standing rule there is "no new short-codes". Use descriptive
  names.
- Referring to a finding, decision, or plan that exists only in chat.
  Write it into the relevant issue first, then point at it. A decision
  that lives only in a conversation was never made, as far as the
  project record is concerned.

**The test for every outgoing message:** could a person who has read
NOTHING but this one message act on it — follow every reference, find
every piece of work, verify every claim? If any noun in it requires
scrollback to resolve, replace that noun with a full GitHub URL.

**Before opening a workstream, search the ISSUES for it — the
checkout is not the record, GitHub is.** A fresh clone, a worktree, or
a container that has not fetched for an hour can be blind to work
another session already landed; GitHub issue search is not. Before
creating a tracking issue, a new top-level directory, or a "first
deliverable" of anything, run an issue search on the topic's plain
name (not just the word the request used). Named cost, 2026-08-22: a
remote session resolved a garbled owner steer to "Lean 4", searched
only for the garbled spelling, and built a complete parallel Lean
package with its own tracking issue
([#468](https://github.com/danbri/factoidal/issues/468)) while
[#466](https://github.com/danbri/factoidal/issues/466) and
`formal/lean4/` already existed — one search for "lean" would have
found them. The duplicate cost a merge, a fold-in landing, and a
corrective trail across two issues.

**Issue state changes at landing time, not later.** When a merge fixes
an issue: close it (or comment on it) in the same work cycle as the
merge. "Fixed it, will close the issue later" produced the five
misleading open issues above. A closing comment states what fixed it,
links the pull request, and names the test that now guards it.

**Cross-reference in both directions.** An issue links its pull
requests, its parent tracker, and its evidence (test names, registry
entries). A tracker links its children. A reader landing on any one
node can reach the rest without a search.

## Rule 2 — every issue reference is a full clickable link

Write

    [#448](https://github.com/danbri/factoidal/issues/448)

everywhere: markdown files, issue bodies, reports, and every chat
message — status updates to the owner are not exempt. Be generous —
link at every mention, not once per document or once per conversation.
A phone reader scrolls into the middle; yesterday's link is gone.

Why the full URL even where `#448` would auto-link: files get mirrored
to the 11ty site, quoted in chat, and pasted between surfaces, and the
auto-linking does not travel. The one place bare `#NNN` is acceptable
is a commit message (GitHub links it, and commit messages are plain
text by nature).

`https://github.com/danbri/factoidal/issues/NNN` also resolves for
pull requests (GitHub redirects), so one URL shape covers both when
the kind is unknown.

Do NOT linkify register numbers: "hazard #24", "rule #11",
"anti-pattern #3" are entries in this repository's rule registers, not
issues. Linking them to unrelated issues is worse than plain text.
When citing a register entry, name the register and link the file:
[skills/workflow-gotchas-debugging/SKILL.md](../workflow-gotchas-debugging/SKILL.md).

## Rule 2b — never write a commit hash from memory. Read it.

A commit hash in a report is a pointer, and a wrong pointer is worse
than no pointer: the reader follows it, finds nothing, and stops
trusting the rest of the table. Copy every hash from `git log
--oneline` in the same turn you write it.

Cost of getting this wrong: 2026-08-26, the closing report on
[#619](https://github.com/danbri/factoidal/issues/619) carried a
thirteen-row table mapping each commit to the score it produced. Ten
of the thirteen hashes were invented — plausible-looking, none real.
The scores and the order were correct, so the error was invisible
until someone tried a link. It cost a correction comment on a report
that was otherwise finished.

The same rule holds for file paths, line numbers and test names in a
report: if it is a pointer, it comes from a command run in this turn,
not from recall.

## Rule 3 — register: technical Simple English

Short sentences. One fact per sentence. Concrete nouns. Numbers with
labels ("631 pass, 0 fail, out of 631" — never a bare ratio). Lead
with the result. The reader is on a phone, between other obligations.

**Banned filler.** These phrases perform confidence instead of carrying
information, and each use reduces the reader's trust in the sentences
around it:

| banned | write instead |
|---|---|
| load-bearing | say what breaks if it is wrong |
| smoke test (in prose) | name the actual test and what it checks |
| sanity check | name the check |
| battle-tested / production-ready | name the evidence: which suite, which counts, since when |
| deep dive | "detail in [issue link]" |
| low-hanging fruit | "cheapest first: ..." |
| under the hood | delete it; just state the mechanism |
| leverage (as a verb) | use |
| robust / seamless / blazingly fast | the measurement, with units |
| delve / journey / landscape / ecosystem | delete or name the specific thing |
| "it's worth noting that" / "importantly" | delete; if it were not worth noting you would not write it |
| game-changer / north star / paradigm | delete |

The sycophantic-adjective list ("honest", "genuine", "critical",
"key insight", ...) is in
[skills/markdown-style/SKILL.md](../markdown-style/SKILL.md) and
applies on top of this table.

File and symbol names are exempt: `cottas_ondisk_smoketest` is a
binary's name and stays; the prose around it says what it checks.

Named example of the drift this table exists to stop: in the week
before this skill landed, session reports used "load-bearing" more
than a dozen times. In every case the sentence was stronger with the
actual consequence spelled out.

## Checklist for any status or planning message

1. Every cited work item resolves to a full GitHub issue URL.
2. No session-local labels or new code names anywhere.
3. Anything decided or discovered in this message that future work
   depends on is ALSO written into an issue, and the message links it.
4. Fixed issues are closed or commented in this same cycle.
5. Scores are labelled counts.
6. Zero entries from the banned-filler table.

## Related

- [skills/issue-hygiene/SKILL.md](../issue-hygiene/SKILL.md) — the
  periodic sweep: finding fixed-but-open, stale, and contradictory
  issues. This skill is the per-message discipline; that one is the
  scheduled audit.
- [skills/markdown-style/SKILL.md](../markdown-style/SKILL.md) —
  clickable-link mechanics and the sycophancy list.
- The one-page work index is
  [#404](https://github.com/danbri/factoidal/issues/404); the hygiene
  tracker is
  [#198](https://github.com/danbri/factoidal/issues/198).
