# checked-cache (orphan branch)

F* `.checked` verification cache for `formal/fstar/`, snapshotted
ONLY from states that passed the full gate battery (F* verification +
W3C suites + perf gates) — see skills/session-restore/SKILL.md, gate
rule. Restores a ~2h cold full-tree verification in seconds; F*'s
per-module content-digest invalidation means even a stale snapshot
gives partial hits after source changes.

Filename: checked-<source-short-sha>-fstar<version>.tar.gz.
Untar into formal/fstar/. Rebuild + amend (single commit, history is
worthless bulk) after landing changes that re-verified large parts of
the tree. Consumer wiring: tools/install-toolchain-cache.sh.
