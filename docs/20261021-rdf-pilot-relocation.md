# RDF pilot relocation — 2026-10-21

At the owner's request, moved the complete `codex-npm-review/_LEAN` directory
to `pilot/_LEAN` in the original `factoidal` repository. The pilot explores
RDF in more depth for debugging and supporting infrastructure and skills.
The [pilot index](../pilot/README.md) records the owner's wording.

The old local path is a compatibility symlink. File contents, nested Git
histories, build outputs, and the virtual environment were preserved by a
directory rename. Historical evidence was not rewritten. Existing changes
in the main Factoidal worktree were preserved.

The two review helpers now use `FACTOIDAL_REVIEW_ROOT`, defaulting to
`~/working/sandbox/october/tpac/codex-npm-review`, instead of assuming the
review is their parent directory. The pilot README documents this dependency.
A pilot-local ignore file excludes local environments, build caches, and the
independent RDF test and Dickory publication checkouts from the parent repo.
Those checkouts remain on disk with their Git metadata.

Validation: compared all file SHA-256 hashes, modes, directory entries and
symlink targets immediately before and after the move; verified the old
path resolves to the new location; parsed both changed Python helpers;
regenerated the eight-file source patch and checked that its bytes and
source-change manifest remained identical. No Lean sources were changed.
This relocation does not establish any new proof or conformance result.
