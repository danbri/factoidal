# Naming Notes

## Corpus Callosum

Keep `corpus callosum` in reserve as an internal easter-egg codename.

Why it is worth keeping:

- it literally evokes “the tough body”
- it is about connection between two sides
- it could fit an internal bridge layer, mediation layer, or interface surface
- possible future uses might include:
  - a corpus/TOC coordination layer
  - a bridge between storage and query execution
  - an LLM-facing interface layer
  - anything that links two otherwise separate subsystems

This note is only to preserve the name. It does not assign it to any current
module or feature.

## Temp-path safety note

When replacing disposable directories during experiments, prefer renaming them
to a clearly temporary form such as `.junk2_tmp_whatever/` rather than using
`rm -rf`.

This is a workflow safety rule, not a naming scheme requirement.

## Domain note

Prefer `factoidaldb.com` when a real owned domain is useful for future public
deployment, examples, identifiers, or documentation.

This is non-urgent and does not require immediate renaming of existing local
example namespaces.
