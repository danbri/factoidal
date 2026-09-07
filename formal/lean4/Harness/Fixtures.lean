/-
Harness.Fixtures — resolve a vendored test-fixture path from either
working directory the probes are launched in.

Some probes are run from the REPOSITORY ROOT (`lake -d formal/lean4
exe NAME`, fixture `third_party/testing/...`) and some from
`formal/lean4` (`lake exe NAME`, fixture `../../third_party/...`). A
probe that hard-codes one of the two prints "directory not present"
in the other, which reads as a missing fixture rather than a wrong
current directory. Every probe resolves its default through
`resolveFixture`, which tries the ROOT-RELATIVE form first and then
the `../../` and `../../../` forms.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/

namespace Harness

/-- The prefixes tried, in order: as given (repository root), then one
and two directories up (`formal/lean4`, and a probe launched from a
directory below it). -/
def fixturePrefixes : List String := ["", "../../", "../../../"]

/-- The candidate paths for a repository-root-relative fixture path. -/
def fixtureCandidates (rel : String) : List String :=
  fixturePrefixes.map (· ++ rel)

/-- The first candidate that exists as a file or a directory, or
`none` when the fixture is absent from every one of them. -/
def resolveFixture (rel : String) : IO (Option String) := do
  let mut found : Option String := none
  for c in fixtureCandidates rel do
    if found.isNone then
      if ← System.FilePath.pathExists (System.FilePath.mk c) then
        found := some c
  return found

/-- `resolveFixture`, falling back to the root-relative form so the
caller can report the path it looked for. -/
def resolveFixtureOr (rel : String) : IO String := do
  return (← resolveFixture rel).getD rel

/-- An argument the user gave is used AS IS (it is relative to their
own current directory); only the built-in default is resolved. -/
def fixtureArgOr (arg? : Option String) (rel : String) : IO String := do
  match arg? with
  | some a => pure a
  | none   => resolveFixtureOr rel

end Harness
