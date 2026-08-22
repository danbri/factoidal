/-
L4Factoidal.RDF.CanonicalTests — build-time tests for RDFC-1.0.

Every `#guard` here evaluates during elaboration, so a wrong answer is
a BUILD ERROR, not a silent regression. The corpus-scale evidence is
separate and lives in `Harness/CanonProbe.lean` (`lake exe
l4rdfc-probe`), which reads the vendored W3C `rdf-canon` files off
disk; these tests pin the specific behaviours a reader of the spec
would want to check by eye.

Provenance of the two worked examples: they are the RDFC-1.0
Recommendation's own §4.2 examples — "Graph with blank nodes resulting
in unique hashes" (`ex-ca-unique-hashes-input`) and "Graph with blank
nodes resulting in shared hashes" (`ex-ca-shared-hashes-input`) — with
the spec's `:` prefix expanded to `http://example.com/#`, and the
expected canonical identifiers taken from the spec's own result tables
(`ex-ca-unique-canon-identifiers`, `ex-ca-shared-canon-identifiers`).
The shared-hashes example is precisely the "two blank nodes with the
same first-degree hash" case that forces Hash N-Degree Quads (§4.7).
-/
import L4Factoidal.RDF.Canonical
import L4Factoidal.Syntax.NQuads

namespace L4Factoidal.RDF.CanonicalTests

open L4Factoidal.RDF
open L4Factoidal.RDF.Canonical
open L4Factoidal.Syntax
open L4Factoidal.Crypto

/-- Parse N-Quads, or the empty dataset on a parse error. A parse
failure would make every guard below compare against the empty
document, so `parsesOk` is checked first for each fixture. -/
def parseDs (s : String) : Dataset :=
  match parseNQuads s .rdf11 with
  | .ok d    => d
  | .error _ => Dataset.empty

def parsesOk (s : String) : Bool :=
  match parseNQuads s .rdf11 with | .ok _ => true | .error _ => false

/-! ## RDFC-1.0 §4.2, example 1 — unique first-degree hashes -/

def uniqueHashesInput : String :=
  "<http://example.com/#p> <http://example.com/#q> _:e0 .\n" ++
  "<http://example.com/#p> <http://example.com/#r> _:e1 .\n" ++
  "_:e0 <http://example.com/#s> <http://example.com/#u> .\n" ++
  "_:e1 <http://example.com/#t> <http://example.com/#u> .\n"

/-- The spec's `ex-ca-canonicalized-unique-dataset`, in the §3 sorted
order (`<` = U+003C sorts before `_` = U+005F, so the IRI-subject
lines come first). -/
def uniqueHashesExpected : String :=
  "<http://example.com/#p> <http://example.com/#q> _:c14n0 .\n" ++
  "<http://example.com/#p> <http://example.com/#r> _:c14n1 .\n" ++
  "_:c14n0 <http://example.com/#s> <http://example.com/#u> .\n" ++
  "_:c14n1 <http://example.com/#t> <http://example.com/#u> .\n"

#guard parsesOk uniqueHashesInput
#guard (parseDs uniqueHashesInput).canonicalNQuads == uniqueHashesExpected

/-! §4.8 issuance is sequential from zero: `c14n0`, `c14n1`, …
(the spec's `ex-ca-unique-canon-identifiers` table). -/
#guard (canonicalize (parseDs uniqueHashesInput)).issued == [("e0", "c14n0"), ("e1", "c14n1")]

/-! Nothing aborted: this input is nowhere near the §4.4 excessive-calls
limit. -/
#guard !(canonicalize (parseDs uniqueHashesInput)).aborted

/-! ## RDFC-1.0 §4.2, example 2 — SHARED first-degree hashes

`e0` and `e1` are mentioned by byte-identical first-degree quads, so
§4.5 gives them the same hash and §4.4 step 5 must fall through to Hash
N-Degree Quads (§4.7) to tell them apart. The expected identifiers are
the spec's own (`e0`→`c14n3`, `e1`→`c14n2`, `e2`→`c14n0`,
`e3`→`c14n1`) — note they are NOT in input order, which is exactly what
makes this a real test of the N-degree path. -/

def sharedHashesInput : String :=
  "<http://example.com/#p> <http://example.com/#q> _:e0 .\n" ++
  "<http://example.com/#p> <http://example.com/#q> _:e1 .\n" ++
  "_:e0 <http://example.com/#p> _:e2 .\n" ++
  "_:e1 <http://example.com/#p> _:e3 .\n" ++
  "_:e2 <http://example.com/#r> _:e3 .\n"

def sharedHashesExpected : String :=
  "<http://example.com/#p> <http://example.com/#q> _:c14n2 .\n" ++
  "<http://example.com/#p> <http://example.com/#q> _:c14n3 .\n" ++
  "_:c14n0 <http://example.com/#r> _:c14n1 .\n" ++
  "_:c14n2 <http://example.com/#p> _:c14n1 .\n" ++
  "_:c14n3 <http://example.com/#p> _:c14n0 .\n"

#guard parsesOk sharedHashesInput
#guard (parseDs sharedHashesInput).canonicalNQuads == sharedHashesExpected

/-! The spec's `ex-ca-shared-canon-identifiers` table, verbatim. -/
#guard (canonicalize (parseDs sharedHashesInput)).issued
         == [("e0", "c14n3"), ("e1", "c14n2"), ("e2", "c14n0"), ("e3", "c14n1")]

/-- The duplicate-hash condition itself: `e0` and `e1` really do share
a first-degree hash, so §4.7 is genuinely on the path here (a guard
that would still pass if the two hashes differed would be testing
nothing). -/
def sharedQuads : List QQuad := dedupQQuads (datasetQuads (parseDs sharedHashesInput))

#guard hashFirstDegreeQuads .sha256 "e0" sharedQuads
         == hashFirstDegreeQuads .sha256 "e1" sharedQuads
#guard hashFirstDegreeQuads .sha256 "e0" sharedQuads
         != hashFirstDegreeQuads .sha256 "e2" sharedQuads
/-! The §4.4 hash-to-blank-nodes map has THREE groups here: the
colliding `{e0, e1}` pair plus a singleton each for `e2` and `e3`. So
step 4 (unique hashes) and step 5 (collisions) both run. -/
#guard (groupByHfdq (hfdqTableOf .sha256 (parseDs sharedHashesInput) sharedQuads)).length == 3

/-! ## Relabelling invariance (measured, on these fixtures)

RDFC-1.0's purpose: two datasets that differ only in their blank-node
labels canonicalise to the SAME bytes. `RDF/CanonicalTheorems.lean`
states this as a theorem and proves the sub-lemmas it rests on; these
guards check it on concrete inputs. -/

/-- The shared-hashes fixture with every blank-node label renamed
(`e0`→`zzz`, `e1`→`aa`, `e2`→`m1`, `e3`→`Q`) — chosen so the renaming
also reverses the original labels' sort order, which would break a
canonicalizer that leaked the input labels into its tie-breaks. -/
def sharedHashesRelabelled : String :=
  "<http://example.com/#p> <http://example.com/#q> _:zzz .\n" ++
  "<http://example.com/#p> <http://example.com/#q> _:aa .\n" ++
  "_:zzz <http://example.com/#p> _:m1 .\n" ++
  "_:aa <http://example.com/#p> _:Q .\n" ++
  "_:m1 <http://example.com/#r> _:Q .\n"

#guard parsesOk sharedHashesRelabelled
#guard (parseDs sharedHashesRelabelled).canonicalNQuads
         == (parseDs sharedHashesInput).canonicalNQuads

/-- The same for the unique-hashes fixture, with the quads also given
in a different document order (a dataset is a SET; the input order
must not survive into the output). -/
def uniqueHashesShuffled : String :=
  "_:second <http://example.com/#t> <http://example.com/#u> .\n" ++
  "<http://example.com/#p> <http://example.com/#q> _:first .\n" ++
  "_:first <http://example.com/#s> <http://example.com/#u> .\n" ++
  "<http://example.com/#p> <http://example.com/#r> _:second .\n"

#guard (parseDs uniqueHashesShuffled).canonicalNQuads == uniqueHashesExpected

/-- Non-isomorphic datasets must NOT collide: change one predicate and
the canonical form changes. (Without this the invariance guards above
would be satisfiable by a constant function.) -/
def sharedHashesPerturbed : String :=
  "<http://example.com/#p> <http://example.com/#q> _:e0 .\n" ++
  "<http://example.com/#p> <http://example.com/#q> _:e1 .\n" ++
  "_:e0 <http://example.com/#p> _:e2 .\n" ++
  "_:e1 <http://example.com/#p> _:e3 .\n" ++
  "_:e2 <http://example.com/#DIFFERENT> _:e3 .\n"

#guard (parseDs sharedHashesPerturbed).canonicalNQuads
         != (parseDs sharedHashesInput).canonicalNQuads

/-- Non-isomorphic by SHAPE rather than by vocabulary: two blank nodes
joined in a cycle versus two joined in a chain. -/
def twoNodeCycle : String :=
  "_:a <http://example.com/#p> _:b .\n_:b <http://example.com/#p> _:a .\n"
def twoNodeChain : String :=
  "_:a <http://example.com/#p> _:b .\n_:b <http://example.com/#p> <http://example.com/#x> .\n"

#guard (parseDs twoNodeCycle).canonicalNQuads != (parseDs twoNodeChain).canonicalNQuads

/-! ## RDF set semantics — a repeated quad must not change anything
(W3C rdf-canon test076 / test077 exercise this at corpus scale). -/

#guard (parseDs (uniqueHashesInput ++ uniqueHashesInput)).canonicalNQuads
         == uniqueHashesExpected

/-! ## Hash agility (crypto-policy: consumers take `HashAlgorithm`)

`.sha384` must select a genuinely different digest AND a genuinely
different canonical labelling — RDFC-1.0 orders blank nodes by their
hashes, so changing the hash changes which node gets `c14n0` (this is
exactly why the W3C suite's test075 exists: it is test020 re-run under
SHA-384).

Both expected values below were produced OUTSIDE Lean, by piping the
canonical document into `shasum`, so they check this port's SHA-2
against a third-party implementation rather than against itself:

    printf '<http://example.com/#p> <http://example.com/#q> _:c14n0 .\n\
    <http://example.com/#p> <http://example.com/#r> _:c14n1 .\n\
    _:c14n0 <http://example.com/#s> <http://example.com/#u> .\n\
    _:c14n1 <http://example.com/#t> <http://example.com/#u> .\n' | shasum -a 256

    printf '<http://example.com/#p> <http://example.com/#q> _:c14n1 .\n\
    <http://example.com/#p> <http://example.com/#r> _:c14n0 .\n\
    _:c14n0 <http://example.com/#t> <http://example.com/#u> .\n\
    _:c14n1 <http://example.com/#s> <http://example.com/#u> .\n' | shasum -a 384
-/

/-- The SHA-384 canonical form of `uniqueHashesInput`: note the
labelling is the REVERSE of the SHA-256 one. -/
def uniqueHashesExpected384 : String :=
  "<http://example.com/#p> <http://example.com/#q> _:c14n1 .\n" ++
  "<http://example.com/#p> <http://example.com/#r> _:c14n0 .\n" ++
  "_:c14n0 <http://example.com/#t> <http://example.com/#u> .\n" ++
  "_:c14n1 <http://example.com/#s> <http://example.com/#u> .\n"

def uniqueHashesSha256 : String :=
  "197dce9a2a3f3c4bb4591910b3762146423c1a4f6901e3789490d1f28fd5e796"

def uniqueHashesSha384 : String :=
  "57521b16f965b21861d02f3f03e1bd6a0b5c761185dc2edd26e0342594dd74e0" ++
  "db2379c72dfd7a91420eff4c59a183e2"

#guard (parseDs uniqueHashesInput).canonicalNQuads .sha384 == uniqueHashesExpected384
#guard (parseDs uniqueHashesInput).canonicalHash .sha256 == uniqueHashesSha256
#guard (parseDs uniqueHashesInput).canonicalHash .sha384 == uniqueHashesSha384
#guard (parseDs uniqueHashesInput).canonicalHash .sha384
         != (parseDs uniqueHashesInput).canonicalHash .sha256
#guard ((parseDs uniqueHashesInput).canonicalHash .sha384).length == 96
#guard ((parseDs uniqueHashesInput).canonicalHash .sha256).length == 64

/-! SHA-384 reorders the blank nodes, not merely the digest bytes. -/
#guard (canonicalize (parseDs uniqueHashesInput) .sha384).issued
         == [("e0", "c14n1"), ("e1", "c14n0")]
#guard (canonicalize (parseDs sharedHashesInput) .sha384).issued
         != (canonicalize (parseDs sharedHashesInput) .sha256).issued

/-! ## §3 escaping -/

#guard escapeChar '\\' == "\\\\"
#guard escapeChar '"' == "\\\""
#guard escapeChar '\n' == "\\n"
#guard escapeChar (Char.ofNat 0x08) == "\\b"
#guard escapeChar (Char.ofNat 0x0C) == "\\f"
#guard escapeChar (Char.ofNat 0x00) == "\\u0000"
#guard escapeChar (Char.ofNat 0x0B) == "\\u000B"
#guard escapeChar (Char.ofNat 0x1F) == "\\u001F"
#guard escapeChar (Char.ofNat 0x7F) == "\\u007F"
/-! Non-ASCII passes through as raw UTF-8, never `\uXXXX` — the W3C
suite's test060 expected output relies on this. -/
#guard escapeLit "∞" == "∞"
#guard escapeLit "a\tb" == "a\\tb"

/-! ## §3 code-point ordering -/

#guard strLe "" "a"
#guard strLe "a" "ab"
#guard !strLe "ab" "a"
#guard strLe "<" "_"          -- U+003C before U+005F: IRI subjects sort first
#guard sortStrings ["c", "a", "b"] == ["a", "b", "c"]
#guard dedupAdj ["a", "a", "b"] == ["a", "b"]
/-! The output is a LIST of lines that the document concatenates, and
each adjacent pair is in code-point order (proved in general in
`CanonicalTheorems.canonicalLines_sorted`; checked concretely here). -/
#guard (parseDs sharedHashesInput).canonicalLines.length == 5
#guard joinStrings ((parseDs sharedHashesInput).canonicalLines) == sharedHashesExpected
#guard ((parseDs sharedHashesInput).canonicalLines.zip
          ((parseDs sharedHashesInput).canonicalLines.drop 1)).all
        (fun p => strLe p.1 p.2)

/-! ## §4.8 label rendering -/

#guard natToString 0 == "0"
#guard natToString 9 == "9"
#guard natToString 10 == "10"
#guard natToString 1234 == "1234"
#guard mkLabel "c14n" 0 == "c14n0"
#guard mkLabel "c14n" 12 == "c14n12"
#guard mkLabel "b" 3 == "b3"
#guard emptyIssuer.labelPrefix == "c14n"
#guard emptyTempIssuer.labelPrefix == "b"
/-! Issuance is idempotent on a label already issued (§4.8 step 1). -/
#guard (issueIdentifier (issueIdentifier emptyIssuer "x").1 "x").2 == "c14n0"
#guard (issueIdentifier (issueIdentifier emptyIssuer "x").1 "y").2 == "c14n1"

/-! ## §4.4 excessive-calls abort -/

/-! With no budget at all, even this small dataset reports the abort —
the mechanism is live, not decorative. -/
#guard canonicalizeExceedsBudget .sha256 0 (parseDs sharedHashesInput)
/-! With the ordinary budget it does not. -/
#guard !canonicalizeExceedsBudget .sha256 defaultHndqBudget (parseDs sharedHashesInput)

/-! ## Permutation enumeration (§4.7 step 5.4) -/

#guard (permutationsOf ["a", "b"]).length == 2
#guard (permutationsOf ["a", "b", "c"]).length == 6
#guard permutationsOf ["a", "b"] == [["a", "b"], ["b", "a"]]
/-! The cap is a stated result variant, so pin it. -/
#guard permutationCap == 6
#guard (permutationsOf (["a","b","c","d","e","f","g"].take permutationCap)).length == 720

/-! ## Axiom audit — the whole point of the Lean port -/

#print axioms L4Factoidal.RDF.Canonical.canonicalize
#print axioms L4Factoidal.RDF.Dataset.canonicalNQuads
#print axioms L4Factoidal.RDF.Canonical.hashFirstDegreeQuads
#print axioms L4Factoidal.RDF.Canonical.hndqRun

end L4Factoidal.RDF.CanonicalTests
