/-
Generator for the tests/stack regression fixture: an SBM0 Shardborough
manifest with N minimal, distinct entries, written as raw bytes to a file.

It exists so `tests/stack/inspect-big.mjs` can drive `storeManifestInspect`
on a large entry list at Node's DEFAULT (tab-sized) stack and confirm the
JSON output writer no longer recurses one C frame per entry
(docs/designissues/2026-09-07-store-over-http.md, "the second overflow").

It uses the engine's own `encode?`; it does not hand-assemble wire bytes.
Digests are not verified at decode, so a zero digest of the right length is
enough to pass `valid` for an SBM0 manifest — this fixture exercises the
inspect PATH, not artifact integrity. Run from formal/lean4:

  lake env lean --run tests/stack/gen_manifest.lean <N> <out-path>
-/
import L4Factoidal.Storage.ShardManifest
import L4Factoidal.RDF.Core

open L4Factoidal.Storage.ShardManifest
open L4Factoidal.RDF

/-- Runtime smart constructor for a well-formed IRI (the `iriW` pattern). -/
def mkIri (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

/-- One minimal SBM0 entry, distinct in predicate and artifact key by index. -/
def mkEntry (i : Nat) : Entry :=
  { predicate := mkIri s!"http://e.org/p{i}"
    artifact := { key := { value := s!"blocks/p{i}.ibk2" }
                  bytes := 1
                  sha256 := ByteArray.mk ((List.replicate 32 (0 : UInt8)).toArray) }
    rows := 1
    ordinal := i }

def mkManifest (n : Nat) : Manifest :=
  { version := 0
    sourceIdentity := ByteArray.mk #[0]
    termRegistryVersion := "terms-v0"
    layout := "predicate-ibk2-v0"
    entries := (List.range n).map mkEntry }

def main (args : List String) : IO Unit := do
  let n := (args[0]? |>.bind String.toNat?).getD 40000
  let out := (args[1]?).getD "/tmp/stack-manifest.sbm0"
  let manifest := mkManifest n
  match encode? manifest with
  | none => throw (IO.userError "encode? returned none — the synthetic manifest was rejected")
  | some bytes =>
      IO.FS.writeBinFile out bytes
      IO.println s!"wrote {bytes.size} bytes, {n} entries, to {out}"
