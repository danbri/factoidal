/-
L4Factoidal.Storage.PredicateQuadBlocks — one IBK4 quad block per predicate.

The quad twin of `PredicateBlocks`. That module partitions a graph of triples
into one `IndexedBlock.Block` per predicate; this one partitions the quads of a
DATASET into one `IndexedBlockWireV4.QuadBlock` per predicate, so a predicate's
rows for every graph live in the same artifact and `GRAPH <iri> { ... }` is a
filter inside the block (`docs/designissues/2026-09-02-quad-aware-block-layout.md`,
option B).

Publication order is the first-occurrence order of the predicate in the
flattened quad list, and row order inside a block is the flattened quad order
restricted to that predicate. Both are the orders `PredicateBlocks` already
uses, so an IBK4 generation of a default-graph-only source has the same block
sequence as the IBK3 generation of the same source.

No `partial`, no `unsafe`, no `sorry`.
-/
import L4Factoidal.Storage.IndexedBlockWireV4
import L4Factoidal.Storage.TermWireV2
import Std.Data.HashMap

namespace L4Factoidal.Storage.PredicateQuadBlocks

open L4Factoidal.RDF
open L4Factoidal.Storage.IndexedBlockWireV4

/-- Flatten a dataset into quads: the default graph first, then each named
    graph in `Dataset.named` order, each graph in its own triple order.

    This is the same list as `RDF.Canonical.datasetQuads`, restated here so the
    storage layer does not depend on the RDFC-1.0 canonicalization module. The
    two definitions must stay in step; the `#guard` at the foot of this file
    pins the shape that matters — the default graph comes first. -/
def quadsOfDataset (ds : Dataset) : List QuadRow :=
  ds.default.map (fun t => ((none : Option GraphRef), t)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => ((some ng.name : Option GraphRef), t)))

/-- Packer-facing construction state. `rows` gives expected constant-time
    predicate lookup; `orderRev` records first-seen predicates in reverse so
    construction stays constant-time per quad. Rows are held in reverse source
    order until `blocksOfBuckets`. -/
structure Buckets where
  rows : Std.HashMap WfIri (List QuadRow) := ∅
  orderRev : List WfIri := []

def addQuad (buckets : Buckets) (quad : QuadRow) : Buckets :=
  let predicate := quad.2.p
  let known := buckets.rows.contains predicate
  { rows := buckets.rows.insert predicate (quad :: buckets.rows.getD predicate [])
  , orderRev := if known then buckets.orderRev else predicate :: buckets.orderRev }

def addQuads (buckets : Buckets) (quads : List QuadRow) : Buckets :=
  quads.foldl addQuad buckets

/-! ## Bounded blocks

A predicate's rows are cut into consecutive runs, and each run becomes its own
block. `docs/designissues/2026-09-04-blocks-per-predicate.md` records the
decision; the rules are:

1. the graph changes — always, so a block holds one predicate in ONE graph and
   its manifest `graphSet` has exactly one member;
2. `maxBlockRows` rows;
3. `maxBlockWireBytes` of estimated wire size.

Cutting NEVER reorders: `quadsOfDataset` is graph-major, so a predicate's rows
already arrive with their graph runs consecutive, and a cut is a partition of
the existing order into consecutive pieces. `PredicateQuadBlocksTheorems`
proves the concatenation of the runs is the row list itself, so the emitted
block set denotes exactly the quads the single-block set denoted.

The two numbers come from the read caps of `Wasm/Ops/Store.lean`, which are
TOTALS over the entries one `storeQuery` selects rather than per-block limits:
8,388,608 bytes and 100,000 rows. A per-block target has to leave room for
several blocks in one query, so the byte target is a quarter of the byte cap
and the row target is a sixth of the row cap, rounded down to a power of two. -/

def maxBlockRows : Nat := 16384
def maxBlockWireBytes : Nat := 2097152

/-- One length-prefixed string of `DeltaLog.serializeLString`: a u32 length and
    the UTF-8 bytes. -/
private def lstringWireBytes (s : String) : Nat := 4 + s.utf8ByteSize

/-- The exact `DeltaLog.serializeTerm` length of a subject term. -/
def subjectWireBytes : Subject → Nat
  | .iri i => 1 + lstringWireBytes i.val
  | .bnode b => 1 + lstringWireBytes b

/-- The dictionary cost of one object term, for the CUT POLICY only. No wire
    byte depends on it: it decides where a block ends, not what a block holds.

    It is the version-2 term width (`Storage/TermWireV2.lean`), which is the
    version-1 width for every term the two codecs share — an IRI, a blank
    node, and an inline literal are tag-for-tag the same size — and differs in
    exactly two places:

    * a literal whose UTF-8 lexical form is above
      `TermWireV2.maxInlineLexicalBytes` is stored OUT OF LINE, so its bytes
      are in a `blob-<hex>.lit` artifact and not in the block. Counting its
      lexical length here would cut a block at a cost the block does not
      carry;
    * a triple term is recursive, so it costs its parts rather than one byte.

    The policy is shared by both quad formats. For IBK4 that is a widening of
    the estimate in two cases IBK4 cannot store at all (it refuses a triple
    term) or has never met in a packed corpus (a literal above 65,536 bytes);
    the measured skosdex block counts are unchanged. -/
def termWireBytes : Term → Nat
  | .iri i => 1 + lstringWireBytes i.val
  | .bnode b => 1 + lstringWireBytes b
  | .literal l =>
      let lang := match l.val.langTag with
        | none => 1
        | some tag => 1 + lstringWireBytes tag
      if l.val.lexicalForm.utf8ByteSize ≤ L4Factoidal.Storage.TermWireV2.maxInlineLexicalBytes then
        1 + lstringWireBytes l.val.lexicalForm + lstringWireBytes l.val.datatype.val + lang
      else
        -- tag, datatype IRI, the flag and its tag, a u64 byte length, a
        -- 32-byte SHA-256.
        1 + lstringWireBytes l.val.datatype.val + lang + 8 + 32
  | .tripleTerm s p o => 1 + subjectWireBytes s + lstringWireBytes p.val + termWireBytes o

/-- A conservative UPPER BOUND of the bytes one quad adds to its block: the
    fixed-width row, one graph-summary entry, and the dictionary cost of all
    four term positions counted WITHOUT de-duplication. PTD1 stores each
    distinct term once, so the true cost is never larger. -/
def quadWireBytes (quad : QuadRow) : Nat :=
  rowBytes + graphEntryBytes +
    subjectWireBytes quad.2.s + 1 + lstringWireBytes quad.2.p.val +
    termWireBytes quad.2.o +
    (match quad.1 with
     | none => 0
     | some graph => subjectWireBytes graph)

/-- Cut one predicate's rows into consecutive runs. Structural on the input
    list; the accumulator is reversed and flipped back at each cut. -/
def chunkGo : List QuadRow → List QuadRow → Nat → Nat → Option GraphRef →
    List (List QuadRow)
  | [], accRev, _, _, _ => if accRev.isEmpty then [] else [accRev.reverse]
  | quad :: rest, accRev, rows, bytes, graph =>
      let weight := quadWireBytes quad
      if accRev.isEmpty then chunkGo rest [quad] 1 weight quad.1
      else if quad.1 == graph && rows < maxBlockRows &&
          bytes + weight <= maxBlockWireBytes then
        chunkGo rest (quad :: accRev) (rows + 1) (bytes + weight) graph
      else accRev.reverse :: chunkGo rest [quad] 1 weight quad.1

/-- The runs of one predicate's rows, in row order. -/
def chunkQuadRows (quads : List QuadRow) : List (List QuadRow) :=
  chunkGo quads [] 0 0 none

/-- The rows of one predicate's blocks, before they are encoded. Separating
    the ROW partition from the block construction lets the packer build one
    `QuadBlock` at a time instead of holding the whole block set. -/
def runsOfBuckets (buckets : Buckets) : List (WfIri × List QuadRow) :=
  buckets.orderRev.reverse.flatMap fun predicate =>
    (chunkQuadRows (buckets.rows.getD predicate []).reverse).map fun rows =>
      (predicate, rows)

def runsOfQuads (quads : List QuadRow) : List (WfIri × List QuadRow) :=
  runsOfBuckets (addQuads {} quads)

def runsOfDataset (ds : Dataset) : List (WfIri × List QuadRow) :=
  runsOfQuads (quadsOfDataset ds)

def blocksOfBuckets (buckets : Buckets) : List (WfIri × QuadBlock) :=
  buckets.orderRev.reverse.flatMap fun predicate =>
    (chunkQuadRows (buckets.rows.getD predicate []).reverse).map fun rows =>
      (predicate, fromQuads rows)

/-- The IBK4 blocks of a quad list: one or more per predicate, each holding
    that predicate's rows for ONE graph, bounded by the two targets above. -/
def blocksOfQuads (quads : List QuadRow) : List (WfIri × QuadBlock) :=
  blocksOfBuckets (addQuads {} quads)

def blocksOfDataset (ds : Dataset) : List (WfIri × QuadBlock) :=
  blocksOfQuads (quadsOfDataset ds)

/-! ## Publication every batch

`docs/designissues/2026-09-05-pack-publication-every-batch.md` records the
policy; section 5 of
`docs/designissues/2026-09-05-wire-version-10-scale.md` decides it. The
packer publishes blocks DURING the ingest pass, so its peak memory is bounded
by two operator numbers instead of by the source.

`Buckets` above holds every row of every predicate until the end of the
source. `Pub` below holds, per predicate, only the OPEN RUN — the rows of the
block currently being built — with the running cut state `chunkGo` carries in
its arguments. The five rules:

1. quads accumulate into the per-predicate open runs;
2. a run the per-block cut rule closes is published at once and its rows are
   released (`pubAdd`);
3. after `batchSourceBytes` of source, every run holding at least
   `minBatchRows` rows is published; smaller runs carry over
   (`pubFlush st minBatchRows`);
4. when the carried rows pass `maxCarriedRows`, every run is published
   (`pubAdd`, which checks after each quad);
5. at end of source every run is published (`pubFlush st 0`).

With no flush between (a source below one batch), rules 2 and 5 cut each
predicate's rows at the same places `runsOfBuckets` does; what differs is the
ORDER the runs are published in, which is completion order rather than
predicate-major order, so the block ORDINALS differ. Rules 3 and 4 are what
cut memory, and they change the block SET as well: a predicate whose rows
straddle a batch boundary gets a block ending at that boundary. Every manifest
since SBM2 admits both — a reader takes the union of the entries for a
predicate.
-/

/-- The default of `--batch-bytes`: 268,435,456 source bytes per batch. -/
def batchSourceBytesDefault : Nat := 268435456

/-- A run below this many rows carries over a batch end rather than becoming
    a block of its own. Without it a source with a few hundred predicates and
    hundreds of batches produces tens of thousands of near-empty entries. -/
def minBatchRows : Nat := 4096

/-- The bound on the rows every open run holds together. Rule 3 retains small
    runs; this is what bounds what it retains, for a source with hundreds of
    thousands of predicates. -/
def maxCarriedRows : Nat := 1048576

/-- The open run of one predicate: the rows of the block being built, in
    reverse order, and the cut state `chunkGo` carries as arguments. -/
structure Run where
  accRev : List QuadRow := []
  rows : Nat := 0
  bytes : Nat := 0
  graph : Option GraphRef := none

/-- The publication state. `orderRev` is the reverse first-occurrence order of
    the predicates, which fixes the order runs are published in at a flush;
    `carried` is the total rows the open runs hold. -/
structure Pub where
  runs : Std.HashMap WfIri Run := ∅
  orderRev : List WfIri := []
  carried : Nat := 0

/-- Publish every open run holding at least `minRows` rows, in first-occurrence
    predicate order. `minRows = 0` publishes every non-empty run. -/
def flushStep (minRows : Nat) (acc : Pub × List (WfIri × List QuadRow))
    (predicate : WfIri) : Pub × List (WfIri × List QuadRow) :=
  match acc.1.runs[predicate]? with
  | none => acc
  | some run =>
      if run.accRev.isEmpty || run.rows < minRows then acc
      else
        ({ acc.1 with runs := acc.1.runs.insert predicate ({} : Run),
                      carried := acc.1.carried - run.rows },
         (predicate, run.accRev.reverse) :: acc.2)

def pubFlush (st : Pub) (minRows : Nat) : Pub × List (WfIri × List QuadRow) :=
  let result := st.orderRev.reverse.foldl (flushStep minRows) (st, [])
  (result.1, result.2.reverse)

/-- The open run one quad starts. -/
def freshRun (quad : QuadRow) : Run :=
  { accRev := [quad], rows := 1, bytes := quadWireBytes quad, graph := quad.1 }

/-- Add one quad to its predicate's open run, publishing the run the
    per-block cut rule closes (rule 2). This is `chunkGo`'s step with the cut
    state held per predicate instead of in the arguments. -/
def pubAddRun (st : Pub) (quad : QuadRow) : Pub × List (WfIri × List QuadRow) :=
  let predicate := quad.2.p
  let weight := quadWireBytes quad
  let fresh : Run := freshRun quad
  match st.runs[predicate]? with
  | none =>
      ({ runs := st.runs.insert predicate fresh
       , orderRev := predicate :: st.orderRev
       , carried := st.carried + 1 }, [])
  | some run =>
      if run.accRev.isEmpty then
        ({ st with runs := st.runs.insert predicate fresh
                 , carried := st.carried + 1 }, [])
      else if quad.1 == run.graph && run.rows < maxBlockRows &&
          run.bytes + weight <= maxBlockWireBytes then
        ({ st with
             runs := st.runs.insert predicate
               { accRev := quad :: run.accRev, rows := run.rows + 1
               , bytes := run.bytes + weight, graph := run.graph }
             carried := st.carried + 1 }, [])
      else
        ({ st with runs := st.runs.insert predicate fresh
                 , carried := st.carried + 1 - run.rows },
         [(predicate, run.accRev.reverse)])

/-- `pubAddRun` with its `let` bindings substituted, so a proof can rewrite
    the match scrutinee. Definitional; the definition above is the executable
    one and evaluates each binding once. -/
theorem pubAddRun_eq (st : Pub) (quad : QuadRow) :
    pubAddRun st quad =
      (match st.runs[quad.2.p]? with
       | none =>
           ({ runs := st.runs.insert quad.2.p (freshRun quad)
            , orderRev := quad.2.p :: st.orderRev
            , carried := st.carried + 1 }, [])
       | some run =>
           if run.accRev.isEmpty then
             ({ st with runs := st.runs.insert quad.2.p (freshRun quad)
                      , carried := st.carried + 1 }, [])
           else if quad.1 == run.graph && run.rows < maxBlockRows &&
               run.bytes + quadWireBytes quad <= maxBlockWireBytes then
             ({ st with
                  runs := st.runs.insert quad.2.p
                    ({ accRev := quad :: run.accRev, rows := run.rows + 1
                     , bytes := run.bytes + quadWireBytes quad, graph := run.graph } : Run)
                  carried := st.carried + 1 }, [])
           else
             ({ st with runs := st.runs.insert quad.2.p (freshRun quad)
                      , carried := st.carried + 1 - run.rows },
              [(quad.2.p, run.accRev.reverse)])) := rfl

/-- `pubAddRun` plus rule 4: when the carried rows pass `maxCarriedRows`
    every open run is published, whatever its size. -/
def pubAdd (st : Pub) (quad : QuadRow) : Pub × List (WfIri × List QuadRow) :=
  let stepped := pubAddRun st quad
  if stepped.1.carried > maxCarriedRows then
    ((pubFlush stepped.1 0).1, stepped.2 ++ (pubFlush stepped.1 0).2)
  else stepped

/-- `pubAdd` with its `let` binding substituted. Definitional. -/
theorem pubAdd_eq (st : Pub) (quad : QuadRow) :
    pubAdd st quad =
      (if (pubAddRun st quad).1.carried > maxCarriedRows then
         ((pubFlush (pubAddRun st quad).1 0).1,
          (pubAddRun st quad).2 ++ (pubFlush (pubAddRun st quad).1 0).2)
       else pubAddRun st quad) := rfl

/-- `pubFlush` with its `let` binding substituted. Definitional. -/
theorem pubFlush_eq (st : Pub) (minRows : Nat) :
    pubFlush st minRows =
      ((st.orderRev.reverse.foldl (flushStep minRows) (st, [])).1,
       (st.orderRev.reverse.foldl (flushStep minRows) (st, [])).2.reverse) := rfl

/-! ## Build-time checks -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def pKind : WfIri := ⟨"http://example.org/kind", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩
private def g1 : GraphRef := .iri ⟨"http://example.org/g1", by simp [isIri]⟩

private def sample : Dataset :=
  { default := [{ s := alice, p := pName, o := .literal (Literal.string "A") },
                { s := alice, p := pKind, o := .iri ⟨"http://example.org/Person", by simp [isIri]⟩ }]
    named := [{ name := g1
                graph := [{ s := bob, p := pName, o := .literal (Literal.string "B") }] }] }

private def sampleBlocks := blocksOfDataset sample

-- The default graph is flattened first, so publication order is the
-- first-occurrence order of the predicate over the whole dataset. `name` has
-- rows in two graphs, so it now publishes two blocks.
#guard sampleBlocks.map Prod.fst == [pName, pName, pKind]
#guard (quadsOfDataset sample).head?.map Prod.fst == some none
#guard (quadsOfDataset sample).length == 3

-- Every block holds ONE graph, is predicate-local, and encodes.
#guard sampleBlocks.map (fun entry => entry.2.rows.size) == [1, 1, 1]
#guard sampleBlocks.all fun entry => onePredicate entry.2
#guard sampleBlocks.all fun entry => (encode? entry.2).isSome
#guard sampleBlocks.all fun entry =>
  (graphNames? entry.2).map List.length == some 1
#guard sampleBlocks.map (fun entry => graphNames? entry.2) ==
  [some [none], some [some g1], some [none]]

-- Cutting is a partition of the row order: no reordering, nothing lost.
#guard (chunkQuadRows (quadsOfDataset sample)).flatten == quadsOfDataset sample

-- Every quad of the dataset is denoted by exactly one block, in source order.
#guard (sampleBlocks.flatMap fun entry => entry.2.denotes).length == 3

-- The streamed publication of a source below one batch is the buffered
-- partition: rules 2 and 5 alone, with no flush in between.
private def pubRunsAll (quads : List QuadRow) : List (WfIri × List QuadRow) :=
  let step := fun (acc : Pub × List (WfIri × List QuadRow)) (quad : QuadRow) =>
    let (state, out) := acc
    let (state, made) := pubAdd state quad
    (state, out ++ made)
  let (state, out) := quads.foldl step ({}, [])
  out ++ (pubFlush state 0).2

#guard pubRunsAll (quadsOfDataset sample) == runsOfDataset sample
#guard (pubRunsAll (quadsOfDataset sample)).flatMap Prod.snd ==
  (runsOfDataset sample).flatMap Prod.snd
#guard (pubRunsAll []) == []

end L4Factoidal.Storage.PredicateQuadBlocks
