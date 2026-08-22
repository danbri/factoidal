/-
L4Factoidal.RDF.Canonical — RDF Dataset Canonicalization 1.0 (RDFC-1.0).

Spec: https://www.w3.org/TR/rdf-canon/ (W3C Recommendation, 2024).
Port of `formal/fstar/RDF.Canonical.fst` (the F* module that passes the
W3C `rdf-canon` suite; it is the spec of record for every edge case
where the prose leaves a choice open).

What this module implements, with the spec sections each step cites:

  * §3  — canonical N-Quads form: the serialisation of one quad, the
          literal escaping table, and "sort the serialised quads in
          code point order".
  * §4.5 (Hash First Degree Quads) — per blank node, render its
          incident quads with the node itself as `_:a` and every other
          blank node as `_:z`, sort, concatenate, hash.
  * §4.6 (Hash Related Blank Node) — position tag + predicate +
          identifier, hashed.
  * §4.7 (Hash N-Degree Quads) — the bucket map over related blank
          nodes and the permutation loop, run through a cloned
          ("temporary") issuer.
  * §4.8 (Issue Identifier) — sequential `c14n0`, `c14n1`, … for the
          canonical issuer; `b0`, `b1`, … for each temporary one.
  * §4.4 (canonicalization algorithm) — two passes over the
          hash-to-blank-nodes map: unique hashes first, then the
          collision groups.

ASSUMPTION REPORT (the point of the port). The F* module has exactly
two `assume val`s — `hash_sha256` and `hash_sha384`, realised outside
F* by hand-written OCaml. Both are REPLACED here by the pure Lean
SHA-2 of `L4Factoidal.Crypto.SHA2`, reached only through the
`HashAlgorithm` parameter (`Crypto.hashHex`), per the hash-agility
rule: no function in this file names `sha256`/`sha384` directly.
Nothing else in the F* module was assumed, and nothing else is assumed
here: no `sorry`, no `axiom`, no `native_decide`, no `partial`.

DIFFERENCES FROM THE F* SOURCE, all deliberate and all listed:

  1. Termination. F* bounds the Hash-N-Degree-Quads recursion with a
     lexicographic `decreases %[fuel; phase; list]` over a six-function
     mutual block. Here the same shape is obtained without any mutual
     recursion: `hndqRun` is structurally recursive on its fuel and
     hands the "recurse one level down" closure (`HndqRec`) to the
     bucket/permutation walkers, each of which is structurally
     recursive on its own list. Consequence: one fuel unit is spent
     per HNDQ level instead of the F* source's two. Fuel is seeded at
     `bnodes + 1` in both, and in both it is a totality device that no
     real input reaches (each level issues at least one fresh blank
     node), so this is strictly more generous, never less.
  2. Permutation cap. Mirrored from F*, NOT silently: each bucket's
     related-blank-node list is truncated to `permutationCap = 6`
     members before permuting (`720` permutations per bucket). A
     dataset with a symmetric collision bucket wider than 6 therefore
     gets a RESULT VARIANT, not the spec's answer. See
     `permutationCap` for the full statement.
  3. Work budget. Mirrored from F*: `hndqBudget` counts calls to Hash
     N-Degree Quads and makes the §4.4 "excessive calls" abort
     explicit (`canonicalizeExceedsBudget`), so a poison input is a
     reported abort rather than a wrong answer.
  4. Sorting. F* uses a merge sort (its inputs reach 100k+ lines).
     Here sorting is a STABLE INSERTION SORT: the same total preorder,
     the same stable tie-breaking, and short enough to prove sorted
     (`RDF/CanonicalTheorems.lean`). The whole W3C corpus is under 50
     lines per file.
  5. Not ported: the F* module's Section 6b/6c "bounded neighbour
     hash" ladder (`compute_all_nbr1`/`nbr2`/`nbr3`, `bn_full_key`,
     `sort_full_keys`). Those are dead code in the F* tree — an
     earlier phase's approximation of HNDQ, no longer reachable from
     `build_canonical_mapping_alg_budgeted`. Grep-confirmed before
     omitting them.
  6. Not ported: the F* performance machinery whose only purpose is
     the OCaml extraction's cost model (byte-level `fs_byte_at`
     scanning, the `bn_lookup_tree` balanced BST for relabelling, the
     accumulator/`rev` rewrites of every list build). The spec/engine
     split of this Lean tree keeps the specification evaluator plain.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.RDF.Canonical

open L4Factoidal.Crypto

/-! ## Code-point ordering

RDFC-1.0 §3 requires the serialised quads to be sorted "in code point
order". The F* source compares UTF-8 BYTES (and documents why that is
the same relative order: byte-wise comparison of valid UTF-8 agrees
with code-point comparison). Lean strings are already code-point
sequences, so the comparison is direct. -/

/-- Lexicographic ≤ over code-point lists — the total preorder every
sort in this module uses. -/
def charsLe : List Char → List Char → Bool
  | [],      _       => true
  | _ :: _,  []      => false
  | a :: as, b :: bs =>
      if a.val < b.val then true
      else if b.val < a.val then false
      else charsLe as bs

/-- Code-point ≤ over strings (RDFC-1.0 §3, "code point order"). -/
def strLe (a b : String) : Bool := charsLe a.toList b.toList

/-! ## Stable insertion sort

Stability matters: RDFC-1.0 §4.4 step 5.3 orders exploration results
"by hash" but leaves ties undefined, and the F* source resolves them
first-explored-wins. Inserting each element after every element it
compares ≥ to, folding left, reproduces exactly that. -/

/-- Insert `x` after every element `y` of the (already sorted) list
with `le y x`. -/
def insertSortedBy (le : α → α → Bool) (x : α) : List α → List α
  | []      => [x]
  | y :: ys => if le y x then y :: insertSortedBy le x ys else x :: y :: ys

/-- Stable insertion sort under the total preorder `le`. -/
def sortBy (le : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertSortedBy le x acc) []

/-- Sort strings into code-point order (RDFC-1.0 §3). -/
def sortStrings (xs : List String) : List String := sortBy strLe xs

/-- Drop adjacent duplicates from a sorted list — RDF set semantics
(RDF 1.1 Concepts §4: a dataset's quads form a set). The F* source
does this both before hashing (so a repeated quad cannot double a
blank node's first-degree contribution) and on the output lines. -/
def dedupAdj : List String → List String
  | []           => []
  | [x]          => [x]
  | x :: y :: rest =>
      if x == y then dedupAdj (y :: rest) else x :: dedupAdj (y :: rest)

/-- Concatenate a list of strings. -/
def joinStrings (xs : List String) : String := xs.foldl (· ++ ·) ""

/-! ## §3 — canonical N-Quads serialisation

Deliberately NOT reusing `Syntax.NTriples.Term.toNTriples`: that is the
EMIT-MINIMAL wire form (its own module header says so), which escapes
only `\ " \n \r \t`. The canonical form additionally escapes every
remaining C0 control character and DEL as an uppercase-hex `\u00XX`,
and passes non-ASCII through as raw UTF-8. -/

/-- One uppercase hex digit. Out-of-range maps to `'0'` to stay total;
`escapeChar` only ever passes values below 16. -/
def hexDigitUC (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n)
  else if n < 16 then Char.ofNat (0x41 + (n - 10))
  else '0'

/-- The canonical N-Quads escape of one character inside a literal's
lexical form (RDFC-1.0 §3 → N-Triples canonical literal form): the five
short mnemonics plus `\"` and `\\`, every other C0 control character
and DEL as `\u00XX` with UPPERCASE hex, everything else raw. -/
def escapeChar (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '"' then "\\\""
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.val == 0x08 then "\\b"
  else if c.val == 0x0C then "\\f"
  else if c.val < 0x20 || c.val == 0x7F then
    let b := c.val.toNat
    String.ofList ['\\', 'u', '0', '0', hexDigitUC ((b / 16) % 16), hexDigitUC (b % 16)]
  else String.singleton c

/-- Escape a literal's lexical form for canonical N-Quads. -/
def escapeLit (s : String) : String :=
  joinStrings (s.toList.map escapeChar)

/-- Canonical N-Quads form of a subject (RDFC-1.0 §3). -/
def canonSubject : Subject → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b

/-- Canonical N-Quads form of a term (RDFC-1.0 §3; RDF 1.2 triple
terms use the `<<( s p o )>>` form, directional literals the
`--ltr`/`--rtl` suffix). -/
def canonTerm : Term → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .literal wl =>
      let l := wl.val
      let lex := escapeLit l.lexicalForm
      match l.langTag with
      | some tag =>
          let dirSuffix := match l.direction with
            | some .ltr => "--ltr"
            | some .rtl => "--rtl"
            | none      => ""
          "\"" ++ lex ++ "\"@" ++ tag ++ dirSuffix
      | none =>
          if l.datatype == xsdString then "\"" ++ lex ++ "\""
          else "\"" ++ lex ++ "\"^^<" ++ l.datatype.val ++ ">"
  | .tripleTerm s p o =>
      "<<( " ++ canonSubject s ++ " <" ++ p.val ++ "> " ++ canonTerm o ++ " )>>"

/-! ### Blank-node graph names

`RDF.NamedGraph.name` is an `Iri` string in both the F* source and this
port, so the N-Quads parser encodes a blank-node graph label as the
sentinel `"_:label"` (see `Syntax.NQuads.graphLabelToIri`). The
canonical serialiser detects the sentinel and emits it as a blank node
rather than wrapping it in angle brackets. -/

def isBnodeGraphLabel (gi : Iri) : Bool := gi.startsWith "_:"

def bnodeOfGraphLabel (gi : Iri) : BNodeId :=
  if isBnodeGraphLabel gi then String.ofList (gi.toList.drop 2) else gi

def canonGraphName (gi : Iri) : String :=
  if isBnodeGraphLabel gi then "_:" ++ bnodeOfGraphLabel gi else "<" ++ gi ++ ">"

/-! ## Quads with graph names

RDFC-1.0 reasons over quads; the default graph is the `none` graph
name. -/

/-- A quad: an optional graph name plus a triple. -/
abbrev QQuad := Option Iri × Triple

/-- Canonical N-Quads line for one quad, `" .\n"`-terminated
(RDFC-1.0 §3). -/
def canonQuad (q : QQuad) : String :=
  let (g, t) := q
  let gs := match g with
    | some gi => " " ++ canonGraphName gi
    | none    => ""
  canonSubject t.s ++ " <" ++ t.p.val ++ "> " ++ canonTerm t.o ++ gs ++ " .\n"

/-- Flatten a dataset into quads: default graph first, then each named
graph in order. -/
def datasetQuads (ds : Dataset) : List QQuad :=
  ds.default.map (fun t => (none, t)) ++
  ds.named.flatMap (fun ng => ng.graph.map (fun t => (some ng.name, t)))

/-- Sort quads by their canonical rendering and drop duplicates (RDF
set semantics). The F* source does this before hashing so a quad
repeated in the input syntax cannot double a blank node's first-degree
contribution (W3C tests test076 / test077). Ordering the survivors by
rendering also fixes the order in which HNDQ buckets are filled, so
mirroring it exactly matters for tie-breaks. -/
def collapseKeyedQQuads : List (String × QQuad) → List QQuad
  | []            => []
  | [(_, q)]      => [q]
  | (k1, q1) :: (k2, q2) :: rest =>
      if k1 == k2 then collapseKeyedQQuads ((k2, q2) :: rest)
      else q1 :: collapseKeyedQQuads ((k2, q2) :: rest)

def dedupQQuads (qs : List QQuad) : List QQuad :=
  collapseKeyedQQuads (sortBy (fun a b => strLe a.1 b.1) (qs.map (fun q => (canonQuad q, q))))

/-! ## Blank-node enumeration -/

/-- Blank nodes occurring in a term, including inside RDF 1.2 triple
terms (they must be issued canonical identifiers too). -/
def bnodesInTerm : Term → List BNodeId
  | .bnode b          => [b]
  | .tripleTerm s _ o =>
      (match s with | .bnode b => [b] | _ => []) ++ bnodesInTerm o
  | _                 => []

/-- Blank nodes occurring anywhere in a quad: subject, object (
recursively), and the graph-name slot. -/
def bnodesInQuad (q : QQuad) : List BNodeId :=
  let (g, t) := q
  (match t.s with | .bnode b => [b] | _ => []) ++
  bnodesInTerm t.o ++
  (match g with
   | some gi => if isBnodeGraphLabel gi then [bnodeOfGraphLabel gi] else []
   | none    => [])

/-- Sort and deduplicate a list of labels. -/
def dedupStrings (xs : List String) : List String := dedupAdj (sortStrings xs)

/-- Every blank node of the dataset, ascending, without duplicates. -/
def datasetBnodes (ds : Dataset) : List BNodeId :=
  dedupStrings ((datasetQuads ds).flatMap bnodesInQuad)

/-! ## §4.5 — Hash First Degree Quads

"For each quad in which the blank node occurs, serialise it with the
node itself replaced by `_:a` and every other blank node replaced by
`_:z`; sort those serialisations in code point order; concatenate;
hash." The `_:a` / `_:z` placeholders are what makes the result
independent of the input labels. -/

def rewriteSubjectForHfdq (target : BNodeId) : Subject → Subject
  | .bnode b => .bnode (if b == target then "a" else "z")
  | s        => s

def rewriteTermForHfdq (target : BNodeId) : Term → Term
  | .bnode b => .bnode (if b == target then "a" else "z")
  | .tripleTerm s p o =>
      .tripleTerm (rewriteSubjectForHfdq target s) p (rewriteTermForHfdq target o)
  | t        => t

def rewriteTripleForHfdq (target : BNodeId) (t : Triple) : Triple :=
  { s := rewriteSubjectForHfdq target t.s, p := t.p,
    o := rewriteTermForHfdq target t.o }

/-- Graph-name slot under the §4.5 rewrite: own label → `_:a`, another
blank node → `_:z`, IRI graph and default graph unchanged. -/
def rewriteGraphForHfdq (target : BNodeId) : Option Iri → Option Iri
  | none      => none
  | some gi   =>
      if isBnodeGraphLabel gi then
        some (if bnodeOfGraphLabel gi == target then "_:a" else "_:z")
      else some gi

/-- Does this quad mention `target` in any slot? -/
def quadMentionsBnode (target : BNodeId) (q : QQuad) : Bool :=
  let (g, t) := q
  (match t.s with | .bnode b => b == target | _ => false) ||
  (bnodesInTerm t.o).contains target ||
  (match g with
   | some gi => isBnodeGraphLabel gi && bnodeOfGraphLabel gi == target
   | none    => false)

/-- The quads a blank node occurs in, input order preserved. -/
def quadsForBnode (target : BNodeId) (qs : List QQuad) : List QQuad :=
  qs.filter (quadMentionsBnode target)

/-- One quad rendered under the §4.5 placeholder rewrite. -/
def renderForHfdq (target : BNodeId) (q : QQuad) : String :=
  let (g, t) := q
  canonQuad (rewriteGraphForHfdq target g, rewriteTripleForHfdq target t)

/-- RDFC-1.0 §4.5 — Hash First Degree Quads. Parameterised by the hash
algorithm (§4.4 note: SHA-256 is the default; the test manifests select
SHA-384 with `rdfc:hashAlgorithm`). -/
def hashFirstDegreeQuads (alg : HashAlgorithm) (target : BNodeId)
    (qs : List QQuad) : String :=
  hashHex alg (joinStrings (sortStrings ((quadsForBnode target qs).map (renderForHfdq target))))

/-! ## §4.8 — Issue Identifier

An issuer holds a label prefix, a counter, and the identifiers issued
so far. The canonical issuer's prefix is `c14n` (§4.4 step 1: "an
identifier issuer initialized with the prefix `c14n`"); each temporary
issuer cloned during §4.7 uses the prefix `b` (§4.4 step 5.2). The
temporary prefix is spec-visible, not cosmetic: those labels are
embedded in the §4.7 path strings, so using `c14n` for them would
change every N-degree hash. -/

/-- Decimal digits of a natural number, most significant first. -/
def natToDigits (n : Nat) : List Char :=
  if h : n < 10 then [Char.ofNat (0x30 + n)]
  else natToDigits (n / 10) ++ [Char.ofNat (0x30 + n % 10)]
decreasing_by omega

/-- Decimal rendering of a natural number. -/
def natToString (n : Nat) : String := String.ofList (natToDigits n)

/-- The label an issuer with prefix `pfx` mints for counter value `n` —
`c14n0`, `c14n1`, … or `b0`, `b1`, …. Built on the character list so
that `CanonicalTheorems` can reason about it without unfolding
`String.append`. -/
def mkLabel (pfx : String) (n : Nat) : String := String.ofList (pfx.toList ++ natToDigits n)

/-- RDFC-1.0 §4.8 identifier issuer state. -/
structure IssuerState where
  labelPrefix : String
  counter : Nat
  issued  : List (BNodeId × String)
  deriving Repr

/-- The canonical issuer (§4.4 step 1). -/
def emptyIssuer : IssuerState := { labelPrefix := "c14n", counter := 0, issued := [] }

/-- A temporary issuer for one §4.7 exploration (§4.4 step 5.2). -/
def emptyTempIssuer : IssuerState := { labelPrefix := "b", counter := 0, issued := [] }

def lookupIssued (b : BNodeId) : List (BNodeId × String) → Option String
  | []            => none
  | (k, v) :: rest => if k == b then some v else lookupIssued b rest

/-- RDFC-1.0 §4.8: return the existing identifier if this blank node
already has one, otherwise mint the next one and record it. -/
def issueIdentifier (st : IssuerState) (b : BNodeId) : IssuerState × String :=
  match lookupIssued b st.issued with
  | some v => (st, v)
  | none   =>
      let label := mkLabel st.labelPrefix st.counter
      ({ st with counter := st.counter + 1, issued := st.issued ++ [(b, label)] }, label)

/-- Issue without the already-issued check — only used where the
caller has partitioned the blank nodes so that `b` is provably fresh
(`assignSingletons` below: each hash group is disjoint and every
singleton member is visited once). -/
def issueFresh (st : IssuerState) (b : BNodeId) : IssuerState :=
  { st with counter := st.counter + 1, issued := (b, mkLabel st.labelPrefix st.counter) :: st.issued }

/-! ## §4.6 — Hash Related Blank Node -/

/-- RDFC-1.0 §4.6: input is the position tag, then `<predicate>` unless
the position is `g`, then the related node's identifier; hash it. -/
def hashRelatedBlankNode (alg : HashAlgorithm) (pos pred identifier : String) : String :=
  hashHex alg (pos ++ (if pos != "g" then "<" ++ pred ++ ">" else "") ++ identifier)

/-! ## §4.7 — Hash N-Degree Quads -/

/-- One entry of the §4.7 "hash to related blank nodes" map: the §4.6
hash, and the related blank nodes that produced it. -/
abbrev Bucket := String × List BNodeId

/-- Insert `b` under key `k`, keeping the bucket list sorted by key and
each bucket's members in insertion order (§4.7 step 3.1). -/
def bucketInsert (k : String) (b : BNodeId) : List Bucket → List Bucket
  | [] => [(k, [b])]
  | (k', members) :: rest =>
      if k == k' then (k', members ++ [b]) :: rest
      else if strLe k k' then (k, [b]) :: (k', members) :: rest
      else (k', members) :: bucketInsert k b rest

/-- RDFC-1.0 §4.7 step 3.1: every blank-node COMPONENT of an incident
quad other than `target`, tagged with the slot it occupies. One quad
can contribute up to three entries (`_:s <p> _:o _:g` seen from `_:s`
yields an `o` entry and a `g` entry); a quad whose only blank node is
`target` contributes none — it was fully accounted for by §4.5. -/
def graphBnodeOf (q : QQuad) : Option BNodeId :=
  match q.1 with
  | some gi => if isBnodeGraphLabel gi then some (bnodeOfGraphLabel gi) else none
  | none    => none

def relatedComponents (target : BNodeId) (q : QQuad) : List (String × BNodeId) :=
  let (_, t) := q
  (match t.s with | .bnode b => if b != target then [("s", b)] else [] | _ => []) ++
  (match t.o with | .bnode b => if b != target then [("o", b)] else [] | _ => []) ++
  (match graphBnodeOf q with | some b => if b != target then [("g", b)] else [] | none => [])

/-- §4.6 step 3: the identifier of a related node is its canonical
label if it already has one, else this exploration's temporary label,
else its first-degree hash. -/
def lookupIssued2 (b : BNodeId) (canonSt localSt : IssuerState) : Option String :=
  match lookupIssued b canonSt.issued with
  | some lbl => some lbl
  | none     => lookupIssued b localSt.issued

def lookupHfdq (b : BNodeId) : List (BNodeId × String) → String
  | []            => ""
  | (k, h) :: rest => if k == b then h else lookupHfdq b rest

def insertRelatedEntries (alg : HashAlgorithm) (pred : String)
    (hfdqTable : List (BNodeId × String)) (canonSt localSt : IssuerState) :
    List (String × BNodeId) → List Bucket → List Bucket
  | [],              acc => acc
  | (pos, rb) :: rest, acc =>
      let identifier := match lookupIssued2 rb canonSt localSt with
        | some lbl => "_:" ++ lbl
        | none     => lookupHfdq rb hfdqTable
      insertRelatedEntries alg pred hfdqTable canonSt localSt rest
        (bucketInsert (hashRelatedBlankNode alg pos pred identifier) rb acc)

/-- Build the §4.7 "hash to related blank nodes" map for `target`. -/
def buildBucketsFor (alg : HashAlgorithm) (target : BNodeId)
    (hfdqTable : List (BNodeId × String)) (canonSt localSt : IssuerState) :
    List QQuad → List Bucket → List Bucket
  | [],       acc => acc
  | q :: rest, acc =>
      if !quadMentionsBnode target q then
        buildBucketsFor alg target hfdqTable canonSt localSt rest acc
      else
        buildBucketsFor alg target hfdqTable canonSt localSt rest
          (insertRelatedEntries alg q.2.p.val hfdqTable canonSt localSt
            (relatedComponents target q) acc)

/-! ### The permutation loop (§4.7 step 5)

`permutationCap` is a RESULT VARIANT, stated here rather than buried:
RDFC-1.0 §4.7 enumerates EVERY permutation of a bucket's related blank
nodes. Both the F* source and this port truncate the bucket to its
first `permutationCap` members first, so at most `permutationCap!`
permutations are explored. For every dataset in the W3C `rdf-canon`
suite no bucket exceeds this width, so the enumerated set is the
complete one and the result is the spec's. For a symmetric graph with a
wider bucket the output is deterministic and self-consistent but NOT
guaranteed to be the spec's canonical form. Removing the cap requires
either the §4.4 "excessive calls" abort (which `hndqBudget` below
already provides) or a real automorphism search. -/
def permutationCap : Nat := 6

/-- Every way to insert `x` into `ys`, in the F* source's order (front
first) — the order matters because §4.7 step 5.4.5 keeps the FIRST
permutation attaining the lowest hash. -/
def insertAtAll (x : BNodeId) : List BNodeId → List (List BNodeId)
  | []      => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAtAll x ys).map (fun zs => y :: zs)

/-- All permutations of a list, in the F* source's enumeration order.
Structurally recursive, so the "permutations of a list are finite"
bound is the list's own structure — no fuel needed here. -/
def permutationsOf : List BNodeId → List (List BNodeId)
  | []       => [[]]
  | hd :: tl => (permutationsOf tl).foldl (fun acc p => acc ++ insertAtAll hd p) []

/-! ### The §4.4 "excessive calls" budget

RDFC-1.0 §4.4 requires an implementation to be able to abort on inputs
that provoke excessive calls to Hash N-Degree Quads (the W3C suite's
`RDFC10NegativeEvalTest`, e.g. its poison-clique fixture). The budget
counts `hndqRun` invocations and latches once spent, so exploration
unwinds in depth-proportional time instead of continuing a
combinatorial blow-up. -/
structure HndqBudget where
  remaining : Nat
  exceeded  : Bool
  deriving Repr

def hbInit (n : Nat) : HndqBudget := { remaining := n, exceeded := false }

def hbConsume (b : HndqBudget) : HndqBudget :=
  if b.exceeded then b
  else if b.remaining == 0 then { b with exceeded := true }
  else { b with remaining := b.remaining - 1 }

/-- The result triple every step of the §4.7 walk threads: the hash (or
path string) built so far, the temporary issuer, and the budget. -/
abbrev HndqOut := String × IssuerState × HndqBudget

/-- "Run Hash N-Degree Quads one level down", as a closure: takes the
temporary issuer, the target node, and the budget. Passing this
explicitly is what removes the F* source's mutual recursion. -/
abbrev HndqRec := IssuerState → BNodeId → HndqBudget → HndqOut

/-- RDFC-1.0 §4.7 step 5.4.4, first pass over a permutation: every
member contributes its `_:label` — already issued (canonically or
locally) or freshly issued here — concatenated with NO separator.
Members freshly issued here are returned, in order, as the list the
second pass recurses into. -/
def buildPathLabels (canonSt : IssuerState) : IssuerState → List BNodeId → String →
    List BNodeId → String × IssuerState × List BNodeId
  | localSt, [],        path, recursion => (path, localSt, recursion)
  | localSt, b :: rest, path, recursion =>
      match lookupIssued2 b canonSt localSt with
      | some lbl => buildPathLabels canonSt localSt rest (path ++ "_:" ++ lbl) recursion
      | none     =>
          let (local1, lbl) := issueIdentifier localSt b
          buildPathLabels canonSt local1 rest (path ++ "_:" ++ lbl) (recursion ++ [b])

/-- RDFC-1.0 §4.7 step 5.4.5, second pass: recurse into each freshly
issued member, appending `_:<label><recursive hash>`. -/
def walkRecursion (rec : HndqRec) : IssuerState → List BNodeId → String → HndqBudget → HndqOut
  | localSt, [],        path, hb => (path, localSt, hb)
  | localSt, b :: rest, path, hb =>
      if hb.exceeded then (path, localSt, hb)
      else
        -- `b` was issued by `buildPathLabels`; `issueIdentifier` is
        -- idempotent, so this recovers the same label.
        let (local1, lbl) := issueIdentifier localSt b
        let (subHash, local2, hb1) := rec local1 b hb
        walkRecursion rec local2 rest (path ++ "_:" ++ lbl ++ "<" ++ subHash ++ ">") hb1

/-- One permutation: label pass, then recursion pass (§4.7 step 5.4). -/
def walkPerm (rec : HndqRec) (canonSt localSt : IssuerState) (perm : List BNodeId)
    (path : String) (hb : HndqBudget) : HndqOut :=
  let (path1, local1, recursion) := buildPathLabels canonSt localSt perm path []
  walkRecursion rec local1 recursion path1 hb

/-- Keep the lowest path hash, first one wins on a tie (§4.7 step
5.4.6 orders by hash; the tie is left open by the spec and settled
first-explored-wins, matching the F* source). -/
def pickBest (rec : HndqRec) (canonSt localStInitial : IssuerState) :
    List (List BNodeId) → String → IssuerState → HndqBudget → HndqOut
  | [],       bestHash, bestSt, hb => (bestHash, bestSt, hb)
  | p :: rest, bestHash, bestSt, hb =>
      if hb.exceeded then (bestHash, bestSt, hb)
      else
        let (h, st', hb1) := walkPerm rec canonSt localStInitial p "" hb
        let (bestHash', bestSt') :=
          if strLe h bestHash && h != bestHash then (h, st') else (bestHash, bestSt)
        pickBest rec canonSt localStInitial rest bestHash' bestSt' hb1

/-- §4.7 step 5.4: explore every permutation of one bucket. -/
def bestPermutation (rec : HndqRec) (canonSt localSt : IssuerState)
    (perms : List (List BNodeId)) (hb : HndqBudget) : HndqOut :=
  match perms with
  | []       => ("", localSt, hb)
  | p :: rest =>
      if hb.exceeded then ("", localSt, hb)
      else
        let (h, st', hb1) := walkPerm rec canonSt localSt p "" hb
        pickBest rec canonSt localSt rest h st' hb1

/-- §4.7 step 5: walk the buckets in key order, appending each key and
its winning permutation hash to the data-to-hash string; hash the
result (§4.7 step 6). -/
def walkBuckets (alg : HashAlgorithm) (rec : HndqRec) (canonSt : IssuerState) :
    IssuerState → List Bucket → String → HndqBudget → HndqOut
  | localSt, [],                 data, hb => (hashHex alg data, localSt, hb)
  | localSt, (k, members) :: rest, data, hb =>
      if hb.exceeded then (hashHex alg data, localSt, hb)
      else
        let perms := permutationsOf (members.take permutationCap)
        let (bestHash, bestSt, hb1) := bestPermutation rec canonSt localSt perms hb
        walkBuckets alg rec canonSt bestSt rest (data ++ k ++ bestHash) hb1

/-- RDFC-1.0 §4.7 — Hash N-Degree Quads.

Totality: structural recursion on `fuel`. `fuel` is seeded at
`|blank nodes| + 1`; each level issues at least one previously
unissued blank node, so no real input reaches the `0` case (it returns
the empty hash, the same defensive answer the F* source gives). The
permutation enumeration inside a level is bounded by the structure of
the (capped) bucket list, not by fuel. -/
def hndqRun (alg : HashAlgorithm) (qs : List QQuad) (hfdqTable : List (BNodeId × String))
    (canonSt : IssuerState) : Nat → IssuerState → BNodeId → HndqBudget → HndqOut
  | 0,        localSt, _,      hb => ("", localSt, hbConsume hb)
  | fuel + 1, localSt, target, hb =>
      let hb1 := hbConsume hb
      if hb1.exceeded then ("", localSt, hb1)
      else
        let buckets := buildBucketsFor alg target hfdqTable canonSt localSt qs []
        walkBuckets alg (hndqRun alg qs hfdqTable canonSt fuel) canonSt localSt buckets "" hb1

/-! ## §4.4 — the canonicalization algorithm -/

/-- The §4.4 "hash to blank nodes" map: blank nodes grouped by their
first-degree hash, groups in code-point order of the hash, members in
ascending label order (which is `datasetBnodes`' order — a stable sort
keeps it). -/
def groupSortedHfdq : List (BNodeId × String) → String → List BNodeId → List Bucket →
    List Bucket
  | [],             curH, curMembers, acc => ((curH, curMembers.reverse) :: acc).reverse
  | (b, h) :: rest, curH, curMembers, acc =>
      if h == curH then groupSortedHfdq rest curH (b :: curMembers) acc
      else groupSortedHfdq rest h [b] ((curH, curMembers.reverse) :: acc)

def groupByHfdq (table : List (BNodeId × String)) : List Bucket :=
  match sortBy (fun a b => strLe a.2 b.2) table with
  | []               => []
  | (b0, h0) :: rest => groupSortedHfdq rest h0 [b0] []

/-- §4.4 step 4: every blank node whose first-degree hash is unique
gets its canonical identifier now, in hash order. This whole pass runs
BEFORE step 5 — interleaving the two would hand out different absolute
`c14nN` numbers whenever a unique hash sorts between two colliding
ones. -/
def assignSingletons (st : IssuerState) : List Bucket → IssuerState
  | []                => st
  | (_, [b]) :: rest  => assignSingletons (issueFresh st b) rest
  | (_, _) :: rest    => assignSingletons st rest

def filterUnissued (st : IssuerState) (xs : List BNodeId) : List BNodeId :=
  xs.filter (fun b => (lookupIssued b st.issued).isNone)

/-- §4.4 step 5.2: explore EVERY not-yet-issued member of a collision
group, each with its own fresh temporary issuer (only the canonical
issuer is shared, and only read). -/
def exploreMembers (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) (canonSt : IssuerState) :
    List BNodeId → HndqBudget → List (String × List (BNodeId × String)) × HndqBudget
  | [],       hb => ([], hb)
  | m :: rest, hb =>
      if hb.exceeded then ([], hb)
      else match lookupIssued m canonSt.issued with
        | some _ => exploreMembers alg fuel qs hfdqTable canonSt rest hb
        | none   =>
            let (local1, _) := issueIdentifier emptyTempIssuer m
            let (h, local2, hb1) := hndqRun alg qs hfdqTable canonSt fuel local1 m hb
            let (restResults, hb2) := exploreMembers alg fuel qs hfdqTable canonSt rest hb1
            ((h, local2.issued) :: restResults, hb2)

/-- §4.4 step 5.3: in ascending-hash order, replay every identifier the
winning exploration touched into the canonical issuer. -/
def replayOne (canonSt : IssuerState) : List (BNodeId × String) → IssuerState
  | []            => canonSt
  | (b, _) :: rest => replayOne (issueIdentifier canonSt b).1 rest

def replayAll (canonSt : IssuerState) :
    List (String × List (BNodeId × String)) → IssuerState
  | []                  => canonSt
  | (_, tempIssued) :: rest => replayAll (replayOne canonSt tempIssued) rest

def processCollisionMembers (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) (st : IssuerState) (members : List BNodeId)
    (hb : HndqBudget) : IssuerState × HndqBudget :=
  let (results, hb1) := exploreMembers alg fuel qs hfdqTable st members hb
  (replayAll st (sortBy (fun a b => strLe a.1 b.1) results), hb1)

/-- §4.4 step 5: the collision groups, in hash order. -/
def processCollisionGroups (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) :
    IssuerState → List Bucket → HndqBudget → IssuerState × HndqBudget
  | st, [],                   hb => (st, hb)
  | st, (_, [_]) :: rest,     hb => processCollisionGroups alg fuel qs hfdqTable st rest hb
  | st, (_, members) :: rest, hb =>
      if hb.exceeded then (st, hb)
      else
        let (st', hb1) :=
          processCollisionMembers alg fuel qs hfdqTable st (filterUnissued st members) hb
        processCollisionGroups alg fuel qs hfdqTable st' rest hb1

/-- §4.4 steps 4 and 5, in that order. -/
def walkGroups (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) (st : IssuerState) (groups : List Bucket)
    (hb : HndqBudget) : IssuerState × HndqBudget :=
  processCollisionGroups alg fuel qs hfdqTable (assignSingletons st groups) groups hb

/-! ## Public entry points -/

/-- Practically unbounded budget for ordinary use. The whole W3C
`rdf-canon` corpus is orders of magnitude below it; only deliberately
pathological inputs reach it. -/
def defaultHndqBudget : Nat := 1000000

/-- The first-degree hash of every blank node, in ascending label
order (§4.4 step 3). -/
def hfdqTableOf (alg : HashAlgorithm) (ds : Dataset) (qs : List QQuad) :
    List (BNodeId × String) :=
  (datasetBnodes ds).map (fun b => (b, hashFirstDegreeQuads alg b qs))

/-- The full §4.4 run under an explicit Hash-N-Degree-Quads budget.
`none` means the budget was spent before every blank node had a
canonical identifier — the §4.4 "excessive calls to Hash N-Degree
Quads" abort. -/
def buildCanonicalMappingBudgeted (alg : HashAlgorithm) (budget : Nat) (ds : Dataset) :
    Option (List (BNodeId × String)) :=
  let qs := dedupQQuads (datasetQuads ds)
  let bs := datasetBnodes ds
  let hfdqTable := hfdqTableOf alg ds qs
  let groups := groupByHfdq hfdqTable
  let (st, hb) := walkGroups alg (bs.length + 1) qs hfdqTable emptyIssuer groups (hbInit budget)
  if hb.exceeded then none
  else
    -- Defensive: any blank node still unissued (only reachable through
    -- fuel exhaustion) gets an identifier in (hash, label) order.
    let leftover := if st.issued.length == bs.length then [] else filterUnissued st bs
    let leftoverSorted :=
      sortBy (fun a b => if a.2 == b.2 then strLe a.1 b.1 else strLe a.2 b.2)
        (leftover.map (fun b => (b, lookupHfdq b hfdqTable)))
    some (leftoverSorted.foldl (fun s p => (issueIdentifier s p.1).1) st).issued

/-- The blank-node label map: original label → `c14nN`. -/
def buildCanonicalMapping (alg : HashAlgorithm := .sha256) (ds : Dataset) :
    List (BNodeId × String) :=
  (buildCanonicalMappingBudgeted alg defaultHndqBudget ds).getD []

/-- True when canonicalization under `budget` aborted for excessive
calls to Hash N-Degree Quads — the W3C suite's `RDFC10NegativeEvalTest`
criterion. Use a budget well below `defaultHndqBudget` so a
pathological input aborts promptly. -/
def canonicalizeExceedsBudget (alg : HashAlgorithm) (budget : Nat) (ds : Dataset) : Bool :=
  (buildCanonicalMappingBudgeted alg budget ds).isNone

/-! ### Applying the map -/

def lookupMap (b : BNodeId) : List (BNodeId × String) → Option String
  | []             => none
  | (k, v) :: rest => if k == b then some v else lookupMap b rest

def relabelSubject (m : List (BNodeId × String)) : Subject → Subject
  | .bnode b => match lookupMap b m with | some l => .bnode l | none => .bnode b
  | s        => s

def relabelTerm (m : List (BNodeId × String)) : Term → Term
  | .bnode b => match lookupMap b m with | some l => .bnode l | none => .bnode b
  | .tripleTerm s p o => .tripleTerm (relabelSubject m s) p (relabelTerm m o)
  | t => t

def relabelTriple (m : List (BNodeId × String)) (t : Triple) : Triple :=
  { s := relabelSubject m t.s, p := t.p, o := relabelTerm m t.o }

/-- Canonical labels are stored bare (`c14n0`); the `"_:"` sentinel is
re-attached when writing back into the `Iri`-typed graph-name slot. -/
def relabelGraphName (m : List (BNodeId × String)) (gi : Iri) : Iri :=
  if isBnodeGraphLabel gi then
    match lookupMap (bnodeOfGraphLabel gi) m with
    | some l => "_:" ++ l
    | none   => gi
  else gi

def relabelDataset (m : List (BNodeId × String)) (ds : Dataset) : Dataset :=
  { default := ds.default.map (relabelTriple m),
    named := ds.named.map (fun ng =>
      { name := relabelGraphName m ng.name, graph := ng.graph.map (relabelTriple m) }) }

/-! ### Canonical N-Quads output -/

/-- The canonical N-Quads LINES of an already-relabelled dataset:
render every quad, sort in code point order (RDFC-1.0 §3), drop
duplicates (RDF set semantics). -/
def canonicalLinesOf (ds : Dataset) : List String :=
  dedupAdj (sortStrings ((datasetQuads ds).map canonQuad))

/-- What `canonicalize` returns: the canonical N-Quads text and the
issued label map. -/
structure CanonResult where
  /-- The canonical N-Quads document (RDFC-1.0 §3 sorted form). -/
  nquads : String
  /-- The `rdfc10map` relation: original blank-node label → canonical
  identifier, WITHOUT the `_:` prefix, in ascending original-label
  order. -/
  issued : List (BNodeId × String)
  /-- True when the run hit the §4.4 excessive-calls abort; `nquads`
  and `issued` are then the un-canonicalised fallback. -/
  aborted : Bool
  deriving Repr

/-- RDFC-1.0 §4.4 — canonicalize a dataset. Default algorithm SHA-256
(§4.4 note 2); the W3C manifests select SHA-384 for some entries via
`rdfc:hashAlgorithm`. -/
def canonicalize (ds : Dataset) (alg : HashAlgorithm := .sha256) : CanonResult :=
  match buildCanonicalMappingBudgeted alg defaultHndqBudget ds with
  | none => { nquads := joinStrings (canonicalLinesOf ds), issued := [], aborted := true }
  | some m =>
      { nquads  := joinStrings (canonicalLinesOf (relabelDataset m ds)),
        issued  := sortBy (fun a b => strLe a.1 b.1) m,
        aborted := false }

/-- The canonical N-Quads document of a dataset. -/
def _root_.L4Factoidal.RDF.Dataset.canonicalNQuads
    (ds : Dataset) (alg : HashAlgorithm := .sha256) : String :=
  (canonicalize ds alg).nquads

/-- The canonical N-Quads LINES of a dataset — the sorted list the
`nquads` field concatenates. Exposed so the sortedness theorem in
`RDF/CanonicalTheorems.lean` has something to talk about. -/
def _root_.L4Factoidal.RDF.Dataset.canonicalLines
    (ds : Dataset) (alg : HashAlgorithm := .sha256) : List String :=
  match buildCanonicalMappingBudgeted alg defaultHndqBudget ds with
  | none   => canonicalLinesOf ds
  | some m => canonicalLinesOf (relabelDataset m ds)

/-- The hash of the canonical N-Quads document — the `canonicalHash`
API of the rdf-canonize implementations. -/
def _root_.L4Factoidal.RDF.Dataset.canonicalHash
    (ds : Dataset) (alg : HashAlgorithm := .sha256) : String :=
  hashHex alg (ds.canonicalNQuads alg)

end L4Factoidal.RDF.Canonical
