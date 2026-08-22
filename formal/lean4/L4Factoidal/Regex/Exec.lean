/-
L4Factoidal.Regex.Exec — the executable path: ACI-normalised derivatives,
unanchored search, the codepoint-class alphabet partition, and a
fuel-bounded language-emptiness check.

Port of `formal/fstar/Regex.Exec.fst` (issue #304, phases 1–2). The F*
module is the IMPLEMENTATION-PRAGMATICS tier of the regex engine; it is
pure, total code and is ported in full because its normalised derivative
`nderiv` is what every consumer (XSD facets, CSVW, fn:matches,
fn:replace) actually runs, and because its correctness is proven:
`nderiv_correct` / `acceptsNorm_correct` / `acceptsNorm_eq_proven` in
`RegexTheorems.lean` show the fast path denotes exactly the reference
language `mem`, the same claim the F* discharges.

What is NOT machine-checked, here as in the F*: the emptiness check
`isEmpty` explores the reachable normalised-derivative states over the
class-representative alphabet, breadth-first, under a fuel budget. Its
per-step transition is the proven `nderiv`, but full soundness also
needs a derivative-class-COVERAGE lemma (that `classReps` and the BFS
enumerate every reachable derivative up to language equality — the
Owens–Reppy–Turon finiteness argument). That lemma is open in the F*
tree too (#304 phase-2 residual) and is not claimed here.
-/
import L4Factoidal.Regex.Derivative

namespace L4Factoidal.Regex.Exec

open Re

/-! ## Full ACI normalisation for alt / inter (Owens–Reppy–Turon)

`smartAlt` / `smartAnd` canonicalise ONE binary node. The derivative
state set is only finite once nested alternation is flattened into a
sorted, deduplicated leaf set (associativity + commutativity +
idempotence); without this the classic `(a?)^n a^n` chain grows
exponentially. -/

/-- Sorted insertion into a leaf list; a structurally-equal leaf
(`reCmp = .eq`) is dropped (F* `insert_regex`). -/
def insertRegex (x : Re) : List Re → List Re
  | [] => [x]
  | y :: ys =>
    match reCmp x y with
    | .eq => y :: ys
    | .lt => x :: y :: ys
    | .gt => y :: insertRegex x ys

/-- Flatten an alt tree, dropping `empty` (identity of union), into a
sorted deduplicated leaf list (F* `alt_flatten`). -/
def altFlatten : Re → List Re → List Re
  | .empty, acc => acc
  | .alt a b, acc => altFlatten a (altFlatten b acc)
  | r, acc => insertRegex r acc

/-- Flatten an inter tree, dropping the universal language (identity of
intersection), into a sorted deduplicated leaf list (F* `and_flatten`). -/
def andFlatten : Re → List Re → List Re
  | .inter a b, acc => andFlatten a (andFlatten b acc)
  | r, acc => if r = rUniversal then acc else insertRegex r acc

def hasUniversal : List Re → Bool
  | [] => false
  | y :: ys => (y = rUniversal) || hasUniversal ys

def hasEmpty : List Re → Bool
  | [] => false
  | y :: ys => (y = .empty) || hasEmpty ys

def rebuildAlt : List Re → Re
  | [] => .empty
  | [x] => x
  | x :: rest => .alt x (rebuildAlt rest)

def rebuildAnd : List Re → Re
  | [] => rUniversal
  | [x] => x
  | x :: rest => .inter x (rebuildAnd rest)

/-- Canonical union: flatten, dedup, sort; universal absorbs (F* `ealt`). -/
def ealt (a b : Re) : Re :=
  let leaves := altFlatten a (altFlatten b [])
  if hasUniversal leaves then rUniversal else rebuildAlt leaves

/-- Canonical intersection: flatten, dedup, sort; `empty` absorbs
(F* `eand`). -/
def eand (a b : Re) : Re :=
  let leaves := andFlatten a (andFlatten b [])
  if hasEmpty leaves then .empty else rebuildAnd leaves

/-! ## Normalised derivative (ACI-flattened alt / inter, `smartCat`) -/

/-- The normalised derivative (F* `nderiv`). Proven language-correct in
`RegexTheorems.lean` (`nderiv_correct`). -/
def nderiv (c : Nat) : Re → Re
  | .empty     => .empty
  | .eps       => .empty
  | .ranges rs => if inRanges c rs then .eps else .empty
  | .alt a b   => ealt (nderiv c a) (nderiv c b)
  | .inter a b => eand (nderiv c a) (nderiv c b)
  | .compl a   => smartNot (nderiv c a)
  | .cat a b   =>
    let left := smartCat (nderiv c a) b
    if nullable a then ealt left (nderiv c b) else left
  | .star a    => smartCat (nderiv c a) (.star a)

/-! ## Anchored matching -/

/-- Tail-recursive fold of the proven derivative over the word
(F* `run_word`). -/
def runWord (r : Re) : List Nat → Re
  | [] => r
  | c :: rest => runWord (Derivative.deriv c r) rest

/-- `matches r w = mem r w` (F* `Regex.Exec.matches`; same function as
`Derivative.matches`). -/
def accepts (r : Re) (w : List Nat) : Bool := nullable (runWord r w)

/-- Same shape with the normalised derivative (F* `run_word_norm`). -/
def runWordNorm (r : Re) : List Nat → Re
  | [] => r
  | c :: rest => runWordNorm (nderiv c r) rest

/-- Whole-word matching on the state-finite fast path (F* `matches_norm`).
`acceptsNorm_correct : acceptsNorm r w = mem r w`. -/
def acceptsNorm (r : Re) (w : List Nat) : Bool := nullable (runWordNorm r w)

/-! ## Unanchored search -/

/-- The class of all codepoints, one range `[0, maxCodepoint]`
(F* `any_char`). -/
def anyChar : Re := .ranges [(0, maxCodepoint)]

/-- `.*` (F* `dot_star`). -/
def dotStar : Re := .star anyChar

/-- `.* r .*` — the unanchored-search reduction (F* `contains`). -/
def contains (r : Re) : Re := .cat dotStar (.cat r dotStar)

/-- Does some substring of `w` match `r`? (F* `search`). -/
def search (r : Re) (w : List Nat) : Bool := acceptsNorm (contains r) w

/-- `r .*` (F* `anchored_prefix`). -/
def anchoredPrefix (r : Re) : Re := .cat r dotStar

/-- Leftmost start index at which `r` matches some prefix of the remaining
word (F* `find_from`). -/
def findFrom (r : Re) : List Nat → Nat → Option Nat
  | w, idx =>
    if acceptsNorm (anchoredPrefix r) w then some idx
    else match w with
      | [] => none
      | _ :: rest => findFrom r rest (idx + 1)

def findMatch (r : Re) (w : List Nat) : Option Nat := findFrom r w 0

/-! ## Codepoint-class alphabet partition

Every derivative class of a regex is determined by the range endpoints
appearing in it: two codepoints in the same maximal gap between
endpoints have identical derivatives. `classReps r` returns one
representative codepoint per class. -/

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x = y then y :: ys
               else if x < y then x :: y :: ys
               else y :: insertSorted x ys

def collectRangeBounds : List (Nat × Nat) → List Nat → List Nat
  | [], acc => acc
  | (lo, hi) :: tl, acc =>
    let acc1 := insertSorted lo acc
    let acc2 := if hi + 1 ≤ maxCodepoint then insertSorted (hi + 1) acc1 else acc1
    collectRangeBounds tl acc2

def collectBounds : Re → List Nat → List Nat
  | .empty, acc => acc
  | .eps, acc => acc
  | .ranges rs, acc => collectRangeBounds rs acc
  | .cat a b, acc => collectBounds b (collectBounds a acc)
  | .alt a b, acc => collectBounds b (collectBounds a acc)
  | .inter a b, acc => collectBounds b (collectBounds a acc)
  | .compl a, acc => collectBounds a acc
  | .star a, acc => collectBounds a acc

/-- Representative codepoints: 0, every range endpoint, and `maxCodepoint`
(F* `class_reps`). -/
def classReps (r : Re) : List Nat :=
  insertSorted 0 (insertSorted maxCodepoint (collectBounds r []))

/-! ## Fuel-bounded emptiness over the normalised-derivative closure

GUARANTEE (precise, as stated at the F* `is_empty`): `isEmpty r` returns
`false` as soon as it reaches ANY nullable state (a witnessed accepting
path exists) OR when the fuel runs out before the closure completes
(conservative "not proven empty"); it returns `true` only when the
worklist drains with no nullable state reached. -/

def memState (r : Re) : List Re → Bool
  | [] => false
  | y :: ys => (r = y) || memState r ys

def succStates (r : Re) : List Nat → List Re
  | [] => []
  | c :: cs => nderiv c r :: succStates r cs

def addNew : List Re → List Re → List Re → List Re × List Re
  | [], visited, worklist => (visited, worklist)
  | s :: rest, visited, worklist =>
    if memState s visited then addNew rest visited worklist
    else addNew rest (s :: visited) (s :: worklist)

def bfsEmpty (reps : List Nat) : Nat → List Re → List Re → Bool
  | 0, _, _ => false
  | fuel + 1, worklist, visited =>
    match worklist with
    | [] => true
    | s :: rest =>
      if nullable s then false
      else
        let succs := succStates s reps
        let (visited', worklist') := addNew succs visited rest
        bfsEmpty reps fuel worklist' visited'

/-- Language emptiness, fuel tied to the regex size (F* `is_empty`). -/
def isEmpty (r : Re) : Bool :=
  let reps := classReps r
  let fuel := 1000 * (r.size + 1)
  bfsEmpty reps fuel [r] [r]

/-- Are there NO strings matching both `p` and `q`? (F* `intersection_empty`). -/
def intersectionEmpty (p q : Re) : Bool := isEmpty (.inter p q)

/-- Does the language of `p` contain that of `q`? `q ∧ ¬p` empty
(F* `subsumes`). -/
def subsumes (p q : Re) : Bool := isEmpty (.inter q (.compl p))

end L4Factoidal.Regex.Exec
