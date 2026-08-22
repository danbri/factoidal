/-
L4Factoidal.Regex.XPath — XPath/XQuery F&O `fn:matches` and `fn:replace`
on the verified codepoint engine, and the public API the SPARQL
evaluator calls for `REGEX` (SPARQL 1.1 §17.4.3.14) and `REPLACE`
(§17.4.3.15).

Port of the regex block of `formal/fstar/SPARQL11.Algebra.fst`
(`regex_match`, lines 1331–1531, issue #304 phase 4; `regex_replace` and
its capturing matcher, lines 1533–1992, phase 5). The F* keeps those
functions inside the SPARQL algebra module because they retired two
`assume val`s that lived there; the Lean port places them with the
engine, where the SPARQL evaluator (`SPARQL/Expr.lean`) imports them.

fn:matches (https://www.w3.org/TR/xpath-functions-31/#func-matches) is
an UNANCHORED substring test with flags `i s m x q`. The XSD parser
reads a pattern as WHOLE-STRING membership and treats `^` / `$` as
no-ops, so both the real anchors and the "somewhere in the string"
wrapping are applied HERE, exactly as the F* does:

  * `^` / `$` get REAL anchor semantics by a sentinel encoding: the
    INPUT word is wrapped in two sentinel codepoints above
    `maxCodepoint` (BEGIN, END) that no real character, `.` or class
    can match; each unescaped, out-of-class `^` / `$` in the PATTERN is
    replaced by the BEGIN / END codepoint, which the parser then reads
    as an ordinary literal — so anchors compose correctly through
    alternation, groups and quantifiers (`^a|b$` anchors each branch);
  * the search is `gapLeft · P' · gapRight`, where the gaps consume the
    BEGIN sentinel + a real-character run on the left and a
    real-character run + the END sentinel on the right, or nothing
    (when `P'` itself consumed a sentinel).

Flag coverage, as in the F*:
  `i` ASCII case-folding of literal ranges (`foldCi`) — non-ASCII case
      folding is NOT applied (documented gap, both trees);
  `s` `.` also matches #xA / #xD (`dotAll`);
  `x` unescaped, out-of-class whitespace elided before parsing
      (`stripWs`);
  `q` the whole pattern is a literal codepoint sequence
      (`literalRegex`);
  `m` in the F*: ACCEPTED but treated as string-level anchoring (`^` /
      `$` match the string start / end, not interior line boundaries),
      which fails the W3C `sparql10/regex` test
      `regex-start-end-multiline` (`^b$` with `m` on `"a\nb\nc"`).
      The Lean `compile` / `isMatch` IMPLEMENT it, with the same
      sentinel machinery extended to line boundaries: the input is
      wrapped as `B l₁ E \n B l₂ E \n … E` (a BEGIN / END sentinel
      pair around every line), every non-sentinel leaf of the pattern
      is allowed to absorb sentinel runs on either side (`absorbMarkers`,
      so `a.*c` with `sm` still crosses lines), and the search gaps
      accept any codepoint including sentinels. `regexMatch` keeps the
      F* behaviour for side-by-side comparison.

fn:replace (https://www.w3.org/TR/xpath-functions-31/#func-replace):
  * WHOLE-MATCH SPANS are found by the verified engine: at each
    candidate start the normalised derivative runs forward and the
    LONGEST prefix whose residual is nullable is taken
    (leftmost-longest, non-overlapping, left to right). This agrees
    with XQuery ordered-alternation greedy semantics on every corpus
    pattern (e.g. `(ab)|(a)`); it would differ only when an earlier
    alternative is a proper prefix of a later one (`(a)|(ab)`).
  * GROUP CAPTURE for `$N` is computed by a total, fuel-bounded
    capturing matcher (`cmatch`) over a capturing AST (`CRe`) parsed by
    `parseCapturing`, which reuses the XSD parser's leaf builders so
    its language agrees with the span-finding regex by construction.
    Every leaf accept / reject is decided by the verified engine
    (`leafEnds`). The capturing matcher only EXPLAINS how the verified
    span decomposes into numbered groups (filtered to outcomes ending
    exactly at the verified span end); it never overrides the span.
  * Template grammar: `$d` (single digit) → group d's text (`$0` = the
    whole match; a non-participating group → ""); `\$` → `$`; `\\` →
    `\`. Multi-digit `$12` reads as `$1` then `2`, as in the F*.
  * `^` / `$` in a replace pattern parse to eps (no-op), as in the F*
    (no fixture exercises them).

Deviations from the F* (all in the DIRECTION of the XPath spec, and
confined to the error channel the F* functions do not have):
  * `compile` reports an unknown flag character (err:FORX0001) and an
    unparseable pattern (err:FORX0002) as `RegexError`s; the F*
    `regex_match` returns `false` and `regex_replace` returns the input
    unchanged. `regexMatch` / `regexReplace` below keep the F*
    behaviour for side-by-side comparison.
  * `replace` reports a pattern that matches the empty string
    (err:FORX0003) and an ill-formed replacement template — `\` not
    followed by `\` or `$`, or `$` not followed by a digit
    (err:FORX0004). The F* copies one codepoint through on an empty
    match and expands `\c` to `c`.
-/
import L4Factoidal.Regex.Exec
import L4Factoidal.Regex.XSDPattern

namespace L4Factoidal.Regex

open XSDPattern (cpCaret cpDollar cpBackslash cpLbracket cpRbracket)

/-! ## Flags -/

/-- Is the flag character present? (F* `rx_flag_has`). -/
def flagHas (flags : String) (ch : Char) : Bool := flags.toList.contains ch

/-- Is `c` an XML / XSD whitespace codepoint (#x9 #xA #xD #x20)? -/
def isWs (c : Nat) : Bool := c = 0x09 || c = 0x0A || c = 0x0D || c = 0x20

/-- `x` flag: drop whitespace that is neither escaped nor inside a
character class (F* `rx_strip_ws`). -/
def stripWs : List Nat → Bool → List Nat
  | [], _ => []
  | c :: t, inClass =>
    if c = cpBackslash then
      match t with
      | c2 :: t2 => c :: c2 :: stripWs t2 inClass
      | [] => [c]
    else if c = cpLbracket && !inClass then c :: stripWs t true
    else if c = cpRbracket && inClass then c :: stripWs t false
    else if isWs c && !inClass then stripWs t inClass
    else c :: stripWs t inClass

/-! ## Real anchors via sentinel encoding -/

def beginSentinel : Nat := maxCodepoint + 1
def endSentinel   : Nat := maxCodepoint + 2

/-- Replace unescaped, out-of-class `^` / `$` with the BEGIN / END
sentinel codepoints (F* `rx_replace_anchors`). -/
def replaceAnchors : List Nat → Bool → List Nat
  | [], _ => []
  | c :: t, inClass =>
    if c = cpBackslash then
      match t with
      | c2 :: t2 => c :: c2 :: replaceAnchors t2 inClass
      | [] => [c]
    else if c = cpLbracket && !inClass then c :: replaceAnchors t true
    else if c = cpRbracket && inClass then c :: replaceAnchors t false
    else if c = cpCaret && !inClass then beginSentinel :: replaceAnchors t inClass
    else if c = cpDollar && !inClass then endSentinel :: replaceAnchors t inClass
    else c :: replaceAnchors t inClass

/-- Any real codepoint — EXCLUDES the two sentinels (F* `rx_nonsent`). -/
def nonSent : Re := .ranges [(0, maxCodepoint)]

/-- Consumes the leading BEGIN sentinel plus a real-character prefix, or
nothing (F* `rx_gap_left`). -/
def gapLeft : Re :=
  .alt .eps (.cat (.ranges [(beginSentinel, beginSentinel)]) (.star nonSent))

/-- Consumes a real-character suffix plus the trailing END sentinel, or
nothing (F* `rx_gap_right`). -/
def gapRight : Re :=
  .alt .eps (.cat (.star nonSent) (.ranges [(endSentinel, endSentinel)]))

/-- Multiline (`m` flag) support — NOT in the F*, see the module header.
The sentinel leaf pair as one class. -/
def markerClass : Re := .ranges [(beginSentinel, beginSentinel), (endSentinel, endSentinel)]

/-- Any codepoint INCLUDING the sentinels: the search gap in `m` mode. -/
def sigmaAllStar : Re := .star (.ranges [(0, endSentinel)])

/-- Is this leaf one of the two anchor sentinels the parser produced? -/
def isSentinelLeaf : List (Nat × Nat) → Bool
  | [(lo, hi)] => (lo = beginSentinel && hi = beginSentinel) || (lo = endSentinel && hi = endSentinel)
  | _ => false

/-- `m` mode: let every non-anchor leaf absorb sentinel runs on either
side, so a match may span the per-line sentinels the input carries
(`a.*c` with `sm` on `"a\nb\nc"`), while an anchor leaf still has to
sit exactly on a sentinel. -/
def absorbMarkers : Re → Re
  | .empty => .empty
  | .eps => .eps
  | .ranges rs =>
    if isSentinelLeaf rs then .ranges rs
    else .cat (.star markerClass) (.cat (.ranges rs) (.star markerClass))
  | .cat a b => .cat (absorbMarkers a) (absorbMarkers b)
  | .alt a b => .alt (absorbMarkers a) (absorbMarkers b)
  | .inter a b => .inter (absorbMarkers a) (absorbMarkers b)
  | .compl a => .compl (absorbMarkers a)
  | .star a => .star (absorbMarkers a)

/-- `m` mode input wrapping: a BEGIN / END sentinel pair around every line. -/
def wrapMultiline (cps : List Nat) : List Nat :=
  beginSentinel :: (cps.flatMap fun c => if c = 0x0A then [endSentinel, 0x0A, beginSentinel] else [c]) ++ [endSentinel]

/-- `q` flag: the pattern as a literal codepoint sequence
(F* `rx_literal_regex`). -/
def literalRegex : List Nat → Re
  | [] => .eps
  | [c] => .ranges [(c, c)]
  | c :: t => .cat (.ranges [(c, c)]) (literalRegex t)

/-! ## `i` flag: ASCII case folding of literal ranges -/

/-- The extra intervals a range also accepts under `i`: for the A–Z
overlap add the a–z image (+0x20), for the a–z overlap the A–Z image
(F* `rx_ci_extra`). -/
def ciExtra (lo hi : Nat) : List (Nat × Nat) :=
  let upLo := if lo > 0x41 then lo else 0x41
  let upHi := if hi < 0x5A then hi else 0x5A
  let imgLower := if upLo ≤ upHi then [(upLo + 0x20, upHi + 0x20)] else []
  let loLo := if lo > 0x61 then lo else 0x61
  let loHi := if hi < 0x7A then hi else 0x7A
  let imgUpper := if loLo ≤ loHi then [(loLo - 0x20, loHi - 0x20)] else []
  imgLower ++ imgUpper

def ciRanges : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (lo, hi) :: t => (lo, hi) :: (ciExtra lo hi ++ ciRanges t)

/-- F* `rx_fold_ci`. -/
def foldCi : Re → Re
  | .empty => .empty
  | .eps => .eps
  | .ranges rs => .ranges (ciRanges rs)
  | .cat a b => .cat (foldCi a) (foldCi b)
  | .alt a b => .alt (foldCi a) (foldCi b)
  | .inter a b => .inter (foldCi a) (foldCi b)
  | .compl a => .compl (foldCi a)
  | .star a => .star (foldCi a)

/-- `s` flag: rewrite the parser's `.` leaf (which excludes #xA / #xD) to
accept every codepoint (F* `rx_dotall`). -/
def dotAll : Re → Re
  | .empty => .empty
  | .eps => .eps
  | .ranges rs => if Re.ranges rs = XSDPattern.dotRegex then Exec.anyChar else .ranges rs
  | .cat a b => .cat (dotAll a) (dotAll b)
  | .alt a b => .alt (dotAll a) (dotAll b)
  | .inter a b => .inter (dotAll a) (dotAll b)
  | .compl a => .compl (dotAll a)
  | .star a => .star (dotAll a)

/-! ## fn:matches, F* shape -/

/-- XPath `fn:matches`: does the pattern match SOMEWHERE in `text`?
Exactly the F* `regex_match` (an unparseable pattern gives `false`);
`flags = ""` is the F* `None`. -/
def regexMatch (text pattern : String) (flags : String) : Bool :=
  let hasI := flagHas flags 'i'
  let hasS := flagHas flags 's'
  let hasX := flagHas flags 'x'
  let hasQ := flagHas flags 'q'
  let inputCps := cpsOfString text
  let patCps0 := cpsOfString pattern
  if hasQ then
    let core0 := literalRegex patCps0
    let core := if hasI then foldCi core0 else core0
    Exec.acceptsNorm (.cat Exec.dotStar (.cat core Exec.dotStar)) inputCps
  else
    let patCps1 := if hasX then stripWs patCps0 false else patCps0
    let patCps := replaceAnchors patCps1 false
    match XSDPattern.parseCps patCps with
    | none => false
    | some r0 =>
      let r1 := if hasS then dotAll r0 else r0
      let r2 := if hasI then foldCi r1 else r1
      let m := Re.cat gapLeft (.cat r2 gapRight)
      let wrapped := beginSentinel :: (inputCps ++ [endSentinel])
      Exec.acceptsNorm m wrapped

/-! ## fn:replace — spans from the verified engine -/

/-- `w[s, e)` (F* `rx_slice`). -/
def slice (w : List Nat) (s e : Nat) : List Nat :=
  if e > s then (w.drop s).take (e - s) else []

/-- All prefix lengths `k` at which `r` matches the first `k` codepoints of
`w`, via the normalised derivative, ascending (F* `rx_leaf_ends_from`).
`r = empty` is the dead state: no longer match is possible. -/
def leafEndsFrom : Re → List Nat → Nat → List Nat
  | r, [], k => if nullable r then [k] else []
  | r, c :: rest, k =>
    let here := if nullable r then [k] else []
    if r = .empty then here else here ++ leafEndsFrom (Exec.nderiv c r) rest (k + 1)

def leafEnds (r : Re) (w : List Nat) : List Nat := leafEndsFrom r w 0

def listMaxOpt : List Nat → Option Nat
  | [] => none
  | x :: t =>
    match listMaxOpt t with
    | none => some x
    | some m => some (if x > m then x else m)

/-- Longest prefix of `suffix` matched by `pr` (leftmost-longest at a
fixed start), or `none` (F* `rx_longest_end`). -/
def longestEnd (pr : Re) (suffix : List Nat) : Option Nat :=
  listMaxOpt (leafEnds pr suffix)

/-! ## Capturing AST and matcher (F* `rx_cre`, `rx_cmatch`) -/

/-- A parallel AST over which `fn:replace` group spans are recovered.
`leaf` carries an ordinary (group-less) sub-regex whose prefix matches
are decided by the verified engine. -/
inductive CRe where
  | leaf : Re → CRe
  | eps : CRe
  | cat : CRe → CRe → CRe
  | alt : CRe → CRe → CRe
  | star : CRe → CRe
  | group : Nat → CRe → CRe
  deriving DecidableEq, Repr, Inhabited

namespace CRe

def size : CRe → Nat
  | .leaf _ => 1
  | .eps => 1
  | .cat a b => 1 + size a + size b
  | .alt a b => 1 + size a + size b
  | .star a => 1 + size a
  | .group _ a => 1 + size a

/-- Flag rewrites lifted to the leaves (F* `rx_cre_fold_ci`). -/
def foldCi : CRe → CRe
  | .leaf x => .leaf (Regex.foldCi x)
  | .eps => .eps
  | .cat a b => .cat (foldCi a) (foldCi b)
  | .alt a b => .alt (foldCi a) (foldCi b)
  | .star a => .star (foldCi a)
  | .group n a => .group n (foldCi a)

/-- F* `rx_cre_dotall`. -/
def dotAll : CRe → CRe
  | .leaf x => .leaf (Regex.dotAll x)
  | .eps => .eps
  | .cat a b => .cat (dotAll a) (dotAll b)
  | .alt a b => .alt (dotAll a) (dotAll b)
  | .star a => .star (dotAll a)
  | .group n a => .group n (dotAll a)

def repeatExact (r : CRe) : Nat → CRe
  | 0 => .eps
  | n + 1 => .cat r (repeatExact r n)

def repeatOpt (r : CRe) : Nat → CRe
  | 0 => .eps
  | k + 1 => .cat (.alt r .eps) (repeatOpt r k)

end CRe

open XSDPattern in
/-- F* `rx_cparse_brace`. -/
def cparseBrace (r : CRe) (t : List Nat) : Option (CRe × List Nat) :=
  match readUint t with
  | none => none
  | some (n, t1) =>
    match t1 with
    | c :: t2 =>
      if c = cpRbrace then some (CRe.repeatExact r n, t2)
      else if c = cpComma then
        match t2 with
        | c2 :: t3 =>
          if c2 = cpRbrace then some (.cat (CRe.repeatExact r n) (.star r), t3)
          else
            match readUint t2 with
            | none => none
            | some (m, t3') =>
              match t3' with
              | c3 :: t4 =>
                if c3 = cpRbrace && m ≥ n then
                  some (.cat (CRe.repeatExact r n) (CRe.repeatOpt r (m - n)), t4)
                else none
              | [] => none
        | [] => none
      else none
    | [] => none

open XSDPattern in
/-- F* `rx_cparse_quant`. -/
def cparseQuant (r : CRe) (rest : List Nat) : Option (CRe × List Nat) :=
  match rest with
  | [] => some (r, [])
  | q :: t =>
    if q = cpStar then some (.star r, skipLazy t)
    else if q = cpPlus then some (.cat r (.star r), skipLazy t)
    else if q = cpQuestion then some (.alt r .eps, skipLazy t)
    else if q = cpLbrace then
      match cparseBrace r t with
      | none => none
      | some (r', t') => some (r', skipLazy t')
    else some (r, q :: t)

section CapturingParser
open XSDPattern

/-! Recursive-descent capturing parser mirroring `XSDPattern`. Threads the
next group number `g`; `(...)` takes the current `g` and parses its body
with `g + 1` (outer groups number lower than nested); `(?:...)` is
non-capturing (F* `rx_cparse_*`). -/
mutual
  def cparseAlt : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match cparseSeq fuel input g with
      | none => none
      | some (r1, rest, g1) =>
        match rest with
        | c :: t =>
          if c = cpPipe then
            match cparseAlt fuel t g1 with
            | none => none
            | some (r2, rest2, g2) => some (.alt r1 r2, rest2, g2)
          else some (r1, c :: t, g1)
        | [] => some (r1, [], g1)

  def cparseSeq : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match input with
      | [] => some (.eps, [], g)
      | h :: _ =>
        if h = cpPipe || h = cpRparen then some (.eps, input, g)
        else
          match cparseRep fuel input g with
          | none => none
          | some (r1, rest, g1) =>
            match rest with
            | [] => some (r1, [], g1)
            | h2 :: _ =>
              if h2 = cpPipe || h2 = cpRparen then some (r1, rest, g1)
              else
                match cparseSeq fuel rest g1 with
                | none => none
                | some (r2, rest2, g2) => some (.cat r1 r2, rest2, g2)

  def cparseRep : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match cparseAtom fuel input g with
      | none => none
      | some (r, rest, g1) =>
        match cparseQuant r rest with
        | none => none
        | some (r', rest') => some (r', rest', g1)

  def cparseAtom : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, input, g =>
      match input with
      | [] => none
      | h :: t =>
        if h = cpLparen then cparseGroup fuel t g
        else if h = cpLbracket then
          match parseClass t with
          | none => none
          | some (r, rest) => some (.leaf r, rest, g)
        else if h = cpDot then some (.leaf dotRegex, t, g)
        else if h = cpCaret then some (.eps, t, g)
        else if h = cpDollar then some (.eps, t, g)
        else if h = cpBackslash then
          match t with
          | [] => none
          | letter :: t2 =>
            match parseEscapeAtom letter t2 with
            | none => none
            | some (r, rest) => some (.leaf r, rest, g)
        else if isAtomMeta h then none
        else some (.leaf (single h), t, g)

  def cparseGroup : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, t, g =>
      match t with
      | q :: c :: t2 =>
        if q = cpQuestion && c = cpColon then cparseNoncap fuel t2 g
        else if q = cpQuestion then none
        else cparseCap fuel t g
      | q :: _ =>
        if q = cpQuestion then none
        else cparseCap fuel t g
      | [] => none

  def cparseCap : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, t, g =>
      match cparseAlt fuel t (g + 1) with
      | none => none
      | some (r, rest, g') =>
        match rest with
        | c :: t2 => if c = cpRparen then some (.group g r, t2, g') else none
        | [] => none

  def cparseNoncap : Nat → List Nat → Nat → Option (CRe × List Nat × Nat)
    | 0, _, _ => none
    | fuel + 1, t, g =>
      match cparseAlt fuel t g with
      | none => none
      | some (r, rest, g') =>
        match rest with
        | c :: t2 => if c = cpRparen then some (r, t2, g') else none
        | [] => none
end

end CapturingParser

/-- F* `rx_parse_capturing`: groups numbered from 1. -/
def parseCapturing (cps : List Nat) : Option CRe :=
  let fuel := 16 * (cps.length + 4)
  match cparseAlt fuel cps 1 with
  | some (r, [], _) => some r
  | _ => none

/-- A captured group span: group number, absolute start, absolute end. -/
structure Cap where
  group : Nat
  start : Nat
  stop  : Nat
  deriving DecidableEq, Repr

/-- One capturing-match outcome (F* `(unconsumed suffix, absolute end
position, group spans)`). -/
structure COut where
  rest   : List Nat
  endPos : Nat
  caps   : List Cap
  deriving DecidableEq, Repr

/-- ALL prefix outcomes of `r` starting at absolute position `pos` of the
suffix `w` (F* `rx_cmatch`). Fuel-bounded: structural descent ≤ size,
star iterations bounded by the strict-progress guard. -/
def cmatch : Nat → CRe → List Nat → Nat → List COut
  | 0, _, _, _ => []
  | fuel + 1, r, w, pos =>
    match r with
    | .eps => [⟨w, pos, []⟩]
    | .leaf x => (leafEnds x w).map fun k => ⟨w.drop k, pos + k, []⟩
    | .cat a b =>
      (cmatch fuel a w pos).flatMap fun oa =>
        (cmatch fuel b oa.rest oa.endPos).map fun ob =>
          ⟨ob.rest, ob.endPos, oa.caps ++ ob.caps⟩
    | .alt a b => cmatch fuel a w pos ++ cmatch fuel b w pos
    | .group n inner =>
      (cmatch fuel inner w pos).map fun o => ⟨o.rest, o.endPos, ⟨n, pos, o.endPos⟩ :: o.caps⟩
    | .star inner =>
      ⟨w, pos, []⟩ ::
      (cmatch fuel inner w pos).flatMap fun oi =>
        if oi.rest.length < w.length then
          (cmatch fuel (.star inner) oi.rest oi.endPos).map fun o2 =>
            ⟨o2.rest, o2.endPos, oi.caps ++ o2.caps⟩
        else []

/-- Caps of the FIRST outcome ending exactly at the verified span end
(alternation order = ordered-alternation preference); else `[]`
(F* `rx_pick_caps`). -/
def pickCaps : List COut → Nat → List Cap
  | [], _ => []
  | o :: t, target => if o.endPos = target then o.caps else pickCaps t target

def findCap : List Cap → Nat → Option (Nat × Nat)
  | [], _ => none
  | c :: t, n => if c.group = n then some (c.start, c.stop) else findCap t n

def groupText (input : List Nat) (caps : List Cap) (n : Nat) : List Nat :=
  match findCap caps n with
  | none => []
  | some (s, e) => slice input s e

/-- Expand a replacement template (F* `rx_expand_template`): `$d` → group
d (`$0` = whole match); `\c` → `c`; other → itself. -/
def expandTemplate : List Nat → List Nat → Nat → Nat → List Cap → List Nat
  | [], _, _, _, _ => []
  | [c], _, _, _, _ => [c]
  | c :: d :: t2, input, mstart, mend, caps =>
    if c = cpBackslash then d :: expandTemplate t2 input mstart mend caps
    else if c = 0x24 then
      if d ≥ 0x30 && d ≤ 0x39 then
        let gnum := d - 0x30
        let gt := if gnum = 0 then slice input mstart mend else groupText input caps gnum
        gt ++ expandTemplate t2 input mstart mend caps
      else c :: expandTemplate (d :: t2) input mstart mend caps
    else c :: expandTemplate (d :: t2) input mstart mend caps

/-- Does the template reference a group (`$` + digit, respecting `\`
escapes)? (F* `rx_template_has_group`). -/
def templateHasGroup : List Nat → Bool
  | [] => false
  | c :: t =>
    if c = cpBackslash then (match t with | _ :: t2 => templateHasGroup t2 | [] => false)
    else if c = 0x24 then
      match t with
      | d :: _ => if d ≥ 0x30 && d ≤ 0x39 then true else templateHasGroup t
      | [] => false
    else templateHasGroup t

/-- XPath F&O §5.6.5 err:FORX0004 check: every `\` is followed by `\` or
`$`, every `$` by a digit. NOT in the F* (whose template expander is
lenient); see the module header. -/
def templateValid : List Nat → Bool
  | [] => true
  | c :: t =>
    if c = cpBackslash then
      match t with
      | c2 :: t2 => (c2 = cpBackslash || c2 = 0x24) && templateValid t2
      | [] => false
    else if c = 0x24 then
      match t with
      | d :: t2 => d ≥ 0x30 && d ≤ 0x39 && templateValid t2
      | [] => false
    else templateValid t

/-- `cmatch` fuel budget (F* `rx_cmatch_fuel`). -/
def cmatchFuel (cre : CRe) (suffix : List Nat) : Nat :=
  (cre.size + 1) * (suffix.length + 2)

/-- Global left-to-right, non-overlapping replace over codepoint lists
(F* `rx_replace_loop`). `pr` is the verified whole-match oracle;
`creOpt` the capturing AST when the template has group refs. An empty
match copies one codepoint through without substitution (the F* policy;
`replace` below rejects such patterns before reaching here). -/
def replaceLoop (pr : Re) (creOpt : Option CRe) (rep inputAll : List Nat) :
    Nat → List Nat → Nat → List Nat
  | 0, suffix, _ => suffix
  | fuel + 1, suffix, pos =>
    match suffix with
    | [] => []
    | c :: rest =>
      match longestEnd pr suffix with
      | none => c :: replaceLoop pr creOpt rep inputAll fuel rest (pos + 1)
      | some len =>
        if len = 0 then
          c :: replaceLoop pr creOpt rep inputAll fuel rest (pos + 1)
        else
          let mend := pos + len
          let caps : List Cap :=
            match creOpt with
            | none => []
            | some cre => pickCaps (cmatch (cmatchFuel cre suffix) cre suffix pos) mend
          let expanded := expandTemplate rep inputAll pos mend caps
          let newSuffix := suffix.drop len
          expanded ++ replaceLoop pr creOpt rep inputAll fuel newSuffix mend

/-- XPath `fn:replace`, exactly the F* `regex_replace` (an unparseable
pattern leaves the text unchanged; `flags = ""` is the F* `None`). -/
def regexReplace (text pattern replacement : String) (flags : String) : String :=
  let hasI := flagHas flags 'i'
  let hasS := flagHas flags 's'
  let hasX := flagHas flags 'x'
  let hasQ := flagHas flags 'q'
  let inputCps := cpsOfString text
  let repCps := cpsOfString replacement
  let patCps0 := cpsOfString pattern
  let fuel := inputCps.length + 1
  if hasQ then
    let core0 := literalRegex patCps0
    let pr := if hasI then foldCi core0 else core0
    stringOfCps (replaceLoop pr none repCps inputCps fuel inputCps 0)
  else
    let patCps1 := if hasX then stripWs patCps0 false else patCps0
    match XSDPattern.parseCps patCps1 with
    | none => text
    | some r0 =>
      let r1 := if hasS then dotAll r0 else r0
      let pr := if hasI then foldCi r1 else r1
      let creOpt :=
        if templateHasGroup repCps then
          match parseCapturing patCps1 with
          | none => none
          | some cre0 =>
            let cre1 := if hasS then cre0.dotAll else cre0
            some (if hasI then cre1.foldCi else cre1)
        else none
      stringOfCps (replaceLoop pr creOpt repCps inputCps fuel inputCps 0)

/-! ## Public API for the SPARQL evaluator -/

/-- Errors of the XPath regex functions, named by their F&O error codes. -/
inductive RegexError where
  /-- err:FORX0001 — a flag character outside `i s m x q`. -/
  | invalidFlags (flags : String)
  /-- err:FORX0002 — the pattern is not in the supported XSD / XPath fragment. -/
  | invalidPattern (pattern : String)
  /-- err:FORX0003 — `fn:replace` with a pattern that matches the empty string. -/
  | matchesEmptyString (pattern : String)
  /-- err:FORX0004 — `fn:replace` with an ill-formed replacement template. -/
  | invalidReplacement (replacement : String)
  deriving DecidableEq, Repr

/-- A compiled pattern: the flag-rewritten regexes for matching and for
replacing, plus the capturing AST (`none` only when the capturing
parser diverged from the XSD parser, which no measured pattern does). -/
structure Compiled where
  /-- `gapLeft · P' · gapRight` with real anchors; run on the sentinel-wrapped input. -/
  matchRe   : Re
  /-- the whole-match oracle for `fn:replace` (anchors as eps, as in the F*). -/
  replaceRe : Re
  capt      : Option CRe
  /-- `m` flag: `isMatch` wraps every line in sentinels. -/
  multiline : Bool
  deriving Repr

/-- The flag characters XPath F&O §5.6.1 defines. -/
def validFlags (flags : String) : Bool :=
  flags.toList.all fun ch => ch = 'i' || ch = 's' || ch = 'm' || ch = 'x' || ch = 'q'

/-- Compile an XPath pattern with flags (SPARQL `REGEX` / `REPLACE`
arguments). The flag / rewrite pipeline is the F* `regex_match` /
`regex_replace` one; see the module header for the error channel. -/
def compile (pattern : String) (flags : String) : Except RegexError Compiled :=
  if !validFlags flags then .error (.invalidFlags flags)
  else
    let hasI := flagHas flags 'i'
    let hasS := flagHas flags 's'
    let hasX := flagHas flags 'x'
    let hasQ := flagHas flags 'q'
    let hasM := flagHas flags 'm'
    let patCps0 := cpsOfString pattern
    let wrap (p : Re) : Re :=
      if hasM then .cat sigmaAllStar (.cat (absorbMarkers p) sigmaAllStar)
      else .cat gapLeft (.cat p gapRight)
    if hasQ then
      let core0 := literalRegex patCps0
      let core := if hasI then foldCi core0 else core0
      .ok { matchRe := wrap core, replaceRe := core, capt := none, multiline := hasM }
    else
      let patCps1 := if hasX then stripWs patCps0 false else patCps0
      match XSDPattern.parseCps (replaceAnchors patCps1 false), XSDPattern.parseCps patCps1 with
      | some m0, some r0 =>
        let m1 := if hasS then dotAll m0 else m0
        let m2 := if hasI then foldCi m1 else m1
        let r1 := if hasS then dotAll r0 else r0
        let r2 := if hasI then foldCi r1 else r1
        let capt :=
          match parseCapturing patCps1 with
          | none => none
          | some cre0 =>
            let cre1 := if hasS then cre0.dotAll else cre0
            some (if hasI then cre1.foldCi else cre1)
        .ok { matchRe := wrap m2, replaceRe := r2, capt := capt, multiline := hasM }
      | _, _ => .error (.invalidPattern pattern)

/-- SPARQL `REGEX` / XPath `fn:matches`: unanchored search, `^` / `$`
honoured as string anchors. (`matches` is a Lean keyword, hence
`isMatch`.) -/
def isMatch (r : Compiled) (s : String) : Bool :=
  let cps := cpsOfString s
  let wrapped := if r.multiline then wrapMultiline cps else beginSentinel :: (cps ++ [endSentinel])
  Exec.acceptsNorm r.matchRe wrapped

/-- SPARQL `REPLACE` / XPath `fn:replace`: global, non-overlapping,
leftmost-longest; `$N` group references, `\$` and `\\` escapes. -/
def replace (r : Compiled) (s replacement : String) : Except RegexError String :=
  let repCps := cpsOfString replacement
  if !templateValid repCps then .error (.invalidReplacement replacement)
  else if nullable r.replaceRe then .error (.matchesEmptyString "")
  else
    let inputCps := cpsOfString s
    let creOpt := if templateHasGroup repCps then r.capt else none
    .ok (stringOfCps (replaceLoop r.replaceRe creOpt repCps inputCps (inputCps.length + 1) inputCps 0))

/-- The XSD `pattern` facet (XML Schema Part 2 §4.3.4): whole-string
membership; `none` when the pattern is outside the supported fragment.
The CSVW / JSON Schema / OWL consumers in the F* call exactly this
(`parse_xsd_pattern` + `matches_norm`). -/
def xsdPatternMatches (pattern : String) (s : String) : Option Bool :=
  match XSDPattern.parseXsdPattern pattern with
  | none => none
  | some r => some (Exec.acceptsNorm r (cpsOfString s))

end L4Factoidal.Regex
