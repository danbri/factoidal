/-
L4Factoidal.Geo.Wkt — WKT literal parsing and serialization, ported
from `formal/fstar/Parser.WKT.fst`.

Grammar: Simple Features WKT as used by `geo:wktLiteral` (GeoSPARQL
1.1 §8.5.1), optionally prefixed by a CRS IRI in angle brackets:

    "<http://.../CRS84> POINT(-0.1 51.5)"

Numbers parse to EXACT decimals (`Scaled`), never floats — the point
of the whole Geo port. `-0.1` is `⟨-1, 1⟩`, not a binary
approximation, so a coordinate that round-trips through parse and
serialize compares equal to itself.

The parser is total: it returns `Option`, never throws, and consumes
the whole input (modulo trailing whitespace) or fails.
-/
import L4Factoidal.Geo.Topology

namespace L4Factoidal.Geo
namespace Wkt

private def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'
private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- Parser state: the remaining characters. Working on `List Char`
    keeps every step structurally decreasing, so the parser is total
    without a fuel parameter (the F* side needed explicit fuel). -/
abbrev P := List Char

def skipWs : P → P
  | c :: rest => if isWs c then skipWs rest else c :: rest
  | []        => []

/-- Digits, as an accumulated natural and a count. -/
def takeDigits : P → (Nat × Nat × P)
  | c :: rest =>
      if isDigit c then
        let d := c.toNat - '0'.toNat
        let (v, n, tl) := takeDigits rest
        (d * Scaled.pow10 n + v, n + 1, tl)
      else (0, 0, c :: rest)
  | [] => (0, 0, [])

/-- A signed decimal number: `-?DIGITS(.DIGITS)?`. Exponent notation
    is not part of Simple Features WKT and is rejected. -/
def number (inp : P) : Option (Scaled × P) :=
  let inp := skipWs inp
  let (neg, inp) := match inp with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _        => (false, inp)
  let (intPart, intLen, inp) := takeDigits inp
  if intLen == 0 then none
  else
    match inp with
    | '.' :: r =>
        let (frac, fracLen, r') := takeDigits r
        if fracLen == 0 then none
        else
          let m : Int := (intPart * Scaled.pow10 fracLen + frac : Nat)
          some (⟨if neg then -m else m, fracLen⟩, r')
    | _ =>
        let m : Int := intPart
        some (⟨if neg then -m else m, 0⟩, inp)

def point (inp : P) : Option (Point × P) := do
  let (x, inp) ← number inp
  let (y, inp) ← number inp
  some (⟨x, y⟩, inp)

def lit (c : Char) (inp : P) : Option P :=
  match skipWs inp with
  | d :: rest => if d == c then some rest else none
  | []        => none

/-- A comma-separated point list, at least one. -/
partial def pointList (inp : P) : Option (List Point × P) := do
  let (p, inp) ← point inp
  match skipWs inp with
  | ',' :: rest => do
      let (ps, inp') ← pointList rest
      some (p :: ps, inp')
  | rest => some ([p], rest)

/-- `( pointlist )`. -/
def parenPoints (inp : P) : Option (List Point × P) := do
  let inp ← lit '(' inp
  let (ps, inp) ← pointList inp
  let inp ← lit ')' inp
  some (ps, inp)

/-- A comma-separated list of parenthesised rings. -/
partial def ringList (inp : P) : Option (List Ring × P) := do
  let (r, inp) ← parenPoints inp
  match skipWs inp with
  | ',' :: rest => do
      let (rs, inp') ← ringList rest
      some (r :: rs, inp')
  | rest => some ([r], rest)

def parenRings (inp : P) : Option (List Ring × P) := do
  let inp ← lit '(' inp
  let (rs, inp) ← ringList inp
  let inp ← lit ')' inp
  some (rs, inp)

partial def polygonList (inp : P) : Option (List Polygon × P) := do
  let (rs, inp) ← parenRings inp
  let poly : Polygon := match rs with
    | []      => ⟨[], []⟩
    | e :: hs => ⟨e, hs⟩
  match skipWs inp with
  | ',' :: rest => do
      let (ps, inp') ← polygonList rest
      some (poly :: ps, inp')
  | rest => some ([poly], rest)

/-- Match a case-insensitive keyword. -/
def keyword (kw : String) (inp : P) : Option P :=
  let inp := skipWs inp
  let rec go : List Char → P → Option P
    | [], rest => some rest
    | k :: ks, c :: rest =>
        if c.toLower == k.toLower then go ks rest else none
    | _ :: _, [] => none
  go kw.toList inp

/-- Is the next token the EMPTY keyword? -/
def tryEmpty (inp : P) : Option P := keyword "EMPTY" inp

mutual

/-- A tagged geometry. Collections recurse, so this is `partial`;
    every other production is structural. -/
partial def geometry (inp : P) : Option (Geometry × P) :=
  let inp0 := skipWs inp
  if let some r := keyword "POINT" inp0 then
    if let some r' := tryEmpty r then some (.empty .point, r')
    else do
      let r ← lit '(' r
      let (p, r) ← point r
      let r ← lit ')' r
      some (.point p, r)
  else if let some r := keyword "MULTIPOINT" inp0 then
    if let some r' := tryEmpty r then some (.empty .multiPoint, r')
    else do let (ps, r) ← parenPoints r; some (.multiPoint ps, r)
  else if let some r := keyword "MULTILINESTRING" inp0 then
    if let some r' := tryEmpty r then some (.empty .multiLineString, r')
    else do let (rs, r) ← parenRings r; some (.multiLineString rs, r)
  else if let some r := keyword "LINESTRING" inp0 then
    if let some r' := tryEmpty r then some (.empty .lineString, r')
    else do let (ps, r) ← parenPoints r; some (.lineString ps, r)
  else if let some r := keyword "MULTIPOLYGON" inp0 then
    if let some r' := tryEmpty r then some (.empty .multiPolygon, r')
    else do
      let r ← lit '(' r
      let (ps, r) ← polygonList r
      let r ← lit ')' r
      some (.multiPolygon ps, r)
  else if let some r := keyword "POLYGON" inp0 then
    if let some r' := tryEmpty r then some (.empty .polygon, r')
    else do
      let (rs, r) ← parenRings r
      match rs with
      | []      => none
      | e :: hs => some (.polygon ⟨e, hs⟩, r)
  else if let some r := keyword "GEOMETRYCOLLECTION" inp0 then
    if let some r' := tryEmpty r then some (.empty .geometryCollection, r')
    else do
      let r ← lit '(' r
      let (gs, r) ← geometryList r
      let r ← lit ')' r
      some (.geometryCollection gs, r)
  else none

/-- Comma-separated geometries inside a collection. -/
partial def geometryList (inp : P) : Option (List Geometry × P) := do
  let (g, inp) ← geometry inp
  match skipWs inp with
  | ',' :: rest => do
      let (gs, inp') ← geometryList rest
      some (g :: gs, inp')
  | rest => some ([g], rest)

end

/-- An optional `<IRI>` CRS prefix. -/
def crsPrefix (inp : P) : (Option String × P) :=
  match skipWs inp with
  | '<' :: rest =>
      let iri := rest.takeWhile (· != '>')
      let tl  := rest.dropWhile (· != '>')
      match tl with
      | '>' :: tl' => (some (String.ofList iri), tl')
      | _          => (none, inp)
  | _ => (none, inp)

/-- Parse a complete `geo:wktLiteral`. The whole string must be
    consumed, modulo trailing whitespace. -/
def parseLiteral (s : String) : Option WktValue := do
  let (crs, inp) := crsPrefix s.toList
  let (g, rest) ← geometry inp
  if (skipWs rest).isEmpty then some ⟨crs, g⟩ else none

end Wkt

/-- Render a `Scaled` in plain decimal notation. -/
def Scaled.toStringDec (a : Scaled) : String :=
  if a.scale == 0 then toString a.mantissa
  else
    let neg := a.mantissa < 0
    let digits := toString (if neg then -a.mantissa else a.mantissa)
    let padded := if digits.length ≤ a.scale then
        "".pushn '0' (a.scale + 1 - digits.length) ++ digits
      else digits
    let cut := padded.length - a.scale
    let intPart := padded.take cut
    let fracPart := padded.drop cut
    (if neg then "-" else "") ++ intPart ++ "." ++ fracPart

end L4Factoidal.Geo
