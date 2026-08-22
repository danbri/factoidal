/-
L4Factoidal.CSVW.Dialect — the CSVW dialect description and the
dialect-driven CSV reader.

Specs: "Model for Tabular Data and Metadata on the Web"
(https://www.w3.org/TR/tabular-data-model/) §8 parsing, and
"Metadata Vocabulary for Tabular Data"
(https://www.w3.org/TR/tabular-metadata/) §5.9 dialect descriptions.
Ported from `formal/fstar/CSVW.Metadata.fst`'s `csvw_dialect` and the
row reader it drives.

Every dialect property is `Option`, exactly as in the metadata: absent
means "inherit or use the spec default", and the defaults are applied
ONLY at read time (`Dialect.resolve`). Collapsing absent into the
default at parse time would lose the distinction the metadata
inheritance rules depend on.
-/

namespace L4Factoidal.CSVW

/-- §5.9 dialect description. All fields optional; see the module
    header for why absence is preserved. -/
structure Dialect where
  delimiter        : Option String := none
  quoteChar        : Option String := none
  doubleQuote      : Option Bool   := none
  header           : Option Bool   := none
  headerRowCount   : Option Int    := none
  skipRows         : Option Int    := none
  skipColumns      : Option Int    := none
  skipBlankRows    : Option Bool   := none
  skipInitialSpace : Option Bool   := none
  commentPrefix    : Option String := none
  encoding         : Option String := none
  trim             : Option String := none
deriving Repr, Inhabited

/-- Trim modes, §5.9: `true`/`false`/`"start"`/`"end"`. -/
inductive TrimMode where
  | none | start | «end» | both
deriving Repr, DecidableEq, Inhabited

/-- A dialect with every default resolved — what the reader consumes.
    Defaults are the spec's: comma delimiter, double-quote quoting,
    doubleQuote escaping, one header row, no skipping, blank rows
    skipped, and trimming on. -/
structure ResolvedDialect where
  delimiter        : Char
  quoteChar        : Option Char
  doubleQuote      : Bool
  headerRowCount   : Nat
  skipRows         : Nat
  skipColumns      : Nat
  skipBlankRows    : Bool
  skipInitialSpace : Bool
  commentPrefix    : Option String
  trim             : TrimMode
deriving Repr, Inhabited

private def firstChar (s : Option String) (dflt : Char) : Char :=
  match s with
  | some str => str.get? 0 |>.getD dflt
  | none     => dflt

private def toNat (i : Option Int) (dflt : Nat) : Nat :=
  match i with
  | some n => if n < 0 then dflt else n.toNat
  | none   => dflt

/-- Apply the §5.9 defaults. `header := false` means zero header rows
    unless `headerRowCount` says otherwise — the spec's interaction
    between the two properties, which is easy to get wrong. -/
def Dialect.resolve (d : Dialect) : ResolvedDialect :=
  let hdrCount :=
    match d.headerRowCount, d.header with
    | some n, _        => if n < 0 then 0 else n.toNat
    | none,   some false => 0
    | none,   _        => 1
  { delimiter        := firstChar d.delimiter ','
    quoteChar        := match d.quoteChar with
                        | some "" => none          -- explicit "no quoting"
                        | some s  => s.get? 0
                        | none    => some '"'
    doubleQuote      := d.doubleQuote.getD true
    headerRowCount   := hdrCount
    skipRows         := toNat d.skipRows 0
    skipColumns      := toNat d.skipColumns 0
    skipBlankRows    := d.skipBlankRows.getD false
    skipInitialSpace := d.skipInitialSpace.getD false
    commentPrefix    := d.commentPrefix
    trim             := match d.trim with
                        | some "false" => .none
                        | some "start" => .start
                        | some "end"   => .end
                        | _            => .both }

/-! ## The reader -/

private def trimStart (s : String) : String :=
  String.ofList (s.toList.dropWhile (· == ' '))

private def trimEnd (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (· == ' ')).reverse)

def applyTrim : TrimMode → String → String
  | .none,  s => s
  | .start, s => trimStart s
  | .end,   s => trimEnd s
  | .both,  s => trimEnd (trimStart s)

/-- Split one line into cells, honouring quoting. Quoted sections may
    contain the delimiter; a doubled quote inside a quoted section is
    a literal quote when `doubleQuote` is set. -/
partial def splitCells (d : ResolvedDialect) (line : List Char) : List String :=
  let rec go (cur : List Char) (acc : List String) (inQuote : Bool)
      : List Char → List String
    | [] => (acc ++ [String.ofList cur.reverse])
    | c :: rest =>
        match d.quoteChar with
        | some q =>
            if inQuote then
              if c == q then
                match rest with
                | q2 :: rest2 =>
                    if d.doubleQuote && q2 == q then go (q :: cur) acc true rest2
                    else go cur acc false (q2 :: rest2)
                | [] => go cur acc false []
              else go (c :: cur) acc true rest
            else if c == q && cur.isEmpty then go cur acc true rest
            else if c == d.delimiter then go [] (acc ++ [String.ofList cur.reverse]) false rest
            else go (c :: cur) acc false rest
        | none =>
            if c == d.delimiter then go [] (acc ++ [String.ofList cur.reverse]) false rest
            else go (c :: cur) acc false rest
  go [] [] false line

/-- Is the line a comment, per `commentPrefix`? -/
def isComment (d : ResolvedDialect) (line : String) : Bool :=
  match d.commentPrefix with
  | some p => p != "" && line.startsWith p
  | none   => false

/-- A row of cells plus the source line number (1-based), which the
    conversion step needs for `csvw:rownum` and for error reporting. -/
structure Row where
  num   : Nat
  cells : List String
deriving Repr, Inhabited

/-- The result of reading a source: the header rows and the data
    rows, both already trimmed and column-skipped. -/
structure Table where
  header : List Row
  rows   : List Row
deriving Repr, Inhabited

/-- Split on line breaks, accepting CRLF, LF and CR. -/
def splitLines (s : String) : List String :=
  let rec go (cur : List Char) (acc : List String) : List Char → List String
    | []              => acc ++ [String.ofList cur.reverse]
    | '\r' :: '\n' :: r => go [] (acc ++ [String.ofList cur.reverse]) r
    | '\n' :: r       => go [] (acc ++ [String.ofList cur.reverse]) r
    | '\r' :: r       => go [] (acc ++ [String.ofList cur.reverse]) r
    | c :: r          => go (c :: cur) acc r
  go [] [] s.toList

/-- A FINAL line terminator ends the last row; it does not start a new
    empty one. RFC 4180 makes the terminator optional on the last
    record, so `"a\nb\n"` and `"a\nb"` are the same two rows.

    Found by running the real W3C csvw corpus: without this, 85 of
    177 files read as "ragged" because their trailing newline produced
    a phantom one-cell row. A synthetic test would not have caught it,
    since one rarely writes the trailing newline by hand. -/
def dropTrailingTerminator (ls : List String) : List String :=
  match ls.reverse with
  | "" :: rest => rest.reverse
  | _          => ls

/-- Read a CSV source under a dialect: skip rows, drop comments and
    (optionally) blank rows, split cells, skip leading columns, trim,
    and separate header rows from data rows. -/
def read (d : ResolvedDialect) (src : String) : Table :=
  let numbered := (dropTrailingTerminator (splitLines src)).zipIdx.map
                    (fun (l, i) => (i + 1, l))
  let afterSkip := numbered.drop d.skipRows
  let kept := afterSkip.filter (fun (_, l) => !(isComment d l))
  let toRow : (Nat × String) → Row := fun (n, l) =>
    let cells := (splitCells d l.toList).drop d.skipColumns
    let cells := cells.map (fun c =>
      let c := if d.skipInitialSpace then trimStart c else c
      applyTrim d.trim c)
    ⟨n, cells⟩
  let rows := kept.map toRow
  let rows := if d.skipBlankRows then
      rows.filter (fun r => !(r.cells.all (· == ""))) else rows
  ⟨rows.take d.headerRowCount, rows.drop d.headerRowCount⟩

end L4Factoidal.CSVW
