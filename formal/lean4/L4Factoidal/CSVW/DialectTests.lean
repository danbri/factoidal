/-
L4Factoidal.CSVW.DialectTests — build-time checks for the CSVW
dialect resolution and the CSV reader.
-/
import L4Factoidal.CSVW.Dialect

namespace L4Factoidal.CSVW

private def dflt : ResolvedDialect := ({} : Dialect).resolve

-- Defaults, §5.9: comma, double-quote, doubleQuote escaping, one
-- header row.
#guard dflt.delimiter == ','
#guard dflt.quoteChar == some '"'
#guard dflt.doubleQuote == true
#guard dflt.headerRowCount == 1

-- `header: false` means no header row; an explicit headerRowCount
-- overrides it either way.
#guard ({ header := some false : Dialect }).resolve.headerRowCount == 0
#guard ({ header := some false, headerRowCount := some 2 : Dialect }).resolve.headerRowCount == 2
#guard ({ headerRowCount := some 0 : Dialect }).resolve.headerRowCount == 0

-- An explicitly empty quoteChar means "no quoting at all".
#guard ({ quoteChar := some "" : Dialect }).resolve.quoteChar == none

-- Basic split.
#guard splitCells dflt "a,b,c".toList == ["a", "b", "c"]
#guard splitCells dflt "".toList == [""]

-- Quoting: the delimiter inside quotes is literal.
#guard splitCells dflt "\"a,b\",c".toList == ["a,b", "c"]
-- A doubled quote inside quotes is one literal quote.
#guard splitCells dflt "\"say \"\"hi\"\"\",x".toList == ["say \"hi\"", "x"]

-- A tab dialect.
private def tabD : ResolvedDialect := ({ delimiter := some "\t" : Dialect }).resolve
#guard splitCells tabD "a\tb".toList == ["a", "b"]

-- Line endings: CRLF, LF and bare CR all split.
#guard splitLines "a\r\nb\nc\rd" == ["a", "b", "c", "d"]

-- Reading: one header row by default, the rest are data.
private def src : String := "name,age\nAlice,30\nBob,24"
#guard (read dflt src).header.length == 1
#guard (read dflt src).rows.length == 2
#guard (read dflt src).header.head!.cells == ["name", "age"]
#guard (read dflt src).rows.head!.cells == ["Alice", "30"]

-- Row numbers are SOURCE line numbers, 1-based — csvw:rownum and
-- error reports depend on them surviving skips.
#guard (read dflt src).rows.head!.num == 2
#guard ((read ({ skipRows := some 1 : Dialect }).resolve src).header.head!.num) == 2

-- skipColumns drops leading cells.
#guard (read ({ skipColumns := some 1 : Dialect }).resolve "a,b,c\n1,2,3").rows.head!.cells
       == ["2", "3"]

-- Comments are dropped before rows are counted.
#guard (read ({ commentPrefix := some "#" : Dialect }).resolve "#note\nh\nv").rows.length == 1

-- skipBlankRows.
#guard (read ({ skipBlankRows := some true : Dialect }).resolve "h\n\nv").rows.length == 1
#guard (read dflt "h\n\nv").rows.length == 2

-- A FINAL line terminator ends the last row; it does not start a new
-- empty one (RFC 4180 makes the terminator optional on the last
-- record). Found by running the real W3C corpus, where 85 of 177
-- files otherwise read as ragged.
#guard (read dflt "h\nv\n").rows.length == 1
#guard (read dflt "h\nv").rows.length == 1
#guard (read dflt "h\nv\r\n").rows.length == 1
-- ...but an INTERIOR blank line is still a row, unless skipBlankRows.
#guard (read dflt "h\n\nv\n").rows.length == 2

-- Trimming is on by default; `trim: false` keeps the spaces.
#guard (read dflt "h\n  v  ").rows.head!.cells == ["v"]
#guard (read ({ trim := some "false" : Dialect }).resolve "h\n  v  ").rows.head!.cells == ["  v  "]
#guard (read ({ trim := some "start" : Dialect }).resolve "h\n  v  ").rows.head!.cells == ["v  "]

end L4Factoidal.CSVW
