# SPARQL demo review — 2026-04-20 / 21

Hands-on review of the in-browser demo at
<https://danbri.github.io/factoidal/fstar-extracted/>. Every dataset × query
combination listed in the dropdowns was executed through Playwright; a handful
of combinations were also driven via Chrome DevTools for a performance trace.
The wasm and js engines were compared on the same queries.

## Scope

- All 6 datasets (People, Products, Music, Places, TriG libraries, schema.org hierarchy).
- All queries from each dataset's dropdown.
- Entailment: `none`, `RDFS`, `OWL-RL` on the schema.org dataset.
- Engines: `js (js_of_ocaml)` and `wasm (wasm_of_ocaml)`.
- Custom SPARQL (`SELECT *`, typo'd keyword, malformed Turtle) on the People dataset.
- One Chrome DevTools performance trace on the music property-path query (saved to `tmp/perf-trace-music-propertypath-js.json`).

## Headline findings

### 1. UTF-8 corruption in the js engine output (HIGH — drops rows, not just cosmetic)

Non-ASCII literals are mangled in the rendered results table when the **js
engine** is selected — but not when the **wasm engine** is selected. The input
Turtle textarea always holds the correct bytes; the damage is on the output
path.

Latin-script accents (known at first pass):

| Source literal | js-engine output | wasm-engine output |
|---|---|---|
| `"Eve Müller"@de` | `"Eve M����r"@de` | `"Eve Müller"@de` ✓ |
| `"Cafetière"` | `"Cafeti鳥"` | (correct) |
| `"Ralf Hütter"` | `"Ralf H����r"` | (correct) |
| `"Gödel, Escher, Bach"` | `"G����, Escher, Bach"` | (correct) |

RTL + mixed-script + emoji stress (added 2026-04-21):

| Source literal | js-engine output | wasm |
|---|---|---|
| `"שלום עולם"@he` (Hebrew) | `"ёӓՕ"@he` | ✓ |
| `"مرحبا بالعالم"@ar` (Arabic) | `"E1-(' ('D9'DE"@ar` | ✓ |
| `"Hello שלום world"@en` (LTR+RTL mix) | `"Hello 靕ݠworld"@en` | ✓ |
| `"混合 español عربي"@mul` (CJK+Latin+Arabic) | `"����spa񯬠91(J"@mul` | ✓ |
| `"كافيه Café ☕"@mul` (Arabic+accent+emoji) | `"C'AJG Caf頕"@mul` | ✓ |
| `"אבגדהו"@he` (Hebrew) | **missing — not in result set** | ✓ |

On the mixed-script dataset **the js engine returned 5 rows when 6 were
expected**. So the corruption is not merely display-layer; a row was silently
dropped from the result set. Most likely cause: the ORDER BY comparator or a
DISTINCT-like collapse hits invalid UTF-8 during comparison and either errors
out of a row quietly or treats two rows as equal. Either way this is a
correctness bug, not just a rendering glitch.

Because the wasm build produces correct output and correct cardinality from
the same F\* sources, the bug lives in the js extraction / JS-side string
handling, not in `.fst` logic. Most likely: a byte-length-indexed slice or
`String.sub` path is producing invalid UTF-8 fragments that the DOM then
renders as U+FFFD replacement characters, and a comparator on those bytes
sometimes produces equality where the source strings differed. The fact that
`UCASE` also corrupts in the js engine (`"EVE M����R"`) confirms the bad
bytes flow all the way through string operations.

This is the single biggest demo-facing bug — and now the biggest correctness
bug in the js build too.

### 2. UCASE (and by extension LCASE) is not Unicode-aware (MEDIUM)

Even on the wasm engine where UTF-8 is preserved, `UCASE("Eve Müller")`
returns `"EVE MüLLER"` — the `ü` is not uppercased. This matches the known
limitation in CLAUDE.md rule #10 (OCaml `Str`/byte operations on UTF-8).
Worth calling out in the demo copy or the review doc because users will
notice. A Unicode-aware casing helper — or an `assume val` boundary to a
Pcre/Re-backed stub — would fix it.

### 3. Raw OCaml exception message leaks into the status line (LOW)

Typing `SELEKT` for `SELECT`:

```
SPARQL parse error: expected SELECT, ASK, CONSTRUCT, or DESCRIBE
SPARQL parse error: Failure("Error: __factoidal_exit__")
```

The second line is raw OCaml internals and should be filtered out of the UI
surface. The first line is fine.

### 4. Malformed Turtle fails silently (MEDIUM)

Pasting `@prefix ex: <http://example.org/> . ex:a ex:p "unterminated` into the
Turtle textarea and running a query returns `Done (js)` / `0 results` with no
parse error shown. The Turtle parser (or its driver) is swallowing the failure
and handing an empty graph to the evaluator. Should surface as an error like
the SPARQL parse path does.

### 5. ORDER BY segregates literals by datatype (LOW)

`ORDER BY ?name` on the People dataset interleaves groups by literal kind
before alphabetising within each group:

```
Bob Nguyen @en
Dave Patel @en
Eve M����r @de        ← language-tagged literals first
Frank O'Connor @en
Heidi Klum @de
Alice Carter          ← then plain xsd:string literals
Carol Diaz
Grace Hopper
```

SPARQL lets implementations choose the order across incomparable literal
types, so this is technically spec-legal, but it makes the demo look
buggy: users expect `Alice` to come before `Bob`. A note in the demo, or an
implementation tweak that compares lexical form across the two groups,
would help.

### 6. Decimal truncation, not rounding, in AVG (LOW)

`AVG` on the books category returns `"31.666666666666"^^xsd:decimal` (13 sixes,
truncated) instead of `31.666666666667` (rounded) or a fully-preserved
repeating representation. Minor but off-spec if the intent was correctly
rounded decimal.

### 7. Prefix compression mismatch in TriG results (LOW)

The TriG dataset declares `@prefix ex: <http://example.org/lib/>` and uses
`ex:central`. In the results table the IRI renders as `ex:lib/central`,
which is what you'd get if the output formatter were using a *different*
prefix table (`ex:` → `http://example.org/`) than the input. Display-only
cosmetic, but confusing.

### 8. `SELECT *` column order (LOW)

`SELECT * WHERE { ?s foaf:name ?n }` produces `?n ?s` — reverse of the
textual order. SPARQL 1.1 §16.2 says `*` projects all in-scope variables
but doesn't pin column order; many engines sort by first-appearance. Not
a bug, but worth noting that the order is stable / deterministic but not
aligned with user expectation.

## Queries verified correct (as best we can eyeball)

People & friendships:
- List everyone by name ✓ (8 rows; see finding #5 on ordering)
- Filter: people over 30 ✓ (5 rows, age desc)
- OPTIONAL: email if known ✓ (8 rows, OPTIONAL binds only where mbox exists)
- Friends of Alice ✓ (3 rows)
- Mutual friendships ✓ (7 unordered pairs, deduped)
- Count friends per person ✓ (7 rows; Heidi correctly excluded with no knows)
- ASK: Alice → knows → Eve? ✓ (Yes: via Carol)
- Only German-tagged names ✓ (Eve, Heidi)
- BIND + string functions ✓ (UCASE + SUBSTR work; see finding #1 on UTF-8)

Product catalogue:
- All products by price DESC ✓ (20 rows)
- Count + average price by category ✓ (6 rows; see finding #6 on trunc)
- Out of stock ✓ (2 rows, stock=0)
- Max price per category with HAVING > 50 ✓ (4 rows; books/stationery
  correctly excluded)

Music:
- Albums with year and artist ✓ (8 rows)
- Band size COUNT members ✓ (Radiohead 5, Beatles 4, Kraftwerk 2)
- Albums per band GROUP_CONCAT ✓ (3 bands, albums joined)
- Albums in the 1970s ✓ (Autobahn, Trans-Europa Express)
- Property path: musicians per album ✓ (29 rows; see finding #1 for Hütter)
- Property path: bandmates of Thom Yorke ✓ (4 rows, Thom excluded)

Places:
- Countries with capital + population ✓ (7 rows)
- Total population by continent ✓ (math checks: Asia 1.506 B, Europe 325 M)
- Capitals of big-country Europe ✓ (4 rows, threshold appears to be 50 M)

TriG libraries:
- Books grouped by library ✓ (10 rows, GRAPH binding works)
- Books held by multiple libraries ✓ (3 titles; GEB in all 3)
- Library names from default graph ✓ (3 rows)
- Central Library holdings only ✓ (4 rows)

schema.org hierarchy:
- All Places with entailment=none → 0 rows ✓ (no direct Place instances)
- All Places with entailment=RDFS → 5 rows ✓ (subClassOf chain;
  legalName → name subPropertyOf also fires for hotelZ)
- Property path `a/rdfs:subClassOf*` with entailment=none → 4 rows ✓
- containedInPlace via owl:inverseOf needs OWL-RL → 0/2 as expected
- owl:sameAs substitution needs OWL-RL → 5 rows; OWL-RL mode includes RDFS

## Performance

Measured wall-clock from button-click to `Done` text, using `performance.now()`
in the page; 10 ms polling granularity. Small queries bottom out around 15 ms
so treat sub-30-ms numbers as noise.

| Test | js (ms) | wasm (ms) | wasm speedup |
|------|---:|---:|---:|
| schemaOrg All Places, OWL-RL | 43.7 | 27.0 | 1.6× |
| schemaOrg All Places, RDFS   | 30.1 | 27.7 | 1.1× |
| schemaOrg All Places, none   | 21.2 | 15.7 | 1.4× |
| music path-performers, none  | 62.2 | 25.6 | 2.4× |
| people count-friends, none   | 19.2 | 21.0 | 0.9× |
| libraries by-library, none   | 28.6 | 15.9 | 1.8× |

wasm is 1.4–2.4× faster than js on the heavier queries; on tiny queries they
tie. Both are well under the 300 ms latency ceiling any user would notice.

### Chrome DevTools trace

Saved to `tmp/perf-trace-music-propertypath-js.json` (music property-path
query under js engine). Total trace span ≈ 24 s including idle time before and
after the click. The actual query took ~60 ms and fit in one frame; there
was no layout shift or long task worth analysing at this data scale. The demo
data is simply too small to stress the engine — to produce a meaningful
trace we'd need a synthetic dataset in the thousands-of-triples range and,
ideally, a slow query (rule #20 — send that to a subagent, not the main
loop). Noted as follow-up.

## Console

Clean on both engines. The only console error across all runs was
`Failed to load resource: the server responded with a status of 404 ()` for
`/favicon.ico` — unrelated to the evaluator, easy to add a favicon or a
1-byte stub.

## Recommended work

Ranked by demo impact:

1. **Fix UTF-8 corruption in the js engine output.** See finding #1.
   Probably a `String.sub` / byte-index slice in the result formatter.
   Trace where a literal's lexical form is converted for DOM insertion in
   the js build and compare with the wasm build's path.
2. **Make malformed Turtle surface as an error** (finding #4). Right now
   it silently becomes an empty graph.
3. **Suppress the raw `Failure("... __factoidal_exit__")` line** in the
   status area (finding #3).
4. **Decide + document the ORDER BY policy** across literal kinds
   (finding #5). Either fix the comparator or add demo copy acknowledging
   the quirk.
5. **Round, don't truncate, AVG decimals** (finding #6) — or declare the
   rounding mode in docs.
6. **Output-prefix table in TriG** (finding #7). The demo should round-trip
   `ex:central` not `ex:lib/central`.
7. **Add the missing favicon** (pure cleanup).
8. **Add a larger synthetic dataset to the demo (or a hidden test page)**
   so perf tracing is worthwhile. The current largest (music, ~70 triples)
   runs in <100 ms and doesn't stress anything.
9. **Unicode-aware UCASE/LCASE** (finding #2) — tracked separately by
   the rule-#10 regex/case issue; mentioning here because demo users
   will hit it the moment they type a German name.

## Method notes

- Playwright MCP drove the page via dropdowns + `Run query` button.
- Chrome DevTools MCP was used for console checks and for the perf trace.
- All results above came from reading the rendered results table via
  `document.querySelector('main').innerText` in the page.
- Turtle textarea is editable (not readonly); switching the dataset
  dropdown regenerates its contents so hand-edits must happen after the
  final dropdown change.
- No PRs opened; this is a review only.
