module Parser.JSONLD

// ============================================================================
// JSON-LD deserialization to RDF.
//
// *****************************************************************
// *  THIS MODULE'S jld_* PIPELINE CONSUMES EXPANDED FORM ONLY.    *
// *  An array of node objects whose keys are absolute IRIs or     *
// *  keywords, and whose property values are arrays of node       *
// *  objects / node references / value objects / list objects.    *
// *  It does not itself interpret @context, resolve compact IRIs, *
// *  or resolve terms.                                            *
// *                                                                *
// *  PHASE 3a (JSONLD.Context / JSONLD.Expand, see                *
// *  docs/designissues/2026-07-04-jsonld-program-lessons.md) adds  *
// *  an expansion step in front: parse_jsonld below now runs       *
// *  JSONLD.Expand.expand over any document carrying an inline     *
// *  @context before handing the result to jld_dataset_of_json —   *
// *  it produces exactly the expanded-form json_val this module    *
// *  already expects. A document with no @context member still     *
// *  goes straight to jld_dataset_of_json (Phase 1 path,           *
// *  unchanged) so the existing context-free fixtures keep working *
// *  exactly as before — UNLESS a document base IRI is supplied     *
// *  (PHASE 6, issue #275): a document with no @context CAN still   *
// *  carry a bare relative "@id" that only resolves against the     *
// *  document's OWN base (the toRdf suite's option.base fixtures,   *
// *  e.g. e076), so `parse_jsonld`'s new `base` parameter also      *
// *  routes through JSONLD.Expand whenever it is `Some _`, seeding  *
// *  the initial active context's `ac_base` with it.                *
// *****************************************************************
//
// This is the "Deserialize JSON-LD to RDF" step of the JSON-LD 1.1
// Processing Algorithms and API spec (§8), simplified to expanded-form
// input. Supported here:
//   - node objects with absolute-IRI @id, blank-node @id (leading "_:"),
//     or no @id (fresh blank node from a counter-threaded pure allocator);
//   - @type on node objects (rdf:type triples; IRI or blank-node values);
//   - value objects: @value + @language -> language-tagged literal;
//     @value + @type -> typed literal; bare string @value -> xsd:string;
//     boolean @value -> xsd:boolean; number @value -> xsd:integer when
//     the lexeme has no fraction/exponent, xsd:double otherwise;
//   - @list -> rdf:first / rdf:rest / rdf:nil chains (empty list -> nil);
//   - top-level node objects carrying @graph -> named graphs (graph name
//     from @id: IRI, blank-node label — stored with the literal "_:"
//     prefix inside ng_name per the Parser.NQuads convention — or a
//     fresh blank node when @id is absent); a top-level object whose ONLY
//     key is @graph is the document wrapper and feeds the default graph;
//   - nested node objects in property position (their triples are
//     emitted and the node is referenced);
//   - bare JSON scalars in value position (string / boolean / number),
//     interpreted as the Expansion algorithm would wrap them — this
//     leniency keeps the context-free W3C toRdf inputs loadable.
//
// PHASE 3b adds @reverse consumption: a node object's ("@reverse", {predIri:
// [items...]}) field (produced by JSONLD.Expand for a term defined with
// "@reverse", or an inline "@reverse" block — see that module's banner)
// expands each item as an ordinary node reference / node object (exactly
// like jld_expand_value's node-object branch) and emits a triple with the
// item as SUBJECT, predIri as predicate, and the enclosing node as OBJECT
// — jld_expand_reverse_map / _entries / _prop below. A node object may
// carry more than one "@reverse" field-list entry (one inline block plus
// one or more reverse terms); jld_expand_fields already processes every
// field-list entry regardless of key repetition, so no merge step is
// needed on this side either.
//
// PHASE 5 adds @included consumption: a node object's ("@included",
// [nodeobj, ...]) field (produced by JSONLD.Expand exactly like "@graph"'s
// contents, see that module's banner) has each entry expanded as an
// ordinary node object whose triples join the CURRENT graph (`acc`) —
// jld_expand_graph_nodes, reused as-is — with NO linking triple to the
// enclosing node (unlike @reverse/ordinary properties, @included nodes
// are independent, merely co-located in the same graph). A node may
// carry more than one "@included" field-list entry (the literal keyword
// plus one or more aliasing terms, toRdf/in03); same no-merge-needed
// reasoning as @reverse above.
//
// PHASE 5 adds JSON-literal (@type: @json / rdf:JSON) consumption: a
// value object whose "@type" is the keyword "@json" (JSONLD.Expand keeps
// the ORIGINAL, unexpanded json_val under "@value" for this case — see
// that module's expand_property_items) is serialized via jld_json_canon
// below (an RFC 8785 JCS SUBSET — see that function's banner for exactly
// which cases are exact vs. an honest documented gap) into an rdf:JSON
// (http://.../1999/02/22-rdf-syntax-ns#JSON) typed literal.
//
// Phase-2+ items deliberately NOT handled here (dropped silently, per the
// spec's treatment of non-conforming data where possible):
//   - @context (see banner above);
//   - relative IRIs (dropped — is_iri requires a colon);
//   - @index, @direction, @graph nested below the top level (PHASE 4
//     handles nested @graph — see that phase's note above),
//     generalized RDF (blank-node predicates);
//   - canonical lexical forms for xsd:double per the JSON-LD Data
//     Round-Tripping algorithm (e.g. 2.5 SHOULD serialize as "2.5E0";
//     this phase keeps the validated JSON lexeme verbatim);
//   - duplicate-triple suppression (house parsers keep duplicates:
//     graph_add_unchecked + finalise, no dedup — same policy here).
//
// PERF SHAPE (per the program lessons doc): triples are PREPENDED onto
// accumulator lists (O(1) each, no membership scans) and every graph is
// reversed exactly once at the end via dataset_finalise. Blank-node
// allocation threads a nat counter through the recursion (same pattern
// as Parser.Turtle.fresh_bnode).
// ============================================================================

open FStar.String
open FStar.List.Tot
open Parser.FastString
open RDF.Graph.Executable
open Parser.JSON
open SPARQL.JSON.Escape
open JSONLD.Context
open JSONLD.Expand

// ================================================================
// RDF vocabulary constants
// ================================================================

let rdf_type_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

let rdf_first_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#first");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"

let rdf_rest_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"

let rdf_nil_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

let rdf_json_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON"

// toRdf/di11-di12: rdfDirection=compound-literal's three predicates
// (JSON-LD 1.1 API §8.6, "Compound-literal" branch of Object to RDF
// Conversion — see jld_compound_literal_term below).
let rdf_value_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#value");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#value"

let rdf_direction_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#direction");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#direction"

let rdf_language_iri : wf_iri =
  assert_norm (is_iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#language");
  "http://www.w3.org/1999/02/22-rdf-syntax-ns#language"

// ================================================================
// PHASE 5: JSON canonicalization for @type: @json (rdf:JSON) literals —
// an RFC 8785 JCS SUBSET.
//
// Exact for this suite's fixtures: booleans, null, numbers whose
// validated JNumber digit string already IS the shortest round-trip
// decimal for its nearest binary64 double (see jcanon_number below —
// covers plain integers, simple decimals, and ECMAScript-notation
// conversion: "1E30" -> "1e+30", "2e-3" -> "0.002", trailing-zero
// stripping "4.50" -> "4.5", small-magnitude scientific "1e-27"), plus
// strings (via SPARQL.JSON.Escape.json_escape — the same "\b\f\n\r\t\"
// \\, else \u00xy for other controls, everything else byte-transparent"
// rule JCS mandates), and object-key sorting (via
// RDF.Graph.Executable.string_lt, i.e. plain byte-order comparison —
// equal to Unicode codepoint order for valid UTF-8, which is what JCS's
// "sort by UTF-16 code unit" reduces to for every key in this suite;
// the two orders diverge only when comparing an astral-plane character,
// U+10000+, against a BMP character in U+E000..U+FFFF, which no
// toRdf/js* fixture exercises).
//
// NOT exact: a lexeme with MORE significant digits than distinguish
// between adjacent binary64 doubles (toRdf/js12's
// "333333333.33333329", 17 significant digits — every OTHER number in
// this same fixture, "1E30"/"4.50"/"2e-3"/"1e-27", has 1-2 significant
// digits and is unaffected) needs the actual
// nearest-binary64-then-shortest-round-trip computation — a Ryu/Grisu-
// class algorithm operating on the true IEEE 754 value — to know WHICH
// digits the shortest form keeps; jcanon_number does not attempt that
// (this codebase represents JSON numbers as validated lexeme strings,
// Parser.JSON.JNumber, not floats, and implementing binary64 rounding
// from scratch is out of scope for this phase). Such a lexeme's own
// digit string passes through the ECMAScript notation rules unchanged,
// which is an HONEST gap (the N-Quads comparison fails visibly,
// toRdf/js12 stays FAIL on this account) rather than a silently wrong
// literal.
//
// 2026-07-05 revisit (goal-wave JSON-LD pass): confirmed this is a
// REAL float-arithmetic gap, not a missing-but-easy string tweak —
// there is no way to decide "does this shorter decimal round-trip to
// the SAME nearest binary64 double" using only this codebase's exact-
// decimal (digit-string) model; it needs an actual IEEE 754 parse
// (float_of_string) plus a bounded "try precision 1..17, format,
// parse back, compare bit-pattern" search, i.e. the SAME `assume val`
// host-engine-call-out taxonomy as `regex_match` (SPARQL11.Algebra.fst)
// — a genuinely new capability this codebase doesn't have anywhere
// else, requiring a stub patch under
// minimal_regrettable_glue_code_each_with_an_open_issue/ plus a fresh
// tracking issue (CLAUDE.md rule #3). Left undone this pass rather
// than wiring a new assume val without one. If picked up: gate the
// call at jcanon_number's `k` (post-trailing-zero-strip significant
// digit count) `> 15` — every OTHER toRdf/js* fixture's numbers have
// 1-2 significant digits (see above) and must not go anywhere near
// the new code path.
// ================================================================

let rec jcanon_find_dot (s:string) (pos:nat) (fuel:nat)
  : Tot (option (p:nat{p < fs_byte_length s})) (decreases fuel) =
  if fuel = 0 then None
  else
    let n = fs_byte_length s in
    if pos >= n then None
    else if jbyte_at s pos = 0x2E then Some pos
    else jcanon_find_dot s (pos + 1) (fuel - 1)

// True for the ASCII digit bytes '0'-'9'.
let jld_is_digit_byte (b:int) : bool = b >= 0x30 && b <= 0x39

let jld_digit_val (b:int) : nat = if jld_is_digit_byte b then (b - 0x30) else 0

// Position of the first 'e'/'E' byte from `pos`, or None (mirrors
// jcanon_find_dot above, for the exponent marker instead of the dot).
let rec jld_find_exp_pos (s:string) (pos:nat) (fuel:nat)
  : Tot (option (p:nat{p < fs_byte_length s})) (decreases fuel) =
  if fuel = 0 then None
  else
    let n = fs_byte_length s in
    if pos >= n then None
    else if jbyte_at s pos = 0x65 || jbyte_at s pos = 0x45 then Some pos
    else jld_find_exp_pos s (pos + 1) (fuel - 1)

// Decimal digits s[pos..endpos) (endpos exclusive) as a nat, most-
// significant digit first. Fuel-bounded; a non-digit byte contributes 0
// (defensive — only ever called on RFC 8259-validated JNumber lexemes).
let rec jld_digits_to_nat (s:string) (pos:nat) (endpos:nat) (acc:nat) (fuel:nat)
  : Tot nat (decreases fuel) =
  if fuel = 0 then acc
  else if pos >= endpos then acc
  else jld_digits_to_nat s (pos + 1) endpos (op_Multiply acc 10 + jld_digit_val (jbyte_at s pos)) (fuel - 1)

// The exponent's signed integer value, starting right after the 'e'/'E'
// marker (an optional '+'/'-' then digits).
let jld_parse_exponent (s:string) (start:nat) : int =
  let n = fs_byte_length s in
  if start >= n then 0
  else
    let b0 = jbyte_at s start in
    if b0 = 0x2B (* + *) then jld_digits_to_nat s (start + 1) n 0 (n - start + 1)
    else if b0 = 0x2D (* - *) then (- (jld_digits_to_nat s (start + 1) n 0 (n - start + 1)))
    else jld_digits_to_nat s start n 0 (n - start + 1)

// Decompose a validated JSON number lexeme into (is_negative,
// int_part_start, int_part_len, frac_part_start, frac_part_len,
// exponent). frac_part_len = 0 when there is no '.'; exponent = 0 when
// there is no 'e'/'E'.
let jld_number_parts (lexeme:string) : (bool & nat & nat & nat & nat & int) =
  let n = fs_byte_length lexeme in
  let neg = n > 0 && jbyte_at lexeme 0 = 0x2D in
  let start0 = if neg then 1 else 0 in
  let dotpos = jcanon_find_dot lexeme start0 (n - start0 + 1) in
  let exppos = jld_find_exp_pos lexeme start0 (n - start0 + 1) in
  let int_end = (match dotpos with
                 | Some d -> d
                 | None -> (match exppos with Some e -> e | None -> n)) in
  let int_len = if int_end > start0 then int_end - start0 else 0 in
  let (frac_start, frac_len) =
    (match dotpos with
     | Some d ->
       let fend = (match exppos with Some e -> e | None -> n) in
       let flen = if fend > d + 1 then fend - d - 1 else 0 in
       (d + 1, flen)
     | None -> (0, 0)) in
  let exp = (match exppos with Some e -> jld_parse_exponent lexeme (e + 1) | None -> 0) in
  (neg, start0, int_len, frac_start, frac_len, exp)

// Index one past the last non-'0' byte of s (a plain, sign-free digit
// string), scanning forward from `pos` — i.e. the length to keep after
// stripping trailing zeros; 0 if every byte scanned is '0' (the
// all-zero / value-is-zero case, handled by the caller).
let rec jld_last_nonzero_len (s:string) (pos:nat) (best:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then best
  else
    let n = fs_byte_length s in
    if pos >= n then best
    else jld_last_nonzero_len s (pos + 1) (if jbyte_at s pos <> 0x30 then pos + 1 else best) (fuel - 1)

// Index of the first non-'0' byte of s, or fs_byte_length s if every
// byte is '0' (leading-zero stripping — the complementary scan to
// jld_last_nonzero_len above).
let rec jld_first_nonzero_pos (s:string) (pos:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then pos
  else
    let n = fs_byte_length s in
    if pos >= n then pos
    else if jbyte_at s pos <> 0x30 then pos
    else jld_first_nonzero_pos s (pos + 1) (fuel - 1)

// A string of `k` '0' bytes (for shifting an integral value's decimal
// point right by `k` places — e.g. digits "15" with a scientific
// exponent of 2 is the plain integer "1500").
let rec jld_zeros (k:nat) : Tot string (decreases k) =
  if k = 0 then "" else String.concat "" ["0"; jld_zeros (k - 1)]

// RFC 8785 (JCS) number serialization — ECMAScript Number::toString
// applied to the JSON number's value (JCS §3.2.2.3). Normalizes the
// lexeme to (sign, significant-digit string `digits` with no leading or
// trailing zeros, decimal exponent `n` such that the value equals
// 0.<digits> * 10^n — same decomposition jld_number_canonicalize below
// uses for the XSD canonical form), then applies the ECMA-262
// Number::toString formatting rules verbatim (current-spec numbering
// 6.1.6.1.20, steps 8-10; k = number of significant digits):
//   - k <= n <= 21: `digits` followed by (n - k) zeros, no decimal point
//     (an integer value written out in full, e.g. digits "15" n 4 -> "1500").
//   - 0 < n <= 21:  first n digits of `digits`, then ".", then the rest.
//   - -6 < n <= 0:  "0.", then (-n) zeros, then `digits`.
//   - otherwise:    exponential — first digit, then "." + the rest (if
//     more than one significant digit), then "e", an EXPLICIT sign, and
//     |n - 1|.
// See this section's banner for the honest gap (lexemes needing real
// binary64 rounding, not just notation conversion).
let jcanon_number (lexeme:string) : string =
  let (neg, int_start, int_len, frac_start, frac_len, exp) = jld_number_parts lexeme in
  let combined = String.concat "" [fs_byte_sub lexeme int_start int_len; fs_byte_sub lexeme frac_start frac_len] in
  let clen = fs_byte_length combined in
  let lead = jld_first_nonzero_pos combined 0 (clen + 1) in
  if lead >= clen then
    // The value is zero (JCS §3.2.2.3: negative zero also serializes as
    // "0" — `combined` already excludes the sign, so this collapses
    // both "0"/"0.0" and "-0"/"-0.0e5" alike).
    "0"
  else
    let after_lead = fs_byte_sub combined lead (clen - lead) in
    let exp_total = exp - frac_len in
    let keep = jld_last_nonzero_len after_lead 0 0 (fs_byte_length after_lead + 1) in
    let digits = fs_byte_sub after_lead 0 keep in
    let tz = fs_byte_length after_lead - keep in
    let exp_total1 = exp_total + tz in
    let k = fs_byte_length digits in
    let sci_exp = exp_total1 + k - 1 in
    let n = sci_exp + 1 in
    let sign_str = if neg then "-" else "" in
    if k <= n && n <= 21 then
      String.concat "" [sign_str; digits; jld_zeros (n - k)]
    else if 0 < n && n <= 21 then
      String.concat "" [sign_str; fs_byte_sub digits 0 n; "."; fs_byte_sub digits n (k - n)]
    else if (-6) < n && n <= 0 then
      String.concat "" [sign_str; "0."; jld_zeros (- n); digits]
    else
      let mantissa =
        (if k <= 1 then digits
         else String.concat "" [fs_byte_sub digits 0 1; "."; fs_byte_sub digits 1 (k - 1)]) in
      let e = n - 1 in
      let exp_str = (if e >= 0 then String.concat "" ["+"; string_of_int e] else string_of_int e) in
      String.concat "" [sign_str; mantissa; "e"; exp_str]

// JCS string: double-quoted, JSON-escaped per SPARQL.JSON.Escape's rule
// (identical to RFC 8785 §3.2.2.2's mandatory escape set).
let jcanon_string (s:string) : string =
  String.concat "" ["\""; SPARQL.JSON.Escape.json_escape s; "\""]

// Insertion-sort an object's fields by key, RFC 8785 §3.2.3 ("sort by
// code point" — see banner above for the UTF-16-vs-codepoint caveat).
let rec jcanon_insert_sorted (kv:(string & json_val)) (xs:list (string & json_val))
  : Tot (list (string & json_val)) (decreases xs) =
  match xs with
  | [] -> [kv]
  | (k2, v2) :: rest ->
    if string_lt (fst kv) k2 then kv :: xs
    else (k2, v2) :: jcanon_insert_sorted kv rest

let rec jcanon_sort_fields (fields:list (string & json_val))
  : Tot (list (string & json_val)) (decreases fields) =
  match fields with
  | [] -> []
  | kv :: rest -> jcanon_insert_sorted kv (jcanon_sort_fields rest)

// The JCS document itself: object keys sorted (jcanon_sort_fields),
// arrays kept in their given order, no whitespace between tokens (JCS
// mandates the tightest separators: ',' and ':' with nothing else).
// Fuel is a generous over-provision (matches JSONLD.Expand.expand's own
// "4 * json_size + 48" style — not a tight bound, just enough that a
// real, if deeply nested, JSON-literal fixture never trips the fuel=0
// safety net).
let rec jcanon_serialize (v:json_val) (fuel:nat) : Tot string (decreases fuel) =
  if fuel = 0 then "null"
  else
    match v with
    | JNull -> "null"
    | JBool b -> if b then "true" else "false"
    | JNumber lex -> jcanon_number lex
    | JString s -> jcanon_string s
    | JArray items -> String.concat "" ["["; jcanon_serialize_items items (fuel - 1); "]"]
    | JObject fields ->
      String.concat "" ["{"; jcanon_serialize_fields (jcanon_sort_fields fields) (fuel - 1); "}"]

and jcanon_serialize_items (items:list json_val) (fuel:nat) : Tot string (decreases fuel) =
  if fuel = 0 then ""
  else
    match items with
    | [] -> ""
    | [x] -> jcanon_serialize x (fuel - 1)
    | x :: rest ->
      String.concat "" [jcanon_serialize x (fuel - 1); ","; jcanon_serialize_items rest (fuel - 1)]

and jcanon_serialize_fields (fields:list (string & json_val)) (fuel:nat) : Tot string (decreases fuel) =
  if fuel = 0 then ""
  else
    match fields with
    | [] -> ""
    | [(k, v)] -> String.concat "" [jcanon_string k; ":"; jcanon_serialize v (fuel - 1)]
    | (k, v) :: rest ->
      String.concat "" [jcanon_string k; ":"; jcanon_serialize v (fuel - 1);
                         ","; jcanon_serialize_fields rest (fuel - 1)]

let jcanon_document (v:json_val) : string =
  jcanon_serialize v (op_Multiply 10 (json_size v) + 32)

// ================================================================
// JSON-LD 1.1 API §8.6 "Data Round Tripping": the canonical xsd:double
// lexical form (ECMAScript-ish "shortest form" scientific notation,
// e.g. "5.3E0", "1.0E21") plus the integer-vs-double DEFAULT DATATYPE
// promotion for a bare (uncoerced) JSON number.
//
// Two INDEPENDENT decisions determined by a JSON number lexeme's actual
// MATHEMATICAL VALUE (not its lexical shape — toRdf/rt01's "-0e0" LOOKS
// double-shaped, having an 'e', but its value 0 is a plain integer):
//   - is_integral: the value has no fractional part.
//   - magnitude_ge_1e21: abs(value) >= 1e21.
// `force_double` (true only for an explicit "@type": xsd:double term
// coercion — Parser.JSONLD.jld_value_object_to_term's typed branch)
// makes the LEXICAL form double-shaped regardless of value (toRdf/0035:
// a term coerced to xsd:double renders the PLAIN INTEGER literal "1" as
// "1.0E0"). Independent of force_double, ANY non-integral value or
// magnitude >= 1e21 ALSO renders double-shaped, even under a DIFFERENT
// declared datatype (toRdf/0035: a term coerced to xsd:integer still
// renders "9.9" as "9.9E0" — the datatype IRI is whatever the term
// declared; only the LEXICAL FORM tracks the value's own shape). When
// no term coercion applies at all (force_double = false, and the
// caller — jld_scalar_to_term — has no separate datatype to keep), the
// same use-double decision ALSO picks the DEFAULT datatype: double
// datatype iff double-shaped rendering was used, else xsd:integer.
//
// The digit-extraction helpers this section used to define here
// (jld_is_digit_byte .. jld_zeros) moved UP to just before jcanon_number
// (JCS canonicalization section, above) — jcanon_number's RFC 8785
// number formatting needs the exact same "normalize to (sign, sig-digit-
// string, decimal exponent)" decomposition this xsd:double canonicalizer
// does, so the two share one normalization pass instead of duplicating
// it. Nothing in this section's OWN logic changed.
// ================================================================

// The canonical lexical form of a validated JSON number lexeme, plus
// whether it rendered double-shaped (see this section's banner for the
// full decision table). `force_double`: true only for an explicit
// "@type": xsd:double term coercion.
let jld_number_canonicalize (lexeme:string) (force_double:bool) : (string & bool) =
  let (neg, int_start, int_len, frac_start, frac_len, exp) = jld_number_parts lexeme in
  let combined = String.concat "" [fs_byte_sub lexeme int_start int_len; fs_byte_sub lexeme frac_start frac_len] in
  let clen = fs_byte_length combined in
  let lead = jld_first_nonzero_pos combined 0 (clen + 1) in
  if lead >= clen then
    // The value is zero (every significant digit is '0', or there were
    // none at all — a malformed lexeme, which a validated JNumber never
    // is, defaults harmlessly to zero too).
    (if force_double then ("0.0E0", true) else ("0", false))
  else
    let after_lead = fs_byte_sub combined lead (clen - lead) in
    let exp_total = exp - frac_len in
    let keep = jld_last_nonzero_len after_lead 0 0 (fs_byte_length after_lead + 1) in
    let digits = fs_byte_sub after_lead 0 keep in
    let tz = fs_byte_length after_lead - keep in
    let exp_total1 = exp_total + tz in
    let ndigits = fs_byte_length digits in
    let sci_exp = exp_total1 + ndigits - 1 in
    let is_integral = exp_total1 >= 0 in
    let magnitude_ge_1e21 = sci_exp >= 21 in
    let use_double = force_double || (not is_integral) || magnitude_ge_1e21 in
    let sign_str = if neg then "-" else "" in
    if use_double then
      let mantissa_first = fs_byte_sub digits 0 1 in
      let mantissa_rest = if ndigits > 1 then fs_byte_sub digits 1 (ndigits - 1) else "0" in
      let lexical = String.concat "" [sign_str; mantissa_first; "."; mantissa_rest; "E"; string_of_int sci_exp] in
      (lexical, true)
    else
      let lexical = String.concat "" [sign_str; digits; jld_zeros exp_total1] in
      (lexical, false)

// ================================================================
// rdfDirection option (JSON-LD 1.1 API "Deserialize JSON-LD to RDF",
// §8.6's rdfDirection processing-mode flag): how a value object's
// "@direction" (threaded through the expanded form by JSONLD.Expand —
// see that module's jexp_expand_value_object / expand_item) becomes RDF.
//   - RDM_Drop (no rdfDirection option given): direction is DROPPED —
//     the literal comes out exactly as it would with no @direction at
//     all (language tag kept if present) — toRdf/di01-di07's default
//     behavior.
//   - RDM_I18nDatatype ("i18n-datatype"): the literal's datatype becomes
//     https://www.w3.org/ns/i18n#<lang>_<dir> (lang lowercased, omitted
//     entirely — "_<dir>" — when there is no @language), replacing
//     rdf:langString / xsd:string — toRdf/di09-di10.
//   - RDM_CompoundLiteral ("compound-literal"): a @direction-bearing
//     value object becomes a FRESH BLANK NODE bearing rdf:value/
//     rdf:direction/rdf:language triples rather than a single literal
//     term — jld_value_object_to_term still returns None for this case
//     (a single-term return can't express the extra triples + bnode
//     allocation), but jld_expand_value's @value branch intercepts
//     RDM_CompoundLiteral + @direction BEFORE calling
//     jld_value_object_to_term and calls jld_compound_literal_term
//     instead (toRdf/di11-di12) — see that function's banner.
type rdf_direction_mode =
  | RDM_Drop
  | RDM_I18nDatatype
  | RDM_CompoundLiteral

// ================================================================
// Small helpers
// ================================================================

// Fresh blank node from a threaded counter (cf. Parser.Turtle.fresh_bnode).
// The "_jld_anon" prefix keeps generated labels visually distinct from
// document-supplied "_:..." labels; a malicious document could still
// collide with it, which Phase 2 can guard by namespacing document labels.
let jld_fresh_bnode (ctr:nat) : (bnode_id & nat) =
  (String.concat "" ["_jld_anon"; string_of_int ctr], ctr + 1)

// True when s begins with the two bytes "_:" (blank-node identifier).
let jld_is_bnode_label (s:string) : bool =
  jbyte_at s 0 = 0x5F && jbyte_at s 1 = 0x3A

// Strip the leading "_:" (bnode_id fields store the label without it;
// serializers re-add it).
let jld_strip_bnode_prefix (s:string) : string =
  let n = fs_byte_length s in
  if n >= 2 then fs_byte_sub s 2 (n - 2) else s

// toRdf/wf01-wf05, wf07, e123 ("well-formedness" battery): a stricter-
// than-shared-`is_iri` gate for IRI/language-tag strings arriving from
// JSON-LD input. RDF.Graph.Executable.is_iri (colon + non-empty) is
// deliberately minimal — every concrete-syntax PARSER enforces its OWN
// grammar (e.g. Parser.Turtle's IRIREF scanner rejects raw spaces via
// its own character class) before a value ever reaches that shared
// model; this module's jld_* pipeline had no equivalent gate of its
// own, so a JSON string containing a raw space (or other IRI-illegal
// byte) sailed through as a "well-formed" IRI. `jld_iri_wf` / `jld_
// lang_tag_wf` close that gap: reject the ASCII control range
// (0x00-0x20, which covers the plain space every wf0x fixture tests)
// plus the handful of bytes RFC 3987 excludes from every IRI reference
// (<>"{}|\^`). An HONEST SUBSET of full IRI-reference / BCP47
// well-formedness (percent-encoding validity, language-subtag grammar,
// etc. are NOT checked) — enough for the toRdf suite's negative
// fixtures, not a general-purpose validator.
let jld_forbidden_byte (b:int) : bool =
  (b >= 0 && b <= 0x20) || b = 0x3C (* < *) || b = 0x3E (* > *) || b = 0x22 (* " *)
  || b = 0x7B (* { *) || b = 0x7D (* } *) || b = 0x7C (* | *) || b = 0x5C (* \ *)
  || b = 0x5E (* ^ *) || b = 0x60 (* ` *)

let rec jld_scan_wf (s:string) (pos:nat) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then true
  else
    let n = fs_byte_length s in
    if pos >= n then true
    else if jld_forbidden_byte (jbyte_at s pos) then false
    else jld_scan_wf s (pos + 1) (fuel - 1)

// toRdf/e111-e112: an IRI reference has AT MOST ONE fragment delimiter
// — RFC 3986 §3.5's fragment grammar is `*( pchar / "/" / "?" )`, which
// excludes a bare "#" (a second, unescaped "#" would open an ambiguous
// second fragment). A vocab-relative property-key expansion that
// concatenates a vocab mapping ENDING in "#" onto a key that itself
// STARTS with "#" (e111: vocab "http://example.com/vocabulary/./rel2#"
// + key "#fragment-works") produces exactly this malformed shape —
// JSONLD.Context's plain string-concatenation vocab expansion
// (jldctx_expand_fallback) has no reason to special-case it (the
// concatenation itself is the spec-mandated behavior for a vocab-
// relative key — see that function's banner), so the resulting
// doubly-fragmented string must be caught here, at the well-formedness
// gate every predicate/subject/@type IRI already passes through.
let rec jld_count_hash (s:string) (pos:nat) (n:nat) (fuel:nat) : Tot nat (decreases fuel) =
  if fuel = 0 then n
  else
    let len = fs_byte_length s in
    if pos >= len then n
    else if jbyte_at s pos = 0x23 (* # *) then jld_count_hash s (pos + 1) (n + 1) (fuel - 1)
    else jld_count_hash s (pos + 1) n (fuel - 1)

let jld_at_most_one_fragment (s:string) : bool =
  jld_count_hash s 0 0 (fs_byte_length s + 1) <= 1

let jld_iri_wf (s:string) : bool =
  is_iri s && jld_scan_wf s 0 (fs_byte_length s + 1) && jld_at_most_one_fragment s

let jld_lang_tag_wf (s:string) : bool =
  jld_scan_wf s 0 (fs_byte_length s + 1)

// toRdf/e068, e075, e038, t0118 ("generalized RDF" battery): a PREDICATE
// position needs a stricter gate than jld_iri_wf. `is_iri` only requires a
// colon, so a blank-node identifier like "_:property" (an ordinary
// EXPANDED-form property key when a term or @vocab maps to a "_:..."
// string — toRdf/e068's `"_:property"` key, e075's `@vocab: "_:"`)
// satisfies it and used to sail through as a bogus "wf_iri" predicate,
// later serialized as the malformed pseudo-IRI `<_:property>` (RDF.
// Canonical.fst always brackets t.p — it has no blank-node-predicate
// print form, because RDF.NQuads' grammar makes a predicate position
// IRIREF-only, i.e. "generalized RDF" triples are not expressible in
// this codebase's N-Quads at all).
//
// The JSON-LD API "Deserialize JSON-LD to RDF" algorithm's answer is:
// keep such triples ONLY when the (now-retired-in-1.1, 1.0-only)
// "produce generalized RDF" flag is set, else drop the property
// entirely (continue to next key). This codebase does not thread that
// flag (no generalized-RDF-aware N-Quads serializer/parser exists to
// make "keep" observably correct either way — see the N-Quads-grammar
// note above), so it drops unconditionally: the common (flag-false)
// case per spec, and — empirically, per the toRdf/0118 fixture, whose
// OWN expected output can only round-trip its single ordinary
// (rdf:type) triple through this codebase's strict-IRIREF-predicate
// N-Quads parser, every blank-predicate line in 0118-out.nq being
// unparseable and silently dropped exactly the same way (see
// Parser.NQuads.parse_nquads_acc's "skip to next line on parse
// failure") — dropping here also matches the flag-true fixtures. No
// misrepresentation either way: this module simply never emits an
// (always-wrong-looking) `<_:...>` pseudo-IRI predicate.
let jld_predicate_iri_wf (s:string) : bool =
  jld_iri_wf s && not (jld_is_bnode_label s)

// Expanded-form @id string -> subject. Relative IRIs yield None (dropped).
let jld_id_to_subject (s:string) : option subject =
  if jld_is_bnode_label s then Some (S_BNode (jld_strip_bnode_prefix s))
  else if jld_iri_wf s then Some (S_IRI s)
  else None

// Keywords all start with a commercial-at byte.
let jld_is_keyword (k:string) : bool =
  jbyte_at k 0 = 0x40

// Expanded form wraps property values in arrays; be lenient about a bare
// object where an array is required.
let jld_as_array (v:json_val) : list json_val =
  match v with
  | JArray items -> items
  | _ -> [v]

// Construct a T_Literal only if well-formed. Same shape as
// Parser.JSONResults.mk_literal; duplicated (it is four lines) rather
// than importing that module, whose lenient embedded JSON parser this
// module exists to bypass. Unify when Parser.JSONResults migrates onto
// Parser.JSON.
let jld_make_literal (lexical:string) (dt:string) (lang:option string)
  : option rdf_term =
  // toRdf/e123: an invalid datatype IRI (e.g. containing a raw space) is
  // rejected via jld_iri_wf, not the shared (minimal) is_iri; toRdf/wf05:
  // likewise for an invalid @language value, via jld_lang_tag_wf.
  if jld_iri_wf dt && (match lang with Some l -> jld_lang_tag_wf l | None -> true) then
    let lit : literal = { lexical_form = lexical; datatype = dt; lang_tag = lang } in
    if literal_wf lit then Some (T_Literal lit) else None
  else None

// A bare JSON scalar in value position, as the Expansion algorithm would
// wrap it: string -> xsd:string, boolean -> xsd:boolean, number ->
// xsd:integer or xsd:double per jld_number_canonicalize's promotion
// rule (the value's own magnitude/integrality, NOT its lexical shape —
// see that function's banner). Accepting bare scalars keeps the
// context-free W3C toRdf inputs (e.g. toRdf/0001) loadable even though
// strict expanded form array-wraps every value.
let jld_scalar_to_term (v:json_val) : option rdf_term =
  match v with
  | JString str -> jld_make_literal str xsd_string None
  | JBool b -> jld_make_literal (if b then "true" else "false") xsd_boolean None
  | JNumber n ->
    let (lex, is_double) = jld_number_canonicalize n false in
    jld_make_literal lex (if is_double then xsd_double else xsd_integer) None
  | _ -> None

// ================================================================
// Value objects (@value)
// ================================================================

// i18n-datatype rdfDirection encoding (JSON-LD 1.1 API §8.6): the
// literal's datatype becomes https://www.w3.org/ns/i18n#<lang>_<dir>,
// with the language part lowercased (toRdf/di10: "@language": "en-US"
// -> datatype suffix "en-us_rtl", but the LEXICAL value keeps its
// original casing) and omitted entirely (just "_<dir>") when there is
// no @language (toRdf/di09).
let jld_i18n_direction_iri (lang:option string) (dir:string) : string =
  let langpart = (match lang with Some lg -> FStar.String.lowercase lg | None -> "") in
  String.concat "" ["https://www.w3.org/ns/i18n#"; langpart; "_"; dir]

// JSON-LD 1.1 API §8.6 "Object to RDF Conversion", value-object half,
// restricted to expanded form. Returns None for non-conforming value
// objects (both @language and @type; @language on a non-string @value;
// null / structured @value; invalid @type IRI). `rdir`: the rdfDirection
// processing mode (see rdf_direction_mode's doc comment above) governing
// what a "@direction"-bearing value object (JSONLD.Expand threads
// @direction through the expanded form exactly like @language — see
// that module's banner) becomes at the RDF layer.
let jld_value_object_to_term (rdir:rdf_direction_mode) (obj:json_val) : option rdf_term =
  match json_get_field "@value" obj with
  | None -> None
  | Some v ->
    let lang = json_get_string "@language" obj in
    let dt = json_get_string "@type" obj in
    let dir = json_get_string "@direction" obj in
    (match dir, dt with
     | Some _, Some _ -> None
     | Some d, None ->
       (match rdir with
        | RDM_Drop ->
          // Direction dropped: comes out exactly as it would with no
          // @direction present at all (toRdf/di01-di07).
          (match v with
           | JString s ->
             (match lang with
              | Some lg -> jld_make_literal s rdf_lang_string (Some lg)
              | None -> jld_make_literal s xsd_string None)
           | _ -> None)
        | RDM_I18nDatatype ->
          (match v with
           | JString s -> jld_make_literal s (jld_i18n_direction_iri lang d) None
           | _ -> None)
        | RDM_CompoundLiteral ->
          // Handled one level up: jld_expand_value's @value branch
          // intercepts RDM_CompoundLiteral + @direction before ever
          // calling this function (a compound-literal encoding needs a
          // fresh blank node plus rdf:value/rdf:direction/rdf:language
          // triples, which this function's single-term return shape
          // can't express — see jld_compound_literal_term). Reachable
          // here only if a future caller invokes this function directly
          // for a @direction-bearing object under this mode; None is the
          // safe/no-worse-than-before answer in that case.
          None)
     | None, Some d ->
       if d = "@json" then
         // PHASE 5: JSONLD.Expand's expand_property_items keeps the
         // ORIGINAL (unexpanded) json_val under "@value" for a @json-
         // coerced term — v here may be any json_val shape (object,
         // array, string, number, bool, null), not just a scalar.
         jld_make_literal (jcanon_document v) rdf_json_iri None
       else
         (match v with
          | JString s -> jld_make_literal s d None
          | JBool b -> jld_make_literal (if b then "true" else "false") d None
          | JNumber n ->
            // toRdf/0035: the LEXICAL form still tracks the value's own
            // shape (double-shaped even under a xsd:integer coercion,
            // e.g. "9.9" -> "9.9E0"^^xsd:integer) while the DATATYPE IRI
            // stays whatever this term declared — see
            // jld_number_canonicalize's banner. force_double (d =
            // xsd:double exactly) makes even an integer-shaped lexeme
            // like "1" render as "1.0E0".
            let (lex, _) = jld_number_canonicalize n (d = xsd_double) in
            jld_make_literal lex d None
          | _ -> None)
     | None, None ->
       (match lang with
        | Some lg ->
          (match v with
           | JString s -> jld_make_literal s rdf_lang_string (Some lg)
           | _ -> None)
        | None -> jld_scalar_to_term v))

// ================================================================
// @type entries on node objects
// ================================================================

let jld_type_term (t:string) : option rdf_term =
  if jld_is_bnode_label t then Some (T_BNode (jld_strip_bnode_prefix t))
  else if jld_iri_wf t then Some (T_IRI t)
  else None

let rec jld_type_prepend_items (subj:subject) (items:list json_val) (acc:list triple)
  : Tot (list triple) (decreases items) =
  match items with
  | [] -> acc
  | JString t :: rest ->
    (match jld_type_term t with
     | Some tm ->
       jld_type_prepend_items subj rest ({ s = subj; p = rdf_type_iri; o = tm } :: acc)
     | None -> jld_type_prepend_items subj rest acc)
  | _ :: rest -> jld_type_prepend_items subj rest acc

let jld_type_prepend (subj:subject) (v:json_val) (acc:list triple) : list triple =
  jld_type_prepend_items subj (jld_as_array v) acc

// ================================================================
// Expansion of node objects / property values / lists
//
// All functions thread (accumulator, counter, named-graph list) and
// PREPEND triples/named-graphs onto their accumulators; the caller
// reverses once at the end. Fuel bounds the recursion; parse_jsonld
// derives it from json_size, which dominates every call-chain length
// here (one fuel unit per value, array element, or object member
// visited).
//
// PHASE 4 adds `named` (list named_graph) as a fourth threaded value
// alongside (ctr, acc): the RDF dataset model is flat (a named graph
// cannot itself directly nest another named graph), so `named` is simply
// a GROWING, GLOBAL list of every named graph discovered ANYWHERE in the
// document tree — at the top level (unchanged from Phase 1/2) AND now at
// ANY nesting depth, whenever jld_expand_node meets an "@graph" member on
// a node object that is not the top-level document wrapper (e.g. a
// property value produced by a graph-container term — see
// JSONLD.Expand's banner for "@container": "@graph" et al, and
// docs/designissues/2026-07-04-jsonld-program-lessons.md's Phase-1
// "nested @graph below the top level" limitation this closes). `acc`
// always means "the CURRENT graph's triples" (default graph, or whatever
// named graph the caller is presently building via jld_expand_graph_nodes
// — see jld_expand_node's "@graph" branch below for exactly how a nested
// graph's own contents are separated from its enclosing graph's).
// ================================================================

// Graph name slot for a named graph. Blank-node graph names are stored
// as the literal string "_:<label>" inside the iri-typed ng_name field —
// the Parser.NQuads convention (see that module's header and
// docs/designissues/2026-04-25-nquads-bnode-graph-fix.md). Defined here,
// ahead of the mutual recursion group below, because jld_expand_node
// (PHASE 4) now calls it directly for a nested "@graph" member's name.
let jld_graph_name_of_subject (s:subject) : iri =
  match s with
  | S_IRI i -> i
  | S_BNode b -> String.concat "" ["_:"; b]

// toRdf/di11-di12: rdfDirection=compound-literal (JSON-LD 1.1 API §8.6,
// "Object to RDF Conversion" compound-literal branch). A @direction-
// bearing value object becomes a FRESH BLANK NODE carrying rdf:value
// (the lexical form), rdf:direction (the direction string), and — only
// when @language is present — rdf:language (LOWERCASED, toRdf/di12) as
// plain xsd:string triples, in place of a single literal term. This is
// the one value-object shape whose RDF isn't a single term (every
// other case returns Some rdf_term with acc/ctr untouched — see
// jld_value_object_to_term above), which is why it needs its own
// (acc, ctr)-threading function rather than folding into that one.
let jld_compound_literal_term (lex:string) (lang:option string) (dir:string) (ctr:nat) (acc:list triple)
  : (rdf_term & list triple & nat) =
  let (b, ctr1) = jld_fresh_bnode ctr in
  let bsubj = S_BNode b in
  let value_lit : wf_literal = { lexical_form = lex; datatype = xsd_string; lang_tag = None } in
  let dir_lit : wf_literal = { lexical_form = dir; datatype = xsd_string; lang_tag = None } in
  let acc1 = { s = bsubj; p = rdf_value_iri; o = T_Literal value_lit } :: acc in
  let acc2 = { s = bsubj; p = rdf_direction_iri; o = T_Literal dir_lit } :: acc1 in
  let acc3 =
    (match lang with
     | Some lg ->
       let lang_lit : wf_literal = { lexical_form = FStar.String.lowercase lg; datatype = xsd_string; lang_tag = None } in
       { s = bsubj; p = rdf_language_iri; o = T_Literal lang_lit } :: acc2
     | None -> acc2) in
  (T_BNode b, acc3, ctr1)

// jld_expand_value's @value branch dispatcher: intercepts the ONE case
// jld_value_object_to_term cannot express (RDM_CompoundLiteral + a
// @direction-bearing, @type-free, string @value — the same guard
// jld_value_object_to_term's own `Some d, None` branch uses to reach
// its RDM_CompoundLiteral arm) and routes it to
// jld_compound_literal_term; every other value object (no @direction,
// @direction under RDM_Drop/RDM_I18nDatatype, an @type value object,
// etc.) is unaffected and goes through the ordinary single-term path
// unchanged.
let jld_value_object_step (rdir:rdf_direction_mode) (obj:json_val) (ctr:nat) (acc:list triple)
  : (option rdf_term & list triple & nat) =
  match rdir, json_get_string "@direction" obj, json_get_string "@type" obj, json_get_field "@value" obj with
  | RDM_CompoundLiteral, Some dir, None, Some (JString lex) ->
    let lang = json_get_string "@language" obj in
    let (t, acc1, ctr1) = jld_compound_literal_term lex lang dir ctr acc in
    (Some t, acc1, ctr1)
  | _ -> (jld_value_object_to_term rdir obj, acc, ctr)

// A property value in expanded form: value object, list object, node
// object, or node reference. Returns the term to link to (None when the
// entry is non-conforming and must be dropped) plus updated acc/named/counter.
let rec jld_expand_value (rdir:rdf_direction_mode) (v:json_val) (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (option rdf_term & list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (None, acc, named, ctr)
  else
    match v with
    | JObject _ ->
      (match json_get_field "@value" v with
       | Some _ ->
         let (t, acc1, ctr1) = jld_value_object_step rdir v ctr acc in
         (t, acc1, named, ctr1)
       | None ->
         (match json_get_field "@list" v with
          | Some lst ->
            let (t, acc1, named1, ctr1) = jld_expand_list rdir (jld_as_array lst) ctr acc named (fuel - 1) in
            (Some t, acc1, named1, ctr1)
          | None ->
            let (osubj, acc1, named1, ctr1) = jld_expand_node rdir v ctr acc named (fuel - 1) in
            (match osubj with
             | Some subj -> (Some (subject_to_term subj), acc1, named1, ctr1)
             | None -> (None, acc1, named1, ctr1))))
    | _ -> (jld_scalar_to_term v, acc, named, ctr)

// JSON-LD 1.1 API §8.3 "List to RDF Conversion": ONE rdf:first/rdf:rest
// cell per original @list ARRAY MEMBER — allocated unconditionally
// (the algorithm's step 2 pre-allocates a blank node per item BEFORE
// attempting each item's own Object-to-RDF conversion), chained via
// rdf:rest regardless of whether any individual member's conversion
// succeeds; only the rdf:first triple for a cell is conditional on that
// member's conversion producing a term (step 4c: "If result is not
// null, append..."). A member that fails to become a term (e.g.
// toRdf/li12/li14: a @type:@id-coerced list item whose value can't
// resolve to a well-formed absolute IRI under an invalid/absent @base)
// still gets its bnode cell and rdf:rest link — it just carries no
// rdf:first triple. Previously this dropped the whole cell (skipping
// straight to the next item), which under-counts cells and, for a
// single-item list, wrongly collapses the property object straight to
// rdf:nil instead of to a one-cell "gap" list.
and jld_expand_list (rdir:rdf_direction_mode) (items:list json_val) (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (rdf_term & list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (T_IRI rdf_nil_iri, acc, named, ctr)
  else
    match items with
    | [] -> (T_IRI rdf_nil_iri, acc, named, ctr)
    | item :: rest ->
      let (oterm, acc1, named1, ctr1) = jld_expand_value rdir item ctr acc named (fuel - 1) in
      let (cell, ctr2) = jld_fresh_bnode ctr1 in
      let (rest_term, acc2, named2, ctr3) = jld_expand_list rdir rest ctr2 acc1 named1 (fuel - 1) in
      let cell_subj = S_BNode cell in
      let acc3 = { s = cell_subj; p = rdf_rest_iri; o = rest_term } :: acc2 in
      let acc4 = (match oterm with
                  | Some t -> { s = cell_subj; p = rdf_first_iri; o = t } :: acc3
                  | None -> acc3) in
      (T_BNode cell, acc4, named2, ctr3)

// A node object: subject from @id (fresh bnode when absent), then every
// member. Returns None subject (and prepends nothing) on a malformed @id.
// PHASE 4: an "@graph" member (produced by a graph-container term, or a
// document literally nesting "@graph" below the top level) introduces a
// FRESH, SEPARATE named graph rather than being silently dropped as an
// unrecognized keyword — its contents are expanded via
// jld_expand_graph_nodes into their OWN triple list (not `acc`), added to
// `named` under this node's subject as the graph name; every OTHER
// member of this same node object still describes the graph-name
// resource in the ENCLOSING graph (`acc`), same as the top-level
// "@graph" wrapper always did.
and jld_expand_node (rdir:rdf_direction_mode) (v:json_val) (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (option subject & list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (None, acc, named, ctr)
  else
    match v with
    | JObject fields ->
      let (subj_opt, ctr1) =
        (match json_get_field "@id" v with
         | Some (JString id_str) -> (jld_id_to_subject id_str, ctr)
         | Some _ -> (None, ctr)
         | None ->
           let (b, ctr') = jld_fresh_bnode ctr in
           (Some (S_BNode b), ctr')) in
      (match subj_opt with
       | None -> (None, acc, named, ctr1)
       | Some subj ->
         (match json_get_field "@graph" v with
          | Some g ->
            let (gtris, named1, ctr2) = jld_expand_graph_nodes rdir (jld_as_array g) ctr1 [] named (fuel - 1) in
            let ng = { ng_name = jld_graph_name_of_subject subj; ng_graph = gtris } in
            let (acc1, named2, ctr3) = jld_expand_fields rdir subj fields ctr2 acc (ng :: named1) (fuel - 1) in
            (Some subj, acc1, named2, ctr3)
          | None ->
            let (acc1, named1, ctr2) = jld_expand_fields rdir subj fields ctr1 acc named (fuel - 1) in
            (Some subj, acc1, named1, ctr2)))
    | _ -> (None, acc, named, ctr)

// Members of a node object. @type emits rdf:type triples; @reverse emits
// swapped-direction triples (jld_expand_reverse_map, PHASE 3b); @graph
// was already consumed by jld_expand_node (PHASE 4) before this is
// called, so it is harmless for the keyword-skip branch below to see it
// again; other keywords are skipped (@id was consumed by jld_expand_node);
// IRI keys emit property triples; non-IRI (relative) keys are dropped.
and jld_expand_fields (rdir:rdf_direction_mode) (subj:subject) (fields:list (string & json_val))
                      (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (acc, named, ctr)
  else
    match fields with
    | [] -> (acc, named, ctr)
    | (key, value) :: rest ->
      let (acc1, named1, ctr1) =
        if key = "@type" then (jld_type_prepend subj value acc, named, ctr)
        else if key = "@reverse" then jld_expand_reverse_map rdir subj value ctr acc named (fuel - 1)
        else if key = "@included" then
          // PHASE 5: each entry is a full node object (produced by
          // JSONLD.Expand exactly like "@graph"'s contents — see that
          // module's banner) whose triples join the CURRENT graph, with
          // no linking triple to `subj` — jld_expand_graph_nodes already
          // does exactly this (expand every node, threading acc), we
          // just don't route the result into a fresh named graph.
          jld_expand_graph_nodes rdir (jld_as_array value) ctr acc named (fuel - 1)
        else if jld_is_keyword key then (acc, named, ctr)
        else if jld_predicate_iri_wf key then
          jld_expand_property rdir subj key (jld_as_array value) ctr acc named (fuel - 1)
        else (acc, named, ctr) in
      jld_expand_fields rdir subj rest ctr1 acc1 named1 (fuel - 1)

// A node object's "@reverse" member: {predIri: [items...], ...} (an
// EXPANDED-form-only shape produced by JSONLD.Expand — see that module's
// banner). Each predIri key must already be an absolute IRI (Expand only
// ever produces one via expand_iri); a malformed key is dropped.
and jld_expand_reverse_map (rdir:rdf_direction_mode) (subj:subject) (v:json_val) (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (acc, named, ctr)
  else
    match v with
    | JObject entries -> jld_expand_reverse_entries rdir subj entries ctr acc named (fuel - 1)
    | _ -> (acc, named, ctr)

and jld_expand_reverse_entries (rdir:rdf_direction_mode) (subj:subject) (entries:list (string & json_val))
                               (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (acc, named, ctr)
  else
    match entries with
    | [] -> (acc, named, ctr)
    | (prop, value) :: rest ->
      let (acc1, named1, ctr1) =
        if jld_predicate_iri_wf prop
        then jld_expand_reverse_prop rdir subj prop (jld_as_array value) ctr acc named (fuel - 1)
        else (acc, named, ctr) in
      jld_expand_reverse_entries rdir subj rest ctr1 acc1 named1 (fuel - 1)

// One reverse predicate's array of item values: each item expands as a
// node reference / node object exactly like an ordinary property value
// (jld_expand_node — a bare literal value object has no subject identity
// and is silently dropped, same non-conforming-input leniency as
// elsewhere); the emitted triple points FROM the item TO the enclosing
// node (the direction swap that makes it a "reverse" property).
and jld_expand_reverse_prop (rdir:rdf_direction_mode) (subj:subject) (prop:wf_iri) (vals:list json_val)
                            (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (acc, named, ctr)
  else
    match vals with
    | [] -> (acc, named, ctr)
    | v :: rest ->
      let (osubj, acc1, named1, ctr1) = jld_expand_node rdir v ctr acc named (fuel - 1) in
      let acc2 =
        (match osubj with
         | Some vsubj -> { s = vsubj; p = prop; o = subject_to_term subj } :: acc1
         | None -> acc1) in
      jld_expand_reverse_prop rdir subj prop rest ctr1 acc2 named1 (fuel - 1)

// The array of values of one property.
and jld_expand_property (rdir:rdf_direction_mode) (subj:subject) (prop:wf_iri) (vals:list json_val)
                        (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (acc, named, ctr)
  else
    match vals with
    | [] -> (acc, named, ctr)
    | v :: rest ->
      let (oterm, acc1, named1, ctr1) = jld_expand_value rdir v ctr acc named (fuel - 1) in
      let acc2 =
        (match oterm with
         | Some t -> { s = subj; p = prop; o = t } :: acc1
         | None -> acc1) in
      jld_expand_property rdir subj prop rest ctr1 acc2 named1 (fuel - 1)

// Expand every node object inside a @graph array. PHASE 4: threads
// `named` too, since one of these nodes may itself carry a further
// nested "@graph" member (jld_expand_node handles that) — in the SAME
// mutual-recursion group as jld_expand_node itself now that jld_expand_node
// calls it directly (its own "@graph"-member branch, PHASE 4), not just
// jld_expand_top.
and jld_expand_graph_nodes (rdir:rdf_direction_mode) (nodes:list json_val) (ctr:nat) (acc:list triple) (named:list named_graph) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (acc, named, ctr)
  else
    match nodes with
    | [] -> (acc, named, ctr)
    | n :: rest ->
      let (_, acc1, named1, ctr1) = jld_expand_node rdir n ctr acc named (fuel - 1) in
      jld_expand_graph_nodes rdir rest ctr1 acc1 named1 (fuel - 1)

// ================================================================
// Top level: default graph + named graphs
// ================================================================

// One top-level array entry. dflt and the per-named-graph triple lists
// are reversed accumulators; named collects named graphs in reverse.
let jld_expand_top (rdir:rdf_direction_mode) (v:json_val) (dflt:list triple) (named:list named_graph)
                   (ctr:nat) (fuel:nat)
  : (list triple & list named_graph & nat) =
  match v with
  | JObject fields ->
    (match json_get_field "@graph" v with
     | Some g ->
       let (subj_opt, ctr1) =
         (match json_get_field "@id" v with
          | Some (JString id_str) -> (jld_id_to_subject id_str, ctr)
          | Some _ -> (None, ctr)
          | None ->
            let (b, ctr') = jld_fresh_bnode ctr in
            (Some (S_BNode b), ctr')) in
       (match subj_opt with
        | None -> (dflt, named, ctr1)
        | Some gsubj ->
          let (gtris, named1, ctr2) = jld_expand_graph_nodes rdir (jld_as_array g) ctr1 [] named fuel in
          // Non-keyword members of the container node describe the
          // graph-name resource in the DEFAULT graph.
          let (dflt1, named2, ctr3) = jld_expand_fields rdir gsubj fields ctr2 dflt named1 fuel in
          let ng = { ng_name = jld_graph_name_of_subject gsubj; ng_graph = gtris } in
          (dflt1, ng :: named2, ctr3))
     | None ->
       let (_, dflt1, named1, ctr1) = jld_expand_node rdir v ctr dflt named fuel in
       (dflt1, named1, ctr1))
  | _ -> (dflt, named, ctr)

let rec jld_expand_tops (rdir:rdf_direction_mode) (vs:list json_val) (dflt:list triple) (named:list named_graph)
                        (ctr:nat) (fuel:nat)
  : Tot (list triple & list named_graph & nat) (decreases fuel) =
  if fuel = 0 then (dflt, named, ctr)
  else
    match vs with
    | [] -> (dflt, named, ctr)
    | v :: rest ->
      let (d1, n1, c1) = jld_expand_top rdir v dflt named ctr fuel in
      jld_expand_tops rdir rest d1 n1 c1 (fuel - 1)

// Is @graph the only key of an object? (Then it is the document wrapper
// and its contents belong to the default graph.)
let rec jld_only_graph_keys (fields:list (string & json_val)) : Tot bool (decreases fields) =
  match fields with
  | [] -> true
  | (k, _) :: rest -> k = "@graph" && jld_only_graph_keys rest

// ================================================================
// Public API
// ================================================================

// Deserialize an already-parsed expanded-form JSON-LD value tree.
// None when the top level is not an array or object.
let jld_dataset_of_json (rdir:rdf_direction_mode) (root:json_val) : option rdf_dataset =
  let fuel = json_size root + 1 in
  match root with
  | JArray tops ->
    let (d, n, _) = jld_expand_tops rdir tops [] [] 0 fuel in
    Some (dataset_finalise { ds_default = d; ds_named = List.Tot.rev n })
  | JObject fields ->
    let tops =
      if jld_only_graph_keys fields then
        (match json_get_field "@graph" root with
         | Some g -> jld_as_array g
         | None -> [root])
      else [root] in
    let (d, n, _) = jld_expand_tops rdir tops [] [] 0 fuel in
    Some (dataset_finalise { ds_default = d; ds_named = List.Tot.rev n })
  | _ -> None

// True when a top-level JSON object document carries an inline @context
// member. A top-level JArray never carries a shared @context (JSON-LD
// @context only applies within an object) and keeps going straight down
// the expanded-form Phase 1 path.
let jld_has_inline_context (root:json_val) : bool =
  match root with
  | JObject fields -> List.Tot.existsb (fun (kv:(string & json_val)) -> fst kv = "@context") fields
  | _ -> false

// The rdfDirection option's raw string value (manifest's `option.
// rdfDirection`, e.g. "i18n-datatype" / "compound-literal") to the
// internal mode enum. `None` (the option absent) and any unrecognized
// string both mean RDM_Drop — the JSON-LD 1.1 API default when no
// explicit rdfDirection is given.
let rdf_direction_mode_of_option (rdf_direction:option string) : rdf_direction_mode =
  match rdf_direction with
  | Some "i18n-datatype" -> RDM_I18nDatatype
  | Some "compound-literal" -> RDM_CompoundLiteral
  | _ -> RDM_Drop

// Parse a JSON-LD document into an RDF dataset. `base`: the document's
// own base IRI (PHASE 6, issue #275 — the manifest's `option.base`, or a
// consumer's own notion of "the IRI this document was loaded from";
// `None` when the consumer has none to offer, e.g. a CLI reading a bare
// file with no associated URL). `rdf_direction`: the manifest's
// `option.rdfDirection` raw string, converted via
// rdf_direction_mode_of_option — see rdf_direction_mode's doc comment
// for what each mode does. `expand_context`: the manifest's
// `option.expandContext` (toRdf/e077) — an ALREADY-ABSOLUTE IRI naming a
// context document to apply BEFORE the document's own inline @context
// (the consumer resolves any manifest-relative path the same way it
// resolves `base` — see bin/jsonld-runner/jsonld_runner.ml's
// jld_rdf_direction-adjacent option threading). Realised by treating it
// EXACTLY like an ordinary remote "@context" string reference
// (JSONLD.Context.context_process's JString branch already does
// "fetch document, extract its top-level @context member, process it" —
// the whole mechanism issue #275 built for remote contexts / "@import").
// A document whose top level is a JObject carrying an inline @context,
// OR for which `base` or `expand_context` is `Some _`, is run through
// JSONLD.Expand first (PHASE 3a: JSONLD.Context + JSONLD.Expand — see
// module banner), seeding the initial active context's `ac_base` from
// `base` and, when `expand_context` is given, pre-applying that context;
// a document with NONE of the three takes the unchanged Phase 1 path
// straight into jld_dataset_of_json, which requires EXPANDED FORM
// input. None when the input is not valid RFC 8259 JSON, expansion (or
// the expandContext pre-application) hits an out-of-scope feature
// (module banner), or the top level is not an array/object.
//
// `processing_mode` (PHASE 8): the manifest's `option.processingMode`
// raw string ("json-ld-1.0" / "json-ld-1.1" / absent). `Some
// "json-ld-1.0"` seeds the active context's `ac_mode10 = true` (see
// JSONLD.Context.active_context's ac_mode10 doc comment) so
// JSONLD.Context's context-processing checks reject 1.1-only
// constructs (@propagate, @import, @protected, @index, scoped
// @context, @type: @none/@json, @graph/@id/@type/array-shaped
// @container, and redefining the @type keyword) exactly as the JSON-LD
// 1.1 API Create Term Definition / Context Processing algorithms
// require — toRdf/c029, ep02, tn01, er21. Any other value (including
// None, the default) behaves as JSON-LD 1.1 (ac_mode10 = false),
// unchanged from before this parameter existed.
let parse_jsonld (input:string) (base:option string) (rdf_direction:option string)
                  (expand_context:option string) (processing_mode:option string) : option rdf_dataset =
  let rdir = rdf_direction_mode_of_option rdf_direction in
  let mode10 = (match processing_mode with Some "json-ld-1.0" -> true | _ -> false) in
  match parse_json input with
  | None -> None
  | Some root ->
    if jld_has_inline_context root || Some? base || Some? expand_context then
      let ac_seed = { empty_active_context with ac_base = base; ac_mode10 = mode10 } in
      let ac0_opt =
        (match expand_context with
         | None -> Some ac_seed
         | Some ctxref -> context_process ac_seed (JString ctxref) false jld_remote_context_fuel []) in
      (match ac0_opt with
       | None -> None
       | Some ac0 ->
         (match expand ac0 root with
          | None -> None
          | Some expanded -> jld_dataset_of_json rdir expanded))
    else jld_dataset_of_json rdir root
