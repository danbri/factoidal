module JSONSchema.Validate

// ============================================================================
// JSON Schema draft-07 validator.
//
// Both the schema and the instance are ordinary JSON values, so this module
// consumes Parser.JSON.json_val trees produced by the verified RFC 8259
// parser (Parser.JSON.parse_json) rather than defining any JSON syntax of its
// own (iron rule #1 / #4). A JSON Schema is itself a json_val: either a
// boolean schema (JBool) or an object of keywords (JObject) that we interpret.
//
// SCOPE (draft-07 core keywords):
//   type (all 7 incl. integer-vs-number), enum, const,
//   properties, required, additionalProperties (bool + schema),
//   patternProperties, propertyNames, minProperties, maxProperties,
//   dependencies,
//   items (single schema + tuple form), additionalItems, contains,
//   minItems, maxItems, uniqueItems,
//   minimum, maximum, exclusiveMinimum, exclusiveMaximum, multipleOf,
//   minLength, maxLength,
//   pattern (ECMA-262-flavor, matched with the VERIFIED regex engine,
//     Regex.XSDPattern.parse + Regex.Exec search/matches_norm),
//   allOf, anyOf, oneOf, not, if/then/else,
//   boolean schemas (true/false),
//   $ref with full draft-07 base-URI resolution: local JSON pointers
//     ("#", "#/definitions/x", "#/items/0"), $id-relative and absolute
//     URI refs, "#anchor" plain-name fragments ($id:"#foo"), and cross-
//     document refs into caller-supplied external documents (the runner
//     hands the vendored draft-07 meta-schema in via validate_ext).
//
// pattern / patternProperties: JSON-Schema patterns are ECMA-262 regexes
// matched UNANCHORED (substring). The XSD-flavor parser treats ^ / $ as
// XSD whole-string no-ops, so ECMA anchoring is reconstructed HERE at the
// string layer (ecma_match): a leading ^ / trailing $ selects prefix /
// suffix / whole-string matching, their absence selects Regex.Exec.search
// (the engine's .*r.* substring reduction). A pattern OUTSIDE the XSD-
// parseable subset (parse_xsd_pattern = None) short-circuits the whole
// subschema to VUnsupported — an honest skip with the pattern intact,
// NEVER a wrong verdict.
//
// NOT COVERED (VUnsupported = skip, never a wrong verdict): format (kept
// as a skip; draft-07 treats format as an annotation and no vendored test
// exercises it as an assertion), any $ref whose target is neither in the
// document nor in a supplied external, and mid-pattern ^ / $ anchors.
// Annotation keywords (title, description, $comment, $schema, definitions,
// default, examples) are ignored per the "unknown keywords are
// annotations" rule.
//
// TERMINATION: validate_schema and its list helpers are fuel-bounded
// (decreases fuel). Every recursive descent — nested subschema application,
// list traversal, AND $ref following — passes fuel-1, so a $ref cycle that
// does not shrink the instance terminates by exhausting fuel and yielding
// VUnsupported (a skip, not a wrong verdict). The top-level entry seeds fuel
// from the JSON sizes, far above the work any real draft-07 test needs.
// ============================================================================

open FStar.Mul
open FStar.String
open Parser.JSON

module L = FStar.List.Tot
module RS = Regex.Syntax
module RX = Regex.XSDPattern
module RE = Regex.Exec

// ================================================================
// Three-valued result: pass, fail, or "outside slice-1 support".
// ================================================================

type vresult =
  | VPass        : vresult
  | VFail        : vresult
  | VUnsupported : vresult

// Conjunction: any definite failure dominates; otherwise any unsupported
// keyword makes the whole verdict undetermined; otherwise pass.
let vand (a b:vresult) : vresult =
  match a, b with
  | VFail, _ | _, VFail -> VFail
  | VUnsupported, _ | _, VUnsupported -> VUnsupported
  | _ -> VPass

// Disjunction (anyOf): any definite pass dominates; otherwise undetermined
// if any branch was unsupported; otherwise fail.
let vor (a b:vresult) : vresult =
  match a, b with
  | VPass, _ | _, VPass -> VPass
  | VUnsupported, _ | _, VUnsupported -> VUnsupported
  | _ -> VFail

// ================================================================
// Numbers as exact rationals parsed from the JNumber lexeme.
//
// A JNumber carries the verbatim RFC 8259 lexeme (already validated by
// Parser.JSON). We reduce it to (num, den) with den a positive power of ten,
// giving exact decimal arithmetic — no floating point. F* int is the
// mathematical integer (extracts to zarith), so numerator/denominator stay
// exact for comparisons and multipleOf.
// ================================================================

let code (c:char) : int = FStar.Char.int_of_char c

let is_dig (c:char) : bool = let n = code c in n >= 48 && n <= 57

// Digit value clamped into [0,9] so magnitudes stay nat.
let dv (c:char) : nat = let n = code c - 48 in if n >= 0 && n <= 9 then n else 0

let rec nat_of_digits (cs:list char) (acc:nat) : Tot nat (decreases cs) =
  match cs with
  | [] -> acc
  | c :: r -> nat_of_digits r (acc * 10 + dv c)

let rec pow10 (n:nat) : Tot pos (decreases n) =
  if n = 0 then 1 else 10 * pow10 (n - 1)

// Split a leading run of ASCII digits: (digit-chars, remainder).
let rec take_digits (cs:list char) : Tot (list char & list char) (decreases cs) =
  match cs with
  | c :: r -> if is_dig c then (let (ds, rest) = take_digits r in (c :: ds, rest)) else ([], cs)
  | [] -> ([], [])

// Parse a JSON number lexeme into an exact rational (num, den). den is a
// positive power of ten. Returns None only for a lexeme with no digits.
let parse_num_rational (s:string) : option (int & pos) =
  let cs0 = list_of_string s in
  let (neg, cs1) =
    (match cs0 with
     | c :: r -> if c = '-' then (true, r) else (false, cs0)
     | [] -> (false, cs0)) in
  let (ipart, cs2) = take_digits cs1 in
  let (fpart, cs3) =
    (match cs2 with
     | c :: r -> if c = '.' then take_digits r else ([], cs2)
     | [] -> ([], cs2)) in
  let k = L.length fpart in
  let exp_i =
    (match cs3 with
     | c :: r ->
       if c = 'e' || c = 'E' then
         (let (esign, r1) =
            (match r with
             | d :: rr -> if d = '+' then (1, rr) else if d = '-' then (-1, rr) else (1, r)
             | [] -> (1, r)) in
          let (ed, _) = take_digits r1 in
          esign * (nat_of_digits ed 0))
       else 0
     | [] -> 0) in
  if L.length ipart = 0 && k = 0 then None
  else
    let mag = nat_of_digits (L.append ipart fpart) 0 in
    let mant = if neg then - mag else mag in
    let eff = exp_i - k in
    if eff >= 0 then (let e:nat = eff in Some (mant * pow10 e, 1))
    else (let e:nat = - eff in Some (mant, pow10 e))

let rat_lt (a b:(int & pos)) : bool = (fst a) * (snd b) < (fst b) * (snd a)
let rat_le (a b:(int & pos)) : bool = (fst a) * (snd b) <= (fst b) * (snd a)

// Is the rational value an integer? den > 0, so integral iff den divides num.
let is_int_val (r:(int & pos)) : bool =
  let n = fst r in let d = snd r in n - (n / d) * d = 0

// Is v an integer multiple of divisor d? v = vn/vd, d = dn/dd; v/d integral
// iff (vd*dn) divides (vn*dd).
let is_multiple (v d:(int & pos)) : bool =
  let a = (fst v) * (snd d) in
  let b = (snd v) * (fst d) in
  if b = 0 then false else a - (a / b) * b = 0

// Floor of a rational (used only for non-negative integer count bounds).
let rat_floor (r:(int & pos)) : int = (fst r) / (snd r)

let num_eq (a b:string) : bool =
  match parse_num_rational a, parse_num_rational b with
  | Some (n1, d1), Some (n2, d2) -> n1 * d2 = n2 * d1
  | _, _ -> a = b

let inst_rat (v:json_val) : option (int & pos) =
  match v with
  | JNumber s -> parse_num_rational s
  | _ -> None

// ================================================================
// Semantic JSON equality (enum / const / uniqueItems).
//
// Numbers compare by rational value (so 1 = 1.0), objects compare as
// unordered key->value maps, arrays elementwise in order. Fuel-bounded so
// the mutual recursion terminates without a structural-measure argument; the
// wrapper seeds fuel from json_size, above the tree depth.
// ================================================================

let rec json_equal (a b:json_val) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    (match a, b with
     | JNull, JNull -> true
     | JBool x, JBool y -> x = y
     | JString x, JString y -> x = y
     | JNumber x, JNumber y -> num_eq x y
     | JArray xs, JArray ys -> jeq_list xs ys (fuel - 1)
     | JObject xs, JObject ys -> L.length xs = L.length ys && jeq_obj xs ys (fuel - 1)
     | _, _ -> false)

and jeq_list (xs ys:list json_val) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    (match xs, ys with
     | [], [] -> true
     | x :: xr, y :: yr -> json_equal x y (fuel - 1) && jeq_list xr yr (fuel - 1)
     | _, _ -> false)

and jeq_obj (xs ys:list (string & json_val)) (fuel:nat) : Tot bool (decreases fuel) =
  if fuel = 0 then false
  else
    (match xs with
     | [] -> true
     | (k, v) :: xr ->
       (match L.find (fun (kk, _) -> kk = k) ys with
        | Some (_, v') -> json_equal v v' (fuel - 1) && jeq_obj xr ys (fuel - 1)
        | None -> false))

let jeq (a b:json_val) : bool = json_equal a b (json_size a + json_size b + 2)

let rec all_unique (xs:list json_val) : Tot bool (decreases xs) =
  match xs with
  | [] -> true
  | h :: t -> (not (L.existsb (fun x -> jeq h x) t)) && all_unique t

// enum membership: does the instance semantically equal one listed value?
let rec enum_member (inst:json_val) (vs:list json_val) : Tot bool (decreases vs) =
  match vs with
  | [] -> false
  | e :: tl -> jeq inst e || enum_member inst tl

// ================================================================
// JSON Pointer resolution for local $ref ("#", "#/a/b", "#/items/0").
// ================================================================

let rec unescape_ptr (cs:list char) : Tot (list char) (decreases cs) =
  match cs with
  | '~' :: '1' :: r -> '/' :: unescape_ptr r
  | '~' :: '0' :: r -> '~' :: unescape_ptr r
  | c :: r -> c :: unescape_ptr r
  | [] -> []

let unescape_token (t:string) : string = string_of_list (unescape_ptr (list_of_string t))

let parse_index (t:string) : option nat =
  let cs = list_of_string t in
  match cs with
  | [] -> None
  | _ -> if L.for_all is_dig cs then Some (nat_of_digits cs 0) else None

let rec resolve_pointer (doc:json_val) (toks:list string) : Tot (option json_val) (decreases toks) =
  match toks with
  | [] -> Some doc
  | t :: rest ->
    let key = unescape_token t in
    (match doc with
     | JObject fs ->
       (match L.find (fun (k, _) -> k = key) fs with
        | Some (_, v) -> resolve_pointer v rest
        | None -> None)
     | JArray xs ->
       (match parse_index key with
        | Some i -> (match L.nth xs i with Some v -> resolve_pointer v rest | None -> None)
        | None -> None)
     | _ -> None)

// ================================================================
// Percent-decoding (RFC 3986). A URI fragment carrying a JSON pointer is
// percent-decoded to yield the pointer string, THEN split on '/'. So
// "#/definitions/percent%25field" resolves to key "percent%field". Only
// single-byte (ASCII / Latin-1) escapes are decoded; multibyte %C3%A1
// sequences are left verbatim (not exercised by the draft-07 pointer
// fixtures).
// ================================================================

let hexv (c:char) : option (d:nat{d < 16}) =
  let n = code c in
  if n >= 48 && n <= 57 then Some (n - 48)          // 0-9
  else if n >= 97 && n <= 102 then Some (n - 87)    // a-f
  else if n >= 65 && n <= 70 then Some (n - 55)     // A-F
  else None

let rec pct_decode (cs:list char) : Tot (list char) (decreases cs) =
  match cs with
  | '%' :: h1 :: h2 :: r ->
    (match hexv h1, hexv h2 with
     | Some a, Some b -> let v = a * 16 + b in FStar.Char.char_of_int v :: pct_decode r
     | _, _ -> '%' :: pct_decode (h1 :: h2 :: r))
  | c :: r -> c :: pct_decode r
  | [] -> []

// Tokens of a JSON-pointer fragment (the text after '#'): percent-decode the
// whole fragment, split on '/', drop the leading empty token, JSON-pointer-
// unescape (~1 -> '/', ~0 -> '~') each token.
let frag_tokens (f:string) : list string =
  let decoded = string_of_list (pct_decode (list_of_string f)) in
  match FStar.String.split ['/'] decoded with
  | _ :: toks -> L.map unescape_token toks
  | [] -> []

// ================================================================
// URI reference resolution (RFC 3986, the subset the draft-07 $ref fixtures
// exercise: absolute refs, fragment-only refs, absolute-path refs, and
// relative-path refs merged against the base's directory). No dot-segment
// removal is needed — no fixture uses "./" or "../".
// ================================================================

let rec split_at_hash (cs:list char) (acc:list char) : Tot (list char & option (list char)) (decreases cs) =
  match cs with
  | [] -> (L.rev acc, None)
  | '#' :: r -> (L.rev acc, Some r)
  | c :: r -> split_at_hash r (c :: acc)

// (base-without-fragment, optional-fragment-text)
let split_fragment (s:string) : (string & option string) =
  match split_at_hash (list_of_string s) [] with
  | (before, Some after) -> (string_of_list before, Some (string_of_list after))
  | (before, None) -> (string_of_list before, None)

let base_of (s:string) : string = fst (split_fragment s)

let is_alpha (c:char) : bool = let n = code c in (n >= 65 && n <= 90) || (n >= 97 && n <= 122)

// A scheme delimiter ':' appears before any '/', '?' or '#'.
let rec scheme_colon (cs:list char) : Tot bool (decreases cs) =
  match cs with
  | [] -> false
  | ':' :: _ -> true
  | c :: r -> if c = '/' || c = '?' || c = '#' then false else scheme_colon r

let is_absolute_ref (s:string) : bool =
  match list_of_string s with
  | c :: _ -> is_alpha c && scheme_colon (list_of_string s)
  | [] -> false

let rec take_to_slash (cs:list char) : Tot (list char) (decreases cs) =
  match cs with [] -> [] | '/' :: _ -> [] | c :: r -> c :: take_to_slash r

let rec take_to_colon (cs:list char) : Tot (list char) (decreases cs) =
  match cs with [] -> [] | ':' :: _ -> [] | c :: r -> c :: take_to_colon r

// Split "scheme://rest" -> (scheme, rest). None if there is no "://".
let rec split_scheme_sep (cs:list char) (acc:list char) : Tot (option (list char & list char)) (decreases cs) =
  match cs with
  | ':' :: '/' :: '/' :: r -> Some (L.rev acc, r)
  | c :: r -> split_scheme_sep r (c :: acc)
  | [] -> None

// "scheme://authority" for an absolute-path ("/x") merge.
let scheme_authority (base:string) : string =
  match split_scheme_sep (list_of_string (base_of base)) [] with
  | Some (sch, rest) -> string_of_list sch ^ "://" ^ string_of_list (take_to_slash rest)
  | None -> base_of base

let scheme_prefix (base:string) : string = string_of_list (take_to_colon (list_of_string (base_of base)))

// Base directory: everything up to and including the last '/'.
let rec dir_prefix (cs:list char) : Tot (list char) (decreases cs) =
  match cs with
  | [] -> []
  | c :: r -> if L.mem '/' r then c :: dir_prefix r else if c = '/' then ['/'] else []

let base_dir (base:string) : string = string_of_list (dir_prefix (list_of_string (base_of base)))

// Resolve reference `r` against absolute base URI `base`.
let resolve_uri (base r:string) : string =
  if r = "" then base_of base
  else if is_absolute_ref r then r
  else
    (match list_of_string r with
     | '#' :: _ -> base_of base ^ r
     | '/' :: '/' :: _ -> scheme_prefix base ^ ":" ^ r
     | '/' :: _ -> scheme_authority base ^ r
     | _ -> base_dir base ^ r)

// Effective base after applying an $id (fragment stripped; a pure "#anchor"
// $id leaves the base unchanged).
let id_base (base idval:string) : string = base_of (resolve_uri base idval)

// ================================================================
// $id / $anchor registry and $ref resolution.
// idreg  : absolute-URI (fragment-stripped) -> schema node (documents / $id).
// anchreg: absolute-anchor-URI ("base#name") -> schema node ($id:"#name").
// The registry is built once from the root document + supplied externals and
// threaded UNCHANGED through validation; only the base URI varies.
// ================================================================

type refctx = { idreg : list (string & json_val); anchreg : list (string & json_val) }

let rec lookup_reg (k:string) (l:list (string & json_val)) : Tot (option json_val) (decreases l) =
  match l with
  | [] -> None
  | (kk, v) :: tl -> if kk = k then Some v else lookup_reg k tl

let frag_is_pointer (f:string) : bool =
  match list_of_string f with c :: _ -> c = '/' | [] -> false

// Resolve a $ref to (target-node, base-URI-for-that-node), or None if the
// target is neither in the document nor in a supplied external.
let resolve_ref (ctx:refctx) (base r:string) : option (json_val & string) =
  let target = resolve_uri base r in
  match split_fragment target with
  | (tbase, None) ->
    (match lookup_reg tbase ctx.idreg with Some n -> Some (n, tbase) | None -> None)
  | (tbase, Some f) ->
    if f = "" then
      (match lookup_reg tbase ctx.idreg with Some n -> Some (n, tbase) | None -> None)
    else if frag_is_pointer f then
      (match lookup_reg tbase ctx.idreg with
       | Some doc -> (match resolve_pointer doc (frag_tokens f) with Some n -> Some (n, tbase) | None -> None)
       | None -> None)
    else
      (match lookup_reg target ctx.anchreg with Some n -> Some (n, tbase) | None -> None)

// Walk the document collecting $id (base-setting) and $anchor ($id:"#name")
// entries. Descends generically into every object field value and array
// element; fuel-bounded like the validator.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec collect_ids (base:string) (node:json_val) (fuel:nat)
  : Tot (list (string & json_val) & list (string & json_val)) (decreases fuel) =
  if fuel = 0 then ([], [])
  else
    (match node with
     | JObject fs ->
       let (nbase, sids, sanch) =
         (match json_get_field "$id" node with
          | Some (JString v) ->
            let resolved = resolve_uri base v in
            (match split_fragment resolved with
             | (rb, Some a) ->
               if rb = base && a <> "" then (base, [], [(resolved, node)])   // pure "#anchor"
               else (rb, [(rb, node)], (if a = "" then [] else [(resolved, node)]))
             | (rb, None) -> (rb, [(rb, node)], []))
          | _ -> (base, [], [])) in
       let (cids, canch) = collect_ids_fields nbase fs (fuel - 1) in
       (L.append sids cids, L.append sanch canch)
     | JArray xs -> collect_ids_list base xs (fuel - 1)
     | _ -> ([], []))
and collect_ids_fields (base:string) (fs:list (string & json_val)) (fuel:nat)
  : Tot (list (string & json_val) & list (string & json_val)) (decreases fuel) =
  if fuel = 0 then ([], [])
  else (match fs with
        | [] -> ([], [])
        | (_, v) :: tl ->
          let (a1, b1) = collect_ids base v (fuel - 1) in
          let (a2, b2) = collect_ids_fields base tl (fuel - 1) in
          (L.append a1 a2, L.append b1 b2))
and collect_ids_list (base:string) (xs:list json_val) (fuel:nat)
  : Tot (list (string & json_val) & list (string & json_val)) (decreases fuel) =
  if fuel = 0 then ([], [])
  else (match xs with
        | [] -> ([], [])
        | v :: tl ->
          let (a1, b1) = collect_ids base v (fuel - 1) in
          let (a2, b2) = collect_ids_list base tl (fuel - 1) in
          (L.append a1 a2, L.append b1 b2))
#pop-options

// ================================================================
// pattern / patternProperties: ECMA-262-flavor matching over the VERIFIED
// regex engine. See the module header for the anchoring reconstruction.
// ================================================================

// True iff the last char is '$' and it is not backslash-escaped.
let last_dollar (cs:list char) : bool =
  match L.rev cs with
  | '$' :: '\\' :: _ -> false
  | '$' :: _ -> true
  | _ -> false

// ECMA-262 unanchored match of pattern `pat` against string `s`.
// None = pattern outside the XSD-parseable subset (honest skip).
let ecma_match (pat s:string) : option bool =
  let pchars = list_of_string pat in
  let starts = (match pchars with c :: _ -> c = '^' | [] -> false) in
  let ends = last_dollar pchars in
  (match RX.parse_xsd_pattern pat with
   | None -> None
   | Some r ->
     let scs = RX.cps_of_string s in
     let re : RS.regex =
       (if starts && ends then r
        else if starts then RS.R_Cat r RE.dot_star
        else if ends then RS.R_Cat RE.dot_star r
        else RE.contains r) in
     Some (RE.matches_norm re scs))

// Does key `k` match any of the given ECMA patterns?
let rec key_matches_any (k:string) (pats:list string) : Tot bool (decreases pats) =
  match pats with
  | [] -> false
  | p :: tl -> (match ecma_match p k with Some true -> true | _ -> key_matches_any k tl)

// A `pattern` / `patternProperties` value the regex engine cannot parse:
// forces the whole subschema to VUnsupported so we never emit a wrong verdict.
let pattern_bad (schema:json_val) : bool =
  match json_get_field "pattern" schema with
  | Some (JString p) -> None? (RX.parse_xsd_pattern p)
  | Some _ -> true
  | None -> false

let rec any_pat_unparseable (pps:list (string & json_val)) : Tot bool (decreases pps) =
  match pps with
  | [] -> false
  | (r, _) :: tl -> None? (RX.parse_xsd_pattern r) || any_pat_unparseable tl

let patprops_bad (schema:json_val) : bool =
  match json_get_field "patternProperties" schema with
  | Some (JObject pps) -> any_pat_unparseable pps
  | Some _ -> true
  | None -> false

// ================================================================
// Instance / type matching and small helpers.
// ================================================================

let inst_matches_type (v:json_val) (t:string) : bool =
  match t with
  | "null" -> JNull? v
  | "boolean" -> JBool? v
  | "string" -> JString? v
  | "object" -> JObject? v
  | "array" -> JArray? v
  | "number" -> JNumber? v
  | "integer" ->
    (match v with
     | JNumber s -> (match parse_num_rational s with Some r -> is_int_val r | None -> false)
     | _ -> false)
  | _ -> false

let type_ok (v:json_val) (tv:json_val) : bool =
  match tv with JString t -> inst_matches_type v t | _ -> false

let lookup (k:string) (l:list (string & json_val)) : option json_val =
  match L.find (fun (kk, _) -> kk = k) l with
  | Some (_, v) -> Some v
  | None -> None

let has_key (k:string) (l:list (string & json_val)) : bool = Some? (lookup k l)

let rec drop_n (#a:Type) (n:nat) (l:list a) : Tot (list a) (decreases n) =
  if n = 0 then l
  else (match l with [] -> [] | _ :: t -> drop_n (n - 1) t)

let rec zip_pairs (#a #b:Type) (xs:list a) (ys:list b) : Tot (list (a & b)) (decreases xs) =
  match xs, ys with
  | x :: xr, y :: yr -> (x, y) :: zip_pairs xr yr
  | _, _ -> []

// required / array-dependency check: are all listed name strings present?
let names_present (fs:list (string & json_val)) (names:list json_val) : bool =
  L.for_all (fun nv -> match nv with JString n -> has_key n fs | _ -> false) names

// ================================================================
// Non-recursive keyword checks (no subschema application). Split out of
// validate_schema so its verification condition stays small enough for z3;
// all the numeric / length / uniqueness assertions are discharged here in a
// leaf function verified once.
// ================================================================

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let check_local (schema inst:json_val) : vresult =
  let get (k:string) : option json_val = json_get_field k schema in
  let c_type =
    (match get "type" with
     | None -> VPass
     | Some (JString t) -> if inst_matches_type inst t then VPass else VFail
     | Some (JArray ts) -> if L.existsb (type_ok inst) ts then VPass else VFail
     | Some _ -> VUnsupported) in
  let c_enum =
    (match get "enum" with
     | Some (JArray vs) -> if enum_member inst vs then VPass else VFail
     | _ -> VPass) in
  let c_const =
    (match get "const" with Some cv -> if jeq inst cv then VPass else VFail | None -> VPass) in
  let c_required =
    (match get "required", inst with
     | Some (JArray names), JObject fs -> if names_present fs names then VPass else VFail
     | _, _ -> VPass) in
  let c_minprops =
    (match get "minProperties", inst with
     | Some (JNumber s), JObject fs ->
       (match parse_num_rational s with Some r -> if L.length fs >= rat_floor r then VPass else VFail | None -> VPass)
     | _, _ -> VPass) in
  let c_maxprops =
    (match get "maxProperties", inst with
     | Some (JNumber s), JObject fs ->
       (match parse_num_rational s with Some r -> if L.length fs <= rat_floor r then VPass else VFail | None -> VPass)
     | _, _ -> VPass) in
  let c_minitems =
    (match get "minItems", inst with
     | Some (JNumber s), JArray xs ->
       (match parse_num_rational s with Some r -> if L.length xs >= rat_floor r then VPass else VFail | None -> VPass)
     | _, _ -> VPass) in
  let c_maxitems =
    (match get "maxItems", inst with
     | Some (JNumber s), JArray xs ->
       (match parse_num_rational s with Some r -> if L.length xs <= rat_floor r then VPass else VFail | None -> VPass)
     | _, _ -> VPass) in
  let c_uniq =
    (match get "uniqueItems", inst with
     | Some (JBool true), JArray xs -> if all_unique xs then VPass else VFail
     | _, _ -> VPass) in
  let c_min =
    (match get "minimum" with
     | Some (JNumber ms) ->
       (match inst_rat inst, parse_num_rational ms with Some iv, Some mv -> if rat_le mv iv then VPass else VFail | _, _ -> VPass)
     | _ -> VPass) in
  let c_max =
    (match get "maximum" with
     | Some (JNumber xs) ->
       (match inst_rat inst, parse_num_rational xs with Some iv, Some xv -> if rat_le iv xv then VPass else VFail | _, _ -> VPass)
     | _ -> VPass) in
  let c_exmin =
    (match get "exclusiveMinimum" with
     | Some (JNumber ms) ->
       (match inst_rat inst, parse_num_rational ms with Some iv, Some mv -> if rat_lt mv iv then VPass else VFail | _, _ -> VPass)
     | _ -> VPass) in
  let c_exmax =
    (match get "exclusiveMaximum" with
     | Some (JNumber xs) ->
       (match inst_rat inst, parse_num_rational xs with Some iv, Some xv -> if rat_lt iv xv then VPass else VFail | _, _ -> VPass)
     | _ -> VPass) in
  let c_mult =
    (match get "multipleOf" with
     | Some (JNumber ds) ->
       (match inst_rat inst, parse_num_rational ds with Some iv, Some dvr -> if is_multiple iv dvr then VPass else VFail | _, _ -> VPass)
     | _ -> VPass) in
  let c_minlen =
    (match get "minLength", inst with
     | Some (JNumber s), JString str ->
       (match parse_num_rational s with Some r -> if L.length (list_of_string str) >= rat_floor r then VPass else VFail | None -> VPass)
     | _, _ -> VPass) in
  let c_maxlen =
    (match get "maxLength", inst with
     | Some (JNumber s), JString str ->
       (match parse_num_rational s with Some r -> if L.length (list_of_string str) <= rat_floor r then VPass else VFail | None -> VPass)
     | _, _ -> VPass) in
  L.fold_left vand VPass
    [ c_type; c_enum; c_const; c_required; c_minprops; c_maxprops; c_minitems;
      c_maxitems; c_uniq; c_min; c_max; c_exmin; c_exmax; c_mult; c_minlen; c_maxlen ]
#pop-options

// ================================================================
// The validator. validate_schema plus a set of list helpers, all
// fuel-bounded. The list helpers make every recursive call to
// validate_schema a DIRECT call (no recursion buried inside a closure
// passed to a higher-order combinator), which is what F* needs to see the
// decreasing measure. The returned vresult lists are folded with the pure
// vand/vor combinators; the non-recursive keywords are delegated to
// check_local.
// ================================================================

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec validate_schema (ctx:refctx) (base:string) (schema inst:json_val) (fuel:nat)
  : Tot vresult (decreases fuel) =
  if fuel = 0 then VUnsupported
  else
    let f1 = fuel - 1 in
    match schema with
    | JBool true -> VPass
    | JBool false -> VFail
    | JObject _ ->
      // $ref, when present, is applied alone; draft-07 ignores siblings
      // (including a sibling $id, so we resolve against the inherited base).
      (match json_get_field "$ref" schema with
       | Some (JString r) ->
         (match resolve_ref ctx base r with
          | None -> VUnsupported
          | Some (sub, nbase) -> validate_schema ctx nbase sub inst f1)
       | Some _ -> VUnsupported
       | None ->
         let get (k:string) : option json_val = json_get_field k schema in
         // $id (when not overridden by $ref) sets the base for descendants.
         let base : string = (match get "$id" with Some (JString i) -> id_base base i | _ -> base) in
         // format stays a skip; an unparseable pattern / patternProperties
         // short-circuits the whole subschema to a skip (never a wrong verdict).
         if Some? (get "format") || pattern_bad schema || patprops_bad schema
         then VUnsupported
         else begin
           let c_local = check_local schema inst in

           let c_pattern =
             (match get "pattern", inst with
              | Some (JString p), JString s ->
                (match ecma_match p s with Some true -> VPass | Some false -> VFail | None -> VUnsupported)
              | _, _ -> VPass) in

           let c_props =
             (match get "properties", inst with
              | Some (JObject ps), JObject fs -> L.fold_left vand VPass (results_props ctx base ps fs f1)
              | _, _ -> VPass) in

           let c_patprops =
             (match get "patternProperties", inst with
              | Some (JObject pps), JObject fs ->
                L.fold_left vand VPass (results_patprops ctx base pps fs f1)
              | _, _ -> VPass) in

           let c_addprops =
             (match get "additionalProperties", inst with
              | Some ap, JObject fs ->
                let declared = (match get "properties" with Some (JObject ps) -> L.map fst ps | _ -> []) in
                let pats = (match get "patternProperties" with Some (JObject pps) -> L.map fst pps | _ -> []) in
                // "additional" = neither a declared property nor a patternProperties match.
                let extra = L.filter (fun (k, _) -> not (L.mem k declared) && not (key_matches_any k pats)) fs in
                (match ap with
                 | JBool true -> VPass
                 | JBool false -> (match extra with [] -> VPass | _ -> VFail)
                 | _ -> L.fold_left vand VPass (results_over_instances ctx base ap (L.map snd extra) f1))
              | _, _ -> VPass) in

           let c_propnames =
             (match get "propertyNames", inst with
              | Some pn, JObject fs ->
                L.fold_left vand VPass
                  (results_over_instances ctx base pn (L.map (fun (k, _) -> JString k) fs) f1)
              | _, _ -> VPass) in

           let c_deps =
             (match get "dependencies", inst with
              | Some (JObject deps), JObject fs ->
                L.fold_left vand VPass (results_deps ctx base deps fs inst f1)
              | _, _ -> VPass) in

           let c_items =
             (match get "items", inst with
              | Some (JArray subs), JArray xs ->
                L.fold_left vand VPass (results_pairs ctx base (zip_pairs subs xs) f1)
              | Some sub, JArray xs ->
                if JObject? sub || JBool? sub
                then L.fold_left vand VPass (results_over_instances ctx base sub xs f1)
                else VPass
              | _, _ -> VPass) in

           let c_additems =
             (match get "additionalItems", get "items", inst with
              | Some ai, Some (JArray subs), JArray xs ->
                let extra = drop_n (L.length subs) xs in
                (match ai with
                 | JBool true -> VPass
                 | JBool false -> (match extra with [] -> VPass | _ -> VFail)
                 | _ -> L.fold_left vand VPass (results_over_instances ctx base ai extra f1))
              | _, _, _ -> VPass) in

           let c_contains =
             (match get "contains", inst with
              | Some sub, JArray xs ->
                let rs = results_over_instances ctx base sub xs f1 in
                if L.existsb (fun r -> r = VPass) rs then VPass
                else if L.existsb (fun r -> r = VUnsupported) rs then VUnsupported
                else VFail
              | _, _ -> VPass) in

           let c_allof =
             (match get "allOf" with
              | Some (JArray subs) -> L.fold_left vand VPass (results_over_schemas ctx base subs inst f1)
              | _ -> VPass) in

           let c_anyof =
             (match get "anyOf" with
              | Some (JArray subs) -> L.fold_left vor VFail (results_over_schemas ctx base subs inst f1)
              | _ -> VPass) in

           let c_oneof =
             (match get "oneOf" with
              | Some (JArray subs) ->
                let rs = results_over_schemas ctx base subs inst f1 in
                if L.existsb (fun r -> r = VUnsupported) rs then VUnsupported
                else if L.length (L.filter (fun r -> r = VPass) rs) = 1 then VPass else VFail
              | _ -> VPass) in

           let c_not =
             (match get "not" with
              | Some s ->
                (match validate_schema ctx base s inst f1 with
                 | VPass -> VFail | VFail -> VPass | VUnsupported -> VUnsupported)
              | None -> VPass) in

           let c_ite =
             (match get "if" with
              | None -> VPass
              | Some ci ->
                (match validate_schema ctx base ci inst f1 with
                 | VUnsupported -> VUnsupported
                 | VPass -> (match get "then" with Some t -> validate_schema ctx base t inst f1 | None -> VPass)
                 | VFail -> (match get "else" with Some e -> validate_schema ctx base e inst f1 | None -> VPass))) in

           L.fold_left vand VPass
             [ c_local; c_pattern; c_props; c_patprops; c_addprops; c_propnames; c_deps;
               c_items; c_additems; c_contains; c_allof; c_anyof; c_oneof; c_not; c_ite ]
         end)
    | _ -> VUnsupported

// Validate a fixed subschema against each instance value in a list.
and results_over_instances (ctx:refctx) (base:string) (sub:json_val) (xs:list json_val) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match xs with
     | [] -> []
     | x :: tl -> validate_schema ctx base sub x (fuel - 1) :: results_over_instances ctx base sub tl (fuel - 1))

// Validate a fixed instance against each subschema in a list.
and results_over_schemas (ctx:refctx) (base:string) (subs:list json_val) (inst:json_val) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match subs with
     | [] -> []
     | s :: tl -> validate_schema ctx base s inst (fuel - 1) :: results_over_schemas ctx base tl inst (fuel - 1))

// properties: for each declared property present in the instance object,
// validate its value against the property subschema.
and results_props (ctx:refctx) (base:string) (ps:list (string & json_val)) (fs:list (string & json_val)) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match ps with
     | [] -> []
     | (pn, psub) :: tl ->
       let rest = results_props ctx base tl fs (fuel - 1) in
       (match lookup pn fs with
        | Some pv -> validate_schema ctx base psub pv (fuel - 1) :: rest
        | None -> rest))

// patternProperties: for each (regex, subschema) pair, validate every
// instance-property value whose NAME matches the regex.
and results_patprops (ctx:refctx) (base:string) (pps:list (string & json_val)) (fs:list (string & json_val)) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match pps with
     | [] -> []
     | (rgx, sub) :: tl ->
       L.append (results_patprop_one ctx base rgx sub fs (fuel - 1))
                (results_patprops ctx base tl fs (fuel - 1)))

// One patternProperties entry: validate matching-keyed values against `sub`.
and results_patprop_one (ctx:refctx) (base rgx:string) (sub:json_val) (fs:list (string & json_val)) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match fs with
     | [] -> []
     | (k, v) :: tl ->
       let rest = results_patprop_one ctx base rgx sub tl (fuel - 1) in
       (match ecma_match rgx k with
        | Some true -> validate_schema ctx base sub v (fuel - 1) :: rest
        | Some false -> rest
        | None -> VUnsupported :: rest))

// items tuple form: validate positionally-paired (subschema, value).
and results_pairs (ctx:refctx) (base:string) (pairs:list (json_val & json_val)) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match pairs with
     | [] -> []
     | (sub, x) :: tl -> validate_schema ctx base sub x (fuel - 1) :: results_pairs ctx base tl (fuel - 1))

// dependencies: property dependency (array of required names) or schema
// dependency (validate the whole instance) triggered by a present property.
and results_deps (ctx:refctx) (base:string) (deps:list (string & json_val)) (fs:list (string & json_val))
                 (inst:json_val) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match deps with
     | [] -> []
     | (pn, dv2) :: tl ->
       let rest = results_deps ctx base tl fs inst (fuel - 1) in
       if has_key pn fs then
         (match dv2 with
          | JArray names -> (if names_present fs names then VPass else VFail) :: rest
          | _ -> validate_schema ctx base dv2 inst (fuel - 1) :: rest)
       else rest)
#pop-options

// Build the $id / $anchor registry from the root document plus any external
// documents. The root is registered under the empty base "" (so bare "#..."
// pointers resolve) and under its own $id if present.
let rec collect_externals (externals:list (string & json_val)) (fuel:nat)
  : Tot (list (string & json_val) & list (string & json_val)) (decreases externals) =
  match externals with
  | [] -> ([], [])
  | (u, doc) :: tl ->
    let (a1, b1) = collect_ids (base_of u) doc fuel in
    let (a2, b2) = collect_externals tl fuel in
    (L.append ((u, doc) :: a1) a2, L.append b1 b2)

let root_base_of (schema:json_val) : string =
  match json_get_field "$id" schema with Some (JString i) -> base_of (resolve_uri "" i) | _ -> ""

let build_ctx (externals:list (string & json_val)) (schema:json_val) : refctx =
  let rb = root_base_of schema in
  let cf : nat = 100 + 4 * json_size schema in
  let (sids, sanch) = collect_ids rb schema cf in
  let (eids, eanch) = collect_externals externals cf in
  let base_reg = ("", schema) :: (if rb = "" then [] else [(rb, schema)]) in
  { idreg = L.append base_reg (L.append sids eids); anchreg = L.append sanch eanch }

// Top-level entry with caller-supplied external documents (URI -> root). The
// runner passes the vendored draft-07 meta-schema here so remote $refs to
// http://json-schema.org/draft-07/schema resolve. Fuel is seeded from the
// JSON sizes, far above the traversal depth any draft-07 test needs.
let validate_ext (externals:list (string & json_val)) (schema inst:json_val) : vresult =
  let ctx = build_ctx externals schema in
  let n = json_size schema + json_size inst + 10 in
  validate_schema ctx (root_base_of schema) schema inst (n * n + 5000)

let validate (schema inst:json_val) : vresult = validate_ext [] schema inst

// Boolean convenience: VUnsupported collapses to "not a definite pass".
let validate_bool (schema inst:json_val) : bool =
  match validate schema inst with VPass -> true | _ -> false
