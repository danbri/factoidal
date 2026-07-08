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
// SCOPE (slice-1, draft-07 core keywords):
//   type (all 7 incl. integer-vs-number), enum, const,
//   properties, required, additionalProperties (bool + schema),
//   propertyNames, minProperties, maxProperties, dependencies,
//   items (single schema + tuple form), additionalItems, contains,
//   minItems, maxItems, uniqueItems,
//   minimum, maximum, exclusiveMinimum, exclusiveMaximum, multipleOf,
//   minLength, maxLength,
//   allOf, anyOf, oneOf, not, if/then/else,
//   boolean schemas (true/false),
//   $ref to local JSON pointers ("#", "#/definitions/x", "#/properties/y",
//   "#/items/0"), resolved within the same document.
//
// NOT COVERED (returned as VUnsupported so the runner counts them as skips,
// never a wrong verdict): pattern, patternProperties, format (need a regex
// facility this project does not expose inside the verified boundary),
// non-local / remote $ref, "#anchor" id-refs. Any subschema that mentions
// pattern / patternProperties / format directly, or a $ref we cannot resolve
// locally, short-circuits to VUnsupported. Annotation keywords (title,
// description, $comment, $schema, $id, definitions, default, examples) are
// ignored per the "unknown keywords are annotations" rule.
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

// Tokens of a local JSON pointer, or None when the $ref is not a resolvable
// local pointer (remote ref, or a "#anchor" id-ref we do not support).
let ptr_tokens (r:string) : option (list string) =
  match list_of_string r with
  | '#' :: rest ->
    let frag = string_of_list rest in
    if frag = "" then Some []
    else
      (match rest with
       | '/' :: _ ->
         (match FStar.String.split ['/'] frag with
          | _ :: toks -> Some toks
          | [] -> Some [])
       | _ -> None)
  | _ -> None

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
let rec validate_schema (root schema inst:json_val) (fuel:nat) : Tot vresult (decreases fuel) =
  if fuel = 0 then VUnsupported
  else
    let f1 = fuel - 1 in
    match schema with
    | JBool true -> VPass
    | JBool false -> VFail
    | JObject _ ->
      // $ref, when present, is applied alone; draft-07 ignores siblings.
      (match json_get_field "$ref" schema with
       | Some (JString r) ->
         (match ptr_tokens r with
          | None -> VUnsupported
          | Some toks ->
            (match resolve_pointer root toks with
             | None -> VUnsupported
             | Some sub -> validate_schema root sub inst f1))
       | Some _ -> VUnsupported
       | None ->
         let get (k:string) : option json_val = json_get_field k schema in
         // Unsupported assertion keywords: short-circuit to a skip so we never
         // emit a wrong verdict from ignoring pattern / format semantics.
         if Some? (get "pattern") || Some? (get "patternProperties") || Some? (get "format")
         then VUnsupported
         else begin
           let c_local = check_local schema inst in

           let c_props =
             (match get "properties", inst with
              | Some (JObject ps), JObject fs -> L.fold_left vand VPass (results_props root ps fs f1)
              | _, _ -> VPass) in

           let c_addprops =
             (match get "additionalProperties", inst with
              | Some ap, JObject fs ->
                let declared = (match get "properties" with Some (JObject ps) -> L.map fst ps | _ -> []) in
                let extra = L.filter (fun (k, _) -> not (L.mem k declared)) fs in
                (match ap with
                 | JBool true -> VPass
                 | JBool false -> (match extra with [] -> VPass | _ -> VFail)
                 | _ -> L.fold_left vand VPass (results_over_instances root ap (L.map snd extra) f1))
              | _, _ -> VPass) in

           let c_propnames =
             (match get "propertyNames", inst with
              | Some pn, JObject fs ->
                L.fold_left vand VPass
                  (results_over_instances root pn (L.map (fun (k, _) -> JString k) fs) f1)
              | _, _ -> VPass) in

           let c_deps =
             (match get "dependencies", inst with
              | Some (JObject deps), JObject fs ->
                L.fold_left vand VPass (results_deps root deps fs inst f1)
              | _, _ -> VPass) in

           let c_items =
             (match get "items", inst with
              | Some (JArray subs), JArray xs ->
                L.fold_left vand VPass (results_pairs root (zip_pairs subs xs) f1)
              | Some sub, JArray xs ->
                if JObject? sub || JBool? sub
                then L.fold_left vand VPass (results_over_instances root sub xs f1)
                else VPass
              | _, _ -> VPass) in

           let c_additems =
             (match get "additionalItems", get "items", inst with
              | Some ai, Some (JArray subs), JArray xs ->
                let extra = drop_n (L.length subs) xs in
                (match ai with
                 | JBool true -> VPass
                 | JBool false -> (match extra with [] -> VPass | _ -> VFail)
                 | _ -> L.fold_left vand VPass (results_over_instances root ai extra f1))
              | _, _, _ -> VPass) in

           let c_contains =
             (match get "contains", inst with
              | Some sub, JArray xs ->
                let rs = results_over_instances root sub xs f1 in
                if L.existsb (fun r -> r = VPass) rs then VPass
                else if L.existsb (fun r -> r = VUnsupported) rs then VUnsupported
                else VFail
              | _, _ -> VPass) in

           let c_allof =
             (match get "allOf" with
              | Some (JArray subs) -> L.fold_left vand VPass (results_over_schemas root subs inst f1)
              | _ -> VPass) in

           let c_anyof =
             (match get "anyOf" with
              | Some (JArray subs) -> L.fold_left vor VFail (results_over_schemas root subs inst f1)
              | _ -> VPass) in

           let c_oneof =
             (match get "oneOf" with
              | Some (JArray subs) ->
                let rs = results_over_schemas root subs inst f1 in
                if L.existsb (fun r -> r = VUnsupported) rs then VUnsupported
                else if L.length (L.filter (fun r -> r = VPass) rs) = 1 then VPass else VFail
              | _ -> VPass) in

           let c_not =
             (match get "not" with
              | Some s ->
                (match validate_schema root s inst f1 with
                 | VPass -> VFail | VFail -> VPass | VUnsupported -> VUnsupported)
              | None -> VPass) in

           let c_ite =
             (match get "if" with
              | None -> VPass
              | Some ci ->
                (match validate_schema root ci inst f1 with
                 | VUnsupported -> VUnsupported
                 | VPass -> (match get "then" with Some t -> validate_schema root t inst f1 | None -> VPass)
                 | VFail -> (match get "else" with Some e -> validate_schema root e inst f1 | None -> VPass))) in

           L.fold_left vand VPass
             [ c_local; c_props; c_addprops; c_propnames; c_deps; c_items; c_additems;
               c_contains; c_allof; c_anyof; c_oneof; c_not; c_ite ]
         end)
    | _ -> VUnsupported

// Validate a fixed subschema against each instance value in a list.
and results_over_instances (root sub:json_val) (xs:list json_val) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match xs with
     | [] -> []
     | x :: tl -> validate_schema root sub x (fuel - 1) :: results_over_instances root sub tl (fuel - 1))

// Validate a fixed instance against each subschema in a list.
and results_over_schemas (root:json_val) (subs:list json_val) (inst:json_val) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match subs with
     | [] -> []
     | s :: tl -> validate_schema root s inst (fuel - 1) :: results_over_schemas root tl inst (fuel - 1))

// properties: for each declared property present in the instance object,
// validate its value against the property subschema.
and results_props (root:json_val) (ps:list (string & json_val)) (fs:list (string & json_val)) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match ps with
     | [] -> []
     | (pn, psub) :: tl ->
       let rest = results_props root tl fs (fuel - 1) in
       (match lookup pn fs with
        | Some pv -> validate_schema root psub pv (fuel - 1) :: rest
        | None -> rest))

// items tuple form: validate positionally-paired (subschema, value).
and results_pairs (root:json_val) (pairs:list (json_val & json_val)) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match pairs with
     | [] -> []
     | (sub, x) :: tl -> validate_schema root sub x (fuel - 1) :: results_pairs root tl (fuel - 1))

// dependencies: property dependency (array of required names) or schema
// dependency (validate the whole instance) triggered by a present property.
and results_deps (root:json_val) (deps:list (string & json_val)) (fs:list (string & json_val))
                 (inst:json_val) (fuel:nat)
  : Tot (list vresult) (decreases fuel) =
  if fuel = 0 then []
  else
    (match deps with
     | [] -> []
     | (pn, dv2) :: tl ->
       let rest = results_deps root tl fs inst (fuel - 1) in
       if has_key pn fs then
         (match dv2 with
          | JArray names -> (if names_present fs names then VPass else VFail) :: rest
          | _ -> validate_schema root dv2 inst (fuel - 1) :: rest)
       else rest)
#pop-options

// Top-level entry: seed fuel from the JSON sizes (far above the traversal
// depth * breadth any real draft-07 test needs).
let validate (schema inst:json_val) : vresult =
  let n = json_size schema + json_size inst + 10 in
  validate_schema schema schema inst (n * n + 5000)

// Boolean convenience: VUnsupported collapses to "not a definite pass".
let validate_bool (schema inst:json_val) : bool =
  match validate schema inst with VPass -> true | _ -> false
