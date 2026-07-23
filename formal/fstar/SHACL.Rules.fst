module SHACL.Rules

/// SHACL 1.2 Rules — the `.srl` rule-language evaluator (shacl12
/// `rules/eval` suite). An `.srl` file is a small surface syntax:
///
///   PREFIX .. .                       (SPARQL-style prefix declarations)
///   RULE { head } WHERE { body }      (a CONSTRUCT-style inference rule)
///   DATA { triples }                  (assert triples directly)
///   ## comment
///
/// Each RULE / DATA block translates to a SPARQL CONSTRUCT query (the
/// prefix header prepended), which we run with the existing
/// `SPARQL11.Algebra.eval_construct_query`. Evaluation is a bottom-up
/// fixpoint: apply every construct to the accumulating graph, add the
/// new triples, and repeat until no triple is added (bounded by fuel).
/// A `NOT { pattern }` in a WHERE clause becomes `FILTER NOT EXISTS`.
///
/// Parser + engine live in F\* per the project rules; the consumer
/// runner only does file I/O and the result-graph comparison.

open FStar.List.Tot
open FStar.Char
open RDF.Graph.Executable
module Str = FStar.String

module Alg = SPARQL11.Algebra
module Parser11 = SPARQL11.Parser

// --- small string helpers --------------------------------------------

let rec drop_ws (cs : list char) : Tot (list char) (decreases cs) =
  match cs with
  | ' '  :: r -> drop_ws r
  | '\t' :: r -> drop_ws r
  | _ -> cs

let lstrip (s : string) : string = Str.string_of_list (drop_ws (Str.list_of_string s))

let starts_with (s : string) (pfx : string) : bool =
  let n = Str.length pfx in
  Str.length s >= n && Str.sub s 0 n = pfx

let rec chars_prefix_match (n : list char) (h : list char) : Tot bool (decreases n) =
  match n, h with
  | [], _ -> true
  | _, [] -> false
  | a :: n', b :: h' -> a = b && chars_prefix_match n' h'

let rec chars_drop (k : nat) (l : list char) : Tot (list char) (decreases l) =
  match k, l with
  | 0, _ -> l
  | _, [] -> []
  | _, _ :: t -> chars_drop (k - 1) t

// Plain (non-regex) replacement of every occurrence of `needle` in the
// char list with `repl`. Fuel-bounded (each step consumes >=1 char).
let rec replace_all_chars (fuel : nat) (cs : list char) (needle repl : list char)
  : Tot (list char) (decreases fuel)
  =
  if fuel = 0 then cs else
  match cs with
  | [] -> []
  | c :: rest ->
    if Cons? needle && chars_prefix_match needle cs
    then repl @ replace_all_chars (fuel - 1) (chars_drop (List.Tot.length needle) cs) needle repl
    else c :: replace_all_chars (fuel - 1) rest needle repl

let replace_all (s needle repl : string) : string =
  let cs = Str.list_of_string s in
  Str.string_of_list (replace_all_chars (Str.length s + 1) cs (Str.list_of_string needle) (Str.list_of_string repl))

// --- .srl -> CONSTRUCT translation -----------------------------------

// Is a (raw) line a RULE / DATA directive? (after leading whitespace)
let line_kind (line : string) : option bool =  // Some true = RULE, Some false = DATA
  let t = lstrip line in
  if starts_with t "RULE" then Some true
  else if starts_with t "DATA" then Some false
  else None

// Everything on `line` after the leading keyword (RULE/DATA), i.e. the
// brace groups. Keyword length is 4 for both RULE and DATA.
let line_body (line : string) : string =
  let t = lstrip line in
  if Str.length t >= 4 then Str.sub t 4 (Str.length t - 4) else ""

let is_block_kw (cs : list char) : bool =
  chars_prefix_match ['R'; 'U'; 'L'; 'E'] cs || chars_prefix_match ['D'; 'A'; 'T'; 'A'] cs

// Split the srl into brace-aware segments: a new segment starts at each
// top-level (brace-depth 0) RULE/DATA keyword that follows whitespace.
// The first segment is the prefix header; each later one is a single
// (possibly multi-line) RULE/DATA block. Fuel = char count.
let rec scan_blocks (cs : list char) (depth : int) (prev_ws : bool)
                    (curr : list char) (blocks : list string) (fuel : nat)
  : Tot (list string) (decreases fuel)
  =
  if fuel = 0 then List.Tot.rev (Str.string_of_list (List.Tot.rev curr) :: blocks) else
  match cs with
  | [] -> List.Tot.rev (Str.string_of_list (List.Tot.rev curr) :: blocks)
  | c :: rest ->
    if depth = 0 && prev_ws && is_block_kw cs
    then scan_blocks rest depth false [c] (Str.string_of_list (List.Tot.rev curr) :: blocks) (fuel - 1)
    else
      let depth' = if c = '{' then depth + 1 else if c = '}' then depth - 1 else depth in
      let ws = (c = ' ' || c = '\n' || c = '\t' || c = '\r') in
      scan_blocks rest depth' ws (c :: curr) blocks (fuel - 1)

// Translate every RULE/DATA line into a CONSTRUCT query text (header
// prepended). RULE {H} WHERE {B} -> CONSTRUCT {H} WHERE {B};
// DATA {T} -> CONSTRUCT {T} WHERE {}. `NOT {` -> `FILTER NOT EXISTS {`.
let rec rule_texts (header : string) (ls : list string) : Tot (list string) (decreases ls) =
  match ls with
  | [] -> []
  | l :: rest ->
    (match line_kind l with
     | Some true ->
       let body = replace_all (line_body l) "NOT {" "FILTER NOT EXISTS {" in
       (Str.concat "" [header; "\nCONSTRUCT "; body]) :: rule_texts header rest
     | Some false ->
       (Str.concat "" [header; "\nCONSTRUCT "; line_body l; " WHERE {}"]) :: rule_texts header rest
     | None -> rule_texts header rest)

let translate_srl (srl : string) : list string =
  match scan_blocks (Str.list_of_string srl) 0 true [] [] (Str.length srl + 2) with
  | [] -> []
  | header :: blocks -> rule_texts header blocks

// --- syntax validation (rules/syntax suite) --------------------------

let str_has_char (c : char) (s : string) : bool = List.Tot.mem c (Str.list_of_string s)

// A single RULE/DATA block is syntactically valid iff its translated
// CONSTRUCT query parses; additionally a DATA block must be GROUND (no
// query variables — SHACL rules DATA is asserted data, not a pattern).
let block_valid (header : string) (block : string) : bool =
  match line_kind block with
  | Some true ->
    let txt = Str.concat "" [header; "\nCONSTRUCT ";
                             replace_all (line_body block) "NOT {" "FILTER NOT EXISTS {"] in
    (match Parser11.parse_sparql txt with Parser11.ParseOk _ _ -> true | _ -> false)
  | Some false ->
    let body = line_body block in
    if str_has_char '?' body || str_has_char '$' body then false
    else (match Parser11.parse_sparql (Str.concat "" [header; "\nCONSTRUCT "; body; " WHERE {}"]) with
          | Parser11.ParseOk _ _ -> true | _ -> false)
  | None -> true

let rec all_blocks_valid (header : string) (bs : list string) : Tot bool (decreases bs) =
  match bs with
  | [] -> true
  | b :: rest -> block_valid header b && all_blocks_valid header rest

// Is the whole ruleset syntactically valid? (Every RULE/DATA block
// translates to a parseable CONSTRUCT, DATA blocks are ground.)
let srl_valid_syntax (srl : string) : bool =
  match scan_blocks (Str.list_of_string srl) 0 true [] [] (Str.length srl + 2) with
  | [] -> true
  | header :: blocks -> all_blocks_valid header blocks

// --- well-formedness (rules/wellformed suite) ------------------------

// A variable-name continuation char: anything that is NOT one of the
// SPARQL token delimiters (so `?name` runs up to the next delimiter).
let is_var_name_char (c : char) : bool =
  not (c = ' ' || c = '\n' || c = '\t' || c = '\r' || c = '.' || c = '{' || c = '}'
       || c = '(' || c = ')' || c = ';' || c = ',' || c = '?' || c = '$'
       || c = '<' || c = '>' || c = '"' || c = '\'' || c = '[' || c = ']')

let rec take_while (p : char -> bool) (cs : list char) : Tot (list char) (decreases cs) =
  match cs with c :: r -> if p c then c :: take_while p r else [] | [] -> []

let rec drop_while (p : char -> bool) (cs : list char) : Tot (list char) (decreases cs) =
  match cs with c :: r -> if p c then drop_while p r else cs | [] -> []

// Every `?name` / `$name` variable token in the char list.
let rec collect_vars (cs : list char) (fuel : nat) : Tot (list string) (decreases fuel) =
  if fuel = 0 then [] else
  match cs with
  | [] -> []
  | c :: rest ->
    if c = '?' || c = '$'
    then (match take_while is_var_name_char rest with
          | [] -> collect_vars rest (fuel - 1)
          | nm -> Str.string_of_list nm :: collect_vars (drop_while is_var_name_char rest) (fuel - 1))
    else collect_vars rest (fuel - 1)

let vars_in (s : string) : list string = collect_vars (Str.list_of_string s) (Str.length s + 1)

// Split `cs` at the first occurrence of `needle`, returning
// (before, after) as strings; None if the needle never appears.
let rec split_at_needle (cs : list char) (needle : list char) (acc : list char) (fuel : nat)
  : Tot (option (string & string)) (decreases fuel)
  =
  if fuel = 0 then None else
  match cs with
  | [] -> None
  | c :: rest ->
    if chars_prefix_match needle cs
    then Some (Str.string_of_list (List.Tot.rev acc),
               Str.string_of_list (chars_drop (List.Tot.length needle) cs))
    else split_at_needle rest needle (c :: acc) (fuel - 1)

let rec all_mem (xs : list string) (ys : list string) : Tot bool (decreases xs) =
  match xs with [] -> true | x :: r -> List.Tot.mem x ys && all_mem r ys

// A RULE is well-formed iff every variable used in its HEAD is bound by
// its body (the range-restriction / safety condition — an unbound head
// variable cannot be instantiated). DATA blocks and non-rule segments
// are trivially well-formed here.
let block_well_formed (block : string) : bool =
  match line_kind block with
  | Some true ->
    (match split_at_needle (Str.list_of_string (line_body block)) ['W'; 'H'; 'E'; 'R'; 'E'] []
             (Str.length block + 1) with
     | Some (head, body) -> all_mem (vars_in head) (vars_in body)
     | None -> true)
  | _ -> true

let rec all_blocks_well_formed (bs : list string) : Tot bool (decreases bs) =
  match bs with [] -> true | b :: rest -> block_well_formed b && all_blocks_well_formed rest

let srl_well_formed (srl : string) : bool =
  match scan_blocks (Str.list_of_string srl) 0 true [] [] (Str.length srl + 2) with
  | [] -> true
  | _ :: blocks -> all_blocks_well_formed blocks

// --- fixpoint evaluation ---------------------------------------------

let parse_constructs (srl : string) : list Alg.query =
  List.Tot.concatMap
    (fun t -> match Parser11.parse_sparql t with
              | Parser11.ParseOk q _ -> [q]
              | _ -> [])
    (translate_srl srl)

// One inference step: union the current graph with every construct's
// output, deduplicated.
let rules_step (g : rdf_graph) (qs : list Alg.query) : rdf_graph =
  let inferred =
    List.Tot.concatMap
      (fun q -> Alg.eval_construct_query q g ({ ds_default = g; ds_named = [] }))
      qs in
  Alg.dedup_triples (g @ inferred)

// Bottom-up fixpoint: stop when a step adds no new triple (graph size
// stable) or the fuel runs out.
let rec rules_fixpoint (g : rdf_graph) (qs : list Alg.query) (fuel : nat)
  : Tot rdf_graph (decreases fuel)
  =
  if fuel = 0 then g else
  let g' = rules_step g qs in
  if List.Tot.length g' = List.Tot.length g then g'
  else rules_fixpoint g' qs (fuel - 1)

// Entry point: the triples INFERRED from `data` by the rules in `srl`
// (the fixpoint closure minus the original data — the shacl12 rules
// suite's mf:result asserts only the newly-derived triples).
let run_rules (data : rdf_graph) (srl : string) : rdf_graph =
  let qs = parse_constructs srl in
  let closure = rules_fixpoint (Alg.dedup_triples data) qs (List.Tot.length data + 100) in
  List.Tot.filter (fun t -> not (List.Tot.existsb (fun d -> triple_eq t d) data)) closure
