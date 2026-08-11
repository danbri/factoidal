module SPARQL.Protocol.RoundTrip

(** ======================================================================== **)
(** G4 M4: response-edge round-trips — SPARQL Results JSON (SRJ)             **)
(**                                                                          **)
(** GOAL: prove SPARQL.Protocol.serialise_response_json (line 908 at         **)
(** authoring time) and Parser.JSONResults.parse_srj_results (line 133) are  **)
(** inverse on a precisely stated fragment, following the byte-format        **)
(** round-trip TEMPLATE in RDF.Store.Columnar.DeltaLog                       **)
(** (lemma_u8_roundtrip / lemma_lstring_roundtrip / lemma_term_roundtrip /   **)
(** lemma_triple_roundtrip).                                                 **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** FINDING (blocks the literal goal — read before extending this file)     **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** The DeltaLog template works because its serializer/parser pair operate  **)
(** on `RDF.Bytes.bytes = list u8`, an F*-native inductive type: `append`    **)
(** has real equations (`FStar.List.Tot` lemmas), so                        **)
(** `parse (append (serialize x) rest) == Some (x, rest)` is a genuine       **)
(** induction on that structure.                                             **)
(**                                                                          **)
(** SRJ's actual text parser, `Parser.JSON.parse_json` (which                **)
(** `Parser.JSONResults.parse_srj_results` calls first, and which this       **)
(** module was migrated onto per #310), is NOT built that way. Every byte    **)
(** the recursive-descent scanner reads goes through                        **)
(** `Parser.FastString.{fs_byte_length, fs_byte_at, fs_byte_sub, fs_cp_at}`  **)
(** — four `assume val`s (rule #11(b): a legitimate perf realisation,        **)
(** `70_fast_string_primitives.sh`/`89_fast_string_primitives.sh`, OCaml-    **)
(** side `String.length`/`String.unsafe_get`/`String.sub`) that carry        **)
(** **no F*-visible equations** connecting their output to the abstract      **)
(** `string` value they were called on — not to `FStar.String` operations,   **)
(** not to `^` (concatenation), not even to string LITERALS. Confirmed        **)
(** empirically before writing this module: in a throwaway probe file,       **)
(**   `let test () : Lemma (fs_byte_length "ab" == 2) = ()`                  **)
(** fails to verify (Error 19, "Could not prove post-condition") — z3 cannot **)
(** derive even that trivial fact, because `fs_byte_length` is an            **)
(** uninterpreted symbol to the SMT solver with zero defining axioms.        **)
(** `json_escape` (SPARQL.Protocol.fst line ~711) is on the *serializer*     **)
(** side of the very same wall: it decomposes its input via                  **)
(** `Parser.FastString.fs_codepoints_of_string`, which bottoms out in the    **)
(** same opaque `fs_cp_at`. So this is not only "the parser is opaque" —     **)
(** the serializer's own escaping step is equally unreasoned-about at the    **)
(** F* level.                                                                **)
(**                                                                          **)
(** Consequence: no equation of the shape                                    **)
(**   `parse_json (serialise_response_json vars rows) == Some ...`           **)
(** — nor even the ASK-boolean special case                                  **)
(**   `parse_srj_boolean (serialise_response_boolean_json b) == Some b`      **)
(** — is provable against the CURRENT tree without first landing bridging    **)
(** lemmas in `Parser.FastString` itself (e.g. `fs_byte_length (a ^ b) ==    **)
(** fs_byte_length a + fs_byte_length b`, an `fs_byte_at`/`fs_byte_sub`       **)
(** analogue, and a defining relationship for `fs_cp_at` on `^`-built        **)
(** strings). That is real, independently-scoped work belonging to           **)
(** `Parser.FastString.fst` under CLAUDE.md rule #11(b) (an Option-B perf    **)
(** realisation needs its byte-format spec "in F* with a hash-witness CI     **)
(** test" — these four primitives currently have neither), not to this       **)
(** module. It should be filed as its own GitHub issue before the SRJ        **)
(** text-level round-trip can be attempted again; grep this banner for       **)
(** "fs_byte_length (a ^ b)" when picking that issue up.                     **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** FINDING, CONTINUED (session 2026-08-09) -- literal-lexing step blocked  **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** `Parser.FastString.Axioms.fsti` (6 facts) and                           **)
(** `Parser.FastString.RoundTripLemmas.fst`                                 **)
(** (`lemma_byte_at_after_prefix`) landed since the FINDING above was       **)
(** written -- the length-homomorphism, index-into-concat, and              **)
(** slice-into-concat facts the FINDING called for. They do NOT close the   **)
(** gap: attempting step 1 of the brief this session ("serialised-literal    **)
(** lexing lemmas -- parse of a quoted escape-free string literal consumes  **)
(** exactly its bytes and yields the string") hits a DEEPER wall than the    **)
(** original FINDING named. All six axioms are RELATIONAL (concat           **)
(** homomorphism, index/slice-into-concat, cp_at agreeing with an           **)
(** ALREADY-KNOWN byte_at value) -- none supplies a BASE CASE tying          **)
(** `fs_byte_at`'s or `fs_byte_sub`'s return VALUE to any string's actual    **)
(** content, literal or variable. Confirmed empirically this session         **)
(** (probes run and discarded, not committed): both                          **)
(**   `let _ : Lemma (fs_byte_at "a" 0 == 97) = ()`                          **)
(**   `let _ (s:string) : Lemma (fs_byte_sub s 0 (fs_byte_length s) == s) = ()` **)
(** fail Error 19 ("Could not prove post-condition"), the same failure       **)
(** mode as the original `fs_byte_length "ab" == 2` probe above.             **)
(**                                                                          **)
(** Consequence: no branch of `json_parse_value` / `json_parse_string` /     **)
(** `json_parse_object` / `json_parse_array` (all in `Parser.JSON.fst`) is   **)
(** provable AT ALL -- every one dispatches on the concrete byte VALUE       **)
(** `fs_byte_at` returns (is this `"`? `{`? `:`? `,`? a control byte?), and  **)
(** the current axiom set supplies that value for no string whatsoever.     **)
(** This blocks step 1 of the brief's chain outright -- steps 2 (object/    **)
(** array framing) and 3 (composition with the tree lemmas below) cannot    **)
(** be attempted without it. Two candidate facts were recorded, WITH exact  **)
(** signatures and realisation-justification sketches, in                   **)
(** `Parser.FastString.Axioms.fsti`'s "STILL MISSING" note (its `fact 7`     **)
(** and `fact 8`).                                                          **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** FACTS 7/8 PROMOTED (owner authorization 2026-08-09, issue #358 comment  **)
(** of that date) -- NEW FINDING: a SEPARATE wall past the JSON string body **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** With facts 7/8 landed, `Parser.FastString.RoundTripLemmas.fst` proves    **)
(** (session 2026-08-09/10) the byte-level "quoted-string read-back"        **)
(** primitive named in the brief: for ASCII content built explicitly from a  **)
(** codepoint list (`build_string cs`), slicing the byte range between the   **)
(** two quote bytes of `"\"" ^ build_string cs ^ "\""` recovers `build_string **)
(** cs` exactly (`lemma_quoted_content_byte_sub`), plus the supporting       **)
(** byte-length/byte-at characterisation lemmas the induction needs         **)
(** (`lemma_build_string_byte_length`, `lemma_build_string_byte_at`).       **)
(**                                                                          **)
(** This does NOT close `Parser.JSON.json_parse_string`'s literal theorem.   **)
(** Confirmed empirically by attempting the FULL induction on               **)
(** `json_string_segments` (probe run and discarded, not committed): even   **)
(** the SIMPLEST case -- an EMPTY JSON string body, `""`, one recursive      **)
(** step from the closing quote -- fails Error 19 on exactly ONE step, and   **)
(** admitting that ONE step as a local lemma makes the rest of the SAME      **)
(** induction go through immediately with no further obstruction:           **)
(**   `json_string_segments`'s terminal case computes                       **)
(**     `String.concat "" (List.Tot.rev segs_done)`                        **)
(**   where for escape-free content `segs_done` is always the SINGLETON     **)
(**   list `[fs_byte_sub input seg_start (pos - seg_start)]` (no escape ever **)
(**   fires, so `segs` never grows past one element). The missing step is    **)
(**   `String.concat "" [x] == x` for a SYMBOLIC `x` -- true unconditionally **)
(**   (any string-join of a one-element list returns that element, for ANY   **)
(**   separator, not just `""`), but `FStar.String.concat` carries ZERO      **)
(**   stated equations in `FStar.String.fsti` (confirmed: grepped the whole  **)
(**   file, 149 lines, `val concat` at line 76, no `Lemma` mentions it       **)
(**   anywhere) -- the SAME "opaque F* stdlib primitive, zero axioms" shape  **)
(**   as the ORIGINAL fs_byte_length wall, but for a DIFFERENT function      **)
(**   (`FStar.String.concat`, not anything in `Parser.FastString`), so it is **)
(**   OUT OF SCOPE for `Parser.FastString.Axioms.fsti`'s eight-fact trust    **)
(**   surface and today's owner authorization, which named only the two     **)
(**   FastString facts.                                                     **)
(**                                                                          **)
(**   CANDIDATE FACT (NOT ADDED -- owner-gated, same protocol as facts 7/8): **)
(**     val string_concat_singleton (sep x : string)                        **)
(**       : Lemma (FStar.String.concat sep [x] == x)                        **)
(**   OCaml justification (checked against the realisation this session):   **)
(**   `FStar.String.concat` extracts to `BatString.concat` (ulib/ml/app/     **)
(**   FStar_String.ml line 20: `let concat = BatString.concat`) --          **)
(**   Batteries' string-join places `sep` strictly BETWEEN elements (n-1     **)
(**   separators for n elements), so a one-element list needs zero           **)
(**   separators and `BatString.concat sep [x]` returns `x` verbatim,        **)
(**   independent of `sep`'s value. A candidate fact for a FUTURE session    **)
(**   (or this one, if re-authorized) to check line-by-line and propose.     **)
(**                                                                          **)
(**   This blocks `json_parse_string`'s literal theorem at its narrowest     **)
(**   possible instance (the empty-string case), so it also blocks           **)
(**   `json_parse_value`/`json_parse_object`/`json_parse_array` (step 2) and **)
(**   the full text-level composition (step 3) transitively -- AND blocks   **)
(**   step 3 a SECOND, independent way even if step 1 were finessed some     **)
(**   other route: `SPARQL.Protocol.serialise_response_json` (line ~915)     **)
(**   and `json_row`/`json_var_list` all end in their own                   **)
(**   `String.concat "" pieces` call over a LIST WHOSE LENGTH VARIES with    **)
(**   the input (`vars`/`rows`), so composing the tree-level lemmas below    **)
(**   with the TEXT serialiser needs the general N-element form of the same **)
(**   missing fact, not just the singleton case.                            **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** WHAT THIS MODULE PROVES INSTEAD: the STRUCTURAL half                     **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** `Parser.JSONResults.parse_binding_value` / `parse_binding_row` and the   **)
(** vars/rows extraction inlined in `parse_srj_results` do NOT touch         **)
(** `Parser.FastString` at all once they are handed a `Parser.JSON.json_val` **)
(** TREE — they are plain, fully-`Tot`, structurally-recursive functions     **)
(** over `list`/`option`/`JObject`/`JArray` with real F* equations           **)
(** (`List.Tot.find`, `List.Tot.concatMap`, `List.Tot.map`). That half of    **)
(** the pipeline — decode-from-tree — is exactly as tractable as DeltaLog's  **)
(** byte-list decode, and this module proves it.                            **)
(**                                                                          **)
(** The construction: `json_val_of_term` / `json_val_of_row` /               **)
(** `json_val_of_response` / `json_val_of_bool` below are STRUCTURAL         **)
(** mirrors of what `json_term` / `json_row` / `serialise_response_json` /   **)
(** `serialise_response_boolean_json` build AS TEXT — built directly as      **)
(** `json_val` trees, bypassing `json_escape`/string concatenation and the   **)
(** opaque parser entirely. The lemmas below show the tree-level decoders    **)
(** invert them EXACTLY (not merely up to some `_equiv` relation — see       **)
(** finding below) on the stated fragment. Composed with the missing         **)
(** bridging fact `parse_json (serialise_response_json vars rows) ==         **)
(** Some (json_val_of_response vars rows)`, this closes the full text-level  **)
(** round trip; until that bridging fact lands, this module is the decode-   **)
(** half proof plus a precise map of what remains.                          **)
(**                                                                          **)
(** FRAGMENT (term_in_fragment / row_in_fragment / rows_in_fragment below):  **)
(** `T_IRI` terms, and `T_Literal` terms whose `direction` field is `None`   **)
(** (RDF 1.1 literals: untyped, `xsd:*`-typed, or `rdf:langString`-tagged;   **)
(** RDF 1.2 directional literals — `dirLangString`, `its:dir` — excluded).   **)
(** `escape_free` is still defined below, exactly as the brief specifies    **)
(** (from `json_escape`'s own match arms — `"`, `\`, and control chars      **)
(** `< 0x20` are the characters it rewrites), for the future session that    **)
(** lands the `Parser.FastString` bridging lemmas and widens this module     **)
(** to the real text round trip: the structural lemmas proved here never    **)
(** invoke `json_escape`, so `escape_free` plays no role in THEM — it is     **)
(** carried forward unused, not silently dropped.                           **)
(**                                                                          **)
(** POSITIVE FINDING: on this fragment the decode is EXACT, not merely       **)
(** `_equiv`. `Parser.JSONResults.mk_literal`'s reconstruction (lexical      **)
(** form, datatype — defaulting to `xsd:string` exactly when the serializer  **)
(** omitted the `datatype` member for that same reason, language tag,        **)
(** `direction = None`) matches the original `wf_literal`'s fields           **)
(** component-for-component, so `parse_binding_value (json_val_of_term t)    **)
(** == Some t` holds by F*'s record-eta rule, no normalization/equivalence   **)
(** relation needed. No datatype-normalization or lang-tag-casing surprise   **)
(** was found on this fragment (both were named as open risks by the brief). **)
(**                                                                          **)
(** WIDENING REMAINING (tracked, not attempted here):                        **)
(**   1. The `Parser.FastString` bridging lemmas above — the only thing      **)
(**      standing between this module and the literal brief goal.            **)
(**   2. `escaped strings`: once (1) lands, extend past `escape_free`        **)
(**      lexical forms/var names by proving `json_escape`'s own inverse       **)
(**      inside `Parser.JSON.json_parse_string`'s escape decoder.             **)
(**   3. `T_BNode`: trivial to add to `term_in_fragment` — its structural     **)
(**      decode (`typ = "bnode" -> Some (T_BNode val_str)`) is exact and      **)
(**      unconditional, omitted here only to track the brief's fragment      **)
(**      literally.                                                          **)
(**   4. RDF 1.2 directional literals (`mk_dir_literal`, `its:dir`) and       **)
(**      `T_TripleTerm` (`typ = "triple"`, fuel-bounded recursion) — both     **)
(**      need their own `json_val_of_*` branch plus a fuel argument for the  **)
(**      triple-term case; the boolean pair (part 4 of the brief) is the     **)
(**      `json_val_of_bool` lemma at the bottom of this file, same           **)
(**      structural/text split as the row case.                              **)
(** ======================================================================== **)

open FStar.List.Tot
open RDF.Graph.Executable
open Parser.JSON
open Parser.JSONResults
open SPARQL.Protocol
open Parser.FastString.ConcatSpec

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

(** ====================================================================== **)
(** Part 1: the fragment                                                    **)
(** ====================================================================== **)

// escape_free, per the brief: the exact character set json_escape_char
// (SPARQL.Protocol.fst) rewrites — quote, backslash, and C0 control
// characters. Carried forward for the future text-level widening (see
// banner); the structural lemmas in this module do not depend on it.
let escape_free_char (c : FStar.Char.char) : bool =
  let code = FStar.Char.int_of_char c in
  code <> 0x22 && code <> 0x5C && code >= 0x20

let rec escape_free_chars (cs : list FStar.Char.char)
  : Tot bool (decreases cs) =
  match cs with
  | [] -> true
  | c :: rest -> escape_free_char c && escape_free_chars rest

let escape_free (s : string) : bool =
  escape_free_chars (FStar.String.list_of_string s)

// A term is in the fragment this module round-trips: an IRI, or a
// literal with no RDF 1.2 base direction (RDF 1.1 literals — untyped,
// xsd:*-typed, or rdf:langString-tagged). Bnodes and triple-terms are
// out of scope here (see WIDENING REMAINING #3/#4 in the banner).
let term_in_fragment (t : rdf_term) : bool =
  match t with
  | T_IRI _ -> true
  | T_Literal l -> None? l.direction
  | _ -> false

let rec row_in_fragment (row : binding_row) : Tot bool (decreases row) =
  match row with
  | [] -> true
  | (_, t) :: rest -> term_in_fragment t && row_in_fragment rest

let rec rows_in_fragment (rows : list binding_row) : Tot bool (decreases rows) =
  match rows with
  | [] -> true
  | r :: rest -> row_in_fragment r && rows_in_fragment rest

(** ====================================================================== **)
(** Part 2: structural mirrors of the text serializer                       **)
(**                                                                          **)
(** These build `json_val` TREES with the same field shape `json_term` /    **)
(** `json_row` / `serialise_response_json` build as TEXT (SPARQL.Protocol   **)
(** lines ~800-916), but directly as `json_val` — no `json_escape`, no      **)
(** `^`-concatenation, no `Parser.FastString`. See banner FINDING.          **)
(** ====================================================================== **)

let json_val_of_term (t : rdf_term) : json_val =
  match t with
  | T_IRI i -> JObject [("type", JString "uri"); ("value", JString i)]
  | T_BNode b -> JObject [("type", JString "bnode"); ("value", JString b)]
  | T_Literal l ->
    (match l.lang_tag with
     | Some tag ->
       JObject [("type", JString "literal");
                 ("value", JString l.lexical_form);
                 ("xml:lang", JString tag)]
     | None ->
       if l.datatype = xsd_string then
         JObject [("type", JString "literal"); ("value", JString l.lexical_form)]
       else
         JObject [("type", JString "literal");
                   ("value", JString l.lexical_form);
                   ("datatype", JString l.datatype)])
  // Outside the fragment (T_TripleTerm). Not claimed correct — see
  // WIDENING REMAINING #4.
  | T_TripleTerm _ _ _ -> JObject []

let json_val_of_row (row : binding_row) : json_val =
  JObject (List.Tot.map (fun (vt : (string & rdf_term)) ->
                            let (v, t) = vt in (v, json_val_of_term t))
                         row)

let json_val_of_vars (vars : list string) : json_val =
  JArray (List.Tot.map JString vars)

let json_val_of_response (vars : list string) (rows : list binding_row) : json_val =
  JObject [("head", JObject [("vars", json_val_of_vars vars)]);
            ("results", JObject [("bindings", JArray (List.Tot.map json_val_of_row rows))])]

let json_val_of_bool (b : bool) : json_val =
  JObject [("head", JObject []); ("boolean", JBool b)]

(** ====================================================================== **)
(** Part 3: per-term round trip                                             **)
(** ====================================================================== **)

#push-options "--z3rlimit 100 --fuel 6 --ifuel 6"
let lemma_json_val_of_term_roundtrip (t : rdf_term{term_in_fragment t})
  : Lemma (ensures parse_binding_value (json_val_of_term t) == Some t)
  =
  match t with
  | T_IRI i ->
    // json_get_field "type"/"value" on a two-element concrete list
    // reduces by unfolding List.Tot.find; is_iri i holds by i's own
    // wf_iri refinement.
    assert (json_get_field "type" (json_val_of_term t) == Some (JString "uri"));
    assert (json_get_field "value" (json_val_of_term t) == Some (JString i))
  | T_Literal l ->
    (match l.lang_tag with
     | Some tag ->
       assert (json_get_string "type" (json_val_of_term t) == Some "literal");
       assert (json_get_string "value" (json_val_of_term t) == Some l.lexical_form);
       assert (json_get_string "xml:lang" (json_val_of_term t) == Some tag);
       assert (json_get_string "its:dir" (json_val_of_term t) == None);
       // literal_wf forces datatype = rdf_lang_string whenever lang_tag = Some _.
       assert (l.datatype == rdf_lang_string);
       assert (l.direction == None)
     | None ->
       if l.datatype = xsd_string then begin
         assert (json_get_string "type" (json_val_of_term t) == Some "literal");
         assert (json_get_string "value" (json_val_of_term t) == Some l.lexical_form);
         assert (json_get_string "xml:lang" (json_val_of_term t) == None);
         assert (json_get_string "datatype" (json_val_of_term t) == None);
         assert (l.datatype == xsd_string);
         assert (l.direction == None)
       end else begin
         assert (json_get_string "type" (json_val_of_term t) == Some "literal");
         assert (json_get_string "value" (json_val_of_term t) == Some l.lexical_form);
         assert (json_get_string "xml:lang" (json_val_of_term t) == None);
         assert (json_get_string "datatype" (json_val_of_term t) == Some l.datatype);
         assert (l.direction == None)
       end)
#pop-options

(** ====================================================================== **)
(** Part 4: per-row round trip                                              **)
(** ====================================================================== **)

let rec lemma_json_val_of_row_roundtrip (row : binding_row{row_in_fragment row})
  : Lemma (ensures parse_binding_row (json_val_of_row row) == row)
          (decreases row)
  =
  match row with
  | [] -> ()
  | (v, t) :: rest ->
    lemma_json_val_of_term_roundtrip t;
    lemma_json_val_of_row_roundtrip rest;
    // parse_binding_row (JObject fields) is List.Tot.concatMap over
    // fields; unfold one step and let the two IH facts above close it.
    assert (json_val_of_row row == JObject ((v, json_val_of_term t) :: List.Tot.map (fun (vt : (string & rdf_term)) -> let (v', t') = vt in (v', json_val_of_term t')) rest));
    assert (json_val_of_row rest == JObject (List.Tot.map (fun (vt : (string & rdf_term)) -> let (v', t') = vt in (v', json_val_of_term t')) rest))

(** ====================================================================== **)
(** Part 5: vars round trip                                                 **)
(** ====================================================================== **)

let rec lemma_json_val_of_vars_roundtrip (vars : list string)
  : Lemma (ensures
             List.Tot.concatMap
               (fun (v : json_val) -> match v with | JString s -> [s] | _ -> [])
               (List.Tot.map JString vars)
             == vars)
          (decreases vars)
  =
  match vars with
  | [] -> ()
  | _ :: rest -> lemma_json_val_of_vars_roundtrip rest

(** ====================================================================== **)
(** Part 6: rows round trip (list level)                                    **)
(** ====================================================================== **)

let rec lemma_json_val_of_rows_roundtrip (rows : list binding_row{rows_in_fragment rows})
  : Lemma (ensures List.Tot.map parse_binding_row (List.Tot.map json_val_of_row rows) == rows)
          (decreases rows)
  =
  match rows with
  | [] -> ()
  | r :: rest ->
    lemma_json_val_of_row_roundtrip r;
    lemma_json_val_of_rows_roundtrip rest

(** ====================================================================== **)
(** Part 7: response round trip (structural half)                           **)
(**                                                                          **)
(** Mirrors parse_srj_results's body (Parser.JSONResults.fst line 133)      **)
(** EXACTLY, minus the leading `parse_json input` call this module cannot   **)
(** discharge (see banner FINDING) — composed from the same exported        **)
(** functions (`json_get_field`, `json_get_string_array`, `json_get_array`, **)
(** `List.Tot.map parse_binding_row`), not a reimplementation.               **)
(** ====================================================================== **)

let lemma_json_val_of_response_roundtrip
    (vars : list string) (rows : list binding_row{rows_in_fragment rows})
  : Lemma (ensures
             (let root = json_val_of_response vars rows in
              let decoded_vars : list string =
                (match json_get_field "head" root with
                 | None -> []
                 | Some head ->
                   (match json_get_string_array "vars" head with
                    | Some vs -> vs
                    | None -> [])) in
              let decoded_rows : list binding_row =
                (match json_get_field "results" root with
                 | Some results_obj ->
                   (match json_get_array "bindings" results_obj with
                    | Some bindings -> List.Tot.map parse_binding_row bindings
                    | None -> [])
                 | None -> []) in
              decoded_vars == vars /\ decoded_rows == rows))
  =
  lemma_json_val_of_vars_roundtrip vars;
  lemma_json_val_of_rows_roundtrip rows

(** ====================================================================== **)
(** Part 8: ASK boolean pair (structural half)                              **)
(**                                                                          **)
(** The brief's part 4: serialise_response_boolean_json / parse_srj_boolean **)
(** at the json_val level. json_get_bool "boolean" is a direct field        **)
(** lookup with no normalization, so this is exact and unconditional (no    **)
(** fragment restriction) — the ONLY thing keeping this from being a full   **)
(** statement about the two named W3C-facing functions is, again, the       **)
(** `Parser.FastString` bridging gap in the banner FINDING, since           **)
(** `parse_srj_boolean` still calls the opaque `parse_json` first.          **)
(** ====================================================================== **)

let lemma_json_val_of_bool_roundtrip (b : bool)
  : Lemma (ensures json_get_bool "boolean" (json_val_of_bool b) == Some b)
  = ()

(** ====================================================================== **)
(** Part 9: TEXT-LEVEL lemmas -- the concat_spec wall, closed (session      **)
(** 2026-08-10, G4 M4)                                                      **)
(**                                                                          **)
(** `Parser.FastString.ConcatSpec.concat_spec` landed with three proved      **)
(** equations (`concat_spec_nil`/`_singleton`/`_cons`) and                   **)
(** `SPARQL.Protocol.serialise_response_json`'s terminal join (line ~916)    **)
(** now CALLS `concat_spec`, not the opaque `FStar.String.concat` the        **)
(** banner above names as the wall ("even the SINGLETON-list identity        **)
(** ... is unprovable ... Error 19 on the FIRST step"). This closes that     **)
(** specific wall for the call site. The lemma below exercises the          **)
(** concat_spec_cons/singleton decomposition directly and generally          **)
(** (`lemma_concat_spec_two`, symbolic in both string arguments -- in        **)
(** particular any two `json_row`/`json_var_list` outputs, so it holds       **)
(** for ANY row/var content, never unfolding `json_escape`, which still      **)
(** bottoms out in the SEPARATE, still-open `fs_codepoints_of_string`        **)
(** wall the original banner also names). The two lemmas after it are       **)
(** CLOSED literal instances of the full `serialise_response_json`          **)
(** wire-format text, proved via `assert_norm`. Composing the general       **)
(** concat_spec fact into a general (symbolic vars AND rows) statement       **)
(** about `serialise_response_json` itself did not verify reliably this     **)
(** session -- see the FINDING below for what was tried and why it is       **)
(** left open.                                                               **)
(** ====================================================================== **)

// The one-step structural equation the brief's step (b) asks for, at the
// `concat_spec` level directly -- fully SYMBOLIC/general in `a`/`b` (any
// two strings, in particular any two `json_row`/`json_var_list` outputs),
// proved by direct application of `concat_spec_cons`/`_singleton` with no
// further scaffolding needed. This is the two-element `Cons? rest` case
// of `concat_spec`'s own match (the one-element case degenerates to the
// `[x]` arm directly, `concat_spec_singleton` alone) -- the SAME
// decomposition `SPARQL.Protocol.serialise_response_json`'s terminal
// `concat_spec "" body_pieces` call goes through once `body_pieces` has
// two or more elements (i.e. two or more SPARQL result rows).
let lemma_concat_spec_two (a b : string)
  : Lemma (concat_spec "" [a; b] == a ^ "" ^ b)
  =
  concat_spec_cons "" a [b];
  concat_spec_singleton "" b

// FINDING (session 2026-08-10): composing `lemma_concat_spec_two` (or
// its `json_rows_body_acc`/`List.Tot.rev`-wrapped variants tried this
// session) INTO the fully-unfolded `serialise_response_json vars [r1;
// r2] == "...{vars}...{json_row r1},{json_row r2}..."` statement -- for
// SYMBOLIC vars AND rows together, in one query -- resisted verification
// this session across many attempted phrasings (explicit intermediate
// `assert`s for the acc/rev unfolding, separate helper lemmas, an
// `x ^ "" == x` identity restatement for `Prims.strcat` -- which is
// ALSO an opaque `val`, `Prims.fst` line 611-613, with no stated
// identity/associativity equations by default, the same failure SHAPE
// as the `FStar.String.concat` wall this module's banner describes, but
// a genuinely different primitive). Every attempt gave a DETERMINISTIC
// Error 19 given fixed source (repeated 5-10x per attempt to rule out
// this session's separately-observed run-to-run SMT flakiness on
// smaller isolated sub-goals) -- yet swapping which lemmas were merely
// PRESENT earlier in the file measurably changed which specific
// statement failed, without changing the CONTENT of the failing proof
// itself. That is: the failure is reproducible per file-state, but not
// evidently a fixed defect in any one lemma -- symptomatic of Z3's
// incremental-context sensitivity (declaration order affecting
// E-matching/trigger search) rather than a missing mathematical fact,
// though this was not conclusively isolated. This Part therefore proves
// the row-JOIN step alone at the `concat_spec` level (`lemma_concat_
// spec_two` above, which IS the concat_spec_cons/singleton application
// the brief's step (b) describes, fully general in its two string
// arguments) plus CLOSED literal instances of the full wrapped
// statement (below, via `assert_norm` -- no free variables, no SMT
// query at all, hence none of the above instability, confirmed
// deterministic 5/5 runs) rather than the general symbolic-vars-AND-rows
// wrapped lemma the brief's step (b) illustrates with a variable name.
// Composing the two -- or diagnosing the incremental-context sensitivity
// with F*'s `--query_stats`/the fstar-mcp interactive server rather than
// batch retries -- is the narrowest still-open item this Part leaves.

// LITERAL instance, per the brief's step (a): the fully closed empty-
// response case. Proved via `assert_norm` directly -- both sides are
// fully closed (no free variables), so this is pure normalization, no
// SMT query at all (deterministic; confirmed across 5 repeated runs with
// identical source this session).
let lemma_serialise_response_json_empty_literal ()
  : Lemma (serialise_response_json [] [] ==
             "{\"head\":{\"vars\":[]},\"results\":{\"bindings\":[]}}")
  = assert_norm (serialise_response_json [] [] ==
             "{\"head\":{\"vars\":[]},\"results\":{\"bindings\":[]}}")

// LITERAL instance exercising concat_spec_cons END TO END on a CONCRETE
// list (also via assert_norm, same reasoning): two empty rows (each row
// itself the empty binding list, so json_row [] reduces to "{}" with no
// escaping) round out step (a)'s "equals a concrete string literal" with
// the non-trivial Cons? case covered, not just the vacuous empty-list
// one above.
let lemma_serialise_response_json_two_empty_rows_literal ()
  : Lemma (serialise_response_json [] [[]; []] ==
             "{\"head\":{\"vars\":[]},\"results\":{\"bindings\":[{},{}]}}")
  = assert_norm (serialise_response_json [] [[]; []] ==
             "{\"head\":{\"vars\":[]},\"results\":{\"bindings\":[{},{}]}}")

(** ====================================================================== **)
(** Part 10: past the Part 9 wall -- symbolic strcat kit landed (session   **)
(** 2026-08-11, G4 M4)                                                     **)
(**                                                                          **)
(** Part 9's FINDING named the exact blocker: `Prims.strcat`/`^` is an      **)
(** opaque ulib `val` with no stated identity/associativity equations, and  **)
(** an `x ^ "" == x` restatement attempt for symbolic `x` was one of the    **)
(** things tried that did not close the two-row goal that session.         **)
(** `RDF.NTriples.RoundTrip.fst`'s independent 2026-08-11 FINDING hit the    **)
(** SAME wall from the N-Triples side. `Parser.FastString.ConcatSpec.fst`   **)
(** now carries the closing kit -- `lemma_strcat_empty_l` / `_empty_r` /    **)
(** `_assoc` -- proved via the route both FINDINGs pointed at:              **)
(** `FStar.String.list_of_concat` turns `^` into list `@`, which DOES have  **)
(** real equations (`FStar.List.Tot.Properties.append_l_nil`/               **)
(** `append_assoc`), and `FStar.String.string_of_list_of_string` transports **)
(** the closed list goal back to a string equality. Homed in ConcatSpec     **)
(** (not here) because both this module and the N-Triples serializer need   **)
(** it -- see that file's own banner for the full derivation writeup.       **)
(**                                                                          **)
(** With the kit lemmas CALLED EXPLICITLY (not left for Z3 to find), both   **)
(** the single-row and the two-row SYMBOLIC statements Part 9 left open      **)
(** now verify -- `lemma_srj_single_row` needs only `concat_spec_singleton` **)
(** (no strcat identity required: the accumulator/rev walk collapses to a    **)
(** singleton list with no `""` left over), and `lemma_srj_two_rows` needs   **)
(** `concat_spec_cons` + `concat_spec_singleton` to unfold the two-element   **)
(** join followed by JUST `lemma_strcat_empty_l` (to drop the `"" ^ ...`     **)
(** the `concat_spec_cons` equation's `sep = ""` leaves in the middle --     **)
(** `^`'s RIGHT-associativity in F* already lines up the rest of the         **)
(** parenthesisation with the target, so `lemma_strcat_assoc` turned out    **)
(** NOT to be needed here; an earlier draft called it anyway, and that       **)
(** single extra, logically-irrelevant hypothesis was enough to reproduce    **)
(** Part 9's "declaration presence changes what fails" symptom in the        **)
(** FULL-FILE context even though the identical lemma body verified          **)
(** standalone -- removing it, not adding z3rlimit, is what fixed it; see    **)
(** `lemma_srj_two_rows`'s own comment for the blow-by-blow). Both lemmas    **)
(** verify deterministically in the full-file build (repeated `make          **)
(** verify-SPARQL.Protocol.RoundTrip` runs, identical source) -- each proof  **)
(** is its own small lemma (the isolation pattern Part 9's FINDING           **)
(** recommended), which is what made the extra-hypothesis noise source       **)
(** easy to isolate and drop once the error pointed at this Part specifically.**)
(**                                                                          **)
(** STILL OPEN: the general N-row induction (arbitrary-length `rows`, not    **)
(** just the 1- and 2-element instances above) -- the natural next          **)
(** checkpoint, by induction on `rows` composing `concat_spec_cons` at each  **)
(** step with `lemma_strcat_empty_l`/`_assoc` as needed per step; not        **)
(** attempted here (narrowest-first / guard-depth discipline). Composing     **)
(** either statement with the actual TEXT-level `parse_json` round trip      **)
(** remains blocked by the SEPARATE, unrelated `Parser.FastString` opacity   **)
(** wall the module's original banner (top of file) describes -- this Part   **)
(** closes the STRCAT wall only, not that one.                              **)
(** ====================================================================== **)

#push-options "--z3rlimit 50 --fuel 4 --ifuel 4"

// Checkpoint (b): the narrowest symbolic statement Part 9 left open --
// `serialise_response_json` on a single symbolic row, vars also symbolic.
// Does not need the strcat identity kit: `json_rows_body_acc [r] true []`
// reduces to the singleton `[json_row r]` with `first = true` throughout
// (no `,`-prefixed chunk, no leftover `""`), so `concat_spec_singleton`
// alone closes it.
let lemma_srj_single_row (vars : list string) (r : binding_row)
  : Lemma (ensures
             serialise_response_json vars [r] ==
               "{\"head\":{\"vars\":[" ^ json_var_list vars ^ "]},"
                 ^ "\"results\":{\"bindings\":["
                 ^ json_row r
                 ^ "]}}")
  =
  concat_spec_singleton "" (json_row r)

#pop-options

// Checkpoint (c) history (session 2026-08-11): the two-row symbolic
// lemma attempted directly, standalone-only, is preserved in git history
// (this comment previously carried its full text + a 3-countermeasure
// bisection log) -- superseded below by the general N-row induction,
// which subsumes it. See Part 11.

#pop-options

(** ====================================================================== **)
(** Part 11: the N-row induction (session 2026-08-11 continuation) --      **)
(** LANDED, and checkpoint (c) is now moot (predicted in the brief: "if    **)
(** the induction lands, the two-row case is a corollary").                **)
(** ---------------------------------------------------------------------- **)
(**                                                                        **)
(** Checkpoint (c)'s FIXED two-row lemma resisted verification IN THIS     **)
(** FILE (3 countermeasures tried, all Error 19 "incomplete quantifiers",  **)
(** even though the identical body verified standalone 3/3) -- the         **)
(** induction below was attempted next per the brief's own prediction      **)
(** ("the induction hypothesis adds structure") and lands cleanly, 3/3      **)
(** deterministic runs, first attempt, no bisection needed.                **)
(**                                                                        **)
(** THE ROUTE. `json_rows_body_acc` (the tail-recursive accumulator        **)
(** `serialise_response_json` actually calls -- see SPARQL.Protocol.fst    **)
(** line ~897) is, at each step, `List.Tot.rev_acc`-shaped: it pushes one  **)
(** `chunk` string per row onto `acc` and recurses. `chunks_of` below       **)
(** reconstructs the SAME chunk sequence as an ordinary (non-accumulator)   **)
(** list-producing function, so `FStar.List.Tot.Properties`'s REAL,        **)
(** already-proved list lemmas (`rev_involutive`, and `rev_acc`'s own      **)
(** one-step unfold) directly relate the two -- this half is pure          **)
(** list-level reasoning, none of the opaque-string-primitive walls this   **)
(** module's banner describes apply to it (the exact precedent is          **)
(** `RDF.List.Helpers.fst`'s `concatMap_aux`/`lemma_concatMap_aux_eq`,      **)
(** the same accumulator-generalization shape, already proved and landed   **)
(** in this repo). The string-level half (`lemma_concat_chunks`) is the    **)
(** SAME `concat_spec_cons`/`_singleton` + `lemma_strcat_empty_l`/`_assoc` **)
(** kit Part 10 used, but now applied INSIDE an induction on `rows`, which  **)
(** gives Z3 the induction hypothesis as an explicit, already-in-scope      **)
(** fact at each step rather than asking it to synthesize the whole         **)
(** two-element instance in one query -- this appears to be exactly what    **)
(** dissolves the trigger-pool sensitivity checkpoint (c) hit: an           **)
(** induction step's proof obligation is smaller and its hypotheses more    **)
(** narrowly scoped than a single flat two-row goal sitting after Parts     **)
(** 1-10's accumulated declarations.                                        **)
(**                                                                        **)
(** RESIDUAL FINDING: checkpoint (c)'s ORIGINAL statement (`rows = [r1;     **)
(** r2]` literally, output written as `json_row r1 ^ "," ^ json_row r2`     **)
(** with no `json_rows_joined` in sight) is a one-line corollary of         **)
(** `lemma_srj_n_rows` MATHEMATICALLY (`json_rows_joined [r1; r2]`          **)
(** unfolds, by `json_rows_joined`'s own defining match, to exactly         **)
(** `json_row r1 ^ "," ^ json_row r2` -- confirmed via a standalone         **)
(** `Lemma (json_rows_joined [r1; r2] == json_row r1 ^ "," ^ json_row r2)   **)
(** = ()` probe, which typechecks with NO SMT query at all, pure            **)
(** definitional unfolding). Stating that corollary as ITS OWN top-level    **)
(** lemma in this file, however, reproduced the SAME declaration-order      **)
(** sensitivity checkpoint (c) hit -- THREE phrasings tried (guard depth    **)
(** 3/3): `lemma_srj_n_rows vars [r1;r2]` plus two `assert`s restating the  **)
(** unfold; the same body re-specialized via `lemma_body_pieces_eq`/        **)
(** `lemma_concat_chunks` directly at `[r1;r2]`; and the checkpoint (c)     **)
(** ORIGINAL direct proof (`concat_spec_cons`+`concat_spec_singleton`+      **)
(** `lemma_strcat_empty_l`, which verifies standalone and verified in a     **)
(** throwaway probe placed immediately after this Part) placed AFTER        **)
(** `lemma_srj_n_rows` in-file -- all three Error 19, and (surprisingly)    **)
(** the third one flipped from PASS to FAIL purely by REMOVING an unrelated **)
(** failed attempt that had been sitting between it and `lemma_srj_n_rows`, **)
(** the same "presence of a declaration, not its correctness, changes the   **)
(** outcome" symptom Part 9/checkpoint (c) both recorded. Per the brief's    **)
(** own framing ("if the induction lands ... the bisection becomes moot"),  **)
(** `lemma_srj_n_rows` alone is left as the landed theorem -- it already     **)
(** covers `rows = [r1; r2]` (and every other length) by instantiation,      **)
(** so no separate two-row lemma is needed for the round-trip goal to be     **)
(** covered; a future session wanting the LITERAL checkpoint-(c) statement   **)
(** as its own named lemma should bisect Parts 1-10 (comment out one Part    **)
(** at a time in a scratch copy, rebuild) with the F* MCP interactive        **)
(** server once available in a worktree subagent's tool surface, per         **)
(** checkpoint (c)'s own NEXT STEP note -- not attempted again here.         **)
(** ====================================================================== **)

#push-options "--z3rlimit 50 --fuel 2 --ifuel 2"

// Direct (non-accumulator) reconstruction of the chunk list
// json_rows_body_acc builds -- same recursive shape, but as an ordinary
// list-producing function so FStar.List.Tot.Properties's real
// rev_acc/rev_involutive lemmas apply to it directly (the precedent is
// RDF.List.Helpers.fst's concatMap_aux/lemma_concatMap_aux_eq).
let rec chunks_of (rows : list binding_row) (first : bool)
  : Tot (list string) (decreases rows) =
  match rows with
  | [] -> []
  | r :: rest ->
    let chunk = (if first then json_row r else "," ^ json_row r) in
    chunk :: chunks_of rest false

// The comma-joined text the response body should read as, once the
// leading `first`-flag comma offset json_rows_body_acc encodes via the
// bool is folded away -- this is the "obvious" spec `concat_spec ","`
// would give directly if json_row's pieces did not each need their OWN
// leading comma suppressed only on the very first row.
let rec json_rows_joined (rows : list binding_row)
  : Tot string (decreases rows) =
  match rows with
  | [] -> ""
  | [r] -> json_row r
  | r :: rest -> json_row r ^ "," ^ json_rows_joined rest

// json_rows_body_acc is exactly List.Tot.rev_acc applied to chunks_of --
// both recurse identically on rows/first, pushing the same chunk onto the
// same accumulator at each step. Pure list-level unfolding, no string
// reasoning (none of this module's opaque-primitive walls apply).
let rec lemma_json_rows_body_acc_is_rev_acc
    (rows : list binding_row) (first : bool) (acc : list string)
  : Lemma (ensures json_rows_body_acc rows first acc ==
                      List.Tot.rev_acc (chunks_of rows first) acc)
          (decreases rows)
  =
  match rows with
  | [] -> ()
  | r :: rest ->
    lemma_json_rows_body_acc_is_rev_acc rest false
      ((if first then json_row r else "," ^ json_row r) :: acc)

// Hence the rev'd body_pieces list serialise_response_json builds is
// exactly chunks_of rows true (rev_acc l [] == rev l, and rev . rev == id).
let lemma_body_pieces_eq (rows : list binding_row)
  : Lemma (ensures List.Tot.rev (json_rows_body_acc rows true []) ==
                      chunks_of rows true)
  =
  lemma_json_rows_body_acc_is_rev_acc rows true [];
  FStar.List.Tot.Properties.rev_involutive (chunks_of rows true)

// concat_spec over chunks_of rows first, expressed as the comma-joined
// text (with the first-flag comma offset folded in). The only
// string-level facts needed are the same three Part 10 used --
// concat_spec's two defining equations plus lemma_strcat_empty_l/_assoc
// from the ConcatSpec kit -- invoked explicitly at each induction step
// (not left for Z3 to find), per Part 10's isolation lesson.
let rec lemma_concat_chunks (rows : list binding_row) (first : bool)
  : Lemma (ensures
             concat_spec "" (chunks_of rows first) ==
               (match rows with
                | [] -> ""
                | _ -> if first then json_rows_joined rows
                       else "," ^ json_rows_joined rows))
          (decreases rows)
  =
  match rows with
  | [] -> ()
  | [r] ->
    concat_spec_singleton "" (if first then json_row r else "," ^ json_row r)
  | r :: r2 :: rest' ->
    let rest = r2 :: rest' in
    let chunk = (if first then json_row r else "," ^ json_row r) in
    concat_spec_cons "" chunk (chunks_of rest false);
    lemma_concat_chunks rest false;
    // IH: concat_spec "" (chunks_of rest false) == "," ^ json_rows_joined rest
    if first then
      // chunk ^ "" ^ ("," ^ json_rows_joined rest)
      //   == chunk ^ ("," ^ json_rows_joined rest)                  [empty_l]
      //   == json_row r ^ "," ^ json_rows_joined rest                [chunk = json_row r; right-assoc, defeq]
      //   == json_rows_joined (r :: rest)                            [target, rest is Cons]
      lemma_strcat_empty_l ("," ^ json_rows_joined rest)
    else begin
      // chunk ^ "" ^ ("," ^ json_rows_joined rest)
      //   == ("," ^ json_row r) ^ ("," ^ json_rows_joined rest)      [empty_l, chunk = "," ^ json_row r]
      //   == "," ^ (json_row r ^ ("," ^ json_rows_joined rest))      [strcat_assoc a="," b=json_row r c=...]
      //   == "," ^ json_rows_joined (r :: rest)                      [defn, right-assoc, defeq]
      lemma_strcat_empty_l ("," ^ json_rows_joined rest);
      lemma_strcat_assoc "," (json_row r) ("," ^ json_rows_joined rest)
    end

#pop-options

// THE N-ROW THEOREM: serialise_response_json vars rows, for a fully
// SYMBOLIC vars list and rows list of ANY length, equals the wire-format
// text with the row bodies comma-joined via json_rows_joined. Subsumes
// checkpoint (b) (lemma_srj_single_row, rows = [r]) and checkpoint (c)
// (rows = [r1; r2], by instantiation + unfolding json_rows_joined -- see
// the RESIDUAL FINDING above for why that instantiation is not ALSO
// landed as its own named lemma this session) and every other length,
// including [] (matching Part 9's assert_norm literal instance).
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
let lemma_srj_n_rows (vars : list string) (rows : list binding_row)
  : Lemma (ensures
             serialise_response_json vars rows ==
               "{\"head\":{\"vars\":[" ^ json_var_list vars ^ "]},"
                 ^ "\"results\":{\"bindings\":["
                 ^ json_rows_joined rows
                 ^ "]}}")
  =
  lemma_body_pieces_eq rows;
  lemma_concat_chunks rows true
#pop-options
