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
(** be attempted without it. Two candidate facts are recorded, WITH exact   **)
(** signatures and realisation-justification sketches, in                   **)
(** `Parser.FastString.Axioms.fsti`'s "STILL MISSING" note (its `fact 7`     **)
(** and `fact 8`) -- NOT added there per DO-NOT-WIDEN; each needs the same   **)
(** line-by-line check against `89_fast_string_primitives.sh` the existing   **)
(** six got before either may land. Until one or both land, this module's   **)
(** structural half (below) is the full extent of what's provable.          **)
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

#pop-options
