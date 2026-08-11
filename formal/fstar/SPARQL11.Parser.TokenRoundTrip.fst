module SPARQL11.Parser.TokenRoundTrip

/// Round-trip theorem for the SPARQL 1.1 tokenizer (`SPARQL11.Parser.fst`):
/// printing a token list from a defined fragment and re-tokenizing it
/// recovers the original list (plus the tokenizer's own trailing
/// `Tok_EOF` sentinel).
///
/// PROOF-ONLY MODULE. Not wired into `build-ocaml.sh` — nothing here is
/// extracted; it is a standalone verification target
/// (`make SPARQL11.Parser.TokenRoundTrip.fst.checked`), same pattern as
/// `RDF.Indexed.StringOrder.fsti`. `make verify` picks it up automatically
/// because that target derives its module list from `$(wildcard *.fst)`
/// (Makefile header, issue #319) — no manual wiring needed for that,
/// only `build-ocaml.sh`'s extraction module list is deliberately left
/// untouched.
///
/// FRAGMENT (this landing). `token_in_fragment` covers the single-char
/// delimiter tokens (braces/parens/brackets/dot/semi/comma), the
/// single- and two-char operator tokens (`* / | ^ ! ? + - = != < <= > >=
/// && || ^^`), disambiguated exactly as the real lexer does (a
/// terminating space after the candidate rules out any longer lexeme —
/// see `next_token_lt_pre`/`next_token_bang_pre`/etc. below). This is
/// narrower than the eventual target (payload-free keyword tokens are
/// NOT yet in `token_in_fragment` — see FINDING below); it is the
/// fragment that verified within the session's attempt budget. `Tok_VAR`
/// and `Tok_IRI` (the payload-carrying widenings named in the task
/// brief) are also not yet included.
///
/// FINDING (keyword-token widening not attempted this landing). Adding
/// payload-free keywords (`Tok_SELECT`, `Tok_WHERE`, `Tok_A`, ...) needs
/// a DIFFERENT print/round-trip argument than the delimiter fragment:
/// the lexer reaches those tokens via `scan_word` + `keyword_of_word`
/// (an uppercase string-match table, `SPARQL11.Parser.fst` ~line 594),
/// not via single/double-character lookahead, so the combinator lemmas
/// below (`next_token_<x>_pre`, all closed by `peek_at_offset` /
/// `peek_at_space` at fixed small offsets) do not transfer — a keyword
/// widening needs its own `next_token_<KW>_pre` per keyword built on
/// `scan_word`/`streq` reasoning instead, which is a different (and
/// per-keyword, ~40-way) case analysis. Left for a follow-up commit
/// rather than risked against this landing's attempt budget (per the
/// "narrow lands, wide stalls" instruction — the first attempt at this
/// module burned 4+ hours without landing anything).
///
/// FUEL. `tokenize_loop`'s `fuel` parameter is decreasing-only ballast
/// against non-termination and never inspected for correctness content:
/// every recursive call either returns immediately (`fuel = 0`) or
/// strictly decrements `fuel` on strict lexer progress (`p' > p`,
/// `SPARQL11.Parser.fst` :1084-1096). `tokenize_roundtrip_fragment`
/// below supplies `String.length (print_tokens ts) + 1` fuel (the same
/// formula `tokenize` itself uses), and `print_tokens_length_bound`
/// shows that is always `> List.Tot.length ts` — so no separate "fuel
/// hypothesis" is threaded through the induction; strict progress alone
/// carries it.
///
/// CHARACTER OPS. All string reasoning below (`String.index`,
/// `String.length`, `^`) goes through real `FStar.String` ulib
/// primitives — `FStar.String.concat_length`, `FStar.String.
/// list_of_concat`, `FStar.String.index_list_of_string` — proved once
/// against strings, not against a project-local string encoding. The
/// FastString split-brained-primitive trap (`fstar-module-style` skill,
/// extraction-semantics traps) is about OCaml-side string libraries
/// disagreeing with F*'s model after extraction; it does not apply here
/// because this module never extracts (no `--codegen`, not in
/// `build-ocaml.sh`) and the reasoning is entirely at the F* ulib
/// specification level.
///
/// CANONICAL, NOT TEXTUAL, RECOVERY. The theorem recovers the token
/// LIST, not the original source text: SPARQL keyword lexing is
/// case-folding (`SPARQL11.Parser.fst` `keyword_of_word` uppercases
/// before matching), so two different input spellings of the same
/// keyword print to the same canonical token and there is no text-level
/// round trip to claim. None of the tokens in this landing's fragment
/// are case-folded (they carry no letters), so the distinction is moot
/// here, but it is deliberate and will matter once keyword tokens are
/// added.

open FStar.String
open FStar.List.Tot
open SPARQL11.Parser
open Parser.FastString
open Parser.FastString.Axioms
open Parser.FastString.RoundTripLemmas

// Local shorthand matching `Parser.FastString.RoundTripLemmas.all_ascii`'s
// shape but as a predicate directly on `string` (that module's `all_ascii`
// is on `list FStar.Char.char`) -- task #52 migration (SPARQL 1.1 lexer's
// `substring`/`peek_char`/`at_end` off `FStar.String.sub`/`index`/`length`
// onto `Parser.FastString`'s byte primitives; docs/designissues/
// 2026-08-10-string-foundation-decision.md gap 1, owner decision "1: A"
// 2026-08-11). Every string this fragment's `print_token`/`print_tokens`
// produces is ASCII (delimiter/operator lexemes plus the `" "` separator),
// so the bridging facts below always apply to this module's own pre/txt/
// tail pieces -- but `peek_char`/`at_end` are now byte-indexed, and
// `FStar.String.index`/`length` stay codepoint-indexed, so every place this
// file used to get `peek_char ... == String.index ...` "for free" (same
// primitive, no bridge needed) now needs an explicit ASCII hypothesis and
// an explicit call into `Parser.FastString.RoundTripLemmas`'s bridge.
let ascii_string (s : string) : bool = all_ascii (FStar.String.list_of_string s)

(* ============================================================ *)
(* Generic string-indexing glue *)
(* ============================================================ *)

val index_append (#a:Type) (l1 l2 : list a) (i:nat{i < List.Tot.length l1 + List.Tot.length l2})
  : Lemma (ensures
      (if i < List.Tot.length l1
       then List.Tot.index (l1 @ l2) i == List.Tot.index l1 i
       else List.Tot.index (l1 @ l2) i == List.Tot.index l2 (i - List.Tot.length l1)))
    (decreases l1)
let rec index_append #a l1 l2 i =
  match l1 with
  | [] -> ()
  | x :: xs ->
    if i = 0 then ()
    else index_append xs l2 (i - 1)

val index_concat_at (s1 s2 : string) (i : nat{i < String.length (s1 ^ s2)})
  : Lemma (requires True)
          (ensures
      (FStar.String.concat_length s1 s2;
       if i < String.length s1
       then String.index (s1 ^ s2) i == String.index s1 i
       else i < String.length s1 + String.length s2 /\
            String.index (s1 ^ s2) i == String.index s2 (i - String.length s1)))
let index_concat_at s1 s2 i =
  FStar.String.list_of_concat s1 s2;
  FStar.String.concat_length s1 s2;
  index_append (String.list_of_string s1) (String.list_of_string s2) i;
  FStar.String.index_list_of_string (s1 ^ s2) i;
  if i < String.length s1
  then FStar.String.index_list_of_string s1 i
  else FStar.String.index_list_of_string s2 (i - String.length s1)

// Ascii-preservation under `@`/`^` -- task #52. Needed because `pre`/`mid`/
// `tail`/`txt` are reasoned about jointly (`peek_char`/`at_end` see the
// WHOLE concatenated string, not the individual piece), so every piece's
// individual `ascii_string` hypothesis needs to combine into one covering
// the concatenation before `lemma_ascii_string_byte_length`/`_byte_at` (on
// the WHOLE string) can be invoked.
val all_ascii_append (cs1 cs2 : list FStar.Char.char)
  : Lemma (requires all_ascii cs1 /\ all_ascii cs2)
          (ensures all_ascii (cs1 @ cs2))
let rec all_ascii_append cs1 cs2 =
  match cs1 with
  | [] -> ()
  | c :: rest -> all_ascii_append rest cs2

val ascii_string_concat (s1 s2 : string)
  : Lemma (requires ascii_string s1 /\ ascii_string s2)
          (ensures ascii_string (s1 ^ s2))
let ascii_string_concat s1 s2 =
  FStar.String.list_of_concat s1 s2;
  all_ascii_append (FStar.String.list_of_string s1) (FStar.String.list_of_string s2)

(* Generic: character at offset k within txt, inside pre^(txt^(" "^tail)) *)
val peek_at_offset (pre txt tail : string) (k : nat{k < String.length txt})
  : Lemma (requires ascii_string pre /\ ascii_string txt /\ ascii_string tail)
          (ensures
      (FStar.String.concat_length txt (" " ^ tail);
       FStar.String.concat_length pre (txt ^ (" " ^ tail));
       not (at_end (pre ^ (txt ^ (" " ^ tail))) (String.length pre + k)) /\
       peek_char (pre ^ (txt ^ (" " ^ tail))) (String.length pre + k) == String.index txt k))
let peek_at_offset pre txt tail k =
  let mid = txt ^ (" " ^ tail) in
  FStar.String.concat_length txt (" " ^ tail);
  FStar.String.concat_length pre mid;
  assert_norm (String.length " " == 1);
  assert_norm (ascii_string " ");
  FStar.String.concat_length " " tail;
  assert (String.length mid >= String.length txt);
  assert (String.length pre + k < String.length (pre ^ mid));
  index_concat_at pre mid (String.length pre + k);
  index_concat_at txt (" " ^ tail) k;
  // -- byte-level bridge (task #52): everything above is the ORIGINAL,
  // still-valid FStar.String-level reasoning; the new part is relating
  // `peek_char`/`at_end` (now fs_byte_*-backed) to it via `ascii_string`.
  assert_norm (ascii_string " ");
  ascii_string_concat " " tail;
  ascii_string_concat txt (" " ^ tail);
  ascii_string_concat pre mid;
  lemma_ascii_string_byte_length (pre ^ mid);
  assert (fs_byte_length (pre ^ mid) == String.length (pre ^ mid));
  assert (not (at_end (pre ^ mid) (String.length pre + k)));
  lemma_ascii_string_byte_length pre;
  lemma_ascii_string_byte_length mid;
  lemma_ascii_string_byte_length txt;
  fs_byte_at_concat pre mid (String.length pre + k);
  assert (fs_byte_at (pre ^ mid) (String.length pre + k) == fs_byte_at mid k);
  fs_byte_at_concat txt (" " ^ tail) k;
  assert (fs_byte_at mid k == fs_byte_at txt k);
  lemma_ascii_string_byte_index txt k;
  fs_byte_index_eq (pre ^ mid) (String.length pre + k);
  fs_byte_index_eq txt k;
  assert (peek_char (pre ^ mid) (String.length pre + k) == fs_byte_index (pre ^ mid) (String.length pre + k));
  assert (fs_byte_index (pre ^ mid) (String.length pre + k) == FStar.Char.char_of_int (fs_byte_at (pre ^ mid) (String.length pre + k)));
  assert (FStar.Char.char_of_int (fs_byte_at (pre ^ mid) (String.length pre + k)) == FStar.Char.char_of_int (fs_byte_at txt k));
  assert (FStar.Char.char_of_int (fs_byte_at txt k) == fs_byte_index txt k);
  assert (fs_byte_index txt k == String.index txt k)

(* Generic: the separator space right after txt *)
val peek_at_space (pre txt tail : string)
  : Lemma (requires ascii_string pre /\ ascii_string txt /\ ascii_string tail)
          (ensures
      (FStar.String.concat_length txt (" " ^ tail);
       FStar.String.concat_length pre (txt ^ (" " ^ tail));
       not (at_end (pre ^ (txt ^ (" " ^ tail))) (String.length pre + String.length txt)) /\
       peek_char (pre ^ (txt ^ (" " ^ tail))) (String.length pre + String.length txt) == FStar.Char.char_of_int 0x20))
let peek_at_space pre txt tail =
  let mid = txt ^ (" " ^ tail) in
  FStar.String.concat_length txt (" " ^ tail);
  FStar.String.concat_length pre mid;
  assert_norm (String.length " " == 1);
  assert_norm (ascii_string " ");
  FStar.String.concat_length " " tail;
  assert (String.length mid == String.length txt + 1 + String.length tail);
  assert (String.length pre + String.length txt < String.length (pre ^ mid));
  index_concat_at pre mid (String.length pre + String.length txt);
  index_concat_at txt (" " ^ tail) (String.length txt);
  assert_norm (String.length " " == 1);
  assert_norm (ascii_string " ");
  index_concat_at " " tail 0;
  assert_norm (String.index " " 0 == FStar.Char.char_of_int 0x20);
  // -- byte-level bridge (task #52), same shape as peek_at_offset above --
  assert_norm (ascii_string " ");
  ascii_string_concat " " tail;
  ascii_string_concat txt (" " ^ tail);
  ascii_string_concat pre mid;
  lemma_ascii_string_byte_length (pre ^ mid);
  assert (not (at_end (pre ^ mid) (String.length pre + String.length txt)));
  lemma_ascii_string_byte_length pre;
  lemma_ascii_string_byte_length mid;
  lemma_ascii_string_byte_length txt;
  fs_byte_at_concat pre mid (String.length pre + String.length txt);
  assert (fs_byte_at (pre ^ mid) (String.length pre + String.length txt) == fs_byte_at mid (String.length txt));
  fs_byte_at_concat txt (" " ^ tail) (String.length txt);
  assert (fs_byte_at mid (String.length txt) == fs_byte_at (" " ^ tail) 0);
  lemma_ascii_string_byte_length (" " ^ tail);
  lemma_ascii_string_byte_length " ";
  fs_byte_at_concat " " tail 0;
  assert (fs_byte_at (" " ^ tail) 0 == fs_byte_at " " 0);
  lemma_ascii_string_byte_index " " 0;
  fs_byte_index_eq (pre ^ mid) (String.length pre + String.length txt);
  fs_byte_index_eq " " 0;
  assert (peek_char (pre ^ mid) (String.length pre + String.length txt)
          == fs_byte_index (pre ^ mid) (String.length pre + String.length txt));
  assert (fs_byte_index (pre ^ mid) (String.length pre + String.length txt)
          == FStar.Char.char_of_int (fs_byte_at " " 0));
  assert (FStar.Char.char_of_int (fs_byte_at " " 0) == fs_byte_index " " 0);
  assert (fs_byte_index " " 0 == String.index " " 0)

(* ============================================================ *)
(* Per-token `next_token` recognition lemmas, fragment members *)
(* ============================================================ *)

(* --- LE : "<=" --- *)
#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_le_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("<=" ^ (" " ^ tail))) (String.length pre) == (Tok_LE, String.length pre + 2))
let next_token_le_pre pre tail =
  assert_norm (String.length "<=" == 2);
  assert_norm (ascii_string "<=");
  peek_at_offset pre "<=" tail 0;
  peek_at_offset pre "<=" tail 1;
  assert_norm (String.index "<=" 0 == FStar.Char.char_of_int 0x3C);
  assert_norm (String.index "<=" 1 == FStar.Char.char_of_int 0x3D)
#pop-options

(* --- AND : "&&" (unconditional, doesn't inspect 2nd char's value) --- *)
#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_and_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("&&" ^ (" " ^ tail))) (String.length pre) == (Tok_AND, String.length pre + 2))
let next_token_and_pre pre tail =
  assert_norm (String.length "&&" == 2);
  assert_norm (ascii_string "&&");
  peek_at_offset pre "&&" tail 0;
  assert_norm (String.index "&&" 0 == FStar.Char.char_of_int 0x26)
#pop-options

(* --- QMARK : "?" (scan_var_name consumes zero chars; substring len=0
   short-circuits without calling the opaque String.sub) --- *)
val var_chars_end_stop (input:string) (q:pos)
  : Lemma
      (requires not (at_end input q) /\ peek_char input q == FStar.Char.char_of_int 0x20)
      (ensures scan_var_chars_end input q == q)
let var_chars_end_stop input q = ()

val var_name_empty (input:string) (q:pos)
  : Lemma
      (requires scan_var_chars_end input q == q)
      (ensures scan_var_name input q == ("", q))
let var_name_empty input q = ()

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_qmark_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("?" ^ (" " ^ tail))) (String.length pre) == (Tok_QMARK, String.length pre + 1))
let next_token_qmark_pre pre tail =
  let full = pre ^ ("?" ^ (" " ^ tail)) in
  assert_norm (String.length "?" == 1);
  assert_norm (ascii_string "?");
  peek_at_offset pre "?" tail 0;
  assert_norm (String.index "?" 0 == FStar.Char.char_of_int 0x3F);
  peek_at_space pre "?" tail;
  let q = String.length pre + 1 in
  var_chars_end_stop full q;
  var_name_empty full q;
  assert (scan_var_name full q == ("", q));
  assert (fst (scan_var_name full q) == "");
  assert (snd (scan_var_name full q) == q);
  assert_norm (String.length "" == 0);
  assert_norm (ascii_string "");
  assert (String.length (fst (scan_var_name full q)) == 0)
#pop-options

(* --- LT : "<" -- the disambiguation case. Needs the separator space to
   fail every IRI-start / LE test so next_token falls through to Tok_LT. --- *)
#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_lt_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("<" ^ (" " ^ tail))) (String.length pre) == (Tok_LT, String.length pre + 1))
let next_token_lt_pre pre tail =
  assert_norm (String.length "<" == 1);
  assert_norm (ascii_string "<");
  peek_at_offset pre "<" tail 0;
  assert_norm (String.index "<" 0 == FStar.Char.char_of_int 0x3C);
  peek_at_space pre "<" tail
#pop-options

(* pre-generalized dot test *)
#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_dot_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("." ^ (" " ^ tail))) (String.length pre) == (Tok_DOT, String.length pre + 1))
let next_token_dot_pre pre tail =
  // Was direct `index_concat_at`-only (String-level, pre-task-#52) --
  // now routed through `peek_at_offset` like every other single-char
  // lemma, since `peek_char`/`at_end` need the fs_byte_* bridge that
  // lives inside `peek_at_offset`'s own proof (see that lemma's body).
  assert_norm (String.length "." == 1);
  assert_norm (ascii_string ".");
  peek_at_offset pre "." tail 0;
  assert_norm (String.index "." 0 == FStar.Char.char_of_int 0x2E)
#pop-options

(* ==== Helper A: single char, no lookahead ==== *)
#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_lbrace_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("{" ^ (" " ^ tail))) (String.length pre) == (Tok_LBRACE, String.length pre + 1))
let next_token_lbrace_pre pre tail =
  assert_norm (String.length "{" == 1);
  assert_norm (ascii_string "{");
  peek_at_offset pre "{" tail 0;
  assert_norm (String.index "{" 0 == FStar.Char.char_of_int 0x7B)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_rbrace_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("}" ^ (" " ^ tail))) (String.length pre) == (Tok_RBRACE, String.length pre + 1))
let next_token_rbrace_pre pre tail =
  assert_norm (String.length "}" == 1);
  assert_norm (ascii_string "}");
  peek_at_offset pre "}" tail 0;
  assert_norm (String.index "}" 0 == FStar.Char.char_of_int 0x7D)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_lparen_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("(" ^ (" " ^ tail))) (String.length pre) == (Tok_LPAREN, String.length pre + 1))
let next_token_lparen_pre pre tail =
  assert_norm (String.length "(" == 1);
  assert_norm (ascii_string "(");
  peek_at_offset pre "(" tail 0;
  assert_norm (String.index "(" 0 == FStar.Char.char_of_int 0x28)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_rparen_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ (")" ^ (" " ^ tail))) (String.length pre) == (Tok_RPAREN, String.length pre + 1))
let next_token_rparen_pre pre tail =
  assert_norm (String.length ")" == 1);
  assert_norm (ascii_string ")");
  peek_at_offset pre ")" tail 0;
  assert_norm (String.index ")" 0 == FStar.Char.char_of_int 0x29)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_lbracket_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("[" ^ (" " ^ tail))) (String.length pre) == (Tok_LBRACKET, String.length pre + 1))
let next_token_lbracket_pre pre tail =
  assert_norm (String.length "[" == 1);
  assert_norm (ascii_string "[");
  peek_at_offset pre "[" tail 0;
  assert_norm (String.index "[" 0 == FStar.Char.char_of_int 0x5B)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_rbracket_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("]" ^ (" " ^ tail))) (String.length pre) == (Tok_RBRACKET, String.length pre + 1))
let next_token_rbracket_pre pre tail =
  assert_norm (String.length "]" == 1);
  assert_norm (ascii_string "]");
  peek_at_offset pre "]" tail 0;
  assert_norm (String.index "]" 0 == FStar.Char.char_of_int 0x5D)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_semi_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ (";" ^ (" " ^ tail))) (String.length pre) == (Tok_SEMI, String.length pre + 1))
let next_token_semi_pre pre tail =
  assert_norm (String.length ";" == 1);
  assert_norm (ascii_string ";");
  peek_at_offset pre ";" tail 0;
  assert_norm (String.index ";" 0 == FStar.Char.char_of_int 0x3B)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_comma_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("," ^ (" " ^ tail))) (String.length pre) == (Tok_COMMA, String.length pre + 1))
let next_token_comma_pre pre tail =
  assert_norm (String.length "," == 1);
  assert_norm (ascii_string ",");
  peek_at_offset pre "," tail 0;
  assert_norm (String.index "," 0 == FStar.Char.char_of_int 0x2C)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_star_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("*" ^ (" " ^ tail))) (String.length pre) == (Tok_STAR, String.length pre + 1))
let next_token_star_pre pre tail =
  assert_norm (String.length "*" == 1);
  assert_norm (ascii_string "*");
  peek_at_offset pre "*" tail 0;
  assert_norm (String.index "*" 0 == FStar.Char.char_of_int 0x2A)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_slash_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("/" ^ (" " ^ tail))) (String.length pre) == (Tok_SLASH, String.length pre + 1))
let next_token_slash_pre pre tail =
  assert_norm (String.length "/" == 1);
  assert_norm (ascii_string "/");
  peek_at_offset pre "/" tail 0;
  assert_norm (String.index "/" 0 == FStar.Char.char_of_int 0x2F)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_eq_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("=" ^ (" " ^ tail))) (String.length pre) == (Tok_EQ, String.length pre + 1))
let next_token_eq_pre pre tail =
  assert_norm (String.length "=" == 1);
  assert_norm (ascii_string "=");
  peek_at_offset pre "=" tail 0;
  assert_norm (String.index "=" 0 == FStar.Char.char_of_int 0x3D)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_plus_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("+" ^ (" " ^ tail))) (String.length pre) == (Tok_PLUS, String.length pre + 1))
let next_token_plus_pre pre tail =
  assert_norm (String.length "+" == 1);
  assert_norm (ascii_string "+");
  peek_at_offset pre "+" tail 0;
  assert_norm (String.index "+" 0 == FStar.Char.char_of_int 0x2B)
#pop-options

#push-options "--z3rlimit 600 --fuel 4 --ifuel 4"
val next_token_minus_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("-" ^ (" " ^ tail))) (String.length pre) == (Tok_MINUS_OP, String.length pre + 1))
let next_token_minus_pre pre tail =
  assert_norm (String.length "-" == 1);
  assert_norm (ascii_string "-");
  peek_at_offset pre "-" tail 0;
  assert_norm (String.index "-" 0 == FStar.Char.char_of_int 0x2D)
#pop-options

(* ==== Helper B: single char, lookahead rules out the 2-char form ==== *)
#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_bang_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("!" ^ (" " ^ tail))) (String.length pre) == (Tok_BANG, String.length pre + 1))
let next_token_bang_pre pre tail =
  assert_norm (String.length "!" == 1);
  assert_norm (ascii_string "!");
  peek_at_offset pre "!" tail 0;
  assert_norm (String.index "!" 0 == FStar.Char.char_of_int 0x21);
  peek_at_space pre "!" tail
#pop-options

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_caret_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("^" ^ (" " ^ tail))) (String.length pre) == (Tok_CARET, String.length pre + 1))
let next_token_caret_pre pre tail =
  assert_norm (String.length "^" == 1);
  assert_norm (ascii_string "^");
  peek_at_offset pre "^" tail 0;
  assert_norm (String.index "^" 0 == FStar.Char.char_of_int 0x5E);
  peek_at_space pre "^" tail
#pop-options

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_pipe_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("|" ^ (" " ^ tail))) (String.length pre) == (Tok_PIPE, String.length pre + 1))
let next_token_pipe_pre pre tail =
  assert_norm (String.length "|" == 1);
  assert_norm (ascii_string "|");
  peek_at_offset pre "|" tail 0;
  assert_norm (String.index "|" 0 == FStar.Char.char_of_int 0x7C);
  peek_at_space pre "|" tail
#pop-options

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_gt_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ (">" ^ (" " ^ tail))) (String.length pre) == (Tok_GT, String.length pre + 1))
let next_token_gt_pre pre tail =
  assert_norm (String.length ">" == 1);
  assert_norm (ascii_string ">");
  peek_at_offset pre ">" tail 0;
  assert_norm (String.index ">" 0 == FStar.Char.char_of_int 0x3E);
  peek_at_space pre ">" tail
#pop-options

(* ==== Helper D: 2-char literal, 2nd char confirms the double form ==== *)
#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_ge_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ (">=" ^ (" " ^ tail))) (String.length pre) == (Tok_GE, String.length pre + 2))
let next_token_ge_pre pre tail =
  assert_norm (String.length ">=" == 2);
  assert_norm (ascii_string ">=");
  peek_at_offset pre ">=" tail 0;
  peek_at_offset pre ">=" tail 1;
  assert_norm (String.index ">=" 0 == FStar.Char.char_of_int 0x3E);
  assert_norm (String.index ">=" 1 == FStar.Char.char_of_int 0x3D)
#pop-options

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_hathat_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("^^" ^ (" " ^ tail))) (String.length pre) == (Tok_HATHAT, String.length pre + 2))
let next_token_hathat_pre pre tail =
  assert_norm (String.length "^^" == 2);
  assert_norm (ascii_string "^^");
  peek_at_offset pre "^^" tail 0;
  peek_at_offset pre "^^" tail 1;
  assert_norm (String.index "^^" 0 == FStar.Char.char_of_int 0x5E);
  assert_norm (String.index "^^" 1 == FStar.Char.char_of_int 0x5E)
#pop-options

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_ne_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("!=" ^ (" " ^ tail))) (String.length pre) == (Tok_NE, String.length pre + 2))
let next_token_ne_pre pre tail =
  assert_norm (String.length "!=" == 2);
  assert_norm (ascii_string "!=");
  peek_at_offset pre "!=" tail 0;
  peek_at_offset pre "!=" tail 1;
  assert_norm (String.index "!=" 0 == FStar.Char.char_of_int 0x21);
  assert_norm (String.index "!=" 1 == FStar.Char.char_of_int 0x3D)
#pop-options

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val next_token_or_pre (pre tail:string)
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ ("||" ^ (" " ^ tail))) (String.length pre) == (Tok_OR, String.length pre + 2))
let next_token_or_pre pre tail =
  assert_norm (String.length "||" == 2);
  assert_norm (ascii_string "||");
  peek_at_offset pre "||" tail 0;
  peek_at_offset pre "||" tail 1;
  assert_norm (String.index "||" 0 == FStar.Char.char_of_int 0x7C);
  assert_norm (String.index "||" 1 == FStar.Char.char_of_int 0x7C)
#pop-options

(* ============================================================ *)
(* Fragment definition *)
(* ============================================================ *)

let token_in_fragment (t : token) : bool =
  match t with
  | Tok_LBRACE | Tok_RBRACE | Tok_LPAREN | Tok_RPAREN
  | Tok_LBRACKET | Tok_RBRACKET | Tok_DOT | Tok_SEMI | Tok_COMMA
  | Tok_STAR | Tok_SLASH | Tok_PIPE | Tok_CARET | Tok_BANG | Tok_QMARK
  | Tok_PLUS | Tok_MINUS_OP | Tok_EQ | Tok_NE | Tok_LT | Tok_LE
  | Tok_GT | Tok_GE | Tok_AND | Tok_OR | Tok_HATHAT -> true
  | _ -> false

(* Return type carries the "safe first character" property directly,
   as a refinement — this is what lets downstream lemmas use the fact
   without re-deriving it via a separate match-with-wildcard lemma
   (which, empirically, chokes Z3 at 26-way case-split scale: see
   FINDING in the module banner above). *)
// `ascii_string s` added to the refinement (task #52): every literal this
// fragment prints IS ascii, and threading that through the RETURN TYPE
// (rather than a separate `print_token_is_ascii` lemma every caller must
// remember to invoke) makes it available for free at every call site,
// matching how `String.length s > 0`/etc. were already handled here.
#push-options "--z3rlimit 2000 --fuel 4 --ifuel 4"
let print_token (t : token{token_in_fragment t})
  : (s:string{String.length s > 0 /\ not (is_ws (String.index s 0)) /\ char_code (String.index s 0) <> 0x23 /\ ascii_string s})
  =
  match t with
  | Tok_LBRACE -> assert_norm (String.length "{" > 0 /\ not (is_ws (String.index "{" 0)) /\ char_code (String.index "{" 0) <> 0x23 /\ ascii_string "{"); "{"
  | Tok_RBRACE -> assert_norm (String.length "}" > 0 /\ not (is_ws (String.index "}" 0)) /\ char_code (String.index "}" 0) <> 0x23 /\ ascii_string "}"); "}"
  | Tok_LPAREN -> assert_norm (String.length "(" > 0 /\ not (is_ws (String.index "(" 0)) /\ char_code (String.index "(" 0) <> 0x23 /\ ascii_string "("); "("
  | Tok_RPAREN -> assert_norm (String.length ")" > 0 /\ not (is_ws (String.index ")" 0)) /\ char_code (String.index ")" 0) <> 0x23 /\ ascii_string ")"); ")"
  | Tok_LBRACKET -> assert_norm (String.length "[" > 0 /\ not (is_ws (String.index "[" 0)) /\ char_code (String.index "[" 0) <> 0x23 /\ ascii_string "["); "["
  | Tok_RBRACKET -> assert_norm (String.length "]" > 0 /\ not (is_ws (String.index "]" 0)) /\ char_code (String.index "]" 0) <> 0x23 /\ ascii_string "]"); "]"
  | Tok_DOT -> assert_norm (String.length "." > 0 /\ not (is_ws (String.index "." 0)) /\ char_code (String.index "." 0) <> 0x23 /\ ascii_string "."); "."
  | Tok_SEMI -> assert_norm (String.length ";" > 0 /\ not (is_ws (String.index ";" 0)) /\ char_code (String.index ";" 0) <> 0x23 /\ ascii_string ";"); ";"
  | Tok_COMMA -> assert_norm (String.length "," > 0 /\ not (is_ws (String.index "," 0)) /\ char_code (String.index "," 0) <> 0x23 /\ ascii_string ","); ","
  | Tok_STAR -> assert_norm (String.length "*" > 0 /\ not (is_ws (String.index "*" 0)) /\ char_code (String.index "*" 0) <> 0x23 /\ ascii_string "*"); "*"
  | Tok_SLASH -> assert_norm (String.length "/" > 0 /\ not (is_ws (String.index "/" 0)) /\ char_code (String.index "/" 0) <> 0x23 /\ ascii_string "/"); "/"
  | Tok_PIPE -> assert_norm (String.length "|" > 0 /\ not (is_ws (String.index "|" 0)) /\ char_code (String.index "|" 0) <> 0x23 /\ ascii_string "|"); "|"
  | Tok_CARET -> assert_norm (String.length "^" > 0 /\ not (is_ws (String.index "^" 0)) /\ char_code (String.index "^" 0) <> 0x23 /\ ascii_string "^"); "^"
  | Tok_BANG -> assert_norm (String.length "!" > 0 /\ not (is_ws (String.index "!" 0)) /\ char_code (String.index "!" 0) <> 0x23 /\ ascii_string "!"); "!"
  | Tok_QMARK -> assert_norm (String.length "?" > 0 /\ not (is_ws (String.index "?" 0)) /\ char_code (String.index "?" 0) <> 0x23 /\ ascii_string "?"); "?"
  | Tok_PLUS -> assert_norm (String.length "+" > 0 /\ not (is_ws (String.index "+" 0)) /\ char_code (String.index "+" 0) <> 0x23 /\ ascii_string "+"); "+"
  | Tok_MINUS_OP -> assert_norm (String.length "-" > 0 /\ not (is_ws (String.index "-" 0)) /\ char_code (String.index "-" 0) <> 0x23 /\ ascii_string "-"); "-"
  | Tok_EQ -> assert_norm (String.length "=" > 0 /\ not (is_ws (String.index "=" 0)) /\ char_code (String.index "=" 0) <> 0x23 /\ ascii_string "="); "="
  | Tok_NE -> assert_norm (String.length "!=" > 0 /\ not (is_ws (String.index "!=" 0)) /\ char_code (String.index "!=" 0) <> 0x23 /\ ascii_string "!="); "!="
  | Tok_LT -> assert_norm (String.length "<" > 0 /\ not (is_ws (String.index "<" 0)) /\ char_code (String.index "<" 0) <> 0x23 /\ ascii_string "<"); "<"
  | Tok_LE -> assert_norm (String.length "<=" > 0 /\ not (is_ws (String.index "<=" 0)) /\ char_code (String.index "<=" 0) <> 0x23 /\ ascii_string "<="); "<="
  | Tok_GT -> assert_norm (String.length ">" > 0 /\ not (is_ws (String.index ">" 0)) /\ char_code (String.index ">" 0) <> 0x23 /\ ascii_string ">"); ">"
  | Tok_GE -> assert_norm (String.length ">=" > 0 /\ not (is_ws (String.index ">=" 0)) /\ char_code (String.index ">=" 0) <> 0x23 /\ ascii_string ">="); ">="
  | Tok_AND -> assert_norm (String.length "&&" > 0 /\ not (is_ws (String.index "&&" 0)) /\ char_code (String.index "&&" 0) <> 0x23 /\ ascii_string "&&"); "&&"
  | Tok_OR -> assert_norm (String.length "||" > 0 /\ not (is_ws (String.index "||" 0)) /\ char_code (String.index "||" 0) <> 0x23 /\ ascii_string "||"); "||"
  | Tok_HATHAT -> assert_norm (String.length "^^" > 0 /\ not (is_ws (String.index "^^" 0)) /\ char_code (String.index "^^" 0) <> 0x23 /\ ascii_string "^^"); "^^"
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
(* `list (t:token{token_in_fragment t})` is not automatically a subtype
   of `list token` in this F* version (list is not treated as
   covariant for refinement widening without help) — widen explicitly
   via map with an element-level coercion, which IS free. *)
let widen_token (t : token{token_in_fragment t}) : token = t

// `ascii_string s` added to the refinement here too (task #52), by the
// same reasoning as `print_token` above -- proved by induction, `[]`
// case trivial (`assert_norm (ascii_string "")`), cons case via
// `ascii_string_concat` composing the head's (now-refinement-carried)
// ascii fact with the recursive call's own.
let rec print_tokens (ts : list (t:token{token_in_fragment t}))
  : Tot (s:string{(s == "" \/
                  (String.length s > 0 /\ not (is_ws (String.index s 0)) /\
                   char_code (String.index s 0) <> 0x23)) /\ ascii_string s})
        (decreases ts)
  =
  match ts with
  | [] -> assert_norm (ascii_string ""); ""
  | t :: rest ->
    let ptail = print_tokens rest in
    let s = print_token t ^ (" " ^ ptail) in
    FStar.String.concat_length (print_token t) (" " ^ ptail);
    assert (String.length s > 0);
    index_concat_at (print_token t) (" " ^ ptail) 0;
    assert_norm (ascii_string " ");
    ascii_string_concat " " ptail;
    ascii_string_concat (print_token t) (" " ^ ptail);
    s
#pop-options

(* ============================================================ *)
(* Fuel/skip-space glue *)
(* ============================================================ *)

val peek_char_concat_right (s1 s2 : string) (p : pos{p >= String.length s1 /\ p < String.length s1 + String.length s2})
  : Lemma (requires ascii_string s1 /\ ascii_string s2)
          (ensures peek_char (s1 ^ s2) p == peek_char s2 (p - String.length s1))
let peek_char_concat_right s1 s2 p =
  FStar.String.concat_length s1 s2;
  ascii_string_concat s1 s2;
  lemma_ascii_string_byte_length s1;
  lemma_ascii_string_byte_length s2;
  lemma_ascii_string_byte_length (s1 ^ s2);
  assert (not (at_end (s1 ^ s2) p));
  assert (not (at_end s2 (p - String.length s1)));
  fs_byte_at_concat s1 s2 p;
  assert (fs_byte_at (s1 ^ s2) p == fs_byte_at s2 (p - String.length s1));
  fs_byte_index_eq (s1 ^ s2) p;
  fs_byte_index_eq s2 (p - String.length s1);
  assert (peek_char (s1 ^ s2) p == fs_byte_index (s1 ^ s2) p);
  assert (peek_char s2 (p - String.length s1) == fs_byte_index s2 (p - String.length s1))

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val next_token_skip_space (input:string) (p:pos)
  : Lemma
      (requires
        not (at_end input p) /\ peek_char input p == FStar.Char.char_of_int 0x20 /\
        (at_end input (p+1) \/
         (not (is_ws (peek_char input (p+1))) /\ char_code (peek_char input (p+1)) <> 0x23)))
      (ensures next_token false input p == next_token false input (p+1))
let next_token_skip_space input p = ()
#pop-options

(* At end of input, next_token returns EOF without moving. Needed to
   close the `rest = []` case of the main induction: `next_token`
   equal-at-p-and-p+1 (above) is not by itself enough to relate
   `tokenize_loop` at p to `tokenize_loop` at p+1, because
   `tokenize_loop`'s own "no progress" guard (`p' <= p`) compares
   against ITS OWN call position, which differs (p vs p+1) between the
   two sides. The bridge needs to know CONCRETELY what `next_token`
   returns — either EOF (this lemma) or a definite forward position
   (the per-token `next_token_<X>_pre` lemmas, reused on the head of
   `rest` in `combine_step` below) — so both sides' guard checks agree
   numerically instead of symbolically. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val next_token_at_end (input:string) (p:pos)
  : Lemma (requires at_end input p)
          (ensures next_token false input p == (Tok_EOF, p))
let next_token_at_end input p = ()
#pop-options

(* Same fact as the 25 `next_token_<X>_pre` lemmas above, but taking
   the fragment token GENERICALLY and dispatching internally — proven
   ONCE, standalone. Reusing this single call from `combine_step`
   (instead of re-inlining a 25-way match on the head of `rest` at
   that call site) keeps the two 25-way case splits (the outer one on
   `t`, this one on `t2`) from being multiplied into one shared SMT
   query — the combined-case-explosion shape that Error 19'd even at
   z3rlimit 4000 / ifuel 8 before this lemma was hoisted out. *)
(* Diagnostic (Scratch.PrintUnfold.fst, kept out of the build) isolated
   the missing step: `FStar.String.concat_length` alone gives
   `length(lit^tail) == length(lit) + length(tail)`, NOT
   `== 1 + length(tail)` — `length(lit) == 1` (or 2) needs its OWN
   `assert_norm`, tied to the branch by an explicit
   `print_token t == "<lit>"` reveal first. Without both, the
   `next_token_<X>_pre` lemma's conclusion (stated over the LITERAL)
   never gets congruence-matched to this lemma's ENSURES (stated over
   `print_token t` symbolically) — that mismatch, not fuel/ifuel/case-
   explosion, was the root cause of the three prior Error 19s. *)
#push-options "--z3rlimit 2000 --fuel 4 --ifuel 4"
val next_token_head_pre (pre tail : string) (t : token{token_in_fragment t})
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures next_token false (pre ^ (print_token t ^ (" " ^ tail))) (String.length pre)
                    == (t, String.length pre + String.length (print_token t)))
let next_token_head_pre pre tail t =
  match t with
  | Tok_LBRACE   -> assert (print_token t == "{");  assert_norm (String.length "{" == 1);  next_token_lbrace_pre pre tail
  | Tok_RBRACE   -> assert (print_token t == "}");  assert_norm (String.length "}" == 1);  next_token_rbrace_pre pre tail
  | Tok_LPAREN   -> assert (print_token t == "(");  assert_norm (String.length "(" == 1);  next_token_lparen_pre pre tail
  | Tok_RPAREN   -> assert (print_token t == ")");  assert_norm (String.length ")" == 1);  next_token_rparen_pre pre tail
  | Tok_LBRACKET -> assert (print_token t == "[");  assert_norm (String.length "[" == 1);  next_token_lbracket_pre pre tail
  | Tok_RBRACKET -> assert (print_token t == "]");  assert_norm (String.length "]" == 1);  next_token_rbracket_pre pre tail
  | Tok_DOT      -> assert (print_token t == ".");  assert_norm (String.length "." == 1);  next_token_dot_pre pre tail
  | Tok_SEMI     -> assert (print_token t == ";");  assert_norm (String.length ";" == 1);  next_token_semi_pre pre tail
  | Tok_COMMA    -> assert (print_token t == ",");  assert_norm (String.length "," == 1);  next_token_comma_pre pre tail
  | Tok_STAR     -> assert (print_token t == "*");  assert_norm (String.length "*" == 1);  next_token_star_pre pre tail
  | Tok_SLASH    -> assert (print_token t == "/");  assert_norm (String.length "/" == 1);  next_token_slash_pre pre tail
  | Tok_PIPE     -> assert (print_token t == "|");  assert_norm (String.length "|" == 1);  next_token_pipe_pre pre tail
  | Tok_CARET    -> assert (print_token t == "^");  assert_norm (String.length "^" == 1);  next_token_caret_pre pre tail
  | Tok_BANG     -> assert (print_token t == "!");  assert_norm (String.length "!" == 1);  next_token_bang_pre pre tail
  | Tok_QMARK    -> assert (print_token t == "?");  assert_norm (String.length "?" == 1);  next_token_qmark_pre pre tail
  | Tok_PLUS     -> assert (print_token t == "+");  assert_norm (String.length "+" == 1);  next_token_plus_pre pre tail
  | Tok_MINUS_OP -> assert (print_token t == "-");  assert_norm (String.length "-" == 1);  next_token_minus_pre pre tail
  | Tok_EQ       -> assert (print_token t == "=");  assert_norm (String.length "=" == 1);  next_token_eq_pre pre tail
  | Tok_NE       -> assert (print_token t == "!="); assert_norm (String.length "!=" == 2); next_token_ne_pre pre tail
  | Tok_LT       -> assert (print_token t == "<");  assert_norm (String.length "<" == 1);  next_token_lt_pre pre tail
  | Tok_LE       -> assert (print_token t == "<="); assert_norm (String.length "<=" == 2); next_token_le_pre pre tail
  | Tok_GT       -> assert (print_token t == ">");  assert_norm (String.length ">" == 1);  next_token_gt_pre pre tail
  | Tok_GE       -> assert (print_token t == ">="); assert_norm (String.length ">=" == 2); next_token_ge_pre pre tail
  | Tok_AND      -> assert (print_token t == "&&"); assert_norm (String.length "&&" == 2); next_token_and_pre pre tail
  | Tok_OR       -> assert (print_token t == "||"); assert_norm (String.length "||" == 2); next_token_or_pre pre tail
  | Tok_HATHAT   -> assert (print_token t == "^^"); assert_norm (String.length "^^" == 2); next_token_hathat_pre pre tail
#pop-options

val string_concat_assoc (a b c : string) : Lemma ((a ^ b) ^ c == a ^ (b ^ c))
let string_concat_assoc a b c =
  FStar.String.list_of_concat a b;
  FStar.String.list_of_concat (a ^ b) c;
  FStar.String.list_of_concat b c;
  FStar.String.list_of_concat a (b ^ c);
  List.Tot.append_assoc (String.list_of_string a) (String.list_of_string b) (String.list_of_string c);
  FStar.String.string_of_list_of_string ((a ^ b) ^ c);
  FStar.String.string_of_list_of_string (a ^ (b ^ c))


(* ============================================================ *)
(* FINDING: the multi-token induction does not verify (this landing) *)
(* ============================================================ *)

(* This section is prose only — no F* declarations — describing the
   shape that resisted five verification attempts in this session, so
   a future widening does not repeat the search. The actual attempted
   code was DELETED (never left as an unproven / admitted definition
   in this file — iron rule #10).

   GOAL: a lemma (named `lemma_tokenize_loop_fragment` across the
   attempts) proving by induction on `ts` that `tokenize_loop`
   walking the string printed from an arbitrary fragment token LIST
   recovers that list. Structure: outer induction on `ts`, with a
   `combine_step` lemma per head token that (a) applies the matching
   `next_token_<X>_pre` fact for the head, then (b) must bridge
   `tokenize_loop` from the head's end position `p1` (the separating
   space) to `p1+1` (where the tail's own printing starts) before
   recursing on the tail via the SAME induction.

   OBSTRUCTION, precisely: `next_token_skip_space` (this file) only
   proves `next_token full p1 == next_token full (p1+1)` — NOT that
   `tokenize_loop full p1 acc fuel == tokenize_loop full (p1+1) acc
   fuel`. `tokenize_loop`'s own "no progress" guard (`p' <= p`)
   compares the position `next_token` returned against the CALL's OWN
   `p` argument, which differs between the two sides (p1 vs p1+1) —
   so the bridge additionally needs the CONCRETE value `next_token`
   returns at p1+1 (EOF, or a definite forward position `> p1+1`), not
   just the equality.

   Attempt 2 supplied that fact via a `match rest with [] |
   t2::rest2` case split inside `combine_step`, reusing the per-token
   lemmas on `t2`. This fixed the SHAPE (attempt 2's Error 19 moved
   from the caller into the case split itself, at the assert
   restating the applied lemma's own conclusion) but exposed a SECOND
   sub-obstruction: `assert (next_token false (pre2 ^ (print_token t2
   ^ ...)) ... == (t2, ... + String.length (print_token t2)))` failed
   even though the matching `next_token_<X>_pre pre2 r2` lemma had
   just been called in the same branch. Attempts 3-4 (raising
   z3rlimit 2000->4000, fuel/ifuel 4->6/8, and hoisting the 25-way
   dispatch into its own standalone lemma `next_token_head_pre` to
   rule out case-split multiplication with the OUTER 25-way match on
   the induction's head token) did not fix it — the ISOLATED
   `next_token_head_pre` failed with the IDENTICAL Error 19, which
   ruled out case-explosion as the cause.

   Root cause, confirmed by an isolated diagnostic
   (`Scratch.PrintUnfold.fst`, throwaway, not committed): connecting a
   `next_token_<X>_pre` fact stated over the LITERAL ("{" etc.) to a
   goal stated over `print_token t2` SYMBOLICALLY needs an EXPLICIT
   `assert (print_token t2 == "{")` PLUS its own `assert_norm
   (String.length "{" == 1)` in scope first — plain congruence does
   not also supply the length fact (`FStar.String.concat_length`
   alone gives `length(lit^tail) == length(lit) + length(tail)`, not
   `== 1 + length(tail)`, without `length(lit)` pinned separately).
   Attempt 5 added exactly that reveal (per branch) to
   `next_token_head_pre`, and `next_token_head_pre` THEN VERIFIED —
   it is landed below, in this file, and is real, reusable machinery.

   But `lemma_tokenize_loop_fragment`'s own top-level match (which
   must relate `tokenize_loop` at PRE_LEN through TWO unfolds — via
   the head token to `p1`, then via `next_token_head_pre` to `p1+1` —
   inside ONE induction step built by MUTUAL RECURSION with
   `combine_step`, rather than a flat sequence of asserts) still did
   not close within the session's time budget on attempt 5 (Error 19,
   same span as attempts 1-2, `See also` pointing at the lemma's own
   `ensures`).

   NEXT STEP for whoever widens this: apply the SAME treatment
   (`print_token t == "<lit>"` reveal + its own `assert_norm` length,
   stated explicitly rather than left to congruence) inside
   `combine_step`'s `t2 :: rest2` branch directly — the working
   pattern already exists in `next_token_head_pre` below, it just
   needs re-applying at the ORIGINAL call site instead of only inside
   the hoisted helper. Confirm the mutual-recursion `decreases` clause
   (`%[length rest; 1]` / `%[length ts; 0]`) is still accepted once
   that branch's proof term grows. This is a concrete, mechanical next
   attempt, not a re-opened question — budget it as attempt 6, not a
   fresh search.

   RESOLVED (attempt 6, same session's follow-up landing). The extra
   ingredient was not a THIRD reveal — it was packaging the reveal
   into a lemma whose CONCLUSION is already a `tokenize_loop` equation
   (`combine_step`, below), not just a `next_token` equation
   (`next_token_head_pre`). Calling `next_token_head_pre` alone from
   inside the induction left the caller to re-derive the
   `tokenize_loop` one-step unfold itself via a generic `assert` — and
   THAT assert is where Error 19 kept recurring, one level up from
   where attempts 1-5 diagnosed it. `combine_step` does the SAME
   per-constructor match + reveal as `next_token_head_pre` (mirroring
   its shape exactly, one branch per fragment constructor) but its
   `ensures` states the `tokenize_loop` step directly:
   `tokenize_loop full p0 acc fuel == tokenize_loop full p1 (t::acc)
   (fuel-1)`. The induction (`tokenize_loop_fragment`) then only ever
   INSTANTIATES that already-proven equation (pure unification, no
   fresh delta-unfold-plus-congruence at the call site) instead of
   re-deriving it. The second piece — the `p1` (space) to `p1+1`
   (start of the next print) gap that `next_token_skip_space` alone
   doesn't bridge at the `tokenize_loop` level, per the OBSTRUCTION
   note above — is `tokenize_loop_step_bridge`: given `next_token`
   agrees at both positions AND the returned position clears the
   further one (or the token is EOF), both sides' progress guards
   evaluate to the same boolean and the two `tokenize_loop` calls are
   the literal same term. No mutual recursion needed in the end: a
   single lemma inducting on `ts`, using `combine_step` once for the
   head token and `next_token_head_pre` + `peek_at_offset` once more
   (only for the NUMERIC fact `tokenize_loop_step_bridge` needs about
   what comes after the gap, not for a second `tokenize_loop` unfold)
   closes each step. See `combine_step`, `tokenize_loop_step_bridge`,
   `tokenize_loop_fragment`, `tokenize_fragment_roundtrip` below. *)

(* ============================================================ *)
(* Top-level wrapper *)
(* ============================================================ *)

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val print_tokens_length_bound (ts : list (t:token{token_in_fragment t}))
  : Lemma (ensures String.length (print_tokens ts) >= List.Tot.length ts)
    (decreases ts)
let rec print_tokens_length_bound ts =
  match ts with
  | [] -> ()
  | t :: rest ->
    print_tokens_length_bound rest;
    FStar.String.concat_length " " (print_tokens rest);
    FStar.String.concat_length (print_token t) (" " ^ print_tokens rest)
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val empty_concat_identity (s : string) : Lemma ("" ^ s == s)
let empty_concat_identity s =
  FStar.String.list_of_concat "" s;
  assert_norm (String.list_of_string "" == []);
  FStar.String.string_of_list_of_string ("" ^ s);
  FStar.String.string_of_list_of_string s
#pop-options

#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val concat_empty_right (s : string) : Lemma (s ^ "" == s)
let concat_empty_right s =
  FStar.String.list_of_concat s "";
  assert_norm (String.list_of_string "" == []);
  List.Tot.append_l_nil (String.list_of_string s);
  FStar.String.string_of_list_of_string (s ^ "");
  FStar.String.string_of_list_of_string s
#pop-options

(* ============================================================ *)
(* Single-token round-trip — the landing per this session's brief's *)
(* fallback clause ("land whatever single-token-class lemma          *)
(* verifies... write a FINDING"). Avoids the multi-token bridge      *)
(* entirely: `rest = []` always here, which is exactly the sub-case  *)
(* the induction attempts above DID close (the `next_token_at_end`   *)
(* path) — this reuses only lemmas that verify standalone:           *)
(* `next_token_head_pre`, `next_token_skip_space`, `next_token_at_end`,*)
(* `peek_at_space`, `empty_concat_identity`. Canonical-token           *)
(* recovery, not text recovery (see CANONICAL, NOT TEXTUAL, RECOVERY  *)
(* in the module banner) — moot here since no fragment token carries  *)
(* letters, but stated precisely because it will matter once keyword  *)
(* tokens widen the fragment (see FINDING above). *)
(* ============================================================ *)

#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val tokenize_single_fragment_token (t : token{token_in_fragment t})
  : Lemma (ensures tokenize (print_token t ^ " ") == [widen_token t; Tok_EOF])
let tokenize_single_fragment_token t =
  let txt = print_token t in
  let full = txt ^ " " in
  assert (String.length txt >= 1);
  assert_norm (ascii_string "");
  next_token_head_pre "" "" t;
  assert (next_token false ("" ^ (txt ^ (" " ^ ""))) (String.length "") == (t, String.length "" + String.length txt));
  empty_concat_identity (txt ^ (" " ^ ""));
  assert ("" ^ (txt ^ (" " ^ "")) == txt ^ (" " ^ ""));
  concat_empty_right " ";
  assert (" " ^ "" == " ");
  assert (txt ^ (" " ^ "") == txt ^ " ");
  assert (txt ^ (" " ^ "") == full);
  assert_norm (String.length "" == 0);
  assert_norm (ascii_string "");
  assert (next_token false full 0 == (t, String.length txt));
  let p1 = String.length txt in
  FStar.String.concat_length txt " ";
  assert_norm (String.length " " == 1);
  assert_norm (ascii_string " ");
  assert (String.length full == p1 + 1);
  ascii_string_concat txt " ";
  lemma_ascii_string_byte_length full;
  assert (not (at_end full p1));
  peek_at_space "" txt "";
  assert (peek_char full p1 == FStar.Char.char_of_int 0x20);
  assert (at_end full (p1 + 1));
  next_token_skip_space full p1;
  next_token_at_end full (p1 + 1);
  assert (next_token false full p1 == (Tok_EOF, p1 + 1));
  let fuel = String.length full + 1 in
  assert (tokenize_loop false full 0 [] fuel == tokenize_loop false full p1 [t] (fuel - 1));
  assert (tokenize_loop false full p1 [t] (fuel - 1) == List.Tot.rev (Tok_EOF :: [t]));
  assert (List.Tot.rev (Tok_EOF :: [t]) == [t; Tok_EOF]);
  assert (widen_token t == t);
  assert (tokenize full == tokenize_loop false full 0 [] fuel)
#pop-options

(* ============================================================ *)
(* Multi-token round-trip (attempt 6 — see RESOLVED note above) *)
(* ============================================================ *)

(* `combine_step`: same per-constructor match + literal reveal as
   `next_token_head_pre`, but its `ensures` states the ONE-STEP
   `tokenize_loop` unfold directly, not just the `next_token` fact —
   this is the piece that was missing from attempts 1-5 (see RESOLVED
   note in the FINDING section above). Packaging it this way lets the
   induction below INSTANTIATE the equation by unification instead of
   re-deriving it via a fresh `assert` at the call site, which is
   where the congruence broke previously. *)
#push-options "--z3rlimit 4000 --fuel 4 --ifuel 4"
val combine_step (pre tail : string) (t : token{token_in_fragment t}) (acc : list token) (fuel : nat{fuel > 0})
  : Lemma (requires ascii_string pre /\ ascii_string tail)
          (ensures
      next_token false (pre ^ (print_token t ^ (" " ^ tail))) (String.length pre)
        == (t, String.length pre + String.length (print_token t)) /\
      tokenize_loop false (pre ^ (print_token t ^ (" " ^ tail))) (String.length pre) acc fuel
        == tokenize_loop false (pre ^ (print_token t ^ (" " ^ tail)))
                          (String.length pre + String.length (print_token t)) (t :: acc) (fuel - 1))
let combine_step pre tail t acc fuel =
  let full = pre ^ (print_token t ^ (" " ^ tail)) in
  let p0 = String.length pre in
  FStar.String.concat_length pre (print_token t ^ (" " ^ tail));
  assert (String.length full == p0 + String.length (print_token t ^ (" " ^ tail)));
  assert (p0 <= String.length full);
  match t with
  | Tok_LBRACE ->
    assert (print_token t == "{");  assert_norm (String.length "{" == 1);  next_token_lbrace_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_RBRACE ->
    assert (print_token t == "}");  assert_norm (String.length "}" == 1);  next_token_rbrace_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_LPAREN ->
    assert (print_token t == "(");  assert_norm (String.length "(" == 1);  next_token_lparen_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_RPAREN ->
    assert (print_token t == ")");  assert_norm (String.length ")" == 1);  next_token_rparen_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_LBRACKET ->
    assert (print_token t == "[");  assert_norm (String.length "[" == 1);  next_token_lbracket_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_RBRACKET ->
    assert (print_token t == "]");  assert_norm (String.length "]" == 1);  next_token_rbracket_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_DOT ->
    assert (print_token t == ".");  assert_norm (String.length "." == 1);  next_token_dot_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_SEMI ->
    assert (print_token t == ";");  assert_norm (String.length ";" == 1);  next_token_semi_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_COMMA ->
    assert (print_token t == ",");  assert_norm (String.length "," == 1);  next_token_comma_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_STAR ->
    assert (print_token t == "*");  assert_norm (String.length "*" == 1);  next_token_star_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_SLASH ->
    assert (print_token t == "/");  assert_norm (String.length "/" == 1);  next_token_slash_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_PIPE ->
    assert (print_token t == "|");  assert_norm (String.length "|" == 1);  next_token_pipe_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_CARET ->
    assert (print_token t == "^");  assert_norm (String.length "^" == 1);  next_token_caret_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_BANG ->
    assert (print_token t == "!");  assert_norm (String.length "!" == 1);  next_token_bang_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_QMARK ->
    assert (print_token t == "?");  assert_norm (String.length "?" == 1);  next_token_qmark_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_PLUS ->
    assert (print_token t == "+");  assert_norm (String.length "+" == 1);  next_token_plus_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_MINUS_OP ->
    assert (print_token t == "-");  assert_norm (String.length "-" == 1);  next_token_minus_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_EQ ->
    assert (print_token t == "=");  assert_norm (String.length "=" == 1);  next_token_eq_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_NE ->
    assert (print_token t == "!="); assert_norm (String.length "!=" == 2); next_token_ne_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 2));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 2) (t :: acc) (fuel - 1))
  | Tok_LT ->
    assert (print_token t == "<");  assert_norm (String.length "<" == 1);  next_token_lt_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_LE ->
    assert (print_token t == "<="); assert_norm (String.length "<=" == 2); next_token_le_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 2));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 2) (t :: acc) (fuel - 1))
  | Tok_GT ->
    assert (print_token t == ">");  assert_norm (String.length ">" == 1);  next_token_gt_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 1));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 1) (t :: acc) (fuel - 1))
  | Tok_GE ->
    assert (print_token t == ">="); assert_norm (String.length ">=" == 2); next_token_ge_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 2));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 2) (t :: acc) (fuel - 1))
  | Tok_AND ->
    assert (print_token t == "&&"); assert_norm (String.length "&&" == 2); next_token_and_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 2));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 2) (t :: acc) (fuel - 1))
  | Tok_OR ->
    assert (print_token t == "||"); assert_norm (String.length "||" == 2); next_token_or_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 2));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 2) (t :: acc) (fuel - 1))
  | Tok_HATHAT ->
    assert (print_token t == "^^"); assert_norm (String.length "^^" == 2); next_token_hathat_pre pre tail;
    assert (next_token false full p0 == (t, p0 + 2));
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full (p0 + 2) (t :: acc) (fuel - 1))
#pop-options

(* Position bridge: relate `tokenize_loop` across the one-char gap
   between the separating space (position `p`) and whatever comes
   right after it (position `q = p+1`) — the piece `next_token_
   skip_space` alone does not supply, because it only equates
   `next_token`'s OWN return value at `p` vs `q`; `tokenize_loop`'s
   progress guard `p' <= p` compares the returned position against
   ITS OWN call argument, which differs (`p` vs `q`) between the two
   sides. Handing in the concrete `next_token` value up front (so the
   caller has already reconciled it via `next_token_skip_space`), plus
   a bound ensuring the guard evaluates the SAME way on both sides,
   lets the two `tokenize_loop` calls reduce to the literal same term
   without needing to know whether the token is EOF or a real one. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val tokenize_loop_step_bridge (input : string) (p q : pos) (acc : list token) (fuel : nat{fuel > 0})
  : Lemma
      (requires
        p <= String.length input /\ q <= String.length input /\ q > p /\
        next_token false input p == next_token false input q /\
        (fst (next_token false input p) == Tok_EOF \/ snd (next_token false input p) > q))
      (ensures tokenize_loop false input p acc fuel == tokenize_loop false input q acc fuel)
let tokenize_loop_step_bridge input p q acc fuel = ()
#pop-options

(* Congruence-isolation lemmas. Plain `a == b |- f a == f b` is a
   logically trivial congruence step, but proving it INLINE as an
   `assert` deep in a large accumulated proof context (many prior
   lets/asserts in scope) intermittently fails with Error 19 in this
   codebase's Z3 setup — apparently a search/resource issue, not a
   logical gap, since the SAME fact discharges instantly once isolated
   into its own near-empty lemma context (this file's own established
   idiom: every nontrivial string fact already goes through a small
   dedicated lemma — `index_concat_at`, `peek_at_offset`, `string_
   concat_assoc`, etc. — never a raw inline substitution). These give
   the induction below a small, reusable toolkit for that pattern so
   it never needs to re-derive a compound congruence inline. *)
#push-options "--z3rlimit 400 --fuel 4 --ifuel 4"
val concat_right_of_eq (pre a b : string) : Lemma (requires a == b) (ensures pre ^ a == pre ^ b)
let concat_right_of_eq pre a b = ()

val length_of_eq (a b : string) : Lemma (requires a == b) (ensures String.length a == String.length b)
let length_of_eq a b = ()

val next_token_input_of_eq (a b : string) (p : pos)
  : Lemma (requires a == b) (ensures next_token false a p == next_token false b p)
let next_token_input_of_eq a b p = ()

val tokenize_loop_input_of_eq (a b : string) (p : pos) (acc : list token) (fuel : nat)
  : Lemma (requires a == b) (ensures tokenize_loop false a p acc fuel == tokenize_loop false b p acc fuel)
let tokenize_loop_input_of_eq a b p acc fuel = ()

(* `(pre ^ (txt ^ " ")) ^ rest_str == pre ^ (txt ^ (" " ^ rest_str))` —
   the exact regrouping needed to show the "already printed head token
   plus its separating space" prefix, reapplied as a fresh `pre` for
   the tail, reconstitutes the original full string. *)
val concat_regroup3 (pre txt rest_str : string)
  : Lemma (ensures (pre ^ (txt ^ " ")) ^ rest_str == pre ^ (txt ^ (" " ^ rest_str)))
let concat_regroup3 pre txt rest_str =
  string_concat_assoc pre (txt ^ " ") rest_str;
  string_concat_assoc txt " " rest_str

(* Length of `txt ^ (" " ^ tail)` when `tail` is (provably) empty. Each
   congruence hop (space-plus-tail collapsing to a bare space, then
   that substituted inside `txt ^ (...)`) is its own lemma call with
   an explicit transitivity `assert` in between — the SAME "isolate,
   don't chain implicitly" discipline as the rest of this toolkit. *)
val space_tail_empty_length (txt tail : string)
  : Lemma (requires tail == "")
          (ensures String.length (txt ^ (" " ^ tail)) == String.length txt + 1)
let space_tail_empty_length txt tail =
  concat_right_of_eq " " tail "";
  assert (" " ^ tail == " " ^ "");
  concat_empty_right " ";
  assert (" " ^ "" == " ");
  assert (" " ^ tail == " ");
  concat_right_of_eq txt (" " ^ tail) " ";
  assert (txt ^ (" " ^ tail) == txt ^ " ");
  FStar.String.concat_length txt " ";
  assert_norm (String.length " " == 1);
  assert_norm (ascii_string " ");
  assert (String.length (txt ^ " ") == String.length txt + 1);
  length_of_eq (txt ^ (" " ^ tail)) (txt ^ " ");
  assert (String.length (txt ^ (" " ^ tail)) == String.length (txt ^ " "))
#pop-options

(* Main induction: `tokenize_loop`, walking the string printed from an
   arbitrary fragment token list, recovers that list (reversed onto
   `acc`, with the tokenizer's own trailing `Tok_EOF`). `fuel > length
   ts` is exactly the invariant `print_tokens_length_bound` supplies
   at the top-level call (`tokenize` itself uses `length input + 1`
   fuel, which always exceeds token count) and it is what keeps this
   induction from ever hitting the `fuel = 0` bail-out early. *)
#push-options "--z3rlimit 6000 --fuel 4 --ifuel 4"
val tokenize_loop_fragment (pre : string) (ts : list (t:token{token_in_fragment t}))
                            (acc : list token) (fuel : nat{fuel > List.Tot.length ts})
  : Lemma (requires ascii_string pre)
          (ensures
      tokenize_loop false (pre ^ print_tokens ts) (String.length pre) acc fuel
        == List.Tot.rev acc @ List.Tot.map widen_token ts @ [Tok_EOF])
    (decreases ts)
let rec tokenize_loop_fragment pre ts acc fuel =
  match ts with
  | [] ->
    let full = pre ^ print_tokens ts in
    assert (print_tokens ts == "");
    concat_empty_right pre;
    assert (full == pre);
    let p0 = String.length pre in
    assert (String.length full == p0);
    lemma_ascii_string_byte_length full;
    assert (at_end full p0);
    next_token_at_end full p0;
    assert (next_token false full p0 == (Tok_EOF, p0));
    assert (tokenize_loop false full p0 acc fuel == List.Tot.rev (Tok_EOF :: acc));
    List.Tot.rev_append [Tok_EOF] acc;
    assert (List.Tot.rev ([Tok_EOF] @ acc) == List.Tot.rev acc @ List.Tot.rev [Tok_EOF]);
    assert ([Tok_EOF] @ acc == Tok_EOF :: acc);
    assert (List.Tot.rev [Tok_EOF] == [Tok_EOF]);
    assert (List.Tot.rev (Tok_EOF :: acc) == List.Tot.rev acc @ [Tok_EOF]);
    assert (List.Tot.map widen_token ts == [])
  | t :: rest ->
    let full = pre ^ print_tokens ts in
    let ntail = print_tokens rest in
    assert (print_tokens ts == print_token t ^ (" " ^ ntail));
    assert (full == pre ^ (print_token t ^ (" " ^ ntail)));
    let p0 = String.length pre in
    let p1 = p0 + String.length (print_token t) in
    combine_step pre ntail t acc fuel;
    assert (tokenize_loop false full p0 acc fuel == tokenize_loop false full p1 (t :: acc) (fuel - 1));
    assert_norm (ascii_string " ");
    ascii_string_concat " " ntail;
    ascii_string_concat (print_token t) (" " ^ ntail);
    ascii_string_concat pre (print_token t ^ (" " ^ ntail));
    lemma_ascii_string_byte_length full;
    peek_at_space pre (print_token t) ntail;
    assert (not (at_end full p1));
    assert (peek_char full p1 == FStar.Char.char_of_int 0x20);
    (match rest with
     | [] ->
       assert (ntail == "");
       space_tail_empty_length (print_token t) ntail;
       assert (String.length (print_token t ^ (" " ^ ntail)) == String.length (print_token t) + 1);
       FStar.String.concat_length pre (print_token t ^ (" " ^ ntail));
       assert (String.length full == p1 + 1);
       assert_norm (ascii_string " ");
       ascii_string_concat " " ntail;
       ascii_string_concat (print_token t) (" " ^ ntail);
       ascii_string_concat pre (print_token t ^ (" " ^ ntail));
       lemma_ascii_string_byte_length full;
       assert (at_end full (p1 + 1));
       next_token_skip_space full p1;
       next_token_at_end full (p1 + 1);
       assert (next_token false full p1 == (Tok_EOF, p1 + 1));
       assert (tokenize_loop false full p1 (t :: acc) (fuel - 1)
               == List.Tot.rev (Tok_EOF :: (t :: acc)));
       List.Tot.rev_append [Tok_EOF] (t :: acc);
       assert (List.Tot.rev (Tok_EOF :: (t :: acc)) == List.Tot.rev (t :: acc) @ [Tok_EOF]);
       List.Tot.rev_append [t] acc;
       assert ([t] @ acc == t :: acc);
       assert (List.Tot.rev (t :: acc) == List.Tot.rev acc @ [t]);
       List.Tot.append_assoc (List.Tot.rev acc) [t] [Tok_EOF];
       assert ((List.Tot.rev acc @ [t]) @ [Tok_EOF] == List.Tot.rev acc @ ([t] @ [Tok_EOF]));
       assert (List.Tot.map widen_token ts == [t]);
       assert (tokenize_loop false full p0 acc fuel == List.Tot.rev acc @ List.Tot.map widen_token ts @ [Tok_EOF])
     | t2 :: rest2 ->
       let pre2 = pre ^ (print_token t ^ " ") in
       FStar.String.concat_length (print_token t) " ";
       assert_norm (String.length " " == 1);
       assert_norm (ascii_string " ");
       ascii_string_concat (print_token t) " ";
       ascii_string_concat pre (print_token t ^ " ");
       FStar.String.concat_length pre (print_token t ^ " ");
       assert (String.length pre2 == p1 + 1);
       concat_regroup3 pre (print_token t) ntail;
       assert (pre2 ^ ntail == full);
       assert (print_token t2 ^ (" " ^ print_tokens rest2) == ntail);
       concat_right_of_eq pre2 (print_token t2 ^ (" " ^ print_tokens rest2)) ntail;
       assert (pre2 ^ (print_token t2 ^ (" " ^ print_tokens rest2)) == pre2 ^ ntail);
       assert (pre2 ^ (print_token t2 ^ (" " ^ print_tokens rest2)) == full);
       next_token_head_pre pre2 (print_tokens rest2) t2;
       assert (next_token false (pre2 ^ (print_token t2 ^ (" " ^ print_tokens rest2))) (String.length pre2)
               == (t2, String.length pre2 + String.length (print_token t2)));
       next_token_input_of_eq (pre2 ^ (print_token t2 ^ (" " ^ print_tokens rest2))) full (String.length pre2);
       assert (next_token false full (String.length pre2) == (t2, String.length pre2 + String.length (print_token t2)));
       assert (next_token false full (p1 + 1) == (t2, p1 + 1 + String.length (print_token t2)));
       peek_at_offset pre2 (print_token t2) (print_tokens rest2) 0;
       assert (peek_char (pre2 ^ (print_token t2 ^ (" " ^ print_tokens rest2))) (String.length pre2 + 0)
               == String.index (print_token t2) 0);
       assert (peek_char full (p1 + 1) == String.index (print_token t2) 0);
       assert (not (is_ws (String.index (print_token t2) 0)));
       assert (char_code (String.index (print_token t2) 0) <> 0x23);
       assert (not (is_ws (peek_char full (p1 + 1))) /\ char_code (peek_char full (p1 + 1)) <> 0x23);
       next_token_skip_space full p1;
       assert (next_token false full p1 == next_token false full (p1 + 1));
       assert (next_token false full p1 == (t2, p1 + 1 + String.length (print_token t2)));
       assert (String.length (print_token t2) > 0);
       assert (snd (next_token false full p1) > p1 + 1);
       assert (p1 <= String.length full);
       assert (p1 + 1 <= String.length full);
       tokenize_loop_step_bridge full p1 (p1 + 1) (t :: acc) (fuel - 1);
       assert (tokenize_loop false full p1 (t :: acc) (fuel - 1)
               == tokenize_loop false full (p1 + 1) (t :: acc) (fuel - 1));
       tokenize_loop_fragment pre2 rest (t :: acc) (fuel - 1);
       assert (tokenize_loop false (pre2 ^ print_tokens rest) (String.length pre2) (t :: acc) (fuel - 1)
               == List.Tot.rev (t :: acc) @ List.Tot.map widen_token rest @ [Tok_EOF]);
       assert (pre2 ^ print_tokens rest == full);
       tokenize_loop_input_of_eq (pre2 ^ print_tokens rest) full (String.length pre2) (t :: acc) (fuel - 1);
       assert (tokenize_loop false full (String.length pre2) (t :: acc) (fuel - 1)
               == List.Tot.rev (t :: acc) @ List.Tot.map widen_token rest @ [Tok_EOF]);
       assert (tokenize_loop false full (p1 + 1) (t :: acc) (fuel - 1)
               == List.Tot.rev (t :: acc) @ List.Tot.map widen_token rest @ [Tok_EOF]);
       assert (tokenize_loop false full p0 acc fuel
               == List.Tot.rev (t :: acc) @ List.Tot.map widen_token rest @ [Tok_EOF]);
       List.Tot.rev_append [t] acc;
       assert ([t] @ acc == t :: acc);
       assert (List.Tot.rev (t :: acc) == List.Tot.rev acc @ [t]);
       List.Tot.append_assoc (List.Tot.rev acc) [t] (List.Tot.map widen_token rest @ [Tok_EOF]);
       assert ((List.Tot.rev acc @ [t]) @ (List.Tot.map widen_token rest @ [Tok_EOF])
               == List.Tot.rev acc @ ([t] @ (List.Tot.map widen_token rest @ [Tok_EOF])));
       assert ([t] @ (List.Tot.map widen_token rest @ [Tok_EOF])
               == t :: (List.Tot.map widen_token rest @ [Tok_EOF]));
       assert (List.Tot.map widen_token ts == t :: List.Tot.map widen_token rest);
       assert (List.Tot.map widen_token ts @ [Tok_EOF]
               == t :: (List.Tot.map widen_token rest @ [Tok_EOF]));
       assert (tokenize_loop false full p0 acc fuel == List.Tot.rev acc @ List.Tot.map widen_token ts @ [Tok_EOF]))
#pop-options

(* Top-level corollary: fold `tokenize_loop_fragment` under `tokenize`
   itself (`pre = ""`, `acc = []`, the same `length input + 1` fuel
   `tokenize` supplies), producing the list-level round-trip theorem
   this module set out to prove. *)
#push-options "--z3rlimit 800 --fuel 4 --ifuel 4"
val tokenize_fragment_roundtrip (ts : list (t:token{token_in_fragment t}))
  : Lemma (ensures tokenize (print_tokens ts) == List.Tot.map widen_token ts @ [Tok_EOF])
let tokenize_fragment_roundtrip ts =
  let s = print_tokens ts in
  let fuel = String.length s + 1 in
  print_tokens_length_bound ts;
  assert (fuel > List.Tot.length ts);
  assert_norm (ascii_string "");
  tokenize_loop_fragment "" ts [] fuel;
  assert_norm (String.length "" == 0);
  assert (tokenize_loop false ("" ^ print_tokens ts) (String.length "") [] fuel
          == List.Tot.rev [] @ List.Tot.map widen_token ts @ [Tok_EOF]);
  empty_concat_identity (print_tokens ts);
  assert ("" ^ print_tokens ts == print_tokens ts);
  assert (List.Tot.rev ([] <: list token) == []);
  assert (tokenize_loop false s 0 [] fuel == List.Tot.map widen_token ts @ [Tok_EOF]);
  // `tokenize`'s fuel is `fs_byte_length input + 1` (task #52 migration —
  // was `String.length input + 1` before `tokenize_loop`'s own bound
  // check and fuel became byte-indexed); `fuel` above was built from
  // `String.length s + 1` to match `print_tokens_length_bound`'s own
  // codepoint-length statement, so the two need reconciling via the
  // ascii bridge (`s = print_tokens ts` carries `ascii_string s` in its
  // own refinement already).
  lemma_ascii_string_byte_length s;
  assert (tokenize s == tokenize_loop false s 0 [] (fs_byte_length s + 1));
  assert (fs_byte_length s + 1 == String.length s + 1);
  assert (tokenize s == List.Tot.map widen_token ts @ [Tok_EOF])
#pop-options
