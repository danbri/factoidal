module RDF.NTriples.RoundTrip

(** ======================================================================== **)
(** G4: N-Triples serialize/parse round-trip theorems                        **)
(**                                                                          **)
(** WHY THIS MATTERS. `bin/npm-entry/entry_jsoo.ml`'s                       **)
(** `construct_triples_to_ntriples` (line ~551) is the function behind the   **)
(** `coreRdfsClosure` / `rdfsPlusClosure` JS API surface (`npm/factoidal/    **)
(** lib/api.js`, `rhoDfClosure` / `rdfsPlusClosure` entry calls) — every     **)
(** closure result crosses the certified API boundary as N-Triples TEXT,     **)
(** and the post-32 downstream chain (further JS calls, hub cells, other     **)
(** engine entry points fed a previous result) re-parses that text via       **)
(** `Parser.NTriples.parse_ntriples` / `parse_ntriples_strict`. This module   **)
(** was commissioned to seal that boundary: prove                            **)
(** `parse_ntriples (serialize g) == g` on a precisely stated fragment.       **)
(** It gets partway there — see FINDING below for exactly how far and why.   **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** SCOUT: locating the real serializer/parser pair                         **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** SERIALIZER — two candidates exist; only one is the actual boundary       **)
(** function:                                                                **)
(**   - `RDF.Pretty.term_to_ntriples` (RDF.Pretty.fst line 46) — the CLI's   **)
(**     display-only renderer. Its own module banner says so explicitly:     **)
(**     "`term_to_ntriples` had a dead-code branch..." / "for factoidal_cli  **)
(**     .ml"; RDF.NQuads.Serialize.fst's banner is blunter still: `term_to   **)
(**     _ntriples` "is intentionally lossy on literal escaping (it's for     **)
(**     display, not wire)". NOT the boundary function — no literal escaping **)
(**     at all, so it is not even wire-correct.                              **)
(**   - `RDF.NQuads.Serialize.{nq_subject_to_string, nq_term_to_string,       **)
(**     nq_line_for_triple_default_graph, canonical_nt_document}`            **)
(**     (RDF.NQuads.Serialize.fst) — THE boundary function.                  **)
(**     `bin/npm-entry/entry_jsoo.ml:551` defines                            **)
(**       `construct_triples_to_ntriples triples = concatMap (fun t ->       **)
(**          RDF_NQuads_Serialize.nq_line_for_triple_default_graph t)`,       **)
(**     called at lines 606/707/1019/1102/1105/1162/1194/1232/1743 for the   **)
(**     construct/closure/tableau/OWL/report result paths — including the    **)
(**     `rhoDfClosure`/`rdfsPlusClosure` results the WHY THIS MATTERS         **)
(**     paragraph names. This module targets THIS pair.                      **)
(**                                                                          **)
(** PARSER — `Parser.NTriples.parse_ntriples` / `.parse_ntriples_acc` /      **)
(** `.parse_triple` / `.parse_subject` / `.parse_object` / `.parse_iri` /    **)
(** `.parse_iri_raw` / `.parse_bnode` / `.parse_literal` (Parser.NTriples    **)
(** .fst). Confirmed: EVERY byte the recursive-descent scanner reads goes    **)
(** through `Parser.FastString.{fs_byte_length, fs_byte_at, fs_byte_sub,     **)
(** fs_byte_index, fs_cp_at}` — five `assume val`-realised primitives        **)
(** (rule #11(b), realised in `89_fast_string_primitives.sh`) with NO        **)
(** F*-visible base-VALUE equations (see FINDING). This is the SAME wall     **)
(** `SPARQL.Protocol.RoundTrip.fst` (SRJ) and issue #358 already named — not **)
(** "real FStar.String primitives", so the parser side of this module        **)
(** cannot use direct FStar.String induction the way `RDF.Store.Columnar.    **)
(** DeltaLog.fst`'s byte-list round trip does.                               **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** FINDING 1 (confirms + extends #358 / SPARQL.Protocol.RoundTrip.fst):     **)
(** the parser cannot be reduced or reasoned about AT ALL, for ANY input,    **)
(** even the most trivial concrete literal.                                  **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** `Parser.FastString.Axioms.fsti` supplies 7 `val`s (6 numbered facts,     **)
(** fact 5 split into a 5a/5b pair) — all RELATIONAL (concat-homomorphism    **)
(** on length, index/slice-into-concat, cp_at agreeing with an ALREADY-      **)
(** KNOWN byte_at value) except fact 3 (`fs_byte_length_ascii_singleton`,    **)
(** an absolute fact, but about LENGTH only). None of the 7 supplies a base  **)
(** case tying `fs_byte_at`'s or `fs_byte_sub`'s return VALUE to any         **)
(** string's actual content — the file's own "STILL MISSING" note names     **)
(** exactly this gap (candidate facts 7/8, drafted but explicitly NOT added, **)
(** DO-NOT-WIDEN). Two probes run and discarded this session (not committed  **)
(** — see the worktree's now-deleted `ZZ.NTProbe.fst`), both against         **)
(** `Parser.NTriples` directly, both `Error 19`:                             **)
(**   `let _ () : Lemma (fs_byte_at "<" 0 == 0x3C) = ()`                     **)
(**     -- "Could not prove post-condition" (reconfirms the Axioms.fsti      **)
(**        probe, this time inside Parser.NTriples' own dependency closure). **)
(**   `let _ () : Lemma (parse_iri_raw "<a>" 0 == ParseOk "a" 3) = ()`       **)
(**     -- ALSO "Could not prove post-condition" — the SIMPLEST possible     **)
(**        concrete N-Triples IRI (3 bytes) does not reduce. `parse_iri_raw` **)
(**        is a total, non-opaque `let` (F*'s normalizer CAN in principle    **)
(**        step through it), but every branch dispatches on the numeric      **)
(**        VALUE `fs_byte_index` returns (`FStar.Char.int_of_char ch =       **)
(**        0x3C`), and `fs_byte_at` is an `assume val`: the normalizer has   **)
(**        no defining equation to unfold, so it cannot even determine       **)
(**        which branch a match takes, let alone compute a result. This is   **)
(**        not a "z3 needs more fuel" failure — no amount of `--z3rlimit`/   **)
(**        `--fuel`/`--ifuel` fixes an uninterpreted symbol.                 **)
(**                                                                          **)
(** Consequence: no branch of `parse_iri_raw` / `parse_bnode` / `parse_      **)
(** literal` / `parse_triple` / `parse_ntriples` is provable for ANY         **)
(** concrete input under the current axiom set, mirroring SRJ's finding      **)
(** about `Parser.JSON.json_parse_*` exactly.                                **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** FINDING 2 (NEW this session — sharper than SRJ's case in two ways):      **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** (a) NO STRUCTURAL-HALF SALVAGE IS AVAILABLE. SRJ's `Parser.JSON.         **)
(** parse_json` builds an intermediate `json_val` TREE via FastString, and   **)
(** THEN `Parser.JSONResults.parse_binding_value`/`parse_binding_row` decode **)
(** that tree via plain `List.Tot` structural recursion with real equations  **)
(** — a second stage that never touches FastString, which is exactly what    **)
(** `SPARQL.Protocol.RoundTrip.fst` proves. N-Triples parsing has NO such     **)
(** checkpoint: `parse_ntriples_acc` walks bytes and emits `triple` records   **)
(** in ONE recursive-descent pass — there is no tree stage to fall back to,   **)
(** so the SRJ salvage strategy does not transfer to this format. This       **)
(** module cannot deliver a "structural half" analog to SRJ's Part 2-8.       **)
(**                                                                          **)
(** (b) THE SERIALIZER ITSELF IS FastString-GATED FOR LITERALS, EVEN WHEN    **)
(** NOTHING NEEDS ESCAPING. `RDF.NQuads.Serialize.nq_escape_literal` (the     **)
(** function every literal branch of `nq_term_to_string`/`nq_canon_term`      **)
(** routes through) walks its input byte-by-byte via `fs_byte_at`/           **)
(** `fs_byte_sub` UNCONDITIONALLY — even on an escape-free lexical form,      **)
(** `nq_escape_literal s == s` would need to know that `fs_byte_at s pos` is  **)
(** NOT one of the 5 special bytes for every `pos < fs_byte_length s`, which  **)
(** is exactly the missing base-VALUE fact again (Finding 1). So literals    **)
(** are excluded from the fragment below NOT merely because "typed/lang      **)
(** literals resist round-tripping" (the brief's anticipated fallback) but   **)
(** because EVERY literal, escape-free or not, is blocked on the SERIALIZER   **)
(** side before the parser is even reached. `term_nt_fragment` below is IRIs **)
(** and blank nodes ONLY — narrower than the brief's starting point, for a   **)
(** reason the brief didn't anticipate.                                      **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** WHAT THIS MODULE PROVES INSTEAD: serializer-side INJECTIVITY             **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(** `nq_subject_to_string` / `nq_term_to_string`'s S_IRI/T_IRI and           **)
(** S_BNode/T_BNode branches (`"<" ^ i ^ ">"` / `"_:" ^ b`) touch ONLY plain  **)
(** `^` (FStar.String concatenation) — no FastString anywhere. That puts     **)
(** them in exactly the territory the brief named as tractable: real         **)
(** `FStar.String` primitives WITH equations (`concat_length`,               **)
(** `list_of_concat`, `index_string_of_list` / the derived                   **)
(** `concat_injective`), all part of the trusted F* standard library, not    **)
(** an assumption this repo adds.                                            **)
(**                                                                          **)
(** INJECTIVITY is not the round-trip theorem itself, but it is a genuinely  **)
(** necessary ingredient of one (if the serializer weren't injective, no     **)
(** parser — however complete its axioms — could invert it), it is TRUE on   **)
(** this fragment, and it is fully provable today with zero new axioms.      **)
(** Two probes (`ZZ.NTProbe.fst`, run and deleted) confirmed both directions **)
(** — same-shape injectivity via `FStar.String.concat_injective` and         **)
(** cross-shape disambiguation (IRI output starts `<`, bnode output starts   **)
(** `_`) via `FStar.String.list_of_concat` plus the literal-reduction fact    **)
(** `list_of_string "<" == [char_of_int 0x3C]` (F*'s normalizer reduces      **)
(** `list_of_string` on concrete single-character literals with no lemma     **)
(** needed — the same fact `Parser.FastString.Axioms.fsti` relies on for its **)
(** fact 3 justification, and the reason this direction is NOT the same      **)
(** wall as Finding 1: `FStar.String.list_of_string` is a trusted stdlib      **)
(** primitive with normalizer support, `Parser.FastString.fs_byte_at` is a   **)
(** bare, unreduced `assume val` this repo added) — both verified first       **)
(** attempt, no `--z3rlimit`/`--fuel` tuning needed beyond the module         **)
(** default.                                                                 **)
(**                                                                          **)
(** FRAGMENT (`term_nt_fragment` / `triple_nt_fragment` / `graph_nt_        **)
(** fragment` below): `T_IRI` and `T_BNode` terms only (see Finding 2b for   **)
(** why literals are excluded outright, not merely typed/lang ones).         **)
(** `subject` needs no fragment restriction — its type (`S_IRI | S_BNode`)   **)
(** already excludes literals structurally, and the predicate position is    **)
(** always `wf_iri`.                                                        **)
(**                                                                          **)
(** `iri_print_safe` / `bnode_label_safe` (Part 1b) are defined per the      **)
(** brief's request — reusing `Parser.NTriples.is_iri_body_char` / `is_      **)
(** bnode_start_cp` / `is_bnode_char_cp` VERBATIM rather than re-implementing **)
(** the character classes — but are UNUSED by the injectivity lemmas below   **)
(** (which don't need content restrictions; see WIDENING REMAINING #2 for    **)
(** why a future triple-level effort will). Carried forward for that         **)
(** future session, exactly as SRJ's `escape_free` was carried forward       **)
(** unused for a different reason.                                          **)
(**                                                                          **)
(** ---------------------------------------------------------------------- **)
(** WIDENING REMAINING (tracked, not attempted here)                        **)
(** ---------------------------------------------------------------------- **)
(**                                                                          **)
(**   1. The actual round-trip theorem (`parse_object (nq_term_to_string t)  **)
(**      0 == ParseOk t ...`) needs base-VALUE facts for `fs_byte_at`/       **)
(**      `fs_byte_sub` (Finding 1) — the same gap SRJ's banner names,        **)
(**      tracked by issue #358. Once landed, THIS module's fragment and      **)
(**      injectivity lemmas are exactly the scaffolding a round-trip proof   **)
(**      needs on top (injectivity is the "at most one preimage" half;       **)
(**      the round trip additionally needs "the parser FINDS that preimage",**)
(**      which is what the missing facts unlock).                           **)
(**   2. TRIPLE-LEVEL injectivity (`nq_line_for_triple_default_graph`) is    **)
(**      NOT a corollary of the term-level lemmas below, for a reason        **)
(**      independent of Finding 1/2: `FStar.String.concat_injective`'s own   **)
(**      precondition is a DISJUNCTION on matching LENGTHS                   **)
(**      (`length s0 == length s0' \/ length s1 == length s1'`) — true       **)
(**      automatically in the term-level proofs below because one side of    **)
(**      every split is a FIXED literal (`"<"`, `">"`, `"_:"`), but NOT      **)
(**      automatically true across the five-part triple line, because       **)
(**      `wf_iri`/`bnode_id` place NO restriction on content (any string     **)
(**      containing a colon is a `wf_iri`). Without a content-safety         **)
(**      predicate excluding the delimiter bytes (`<`,`>`,` `,`\n`, …) from  **)
(**      IRI/bnode-label text, triple-line injectivity is not just           **)
(**      unprovable, it is FALSE in general (an IRI containing `"> <"` can   **)
(**      make two distinct triples serialize identically) — exactly the      **)
(**      role `iri_print_safe`/`bnode_label_safe` above are for. A future    **)
(**      session should restate triple/graph-level injectivity WITH those    **)
(**      predicates as hypotheses and prove it via an explicit first-        **)
(**      delimiter-occurrence argument (pure `FStar.String`, no FastString — **)
(**      this is provable in principle, just more proof engineering than     **)
(**      this session's per-term scope covers).                             **)
(** ======================================================================== **)
(** UPDATE 2026-08-11 (G4 M1-adjacent, ntriples-parser-lemmas session):      **)
(** FINDING 1's WALL IS PARTIALLY CROSSED. The FastString re-founding        **)
(** (2026-08-10, `Parser.FastString.fsti`'s bridging lemmas + `Parser.       **)
(** FastString.Axioms.fst`'s eight PROVED facts + `Parser.FastString.        **)
(** BaseCases.fst`) gave `fs_byte_length`/`fs_byte_at`/`fs_byte_sub` real,    **)
(** Spec-backed definitions with F*-visible equations — the "no base-VALUE   **)
(** fact ties a return value to string content" gap Finding 1 named is       **)
(** CLOSED for concrete inputs (Axioms facts 3/7 + BaseCases' per-delimiter  **)
(** lemmas). One gap remained even after that: `fs_byte_index` (the wrapper  **)
(** EVERY parser byte-dispatch site in this tree actually calls, not         **)
(** `fs_byte_at` directly) had no bridging lemma of its own — confirmed by   **)
(** probe, `fs_byte_at_eq` alone does not discharge `fs_byte_index "a" 0 ==  **)
(** FStar.Char.char_of_int 0x61` (Error 19). Added `fs_byte_index_eq` to     **)
(** `Parser.FastString.fsti`/`.fst` (trivial unfolding proof — the `b <      **)
(** 0xD800` guard in `fs_byte_index`'s definition is always taken since      **)
(** `fs_byte_at` returns `n:nat{n < 256}`).                                  **)
(**                                                                          **)
(** With that lemma, `parse_iri_raw "<a>" 0 == ParseOk "a" 3` — the EXACT    **)
(** probe Finding 1 named as failing (Error 19) — now VERIFIES. Part 5/6     **)
(** below build on this: a reusable `fs_byte_sub`-extraction helper (which   **)
(** deliberately avoids `FStar.String.string_of_list`/`list_of_string`       **)
(** entirely — chaining a separately-established `list_of_string s == [c]`   **)
(** fact through `string_of_list` to identify a result with a literal FAILS  **)
(** even with every fact in one SMT context, confirmed empirically this      **)
(** session, exactly the quirk `Parser.FastString.RoundTripLemmas.fst`'s     **)
(** banner already documents for a different pair of primitives — so this    **)
(** module's helper composes ONLY Axioms facts 2/4/5a/5b/8, landing on a     **)
(** concat operand that is ALREADY the target literal, never asking          **)
(** `string_of_list` to reproduce one) and a CLOSED triple-level round-trip  **)
(** theorem (checkpoint (a)): `parse_triple (nq_line_for_triple_default_     **)
(** graph t) 0 == ParseOk t <finalpos>` for a concrete `t` with `S_IRI`/     **)
(** `T_IRI` subject/predicate/object. This is the first PARSER-side round-   **)
(** trip statement this module proves — WIDENING REMAINING #1's "actual      **)
(** round-trip theorem" goal, at the narrowest (closed, concrete) grain.     **)
(** Still open: the SYMBOLIC term-level statement (arbitrary `wf_iri`, not   **)
(** one literal) and the general triple-level statement (WIDENING           **)
(** REMAINING #1/#2, now with the base-value wall gone but the proof-        **)
(** engineering scope still ahead) — see Part 6's own banner for the exact   **)
(** next-narrowest unproved statement.                                      **)
(** ======================================================================== **)

open FStar.List.Tot
open RDF.Graph.Executable
open RDF.NQuads.Serialize
open Parser.NTriples
open Parser.FastString
open Parser.FastString.Axioms
open Parser.Combinators

module Str = FStar.String
module Spec = Parser.FastString.Spec

#push-options "--z3rlimit 50 --fuel 4 --ifuel 4"

(** ====================================================================== **)
(** Part 1a: the fragment                                                   **)
(** ====================================================================== **)

// T_IRI / T_BNode only — see FINDING 2b for why literals are excluded
// outright.
let term_nt_fragment (t : rdf_term) : bool =
  match t with
  | T_IRI _   -> true
  | T_BNode _ -> true
  | _         -> false

// `subject` needs no restriction: S_IRI/S_BNode already exclude literals
// structurally, and `triple.p : wf_iri` is always in-fragment (an IRI).
// Only the object position needs the check.
let triple_nt_fragment (t : triple) : bool = term_nt_fragment t.o

let rec graph_nt_fragment (g : list triple) : Tot bool (decreases g) =
  match g with
  | [] -> true
  | t :: rest -> triple_nt_fragment t && graph_nt_fragment rest

(** ====================================================================== **)
(** Part 1b: content-safety predicates (defined per the brief; UNUSED by    **)
(** the injectivity lemmas below — see WIDENING REMAINING #2 for what a     **)
(** future triple-level effort needs them for). Reuse the parser's own      **)
(** character classes verbatim rather than re-implementing them, so this    **)
(** fragment never drifts from `Parser.NTriples`'s actual grammar.          **)
(** ====================================================================== **)

let rec chars_all (p : FStar.Char.char -> bool) (l : list FStar.Char.char)
  : Tot bool (decreases l) =
  match l with
  | [] -> true
  | c :: rest -> p c && chars_all p rest

// Exactly the character set `Parser.NTriples.parse_iri_body_acc`'s raw-byte
// arm accepts unescaped (no \u/\U needed): `is_iri_body_char`.
let iri_print_safe (i : string) : bool =
  chars_all Parser.NTriples.is_iri_body_char (Str.list_of_string i)

// A blank-node label the parser accepts on one pass: start char satisfies
// `is_bnode_start_cp`, every subsequent char satisfies `is_bnode_char_cp`
// (both codepoint-keyed in Parser.NTriples; ASCII chars have codepoint ==
// `FStar.Char.int_of_char`).
let bnode_label_safe (b : string) : bool =
  match Str.list_of_string b with
  | [] -> false
  | c0 :: rest ->
    Parser.NTriples.is_bnode_start_cp (FStar.Char.int_of_char c0) &&
    chars_all (fun c -> Parser.NTriples.is_bnode_char_cp (FStar.Char.int_of_char c)) rest

(** ====================================================================== **)
(** Part 2: subject-level injectivity of `nq_subject_to_string`             **)
(**                                                                          **)
(** `nq_subject_to_string` (RDF.NQuads.Serialize.fst) is the subject half    **)
(** of the boundary serializer: S_IRI i -> "<" ^ i ^ ">", S_BNode b ->       **)
(** "_:" ^ b. Both branches are pure FStar.String concatenation — the        **)
(** proof below never touches Parser.FastString.                            **)
(** ====================================================================== **)

let lemma_nq_subject_to_string_same_shape_iri (i1 i2 : wf_iri)
  : Lemma (requires nq_subject_to_string (S_IRI i1) == nq_subject_to_string (S_IRI i2))
          (ensures i1 == i2)
  =
  assert (nq_subject_to_string (S_IRI i1) == "<" ^ i1 ^ ">");
  assert (nq_subject_to_string (S_IRI i2) == "<" ^ i2 ^ ">");
  Str.concat_injective "<" "<" (i1 ^ ">") (i2 ^ ">");
  Str.concat_injective i1 i2 ">" ">"

let lemma_nq_subject_to_string_same_shape_bnode (b1 b2 : bnode_id)
  : Lemma (requires nq_subject_to_string (S_BNode b1) == nq_subject_to_string (S_BNode b2))
          (ensures b1 == b2)
  =
  assert (nq_subject_to_string (S_BNode b1) == "_:" ^ b1);
  assert (nq_subject_to_string (S_BNode b2) == "_:" ^ b2);
  Str.concat_injective "_:" "_:" b1 b2

// Cross-shape: an IRI's output always starts with '<' (0x3C), a bnode's
// always with '_' (0x5F) — distinguished via `list_of_concat` plus the
// literal-reduction fact `list_of_string "<" == [char_of_int 0x3C]` (F*'s
// normalizer computes `list_of_string` on concrete single-char literals
// directly, no lemma needed — see banner).
let lemma_nq_subject_to_string_cross_shape (i : wf_iri) (b : bnode_id)
  : Lemma (nq_subject_to_string (S_IRI i) =!= nq_subject_to_string (S_BNode b))
  =
  Str.list_of_concat "<" (i ^ ">");
  Str.list_of_concat "_:" b;
  assert (Str.list_of_string "<" == [FStar.Char.char_of_int 0x3C]);
  assert (Str.list_of_string "_:" == [FStar.Char.char_of_int 0x5F; FStar.Char.char_of_int 0x3A])

// Composed: subject-level injectivity over the full `subject` type.
let lemma_nq_subject_to_string_injective (s1 s2 : subject)
  : Lemma (requires nq_subject_to_string s1 == nq_subject_to_string s2)
          (ensures s1 == s2)
  =
  match s1, s2 with
  | S_IRI i1, S_IRI i2 -> lemma_nq_subject_to_string_same_shape_iri i1 i2
  | S_BNode b1, S_BNode b2 -> lemma_nq_subject_to_string_same_shape_bnode b1 b2
  | S_IRI i, S_BNode b -> lemma_nq_subject_to_string_cross_shape i b
  | S_BNode b, S_IRI i -> lemma_nq_subject_to_string_cross_shape i b

(** ====================================================================== **)
(** Part 3: term-level injectivity of `nq_term_to_string`, restricted to    **)
(** the fragment (T_IRI / T_BNode only). Same shape as Part 2 — `nq_term_   **)
(** to_string`'s IRI/BNode branches are textually identical to `nq_subject_ **)
(** to_string`'s.                                                          **)
(** ====================================================================== **)

let lemma_nq_term_to_string_same_shape_iri (i1 i2 : wf_iri)
  : Lemma (requires nq_term_to_string (T_IRI i1) == nq_term_to_string (T_IRI i2))
          (ensures i1 == i2)
  =
  assert (nq_term_to_string (T_IRI i1) == "<" ^ i1 ^ ">");
  assert (nq_term_to_string (T_IRI i2) == "<" ^ i2 ^ ">");
  Str.concat_injective "<" "<" (i1 ^ ">") (i2 ^ ">");
  Str.concat_injective i1 i2 ">" ">"

let lemma_nq_term_to_string_same_shape_bnode (b1 b2 : bnode_id)
  : Lemma (requires nq_term_to_string (T_BNode b1) == nq_term_to_string (T_BNode b2))
          (ensures b1 == b2)
  =
  assert (nq_term_to_string (T_BNode b1) == "_:" ^ b1);
  assert (nq_term_to_string (T_BNode b2) == "_:" ^ b2);
  Str.concat_injective "_:" "_:" b1 b2

let lemma_nq_term_to_string_cross_shape (i : wf_iri) (b : bnode_id)
  : Lemma (nq_term_to_string (T_IRI i) =!= nq_term_to_string (T_BNode b))
  =
  Str.list_of_concat "<" (i ^ ">");
  Str.list_of_concat "_:" b;
  assert (Str.list_of_string "<" == [FStar.Char.char_of_int 0x3C]);
  assert (Str.list_of_string "_:" == [FStar.Char.char_of_int 0x5F; FStar.Char.char_of_int 0x3A])

// Composed: term-level injectivity over the fragment. `t1`/`t2` range over
// all of `rdf_term`, but the `term_nt_fragment` hypothesis rules out
// T_Literal/T_TripleTerm, leaving exactly the two cases Parts above cover.
let lemma_nq_term_to_string_injective
    (t1 t2 : rdf_term{term_nt_fragment t1 /\ term_nt_fragment t2})
  : Lemma (requires nq_term_to_string t1 == nq_term_to_string t2)
          (ensures t1 == t2)
  =
  match t1, t2 with
  | T_IRI i1, T_IRI i2 -> lemma_nq_term_to_string_same_shape_iri i1 i2
  | T_BNode b1, T_BNode b2 -> lemma_nq_term_to_string_same_shape_bnode b1 b2
  | T_IRI i, T_BNode b -> lemma_nq_term_to_string_cross_shape i b
  | T_BNode b, T_IRI i -> lemma_nq_term_to_string_cross_shape i b

(** ====================================================================== **)
(** Part 4: graph-level injectivity (list level), the term-level lemma       **)
(** lifted pointwise. NOT a round-trip theorem (see FINDING 1/2 and         **)
(** WIDENING REMAINING #1) — this is the "at most one preimage per graph"    **)
(** half only, over the object position at each list index, given the two   **)
(** graphs already agree elsewhere. Triple-line-level injectivity (subject   **)
(** + predicate + object composed into one string) is WIDENING REMAINING    **)
(** #2, not attempted here.                                                 **)
(** ====================================================================== **)

// Pointwise object-injectivity down two structurally-aligned triple lists:
// if every object serializes the same and both graphs are in-fragment,
// the objects are equal position-by-position.
let rec lemma_nq_objects_injective_pointwise
    (g1 g2 : list triple{graph_nt_fragment g1 /\ graph_nt_fragment g2 /\
                          List.Tot.length g1 == List.Tot.length g2})
  : Lemma (requires
             (let os1 = List.Tot.map (fun t -> nq_term_to_string t.o) g1 in
              let os2 = List.Tot.map (fun t -> nq_term_to_string t.o) g2 in
              os1 == os2))
          (ensures
             List.Tot.map (fun t -> t.o) g1 == List.Tot.map (fun t -> t.o) g2)
          (decreases g1)
  =
  match g1, g2 with
  | [], [] -> ()
  | t1 :: rest1, t2 :: rest2 ->
    lemma_nq_term_to_string_injective t1.o t2.o;
    lemma_nq_objects_injective_pointwise rest1 rest2

#pop-options

(** ====================================================================== **)
(** Part 5: `fs_byte_sub`-extraction helper — the PARSER-side counterpart   **)
(** to Parts 2-4's serializer-side injectivity. See the module banner's     **)
(** 2026-08-11 UPDATE for the full context.                                 **)
(**                                                                          **)
(** `lemma_extract_middle prefix mid suffix` says: slicing the MIDDLE       **)
(** piece back out of a right-associated three-way concatenation recovers    **)
(** it exactly. This is `Parser.FastString.RoundTripLemmas.                  **)
(** lemma_quoted_content_byte_sub` generalised from a FIXED one-quote-char   **)
(** `suffix` to an ARBITRARY `suffix` — the shape every IRI-content          **)
(** extraction in `Parser.NTriples.parse_iri_raw`'s fast path needs (the     **)
(** N-Triples grammar's closing delimiter is one byte, `>`, but what FOLLOWS **)
(** it in a full triple line is not fixed the way JSON's closing quote is).  **)
(**                                                                          **)
(** WHY NOT `FStar.String.string_of_list`/`list_of_string`: the tempting     **)
(** alternative route — reduce `fs_byte_sub`'s definition (`string_of_list   **)
(** (utf8_decode_all (slice_bytes ...))`) all the way to a literal via the    **)
(** SAME `list_of_string s == [c]` / `string_of_list_of_string s` pair       **)
(** `Parser.FastString.BaseCases.fst` uses for single characters — was       **)
(** tried FIRST this session and FAILS even with every fact available in     **)
(** ONE SMT context (not just across separately-scoped `assert`s): given     **)
(** `list_of_string "a" == [c]` and `string_of_list (list_of_string "a") ==  **)
(** "a"` (from `string_of_list_of_string`) as two SEPARATE hypotheses, Z3     **)
(** does not combine them via congruence to conclude `string_of_list [c] ==  **)
(** "a"` — reproduced standalone against a fresh `assume val myf : list int  **)
(** -> int` (WORKS) vs the identical pattern against `FStar.String.          **)
(** string_of_list`/`list_of_string` (FAILS), matching the EXACT quirk       **)
(** `Parser.FastString.RoundTripLemmas.fst`'s own banner already documents   **)
(** for a different derivation. `lemma_extract_middle` below sidesteps it    **)
(** entirely: it never asks `string_of_list` to REPRODUCE a literal — Axiom  **)
(** fact 8 (`fs_byte_sub_self`) concludes `fs_byte_sub mid 0 (fs_byte_length **)
(** mid) == mid`, where `mid` is ALREADY the term on both sides (reflexivity **)
(** under the hood, not a re-identification), so the wall never applies.     **)
(** ====================================================================== **)

#push-options "--z3rlimit 400 --fuel 24 --ifuel 24"

// Extracts the middle piece of a right-associated 3-way string
// concatenation via its own byte length — the general shape every
// N-Triples-parser content-extraction call (`fs_byte_sub` after a
// `scan_..._end`-style scanner has found the closing delimiter) needs.
// Composes Axioms facts 2 (`fs_byte_length_concat`, twice: to compute the
// combined length AND to shift the right split), 5a/5b (`fs_byte_sub_
// concat_left`/`_right`: peel `prefix`, then peel `suffix`), and 8
// (`fs_byte_sub_self`: what remains IS `mid`).
let lemma_extract_middle (prefix mid suffix : string)
  : Lemma (fs_byte_sub (prefix ^ (mid ^ suffix)) (fs_byte_length prefix) (fs_byte_length mid) == mid)
  =
  fs_byte_length_concat mid suffix;
  fs_byte_length_concat prefix (mid ^ suffix);
  fs_byte_sub_concat_right prefix (mid ^ suffix) (fs_byte_length prefix) (fs_byte_length mid);
  fs_byte_sub_concat_left mid suffix 0 (fs_byte_length mid);
  fs_byte_sub_self mid

#pop-options

(** ====================================================================== **)
(** Part 6: checkpoint (a) — closed-literal PARSER round-trip.              **)
(**                                                                          **)
(** `checkpoint_a_closed_triple_round_trip`: for ONE concrete triple whose   **)
(** subject/predicate/object are all short IRIs (`"x:"`, `"y:"`, `"z:"` —    **)
(** the minimal `wf_iri` witnesses: `is_iri` only demands non-empty +        **)
(** colon-containing, so a bare `":"`-suffixed single letter is the          **)
(** shortest concrete witness that also keeps the three positions            **)
(** visually distinguishable in the proof), `parse_triple` applied to the    **)
(** ACTUAL SERIALIZER OUTPUT (`nq_line_for_triple_default_graph`, not a      **)
(** hand-typed lookalike string) recovers the exact original triple, at the  **)
(** exact byte position immediately after the trailing `.` (position 16;    **)
(** the line's own `\n` is left unconsumed, matching `parse_triple`'s        **)
(** contract — it does not consume trailing newline, that is `parse_        **)
(** ntriples_acc`'s job at the document level).                              **)
(**                                                                          **)
(** METHOD, in order (mirrors how `parse_triple` itself dispatches,          **)
(** `pws`/`parse_subject`/`pws`/`parse_iri`/`pws`/`parse_object`/`pws`/`.`   **)
(** — see that function in `Parser.NTriples.fst`):                          **)
(**   1. Pin the serializer output down to the flat 17-byte literal via      **)
(**      `assert_norm` (pure definitional unfolding — `nq_line_for_triple_   **)
(**      default_graph`/`nq_subject_to_string`/`nq_term_to_string` are all   **)
(**      transparent, and `target_triple`'s constructor fields are literal   **)
(**      `S_IRI`/`T_IRI` values, so this needs no fs_* reasoning at all).    **)
(**   2. Get `fs_byte_length`/`fs_byte_at`/`fs_byte_index` at every position  **)
(**      the parser actually reads (0..15) via the bridging lemmas +         **)
(**      `assert_norm` on `Parser.FastString.Spec.utf8_bytes`/`nth_byte`     **)
(**      (which DO reduce on concrete literals — confirmed for a 17-byte     **)
(**      literal this session, no chunking needed). `--fuel 24 --ifuel 24`   **)
(**      above `Parts 5`/`6` (vs. the file's usual `--fuel 4 --ifuel 4`) is   **)
(**      load-bearing: `FStar.List.Tot.length`/`Spec.nth_byte` need enough    **)
(**      fuel to unfold across a 17-element list; `--fuel 8` (the file's     **)
(**      other elevated setting, tried first) was NOT enough and failed      **)
(**      Error 19 at exactly the length assertion — recorded here since a    **)
(**      future narrower/wider variant will hit the same wall at whatever    **)
(**      fuel it tries first.                                                **)
(**   3. Get the three IRI-content `fs_byte_sub` results via `lemma_extract_ **)
(**      middle`, re-associating the flat literal into the needed            **)
(**      `prefix ^ (mid ^ suffix)` shape via `assert_norm` each time (works   **)
(**      for CONCRETE literal pieces — confirmed separately; plain           **)
(**      symbolic-variable associativity `(a^b)^c == a^(b^c)` does NOT hold   **)
(**      via `()`/`assert_norm` with no further help, a DIFFERENT, narrower   **)
(**      finding than the string_of_list wall above, not attempted further   **)
(**      since concrete reassociation is all this checkpoint needs).         **)
(**   4. `is_iri "x:"`/`"y:"`/`"z:"` via `assert_norm` (same reduction as     **)
(**      `RDF.Term.fsti`'s `xsd_string`-family constants use).                **)
(**   5. The final `assert (parse_triple s 0 == ParseOk target_triple 16)`   **)
(**      then goes through directly — every opaque atom `parse_triple`'s     **)
(**      definition touches (`fs_byte_length`/`fs_byte_at`/`fs_byte_index`/  **)
(**      `fs_byte_sub`, transitively through `pws`/`parse_subject`/          **)
(**      `parse_iri`/`parse_iri_raw`/`scan_iri_end`/`parse_object`) has a     **)
(**      known value in context, so Z3 walks the (fuel-unfolded) recursive    **)
(**      structure and checks equality of a fully-determined chain of        **)
(**      branches — no further lemma calls needed for this step itself.      **)
(**                                                                          **)
(** NEXT NARROWEST UNPROVED STATEMENT (WIDENING REMAINING #1, continued) —    **)
(** checkpoint (b) attempted this session, NOT LANDED, exact wall recorded:   **)
(**                                                                          **)
(** TARGET: the SYMBOLIC term-level lemma — `parse_iri_raw ("<" ^ i ^ ">")    **)
(** 0 == ParseOk i (fs_byte_length i + 2)` for an ARBITRARY `i : wf_iri`      **)
(** under `iri_print_safe i` (Part 1b's predicate, defined but still unused   **)
(** below — this is exactly what it is FOR). Needs `scan_iri_end` shown to    **)
(** terminate at `fs_byte_length i` for ANY such `i`, by induction on `i`'s   **)
(** byte content — the natural route is `Parser.FastString.BaseCases.          **)
(** build_string`/`all_ascii`-style structural induction: state and prove     **)
(** the lemma for `i = build_string cs` (a `cs : list char` satisfying         **)
(** `all_ascii cs /\ chars_all is_iri_body_char cs`), by induction on `cs`,    **)
(** the way `BaseCases.lemma_build_string_byte_at` generalises `BaseCases.    **)
(** fs_ascii_singleton_facts` from one character to arbitrarily many.         **)
(**                                                                          **)
(** THE WALL, precisely (probed this session, then reverted — not committed): **)
(** the inductive step needs to relate `scan_iri_end` starting at position 0  **)
(** of `(one_char_string c ^ build_string rest_cs) ^ (">" ^ tail)` (the CONS  **)
(** case) to the INDUCTIVE HYPOTHESIS's statement about `build_string          **)
(** rest_cs ^ (">" ^ tail)` — i.e. it needs a general "scan_iri_end commutes   **)
(** with prefixing" shift lemma, `Parser.FastString.RoundTripLemmas.           **)
(** lemma_byte_at_after_prefix`'s analogue for the RECURSIVE scanner, not      **)
(** just one `fs_byte_at` read. Building THAT shift lemma hits a wall ONE      **)
(** LAYER BELOW where Finding 1/2 lived: proving even the BASE CASE            **)
(** (`build_string [] ^ (">" ^ rest) == ">" ^ rest`, i.e. `"" ^ x == x` for    **)
(** a SYMBOLIC `x : string`) is NOT free — confirmed by direct probe:          **)
(**   `let _ (s:string) : Lemma ("" ^ s == s) = ()`                           **)
(**     -- FAILED, Error 19, "Could not prove post-condition".                **)
(** Z3 does not carry native associativity/identity reasoning for `^`         **)
(** (`Prims.op_Hat`/`strcat`) over SYMBOLIC string variables the way it does   **)
(** for CONCRETE literals (`assert_norm` on ground pieces — e.g. `("<" ^      **)
(** "a:") ^ ">" == "<" ^ ("a:" ^ ">")` in checkpoint (a) above — reduces       **)
(** fine; the identical shape with even ONE symbolic operand does not,        **)
(** confirmed by a parallel probe: `let _ (a b c:string) : Lemma ((a^b)^c ==  **)
(** a^(b^c)) = ()` ALSO fails Error 19). Every Axioms fact in this file       **)
(** (`fs_byte_length_concat`, `fs_byte_at_concat`, `fs_byte_sub_concat_       **)
(** left`/`_right`) is stated at the LENGTH/BYTE-VALUE level for exactly       **)
(** this reason — `Parser.FastString.BaseCases.fst`'s own lemma family         **)
(** (`lemma_build_string_byte_length`/`_byte_at`) never asserts a raw string   **)
(** equality involving `^` on a symbolic piece either, only length/byte-at     **)
(** consequences. A `scan_iri_end`-prefixing shift lemma built the SAME way    **)
(** — entirely in POSITION/VALUE terms, deriving `fs_byte_at`/`fs_byte_       **)
(** length` facts about the shifted call rather than a raw string identity     **)
(** about the input strings themselves — is very likely provable (nothing     **)
(** here contradicts it), but is a genuinely separate multi-step induction     **)
(** (fuel-matched to `scan_iri_end`'s own recursion, one step per byte of      **)
(** the accumulated prefix) that a 3-attempt guard does not clear. NOT         **)
(** attempted further this landing per the guard-depth rule — recorded as      **)
(** the precise next rung, not a vague "harder than expected".                **)
(** ====================================================================== **)

#push-options "--z3rlimit 400 --fuel 24 --ifuel 24"

// The witness triple: minimal `wf_iri` content ("x:"/"y:"/"z:" — a bare
// colon-suffixed letter is the shortest string satisfying `is_iri`, per
// RDF.Term.fsti's `is_iri s = length s > 0 && string_contains_colon s`).
let target_triple : triple =
  assert_norm (is_iri "x:" == true);
  assert_norm (is_iri "y:" == true);
  assert_norm (is_iri "z:" == true);
  { s = S_IRI "x:"; p = "y:"; o = T_IRI "z:" }

// Checkpoint (a): parsing the ACTUAL SERIALIZER OUTPUT for `target_triple`
// recovers it exactly, at the byte position right after the trailing `.`
// (the `\n` is left for the document-level parser to consume).
let checkpoint_a_closed_triple_round_trip (_:unit)
  : Lemma (parse_triple (nq_line_for_triple_default_graph target_triple) 0
           == ParseOk target_triple 16)
  =
  let s : string = nq_line_for_triple_default_graph target_triple in
  assert_norm (s == "<x:> <y:> <z:> .\n");
  // -- fs_byte_length / fs_byte_at / fs_byte_index at every position the
  // -- parser actually reads (0..15) --
  let bytes17 : list Spec.byte =
    [0x3C;0x78;0x3A;0x3E;0x20;0x3C;0x79;0x3A;0x3E;0x20;0x3C;0x7A;0x3A;0x3E;0x20;0x2E;0x0A] in
  assert_norm (Spec.utf8_bytes s == bytes17);
  fs_byte_length_eq s;
  assert_norm (FStar.List.Tot.length bytes17 == 17);
  assert (fs_byte_length s == 17);
  let get_byte (i:nat) (v:Spec.byte) : Lemma (requires Spec.nth_byte bytes17 i == Some v)
                                              (ensures fs_byte_at s i == v /\
                                                       fs_byte_index s i == FStar.Char.char_of_int v)
    = fs_byte_at_eq s i; fs_byte_index_eq s i
  in
  get_byte 0  0x3C; get_byte 1  0x78; get_byte 2  0x3A; get_byte 3  0x3E; get_byte 4  0x20;
  get_byte 5  0x3C; get_byte 6  0x79; get_byte 7  0x3A; get_byte 8  0x3E; get_byte 9  0x20;
  get_byte 10 0x3C; get_byte 11 0x7A; get_byte 12 0x3A; get_byte 13 0x3E; get_byte 14 0x20;
  get_byte 15 0x2E;
  assert (fs_byte_at s 0 == 0x3C);  assert (fs_byte_at s 1 == 0x78);
  assert (fs_byte_at s 2 == 0x3A);  assert (fs_byte_at s 3 == 0x3E);
  assert (fs_byte_at s 4 == 0x20);  assert (fs_byte_at s 5 == 0x3C);
  assert (fs_byte_at s 6 == 0x79);  assert (fs_byte_at s 7 == 0x3A);
  assert (fs_byte_at s 8 == 0x3E);  assert (fs_byte_at s 9 == 0x20);
  assert (fs_byte_at s 10 == 0x3C); assert (fs_byte_at s 11 == 0x7A);
  assert (fs_byte_at s 12 == 0x3A); assert (fs_byte_at s 13 == 0x3E);
  assert (fs_byte_at s 14 == 0x20); assert (fs_byte_at s 15 == 0x2E);
  assert (fs_byte_index s 0 == FStar.Char.char_of_int 0x3C);
  assert (fs_byte_index s 1 == FStar.Char.char_of_int 0x78);
  assert (fs_byte_index s 2 == FStar.Char.char_of_int 0x3A);
  assert (fs_byte_index s 3 == FStar.Char.char_of_int 0x3E);
  assert (fs_byte_index s 4 == FStar.Char.char_of_int 0x20);
  assert (fs_byte_index s 5 == FStar.Char.char_of_int 0x3C);
  assert (fs_byte_index s 6 == FStar.Char.char_of_int 0x79);
  assert (fs_byte_index s 7 == FStar.Char.char_of_int 0x3A);
  assert (fs_byte_index s 8 == FStar.Char.char_of_int 0x3E);
  assert (fs_byte_index s 9 == FStar.Char.char_of_int 0x20);
  assert (fs_byte_index s 10 == FStar.Char.char_of_int 0x3C);
  assert (fs_byte_index s 11 == FStar.Char.char_of_int 0x7A);
  assert (fs_byte_index s 12 == FStar.Char.char_of_int 0x3A);
  assert (fs_byte_index s 13 == FStar.Char.char_of_int 0x3E);
  assert (fs_byte_index s 14 == FStar.Char.char_of_int 0x20);
  assert (fs_byte_index s 15 == FStar.Char.char_of_int 0x2E);
  // -- fs_byte_sub for the three IRI contents, via lemma_extract_middle --
  assert_norm (s == "<" ^ ("x:" ^ "> <y:> <z:> .\n"));
  lemma_extract_middle "<" "x:" "> <y:> <z:> .\n";
  assert_norm (Spec.utf8_bytes "<" == [0x3C]);
  fs_byte_length_eq "<";
  assert (fs_byte_length "<" == 1);
  assert_norm (Spec.utf8_bytes "x:" == [0x78; 0x3A]);
  fs_byte_length_eq "x:";
  assert (fs_byte_length "x:" == 2);
  assert (fs_byte_sub s 1 2 == "x:");
  assert_norm (s == "<x:> <" ^ ("y:" ^ "> <z:> .\n"));
  lemma_extract_middle "<x:> <" "y:" "> <z:> .\n";
  assert_norm (Spec.utf8_bytes "<x:> <" == [0x3C;0x78;0x3A;0x3E;0x20;0x3C]);
  fs_byte_length_eq "<x:> <";
  assert (fs_byte_length "<x:> <" == 6);
  assert_norm (Spec.utf8_bytes "y:" == [0x79; 0x3A]);
  fs_byte_length_eq "y:";
  assert (fs_byte_length "y:" == 2);
  assert (fs_byte_sub s 6 2 == "y:");
  assert_norm (s == "<x:> <y:> <" ^ ("z:" ^ "> .\n"));
  lemma_extract_middle "<x:> <y:> <" "z:" "> .\n";
  assert_norm (Spec.utf8_bytes "<x:> <y:> <" == [0x3C;0x78;0x3A;0x3E;0x20;0x3C;0x79;0x3A;0x3E;0x20;0x3C]);
  fs_byte_length_eq "<x:> <y:> <";
  assert (fs_byte_length "<x:> <y:> <" == 11);
  assert_norm (Spec.utf8_bytes "z:" == [0x7A; 0x3A]);
  fs_byte_length_eq "z:";
  assert (fs_byte_length "z:" == 2);
  assert (fs_byte_sub s 11 2 == "z:");
  // -- well-formedness of the three IRI contents --
  assert_norm (is_iri "x:" == true);
  assert_norm (is_iri "y:" == true);
  assert_norm (is_iri "z:" == true);
  // -- the parse itself --
  assert (parse_triple s 0 == ParseOk target_triple 16)

#pop-options

(** ====================================================================== **)
(** Part 7: checkpoint (b) -- SYMBOLIC IRI-term round trip.                 **)
(**                                                                          **)
(** Closes WIDENING REMAINING #1's next-narrowest target from Part 6's own  **)
(** banner, at the scope that banner named as the natural route: `i =       **)
(** build_string cs` for an ASCII, `is_iri_body_char`-safe codepoint list    **)
(** `cs`, rather than an arbitrary `wf_iri` string. The two walls Part 6     **)
(** recorded are each closed by prior art landed independently THIS same    **)
(** session, consumed here as-is (neither reproven):                        **)
(**   - `"" ^ s == s` / `(a^b)^c == a^(b^c)` for SYMBOLIC strings --         **)
(**     `Parser.FastString.ConcatSpec.lemma_strcat_empty_l/_r/_assoc`.       **)
(**   - the "`scan_iri_end` commutes with prefixing" shift lemma Part 6      **)
(**     named as the remaining multi-step induction --                      **)
(**     `Parser.NTriples.Locality.lemma_scan_iri_end_shift_from_start`       **)
(**     (PILOT case of the parser-locality induction program).              **)
(**                                                                          **)
(** (b1) `lemma_scan_iri_end_build_string`: `scan_iri_end` on `build_string  **)
(** cs ^ (">" ^ rest)` finds `>` at position `length cs`, for ANY `cs`       **)
(** satisfying `all_ascii`/`chars_all is_iri_body_char` and ANY continuation **)
(** `rest`. Induction on `cs`: the base case unfolds via `lemma_strcat_      **)
(** empty_l`; the cons case re-associates via `lemma_strcat_assoc`, reads    **)
(** the ONE new byte (`fs_ascii_singleton_facts` + `fs_byte_at_concat`),     **)
(** and hands the TAIL off to the IH shifted by one position via `lemma_     **)
(** scan_iri_end_shift_from_start` -- so this induction contributes only     **)
(** the single-step reasoning `Parser.NTriples.Locality` does not already    **)
(** supply (it proves embedding preserves an ALREADY-SUCCESSFUL scan; it     **)
(** does not, and structurally cannot, establish that the scan succeeds in   **)
(** the first place for a content list built by consing one more char on).  **)
(**                                                                          **)
(** (b2) `lemma_parse_iri_raw_build_string`: `parse_iri_raw` on              **)
(** `"<" ^ (build_string cs ^ ">")` recovers `build_string cs` at position   **)
(** `length cs + 2` -- EXACTLY the "NEXT NARROWEST UNPROVED STATEMENT" Part  **)
(** 6 named (with `i` narrowed to `build_string cs`). Composes (b1) at       **)
(** `rest = ""` with one MORE application of `lemma_scan_iri_end_shift_      **)
(** from_start` (prefix `"<"`) to place the terminator inside the FULL       **)
(** bracketed string, then extracts the content via `lemma_extract_middle`   **)
(** (Part 5, already proved, reused verbatim, no new fs_byte_sub reasoning). **)
(**                                                                          **)
(** (b3) `lemma_parse_iri_build_string` / `lemma_term_iri_round_trip_        **)
(** build_string`: wraps (b2) through `parse_iri`'s `is_iri` check and       **)
(** `parse_object`'s `<`-dispatch branch, and restates the input as the      **)
(** ACTUAL SERIALIZER OUTPUT (`nq_term_to_string (T_IRI (build_string cs))`, **)
(** not a hand-typed lookalike -- same discipline checkpoint (a) used) via   **)
(** one MORE `lemma_strcat_assoc` re-association (`nq_term_to_string`'s      **)
(** `"<" ^ i ^ ">"` is LEFT-associated per F*'s default `^` fixity; (b2)'s   **)
(** statement is stated RIGHT-associated, matching `lemma_extract_middle`'s  **)
(** own `prefix ^ (mid ^ suffix)` shape). `lemma_term_iri_round_trip_        **)
(** build_string` IS checkpoint (b): the SYMBOLIC IRI-TERM round trip --     **)
(** `parse_object (nq_term_to_string (T_IRI i)) 0 == ParseOk (T_IRI i) ...`  **)
(** for an ARBITRARY well-formed `i = build_string cs` in the ASCII/         **)
(** iri-body-safe fragment (narrower than a fully arbitrary `wf_iri` -- see  **)
(** NEXT NARROWEST below for what that widening still needs).               **)
(**                                                                          **)
(** NEXT NARROWEST UNPROVED STATEMENT: dropping the `i = build_string cs`    **)
(** witness form for a fully arbitrary `i : wf_iri{iri_print_safe i}` (Part  **)
(** 1b's predicate, still otherwise unused) needs exactly one more bridging  **)
(** step -- `i == build_string (Str.list_of_string i)` for `iri_print_safe   **)
(** i`. STILL UNRESOLVED (re-attempted session 2026-08-11, `build-string-    **)
(** total` branch, ~20 throwaway probes, not committed) -- and SHARPER than  **)
(** this banner previously characterised it: the wall is not "chaining an    **)
(** IH string equality through a separate `list_of_string`/`string_of_list`  **)
(** congruence step" (that framing suggested a fixable proof-engineering     **)
(** gap); it reproduces even for the MINIMAL possible recursive Lemma        **)
(** (`let rec f (cs) : Lemma (list_of_string (build_string cs) == cs)        **)
(** (decreases cs) = match cs with | c::rest -> f rest; admit () | ...`)     **)
(** -- Z3 fails "incomplete quantifiers" AT THE RECURSIVE CALL STATEMENT     **)
(** ITSELF, before the `admit ()` even runs, i.e. with NOTHING downstream    **)
(** consuming the call's postcondition. Full minimal repro, the control      **)
(** probes that rule out the "separate hypothesis" and "string-specific"     **)
(** theories, and the (also-blocked) `fs_byte_sub`-based alternative route:  **)
(** `Parser.FastString.RoundTripLemmas.fst`'s "SHARPENED FINDING" section    **)
(** (end of file, session 2026-08-11). Not reattempted here beyond that      **)
(** session's probing per the guard-depth rule; recorded as the precise      **)
(** next rung, not a vague "harder than expected".                          **)
(** ====================================================================== **)

open Parser.NTriples.Locality
open Parser.FastString.ConcatSpec
open Parser.FastString.BaseCases

#push-options "--z3rlimit 300 --fuel 8 --ifuel 8"

// (b1): the scanner finds the terminator immediately after any
// all-ASCII, iri-body-safe codepoint list, for any continuation `rest`.
val lemma_scan_iri_end_build_string
    (cs : list FStar.Char.char{all_ascii cs /\ chars_all is_iri_body_char cs})
    (rest : string) (fuel : nat)
  : Lemma
      (requires fuel > FStar.List.Tot.length cs)
      (ensures
        scan_iri_end (build_string cs ^ (">" ^ rest)) 0 fuel
          == ParseOk (FStar.List.Tot.length cs) (FStar.List.Tot.length cs))
      (decreases cs)
let rec lemma_scan_iri_end_build_string cs rest fuel =
  match cs with
  | [] ->
    lemma_strcat_empty_l (">" ^ rest);
    fs_byte_length_gt ();
    fs_byte_at_gt ();
    fs_byte_length_concat ">" rest;
    fs_byte_at_concat ">" rest 0;
    fs_byte_index_eq (">" ^ rest) 0
  | c :: rest_cs ->
    let c_str = one_char_string c in
    let mid = build_string rest_cs ^ (">" ^ rest) in
    assert (FStar.Char.int_of_char c < 0x80);
    assert (is_iri_body_char c);
    assert (all_ascii rest_cs);
    assert (chars_all is_iri_body_char rest_cs);
    lemma_strcat_assoc c_str (build_string rest_cs) (">" ^ rest);
    lemma_one_char_list_of_string c;
    fs_ascii_singleton_facts c_str c;
    fs_byte_length_concat c_str mid;
    fs_byte_at_concat c_str mid 0;
    fs_byte_index_eq (c_str ^ mid) 0;
    let code = FStar.Char.int_of_char c in
    if code = 0x3E then ()
    else if code = 0x5C then ()
    else if code <= 0x20 || is_iri_forbidden_codepoint code then ()
    else begin
      lemma_scan_iri_end_build_string rest_cs rest (fuel - 1);
      lemma_build_string_byte_length rest_cs;
      fs_byte_length_gt ();
      fs_byte_length_concat ">" rest;
      fs_byte_length_concat (build_string rest_cs) (">" ^ rest);
      lemma_scan_iri_end_shift_from_start c_str mid "" (fuel - 1) (FStar.List.Tot.length rest_cs);
      lemma_strcat_empty_r mid
    end

#pop-options

#push-options "--z3rlimit 300 --fuel 8 --ifuel 8"

// (b2): the NEXT NARROWEST target Part 6 named, at i = build_string cs.
val lemma_parse_iri_raw_build_string
    (cs : list FStar.Char.char{all_ascii cs /\ chars_all is_iri_body_char cs})
  : Lemma
      (ensures
        parse_iri_raw ("<" ^ (build_string cs ^ ">")) 0
          == ParseOk (build_string cs) (FStar.List.Tot.length cs + 2))
let lemma_parse_iri_raw_build_string cs =
  let content = build_string cs in
  let n = FStar.List.Tot.length cs in
  let s = "<" ^ (content ^ ">") in
  lemma_build_string_byte_length cs;
  fs_byte_length_lt ();
  fs_byte_length_gt ();
  fs_byte_length_concat content ">";
  fs_byte_length_concat "<" (content ^ ">");
  fs_byte_at_lt ();
  fs_byte_at_concat "<" (content ^ ">") 0;
  fs_byte_index_eq s 0;
  lemma_strcat_empty_r ">";
  lemma_scan_iri_end_build_string cs "" (n + 2);
  fs_byte_length_concat ">" "";
  fs_byte_length_empty ();
  fs_byte_length_concat content (">" ^ "");
  lemma_scan_iri_end_shift_from_start "<" (content ^ (">" ^ "")) "" (n + 2) n;
  lemma_strcat_empty_r (content ^ (">" ^ ""));
  lemma_extract_middle "<" content ">"

#pop-options

#push-options "--z3rlimit 300 --fuel 8 --ifuel 8"

// (b3a): the `is_iri`-checked wrapper.
val lemma_parse_iri_build_string
    (cs : list FStar.Char.char{all_ascii cs /\ chars_all is_iri_body_char cs})
  : Lemma
      (requires is_iri (build_string cs))
      (ensures
        parse_iri ("<" ^ (build_string cs ^ ">")) 0
          == ParseOk (build_string cs) (FStar.List.Tot.length cs + 2))
let lemma_parse_iri_build_string cs =
  lemma_parse_iri_raw_build_string cs

// (b3): CHECKPOINT (b) -- the symbolic IRI-TERM round trip, against the
// actual serializer output `nq_term_to_string (T_IRI _)`, not a hand-typed
// lookalike (same discipline checkpoint (a) used).
val lemma_term_iri_round_trip_build_string
    (cs : list FStar.Char.char{all_ascii cs /\ chars_all is_iri_body_char cs})
  : Lemma
      (requires is_iri (build_string cs))
      (ensures
        parse_object (nq_term_to_string (T_IRI (build_string cs))) 0
          == ParseOk (T_IRI (build_string cs)) (FStar.List.Tot.length cs + 2))
let lemma_term_iri_round_trip_build_string cs =
  let content = build_string cs in
  let s = "<" ^ (content ^ ">") in
  lemma_parse_iri_build_string cs;
  assert (nq_term_to_string (T_IRI content) == "<" ^ content ^ ">");
  lemma_strcat_assoc "<" content ">";
  fs_byte_length_lt ();
  fs_byte_length_concat content ">";
  fs_byte_length_concat "<" (content ^ ">");
  fs_byte_at_lt ();
  fs_byte_at_concat "<" (content ^ ">") 0;
  fs_byte_index_eq s 0

#pop-options
