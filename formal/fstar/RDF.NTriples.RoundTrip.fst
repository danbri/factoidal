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

open FStar.List.Tot
open RDF.Graph.Executable
open RDF.NQuads.Serialize

module Str = FStar.String

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
