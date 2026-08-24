/-
L4Factoidal.SPARQL.AskBgpRoundTripString — the STRING round trip for the
ASK-BGP fragment.

`SPARQL11.Parser.AskBgpRoundTrip.fst` reaches this step and stops. Its
own banner says so, in capitals:

> "(a) STRING round-trip (`tokenize (print_query_1 q) ==
> expected_tokens_1 q`) and hence (e) the full string-to-AST MAIN
> THEOREM the brief specifies — IMPOSSIBLE, proved via an isolated
> minimal counter-probe … Root cause: `FStar.String.sub`'s specification
> in this ulib snapshot exposes ONLY a length refinement, no lemma
> relating its output characters to the input string's content — so no
> lemma can be stated, let alone proved, connecting a printed payload
> string back to the token's extract."

`askBgp_string_roundtrip` in this module is that theorem, proved. The
obstruction was never about SPARQL: it was about one library's interface
to one datatype. The Lean lexer scans `List Char`, so `scanIriBody` and
`scanVarName` have ordinary equation lemmas and relating a printed
payload to its token is an ordinary induction.

This is what the two-tree design is for. A property that holds in one
tree and not the other is about the trees, not about RDF — and here the
difference is nameable: `String.sub` versus a list recursion.

## How the proof goes

The printed query is cut into CHUNKS, each one token's text with its
leading separator: `ASK`, ` {`, ` <s>`, ` <p>`, ` <o>`, ` .`, …, ` }`.
`LexesTo` says a chunk lexes to its token and leaves the rest untouched,
`tokenizeLoop_chunks` folds that along the list, and `chunksOfQuery`
builds the chunk list whose concatenation is the printed string.

The separator goes at the START of each chunk, not the end. That is
forced: `nextToken` calls `skipWs` first, so a chunk with a TRAILING
space would leave the space unconsumed and `LexesTo` would be false.

## ⚠️ The side conditions are the specification, not decoration

`LexesTo` quantifies over what follows the chunk, so `ASK` followed by a
letter is not the `ASK` token — hence `SepStart`. And an IRI body must
satisfy TWO conditions:

* `iriBodyPlain` — no `>` (it ends the IRIREF) and no `\` (it starts an
  escape). This is §19.8 [139]'s own character rule.
* `iriFirstOk` — the first character must be one the lexer's `<`
  disambiguation accepts.

The second is NOT in the specification. Writing this theorem is what
exposed that: §19.8 [139] admits `<1abc>` and the lexer does not, in
both trees, and on the shipping binary. Filed as
<https://github.com/danbri/factoidal/issues/573>. Until that is fixed,
`iriFirstOk` is the honest side condition — narrowing the theorem to the
fragment the engine actually round-trips rather than claiming the
fragment the grammar allows.

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.SPARQL.AskBgpRoundTrip

namespace L4Factoidal.SPARQL.AskBgpRoundTrip

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## 1. Two scanning lemmas -/

/-- A backslash-free body passes through escape processing unchanged. -/
theorem processIriEscapesRec_id : ∀ (fuel : Nat) (cs acc : List Char),
    cs.length ≤ fuel → cs.all (fun c => c != '\\') = true →
    processIriEscapesRec fuel cs acc = acc.reverse ++ cs
  | 0, cs, acc, hf, _ => by
      have : cs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp [processIriEscapesRec]
  | _ + 1, [], acc, _, _ => by simp [processIriEscapesRec]
  | fuel + 1, c :: rest, acc, hf, hall => by
      have hc : ¬ (c == '\\') = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hall
        simpa using hall.1
      rw [processIriEscapesRec.eq_def]
      simp only [if_neg hc]
      rw [processIriEscapesRec_id fuel rest (c :: acc) (by simp at hf ⊢; omega)
            (by simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2)]
      simp

theorem processIriEscapes_id (cs : List Char)
    (h : cs.all (fun c => c != '\\') = true) : processIriEscapes cs = cs := by
  rw [processIriEscapes]
  simpa using processIriEscapesRec_id (cs.length + 1) cs [] (by omega) h

/-- `scanWhile` consumes a prefix that all satisfies its predicate and
stops at the first character that does not. -/
theorem scanWhile_prefix (p : Char → Bool) : ∀ (pre : List Char),
    pre.all p = true → ∀ (rest : List Char), (∀ c ∈ rest.head?, p c = false) →
    ∀ (pos : Nat) (acc : List Char),
      scanWhile p pos (pre ++ rest) acc
        = (acc.reverse ++ pre, pos + pre.length, rest)
  | [], _, rest, hr, pos, acc => by
      cases hrest : rest with
      | nil => simp [scanWhile]
      | cons c r => have := hr c (by simp [hrest]); simp [scanWhile, this]
  | c :: pre', hall, rest, hr, pos, acc => by
      have hc : p c = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.1
      rw [List.cons_append, scanWhile, if_pos hc,
          scanWhile_prefix p pre'
            (by simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2)
            rest hr (pos + 1) (c :: acc)]
      simp
      omega

/-! ## 2. Two `nextToken` unfoldings

The character dispatch is a twenty-branch `if` chain; naming the two
entries this fragment reaches keeps every proof below from re-walking
it. -/

set_option maxHeartbeats 2000000 in
theorem nextToken_sp_qmark (pos : Nat) (tail : List Char) :
    nextToken false pos (' ' :: '?' :: tail)
      = (let (name, pos', rest') := scanVarName (pos + 2) tail
         if name.length == 0 then (Token.qmark, pos + 1, pos + 2, tail)
         else (Token.var name, pos + 1, pos', rest')) := by
  rw [nextToken]
  simp only [show skipWs pos (' ' :: '?' :: tail) = (pos + 1, '?' :: tail) from rfl]
  simp

set_option maxHeartbeats 2000000 in
theorem nextToken_sp_lt (pos : Nat) (d : Char) (tail : List Char)
    (h1 : ¬ (d = '<')) (h2 : ¬ (d = '=')) :
    nextToken false pos (' ' :: '<' :: d :: tail)
      = nextToken.ltCase (pos + 1) '<' (d :: tail) := by
  rw [nextToken]
  simp only [show skipWs pos (' ' :: '<' :: d :: tail)
    = (pos + 1, '<' :: d :: tail) from rfl]
  simp only [beq_self_eq_true, if_pos]
  cases hd : d with
  | _ => simp_all

/-! ## 3. Chunks -/

/-- What may follow a chunk: nothing, or a separating space. Without
this, `ASK` followed by a letter is not the `ASK` token. -/
def SepStart (cs : List Char) : Prop := ∀ c ∈ cs.head?, c = ' '

/-- `chunk` lexes to exactly `t` and leaves `rest` untouched. -/
def LexesTo (t : Token) (chunk : List Char) : Prop :=
  chunk ≠ [] ∧
  ∀ (pos : Nat) (rest : List Char), SepStart rest →
    (nextToken false pos (chunk ++ rest)).1 = t
    ∧ (nextToken false pos (chunk ++ rest)).2.2.2 = rest

def chunkChars (parts : List (Token × List Char)) : List Char :=
  (parts.map (·.2)).flatten

def ChunksOk : List (Token × List Char) → Prop
  | [] => True
  | p :: rest =>
      LexesTo p.1 p.2 ∧ p.1 ≠ .eof ∧ SepStart (chunkChars rest) ∧ ChunksOk rest

/-! ## 4. Folding the tokenizer along the chunks -/

theorem tokenizeLoop_nil (fuel pos : Nat) (acc : List PosToken) :
    ((tokenizeLoop false (fuel + 1) pos [] acc).map (·.tok))
      = (acc.reverse.map (·.tok)) ++ [Token.eof] := by
  rw [tokenizeLoop]
  simp [nextToken, skipWs, skipWsComments]

theorem tokenizeLoop_chunk (t : Token) (chunk : List Char)
    (h : LexesTo t chunk) (ht : t ≠ .eof) (hsep : SepStart rest)
    (fuel pos : Nat) (acc : List PosToken) :
    tokenizeLoop false (fuel + 1) pos (chunk ++ rest) acc
      = tokenizeLoop false fuel (nextToken false pos (chunk ++ rest)).2.2.1 rest
          (⟨t, (nextToken false pos (chunk ++ rest)).2.1⟩ :: acc) := by
  obtain ⟨hne, hlex⟩ := h
  obtain ⟨h1, h2⟩ := hlex pos rest hsep
  rw [tokenizeLoop]
  simp only [h1, h2]
  have hcl : 0 < chunk.length := List.length_pos_iff.mpr hne
  have hlen : ¬ (rest.length ≥ (chunk ++ rest).length) := by
    simp only [List.length_append]; omega
  cases ht' : t with
  | eof => exact absurd ht' ht
  | _ => rw [if_neg hlen]

theorem tokenizeLoop_chunks :
    ∀ (parts : List (Token × List Char)) (fuel pos : Nat) (acc : List PosToken),
      ChunksOk parts → parts.length < fuel →
      (tokenizeLoop false fuel pos (chunkChars parts) acc).map (·.tok)
        = (acc.reverse.map (·.tok)) ++ parts.map (·.1) ++ [Token.eof]
  | [], fuel, pos, acc, _, hf => by
      cases fuel with
      | zero => omega
      | succ f => simpa [chunkChars] using tokenizeLoop_nil f pos acc
  | p :: rest, fuel, pos, acc, hok, hf => by
      cases fuel with
      | zero => omega
      | succ f =>
        obtain ⟨hlex, hne, hsep, hrest⟩ := hok
        simp only [chunkChars, List.map_cons, List.flatten_cons]
        rw [show ((rest.map (·.2)).flatten) = chunkChars rest from rfl,
            tokenizeLoop_chunk p.1 p.2 hlex hne (rest := chunkChars rest) hsep
              f pos acc,
            tokenizeLoop_chunks rest f _ _ hrest (by simp at hf ⊢; omega)]
        simp

/-! ## 5. Every chunk this fragment uses -/

theorem lexes_ask : LexesTo .ask ['A', 'S', 'K'] := by
  refine ⟨by simp, fun pos rest hsep => ?_⟩
  cases hr : rest with
  | nil => exact ⟨rfl, rfl⟩
  | cons c r => have : c = ' ' := hsep c (by simp [hr]); subst this; exact ⟨rfl, rfl⟩

theorem lexes_lbrace : LexesTo .lbrace [' ', '{'] := by
  refine ⟨by simp, fun pos rest hsep => ?_⟩
  cases hr : rest with
  | nil => exact ⟨rfl, rfl⟩
  | cons c r => have : c = ' ' := hsep c (by simp [hr]); subst this; exact ⟨rfl, rfl⟩

theorem lexes_rbrace : LexesTo .rbrace [' ', '}'] := by
  refine ⟨by simp, fun pos rest hsep => ?_⟩
  cases hr : rest with
  | nil => exact ⟨rfl, rfl⟩
  | cons c r => have : c = ' ' := hsep c (by simp [hr]); subst this; exact ⟨rfl, rfl⟩

theorem lexes_dot : LexesTo .dot [' ', '.'] := by
  refine ⟨by simp, fun pos rest hsep => ?_⟩
  cases hr : rest with
  | nil => exact ⟨rfl, rfl⟩
  | cons c r => have : c = ' ' := hsep c (by simp [hr]); subst this; exact ⟨rfl, rfl⟩

theorem lexes_var (name : List Char)
    (hall : name.all (fun c => isAlnum c || c == '_') = true) (hne : name ≠ []) :
    LexesTo (.var (String.ofList name)) (' ' :: '?' :: name) := by
  refine ⟨by simp, fun pos rest hsep => ?_⟩
  have hstop : ∀ c ∈ rest.head?, (fun c => isAlnum c || c == '_') c = false := by
    intro c hc; have : c = ' ' := hsep c hc; subst this; decide
  have hscan : scanVarName (pos + 2) (name ++ rest)
      = (String.ofList name, pos + 2 + name.length, rest) := by
    simp only [scanVarName,
               scanWhile_prefix (fun c => isAlnum c || c == '_') name hall rest
                 hstop (pos + 2) []]
    simp
  have hlen : ¬ ((String.ofList name).length == 0) = true := by
    simp only [String.length_ofList, beq_iff_eq]
    have := List.length_pos_iff.mpr hne
    omega
  have hnt : nextToken false pos (' ' :: '?' :: (name ++ rest))
      = (Token.var (String.ofList name), pos + 1, pos + 2 + name.length, rest) := by
    rw [nextToken_sp_qmark pos (name ++ rest)]
    simp only [hscan]
    simp only [hlen, if_neg, Bool.false_eq_true, not_false_eq_true]
  exact ⟨by rw [List.cons_append, List.cons_append, hnt], by
    rw [List.cons_append, List.cons_append, hnt]⟩

/-- The first characters this lexer's `<` disambiguation accepts. ⚠️
NARROWER than §19.8 [139] — see the module header and issue 573. -/
def iriFirstOk (cs : List Char) : Bool :=
  match cs with
  | [] => true
  | d :: _ => isAlpha d || d == '_' || d == '/' || d == '#'

theorem lexes_iri (body : List Char) (hplain : iriBodyPlain body = true)
    (hfirst : iriFirstOk body = true) :
    LexesTo (.iri (String.ofList body)) (' ' :: '<' :: (body ++ ['>'])) := by
  have hnb : body.all (fun c => c != '\\') = true := by
    simp only [iriBodyPlain, List.all_eq_true] at hplain ⊢
    intro c hc; have := hplain c hc; simp at this ⊢; exact this.2
  have hesc : processIriEscapes body = body := processIriEscapes_id body hnb
  refine ⟨by simp, fun pos rest hsep => ?_⟩
  have hkey : nextToken false pos ((' ' :: '<' :: (body ++ ['>'])) ++ rest)
      = (Token.iri (String.ofList body), pos + 1,
         pos + 1 + 1 + body.length + 1, rest) := by
    cases hb : body with
    | nil =>
        simp only [hb, List.nil_append, List.cons_append]
        rw [nextToken_sp_lt pos '>' rest (by decide) (by decide)]
        simp only [nextToken.ltCase]
        rw [if_pos (by simp)]
        have hnil : scanIriBody (pos + 1 + 1) ('>' :: rest) []
            = ([], pos + 1 + 1 + 0 + 1, rest) := by
          simpa using scanIriBody_printed_nil [] rest (pos + 1 + 1) (by decide)
        rw [hnil]
        simp [processIriEscapes, processIriEscapesRec]
    | cons d body' =>
        have hd : (isAlpha d || d == '_' || d == '/' || d == '#') = true := by
          simpa [iriFirstOk, hb] using hfirst
        have hdlt : ¬ (d = '<') := by intro h; subst h; simp [isAlpha] at hd
        have hdeq : ¬ (d = '=') := by intro h; subst h; simp [isAlpha] at hd
        have hguard : (isAlpha d || d == '>' || d == '_' || d == '/' || d == '#'
            || ((d == '?' || d == '$') && hasGtBeforeTerminator (d :: body'
                 ++ '>' :: rest))) = true := by
          have h1 : isAlpha d = true ∨ (d == '_') = true ∨ (d == '/') = true
              ∨ (d == '#') = true := by
            simp only [Bool.or_eq_true] at hd
            rcases hd with ((h | h) | h) | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
          rcases h1 with h | h | h | h <;> simp [h]
        simp only [hb, List.cons_append]
        rw [nextToken_sp_lt pos d (body' ++ ['>'] ++ rest) hdlt hdeq]
        simp only [nextToken.ltCase]
        have hcat : d :: (body' ++ ['>'] ++ rest) = (d :: body') ++ '>' :: rest := by
          simp
        rw [hcat]
        rw [if_pos (by rw [← hcat] at hguard ⊢; exact hguard)]
        rw [scanIriBody_printed_nil (d :: body') rest (pos + 1 + 1)
              (by rw [← hb]; exact hplain)]
        rw [show processIriEscapes (d :: body') = d :: body' by
              rw [← hb]; exact hesc]
  exact ⟨by rw [hkey], by rw [hkey]⟩

/-! ## 6. The chunk list of a printed query

Each chunk carries its LEADING separator, because `nextToken` calls
`skipWs` first. -/

def chunksOfSubject : PatternSubject → List (Token × List Char)
  | .iri i => [(.iri i.val, ' ' :: '<' :: (i.val.toList ++ ['>']))]
  | .var v => [(.var v, ' ' :: '?' :: v.toList)]
  | _ => []

def chunksOfTerm : PatternTerm → List (Token × List Char)
  | .iri i => [(.iri i.val, ' ' :: '<' :: (i.val.toList ++ ['>']))]
  | .var v => [(.var v, ' ' :: '?' :: v.toList)]
  | _ => []

def chunksOfTriple (tp : TriplePattern) : List (Token × List Char) :=
  chunksOfSubject tp.s ++ chunksOfTerm tp.p ++ chunksOfTerm tp.o
    ++ [(.dot, [' ', '.'])]

def chunksOfBgp : Bgp → List (Token × List Char)
  | [] => []
  | tp :: rest => chunksOfTriple tp ++ chunksOfBgp rest

def chunksOfQuery (q : Query) : List (Token × List Char) :=
  match q.pattern with
  | .bgp b => (.ask, ['A', 'S', 'K']) :: (.lbrace, [' ', '{']) :: chunksOfBgp b
                ++ [(.rbrace, [' ', '}'])]
  | _ => [(.ask, ['A', 'S', 'K']), (.lbrace, [' ', '{']), (.rbrace, [' ', '}'])]

/-- The chunk tokens ARE the expected tokens, minus the trailing EOF the
tokenizer appends. -/
theorem chunkTokens_bgp : ∀ (b : Bgp),
    (chunksOfBgp b).map (·.1) = tokensOfBgp b
  | [] => rfl
  | tp :: rest => by
      simp only [chunksOfBgp, tokensOfBgp, List.map_append,
                 chunkTokens_bgp rest]
      congr 1
      cases hs : tp.s <;> cases hp : tp.p <;> cases ho : tp.o
        <;> simp [chunksOfTriple, tokensOfTriple, chunksOfSubject, chunksOfTerm,
                  tokensOfSubject, tokensOfTerm, hs, hp, ho]

theorem chunkTokens_query (q : Query) :
    (chunksOfQuery q).map (·.1) ++ [Token.eof] = expectedTokens q := by
  simp only [chunksOfQuery, expectedTokens]
  cases hp : q.pattern <;> simp [chunkTokens_bgp]

/-! ## 7. The chunks concatenate to the printed string -/

/-- The shape half of the fragment predicate: every position is an IRI
or a variable. This is what the printer and the chunk list need; the
reserved-IRI half of `bgpInFragment` is a parser concern. -/
def subjShapeOk : PatternSubject → Bool
  | .iri _ => true
  | .var _ => true
  | _ => false

def termShapeOk : PatternTerm → Bool
  | .iri _ => true
  | .var _ => true
  | _ => false

def tripleShapeOk (tp : TriplePattern) : Bool :=
  subjShapeOk tp.s && termShapeOk tp.p && termShapeOk tp.o

def bgpShapeOk (b : Bgp) : Bool := b.all tripleShapeOk

theorem shapeOk_of_inFragment (reserved : List WfIri) : ∀ (b : Bgp),
    bgpInFragment reserved b = true → bgpShapeOk b = true
  | [], _ => rfl
  | tp :: rest, h => by
      simp only [bgpInFragment, List.all_cons, Bool.and_eq_true] at h
      simp only [bgpShapeOk, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, shapeOk_of_inFragment reserved rest (by
        simpa [bgpInFragment] using h.2)⟩
      have := h.1
      simp only [triplePatternInFragment, Bool.and_eq_true] at this
      cases hs : tp.s <;> cases hp : tp.p <;> cases ho : tp.o
        <;> simp_all [tripleShapeOk, subjShapeOk, termShapeOk,
                      subjectInFragment, termInFragment]

theorem chunkChars_triple (tp : TriplePattern) (h : tripleShapeOk tp = true) :
    chunkChars (chunksOfTriple tp) = ' ' :: (printTriple tp).toList := by
  cases hs : tp.s <;> cases hp : tp.p <;> cases ho : tp.o
    <;> simp_all [chunkChars, chunksOfTriple, chunksOfSubject, chunksOfTerm,
                  printTriple, printSubject, printTerm, tripleShapeOk,
                  subjShapeOk, termShapeOk, String.toList_append]

theorem chunkChars_bgp : ∀ (b : Bgp), b ≠ [] → bgpShapeOk b = true →
    chunkChars (chunksOfBgp b) = ' ' :: (printBgp b).toList
  | [tp], _, h => by
      have ht : tripleShapeOk tp = true := by
        simpa [bgpShapeOk] using h
      simpa [chunkChars, chunksOfBgp, printBgp] using chunkChars_triple tp ht
  | tp :: tp2 :: rest, _, h => by
      have ht : tripleShapeOk tp = true := by
        simp only [bgpShapeOk, List.all_cons, Bool.and_eq_true] at h; exact h.1
      have hrest : bgpShapeOk (tp2 :: rest) = true := by
        simp only [bgpShapeOk, List.all_cons, Bool.and_eq_true] at h ⊢
        exact h.2
      have hne : (tp2 :: rest) ≠ [] := by simp
      have hsplit : chunkChars (chunksOfBgp (tp :: tp2 :: rest))
          = chunkChars (chunksOfTriple tp) ++ chunkChars (chunksOfBgp (tp2 :: rest)) := by
        simp [chunkChars, chunksOfBgp, List.map_append, List.flatten_append]
      rw [hsplit, chunkChars_triple tp ht, chunkChars_bgp (tp2 :: rest) hne hrest]
      simp [printBgp, String.toList_append]

theorem chunkChars_query (q : Query) (b : Bgp) (hq : q.pattern = .bgp b)
    (hb : b ≠ []) (hs : bgpShapeOk b = true) :
    chunkChars (chunksOfQuery q) = (printQuery q).toList := by
  have hsplit : chunkChars (chunksOfQuery q)
      = ['A', 'S', 'K'] ++ [' ', '{'] ++ chunkChars (chunksOfBgp b)
        ++ [' ', '}'] := by
    simp [chunksOfQuery, hq, chunkChars, List.map_append, List.flatten_append]
  rw [hsplit, chunkChars_bgp b hb hs]
  simp [printQuery, hq, String.toList_append]

/-! ## 8. Every chunk is lexable

The side conditions, gathered. `iriBodyPlain` is §19.8 [139]'s own rule;
`iriFirstOk` is this lexer's narrower one (issue 573); `varNamePlain`
plus non-emptiness is [143] VAR1. -/

def subjLexable : PatternSubject → Bool
  | .iri i => iriBodyPlain i.val.toList && iriFirstOk i.val.toList
  | .var v => varNamePlain v.toList && !v.toList.isEmpty
  | _ => false

def termLexable : PatternTerm → Bool
  | .iri i => iriBodyPlain i.val.toList && iriFirstOk i.val.toList
  | .var v => varNamePlain v.toList && !v.toList.isEmpty
  | _ => false

def tripleLexable (tp : TriplePattern) : Bool :=
  subjLexable tp.s && termLexable tp.p && termLexable tp.o

def bgpLexable (b : Bgp) : Bool := b.all tripleLexable

theorem lexable_shapeOk : ∀ (b : Bgp), bgpLexable b = true → bgpShapeOk b = true
  | [], _ => rfl
  | tp :: rest, h => by
      simp only [bgpLexable, List.all_cons, Bool.and_eq_true] at h
      simp only [bgpShapeOk, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, lexable_shapeOk rest (by simpa [bgpLexable] using h.2)⟩
      have := h.1
      cases hs : tp.s <;> cases hp : tp.p <;> cases ho : tp.o
        <;> simp_all [tripleLexable, tripleShapeOk, subjLexable, termLexable,
                      subjShapeOk, termShapeOk]

/-- Every chunk of a lexable subject or term lexes to its token, is not
EOF, and starts with the separator every following chunk needs. -/
theorem chunks_sep_cons (parts : List (Token × List Char))
    (h : ∀ p ∈ parts, ∃ r, p.2 = ' ' :: r) : SepStart (chunkChars parts) := by
  cases hp : parts with
  | nil => intro c hc; simp [chunkChars, hp] at hc
  | cons p rest =>
      obtain ⟨r, hr⟩ := h p (by simp [hp])
      intro c hc
      simp only [chunkChars, hp, List.map_cons, List.flatten_cons, hr,
                 List.cons_append, List.head?_cons, Option.mem_def,
                 Option.some.injEq] at hc
      exact hc.symm

theorem chunksOfBgp_sepStart : ∀ (b : Bgp),
    ∀ p ∈ chunksOfBgp b, ∃ r, p.2 = ' ' :: r
  | [], p, hp => by simp [chunksOfBgp] at hp
  | tp :: rest, p, hp => by
      simp only [chunksOfBgp, List.mem_append] at hp
      rcases hp with hp | hp
      · simp only [chunksOfTriple, List.mem_append] at hp
        rcases hp with ((hp | hp) | hp) | hp
        · cases hs : tp.s <;> simp_all [chunksOfSubject] <;> exact ⟨_, rfl⟩
        · cases hs : tp.p <;> simp_all [chunksOfTerm] <;> exact ⟨_, rfl⟩
        · cases hs : tp.o <;> simp_all [chunksOfTerm] <;> exact ⟨_, rfl⟩
        · simp at hp; subst hp; exact ⟨['.'], rfl⟩
      · exact chunksOfBgp_sepStart rest p hp

theorem chunksOk_bgp : ∀ (b : Bgp), bgpLexable b = true →
    (∀ p ∈ chunksOfBgp b, LexesTo p.1 p.2 ∧ p.1 ≠ .eof)
  | [], _, p, hp => by simp [chunksOfBgp] at hp
  | tp :: rest, h, p, hp => by
      simp only [bgpLexable, List.all_cons, Bool.and_eq_true] at h
      simp only [chunksOfBgp, List.mem_append] at hp
      rcases hp with hp | hp
      · have ht := h.1
        simp only [tripleLexable, Bool.and_eq_true] at ht
        simp only [chunksOfTriple, List.mem_append] at hp
        rcases hp with ((hp | hp) | hp) | hp
        · cases hs : tp.s with
          | iri i =>
              simp only [chunksOfSubject, hs, List.mem_singleton] at hp
              subst hp
              have hl : iriBodyPlain i.val.toList = true
                  ∧ iriFirstOk i.val.toList = true := by
                have := ht.1.1; rw [hs] at this
                simpa [subjLexable, Bool.and_eq_true] using this
              exact ⟨by simpa using lexes_iri i.val.toList hl.1 hl.2, by simp⟩
          | var v =>
              simp only [chunksOfSubject, hs, List.mem_singleton] at hp
              subst hp
              have hl : varNamePlain v.toList = true ∧ v.toList ≠ [] := by
                have := ht.1.1; rw [hs] at this
                simp only [subjLexable, Bool.and_eq_true] at this
                exact ⟨this.1, by simpa using this.2⟩
              exact ⟨by simpa using lexes_var v.toList hl.1 hl.2, by simp⟩
          | _ => simp_all [chunksOfSubject]
        · cases hs : tp.p with
          | iri i =>
              simp only [chunksOfTerm, hs, List.mem_singleton] at hp
              subst hp
              have hl : iriBodyPlain i.val.toList = true
                  ∧ iriFirstOk i.val.toList = true := by
                have := ht.1.2; rw [hs] at this
                simpa [termLexable, Bool.and_eq_true] using this
              exact ⟨by simpa using lexes_iri i.val.toList hl.1 hl.2, by simp⟩
          | var v =>
              simp only [chunksOfTerm, hs, List.mem_singleton] at hp
              subst hp
              have hl : varNamePlain v.toList = true ∧ v.toList ≠ [] := by
                have := ht.1.2; rw [hs] at this
                simp only [termLexable, Bool.and_eq_true] at this
                exact ⟨this.1, by simpa using this.2⟩
              exact ⟨by simpa using lexes_var v.toList hl.1 hl.2, by simp⟩
          | _ => simp_all [chunksOfTerm]
        · cases hs : tp.o with
          | iri i =>
              simp only [chunksOfTerm, hs, List.mem_singleton] at hp
              subst hp
              have hl : iriBodyPlain i.val.toList = true
                  ∧ iriFirstOk i.val.toList = true := by
                have := ht.2; rw [hs] at this
                simpa [termLexable, Bool.and_eq_true] using this
              exact ⟨by simpa using lexes_iri i.val.toList hl.1 hl.2, by simp⟩
          | var v =>
              simp only [chunksOfTerm, hs, List.mem_singleton] at hp
              subst hp
              have hl : varNamePlain v.toList = true ∧ v.toList ≠ [] := by
                have := ht.2; rw [hs] at this
                simp only [termLexable, Bool.and_eq_true] at this
                exact ⟨this.1, by simpa using this.2⟩
              exact ⟨by simpa using lexes_var v.toList hl.1 hl.2, by simp⟩
          | _ => simp_all [chunksOfTerm]
        · simp at hp; subst hp; exact ⟨lexes_dot, by simp⟩
      · exact chunksOk_bgp rest (by simpa [bgpLexable] using h.2) p hp

/-! ## 9. `ChunksOk` for a whole query -/

theorem chunksOk_of_pairwise (parts : List (Token × List Char))
    (hlex : ∀ p ∈ parts, LexesTo p.1 p.2 ∧ p.1 ≠ .eof)
    (hsep : ∀ p ∈ parts, ∃ r, p.2 = ' ' :: r) : ChunksOk parts := by
  induction parts with
  | nil => trivial
  | cons p rest ih =>
      refine ⟨(hlex p (by simp)).1, (hlex p (by simp)).2, ?_,
        ih (fun q hq => hlex q (by simp [hq])) (fun q hq => hsep q (by simp [hq]))⟩
      exact chunks_sep_cons rest (fun q hq => hsep q (by simp [hq]))

theorem chunksOk_query (q : Query) (b : Bgp) (hq : q.pattern = .bgp b)
    (hl : bgpLexable b = true) : ChunksOk (chunksOfQuery q) := by
  have hbody : ∀ p ∈ chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])],
      LexesTo p.1 p.2 ∧ p.1 ≠ .eof := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact chunksOk_bgp b hl p hp
    · simp at hp; subst hp; exact ⟨lexes_rbrace, by simp⟩
  have hbodysep : ∀ p ∈ chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])],
      ∃ r, p.2 = ' ' :: r := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact chunksOfBgp_sepStart b p hp
    · simp at hp; subst hp; exact ⟨['}'], rfl⟩
  have htail : ChunksOk (chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])]) :=
    chunksOk_of_pairwise _ hbody hbodysep
  have hsep2 : SepStart (chunkChars (chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])])) :=
    chunks_sep_cons _ hbodysep
  have hlb : ChunksOk ((Token.lbrace, [' ', '{']) ::
      (chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])])) :=
    ⟨lexes_lbrace, by simp, hsep2, htail⟩
  have hsep1 : SepStart (chunkChars ((Token.lbrace, [' ', '{']) ::
      (chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])]))) := by
    intro c hc
    simp only [chunkChars, List.map_cons, List.flatten_cons, List.cons_append,
               List.head?_cons, Option.mem_def, Option.some.injEq] at hc
    exact hc.symm
  have hall : ChunksOk ((Token.ask, ['A', 'S', 'K']) :: (Token.lbrace, [' ', '{']) ::
      (chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])])) :=
    ⟨lexes_ask, by simp, hsep1, hlb⟩
  have heq : chunksOfQuery q = (Token.ask, ['A', 'S', 'K']) ::
      (Token.lbrace, [' ', '{']) :: (chunksOfBgp b ++ [(Token.rbrace, [' ', '}'])]) := by
    simp [chunksOfQuery, hq]
  rw [heq]; exact hall

/-- Every chunk of a well-formed chunk list is non-empty — what the fuel
bound in the main theorem needs. -/
theorem chunksOk_ne : ∀ (parts : List (Token × List Char)), ChunksOk parts →
    ∀ p ∈ parts, p.2 ≠ []
  | [], _, p, hp => by simp at hp
  | q :: rest, h, p, hp => by
      obtain ⟨hlex, _, _, hrest⟩ := h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hlex.1
      · exact chunksOk_ne rest hrest p hp

/-! ## 10. The theorem

`SPARQL11.Parser.AskBgpRoundTrip.fst` reaches this statement, declares
it IMPOSSIBLE, and proves the impossibility with a counter-probe against
`FStar.String.sub`'s interface. Here it is a theorem. -/

/-- **The string round trip.** Print a query in the fragment, tokenize
the result, and you get back exactly the tokens the query denotes.

The hypotheses are the fragment: an ASK over a non-empty BGP whose every
position is an IRI or a variable, whose IRI bodies carry no `>` and no
`\\` and start with a character the lexer's `<` disambiguation accepts
(⚠️ narrower than §19.8 [139] — issue 573), and whose variable names are
non-empty [143] VAR1 names. -/
theorem askBgp_string_roundtrip (q : Query) (b : Bgp)
    (hq : q.pattern = .bgp b) (hb : b ≠ []) (hl : bgpLexable b = true) :
    (tokenize (printQuery q)).map (·.tok) = expectedTokens q := by
  have hshape : bgpShapeOk b = true := lexable_shapeOk b hl
  have hchars : chunkChars (chunksOfQuery q) = (printQuery q).toList :=
    chunkChars_query q b hq hb hshape
  have hok : ChunksOk (chunksOfQuery q) := chunksOk_query q b hq hl
  have hfuel : (chunksOfQuery q).length < (printQuery q).toList.length + 1 := by
    rw [← hchars]
    have hlen : ∀ (parts : List (Token × List Char)),
        (∀ p ∈ parts, p.2 ≠ []) → parts.length ≤ (chunkChars parts).length := by
      intro parts
      induction parts with
      | nil => intro _; simp [chunkChars]
      | cons p rest ih =>
          intro hne
          have h1 : 0 < p.2.length :=
            List.length_pos_iff.mpr (hne p (by simp))
          have h2 := ih (fun q hq => hne q (by simp [hq]))
          simp only [chunkChars, List.map_cons, List.flatten_cons,
                     List.length_append, List.length_cons] at *
          omega
    have hne : ∀ p ∈ chunksOfQuery q, p.2 ≠ [] := by
      intro p hp
      exact chunksOk_ne (chunksOfQuery q) hok p hp
    have := hlen (chunksOfQuery q) hne
    omega
  rw [tokenize, ← hchars,
      tokenizeLoop_chunks (chunksOfQuery q) _ 0 [] hok (by rw [hchars]; exact hfuel)]
  simpa using chunkTokens_query q

/-! ## Build-time checks

The theorem's hypotheses, exercised. -/

private def rS : WfIri := ⟨"http://example.org/s", by decide⟩
private def rP : WfIri := ⟨"http://example.org/p", by decide⟩
private def rtp : TriplePattern := { s := .iri rS, p := .iri rP, o := .var "o" }
private def rq : Query := mkQuery .ask (.bgp [rtp])

#guard bgpLexable [rtp] == true
#guard (tokenize (printQuery rq)).map (·.tok) == expectedTokens rq

/-! ⚠️ An IRI starting with a digit is a valid IRIREF and is NOT lexable
by this engine — the theorem's `iriFirstOk` side condition, and issue
573. -/
private def rBad : WfIri := ⟨"1abc:x", by decide⟩
#guard iriBodyPlain rBad.val.toList == true
#guard iriFirstOk rBad.val.toList == false
#guard termLexable (PatternTerm.iri rBad) == false

/-! And the engine really does mis-lex it, which is why the side
condition is not a proof convenience. -/
private def rqBad : Query :=
  mkQuery .ask (.bgp [{ s := .iri rBad, p := .iri rP, o := .var "o" }])
#guard ((tokenize (printQuery rqBad)).map (·.tok) == expectedTokens rqBad) == false

/-! An empty variable name is not lexable either: `?` alone is `qmark`. -/
#guard termLexable (PatternTerm.var "") == false
#guard varNamePlain "ok_1".toList == true

/-! ## Axiom audit -/

#print axioms lexes_ask
#print axioms lexes_iri
#print axioms lexes_var
#print axioms tokenizeLoop_chunks
#print axioms chunkChars_query
#print axioms askBgp_string_roundtrip

end L4Factoidal.SPARQL.AskBgpRoundTrip
