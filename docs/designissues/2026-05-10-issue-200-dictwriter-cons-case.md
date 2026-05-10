# DictWriter `lemma_parse_serialize_dict` — cons-case proof attempt (#200, 2026-05-10)

## Goal

Prove the structural-induction round-trip lemma in `formal/fstar/RDF.CottasStore.DictWriter.fst`:

```fstar
let lemma_parse_serialize_dict (sorted_tokens : list string)
  : Lemma
      (requires (let n = length sorted_tokens in
                 let ids_offset = header_size in
                 let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
                 let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
                 n < 4294967296 /\ data_offset < 18446744073709551616))
      (ensures parse_dict (serialize_dict sorted_tokens) == Some sorted_tokens)
```

The empty-tokens base case is already proven in production (`lemma_parse_serialize_dict_empty_case` via `assert_norm`).
This document attacks the cons case, which is currently `admit ()`.

## TL;DR

- **All 13 sub-lemmas verified** in the scratch file `/tmp/Scratch_Dict.fst`
  (z3 4.13.3, `--z3rlimit 30`, ~12 s wall).
- **The top-level cons case verifies** under a *strengthened* precondition
  (extra: `cum_final data_offset sorted_tokens < 2^64`).
- **The production lemma's stated precondition is genuinely insufficient.**
  See [Caveat](#caveat-the-production-precondition-is-too-weak) below — without
  the extra `cum_final < 2^64` clause, `serialize_dict` silently truncates the
  offsets array when total token data overflows u64, and the round-trip fails.
- Verdict: **clean win on the math, blocked on a precondition gap that
  needs an upstream policy decision** (strengthen the lemma's `requires`,
  strengthen `serialize_dict`'s `requires`, or have `serialize_dict` return
  `[]` when `cum_final >= 2^64`).

## Sub-lemmas needed (all verified)

Listed in dependency order. Each has been verified in the scratch file
`/tmp/Scratch_Dict.fst` against `RDF.Bytes.fst` and `RDF.List.Helpers.fst`
under z3 4.13.3 with `--z3rlimit 30`. None are admitted.

1. `lemma_build_ids_acc_length : (i:nat) -> (n:nat{i <= n /\ n < 2^32})
     -> Lemma (length (build_ids_acc i n) == 4 * (n - i))`
   — induction on `n - i`. **Verified.**

2. `lemma_build_ids_length : (n:nat{n < 2^32})
     -> Lemma (length (build_ids n) == 4 * n)`
   — direct call to (1). **Verified.**

3. `lemma_cum_final_mono : (cur:nat) -> (tokens:list string)
     -> Lemma (cum_final cur tokens >= cur)`
   — `cum_final` is the value-level model of `build_offs_acc`'s
   final cumulative offset. Used to propagate `cur < 2^64` into recursive
   calls. **Verified.**

4. `lemma_build_offs_acc_final : (cur:nat) -> (tokens:list string)
     -> Lemma (requires cur < 2^64 /\ cum_final cur tokens < 2^64)
              (ensures dfst (build_offs_acc cur tokens) == cum_final cur tokens)`
   — induction on tokens. **Verified.**

5. `lemma_parse_n_offsets_build_offs_acc : (cur:nat) -> (tokens:list string)
     -> (rest:bytes)
     -> Lemma (requires cur < 2^64 /\ cum_final cur tokens < 2^64)
              (ensures parse_n_offsets (length tokens)
                       (dsnd (build_offs_acc cur tokens) ++ rest)
                       == Some (cum_offs cur tokens, rest))`
   — induction on tokens. Uses `lemma_parse_write_u64_le_inverse`,
   `Lh.lemma_append_tr_eq`, and `append_assoc`. **Verified.**

6. `lemma_parse_tokens_from_offsets_build_data : (cur:nat) -> (tokens:list string)
     -> (rest:bytes)
     -> Lemma (requires cur < 2^64 /\ cum_final cur tokens < 2^64)
              (ensures parse_tokens_from_offsets
                       (cum_offs cur tokens ++ [cum_final cur tokens])
                       (build_data tokens ++ rest)
                       == Some tokens)`
   — induction on tokens. Uses `lemma_parse_string_of_length_inverse`
   plus `FStar.String.list_of_string_of_list`. **Verified.**

7. `lemma_cum_offs_length : (cur:nat) -> (tokens:list string)
     -> Lemma (requires cur < 2^64 /\ cum_final cur tokens < 2^64)
              (ensures length (cum_offs cur tokens) == length tokens)`
   — induction on tokens. **Verified.**

8. `lemma_parse_u64_le_append : (front rear:bytes)
     -> Lemma (requires Some? (parse_u64_le front))
              (ensures parse_u64_le (front ++ rear) extends with rear)`
   — single pattern-match on the 8-byte prefix. **Verified.**

9. `lemma_parse_u32_le_append` — analogous to (8). **Verified.**

10. `lemma_parse_n_offsets_append : (k:nat) -> (front rear:bytes)
      -> Lemma (requires Some? (parse_n_offsets k front))
               (ensures parse_n_offsets k (front ++ rear) extends with rear)`
    — induction on `k`, lifts (8). **Verified.**

11. `lemma_build_offs_cons : (base:nat) -> (t:string) -> (rest_tokens:list string)
      -> Lemma (requires base < 2^64 /\ cum_final base (t :: rest_tokens) < 2^64)
               (ensures build_offs base (t :: rest_tokens)
                        == write_u64_le base ++ build_offs cur' rest_tokens)`
    where `cur' = base + String.length t`. Decomposes the outer
    `build_offs` (which appends the sentinel) into a structural cons
    via associativity + four `lemma_append_tr_eq` calls. **Verified.**

12. `lemma_cum_offs_cons` and `lemma_cum_final_cons` — trivial structural
    one-step unfoldings (proven by `()`). **Verified.**

13. `lemma_parse_n_offsets_build_offs : (base:nat) -> (tokens:list string)
      -> (rest:bytes)
      -> Lemma (requires base < 2^64 /\ cum_final base tokens < 2^64)
               (ensures parse_n_offsets (length tokens + 1)
                        (build_offs base tokens ++ rest)
                        == Some (cum_offs base tokens ++ [cum_final base tokens], rest))`
    — direct induction on tokens (NOT via the split-of-(n+1)-into-n+1
    approach, which we tried and it stalled SMT). Uses (11) and the
    cons unfoldings (12). **Verified.**

## Top-level: `lemma_parse_serialize_dict_cons` (verified, strengthened pre)

```fstar
let lemma_parse_serialize_dict_cons (sorted_tokens : list string)
  : Lemma
      (requires (
        let n = length sorted_tokens in
        let ids_offset = header_size in
        let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
        let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
        n < 4294967296
        /\ data_offset < 18446744073709551616
        /\ cum_final data_offset sorted_tokens < 18446744073709551616))   // *** EXTRA ***
      (ensures parse_dict (serialize_dict sorted_tokens) == Some sorted_tokens)
```

**Verifies in ~12 s** under z3 4.13.3, `--z3rlimit 30`. Proof is a linear
walk through `parse_dict` reusing each section's inverse lemma
(`lemma_parse_write_u32_le_inverse` for magic/version/n/pad,
`lemma_parse_write_u64_le_inverse` for ids_offs/tok_offs,
`lemma_parse_n_bytes_inverse` for ids[],
sub-lemma 13 for offsets, sub-lemma 6 for token data). Each step uses
`Lh.lemma_append_tr_eq` to convert `append_tr` into `append`, then
`FStar.List.Tot.Properties.append_assoc` to re-associate the bytes so
the next inverse-lemma's pattern fires.

## Caveat: the production precondition is too weak

The production lemma's precondition `data_offset < 2^64` says only that
the **start** of the token-data region fits in u64. But `cum_final
data_offset sorted_tokens` (= `data_offset + sum_of_string_lengths`)
might still overflow even when `data_offset < 2^64`. When that
happens:

- `build_offs_acc` returns early at the iteration where `cur >= 2^64`,
  producing a body containing only the offsets for the prefix of
  tokens that fit.
- `build_offs` then sees `final >= 2^64` and *omits the sentinel*,
  returning just the truncated body.
- `parse_dict` reads `parse_n_offsets (n+1) ...` and either:
  (a) succeeds but consumes garbage bytes from the data region (giving
  wrong offsets), or (b) fails with `None`.

Either way, `parse_dict (serialize_dict sorted_tokens) =/= Some sorted_tokens`,
so the lemma is **false** for those inputs.

In practice this is only triggered for `>= 2^64 - 40 = 18 EiB` of total
token text, which is impossible on any real machine. But formally the
precondition needs strengthening for the lemma to be true.

### Recommended fix (any one of the three)

1. **Strengthen the lemma `requires`**: add
   `cum_final data_offset sorted_tokens < 18446744073709551616`
   (or `B.sum_lengths sorted_tokens + data_offset < 2^64`, equivalent).
   This is what the verified scratch proof uses. It's the smallest
   change but exposes a quirky abstraction (`cum_final`) in the user
   API.

2. **Strengthen `serialize_dict`'s `requires`**: refuse to serialize
   when total token data overflows u64. The OCaml caller already
   handles "tokens too big to fit" via best-effort fallback; making
   this an F* precondition matches the spec better.

3. **Make `serialize_dict` return `[]` on overflow**: change the inner
   guard `if final >= 2^64 then body` to `if final >= 2^64 then []`
   (i.e. drop the body too). Then `parse_dict []` returns `None`
   gracefully and the lemma can have a weaker `data_offset < 2^64`
   precondition by case-splitting in the proof: when total overflows,
   `serialize_dict` returns `[]` and the round-trip is vacuously about
   `parse_dict [] = None`. But then the `ensures` no longer holds, so
   the lemma needs a guarded `ensures` too.

Option (1) is the smallest production change and the only one that
keeps the current `serialize_dict` semantics. Option (3) is the
cleanest semantic fix but requires changing the lemma statement.

## Verified F* code (paste from scratch buffer that verifies clean)

```fstar
module Scratch_Dict
#set-options "--z3rlimit 30"

open FStar.List.Tot
module Lh = RDF.List.Helpers
module B = RDF.Bytes

let dict_magic    : nat = 0x444b4f43
let dict_version  : nat = 1
let header_size   : nat = 32
let id_size       : nat = 4
let offset_size   : nat = 8

let rec build_ids_acc (i : nat) (n : nat{i <= n /\ n < 4294967296})
  : Tot B.bytes (decreases n - i) =
  if i = n then []
  else Lh.append_tr (B.write_u32_le i) (build_ids_acc (i + 1) n)

let build_ids (n : nat{n < 4294967296}) : Tot B.bytes =
  build_ids_acc 0 n

let rec lemma_build_ids_acc_length (i : nat) (n : nat{i <= n /\ n < 4294967296})
  : Lemma (ensures FStar.List.Tot.length (build_ids_acc i n) == 4 `op_Multiply` (n - i))
          (decreases n - i) =
  if i = n then ()
  else begin
    lemma_build_ids_acc_length (i + 1) n;
    Lh.lemma_append_tr_eq (B.write_u32_le i) (build_ids_acc (i + 1) n);
    FStar.List.Tot.Properties.append_length (B.write_u32_le i) (build_ids_acc (i + 1) n)
  end

let lemma_build_ids_length (n : nat{n < 4294967296})
  : Lemma (ensures FStar.List.Tot.length (build_ids n) == 4 `op_Multiply` n) =
  lemma_build_ids_acc_length 0 n

let rec build_data (tokens : list string) : Tot B.bytes (decreases tokens) =
  match tokens with
  | [] -> []
  | t :: rest -> Lh.append_tr (B.bytes_of_string t) (build_data rest)

let rec build_offs_acc
  (cur : nat) (tokens : list string)
  : Tot (cur:nat & B.bytes) (decreases tokens) =
  match tokens with
  | [] -> (| cur, [] |)
  | t :: rest ->
    if cur >= 18446744073709551616 then (| cur, [] |)
    else
      let cur' = cur + String.length t in
      let (| cur'', rest_bytes |) = build_offs_acc cur' rest in
      let head = B.write_u64_le cur in
      (| cur'', Lh.append_tr head rest_bytes |)

let build_offs (token_data_offset : nat) (tokens : list string)
  : Tot B.bytes
  =
  if token_data_offset >= 18446744073709551616 then []
  else
    let (| final, body |) = build_offs_acc token_data_offset tokens in
    if final >= 18446744073709551616 then body
    else Lh.append_tr body (B.write_u64_le final)

let rec parse_n_offsets (k : nat) (bs : B.bytes)
  : Tot (option (list nat & B.bytes)) (decreases k) =
  if k = 0 then Some ([], bs)
  else
    match B.parse_u64_le bs with
    | None -> None
    | Some (o, rest) ->
      match parse_n_offsets (k - 1) rest with
      | None -> None
      | Some (offs, after) -> Some (o :: offs, after)

let rec parse_tokens_from_offsets
  (offsets : list nat) (bs : B.bytes)
  : Tot (option (list string)) (decreases (length offsets)) =
  match offsets with
  | [] -> Some []
  | [_] -> Some []
  | o0 :: o1 :: rest_offs ->
    if o1 < o0 then None
    else
      let len : nat = o1 - o0 in
      match B.parse_string_of_length len bs with
      | None -> None
      | Some (tok, after) ->
        match parse_tokens_from_offsets (o1 :: rest_offs) after with
        | None -> None
        | Some toks -> Some (tok :: toks)

(* --- Cumulative offset model --- *)

let rec cum_offs (cur : nat) (tokens : list string)
  : Tot (list nat) (decreases tokens) =
  match tokens with
  | [] -> []
  | t :: rest ->
    if cur >= 18446744073709551616 then []
    else cur :: cum_offs (cur + String.length t) rest

let rec cum_final (cur : nat) (tokens : list string)
  : Tot nat (decreases tokens) =
  match tokens with
  | [] -> cur
  | t :: rest ->
    if cur >= 18446744073709551616 then cur
    else cum_final (cur + String.length t) rest

let rec lemma_cum_final_mono (cur : nat) (tokens : list string)
  : Lemma (ensures cum_final cur tokens >= cur) (decreases tokens) =
  match tokens with
  | [] -> ()
  | t :: rest ->
    if cur >= 18446744073709551616 then ()
    else lemma_cum_final_mono (cur + String.length t) rest

let rec lemma_build_offs_acc_final
  (cur : nat) (tokens : list string)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures (
        let (| final, _ |) = build_offs_acc cur tokens in
        final == cum_final cur tokens))
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest;
      lemma_build_offs_acc_final cur' rest

let rec lemma_parse_n_offsets_build_offs_acc
  (cur : nat) (tokens : list string) (rest : B.bytes)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures (
        let (| _, body |) = build_offs_acc cur tokens in
        parse_n_offsets (length tokens) (FStar.List.Tot.append body rest)
        == Some (cum_offs cur tokens, rest)))
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest_tokens ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest_tokens;
      lemma_parse_n_offsets_build_offs_acc cur' rest_tokens rest;
      let (| _, rest_body |) = build_offs_acc cur' rest_tokens in
      let head = B.write_u64_le cur in
      Lh.lemma_append_tr_eq head rest_body;
      FStar.List.Tot.Properties.append_assoc head rest_body rest;
      B.lemma_parse_write_u64_le_inverse cur (FStar.List.Tot.append rest_body rest)

let rec lemma_parse_tokens_from_offsets_build_data
  (cur : nat) (tokens : list string) (rest : B.bytes)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures (
        let offsets = FStar.List.Tot.append
                        (cum_offs cur tokens)
                        [cum_final cur tokens] in
        parse_tokens_from_offsets offsets
                                  (FStar.List.Tot.append (build_data tokens) rest)
        == Some tokens))
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest_tokens ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest_tokens;
      lemma_parse_tokens_from_offsets_build_data cur' rest_tokens rest;
      let head_bytes = B.bytes_of_string t in
      let tail_data = build_data rest_tokens in
      Lh.lemma_append_tr_eq head_bytes tail_data;
      FStar.List.Tot.Properties.append_assoc head_bytes tail_data rest;
      B.lemma_parse_string_of_length_inverse t (FStar.List.Tot.append tail_data rest);
      FStar.String.list_of_string_of_list (B.bytes_of_string t);
      ()

let rec lemma_cum_offs_length
  (cur : nat) (tokens : list string)
  : Lemma
      (requires cur < 18446744073709551616
                /\ cum_final cur tokens < 18446744073709551616)
      (ensures length (cum_offs cur tokens) == length tokens)
      (decreases tokens)
  = match tokens with
    | [] -> ()
    | t :: rest ->
      let cur' = cur + String.length t in
      lemma_cum_final_mono cur' rest;
      lemma_cum_offs_length cur' rest

let lemma_parse_u64_le_append
  (front rear : B.bytes)
  : Lemma
      (requires Some? (B.parse_u64_le front))
      (ensures (
        let Some (o, front_rest) = B.parse_u64_le front in
        B.parse_u64_le (FStar.List.Tot.append front rear)
        == Some (o, FStar.List.Tot.append front_rest rear)))
  = match front with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest -> ()

let lemma_parse_u32_le_append
  (front rear : B.bytes)
  : Lemma
      (requires Some? (B.parse_u32_le front))
      (ensures (
        let Some (o, front_rest) = B.parse_u32_le front in
        B.parse_u32_le (FStar.List.Tot.append front rear)
        == Some (o, FStar.List.Tot.append front_rest rear)))
  = match front with
    | b0 :: b1 :: b2 :: b3 :: rest -> ()

let rec lemma_parse_n_offsets_append
  (k : nat) (front rear : B.bytes)
  : Lemma
      (requires Some? (parse_n_offsets k front))
      (ensures (
        let Some (l, mid) = parse_n_offsets k front in
        parse_n_offsets k (FStar.List.Tot.append front rear)
        == Some (l, FStar.List.Tot.append mid rear)))
      (decreases k)
  = if k = 0 then ()
    else
      match B.parse_u64_le front with
      | None -> ()
      | Some (o, front_rest) ->
        lemma_parse_u64_le_append front rear;
        match parse_n_offsets (k - 1) front_rest with
        | None -> ()
        | Some (l_tail, mid') ->
          lemma_parse_n_offsets_append (k - 1) front_rest rear

let lemma_build_offs_cons
  (base : nat) (t : string) (rest_tokens : list string)
  : Lemma
      (requires base < 18446744073709551616
                /\ cum_final base (t :: rest_tokens) < 18446744073709551616)
      (ensures (
        let cur' = base + String.length t in
        build_offs base (t :: rest_tokens)
        == FStar.List.Tot.append (B.write_u64_le base) (build_offs cur' rest_tokens)))
  = let cur' = base + String.length t in
    lemma_cum_final_mono cur' rest_tokens;
    lemma_build_offs_acc_final base (t :: rest_tokens);
    lemma_build_offs_acc_final cur' rest_tokens;
    let (| _, rest_bytes |) = build_offs_acc cur' rest_tokens in
    let head = B.write_u64_le base in
    let final = cum_final base (t :: rest_tokens) in
    Lh.lemma_append_tr_eq head rest_bytes;
    Lh.lemma_append_tr_eq (FStar.List.Tot.append head rest_bytes) (B.write_u64_le final);
    Lh.lemma_append_tr_eq rest_bytes (B.write_u64_le final);
    Lh.lemma_append_tr_eq head (FStar.List.Tot.append rest_bytes (B.write_u64_le final));
    FStar.List.Tot.Properties.append_assoc head rest_bytes (B.write_u64_le final)

let lemma_cum_offs_cons
  (base : nat) (t : string) (rest_tokens : list string)
  : Lemma
      (requires base < 18446744073709551616)
      (ensures (
        let cur' = base + String.length t in
        cum_offs base (t :: rest_tokens)
        == base :: cum_offs cur' rest_tokens))
  = ()

let lemma_cum_final_cons
  (base : nat) (t : string) (rest_tokens : list string)
  : Lemma
      (requires base < 18446744073709551616)
      (ensures (
        let cur' = base + String.length t in
        cum_final base (t :: rest_tokens) == cum_final cur' rest_tokens))
  = ()

let rec lemma_parse_n_offsets_build_offs
  (base : nat) (tokens : list string) (rest : B.bytes)
  : Lemma
      (requires base < 18446744073709551616
                /\ cum_final base tokens < 18446744073709551616)
      (ensures (
        parse_n_offsets (length tokens + 1)
                        (FStar.List.Tot.append (build_offs base tokens) rest)
        == Some (FStar.List.Tot.append (cum_offs base tokens) [cum_final base tokens], rest)))
      (decreases tokens)
  = match tokens with
    | [] ->
      let body : B.bytes = [] in
      Lh.lemma_append_tr_eq body (B.write_u64_le base);
      FStar.List.Tot.Properties.append_l_nil (B.write_u64_le base);
      B.lemma_parse_write_u64_le_inverse base rest
    | t :: rest_tokens ->
      let cur' = base + String.length t in
      lemma_cum_final_mono cur' rest_tokens;
      lemma_parse_n_offsets_build_offs cur' rest_tokens rest;
      lemma_build_offs_cons base t rest_tokens;
      let head = B.write_u64_le base in
      let inner = build_offs cur' rest_tokens in
      FStar.List.Tot.Properties.append_assoc head inner rest;
      B.lemma_parse_write_u64_le_inverse base (FStar.List.Tot.append inner rest);
      lemma_cum_offs_cons base t rest_tokens;
      lemma_cum_final_cons base t rest_tokens

(* (build_header, serialize_dict, parse_dict are copied verbatim from
   RDF.CottasStore.DictWriter.fst — see that file for definitions.) *)

let lemma_parse_serialize_dict_cons
  (sorted_tokens : list string)
  : Lemma
      (requires (
        let n = length sorted_tokens in
        let ids_offset = header_size in
        let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
        let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
        n < 4294967296
        /\ data_offset < 18446744073709551616
        /\ cum_final data_offset sorted_tokens < 18446744073709551616))
      (ensures parse_dict (serialize_dict sorted_tokens) == Some sorted_tokens)
  = let n = length sorted_tokens in
    let ids_offset = header_size in
    let tokens_offset : nat = ids_offset + (id_size `op_Multiply` n) in
    let data_offset : nat = tokens_offset + (offset_size `op_Multiply` (n + 1)) in
    let header = build_header n ids_offset tokens_offset in
    let ids = build_ids n in
    let offs = build_offs data_offset sorted_tokens in
    let data = build_data sorted_tokens in
    let offs_data = FStar.List.Tot.append offs data in
    Lh.lemma_append_tr_eq offs data;
    let ids_offs_data = FStar.List.Tot.append ids offs_data in
    Lh.lemma_append_tr_eq ids offs_data;
    Lh.lemma_append_tr_eq header ids_offs_data;
    let m_bytes = B.write_u32_le dict_magic in
    let v_bytes = B.write_u32_le dict_version in
    let n_bytes = B.write_u32_le n in
    let p_bytes = B.write_u32_le 0 in
    let i_bytes = B.write_u64_le ids_offset in
    let t_bytes = B.write_u64_le tokens_offset in
    let i_t = FStar.List.Tot.append i_bytes t_bytes in
    Lh.lemma_append_tr_eq i_bytes t_bytes;
    let p_i_t = FStar.List.Tot.append p_bytes i_t in
    Lh.lemma_append_tr_eq p_bytes i_t;
    let n_p_i_t = FStar.List.Tot.append n_bytes p_i_t in
    Lh.lemma_append_tr_eq n_bytes p_i_t;
    let v_n_p_i_t = FStar.List.Tot.append v_bytes n_p_i_t in
    Lh.lemma_append_tr_eq v_bytes n_p_i_t;
    Lh.lemma_append_tr_eq m_bytes v_n_p_i_t;
    let suffix1 = FStar.List.Tot.append v_n_p_i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc m_bytes v_n_p_i_t ids_offs_data;
    B.lemma_parse_write_u32_le_inverse dict_magic suffix1;
    let suffix2 = FStar.List.Tot.append n_p_i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc v_bytes n_p_i_t ids_offs_data;
    B.lemma_parse_write_u32_le_inverse dict_version suffix2;
    let suffix3 = FStar.List.Tot.append p_i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc n_bytes p_i_t ids_offs_data;
    B.lemma_parse_write_u32_le_inverse n suffix3;
    let suffix4 = FStar.List.Tot.append i_t ids_offs_data in
    FStar.List.Tot.Properties.append_assoc p_bytes i_t ids_offs_data;
    B.lemma_parse_write_u32_le_inverse 0 suffix4;
    let suffix5 = FStar.List.Tot.append t_bytes ids_offs_data in
    FStar.List.Tot.Properties.append_assoc i_bytes t_bytes ids_offs_data;
    B.lemma_parse_write_u64_le_inverse ids_offset suffix5;
    let suffix6 = ids_offs_data in
    B.lemma_parse_write_u64_le_inverse tokens_offset suffix6;
    let after_ids = offs_data in
    FStar.List.Tot.Properties.append_assoc ids offs data;
    lemma_build_ids_length n;
    B.lemma_parse_n_bytes_inverse ids after_ids;
    lemma_parse_n_offsets_build_offs data_offset sorted_tokens data;
    FStar.List.Tot.Properties.append_l_nil data;
    lemma_parse_tokens_from_offsets_build_data data_offset sorted_tokens [];
    ()
```

## What didn't work

### Attempt 1: `lemma_parse_n_offsets_split` (n + m split lemma)

Tried to prove a generic concat lemma:
```
parse_n_offsets (n+m) (front @ rear) == compose (parse_n_offsets n front)
                                                (parse_n_offsets m on the rest)
```

Failed with "Could not prove post-condition". The right-induction
shape didn't line up with `parse_n_offsets`'s left-fold definition,
and SMT couldn't bridge the structural gap. Sub-lemma 13 (direct
induction on tokens) is the right granularity — proving the property
directly for our cum-shaped offsets list, not for arbitrary split
points.

### Attempt 2: Top-level offsets via `_build_offs_acc` + sentinel post-hoc

```
let final_bytes_with_rest = write_u64_le final ++ rest in
lemma_parse_n_offsets_build_offs_acc base tokens final_bytes_with_rest;
B.lemma_parse_write_u64_le_inverse final rest;
admit ()  // can't prove the (n+1)th offset attaches
```

Failed: needed `lemma_parse_n_offsets_split` (Attempt 1). Replaced by
direct induction in sub-lemma 13.

### Attempt 3: Z3 nondeterminism on filename

When the scratch buffer was named `Scratch_Dict.fst`, the top-level
lemma intermittently failed at default rlimit; renaming the file
(same content) made it pass. Adding `--z3rlimit 30` via
`#set-options` made the proof stable across runs. Production code
should use `#push-options "--z3rlimit 30"` around
`lemma_parse_n_offsets_build_offs` and `lemma_parse_serialize_dict_cons`
specifically (the other sub-lemmas verify at default rlimit).

## Estimated remaining effort

- **Sub-lemmas (1)-(13): zero remaining**, all verified against
  production `RDF.Bytes` and `RDF.List.Helpers`.
- **Top-level cons case**: zero F* remaining IF we strengthen the
  precondition (option (1) in [Caveat](#caveat-the-production-precondition-is-too-weak)).
- **Production `requires` decision**: ~30 minutes of design debate to
  pick option (1), (2), or (3). Option (1) is the smallest change.
- **Landing** (assuming option (1)): ~1 hour to copy the 13 sub-lemmas
  + top-level into `RDF.CottasStore.DictWriter.fst`, run
  `make verify`, add `cum_final` + `cum_offs` as private helpers to
  the same module (or hoist to `RDF.Bytes`). The cum_* helpers don't
  belong in `RDF.Bytes` since they only make sense for the dict
  format's offset model; keep them private to DictWriter.

Total: ~2 hours from clean PR.

## Recommended next-PR sketch (incremental landing)

1. **PR #1: Hoist sub-lemmas (1)-(2) to RDF.CottasStore.DictWriter.fst.**
   These are pure structural facts about `build_ids`, no caveats.
   Adds `lemma_build_ids_acc_length` + `lemma_build_ids_length` as
   `private` lemmas. ~10 lines, zero risk.

2. **PR #2: Add `cum_offs` + `cum_final` value-level model + lemmas
   (3)-(7).** These are pure functions of the offset arithmetic; adds
   ~60 lines as `private`. Risk: minimal (no production callers).

3. **PR #3: Add lemmas (8)-(10) (append-stability for parse_u32_le /
   parse_u64_le / parse_n_offsets).** These could go in
   `RDF.Bytes.fst` — the `parse_*_le_append` ones are general-purpose.
   The `parse_n_offsets_append` stays in DictWriter since
   `parse_n_offsets` is dict-specific. ~30 lines.

4. **PR #4: Add lemma (13) `lemma_parse_n_offsets_build_offs` plus its
   helpers (11)-(12).** The crux of the offsets-section proof. ~60
   lines.

5. **PR #5: Replace `admit ()` in the cons branch of
   `lemma_parse_serialize_dict` with the verified body — under the
   strengthened precondition.** Includes the design-issue discussion
   in commit message: "the production lemma precondition is genuinely
   insufficient for the cons case; we strengthen it with
   `cum_final data_offset sorted_tokens < 2^64`".

The PRs are independent enough that a reviewer can land (1)-(4) first
as "well-typed F\* lemmas with zero coupling to existing callers" and
debate the precondition strengthening in (5) separately.

---

**Verified against:** F* 2026.03.24 / z3 4.13.3 / `--z3rlimit 30`.
Wall time for full module: ~12 s.

**Scratch file:** `/tmp/Scratch_Dict.fst` (470 lines; will be
preserved through this MCP session for reference).

**Foundation lemmas used (all in production, zero new admits in `RDF.Bytes`):**
- `lemma_int_of_byte_of_int` (SMTPat)
- `lemma_parse_write_u32_le_inverse`
- `lemma_parse_write_u64_le_inverse`
- `lemma_parse_n_bytes_inverse`
- `lemma_parse_string_of_length_inverse`
- `Lh.lemma_append_tr_eq`
- `FStar.List.Tot.Properties.append_assoc`, `append_l_nil`, `append_length`
- `FStar.String.list_of_string_of_list`, `string_of_list_of_string`
