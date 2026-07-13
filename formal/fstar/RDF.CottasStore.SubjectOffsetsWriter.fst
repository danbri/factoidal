module RDF.CottasStore.SubjectOffsetsWriter

(* Pure-F* serialiser for the COTTAS `.s.offsets` companion file. Issue
   #100 follow-up (2026-07-13), sibling of `RDF.CottasStore.
   OffsetsWriter.fst` (the `.p.offsets` writer). Closes the q3
   subject-point-lookup gap (docs/test-results/competitive-bench.json)
   by recording, per SUBJECT, the CONTIGUOUS global row range that
   subject's rows occupy.

   Why this format is different from (and simpler than) `.p.offsets`:
   `RDF.CottasStore.BaseWriter.fst` sorts every row (s, p, o, g)
   BEFORE serialisation (`bin/factoidal-cli/factoidal_cli.ml`'s
   `cottas_quad_key` orders by `(cq_s, cq_p, cq_o, cq_g)`, subject
   primary). A predicate has 6-ish distinct values scattered across
   every row group (no useful global contiguity), so `.p.offsets` had
   to record a per-(row-group, predicate) row-position LIST. A
   subject, sorted primary, occupies a single CONTIGUOUS global row
   range `[start, end)` -- one (start, end) pair per subject is
   sufficient and exact, no per-row-group breakdown needed. At 91,871
   distinct subjects (gene corpus) that is 91,871 * 16 bytes ~= 1.4MB,
   dramatically smaller than `.p.offsets` scaling would suggest for a
   naive (row-group * key) matrix at subject cardinality.

   Subject IDs are the SAME sorted-lexicographic-rank id-space
   `compound_po_dict_encode path "s" tok` already resolves against the
   on-disk `.s.dict` (see that function's banner comment in
   `RDF.CottasStore.fst`): id `i` is the i'th subject string in
   ascending lexicographic order. Because rows are ALSO globally
   s-sorted, subject id order and row-appearance order coincide, so
   the writer emits ranges in ascending subject-id order simply by
   walking the corpus once and recording each subject's first/last
   row index.

   Rule-#11 scope: same split as `OffsetsWriter`/`PresenceWriter`. The
   16-byte header (magic, version, num_subjects, num_rows_total)
   belongs in F*; so does the round-trip byte layout of the range
   array itself (unlike `.p.offsets`'s per-(rg,pred) bucket-fill,
   which needs OCaml's mutable growable arrays, a flat per-subject
   (start,end) array is naturally producible as a pure F* list -- the
   OCaml companion writer still owns the corpus WALK (I/O-bound column
   decode) and the tok_to_id dictionary lookup, but the byte assembly
   of the range array itself can and does reuse this module's
   `serialize_subject_offsets`.

   On-disk format (little-endian throughout):

     [ magic         : u32   'COTS' = 0x53544f43 (LE) ]
     [ version       : u32   currently 1 ]
     [ num_subjects  : u32 ]
     [ num_rows_total: u32   sanity cross-check against probe_parquet_num_rows ]
                                                        (16 bytes header)
     [ ranges : (u64 start_row, u64 end_row_exclusive) * num_subjects,
                ascending subject-id order, start/end are GLOBAL row
                indices (not per-row-group) ]

   Caller responsibility:
     1. Walk the corpus once (row group order, which is global row
        order), decode the subject column, resolve each token to its
        `.s.dict` id.
     2. Detect subject-value transitions (rows are pre-sorted by
        subject) and record (subject_id, start_row, end_row) triples.
     3. Call `serialize_subject_offsets` with num_subjects,
        num_rows_total, and the ranges list in ascending subject-id
        order.
     4. Write the result via `atomic_write`. *)

open FStar.List.Tot

module Lh = RDF.List.Helpers
module OW = RDF.CottasStore.OffsetsWriter

(* --- Header constants ------------------------------------------------- *)

let cots_magic   : nat = 0x53544f43      (* 'COTS' little-endian *)
let cots_version : nat = 1
let header_size  : nat = 16

(* --- Header builder --------------------------------------------------- *)

let build_header
  (num_subjects   : nat{num_subjects   < 4294967296})
  (num_rows_total : nat{num_rows_total < 4294967296})
  : Tot RDF.Bytes.bytes
  =
  Lh.append_tr (RDF.Bytes.write_u32_le cots_magic)
    (Lh.append_tr (RDF.Bytes.write_u32_le cots_version)
      (Lh.append_tr (RDF.Bytes.write_u32_le num_subjects)
        (RDF.Bytes.write_u32_le num_rows_total)))

(* serialize_subject_offsets_header num_subjects num_rows_total
     Produces the 16-byte `.s.offsets` header. Returns [] on u32
     overflow of either field; the reader checks the same bounds. *)
let serialize_subject_offsets_header
  (num_subjects   : nat)
  (num_rows_total : nat)
  : Tot RDF.Bytes.bytes
  =
  if num_subjects   >= 4294967296 then []
  else if num_rows_total >= 4294967296 then []
  else build_header num_subjects num_rows_total

(* --- Range-array (de)serialisation ------------------------------------ *)

(* Flatten a list of (start, end) row-range pairs into an interleaved
   flat u64 list [s0; e0; s1; e1; ...], reusing `OffsetsWriter`'s
   already-verified u64-list (de)serialiser + round-trip lemma so this
   module doesn't re-derive that proof. *)
let rec flatten_ranges (rs : list (nat & nat)) : Tot (list nat) (decreases rs) =
  match rs with
  | [] -> []
  | (s, e) :: tl -> s :: e :: flatten_ranges tl

let rec unflatten_ranges (xs : list nat) : Tot (option (list (nat & nat))) (decreases xs) =
  match xs with
  | [] -> Some []
  | s :: e :: tl ->
    (match unflatten_ranges tl with
     | None -> None
     | Some rest -> Some ((s, e) :: rest))
  | [_] -> None  // odd-length flat list: malformed, no matching end

let rec lemma_unflatten_flatten (rs : list (nat & nat))
  : Lemma (ensures unflatten_ranges (flatten_ranges rs) == Some rs) (decreases rs)
  = match rs with
    | [] -> ()
    | _ :: tl -> lemma_unflatten_flatten tl

let rec lemma_flatten_length (rs : list (nat & nat))
  : Lemma (ensures FStar.List.Tot.length (flatten_ranges rs)
                  == 2 `op_Multiply` FStar.List.Tot.length rs)
          (decreases rs)
  = match rs with
    | [] -> ()
    | _ :: tl -> lemma_flatten_length tl

(* "All range endpoints in rs satisfy < bound". *)
let rec ranges_all_lt (rs : list (nat & nat)) (bound : nat) : Tot bool (decreases rs) =
  match rs with
  | [] -> true
  | (s, e) :: tl -> s < bound && e < bound && ranges_all_lt tl bound

let rec lemma_flatten_all_lt (rs : list (nat & nat)) (bound : nat)
  : Lemma
      (requires ranges_all_lt rs bound)
      (ensures OW.all_lt (flatten_ranges rs) bound)
      (decreases rs)
  = match rs with
    | [] -> ()
    | _ :: tl -> lemma_flatten_all_lt tl bound

(* --- Top-level serialiser -------------------------------------------- *)

(* serialize_subject_offsets num_subjects num_rows_total ranges
     Produces the full `.s.offsets` file byte sequence.

     Returns [] on u32 overflow of num_subjects / num_rows_total.
     Caller-provided invariants:
       - length ranges = num_subjects
       - ranges is in ascending subject-id order (id `i` is `nth ranges i`)
       - every (start, end) pair satisfies start <= end (contiguity;
         not checked here -- the reader treats end < start defensively
         as an empty range, mirroring `row_positions_count_from_bounds`
         in `RDF.Store.Columnar.OffsetIndex`)
       - every start/end fits in u64. *)
let serialize_subject_offsets
  (num_subjects   : nat)
  (num_rows_total : nat)
  (ranges         : list (nat & nat))
  : Tot RDF.Bytes.bytes
  =
  if num_subjects   >= 4294967296 then []
  else if num_rows_total >= 4294967296 then []
  else
    let header = build_header num_subjects num_rows_total in
    let flat   = flatten_ranges ranges in
    Lh.append_tr header (OW.serialize_u64_list flat)

(* --- Round-trip parser ------------------------------------------------ *)

(* parse_subject_offsets bs
     Inverse of `serialize_subject_offsets`. Reads the COTS header,
     validates magic + version, peels `2 * num_subjects` u64s, and
     unflattens them back into (start, end) pairs.

     Returns None on:
       - magic mismatch ('COTS' = 0x53544f43)
       - version mismatch (currently 1)
       - input shorter than declared
       - odd-length flat range list (malformed) *)
let parse_subject_offsets (bs : RDF.Bytes.bytes)
  : Tot (option (nat & nat & list (nat & nat)))
  =
  match RDF.Bytes.parse_u32_le bs with
  | None -> None
  | Some (m, after_magic) ->
    if not (m = cots_magic) then None
    else
      match RDF.Bytes.parse_u32_le after_magic with
      | None -> None
      | Some (v, after_version) ->
        if not (v = cots_version) then None
        else
          match RDF.Bytes.parse_u32_le after_version with
          | None -> None
          | Some (num_subjects, after_ns) ->
            match RDF.Bytes.parse_u32_le after_ns with
            | None -> None
            | Some (num_rows_total, after_header) ->
              let n_flat : nat = 2 `op_Multiply` num_subjects in
              match OW.parse_n_u64s n_flat after_header with
              | None -> None
              | Some (flat, _trailing) ->
                match unflatten_ranges flat with
                | None -> None
                | Some ranges -> Some (num_subjects, num_rows_total, ranges)

(* --- Round-trip lemma -------------------------------------------------- *)

(* serialize_subject_offsets num_subjects num_rows_total ranges
   round-trips back to (num_subjects, num_rows_total, ranges).

   Preconditions:
   - num_subjects, num_rows_total < 2^32 (else serialize returns []).
   - length ranges == num_subjects.
   - every range endpoint < 2^64 (u64 fits). *)
#push-options "--z3rlimit 30"
let lemma_parse_serialize_subject_offsets
  (num_subjects : nat) (num_rows_total : nat) (ranges : list (nat & nat))
  : Lemma
      (requires num_subjects < 4294967296
                /\ num_rows_total < 4294967296
                /\ FStar.List.Tot.length ranges == num_subjects
                /\ ranges_all_lt ranges 18446744073709551616)
      (ensures parse_subject_offsets
                 (serialize_subject_offsets num_subjects num_rows_total ranges)
               == Some (num_subjects, num_rows_total, ranges))
  = let m = RDF.Bytes.write_u32_le cots_magic in
    let v = RDF.Bytes.write_u32_le cots_version in
    let ns = RDF.Bytes.write_u32_le num_subjects in
    let nr = RDF.Bytes.write_u32_le num_rows_total in
    let flat = flatten_ranges ranges in
    let flat_b = OW.serialize_u64_list flat in
    (* Bridge build_header's append_tr chain to FStar.List.Tot.append. *)
    Lh.lemma_append_tr_eq ns nr;
    Lh.lemma_append_tr_eq v (Lh.append_tr ns nr);
    Lh.lemma_append_tr_eq m (Lh.append_tr v (Lh.append_tr ns nr));
    let header = build_header num_subjects num_rows_total in
    Lh.lemma_append_tr_eq header flat_b;
    (* Re-associate: header @ flat_b == m @ (v @ (ns @ (nr @ flat_b))). *)
    FStar.List.Tot.Properties.append_assoc m
      (FStar.List.Tot.append v (FStar.List.Tot.append ns nr)) flat_b;
    FStar.List.Tot.Properties.append_assoc v
      (FStar.List.Tot.append ns nr) flat_b;
    FStar.List.Tot.Properties.append_assoc ns nr flat_b;
    (* Peel four header u32s. *)
    RDF.Bytes.lemma_parse_write_u32_le_inverse cots_magic
      (FStar.List.Tot.append v
        (FStar.List.Tot.append ns
          (FStar.List.Tot.append nr flat_b)));
    RDF.Bytes.lemma_parse_write_u32_le_inverse cots_version
      (FStar.List.Tot.append ns
        (FStar.List.Tot.append nr flat_b));
    RDF.Bytes.lemma_parse_write_u32_le_inverse num_subjects
      (FStar.List.Tot.append nr flat_b);
    RDF.Bytes.lemma_parse_write_u32_le_inverse num_rows_total flat_b;
    (* Peel the flat u64 range list. *)
    lemma_flatten_all_lt ranges 18446744073709551616;
    OW.lemma_parse_n_u64s_serialize_u64_list flat [];
    FStar.List.Tot.Properties.append_l_nil flat_b;
    lemma_flatten_length ranges;
    lemma_unflatten_flatten ranges
#pop-options
