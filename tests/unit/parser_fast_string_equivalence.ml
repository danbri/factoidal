(* parser_fast_string_equivalence.ml -- FastString re-founding Step 3
   equivalence obligation (docs/designissues/
   2026-08-10-faststring-refounding-plan.md).

   Parser.FastString.fst (Step 2) re-founded fs_byte_length, fs_byte_at,
   fs_byte_sub, fs_find_byte, fs_cp_at, fs_cp_len as real
   Parser.FastString.Spec-backed definitions. Step 3's
   experimental_ocaml_glue/parser_faststring_ops_runtime.sh overrides
   each `fs_*` with a fast OCaml body (the same one the old patch 89
   used against the pre-migration assume vals), while `fs_*_spec` stays
   bound to the untouched, independently-F*-verified Spec definition.

   This file is the equivalence obligation the plan requires before that
   speed-up can be trusted: fs_op(x) == fs_op_spec(x) on every generated
   input. Style follows parser_fast_string_byte_semantics.ml /
   parser_fast_string_codepoint_semantics.ml (PASS/XFAIL/FAIL bucketed
   summary, deterministic, no external dependencies beyond
   Parser_FastString and the stdlib). *)

let passed = ref 0
let failed = ref 0
let expected_failures = ref 0

let check ~name ~expected_pass ok_bool =
  if ok_bool then begin
    incr passed
    (* Quiet on PASS -- thousands of generated rows would otherwise
       drown the summary. Only the per-generator totals print. *)
  end else if not expected_pass then begin
    incr expected_failures
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name
  end

(* ------------------------------------------------------------------ *)
(* Deterministic RNG -- fixed seed so a re-run reproduces the same     *)
(* generated corpus (and the same failing case, if any, for a repro). *)
(* ------------------------------------------------------------------ *)

let () = Random.init 20260810

(* ------------------------------------------------------------------ *)
(* A standalone RFC 3629 UTF-8 encoder, used ONLY to build test         *)
(* fixtures (valid multi-byte strings with KNOWN codepoint boundaries). *)
(* This is fixture generation, not product logic -- Parser.FastString   *)
(* itself is never consulted while building inputs.                     *)
(* ------------------------------------------------------------------ *)

let encode_cp (cp : int) : string =
  let b = Buffer.create 4 in
  if cp < 0x80 then
    Buffer.add_char b (Char.chr cp)
  else if cp < 0x800 then begin
    Buffer.add_char b (Char.chr (0xC0 lor (cp lsr 6)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end else if cp < 0x10000 then begin
    Buffer.add_char b (Char.chr (0xE0 lor (cp lsr 12)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end else begin
    Buffer.add_char b (Char.chr (0xF0 lor (cp lsr 18)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end;
  Buffer.contents b

(* Random codepoint drawn from one of the four RFC 3629 length classes,
   avoiding the UTF-16 surrogate gap (never a valid scalar value). *)
let random_valid_cp () =
  match Random.int 4 with
  | 0 -> Random.int 0x80                                (* 1-byte ASCII *)
  | 1 -> 0x80 + Random.int (0x800 - 0x80)                (* 2-byte *)
  | 2 ->
    (* 3-byte, skip the surrogate range D800..DFFF. *)
    let cp = 0x800 + Random.int (0x10000 - 0x800) in
    if cp >= 0xD800 && cp <= 0xDFFF then 0xE000 + (cp - 0xD800) else cp
  | _ -> 0x10000 + Random.int (0x110000 - 0x10000)       (* 4-byte astral *)

(* A random valid multi-byte string of `n` codepoints, plus the list of
   BYTE-BOUNDARY offsets after each codepoint (0 included as the first
   boundary) -- used to pick boundary-aligned fs_byte_sub probes without
   re-deriving boundaries via the engine under test. *)
let random_valid_string (n : int) : string * int list =
  let buf = Buffer.create 64 in
  let boundaries = ref [0] in
  for _ = 1 to n do
    let enc = encode_cp (random_valid_cp ()) in
    Buffer.add_string buf enc;
    boundaries := Buffer.length buf :: !boundaries
  done;
  (Buffer.contents buf, List.rev !boundaries)

let random_ascii_string (n : int) : string =
  String.init n (fun _ -> Char.chr (0x20 + Random.int (0x7E - 0x20 + 1)))

(* ------------------------------------------------------------------ *)
(* Adversarial invalid UTF-8 fixtures -- truncated tails, bare          *)
(* continuation bytes, overlong encodings, surrogate encodings, and    *)
(* 0xF5-0xFF leads. Fixed corpus (not randomly generated: the point is  *)
(* to hit every RFC 3629 rejection branch at least once, and a fixed    *)
(* list is the more legible executable record of that intent).         *)
(* ------------------------------------------------------------------ *)

let adversarial_snippets : string list = [
  (* Truncated tails: a valid multi-byte lead with 1..N-1 of its
     continuation bytes missing. *)
  "\xC3";                       (* 2-byte lead, 0 of 1 continuation bytes *)
  "\xE6\x97";                   (* 3-byte lead, 1 of 2 continuation bytes *)
  "\xF0\x9F\x8E";               (* 4-byte lead, 2 of 3 continuation bytes *)
  "\xE0";                       (* 3-byte lead, 0 of 2 continuation bytes *)
  "\xF0";                       (* 4-byte lead, 0 of 3 continuation bytes *)
  (* Bare continuation bytes, no lead byte at all. *)
  "\x80"; "\xBF"; "\x80\x80\x80";
  (* Overlong encodings (reject even though the arithmetic "works"). *)
  "\xC0\x80";                   (* overlong NUL, 2-byte encoding of U+0000 *)
  "\xC1\xBF";                   (* overlong 2-byte encoding of U+007F *)
  "\xE0\x80\x80";               (* overlong 3-byte encoding of U+0000 *)
  "\xF0\x80\x80\x80";           (* overlong 4-byte encoding of U+0000 *)
  (* Surrogate encodings (U+D800..U+DFFF raw-encoded as 3-byte UTF-8;
     invalid per RFC 3629 sec. 3, "Constraints on UTF-8"). *)
  "\xED\xA0\x80";                (* U+D800, low surrogate boundary *)
  "\xED\xAD\xBF";                (* U+D7FF+... mid-range surrogate *)
  "\xED\xBF\xBF";                (* U+DFFF, high surrogate boundary *)
  (* 0xF5-0xFF lead bytes: always invalid (codepoint would exceed
     U+10FFFF or the byte is not a valid UTF-8 lead at all). *)
  "\xF5\x80\x80\x80";
  "\xF8\x88\x80\x80\x80";
  "\xFF";
  "\xFE";
  (* A continuation byte where a lead byte was expected, embedded mid
     valid-looking sequence. *)
  "\xE6\x80\x97\xA5";
]

(* Adversarial fixtures embedded inside a valid prefix/suffix, so
   fs_find_byte / fs_cp_at / fs_cp_len are also exercised at non-zero
   start positions over invalid input, not just at position 0. *)
let embedded_adversarial_strings : string list =
  List.map (fun snip -> "abc:" ^ snip ^ ":xyz") adversarial_snippets

(* ------------------------------------------------------------------ *)
(* Per-string op comparisons.                                          *)
(* ------------------------------------------------------------------ *)

let z = Z.of_int
let zi = Z.to_int

let check_byte_length ~tag s =
  check ~name:(Printf.sprintf "fs_byte_length == fs_byte_length_spec [%s]" tag)
    ~expected_pass:true
    (Z.equal (Parser_FastString.fs_byte_length s) (Parser_FastString.fs_byte_length_spec s))

let check_byte_at ~tag s =
  let len = zi (Parser_FastString.fs_byte_length s) in
  (* In-bounds probes: every position. *)
  for i = 0 to len - 1 do
    check ~name:(Printf.sprintf "fs_byte_at == fs_byte_at_spec [%s] i=%d" tag i)
      ~expected_pass:true
      (Z.equal (Parser_FastString.fs_byte_at s (z i)) (Parser_FastString.fs_byte_at_spec s (z i)))
  done;
  (* Out-of-bounds probes: both must be TOTAL and agree (0), per
     Parser.FastString.fsti's `n:nat{n<256}` refinement and the fast
     realisation's added bounds check (patch 89's original body had no
     bounds check at all -- this is the ONE deliberate behaviour change
     from the pre-migration fast primitive; see the patch's own banner). *)
  List.iter (fun i ->
    check ~name:(Printf.sprintf "fs_byte_at == fs_byte_at_spec (OOB) [%s] i=%d" tag i)
      ~expected_pass:true
      (Z.equal (Parser_FastString.fs_byte_at s (z i)) (Parser_FastString.fs_byte_at_spec s (z i)))
  ) [len; len + 1; len + 1000]

let check_find_byte ~tag s =
  List.iter (fun b ->
    List.iter (fun start ->
      if start >= 0 then
        check ~name:(Printf.sprintf "fs_find_byte == fs_find_byte_spec [%s] b=0x%02x start=%d" tag b start)
          ~expected_pass:true
          (Z.equal
             (Parser_FastString.fs_find_byte s (z b) (z start))
             (Parser_FastString.fs_find_byte_spec s (z b) (z start)))
    ) [0; 1; String.length s / 2; String.length s; String.length s + 5]
  ) [0x00; 0x3A; 0x61; 0xC3; 0xFF]

let check_cp_at_len ~tag s =
  let len = zi (Parser_FastString.fs_byte_length s) in
  for pos = 0 to len do  (* include pos = len (one past end, defensive) *)
    let (cp1, adv1) = Parser_FastString.fs_cp_at s (z pos) in
    let (cp2, adv2) = Parser_FastString.fs_cp_at_spec s (z pos) in
    check ~name:(Printf.sprintf "fs_cp_at == fs_cp_at_spec [%s] pos=%d" tag pos)
      ~expected_pass:true
      (Z.equal cp1 cp2 && Z.equal adv1 adv2);
    check ~name:(Printf.sprintf "fs_cp_len == fs_cp_len_spec [%s] pos=%d" tag pos)
      ~expected_pass:true
      (Z.equal (Parser_FastString.fs_cp_len s (z pos)) (Parser_FastString.fs_cp_len_spec s (z pos)))
  done

(* fs_byte_sub -- ONLY on boundary-aligned, in-bounds slices (the domain
   the migration plan and Parser.FastString.fsti's fs_byte_sub_eq banner
   both scope this equivalence to). `boundaries` is the codepoint-
   boundary offset list threaded in by the caller for strings built by
   random_valid_string / ASCII strings (every offset is a boundary for
   pure ASCII). Off-boundary and adversarial-input rows are recorded
   separately below as documented XFAIL, per the task brief. *)
let check_byte_sub_in_domain ~tag s (boundaries : int list) =
  let arr = Array.of_list boundaries in
  let n = Array.length arr in
  for bi = 0 to n - 1 do
    for bj = bi to n - 1 do
      let start = arr.(bi) in
      let len = arr.(bj) - arr.(bi) in
      check ~name:(Printf.sprintf "fs_byte_sub == fs_byte_sub_spec (boundary-aligned) [%s] start=%d len=%d" tag start len)
        ~expected_pass:true
        (String.equal
           (Parser_FastString.fs_byte_sub s (z start) (z len))
           (Parser_FastString.fs_byte_sub_spec s (z start) (z len)))
    done
  done

(* Off-domain XFAIL rows: fs_byte_sub's fast realisation is a raw byte
   copy (patch 89's original behaviour, unchanged by Step 3 -- it was
   never given a decode-reencode treatment because the whole point of
   the byte-level primitives is to stay byte-level); fs_byte_sub_spec
   decode-reencodes through Parser.FastString.Spec.utf8_decode_all. An
   F* string cannot represent "half a multi-byte character", so slicing
   INSIDE a multi-byte codepoint necessarily makes the two diverge: the
   fast path returns the raw (possibly invalid-as-UTF-8) bytes, the spec
   path decodes what it can and re-encodes U+FFFD replacement characters
   for the rest. This is Parser.FastString.fsti's documented off-domain
   divergence from the plan's "boundary-respecting slice" phrasing, not
   a bug -- recorded here as an explicit XFAIL so it stays visible rather
   than silently un-tested. *)
let check_byte_sub_off_domain () =
  let ab = "\xc3\xa4" ^ "b" in (* "äb" = c3 a4 62, mid-codepoint at offset 1 *)
  check ~name:"fs_byte_sub != fs_byte_sub_spec at a mid-codepoint offset (documented XFAIL)"
    ~expected_pass:false
    (String.equal
       (Parser_FastString.fs_byte_sub ab (z 1) (z 1))
       (Parser_FastString.fs_byte_sub_spec ab (z 1) (z 1)));
  List.iter (fun snip ->
    (* Slicing the whole adversarial (generally invalid-as-UTF-8) snippet
       is off-domain almost by definition: the fast path returns it
       verbatim, the spec path decodes-and-reencodes through the
       replacement-character policy, which is very unlikely to be
       byte-identical to the original invalid bytes. *)
    let len = String.length snip in
    if len > 0 then
      check ~name:(Printf.sprintf "fs_byte_sub != fs_byte_sub_spec on adversarial snippet %S (documented XFAIL)" snip)
        ~expected_pass:false
        (String.equal
           (Parser_FastString.fs_byte_sub snip (z 0) (z len))
           (Parser_FastString.fs_byte_sub_spec snip (z 0) (z len)))
  ) adversarial_snippets

(* ------------------------------------------------------------------ *)
(* Driver.                                                              *)
(* ------------------------------------------------------------------ *)

let run_all_ops ~tag ?boundaries s =
  check_byte_length ~tag s;
  check_byte_at ~tag s;
  check_find_byte ~tag s;
  check_cp_at_len ~tag s;
  (match boundaries with
   | Some bs -> check_byte_sub_in_domain ~tag s bs
   | None -> ())

let () =
  Printf.printf "== parser_fast_string_equivalence ==\n";

  (* Empty string: every op's base case. *)
  run_all_ops ~tag:"empty" ~boundaries:[0] "";

  (* Random ASCII strings -- every byte position is a codepoint
     boundary. *)
  for k = 1 to 200 do
    let n = Random.int 40 in
    let s = random_ascii_string n in
    let boundaries = List.init (n + 1) (fun i -> i) in
    run_all_ops ~tag:(Printf.sprintf "ascii#%d len=%d" k n) ~boundaries s
  done;

  (* Random valid multi-byte UTF-8 strings, with their own known
     codepoint-boundary list. *)
  for k = 1 to 200 do
    let ncp = Random.int 12 in
    let (s, boundaries) = random_valid_string ncp in
    run_all_ops ~tag:(Printf.sprintf "utf8#%d cps=%d" k ncp) ~boundaries s
  done;

  (* Adversarial invalid UTF-8, standalone and embedded in a valid
     prefix/suffix -- fs_byte_length/at/find_byte/cp_at/cp_len must all
     still AGREE between fast and spec (both are total, so both must
     produce the exact same numbers on invalid input too -- only
     fs_byte_sub is scoped to boundary-aligned slices and therefore
     skipped here, see check_byte_sub_off_domain below). *)
  List.iteri (fun k snip ->
    run_all_ops ~tag:(Printf.sprintf "adversarial#%d %S" k snip) snip
  ) adversarial_snippets;
  List.iteri (fun k s ->
    run_all_ops ~tag:(Printf.sprintf "adversarial-embedded#%d %S" k s) s
  ) embedded_adversarial_strings;

  (* Documented off-domain XFAIL rows for fs_byte_sub. *)
  check_byte_sub_off_domain ();

  Printf.printf "summary: %d pass, %d expected-fail, %d unexpected fail\n"
    !passed !expected_failures !failed;
  if !failed > 0 then exit 1
