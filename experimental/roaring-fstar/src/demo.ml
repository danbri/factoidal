(* End-to-end demo: build, query, and modify an array container produced
   by F*-extracted code. This is the smallest possible "verified F*
   spec → running native code" demonstration for Phase A.

   Not connected to the existing factoidal RDF tools yet — that needs
   Phase B–J. But it proves the verification + extraction pipeline
   works on this machine, end to end. *)

open Container_Array

let int_of_nat = Z.to_int
let nat_of_int n = Z.of_int n

let print_container label c =
  Printf.printf "%s: [" label;
  let rec go = function
    | [] -> ()
    | [x] -> Printf.printf "%d" (int_of_nat x)
    | x :: rest -> Printf.printf "%d, " (int_of_nat x); go rest
  in
  go c;
  Printf.printf "] (cardinality = %d)\n"
    (int_of_nat (array_cardinality c))

let () =
  Printf.printf "=== Roaring F* Phase A end-to-end demo ===\n\n";

  let empty = array_empty in
  print_container "empty" empty;

  (* Build [42] *)
  let c1 = array_insert empty (nat_of_int 42) in
  print_container "after insert 42" c1;

  (* Inserts go in sorted order *)
  let c2 = array_insert c1 (nat_of_int 7) in
  let c3 = array_insert c2 (nat_of_int 100) in
  let c4 = array_insert c3 (nat_of_int 50) in
  print_container "after inserts 7, 100, 50" c4;

  (* Idempotent insert *)
  let c5 = array_insert c4 (nat_of_int 42) in
  print_container "after re-insert 42 (idempotent)" c5;

  (* Membership *)
  let test_contains x =
    let r = array_contains c5 (nat_of_int x) in
    Printf.printf "  contains %d? %b\n" x r
  in
  Printf.printf "Membership tests on c5:\n";
  test_contains 7;
  test_contains 42;
  test_contains 50;
  test_contains 99;
  test_contains 100;

  (* Remove *)
  let c6 = array_remove c5 (nat_of_int 42) in
  print_container "after remove 42" c6;

  let c7 = array_remove c6 (nat_of_int 999) in
  print_container "after remove 999 (no-op)" c7;

  (* Bigger test: insert 100 distinct values, check cardinality *)
  let big = ref array_empty in
  for i = 0 to 99 do
    big := array_insert !big (nat_of_int (i * 37 mod 65536))
  done;
  Printf.printf "100 inserts of (i*37 mod 65536): cardinality = %d\n"
    (int_of_nat (array_cardinality !big));

  (* Pure-F* popcount and tzcnt — used by Phase B's bitmap container. *)
  Printf.printf "\n=== Bit primitives (pure F*, no assume) ===\n";
  let u64 i = Stdint.Uint64.of_int i in
  let test_popcount label n =
    Printf.printf "  popcount %s = %d\n" label
      (int_of_nat (Bits.popcount_u64 (u64 n)))
  in
  test_popcount "0x0" 0;
  test_popcount "0x1" 1;
  test_popcount "0xFF" 0xFF;
  test_popcount "0xAAAAAAAA" 0xAAAAAAAA;
  test_popcount "0xFFFFFFFF" 0xFFFFFFFF;

  let test_tzcnt label n =
    Printf.printf "  tzcnt %s = %d\n" label
      (int_of_nat (Bits.tzcnt_u64 (u64 n)))
  in
  test_tzcnt "0x0" 0;
  test_tzcnt "0x1" 1;
  test_tzcnt "0x2" 2;
  test_tzcnt "0x100" 0x100;
  test_tzcnt "0x80000000" 0x80000000;

  (* File round-trip via FStar.IO (no `assume val` for I/O). *)
  Printf.printf "\n=== File round-trip via FStar.IO ===\n";
  let path = "/tmp/roaring_demo.txt" in
  let original : Container_Array.array_container =
    [nat_of_int 7; nat_of_int 42; nat_of_int 50; nat_of_int 100]
  in
  Printf.printf "  encoded: \"%s\"\n"
    (IODemo.encode original);
  Printf.printf "  writing to %s ...\n" path;
  IODemo.write_to_file path original;
  Printf.printf "  reading back...\n";
  (match IODemo.read_from_file path with
   | None -> Printf.printf "  FAIL: decode returned None\n"
   | Some restored ->
     let same = (List.length original = List.length restored) &&
                List.for_all2 (fun a b -> Z.equal a b) original restored in
     Printf.printf "  decoded: ";
     print_container "" restored;
     Printf.printf "  matches original? %b\n" same);

  Printf.printf "\n=== Done. F*-extracted Phase A + Bits + IO running. ===\n"
