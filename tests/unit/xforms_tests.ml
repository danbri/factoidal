(* xforms_tests.ml — spec-cited regression battery for the XForms
   model-layer bind/recalculation engine (XForms.Bind.fst, Stage 2 of
   docs/designissues/2026-07-05-xforms-model-program-plan.md).

   Every case names the XForms 1.1 (https://www.w3.org/TR/xforms11/)
   section it exercises. No machine-checkable public XForms model-layer
   conformance corpus exists (the program plan says so, and XForms
   conformance suites test the UI/submission layers this program does
   NOT build), so this file IS the conformance signal for Stage 2 —
   scored "N pass, N fail (out of K)" per CLAUDE.md rule #25.

   This is a CONSUMER: it does I/O (printing) and value comparison
   only. All recalc/bind/type/cycle logic lives in XForms.Bind.fst and
   is reached through the extracted module (Iron Rule #7). No XForms
   semantics are implemented here. *)

module XB = XForms_Bind
module PX = Parser_XML

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if String.equal expected actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %S got %S\n" name expected actual
  end

let check_bool ~name expected actual =
  check ~name (if expected then "true" else "false") (if actual then "true" else "false")

let doc_of (xml : string) : PX.xml_node =
  match PX.parse_xml_document xml with
  | FStar_Pervasives_Native.Some n -> n
  | FStar_Pervasives_Native.None -> failwith ("fixture failed to parse: " ^ xml)

(* ------------------------------------------------------------------ *)
(* Small helpers to build binds without wrestling the record labels    *)
(* in every case.                                                      *)
(* ------------------------------------------------------------------ *)

let some s = FStar_Pervasives_Native.Some s
let none = FStar_Pervasives_Native.None

let bind ?(calc=none) ?(cons=none) ?(rel=none) ?(req=none) ?(ro=none)
         ?(ty=XB.MipTypeNone) ~target () : XB.xf_bind =
  { XB.bind_id = target;
    XB.bind_target = target;
    XB.bind_calculate = calc;
    XB.bind_constraint = cons;
    XB.bind_relevant = rel;
    XB.bind_required = req;
    XB.bind_readonly = ro;
    XB.bind_type = ty }

(* Run recalculate; None means "document error" (cycle / unparseable). *)
let recalc binds doc = XB.recalculate binds doc

(* Look up a node's post-recalc value in a validity report list. *)
let rec find_validity target = function
  | [] -> None
  | nv :: rest ->
    if String.equal nv.XB.nv_target target then Some nv
    else find_validity target rest

let leaf_value doc name = XB.get_leaf_text doc name

(* ================================================================== *)
(* §7.6 calculate — a dependency chain a -> b -> c recomputes in order *)
(* ================================================================== *)
(* Instance: <data><a>2</a><b/><c/></data>.  b calculates ../a * 10,
   c calculates ../b + 1.  Topologically c depends on b depends on a,
   so after recalc b=20, c=21 regardless of the bind list order given.  *)

let test_calc_chain () =
  let doc = doc_of "<data><a>2</a><b>0</b><c>0</c></data>" in
  (* Deliberately supply the binds OUT of dependency order (c before b)
     to prove the engine topologically sorts rather than trusting the
     input order — XForms 1.1 §7.6.1. *)
  let binds = [
    bind ~target:"c" ~calc:(some "../b + 1") ();
    bind ~target:"b" ~calc:(some "../a * 10") ();
  ] in
  match recalc binds doc with
  | FStar_Pervasives_Native.None ->
    check ~name:"§7.6 calculate chain a->b->c (recalc must succeed)" "ok" "document-error"
  | FStar_Pervasives_Native.Some (doc2, _report) ->
    check ~name:"§7.6 calculate b = ../a * 10 = 20" "20" (leaf_value doc2 "b");
    check ~name:"§7.6.1 calculate c = ../b + 1 = 21 (b computed first)" "21" (leaf_value doc2 "c")

(* ================================================================== *)
(* §7.6.1 recalculation ORDER — a diamond a -> {b,c} -> d              *)
(* ================================================================== *)

let test_calc_diamond () =
  let doc = doc_of "<data><a>3</a><b>0</b><c>0</c><d>0</d></data>" in
  let binds = [
    bind ~target:"d" ~calc:(some "../b + ../c") ();
    bind ~target:"b" ~calc:(some "../a + 1") ();
    bind ~target:"c" ~calc:(some "../a + 2") ();
  ] in
  match recalc binds doc with
  | FStar_Pervasives_Native.None ->
    check ~name:"§7.6.1 diamond recalc (must succeed)" "ok" "document-error"
  | FStar_Pervasives_Native.Some (doc2, _) ->
    check ~name:"§7.6.1 diamond b = a+1 = 4" "4" (leaf_value doc2 "b");
    check ~name:"§7.6.1 diamond c = a+2 = 5" "5" (leaf_value doc2 "c");
    check ~name:"§7.6.1 diamond d = b+c = 9" "9" (leaf_value doc2 "d")

(* ================================================================== *)
(* §7.6.1 CYCLE — a calculate cycle is a document error, NOT a loop    *)
(* ================================================================== *)
(* The whole point of the termination-proof design: a <-> b mutual
   calculate reference has no in-degree-0 node, so topo_pass returns
   None WITHOUT looping.  We assert the engine returns a document error
   (None) rather than hanging or producing a wrong answer.            *)

let test_calc_cycle () =
  let doc = doc_of "<data><a>1</a><b>1</b></data>" in
  let binds = [
    bind ~target:"a" ~calc:(some "../b + 1") ();
    bind ~target:"b" ~calc:(some "../a + 1") ();
  ] in
  (match recalc binds doc with
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.6.1 two-node calculate cycle a<->b rejected (document error)" "rejected" "rejected"
   | FStar_Pervasives_Native.Some _ ->
     check ~name:"§7.6.1 two-node calculate cycle a<->b rejected (document error)" "rejected" "accepted-WRONG");
  (* self-cycle: a calculate that references its own target node *)
  let doc2 = doc_of "<data><a>1</a></data>" in
  let sbinds = [ bind ~target:"a" ~calc:(some "../a + 1") () ] in
  (match recalc sbinds doc2 with
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.6.1 self-referential calculate a = ../a + 1 rejected" "rejected" "rejected"
   | FStar_Pervasives_Native.Some _ ->
     check ~name:"§7.6.1 self-referential calculate a = ../a + 1 rejected" "rejected" "accepted-WRONG");
  (* three-node cycle a -> b -> c -> a *)
  let doc3 = doc_of "<data><a>1</a><b>1</b><c>1</c></data>" in
  let cbinds = [
    bind ~target:"a" ~calc:(some "../c + 1") ();
    bind ~target:"b" ~calc:(some "../a + 1") ();
    bind ~target:"c" ~calc:(some "../b + 1") ();
  ] in
  (match recalc cbinds doc3 with
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.6.1 three-node calculate cycle a->b->c->a rejected" "rejected" "rejected"
   | FStar_Pervasives_Native.Some _ ->
     check ~name:"§7.6.1 three-node calculate cycle a->b->c->a rejected" "rejected" "accepted-WRONG")

(* A DAG that merely LOOKS deep (a chain of 4) must still be accepted —
   proves the cycle rejection is not over-eager. *)
let test_calc_deep_chain_ok () =
  let doc = doc_of "<data><a>1</a><b>0</b><c>0</c><d>0</d></data>" in
  let binds = [
    bind ~target:"d" ~calc:(some "../c + 1") ();
    bind ~target:"c" ~calc:(some "../b + 1") ();
    bind ~target:"b" ~calc:(some "../a + 1") ();
  ] in
  match recalc binds doc with
  | FStar_Pervasives_Native.None ->
    check ~name:"§7.6 deep acyclic chain a->b->c->d accepted" "ok" "document-error"
  | FStar_Pervasives_Native.Some (doc2, _) ->
    check ~name:"§7.6 deep chain d = 4 (1+1+1+1)" "4" (leaf_value doc2 "d")

(* ================================================================== *)
(* §7.7 constraint — produces per-node validity                        *)
(* ================================================================== *)

let test_constraint () =
  let doc = doc_of "<data><age>17</age></data>" in
  let binds = [ bind ~target:"age" ~cons:(some ". >= 18") () ] in
  (match recalc binds doc with
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.7 constraint recalc (must succeed)" "ok" "document-error"
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "age" report with
      | Some nv ->
        check_bool ~name:"§7.7 constraint '. >= 18' on age=17 is UNsatisfied" false nv.XB.nv_constraint;
        check_bool ~name:"§7.7 node age invalid when constraint fails" false nv.XB.nv_valid
      | None -> check ~name:"§7.7 constraint report present" "present" "missing"));
  (* satisfied case *)
  let doc2 = doc_of "<data><age>21</age></data>" in
  (match recalc [ bind ~target:"age" ~cons:(some ". >= 18") () ] doc2 with
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "age" report with
      | Some nv ->
        check_bool ~name:"§7.7 constraint '. >= 18' on age=21 satisfied" true nv.XB.nv_constraint;
        check_bool ~name:"§7.7 node age valid when constraint holds" true nv.XB.nv_valid
      | None -> check ~name:"§7.7 constraint report present (2)" "present" "missing")
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.7 constraint recalc (must succeed 2)" "ok" "document-error")

(* ================================================================== *)
(* §7.4 relevant / §7.5 required — boolean MIPs                        *)
(* ================================================================== *)

let test_relevant_required () =
  (* relevant depends on a sibling flag; required on the same.          *)
  let doc = doc_of "<data><wantsMail>false</wantsMail><email></email></data>" in
  let binds = [
    bind ~target:"email"
         ~rel:(some "../wantsMail = 'true'")
         ~req:(some "../wantsMail = 'true'") ();
  ] in
  (match recalc binds doc with
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "email" report with
      | Some nv ->
        check_bool ~name:"§7.4 relevant false when wantsMail=false" false nv.XB.nv_relevant;
        check_bool ~name:"§7.5 required false when wantsMail=false" false nv.XB.nv_required;
        (* §7.4: a non-relevant empty required node does not make the model invalid *)
        check_bool ~name:"§7.4 non-relevant empty node stays valid" true nv.XB.nv_valid
      | None -> check ~name:"§7.4 relevant report present" "present" "missing")
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.4 relevant recalc (must succeed)" "ok" "document-error");
  (* Now flip wantsMail=true: email becomes relevant AND required, but
     empty -> the required-but-empty node is invalid (§7.5).            *)
  let doc2 = doc_of "<data><wantsMail>true</wantsMail><email></email></data>" in
  (match recalc binds doc2 with
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "email" report with
      | Some nv ->
        check_bool ~name:"§7.4 relevant true when wantsMail=true" true nv.XB.nv_relevant;
        check_bool ~name:"§7.5 required true when wantsMail=true" true nv.XB.nv_required;
        check_bool ~name:"§7.5 required-but-empty relevant node is INVALID" false nv.XB.nv_valid
      | None -> check ~name:"§7.5 required report present" "present" "missing")
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.5 required recalc (must succeed)" "ok" "document-error")

(* ================================================================== *)
(* §6.2.1 type MIP — dispatch to XSD.Datatypes (valid + ill-formed)    *)
(* ================================================================== *)

let test_type_mip () =
  (* well-formed xsd:integer *)
  let doc = doc_of "<data><n>42</n></data>" in
  (match recalc [ bind ~target:"n" ~ty:XB.MipTypeInteger () ] doc with
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "n" report with
      | Some nv ->
        check_bool ~name:"§6.2.1 type xsd:integer accepts \"42\"" true nv.XB.nv_type_valid;
        check_bool ~name:"§6.2.1 node valid for well-formed integer" true nv.XB.nv_valid
      | None -> check ~name:"§6.2.1 integer report present" "present" "missing")
   | FStar_Pervasives_Native.None -> check ~name:"§6.2.1 integer recalc" "ok" "err");
  (* ill-formed xsd:integer *)
  let doc2 = doc_of "<data><n>4.2</n></data>" in
  (match recalc [ bind ~target:"n" ~ty:XB.MipTypeInteger () ] doc2 with
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "n" report with
      | Some nv ->
        check_bool ~name:"§6.2.1 type xsd:integer REJECTS \"4.2\"" false nv.XB.nv_type_valid;
        check_bool ~name:"§6.2.1 node invalid for ill-formed integer" false nv.XB.nv_valid
      | None -> check ~name:"§6.2.1 integer report present (2)" "present" "missing")
   | FStar_Pervasives_Native.None -> check ~name:"§6.2.1 integer recalc (2)" "ok" "err");
  (* xsd:decimal accepts "4.2" *)
  let doc3 = doc_of "<data><n>4.2</n></data>" in
  (match recalc [ bind ~target:"n" ~ty:XB.MipTypeDecimal () ] doc3 with
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "n" report with
      | Some nv -> check_bool ~name:"§6.2.1 type xsd:decimal accepts \"4.2\"" true nv.XB.nv_type_valid
      | None -> check ~name:"§6.2.1 decimal report present" "present" "missing")
   | FStar_Pervasives_Native.None -> check ~name:"§6.2.1 decimal recalc" "ok" "err");
  (* unsupported type QName -> explicit INVALID, not a silent pass *)
  let doc4 = doc_of "<data><n>whatever</n></data>" in
  (match recalc [ bind ~target:"n" ~ty:(XB.mip_type_of_qname "xsd:hexBinary") () ] doc4 with
   | FStar_Pervasives_Native.Some (_, report) ->
     (match find_validity "n" report with
      | Some nv -> check_bool ~name:"§6.2.1 unsupported type QName is explicitly INVALID" false nv.XB.nv_type_valid
      | None -> check ~name:"§6.2.1 unsupported report present" "present" "missing")
   | FStar_Pervasives_Native.None -> check ~name:"§6.2.1 unsupported recalc" "ok" "err")

(* ================================================================== *)
(* §7.6 + type interaction via apply_edit — the plan's edit signature  *)
(* ================================================================== *)
(* A calculated total that must be an integer; edit a source cell and
   watch the calculated cell + its type validity update.               *)

let test_apply_edit () =
  let doc = doc_of "<data><qty>2</qty><price>3</price><total>0</total></data>" in
  let binds = [
    bind ~target:"total" ~calc:(some "../qty * ../price") ~ty:XB.MipTypeInteger ();
  ] in
  (* edit qty 2 -> 5, total should recompute to 15 *)
  match XB.apply_edit binds doc "qty" "5" with
  | FStar_Pervasives_Native.None ->
    check ~name:"§7.6 apply_edit (must succeed)" "ok" "document-error"
  | FStar_Pervasives_Native.Some (doc2, report) ->
    check ~name:"§7.6 apply_edit qty:=5 recomputes total = 5*3 = 15" "15" (leaf_value doc2 "total");
    (match find_validity "total" report with
     | Some nv -> check_bool ~name:"§6.2.1 recomputed total 15 is a valid xsd:integer" true nv.XB.nv_type_valid
     | None -> check ~name:"§7.6 apply_edit report present" "present" "missing")

(* ================================================================== *)
(* §7.3 bind decode from a standalone <xf:bind .../> tree              *)
(* ================================================================== *)

let test_decode_binds () =
  let model = doc_of
    "<binds><xf:bind nodeset=\"b\" calculate=\"../a + 1\"/><xf:bind nodeset=\"a\" type=\"xsd:integer\"/></binds>" in
  let binds = XB.decode_binds model in
  let n = List.length binds in
  check ~name:"§7.3 decode_binds reads two <xf:bind> elements" "2" (string_of_int n);
  let doc = doc_of "<data><a>7</a><b>0</b></data>" in
  (match recalc binds doc with
   | FStar_Pervasives_Native.Some (doc2, _) ->
     check ~name:"§7.3 decoded bind computes b = ../a + 1 = 8" "8" (leaf_value doc2 "b")
   | FStar_Pervasives_Native.None ->
     check ~name:"§7.3 decoded bind recalc (must succeed)" "ok" "document-error")

let () =
  Printf.printf "xforms_tests: XForms 1.1 model-layer bind/recalc (spec-cited)\n";
  test_calc_chain ();
  test_calc_diamond ();
  test_calc_cycle ();
  test_calc_deep_chain_ok ();
  test_constraint ();
  test_relevant_required ();
  test_type_mip ();
  test_apply_edit ();
  test_decode_binds ();
  Printf.printf "XForms bind/recalc: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
