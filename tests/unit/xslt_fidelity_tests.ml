(* xslt_fidelity_tests.ml — XSLT engine-fidelity regression battery mined
   from the GRDDL suite's fail-graph-mismatch bucket (issue #301).

   Provenance: the GRDDL Stage-2 runner canonicalises the RDF produced by
   consumed GRDDL transforms and compares it (RDFC-1.0, NOT string diff)
   against each test's expected-output graph. Several of its
   fail-graph-mismatch entries are genuine XSLT-engine fidelity gaps in
   the consumed real-world stylesheets (hcard2rdf.xsl, grokSheet.xsl, ...)
   rather than GRDDL content-negotiation / namespace-recursion / XInclude
   posture. This file pins the engine behaviour those tests depend on.

   Root cause fixed alongside this file (XSLT.Transform.fst): an
   <xsl:apply-templates> carrying <xsl:with-param> children dropped them
   on the floor — the selected nodes' matched templates only ever saw
   their <xsl:param> defaults, never the passed values. hcard2rdf.xsl
   routes every structured field (n/given-name/family-name, nickname,
   adr, tel, ...) through <xsl:apply-templates ... mode="extract-field">
   with a forwarded field= param, so all of them silently vanished while
   the direct-emit fields (fn, sort-string, title) came through. card5n's
   only difference from its expected graph was the missing v:nickname.

   Oracle (CLAUDE.md rule #25, "fidelity oracle" per the task): the
   RDF-producing cases compare the RESULT GRAPH's canonical N-Quads
   (GRDDL_Discovery.graph_to_canonical_nquads) against the expected
   graph's — stricter than string comparison of the transform output, and
   independent of blank-node labelling / triple order / xmlns prefixes.
   The two isolation cases produce plain XML (not RDF) and use an exact
   string oracle to name the precise instruction-level gap.

   Wired into tests/unit/run-all.sh by auto-discovery (any *.ml here is a
   test); its per-test ocamldep closure links XSLT_Transform, Parser_XML,
   Parser_RDFXML and GRDDL_Discovery. Exit code is 0 iff every case
   passes. *)

let passed = ref 0
let failed = ref 0

let some = function
  | FStar_Pervasives_Native.Some x -> Some x
  | FStar_Pervasives_Native.None -> None

let doc_of (xml : string) : Parser_XML.xml_node =
  match some (Parser_XML.parse_xml_document xml) with
  | Some n -> n
  | None -> failwith ("fixture failed to parse: " ^ xml)

(* A stable base for about="" / rdf:about resolution in the fixtures. *)
let base = "http://example.org/card"

(* Graph-level (canonical N-Quads) oracle: transform, RDF/XML-parse both
   sides against the same base, compare canonical forms. *)
let check_graph ~name ~stylesheet ~input ~expected =
  let out = XSLT_Transform.transform (doc_of stylesheet) (doc_of input) in
  let result = Parser_RDFXML.parse_rdfxml_with_base base out in
  let exp = Parser_RDFXML.parse_rdfxml_with_base base expected in
  if GRDDL_Discovery.graphs_isomorphic result exp then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n" name;
    Printf.printf "    --- xslt output ---\n%s\n" out;
    Printf.printf "    --- result canonical ---\n%s\n"
      (GRDDL_Discovery.graph_to_canonical_nquads result);
    Printf.printf "    --- expected canonical ---\n%s\n"
      (GRDDL_Discovery.graph_to_canonical_nquads exp)
  end

(* Exact-string oracle for the plain-XML isolation cases. *)
let check_str ~name ~stylesheet ~input ~expected =
  let out = String.trim (XSLT_Transform.transform (doc_of stylesheet) (doc_of input)) in
  let exp = String.trim expected in
  if String.equal out exp then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s\n    expected: %s\n    got:      %s\n" name exp out
  end

let read_file_opt path =
  try
    let ic = open_in_bin path in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Some (Bytes.to_string s)
  with Sys_error _ -> None

let rec find_repo_root d =
  if d = "/" || d = "" then None
  else if Sys.file_exists (Filename.concat d "CLAUDE.md") then Some d
  else find_repo_root (Filename.dirname d)

(* ================================================================== *)
(* Isolation repros — name the exact instruction-level gap.           *)
(* ================================================================== *)

(* ISO-1: <xsl:apply-templates> must deliver <xsl:with-param> to the
   matched template's <xsl:param>. Before the fix the param kept its
   default ("DEFLT"). No mode, literal param value. *)
let iso1_xsl = {xsl|<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
<xsl:template match="/"><out><xsl:apply-templates select="doc/item"><xsl:with-param name="field" select="'nickname'"/></xsl:apply-templates></out></xsl:template>
<xsl:template match="item"><xsl:param name="field" select="'DEFLT'"/><lit field="{$field}"/></xsl:template>
</xsl:stylesheet>|xsl}

(* ISO-2: with-param on a MODED apply-templates, plus a param whose
   default references a PRIOR param (prop = concat('v-',$field)) and a
   computed element/attribute name. This is the exact shape of
   hcard2rdf.xsl's extract-field header. *)
let iso2_xsl = {xsl|<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
<xsl:template match="/"><out><xsl:apply-templates select="doc/item" mode="ef"><xsl:with-param name="field" select="'nickname'"/></xsl:apply-templates></out></xsl:template>
<xsl:template match="*" mode="ef"><xsl:param name="field" select="''"/><xsl:param name="prop" select="concat('v-',$field)"/><lit prop="{$prop}" field="{$field}"/></xsl:template>
</xsl:stylesheet>|xsl}

let iso_input = {x|<doc><item class="nickname">Hafmo</item></doc>|x}

(* ================================================================== *)
(* Graph-level repros — mirror hcard2rdf.xsl's real routing.          *)
(* ================================================================== *)

(* G-1: single field via moded apply-templates + forwarded literal param
   + computed property element name from a chained param default. This is
   the minimal shape of the v:nickname path that card5n needs. *)
let g1_xsl = {xsl|<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:v="http://www.w3.org/2006/vcard/ns#">
<xsl:template match="/"><rdf:RDF><rdf:Description rdf:about="http://example.org/card"><xsl:apply-templates select="//span" mode="ef"><xsl:with-param name="field" select="'nickname'"/></xsl:apply-templates></rdf:Description></rdf:RDF></xsl:template>
<xsl:template match="*" mode="ef"><xsl:param name="field" select="''"/><xsl:param name="prop" select="concat('v:',$field)"/><xsl:if test="@class=$field"><xsl:element name="{$prop}"><xsl:value-of select="."/></xsl:element></xsl:if></xsl:template>
</xsl:stylesheet>|xsl}

let g1_input = {x|<doc><span class="nickname">Hafmo</span></doc>|x}

let g1_expected = {x|<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:v="http://www.w3.org/2006/vcard/ns#"><rdf:Description rdf:about="http://example.org/card"><v:nickname>Hafmo</v:nickname></rdf:Description></rdf:RDF>|x}

(* G-2: param FORWARDED through recursion. The moded template forwards
   both field= and prop= (select="$field" / "$prop" referencing its own
   in-scope params) into a nested apply-templates over its children, and
   the leaf span emits. This is hcard2rdf.xsl's extract-field recursion
   and exercises the scoped-evaluation half of the fix (a with-param
   select that names a LOCAL variable of the calling template). *)
let g2_xsl = {xsl|<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:v="http://www.w3.org/2006/vcard/ns#">
<xsl:template match="/"><rdf:RDF><rdf:Description rdf:about="http://example.org/card"><xsl:apply-templates select="//div" mode="ef"><xsl:with-param name="field" select="'given-name'"/></xsl:apply-templates></rdf:Description></rdf:RDF></xsl:template>
<xsl:template match="*" mode="ef"><xsl:param name="field" select="''"/><xsl:param name="prop" select="concat('v:',$field)"/><xsl:if test="@class=$field"><xsl:element name="{$prop}"><xsl:value-of select="."/></xsl:element></xsl:if><xsl:apply-templates select="*" mode="ef"><xsl:with-param name="field" select="$field"/><xsl:with-param name="prop" select="$prop"/></xsl:apply-templates></xsl:template>
</xsl:stylesheet>|xsl}

let g2_input = {x|<doc><div class="n"><span class="given-name">Cory</span></div></doc>|x}

let g2_expected = {x|<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#" xmlns:v="http://www.w3.org/2006/vcard/ns#"><rdf:Description rdf:about="http://example.org/card"><v:given-name>Cory</v:given-name></rdf:Description></rdf:RDF>|x}

(* ================================================================== *)
(* Real-world regression: the actual GRDDL card5n test, end to end.   *)
(* Reads the vendored hcard2rdf.xsl + card5n input + card5n-output     *)
(* expected graph from the committed grddl docroot and compares        *)
(* canonical graphs. This is the direct pin for the flipped GRDDL      *)
(* fail-graph-mismatch entry `card5n`. *)
let check_card5n () =
  let name = "real:grddl-card5n (hcard2rdf.xsl)" in
  match find_repo_root (Sys.getcwd ()) with
  | None -> incr failed; Printf.printf "  FAIL  %s: repo root not found\n" name
  | Some root ->
    let d = Filename.concat root "third_party/testing/grddl/docroot/td" in
    (match read_file_opt (Filename.concat d "hcard2rdf.xsl"),
           read_file_opt (Filename.concat d "card5n"),
           read_file_opt (Filename.concat d "card5n-output") with
     | Some sty, Some inp, Some exp ->
       let out = XSLT_Transform.transform (doc_of sty) (doc_of inp) in
       (* card5n's transform describes the source doc; both result and
          expected are read against the source-document base, matching the
          GRDDL runner. *)
       let src_base = "http://www.w3.org/2001/sw/grddl-wg/td/card5n" in
       let result = Parser_RDFXML.parse_rdfxml_with_base src_base out in
       let expected = Parser_RDFXML.parse_rdfxml_with_base src_base exp in
       if GRDDL_Discovery.graphs_isomorphic result expected then begin
         incr passed; Printf.printf "  PASS  %s\n" name
       end else begin
         incr failed;
         Printf.printf "  FAIL  %s\n    --- result canonical ---\n%s\n    --- expected canonical ---\n%s\n"
           name
           (GRDDL_Discovery.graph_to_canonical_nquads result)
           (GRDDL_Discovery.graph_to_canonical_nquads expected)
       end
     | _ ->
       incr failed;
       Printf.printf "  FAIL  %s: vendored grddl docroot files missing\n" name)

(* ================================================================== *)

let () =
  Printf.printf "xslt_fidelity_tests: apply-templates/with-param + hcard2rdf routing\n\n";
  check_str ~name:"iso1:apply-templates delivers with-param"
    ~stylesheet:iso1_xsl ~input:iso_input
    ~expected:{x|<out><lit field="nickname"/></out>|x};
  check_str ~name:"iso2:moded with-param + chained param default + AVT name"
    ~stylesheet:iso2_xsl ~input:iso_input
    ~expected:{x|<out><lit prop="v-nickname" field="nickname"/></out>|x};
  check_graph ~name:"graph:single field (nickname) via moded apply-templates"
    ~stylesheet:g1_xsl ~input:g1_input ~expected:g1_expected;
  check_graph ~name:"graph:forwarded param through recursion (given-name)"
    ~stylesheet:g2_xsl ~input:g2_input ~expected:g2_expected;
  check_card5n ();
  Printf.printf "\nxslt_fidelity_tests summary: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
