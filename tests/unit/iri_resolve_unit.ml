(* iri_resolve_unit.ml — pins SPARQL11.IRI.Resolve.resolve_iri's RFC 3986
   §5.2/5.3 reference-resolution behavior.

   This module's own banner (formal/fstar/SPARQL11.IRI.Resolve.fst)
   already claims validation against the RFC 3986 §5.4 42-case worked-
   example battery via an external Python prototype at write-time; this
   file pins that contract IN-REPO so a future edit to jir_merge /
   jir_remove_dot_segments / resolve_iri's empty-path branch fails a
   fast native check instead of only a slow W3C-suite regression.

   2026-07-05 (JSON-LD "IRI Resolution" bucket, toRdf/0122-0125): the
   W3C JSON-LD toRdf suite's "IRI Resolution (2)-(5)" family exercises a
   case the original 42-case battery didn't: a BASE IRI whose own path
   contains dot segments (e.g. "http://a/bb/ccc/./d;p?q"), resolved
   against a reference with an EMPTY PATH (query-only "?y", fragment-
   only "#s", or the empty string). RFC 3986 §5.3's Transform-References
   algorithm's "R.path is empty" branch copies Base.path VERBATIM (no
   remove_dot_segments) — only the two "R.path is non-empty" branches
   (absolute-path replace, or merge-then-normalize) run remove_dot_
   segments. This function already had it right (verified against these
   fixtures during the 2026-07-05 investigation — the JSON-LD test
   failures traced to JSONLD.Context.fst's "@base" context-processing
   step calling THIS function on an already-absolute @base value, which
   the JSON-LD API's context-processing algorithm says to adopt
   verbatim instead of resolving; that is JSONLD.Context.fst's bug, not
   resolve_iri's — see docs/designissues 2026-07-05 JSON-LD skip/IRI
   notes). The empty-path-preserves-base-dots cases below pin the
   CORRECT resolve_iri behavior so nobody "fixes" it into matching the
   upstream bug. *)

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

let () =
  let r = SPARQL11_IRI_Resolve.resolve_iri in

  (* --- RFC 3986 §5.4.1 "Normal Examples" (representative subset) --- *)
  let base = "http://a/b/c/d;p?q" in
  check ~name:"5.4.1 g:h"       "g:h"                (r base "g:h");
  check ~name:"5.4.1 g"         "http://a/b/c/g"      (r base "g");
  check ~name:"5.4.1 ./g"       "http://a/b/c/g"      (r base "./g");
  check ~name:"5.4.1 g/"        "http://a/b/c/g/"     (r base "g/");
  check ~name:"5.4.1 /g"        "http://a/g"          (r base "/g");
  check ~name:"5.4.1 //g"       "http://g"            (r base "//g");
  check ~name:"5.4.1 ?y"        "http://a/b/c/d;p?y"  (r base "?y");
  check ~name:"5.4.1 g?y"       "http://a/b/c/g?y"    (r base "g?y");
  check ~name:"5.4.1 #s"        "http://a/b/c/d;p?q#s" (r base "#s");
  check ~name:"5.4.1 g#s"       "http://a/b/c/g#s"    (r base "g#s");
  check ~name:"5.4.1 ;x"        "http://a/b/c/;x"     (r base ";x");
  check ~name:"5.4.1 g;x"       "http://a/b/c/g;x"    (r base "g;x");
  check ~name:"5.4.1 (empty)"   "http://a/b/c/d;p?q"  (r base "");
  check ~name:"5.4.1 ."         "http://a/b/c/"       (r base ".");
  check ~name:"5.4.1 ./"        "http://a/b/c/"       (r base "./");
  check ~name:"5.4.1 .."        "http://a/b/"         (r base "..");
  check ~name:"5.4.1 ../"       "http://a/b/"         (r base "../");
  check ~name:"5.4.1 ../g"      "http://a/b/g"        (r base "../g");
  check ~name:"5.4.1 ../.."     "http://a/"           (r base "../..");
  check ~name:"5.4.1 ../../"    "http://a/"           (r base "../../");
  check ~name:"5.4.1 ../../g"   "http://a/g"          (r base "../../g");

  (* --- RFC 3986 §5.4.2 "Abnormal Examples" (representative subset) --- *)
  check ~name:"5.4.2 ../../../g"    "http://a/g" (r base "../../../g");
  check ~name:"5.4.2 ../../../../g" "http://a/g" (r base "../../../../g");
  check ~name:"5.4.2 /./g"          "http://a/g" (r base "/./g");
  check ~name:"5.4.2 /../g"         "http://a/g" (r base "/../g");
  check ~name:"5.4.2 g."            "http://a/b/c/g."   (r base "g.");
  check ~name:"5.4.2 .g"            "http://a/b/c/.g"   (r base ".g");
  check ~name:"5.4.2 g.."           "http://a/b/c/g.."  (r base "g..");
  check ~name:"5.4.2 ..g"           "http://a/b/c/..g"  (r base "..g");
  check ~name:"5.4.2 ./../g"        "http://a/b/g"      (r base "./../g");
  check ~name:"5.4.2 ./g/."         "http://a/b/c/g/"   (r base "./g/.");
  check ~name:"5.4.2 g/./h"         "http://a/b/c/g/h"  (r base "g/./h");
  check ~name:"5.4.2 g/../h"        "http://a/b/c/h"    (r base "g/../h");
  check ~name:"5.4.2 g;x=1/./y"     "http://a/b/c/g;x=1/y"  (r base "g;x=1/./y");
  check ~name:"5.4.2 g;x=1/../y"    "http://a/b/c/y"        (r base "g;x=1/../y");
  check ~name:"5.4.2 g?y/./x"       "http://a/b/c/g?y/./x"  (r base "g?y/./x");
  check ~name:"5.4.2 g?y/../x"      "http://a/b/c/g?y/../x" (r base "g?y/../x");
  check ~name:"5.4.2 g#s/./x"       "http://a/b/c/g#s/./x"  (r base "g#s/./x");
  check ~name:"5.4.2 g#s/../x"      "http://a/b/c/g#s/../x" (r base "g#s/../x");
  check ~name:"5.4.2 http:g"        "http:g" (r base "http:g");

  (* --- toRdf/0122-0125 family: base path itself has dot segments; an
     empty-path reference (query-only / fragment-only / empty) must
     copy the base path VERBATIM, not remove_dot_segments it. --- *)
  let dotted_base = "http://a/bb/ccc/./d;p?q" in
  check ~name:"0122 ?y (dotted base, query-only ref)"
    "http://a/bb/ccc/./d;p?y" (r dotted_base "?y");
  check ~name:"0122 #s (dotted base, fragment-only ref)"
    "http://a/bb/ccc/./d;p?q#s" (r dotted_base "#s");
  check ~name:"0122 (empty) (dotted base, empty ref)"
    "http://a/bb/ccc/./d;p?q" (r dotted_base "");
  (* A NON-empty-path reference against the same dotted base DOES merge
     + remove_dot_segments as usual (RFC 3986 §5.3's other two
     branches) — "g" replaces the base's last path segment, so the
     base's OWN "./" never enters the merge. *)
  check ~name:"0122 g (dotted base, non-empty ref merges+normalizes)"
    "http://a/bb/ccc/g" (r dotted_base "g");

  let dotdot_base = "http://a/bb/ccc/.." in
  check ~name:"0125 g (base path ends in .., merge truncates before it)"
    "http://a/bb/ccc/g" (r dotdot_base "g");
  check ~name:"0125 ?y (empty-path ref keeps base's trailing .. verbatim)"
    "http://a/bb/ccc/..?y" (r dotdot_base "?y");

  Printf.printf "iri_resolve_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
