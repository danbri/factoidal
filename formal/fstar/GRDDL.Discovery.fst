module GRDDL.Discovery

// GRDDL ("Gleaning Resource Descriptions from Dialects of Languages",
// W3C Rec. 11 Sept 2007) Stage 1: same-document transformation
// discovery over already-parsed, well-formed XML/XHTML `xml_node`
// trees, composed with the already-verified XSLT 1.0 engine
// (XSLT.Transform) and RDF/XML parser (Parser.RDFXML) to produce an
// RDF graph. Scope (per docs/designissues/2026-07-08-grddl-scoping.md):
//
//   * path (a): the `grddl:transformation` attribute (namespace
//     http://www.w3.org/2003/g/data-view#) on the document's ROOT
//     element -- a whitespace-separated list of IRI references.
//   * path (b): XHTML `head/@profile` gating `link`/`a` elements whose
//     `@rel` token list includes "transformation"; collect their
//     `@href`. The profile URI gate is the fixed constant
//     http://www.w3.org/2003/g/data-view.
//   * rdfxbase: an RDF/XML source document is itself a GRDDL result --
//     its faithful RDF/XML rendition is unioned into the output.
//
// DELIBERATELY OUT of Stage-1 scope (handled by a later stage, and
// reported as skip-network by the runner, never as a pass): the
// namespace-document (§3) and profile-document (§5) transformation
// paths, which dereference a SECOND resource; HTML tag-soup input
// (Parser.XML parses well-formed XML only); and non-RDF/XML
// transformation output.
//
// Everything here is pure Tot over `xml_node` plus the existing
// verified functions -- zero `assume val`, no I/O, no --lax. The
// consumer (bin/grddl-runner) supplies the file I/O: it reads the
// source, stylesheet, and expected-output files from a local
// allowlisted directory (no network) and calls the functions below.

open FStar.List.Tot
open Parser.XML
open Parser.RDFXML
open RDF.Triple
open RDF.Graph

(* ================================================================ *)
(* GRDDL / manifest vocabulary constants                             *)
(* ================================================================ *)

// The GRDDL namespace (attribute namespace for grddl:transformation).
let grddl_ns : string = "http://www.w3.org/2003/g/data-view#"

// The GRDDL profile URI (value gate on XHTML head/@profile). Note the
// deliberate absence of the trailing '#': §4 uses the bare form.
let grddl_profile : string = "http://www.w3.org/2003/g/data-view"

let rdf_ns : string = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

// GRDDL test-vocabulary + rdfcore test-schema IRIs, surfaced here so
// the OCaml runner classifies tests via these predicates rather than
// hard-coding the Stage-1/Stage-2 boundary (CLAUDE.md rule #11: the
// runner does data extraction; the classification lives in F*).
let grddl_testvocab_ns : string =
  "http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#"
let networked_test_iri : string =
  "http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#NetworkedTest"
let rule_nstx : string = "http://www.w3.org/TR/grddl/#rule_nstx"
let rule_profiletrans : string = "http://www.w3.org/TR/grddl/#rule_profiletrans"

// A test whose type is g:NetworkedTest requires a live HTTP fetch --
// Stage 2, always skip.
let is_networked_type (iri : string) : bool = iri = networked_test_iri

// rule_nstx (namespace-document transformation, §3) and
// rule_profiletrans (profile-document transformation, §5) both require
// dereferencing a SECOND resource -- Stage 2 discovery paths, skip.
let is_stage2_rule (iri : string) : bool =
  iri = rule_nstx || iri = rule_profiletrans

(* ================================================================ *)
(* Whitespace tokenisation                                           *)
(* ================================================================ *)

let is_ws_char (c : FStar.Char.char) : bool =
  let n = FStar.Char.int_of_char c in
  n = 0x20 || n = 0x09 || n = 0x0A || n = 0x0D

let rec split_ws_acc (cs : list FStar.Char.char) (cur : list FStar.Char.char)
                     (acc : list string)
  : Tot (list string) (decreases cs) =
  match cs with
  | [] ->
    (match cur with
     | [] -> List.Tot.rev acc
     | _ -> List.Tot.rev (String.string_of_list (List.Tot.rev cur) :: acc))
  | c :: rest ->
    if is_ws_char c then
      (match cur with
       | [] -> split_ws_acc rest [] acc
       | _ -> split_ws_acc rest [] (String.string_of_list (List.Tot.rev cur) :: acc))
    else split_ws_acc rest (c :: cur) acc

// Split a string on XML whitespace, dropping empty tokens.
let split_ws (s : string) : list string =
  split_ws_acc (String.list_of_string s) [] []

(* ================================================================ *)
(* Namespace-map + local-name helpers over an element's attributes   *)
(* ================================================================ *)

// Build a prefix -> namespace-URI map from an element's xmlns:*
// attributes. `split_qname` (Parser.RDFXML) turns "xmlns:data-view"
// into ("xmlns", "data-view"); we keep the local part as the prefix.
let rec ns_map_of_attrs (attrs : list xml_attribute)
  : Tot (list (string * string)) (decreases attrs) =
  match attrs with
  | [] -> []
  | a :: rest ->
    let (pfx, loc) = split_qname a.attr_name in
    if pfx = "xmlns" && loc <> "" then (loc, a.attr_value) :: ns_map_of_attrs rest
    else ns_map_of_attrs rest

(* ================================================================ *)
(* Path (a): grddl:transformation attribute on the root element      *)
(* ================================================================ *)

let rec find_grddl_attr_val (nsm : list (string * string)) (attrs : list xml_attribute)
  : Tot (option string) (decreases attrs) =
  match attrs with
  | [] -> None
  | a :: rest ->
    let (pfx, loc) = split_qname a.attr_name in
    if loc = "transformation" && pfx <> "" then
      (match lookup_ns pfx nsm with
       | Some uri ->
         if uri = grddl_ns || uri = grddl_profile then Some a.attr_value
         else find_grddl_attr_val nsm rest
       | None -> find_grddl_attr_val nsm rest)
    else find_grddl_attr_val nsm rest

// Path (a): the whitespace-separated IRI-reference list carried by the
// root element's grddl:transformation attribute (any prefix bound to
// the data-view namespace). References are returned unresolved.
let find_transformation_attr (root : xml_node) : list string =
  let attrs = element_attrs root in
  let nsm = ns_map_of_attrs attrs in
  match find_grddl_attr_val nsm attrs with
  | Some v -> split_ws v
  | None -> []

(* ================================================================ *)
(* Path (b): XHTML head/@profile gate + rel="transformation" links   *)
(* ================================================================ *)

// The local name of an element/attribute QName (part after the colon,
// or the whole name if unprefixed). XHTML test documents bind the
// XHTML namespace as the default namespace, so head/link/a arrive
// unprefixed; stripping any prefix keeps the walk robust either way.
let local_of (name : string) : string =
  let (_, loc) = split_qname name in
  if loc = "" then name else loc

let rec find_head_in_node (node : xml_node) : Tot (option xml_node) (decreases node) =
  match node with
  | XElement tag _ children ->
    if local_of tag = "head" then Some node
    else find_head_in_list children
  | _ -> None
and find_head_in_list (nodes : list xml_node) : Tot (option xml_node) (decreases nodes) =
  match nodes with
  | [] -> None
  | n :: rest ->
    (match find_head_in_node n with
     | Some h -> Some h
     | None -> find_head_in_list rest)

// True iff the document's head element declares the GRDDL profile in
// its @profile token list -- the §4 gate that enables rel-based
// transformation links.
let head_has_grddl_profile (root : xml_node) : bool =
  match find_head_in_node root with
  | Some (XElement _ attrs _) ->
    (match find_attr "profile" attrs with
     | Some pv -> List.Tot.mem grddl_profile (split_ws pv)
     | None -> false)
  | _ -> false

let elt_is_transform_link (node : xml_node) : bool =
  match node with
  | XElement tag attrs _ ->
    let ln = local_of tag in
    (ln = "link" || ln = "a") &&
    (match find_attr "rel" attrs with
     | Some rv -> List.Tot.mem "transformation" (split_ws rv)
     | None -> false)
  | _ -> false

let elt_href (node : xml_node) : list string =
  match node with
  | XElement _ attrs _ ->
    (match find_attr "href" attrs with Some h -> [h] | None -> [])
  | _ -> []

let rec collect_links_node (node : xml_node) : Tot (list string) (decreases node) =
  let here = if elt_is_transform_link node then elt_href node else [] in
  match node with
  | XElement _ _ children -> here @ collect_links_list children
  | _ -> here
and collect_links_list (nodes : list xml_node) : Tot (list string) (decreases nodes) =
  match nodes with
  | [] -> []
  | n :: rest -> collect_links_node n @ collect_links_list rest

// Path (b): only when the head declares the GRDDL profile, the @href of
// every link/a element (anywhere in the document -- head OR body, per
// the InBody test cases) whose @rel token list includes
// "transformation". References are returned unresolved.
let find_xhtml_transformation_links (root : xml_node) : list string =
  if head_has_grddl_profile root then collect_links_node root
  else []

(* ================================================================ *)
(* IRI resolution + document base                                    *)
(* ================================================================ *)

// The document base for resolving relative transformation references:
// a root xml:base attribute overrides the fetch/fallback base
// (the source document's own IRI). Resolution reuses Parser.RDFXML's
// resolve_iri, which delegates to the RFC 3986 §5 algorithm.
let effective_base (fallback : string) (root : xml_node) : string =
  match find_attr "xml:base" (element_attrs root) with
  | Some b -> resolve_iri fallback b
  | None -> fallback

let rec resolve_all (base : string) (refs : list string)
  : Tot (list string) (decreases refs) =
  match refs with
  | [] -> []
  | r :: rest -> resolve_iri base r :: resolve_all base rest

// Full same-document discovery: path (a) ++ path (b), each relative
// reference resolved against the document base.
let discover_transformations (fallback_base : string) (root : xml_node) : list string =
  let base = effective_base fallback_base root in
  let raw = find_transformation_attr root @ find_xhtml_transformation_links root in
  resolve_all base raw

(* ================================================================ *)
(* Stage 2: namespace-document (section 3) + profile-document        *)
(* (section 5) transformation discovery.                             *)
(*                                                                    *)
(* These are pure Tot tree-walks over an ALREADY-FETCHED, already-    *)
(* parsed second-document `xml_node`. The consumer (bin/grddl-runner) *)
(* performs the document FETCH -- resolving the root-element          *)
(* namespace URI (section 3) and each head @profile URI (section 5)   *)
(* to local allowlisted files, no network -- and hands the parsed     *)
(* trees to the functions below (CLAUDE.md rule #11: the runner does  *)
(* I/O, the discovery semantics live here). Single level: a fetched   *)
(* namespace/profile document that itself declares further namespace/ *)
(* profile documents is NOT recursed into (the recursive `loop`/      *)
(* `loopx`/`ns-*` corpus stays honestly unmet residue).              *)
(* ================================================================ *)

// An XHTML `<base href="...">` element in the document head sets the
// document base for relative reference resolution (grddlProfileWith-
// BaseElement, hcard). Scan the head's children for it.
let rec find_base_href_in_list (nodes : list xml_node)
  : Tot (option string) (decreases nodes) =
  match nodes with
  | [] -> None
  | n :: rest ->
    (match n with
     | XElement tag attrs _ ->
       if local_of tag = "base" then
         (match find_attr "href" attrs with
          | Some h -> Some h
          | None -> find_base_href_in_list rest)
       else find_base_href_in_list rest
     | _ -> find_base_href_in_list rest)

let html_base_href (root : xml_node) : option string =
  match find_head_in_node root with
  | Some (XElement _ _ children) -> find_base_href_in_list children
  | _ -> None

// The effective document base: an XHTML `<base href>` element takes
// precedence, then a root `xml:base` attribute (effective_base), then
// the fetch fallback (the document's own IRI).
let doc_base (fallback : string) (root : xml_node) : string =
  match html_base_href root with
  | Some b -> resolve_iri fallback b
  | None -> effective_base fallback root

(* ---- Section 5: profile-document transformation discovery -------- *)

// The custom profile URIs the agent must dereference: the head
// @profile token list minus the fixed GRDDL profile constant (which
// only gates same-document rel="transformation" links, path b; it is
// never itself a profile document to fetch). Resolved against the
// document base.
let head_custom_profile_uris (fallback : string) (root : xml_node) : list string =
  let base = doc_base fallback root in
  match find_head_in_node root with
  | Some (XElement _ attrs _) ->
    (match find_attr "profile" attrs with
     | Some pv ->
       resolve_all base
         (List.Tot.filter (fun (u:string) -> u <> grddl_profile) (split_ws pv))
     | None -> [])
  | _ -> []

let elt_is_profiletx_link (node : xml_node) : bool =
  match node with
  | XElement tag attrs _ ->
    let ln = local_of tag in
    (ln = "link" || ln = "a") &&
    (match find_attr "rel" attrs with
     | Some rv -> List.Tot.mem "profileTransformation" (split_ws rv)
     | None -> false)
  | _ -> false

let rec collect_profiletx_node (node : xml_node) : Tot (list string) (decreases node) =
  let here = if elt_is_profiletx_link node then elt_href node else [] in
  match node with
  | XElement _ _ children -> here @ collect_profiletx_list children
  | _ -> here
and collect_profiletx_list (nodes : list xml_node) : Tot (list string) (decreases nodes) =
  match nodes with
  | [] -> []
  | n :: rest -> collect_profiletx_node n @ collect_profiletx_list rest

// Section 5: the transformations a fetched profile document associates
// with documents that reference it -- the @href of every link/a whose
// @rel token list includes "profileTransformation" -- resolved against
// the profile document's own base. The profile document must itself
// carry the GRDDL profile in its head @profile (the §5 gate).
let profile_doc_transformations (profile_iri : string) (profile_doc : xml_node)
  : list string =
  if head_has_grddl_profile profile_doc then
    resolve_all (doc_base profile_iri profile_doc)
      (collect_profiletx_node profile_doc)
  else []

(* ---- Section 3: namespace-document transformation discovery ------ *)

// The root element's namespace URI -- the namespace document the agent
// dereferences (section 3). Unprefixed root name -> the default xmlns;
// prefixed -> the prefix's binding among the root's xmlns:* attributes.
let root_namespace_uri (root : xml_node) : option string =
  match root with
  | XElement tag attrs _ ->
    let (pfx, _) = split_qname tag in
    if pfx = "" then find_attr "xmlns" attrs
    else lookup_ns pfx (ns_map_of_attrs attrs)
  | _ -> None

// A grddl:namespaceTransformation element (data-view namespace) carries
// the transform IRI in its rdf:resource attribute. Matched by local
// name (consistent with this module's local_of-based link matching) and
// gated on the presence of an rdf:resource, so a stray element named
// "namespaceTransformation" without one contributes nothing.
let elt_ns_transform (node : xml_node) : list string =
  match node with
  | XElement tag attrs _ ->
    if local_of tag = "namespaceTransformation" then
      (match find_attr "rdf:resource" attrs with
       | Some r -> [r]
       | None -> [])
    else []
  | _ -> []

let rec collect_nstx_node (node : xml_node) : Tot (list string) (decreases node) =
  let here = elt_ns_transform node in
  match node with
  | XElement _ _ children -> here @ collect_nstx_list children
  | _ -> here
and collect_nstx_list (nodes : list xml_node) : Tot (list string) (decreases nodes) =
  match nodes with
  | [] -> []
  | n :: rest -> collect_nstx_node n @ collect_nstx_list rest

// Section 3: the transformations a fetched namespace document declares
// -- the rdf:resource of every grddl:namespaceTransformation element --
// resolved against the namespace document's own base.
let namespace_doc_transformations (ns_iri : string) (ns_doc : xml_node)
  : list string =
  resolve_all (doc_base ns_iri ns_doc) (collect_nstx_node ns_doc)

(* ================================================================ *)
(* rdfxbase: an RDF/XML source contributes its own faithful rendition *)
(* ================================================================ *)

// True iff the root element's expanded name is rdf:RDF.
let is_rdfxml_root (root : xml_node) : bool =
  match root with
  | XElement tag attrs _ ->
    let (pfx, loc) = split_qname tag in
    loc = "RDF" &&
    (match lookup_ns pfx (ns_map_of_attrs attrs) with
     | Some uri -> uri = rdf_ns
     | None -> false)
  | _ -> false

// The RDF/XML-base contribution to the GRDDL result: when the source
// is itself an RDF/XML document, the triples obtained by parsing it as
// RDF/XML (relative IRIs against the document base). Otherwise empty.
let rdfxml_base_triples (base : string) (root : xml_node) (input : string) : list triple =
  if is_rdfxml_root root then parse_rdfxml_with_base base input
  else []

(* ================================================================ *)
(* grddl_apply: compose XSLT transform + RDF/XML re-parse             *)
(* ================================================================ *)

// Apply one discovered transformation to the source tree, then parse
// the (RDF/XML) result string against the document base. None when the
// transform output is not well-formed RDF/XML.
let grddl_apply (base : string) (stylesheet : xml_node) (source : xml_node)
  : option (list triple) =
  let out = XSLT.Transform.transform stylesheet source in
  parse_rdfxml_with_base_strict base out

let rec grddl_apply_all (base : string) (styles : list xml_node) (source : xml_node)
  : Tot (list triple) (decreases styles) =
  match styles with
  | [] -> []
  | s :: rest ->
    let ts =
      (match grddl_apply base s source with
       | Some t -> t
       | None ->
         // strict parse rejected the output; fall back to the lenient
         // parser so a partially-correct transform still contributes
         // its triples to the merge (the graph comparison decides).
         parse_rdfxml_with_base base (XSLT.Transform.transform s source)) in
    ts @ grddl_apply_all base rest source

// The full GRDDL result of a source document given the parsed
// stylesheet trees discovered for it: the RDF/XML-base contribution
// unioned with every transform's output (§7 "merge those GRDDL
// results").
let grddl_result (base : string) (root : xml_node) (input : string)
                 (styles : list xml_node) : list triple =
  rdfxml_base_triples base root input @ grddl_apply_all base styles root

(* ================================================================ *)
(* Graph comparison via the verified RDFC-1.0 canonicalizer          *)
(* ================================================================ *)

let rec triple_mem (t : triple) (ts : list triple) : Tot bool (decreases ts) =
  match ts with
  | [] -> false
  | h :: r -> if triple_eq t h then true else triple_mem t r

// A graph is a SET of triples (RDF 1.1 Concepts §3); drop duplicates
// so the canonical N-Quads of two graphs are equal iff the graphs are
// isomorphic, not merely list-equal.
let rec dedup_triples (ts : list triple) : Tot (list triple) (decreases ts) =
  match ts with
  | [] -> []
  | h :: r ->
    let d = dedup_triples r in
    if triple_mem h d then d else h :: d

let graph_to_canonical_nquads (ts : list triple) : string =
  RDF.Canonical.canonicalize_to_nquads
    ({ ds_default = dedup_triples ts; ds_named = [] })

// Two RDF graphs compared by RDFC-1.0 canonicalization (blank-node
// isomorphism aware) -- NOT string diff.
let graphs_isomorphic (g1 g2 : list triple) : bool =
  graph_to_canonical_nquads g1 = graph_to_canonical_nquads g2
