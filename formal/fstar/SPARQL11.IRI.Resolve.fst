module SPARQL11.IRI.Resolve

(* RFC 3986 reference-resolution algorithm + lightweight helpers,
   factored out of `SPARQL11.Algebra.fst`. The resolution functions
   themselves are unchanged from the original location (lines 1640..1726
   pre-factor); only the ambient string/list helpers are duplicated
   here so the new module has no dependency on `SPARQL11.Algebra`.

   #200 / #65 Step 1 (clean refactor; no behavior change). The Step 2
   migration — threading `option wf_iri` through `eval_expr` to retire
   the OCaml mutable `current_base_iri_ref` — is a follow-up that
   imports this module.

   Design constraint: keeping the module dependency-free of
   SPARQL11.Algebra (apart from the upstream `RDF.Graph.Executable`
   that defines `wf_iri` / `is_iri`) means duplicating
   `list_is_prefix`, `list_contains_sublist`, `string_contains`, and
   `string_to_iri` here. They're tiny and stable; consolidation into
   a shared helper module is a separate cleanup. *)

open FStar.List.Tot
open FStar.Char
open RDF.Graph.Executable

(* --- Local helpers (duplicated from SPARQL11.Algebra) ---------------- *)

let rec list_is_prefix (#a:eqtype) (prefix lst : list a) : Tot bool (decreases prefix) =
  match prefix, lst with
  | [], _ -> true
  | _, [] -> false
  | x :: xs, y :: ys -> x = y && list_is_prefix xs ys

let rec list_contains_sublist (#a:eqtype) (needle haystack : list a)
  : Tot bool (decreases haystack) =
  match haystack with
  | [] -> Nil? needle
  | _ :: rest -> list_is_prefix needle haystack || list_contains_sublist needle rest

let string_contains (s sub : string) : bool =
  list_contains_sublist (String.list_of_string sub) (String.list_of_string s)

let string_to_iri (s : string) : option wf_iri =
  if is_iri s then Some s else None

module Lh = RDF.List.Helpers

(** 6.1 IRI resolution against BASE (§5.1.1) **)

(* Resolve a relative IRI reference against a base IRI per RFC 3986.
   If the reference has a scheme, it is returned as-is.
   Fragment references (#foo) are appended to the base (after removing
   any existing fragment). Otherwise, the reference replaces the last
   path segment of the base. *)
(* Helper: find the index after "://" in a char list, or None *)
let rec find_scheme_end (cs : list char) (pos : nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | c1 :: c2 :: c3 :: rest ->
    if c1 = FStar.Char.char_of_int 58 (* ':' *)
       && c2 = FStar.Char.char_of_int 47 (* '/' *)
       && c3 = FStar.Char.char_of_int 47 (* '/' *)
    then Some (pos + 3)
    else find_scheme_end (c2 :: c3 :: rest) (pos + 1)
  | _ -> None

(* Helper: find the index of the first '/' at or after pos in a char list *)
let rec find_slash_from (cs : list char) (pos : nat) (cur : nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> None
  | c :: rest ->
    if cur >= pos && c = FStar.Char.char_of_int 47 (* '/' *)
    then Some cur
    else find_slash_from rest pos (cur + 1)

(* Helper: find the index of the last '/' in a char list *)
let rec find_last_slash (cs : list char) (cur : nat) (last : option nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> last
  | c :: rest ->
    if c = FStar.Char.char_of_int 47 (* '/' *)
    then find_last_slash rest (cur + 1) (Some cur)
    else find_last_slash rest (cur + 1) last

(* Helper: take the first n characters from a char list *)
let rec take_chars (n : nat) (cs : list char) : Tot (list char) (decreases n) =
  if n = 0 then []
  else match cs with
    | [] -> []
    | c :: rest -> c :: take_chars (n - 1) rest

(* Helper: remove fragment (#...) from end of a char list *)
let rec remove_fragment (cs : list char) (last_hash : option nat) (cur : nat)
  : Tot (option nat) (decreases cs) =
  match cs with
  | [] -> last_hash
  | c :: rest ->
    if c = FStar.Char.char_of_int 35 (* '#' *)
    then remove_fragment rest (Some cur) (cur + 1)
    else remove_fragment rest last_hash (cur + 1)

(* Resolve a relative IRI reference against a base IRI.
   Simplified implementation covering common SPARQL cases. *)
let resolve_iri (base : wf_iri) (relative : string) : wf_iri =
  let base_chars = String.list_of_string base in
  let rel_chars = String.list_of_string relative in
  (* If relative contains "://", it's absolute *)
  if string_contains relative "://" then
    (* relative is absolute — it must contain ':' since it contains "://" *)
    base   (* fallback: if relative isn't a valid IRI, return base *)
  else if String.length relative = 0 then
    base
  else
    let result_chars =
      let first_char = List.Tot.hd rel_chars in
      if first_char = FStar.Char.char_of_int 35 (* '#' *) then
        (* Fragment: append to base after removing any existing fragment *)
        match remove_fragment base_chars None 0 with
        | Some hash_pos -> Lh.append_tr (take_chars hash_pos base_chars) rel_chars
        | None -> Lh.append_tr base_chars rel_chars
      else if first_char = FStar.Char.char_of_int 47 (* '/' *) then
        (* Absolute path: use scheme+authority from base *)
        match find_scheme_end base_chars 0 with
        | Some after_scheme ->
          (* Find the next '/' after "://" for end of authority *)
          (match find_slash_from base_chars after_scheme 0 with
           | Some auth_end -> Lh.append_tr (take_chars auth_end base_chars) rel_chars
           | None -> Lh.append_tr base_chars rel_chars)
        | None -> Lh.append_tr base_chars rel_chars
      else
        (* Relative: replace everything after last '/' in base *)
        match find_last_slash base_chars 0 None with
        | Some slash_pos -> Lh.append_tr (take_chars (slash_pos + 1) base_chars) rel_chars
        | None -> Lh.append_tr base_chars (Lh.append_tr [FStar.Char.char_of_int 47] rel_chars)
    in
    (* The result should be a valid IRI since all branches preserve the base
       scheme prefix (which contains ':'). Rather than proving list_has_colon
       through take_chars (which would require additional lemmas about colon
       preservation over list operations), we use a runtime is_iri check
       with a fallback to the base IRI. No admit() is needed. *)
    let result = String.string_of_list result_chars in
    if is_iri result then result
    else base  (* fallback to base if result somehow isn't valid *)

(* Prefix namespace IRIs are resolved against BASE during parsing.
   All IRIs in the query body are then resolved against BASE.
   This ensures that relative IRIs like <x> or <#x> become absolute. *)
let resolve_query_iri (base : option wf_iri) (rel : string) : option wf_iri =
  match base with
  | Some b -> Some (resolve_iri b rel)
  | None -> string_to_iri rel
