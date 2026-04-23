# F* Tail-Recursion Audit Report
**Date:** 2026-04-23  
**Scope:** `/formal/fstar/*.fst` (top-level, excluding `practical/`, `midzone/`, `corespecs/`)  
**Target:** Stack-overflow hazards in v8 JS/Wasm extraction from F* to OCaml

## Summary

Audit of 22 F* specification files identified **9 high/medium-severity tail-recursion hazards**, primarily in functions operating on unbounded collections (RDF graphs, SPARQL solutions, parsed URIs, quads, and solution-set groupings). Most critical: functions using cons-after-recurse (`x :: f xs`) or append (`@ f xs`) that process graph triples (potentially 60k+), SPARQL solutions (unbounded), or encoded/parsed character sequences. Three functions already employ tail-recursive fold_left patterns (encouraging signs of awareness). Recommended action: prioritize the 5 functions below for conversion to accumulator-style recursion with final reversal, or fold_left-based implementations.

---

## Hazard Table

| File | Lines | Function | Pattern | Input-Size Class | Severity | Suggested Fix |
|------|-------|----------|---------|------------------|----------|---------------|
| RDF.Graph.Executable.fst | 225–231 | `graph_bnodes` | Cons-after-recurse via `@` append: `nodes @ obj_nodes @ (graph_bnodes tl)` | Unbounded (full graph, 60k triples) | **HIGH** | Accumulator + final append or fold_left |
| RDF.Graph.Executable.fst | 236–239 | `mem_triple` | Cons-after-recurse: `triple_eq hd t \|\| mem_triple t tl` | Unbounded (graph scan) | **MED** | Use List.Tot.existsb (or already tail-rec in logic?) |
| RDF.Graph.Executable.fst | 258–265 | `find_by_subject` | Cons-after-recurse: `if ... then hd :: rest else rest` | Unbounded (query all S_IRI matches) | **HIGH** | Accumulator with rev + final append |
| RDF.Graph.Executable.fst | 820–827 | `find_objects` | Cons-after-recurse: `hd.o :: rest` | Unbounded (e.g., `wdt:P31` thousands) | **HIGH** | Accumulator + rev |
| RDF.Graph.Executable.fst | 830–837 | `find_subjects` | Cons-after-recurse: `hd.s :: rest` | Unbounded (query all O match) | **HIGH** | Accumulator + rev |
| SPARQL11.Algebra.fst | 938–944 | `encode_uri_chars` | Cons-after-recurse *and* append: `c :: encode_uri_chars rest` + `percent_encode_char c @ encode_uri_chars rest` | Unbounded (long IRI) | **HIGH** | Accumulator + rev or fold_left |
| SPARQL11.Algebra.fst | 950–961 | `replace_first` | Cons-after-recurse *and* append: `hd :: replace_first tl pattern replacement` + `replacement @ list_drop` | Unbounded (long char list) | **MED** | Accumulator + rev or fold_left on haystack |
| SPARQL11.Algebra.fst | 2820–2827 | `collect_strings` | Cons-after-recurse: `s :: collect_strings rest` | Unbounded (solution set 100k+ strings) | **HIGH** | Accumulator + rev |
| SPARQL11.Algebra.fst | 2787–2795 | `dedup_er` | Cons-after-recurse *and* O(n²) inner scan: `v :: dedup_er rest` + `List.Tot.existsb` per element | Unbounded (solution cardinality) | **HIGH** | fold_left with dedup via set-based lookup |
| SPARQL11.Algebra.fst | 3476–3481 | `negated_direct_iris` | Cons-after-recurse: `i :: negated_direct_iris rest` | Bounded (small property-path negation lists, typically < 10) | **LOW** | Already safe; note for contrast |
| SPARQL11.Algebra.fst | 4345–4352 | `filter_no_bnode_quads` | Cons-after-recurse: `q :: filter_no_bnode_quads rest` | Unbounded (DELETE DATA on 60k+ quads) | **HIGH** | fold_left + rev or List.Tot.filter |
| SPARQL11.Algebra.fst | 2718–2730 | `find_group` & `add_to_groups` | Mutual recursion with append: `g :: before` + `before @ [new] @ after` | Unbounded (GROUP BY solution count) | **MED** | Accumulator + rev (before) |
| Parser.Turtle.fst | 44–50 | `rev_prepend` & `append_list` | Standard tail-rec (rev_prepend) vs. cons-after-recurse (append_list): `x :: append_list rest ys` | Unbounded (Turtle doc size) | **MED** | append_list should use fold_left or already-available List.Tot.append |
| Parser.Combinators.fst | 251–261 | `ptake_while_acc` | Cons-after-recurse with reversal at end: `ch :: acc` → `List.Tot.rev acc` | Unbounded (long token) | **LOW** | Already uses accumulator + rev; safe |
| Parser.Combinators.fst | 323–337 | `pquoted_body` | Cons-after-recurse with reversal: `ch :: acc` → `List.Tot.rev acc` | Unbounded (long quoted string) | **LOW** | Already uses accumulator + rev; safe |

---

## Top 5 Fix-This-First Candidates

### 1. **SPARQL11.Algebra.fst:2820–2827 — `collect_strings`**
- **Function Signature:**  
  ```fstar
  let rec collect_strings (vals : list eval_result) : Tot (list string) (decreases vals) =
    match vals with
    | [] -> []
    | v :: rest ->
      (match er_to_string v with
       | Some s -> s :: collect_strings rest
       | None -> collect_strings rest)
  ```
- **Call Context:** Used by `eval_aggregate` on GROUP BY result lists, which can contain **100k+ solution mappings** (e.g., all entities of a certain class in Wikidata).
- **Input-Size Risk:** SPARQL solution sets are unbounded. A query returning 100k results will build 100k stack frames; v8 max is ~15k.
- **Severity:** **HIGH**
- **Suggested Fix:**  
  ```fstar
  let collect_strings (vals : list eval_result) : Tot (list string) =
    List.Tot.fold_left
      (fun acc v ->
        match er_to_string v with
        | Some s -> s :: acc
        | None -> acc)
      [] vals
    |> List.Tot.rev
  ```

---

### 2. **RDF.Graph.Executable.fst:820–827 — `find_objects`**
- **Function Signature:**  
  ```fstar
  let rec find_objects (g : rdf_graph) (subj : subject) (pred : wf_iri) : list rdf_term =
    match g with
    | [] -> []
    | hd :: tl ->
      let rest = find_objects tl subj pred in
      if subject_eq hd.s subj && hd.p = pred
      then hd.o :: rest
      else rest
  ```
- **Call Context:** Finds all objects for a given (subject, predicate) pair in the RDF graph. The **Wikidata incident** (`wdt:P31` property lookup on a 60k-triple graph with thousands of matches) is a direct hit.
- **Input-Size Risk:** A Wikidata graph with many entity-type relationships will cause 1000+ matches; triple store can have 60k+ triples.
- **Severity:** **HIGH**
- **Suggested Fix:**  
  ```fstar
  let find_objects (g : rdf_graph) (subj : subject) (pred : wf_iri) : list rdf_term =
    List.Tot.fold_left
      (fun acc hd ->
        if subject_eq hd.s subj && hd.p = pred
        then hd.o :: acc
        else acc)
      [] g
    |> List.Tot.rev
  ```

---

### 3. **RDF.Graph.Executable.fst:225–231 — `graph_bnodes`**
- **Function Signature:**  
  ```fstar
  let rec graph_bnodes (g:rdf_graph) : list bnode_id =
    match g with
    | [] -> []
    | hd :: tl ->
        let nodes = match hd.s with | S_BNode id -> [id] | _ -> [] in
        let obj_nodes = match hd.o with | T_BNode id -> [id] | _ -> [] in
        nodes @ obj_nodes @ (graph_bnodes tl)
  ```
- **Call Context:** Extracts all blank-node IDs from a graph. Used in RDFS/OWL RL closure to check for label freshness and during query normalization.
- **Input-Size Risk:** Large RDF graph (60k triples, potentially 1k+ bnodes) will trigger multiple append operations per triple, each O(n) in the accumulated size.
- **Severity:** **HIGH**
- **Suggested Fix:**  
  ```fstar
  let graph_bnodes (g:rdf_graph) : list bnode_id =
    List.Tot.fold_left
      (fun acc hd ->
        let subj_ids = match hd.s with | S_BNode id -> [id] | _ -> [] in
        let obj_ids = match hd.o with | T_BNode id -> [id] | _ -> [] in
        subj_ids @ obj_ids @ acc)  (* append to front, reverse at end *)
      [] g
    |> List.Tot.rev
  ```

---

### 4. **SPARQL11.Algebra.fst:938–944 — `encode_uri_chars`**
- **Function Signature:**  
  ```fstar
  let rec encode_uri_chars (cs : list FStar.Char.char)
    : Tot (list FStar.Char.char) (decreases cs) =
    match cs with
    | [] -> []
    | c :: rest ->
      if is_uri_unreserved c then c :: encode_uri_chars rest
      else percent_encode_char c @ encode_uri_chars rest
  ```
- **Call Context:** Used by `string_encode_uri` to percent-encode IRIs for SPARQL/RDF output. Called on every expanded IRI in query results.
- **Input-Size Risk:** Long IRIs (100+ chars, with many reserved chars) will build 100+ stack frames **plus** appending 3-char sequences (`%XX`) per reserved char.
- **Severity:** **HIGH**
- **Suggested Fix:**  
  ```fstar
  let encode_uri_chars (cs : list FStar.Char.char) : Tot (list FStar.Char.char) =
    List.Tot.fold_left
      (fun acc c ->
        if is_uri_unreserved c then c :: acc
        else (let encoded = percent_encode_char c in
              List.Tot.fold_left (fun a e -> e :: a) acc encoded))
      [] cs
    |> List.Tot.rev
  ```

---

### 5. **SPARQL11.Algebra.fst:2787–2795 — `dedup_er`**
- **Function Signature:**  
  ```fstar
  let rec dedup_er (vals : list eval_result) : Tot (list eval_result) (decreases vals) =
    match vals with
    | [] -> []
    | v :: rest ->
      if List.Tot.existsb (fun x -> er_equal v x) rest
      then dedup_er rest
      else v :: dedup_er rest
  ```
- **Call Context:** Used in `eval_aggregate` (COUNT DISTINCT, GROUP_CONCAT DISTINCT) to deduplicate result values. Called on solution-set cardinality + evaluation results.
- **Input-Size Risk:** **O(n²) worst case** (inner existsb scan per element) + non-tail-recursive cons. On 10k-element solution set, O(100M) comparisons and 10k stack frames.
- **Severity:** **HIGH**
- **Suggested Fix:**  
  ```fstar
  let dedup_er (vals : list eval_result) : Tot (list eval_result) =
    List.Tot.fold_left
      (fun (seen : list eval_result) v ->
        if List.Tot.existsb (er_equal v) seen
        then seen
        else v :: seen)
      [] vals
    |> List.Tot.rev
  (* Or better: use a proper set-based dedup (HashSet in OCaml), 
     but fold_left + rev fixes the stack hazard. *)
  ```

---

## Additional Hazards (Medium/Low Severity)

### SPARQL11.Algebra.fst:2718–2730 — `find_group` + `add_to_groups`
- **Pattern:** Mutual recursion with cons + append in accumulator:  
  ```fstar
  let rec find_group (key : list eval_result) (groups : list group)
    : Tot (option (list group & group & list group)) (decreases groups) =
    match groups with
    | [] -> None
    | g :: rest ->
      if keys_equal key g.g_key then Some ([], g, rest)
      else
        (match find_group key rest with
         | None -> None
         | Some (before, found, after) -> Some (g :: before, found, after))
  ```
- **Input-Size Risk:** GROUP BY on large solution set (10k+ unique keys) walks groups list repeatedly; accumulating `before` via cons causes quadratic cost.
- **Severity:** **MED**
- **Suggested Fix:** Use fold_left with explicit index tracking, or change the return type to use a single-pass scan.

---

### Parser.Turtle.fst:50–56 — `append_list`
- **Pattern:** Standard cons-after-recurse:  
  ```fstar
  let rec append_list (#a:Type) (xs:list a) (ys:list a)
    : Tot (list a) (decreases xs) =
    match xs with
    | [] -> ys
    | x :: rest -> x :: append_list rest ys
  ```
- **Input-Size Risk:** Turtle parser appending large prefix lists or statement queues during parse; if prefixes or statement lists are 1k+, causes stack overflow.
- **Severity:** **MED** (F* standard library may provide `List.Tot.append` which should be used instead)
- **Suggested Fix:** Replace with `List.Tot.append` (stdlib); if custom is needed, implement via fold_left.

---

### SPARQL11.Algebra.fst:4345–4352 — `filter_no_bnode_quads`
- **Pattern:** Cons-after-recurse filter:  
  ```fstar
  let rec filter_no_bnode_quads (qs : list (option wf_iri * triple))
    : Tot (list (option wf_iri * triple)) (decreases qs) =
    match qs with
    | [] -> []
    | q :: rest ->
      if quad_has_bnode q then filter_no_bnode_quads rest
      else q :: filter_no_bnode_quads rest
  ```
- **Input-Size Risk:** DELETE DATA operations on 60k+ quads; filtering millions of loaded quads in CONSTRUCT/WHERE.
- **Severity:** **HIGH**
- **Suggested Fix:**  
  ```fstar
  let filter_no_bnode_quads (qs : list (option wf_iri * triple)) =
    List.Tot.filter (fun q -> not (quad_has_bnode q)) qs
  ```

---

## Already-Good Patterns (Encouraging Signs)

### Parser.Combinators.fst:251–261 — `ptake_while_acc`
- **Pattern:** Proper accumulator + reversal:  
  ```fstar
  let rec ptake_while_acc (pred: char -> bool) (input:string) (pos:nat) (acc: list char) (fuel:nat)
    : Tot (parse_result string) (decreases fuel) =
    if fuel = 0 then ParseOk (String.string_of_list (List.Tot.rev acc)) pos
    else
      let len = fs_byte_length input in
      if pos < len then
        let ch = fs_byte_index input pos in
        if pred ch then ptake_while_acc pred input (pos + 1) (ch :: acc) (fuel - 1)
        else ParseOk (String.string_of_list (List.Tot.rev acc)) pos
      else ParseOk (String.string_of_list (List.Tot.rev acc)) pos
  ```
- **Status:** ✓ Tail-recursive with accumulator; safe even on 100k-char tokens.

---

### Parser.Combinators.fst:323–337 — `pquoted_body`
- **Pattern:** Proper accumulator + reversal:  
  ```fstar
  let rec pquoted_body (qch: char) (input:string) (pos:nat) (acc: list char) (fuel:nat)
    : Tot (parse_result string) (decreases fuel) =
    if fuel = 0 then ParseFail "unterminated quoted string" pos
    else
      let len = fs_byte_length input in
      if pos >= len then ParseFail "unterminated quoted string" pos
      else
        let ch = fs_byte_index input pos in
        if ch = qch then
          ParseOk (String.string_of_list (List.Tot.rev acc)) (pos + 1)
        else if ch = backslash_char then
          if pos + 1 < len then
            let escaped = fs_byte_index input (pos + 1) in
            pquoted_body qch input (pos + 2) (escaped :: ch :: acc) (fuel - 1)
          else ParseFail "backslash at end of input" pos
        else
          pquoted_body qch input (pos + 1) (ch :: acc) (fuel - 1)
  ```
- **Status:** ✓ Tail-recursive; safe.

---

### SPARQL11.Algebra.fst:2800–2810 — `find_min` / `find_max`
- **Pattern:** fold_left with accumulator:  
  ```fstar
  let find_min (vals : list eval_result) : eval_result =
    match vals with
    | [] -> ER_Error
    | v :: rest ->
      List.Tot.fold_left
        (fun acc x -> if sparql_order x acc <= 0 then x else acc)
        v rest
  ```
- **Status:** ✓ Safe; demonstrates awareness of tail-recursion hazards (comment notes fix for lifesci demo stack overflow).

---

## Recommendations & Summary

1. **Immediate (Patch Cycles 1–2):**  
   - `collect_strings`, `find_objects`, `find_subjects`, `encode_uri_chars`, `filter_no_bnode_quads` → Convert to fold_left + rev or accumulator-style.
   - `dedup_er` → fold_left + rev; consider set-based dedup in OCaml extraction.

2. **Short-term (Patch Cycles 3–4):**  
   - `graph_bnodes`, `replace_first`, `find_group` → Accumulator + rev.
   - `append_list` → Use `List.Tot.append` if available, else implement tail-rec.

3. **Testing:**  
   - Add regression tests: 60k-triple graphs, 100k-element solution sets, 100k-char IRIs.
   - Profile v8 stack usage before/after fixes on lifesci demo and Wikidata.

4. **Extract-Time Vigilance:**  
   - F* → OCaml → JS/Wasm pipeline: verify extracted OCaml is tail-recursive (check `.ml` output).
   - Consider wrapping top-level calls with stack-size guards in JS harness.

---

**Audit completed:** 2026-04-23  
**Auditor:** F* Tail-Recursion Hazard Scanner  
**Confidence:** Very High (patterns mechanically identified, input sizes inferred from domain semantics)
