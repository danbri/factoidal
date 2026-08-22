/-
L4Factoidal.SPARQL.UpdateParser — the SPARQL 1.1 Update grammar,
productions [29]–[52] of "SPARQL 1.1 Query Language" §19.8 (the
Update grammar shares the query grammar's table).

Port of `formal/fstar/SPARQL11.Parser.fst` Part 9 — `parse_iri_ref`,
`parse_graph_ref_graph_only`, `parse_graph_ref_all`,
`parse_graph_or_default`, `parse_silent`, the `gp_has_var` /
`gp_has_bnode` / `gp_has_nested_graph_under_graph` validators,
`parse_quad_block` / `parse_quad_data`, `parse_single_update_op`,
`parse_using_list`, `parse_modify_after_with`, `parse_update_seq`,
`bnode_labels_unique_across_data_ops`, and the entry points
`parse_sparql_update_with_base` / `parse_sparql_update_12_with_base`.

The terminal layer is `SPARQL/Tokenizer.lean` (it already emits every
Update keyword); templates and WHERE clauses reuse the QUERY parser's
`pTriplesBlock`, `pGroupGraphPattern`, `pGraphName` and `pPrologue`
unchanged, exactly as the F* reuses `parse_triples_block` and
`parse_group_graph_pattern`.

WELL-FORMEDNESS REJECTIONS (message text is the F*'s verbatim):

  | message | rule |
  |---|---|
  | `INSERT DATA must not contain variables` | [48] QuadData is ground (§3.1.1, W3C syntax-update-bad-04) |
  | `DELETE DATA must not contain variables` | §3.1.2 (bad-03) |
  | `DELETE DATA must not contain blank nodes` | §3.1.2 (bad-12) |
  | `INSERT DATA: nested GRAPH blocks not allowed`, `DELETE DATA: …` | [50] QuadsNotTriples holds a TriplesTemplate, not Quads (bad-05) |
  | `DELETE WHERE must not contain blank nodes` | §3.1.3.3 (bad-10) |
  | `DELETE template must not contain blank nodes` | §3.1.3 (bad-11) |
  | `unexpected ';' (no preceding update operation)` | [29] Update — `;;` (bad-08, bad-09) |
  | `missing ';' between update operations` | [29] (bad-07) |
  | `blank node label reused across INSERT DATA / DELETE DATA ops (SPARQL 1.1 Update §19.6)` | §19.6 (syntax-update-54) |
  | `unexpected tokens after update request` | the stream must end at EOF |

TERMINATION: structural on a `fuel : Nat`, seeded with the query
parser's `topFuel`, as in the F* (`decreases fuel`). No `partial`, no
well-founded recursion.
-/
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-! ## Small productions -/

/-- [135] iri — an IRIREF or a prefixed name, resolved (port of
`parse_iri_ref`). -/
def pIriRef (st : PState) (ts : TStream) : Except ParseError (WfIri × TStream) :=
  match peekTok ts with
  | .iri i =>
      (match mkIri? i with
       | some wi => .ok (wi, advTok ts)
       | none    => pErr "invalid IRI" ts)
  | .pname pn =>
      (match resolvePnameIri st pn with
       | some wi => .ok (wi, advTok ts)
       | none    => pErr "unresolved PNAME prefix" ts)
  | _ => pErr "expected IRI or prefixed name" ts

/-- [46] GraphRef ::= 'GRAPH' iri (port of `parse_graph_ref_graph_only`). -/
def pGraphRef (st : PState) (ts : TStream) : Except ParseError (WfIri × TStream) :=
  match peekTok ts with
  | .graph => pIriRef st (advTok ts)
  | _      => pErr "expected GRAPH <iri>" ts

/-- [45] GraphRefAll ::= GraphRef | 'DEFAULT' | 'NAMED' | 'ALL' (port of
`parse_graph_ref_all`). -/
def pGraphRefAll (st : PState) (ts : TStream) : Except ParseError (GraphRef × TStream) :=
  match peekTok ts with
  | .defaultKw => .ok (.default, advTok ts)
  | .named     => .ok (.named, advTok ts)
  | .allKw     => .ok (.all, advTok ts)
  | .graph     => do
      let (i, ts1) ← pGraphRef st ts
      .ok (.graph i, ts1)
  | _ => pErr "expected DEFAULT, NAMED, ALL, or GRAPH <iri>" ts

/-- [44] GraphOrDefault ::= 'DEFAULT' | 'GRAPH'? iri (port of
`parse_graph_or_default`). -/
def pGraphOrDefault (st : PState) (ts : TStream) : Except ParseError (GraphRef × TStream) :=
  match peekTok ts with
  | .defaultKw => .ok (.default, advTok ts)
  | .graph     => do
      let (i, ts1) ← pIriRef st (advTok ts)
      .ok (.graph i, ts1)
  | .iri _ | .pname _ => do
      let (i, ts1) ← pIriRef st ts
      .ok (.graph i, ts1)
  | _ => pErr "expected DEFAULT or [GRAPH] <iri>" ts

/-- An optional `SILENT` (port of `parse_silent`). -/
def pSilent (ts : TStream) : Bool × TStream :=
  match peekTok ts with
  | .silent => (true, advTok ts)
  | _       => (false, ts)

/-! ## Validators — §3.1.1, §3.1.2, §3.1.3 restrictions on templates -/

/-- Port of `bgp_has_any_var`. -/
def bgpHasVar (b : Bgp) : Bool :=
  b.any (fun tp =>
    (match tp.s with | .var _ => true | _ => false) ||
    (match tp.p with | .var _ => true | _ => false) ||
    (match tp.o with | .var _ => true | _ => false))

/-- Does a QuadData block contain a variable (or anything else that is
not ground data — a property path, VALUES, a sub-pattern)? Port of
`gp_has_var`. -/
def patHasVar : QueryPattern → Bool
  | .bgp b            => bgpHasVar b
  | .empty            => false
  | .join a b         => patHasVar a || patHasVar b
  | .graph (.var _) _ => true
  | .graph _ inner    => patHasVar inner
  | .propertyPath _ _ _ => true
  | .leftJoin a b _   => patHasVar a || patHasVar b
  | .union a b        => patHasVar a || patHasVar b
  | .minus a b        => patHasVar a || patHasVar b
  | .lateral a b      => patHasVar a || patHasVar b
  | .filter _ inner   => patHasVar inner
  | .bind _ _ inner   => patHasVar inner
  | .values _ _       => true
  | .service _ _ _    => true
  | .serviceVar _ _ _ => true
  | .subSelect _      => true

/-- Port of `bgp_has_any_bnode`. -/
def bgpHasBnode (b : Bgp) : Bool :=
  b.any (fun tp =>
    (match tp.s with | .bnode _ => true | _ => false) ||
    (match tp.p with | .bnode _ => true | _ => false) ||
    (match tp.o with | .bnode _ => true | _ => false))

/-- Port of `gp_has_bnode`. -/
def patHasBnode : QueryPattern → Bool
  | .bgp b            => bgpHasBnode b
  | .empty            => false
  | .join a b         => patHasBnode a || patHasBnode b
  | .graph _ inner    => patHasBnode inner
  | .propertyPath s _ o =>
      (match s with | .bnode _ => true | _ => false) ||
      (match o with | .bnode _ => true | _ => false)
  | .leftJoin a b _   => patHasBnode a || patHasBnode b
  | .union a b        => patHasBnode a || patHasBnode b
  | .minus a b        => patHasBnode a || patHasBnode b
  | .lateral a b      => patHasBnode a || patHasBnode b
  | .filter _ inner   => patHasBnode inner
  | .bind _ _ inner   => patHasBnode inner
  | .values _ _       => false
  | .service _ _ inner    => patHasBnode inner
  | .serviceVar _ _ inner => patHasBnode inner
  | .subSelect _      => false

/-- Port of `gp_has_graph_anywhere`. -/
def patHasGraph : QueryPattern → Bool
  | .graph _ _      => true
  | .join a b       => patHasGraph a || patHasGraph b
  | .filter _ inner => patHasGraph inner
  | .bind _ _ inner => patHasGraph inner
  | _               => false

/-- A `GRAPH` block nested inside a `GRAPH` block — [50]
QuadsNotTriples admits only a TriplesTemplate inside. Port of
`gp_has_nested_graph_under_graph`. -/
def patHasNestedGraph : QueryPattern → Bool
  | .graph _ inner => patHasGraph inner
  | .join a b      => patHasNestedGraph a || patHasNestedGraph b
  | _              => false

/-! ## [48]–[51] QuadData / QuadPattern / Quads / QuadsNotTriples -/

/-- [49] Quads ::= TriplesTemplate? ( QuadsNotTriples '.'?
TriplesTemplate? )* — the body of a `{ … }` quad block: default-graph
triples blocks interleaved with `GRAPH VarOrIri { TriplesTemplate? }`
blocks, joined in order. Port of `parse_quad_block`. -/
def pQuadBlock (fuel : Nat) (st : PState) (acc : QueryPattern) (ts : TStream) :
    Except ParseError (QueryPattern × TStream) :=
  match fuel with
  | 0     => .ok (acc, ts)
  | f + 1 =>
    match peekTok ts with
    | .rbrace => .ok (acc, ts)
    | .graph => do
        let (gn, ts2) ← pGraphName f st (advTok ts)
        let (_, ts3)  ← expectTok .lbrace ts2
        match peekTok ts3 with
        | .rbrace =>
            let ts4 := advTok ts3
            let ts4 := if peekTok ts4 == Token.dot then advTok ts4 else ts4
            pQuadBlock f st (ggpJoin acc (.graph gn .empty)) ts4
        | _ => do
            let (inner, ts4) ← pTriplesBlock f st .empty ts3
            let (_, ts5)     ← expectTok .rbrace ts4
            let ts5 := if peekTok ts5 == Token.dot then advTok ts5 else ts5
            pQuadBlock f st (ggpJoin acc (.graph gn inner)) ts5
    | _ =>
        match pTriplesBlock f st .empty ts with
        | .error _            => .ok (acc, ts)
        | .ok (triples, ts1)  => pQuadBlock f st (ggpJoin acc triples) ts1

/-- [48] QuadData ::= '{' Quads '}' (also [47] QuadPattern, the
template form). Port of `parse_quad_data`. -/
def pQuadData (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError (QueryPattern × TStream) := do
  let (_, ts1) ← expectTok .lbrace ts
  let (g, ts2) ← pQuadBlock fuel st .empty ts1
  let (_, ts3) ← expectTok .rbrace ts2
  .ok (g, ts3)

/-- [43] UsingClause ::= 'USING' ( iri | 'NAMED' iri ), zero or more
(port of `parse_using_list`). -/
def pUsingList (fuel : Nat) (st : PState) (acc : List DatasetClause) (ts : TStream) :
    Except ParseError (List DatasetClause × TStream) :=
  match fuel with
  | 0     => .ok (acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .using =>
        let ts1 := advTok ts
        (match peekTok ts1 with
         | .named => do
             let (i, ts2) ← pIriRef st (advTok ts1)
             pUsingList f st (.named i :: acc) ts2
         | _ => do
             let (i, ts2) ← pIriRef st ts1
             pUsingList f st (.default i :: acc) ts2)
    | _ => .ok (acc.reverse, ts)

/-- An optional `INSERT { … }` template after a DELETE template. -/
def pInsertTemplateOpt (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError (Option QueryPattern × TStream) :=
  match peekTok ts with
  | .insert => do
      let (t, ts1) ← pQuadData fuel st (advTok ts)
      .ok (some t, ts1)
  | _ => .ok (none, ts)

/-- The tail of [41] Modify after its templates: `UsingClause* 'WHERE'
GroupGraphPattern`. -/
def pModifyRest (fuel : Nat) (st : PState) (withIri : Option WfIri)
    (deleteTmpl insertTmpl : Option QueryPattern) (ts : TStream) :
    Except ParseError (UpdateOp × TStream) := do
  let (usingClauses, ts1) ← pUsingList fuel st [] ts
  let (_, ts2)            ← expectTok .whereKw ts1
  let (wherePat, ts3)     ← pGroupGraphPattern fuel st ts2
  .ok (.modify withIri deleteTmpl insertTmpl usingClauses wherePat, ts3)

/-- [41] Modify after `WITH iri`: a DELETE and/or INSERT clause, or the
`DELETE WHERE` shorthand (port of `parse_modify_after_with`, which
keeps the F*'s reading of `WITH <g> DELETE WHERE { P }` as a Modify
whose DELETE template is `P`). -/
def pModifyAfterWith (fuel : Nat) (st : PState) (withIri : Option WfIri) (ts : TStream) :
    Except ParseError (UpdateOp × TStream) :=
  match peekTok ts with
  | .delete =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .whereKw => do
           let (pat, ts2) ← pGroupGraphPattern fuel st (advTok ts1)
           if patHasBnode pat then pErr "DELETE WHERE must not contain blank nodes" ts1
           else .ok (.modify withIri (some pat) none [] pat, ts2)
       | .lbrace => do
           let (del, ts2) ← pQuadData fuel st ts1
           if patHasBnode del then pErr "DELETE template must not contain blank nodes" ts1
           else do
             let (ins, ts3) ← pInsertTemplateOpt fuel st ts2
             pModifyRest fuel st withIri (some del) ins ts3
       | _ => pErr "expected { or WHERE after DELETE" ts1)
  | .insert =>
      let ts1 := advTok ts
      (match peekTok ts1 with
       | .lbrace => do
           let (ins, ts2) ← pQuadData fuel st ts1
           pModifyRest fuel st withIri none (some ins) ts2
       | _ => pErr "expected { after INSERT" ts1)
  | _ => pErr "expected DELETE or INSERT after WITH <iri>" ts

/-- [30] Update1 — one operation (port of `parse_single_update_op`). -/
def pUpdateOp (fuel : Nat) (st : PState) (ts : TStream) :
    Except ParseError (UpdateOp × TStream) :=
  match fuel with
  | 0     => pErr "update op recursion limit" ts
  | f + 1 =>
    match peekTok ts with
    -- [31] Load ::= 'LOAD' 'SILENT'? iri ( 'INTO' GraphRef )?
    | .load =>
        let (silent, ts2) := pSilent (advTok ts)
        (do
          let (src, ts3) ← pIriRef st ts2
          match peekTok ts3 with
          | .into => do
              let (dst, ts4) ← pGraphRef st (advTok ts3)
              .ok (.load silent src (some dst), ts4)
          | _ => .ok (.load silent src none, ts3))
    -- [32] Clear ::= 'CLEAR' 'SILENT'? GraphRefAll
    | .clear =>
        let (silent, ts2) := pSilent (advTok ts)
        (do
          let (gr, ts3) ← pGraphRefAll st ts2
          .ok (.clear silent gr, ts3))
    -- [33] Drop ::= 'DROP' 'SILENT'? GraphRefAll
    | .drop =>
        let (silent, ts2) := pSilent (advTok ts)
        (do
          let (gr, ts3) ← pGraphRefAll st ts2
          .ok (.drop silent gr, ts3))
    -- [34] Create ::= 'CREATE' 'SILENT'? GraphRef
    | .create =>
        let (silent, ts2) := pSilent (advTok ts)
        (do
          let (i, ts3) ← pGraphRef st ts2
          .ok (.create silent i, ts3))
    -- [35]–[37] Add / Move / Copy ::= KW 'SILENT'? GraphOrDefault 'TO' GraphOrDefault
    | .addKw | .move | .copy =>
        let kw := peekTok ts
        let (silent, ts2) := pSilent (advTok ts)
        (do
          let (src, ts3) ← pGraphOrDefault st ts2
          let (_, ts4)   ← expectTok .to ts3
          let (dst, ts5) ← pGraphOrDefault st ts4
          match kw with
          | .addKw => .ok (.add silent src dst, ts5)
          | .move  => .ok (.move silent src dst, ts5)
          | _      => .ok (.copy silent src dst, ts5))
    -- [38] InsertData ::= 'INSERT DATA' QuadData
    -- [42] InsertClause ::= 'INSERT' QuadPattern (the Modify form)
    | .insert =>
        let ts1 := advTok ts
        (match peekTok ts1 with
         | .data => do
             let (data, ts3) ← pQuadData f st (advTok ts1)
             if patHasVar data then pErr "INSERT DATA must not contain variables" ts1
             else if patHasNestedGraph data then pErr "INSERT DATA: nested GRAPH blocks not allowed" ts1
             else .ok (.insertData data, ts3)
         | .lbrace => do
             let (ins, ts2) ← pQuadData f st ts1
             pModifyRest f st none none (some ins) ts2
         | _ => pErr "expected DATA or { after INSERT" ts1)
    -- [39] DeleteData, [40] DeleteWhere, [42] DeleteClause
    | .delete =>
        let ts1 := advTok ts
        (match peekTok ts1 with
         | .data => do
             let (data, ts3) ← pQuadData f st (advTok ts1)
             if patHasVar data then pErr "DELETE DATA must not contain variables" ts1
             else if patHasBnode data then pErr "DELETE DATA must not contain blank nodes" ts1
             else if patHasNestedGraph data then pErr "DELETE DATA: nested GRAPH blocks not allowed" ts1
             else .ok (.deleteData data, ts3)
         | .whereKw => do
             let (pat, ts3) ← pGroupGraphPattern f st (advTok ts1)
             if patHasBnode pat then pErr "DELETE WHERE must not contain blank nodes" ts1
             else .ok (.deleteWhere pat, ts3)
         | .lbrace => do
             let (del, ts2) ← pQuadData f st ts1
             if patHasBnode del then pErr "DELETE template must not contain blank nodes" ts1
             else do
               let (ins, ts3) ← pInsertTemplateOpt f st ts2
               pModifyRest f st none (some del) ins ts3
         | _ => pErr "expected DATA, WHERE, or { after DELETE" ts1)
    -- [41] Modify with a leading 'WITH' iri
    | .withKw => do
        let (w, ts2) ← pIriRef st (advTok ts)
        pModifyAfterWith f st (some w) ts2
    | _ => pErr "expected update operation" ts

/-! ## [29] Update — the ';'-separated sequence -/

/-- Port of `parse_update_seq`. A prologue may recur between
operations (§2.1 — `PREFIX` / `BASE` are allowed before each
operation); a `;` is valid only directly after an operation, and two
operations need a `;` between them. -/
def pUpdateSeq (fuel : Nat) (st : PState) (acc : List UpdateOp) (needSep : Bool)
    (ts : TStream) : Except ParseError (PState × List UpdateOp × TStream) :=
  match fuel with
  | 0     => .ok (st, acc.reverse, ts)
  | f + 1 =>
    match peekTok ts with
    | .eof => .ok (st, acc.reverse, ts)
    | .prefixKw | .baseKw | .versionKw => do
        let (st', ts1) ← pPrologue f st ts
        pUpdateSeq f st' acc false (resolveIriTokens st'.base ts1)
    | .semi =>
        if needSep then pUpdateSeq f st acc false (advTok ts)
        else pErr "unexpected ';' (no preceding update operation)" ts
    | _ =>
        if needSep then pErr "missing ';' between update operations" ts
        else do
          let (op, ts1) ← pUpdateOp f st ts
          pUpdateSeq f st (op :: acc) true ts1

/-- §19.6: a blank-node label used in one INSERT DATA / DELETE DATA
block may not reappear in another block of the same request (port of
`labeled_bnodes_in_data_op` / `bnode_labels_unique_across_data_ops`).
Template labels are exempt — they are fresh per operation at run
time (§3.1.3.2). -/
def labeledBnodesInDataOp : UpdateOp → List String
  | .insertData g => ggpLabeledBnodes g
  | .deleteData g => ggpLabeledBnodes g
  | _             => []

def bnodeLabelsUniqueAcrossDataOps (seen : List String) : List UpdateOp → Bool
  | []        => true
  | op :: rest =>
      let labels := labeledBnodesInDataOp op
      if strOverlaps labels seen then false
      else bnodeLabelsUniqueAcrossDataOps (strUnion labels seen) rest

/-! ## Entry points -/

/-- Parse a SPARQL 1.1 Update request. `base` is the BASE in scope
before the prologue (the request IRI, Protocol §2.2.3); `version`
selects the 1.1 or 1.2 terminal layer. Port of
`parse_sparql_update_with_base` / `parse_sparql_update_12_with_base`.
The fuel is a parameter for the same reason `parseSparqlWith`'s is
(see `Parser.lean`). -/
def parseSparqlUpdateWith (fuel : Nat) (text : String) (base : Option String)
    (version : SparqlVersion) : Except ParseError Update :=
  let toks := tokenizeAt version text
  match firstInvalidToken toks with
  | some e => .error e
  | none =>
    let toks := match base with
      | some _ => resolveIriTokens base toks
      | none   => toks
    match pUpdateSeq fuel { base := base, v12 := version.is12 } [] false toks with
    | .error e => .error e
    | .ok (st, ops, rest) =>
      if !tokensOnlyEof rest then .error ⟨"unexpected tokens after update request", peekPos rest⟩
      else if !bnodeLabelsUniqueAcrossDataOps [] ops then
        .error ⟨"blank node label reused across INSERT DATA / DELETE DATA ops (SPARQL 1.1 Update §19.6)", 0⟩
      else .ok { base := st.base, prefixes := st.prefixes, ops := ops }

/-- Parse at the query parser's fuel seed. -/
def parseSparqlUpdate (text : String) (base : Option String := none)
    (version : SparqlVersion := .v11) : Except ParseError Update :=
  parseSparqlUpdateWith topFuel text base version

end L4Factoidal.SPARQL
