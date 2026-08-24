# Both module lists are DERIVED from the repository on every run.
#
# They used to be read from two text files in the session scratchpad.
# That directory is per-session and is deleted with the container, so
# the tool either crashed on a fresh session or -- worse -- read a
# snapshot taken before the newest ports and reported a stale count.
# It did exactly that on 2026-08-23: a landed module was reported as
# not covered because the cached Lean list predated it. A measurement
# tool must not depend on a cache the measurer has to remember to
# refresh. See hazard #28 in skills/workflow-gotchas-debugging.
import os, sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FSTAR_DIR = os.path.join(REPO, "formal", "fstar")
LEAN_DIR = os.path.join(REPO, "formal", "lean4", "L4Factoidal")
import tempfile
D = os.environ.get("LEAN_PORT_GAP_OUT", tempfile.gettempdir())

fs = sorted(f[:-4] for f in os.listdir(FSTAR_DIR) if f.endswith(".fst"))

ln = set()
for root, _dirs, files in os.walk(LEAN_DIR):
    for f in files:
        if not f.endswith(".lean"):
            continue
        rel = os.path.relpath(os.path.join(root, f), LEAN_DIR)
        ln.add(rel[:-5].replace(os.sep, "."))

if not fs or not ln:
    sys.exit("lean-port-gap: found %d F* and %d Lean modules -- wrong "
             "working tree?" % (len(fs), len(ln)))
alias={
 "Parser.XML":"XML.Parser","Parser.NTriples":"Syntax.NTriples","Parser.NQuads":"Syntax.NQuads",
 "Parser.Turtle":"Syntax.Turtle","Parser.TriG":"Syntax.TriG","Parser.RDFXML":"Syntax.RdfXml",
 "Parser.IRI":"Syntax.IriResolve","Parser.JSON":"JSON.Parser","Parser.XPath":"XPath.Expr",
 "Parser.ShExC":"ShEx.Compact","Parser.OWLFunctional":"OWL.FunctionalSyntax",
 "Parser.Combinators":"Syntax.Lexing","Parser.TurtleScanner":"Syntax.Lexing",
 "RDF.Term":"RDF.Core","RDF.Triple":"RDF.Core","RDF.Graph.Executable":"RDF.Graph",
 "RDF.GraphIsomorphism":"RDF.Isomorphism","RDF.Indexed":"OWL.RLClosureIndexed",
 "RDF.NQuads.Serialize":"Syntax.NQuads",
 # RDF.NQuads.Streaming is ported across Syntax/NQuadsStreaming.lean
 # (splitter + dataset chunk fold), Syntax/NQuadsConcat.lean (the
 # line-boundary concatenation lemma), Syntax/NQuadsHomomorphism.lean
 # (streamParse11_eq_batch) and Syntax/NQuadsFold.lean (the generic
 # consumer: foldQuadLinesAcc / streamConsume / batchConsume /
 # streamConsume11_eq_batch, with fuel independence and concatenation
 # proved once over the accumulator type and the dataset case obtained
 # by parseQuadLinesAcc_eq_fold). Definition-level audit, 2026-08-24:
 # 118 F* names, every one resolved by hand.
 #  * ~40 splitter/stream/consumer names map directly (is_nl -> isNl,
 #    split_complete_lines -> splitCompleteLines and its three
 #    invariants, stream_state/feed_chunk/finish/stream_parse ->
 #    StreamState/feedChunk/finish/streamParse, feed_chunk_consume /
 #    finish_consume / stream_consume / batch_consume -> feedChunkC /
 #    finishC / streamConsume / batchConsume, fold_nquads_acc_eq_
 #    parse_nquads_acc -> parseQuadLinesAcc_eq_fold, the staged
 #    single-chunk/no-newline/ends-in-newline theorems subsumed by the
 #    general streamParse11_eq_batch / streamConsume11_eq_batch).
 #  * ~55 names are the witness-and-shift machinery (line_witness,
 #    blank/comment/quad_ok/quad_fail witnesses, lw_*, chain_*,
 #    shift_line_witness, every lemma_*_step_shift / _restart /
 #    _full_via_chain / _skip_blanks). ABSENT BY DESIGN, replaced by a
 #    different decomposition: the F* parser walks a string by integer
 #    offset, so a mid-document restart needs witnesses shifted to the
 #    new offsets; the Lean parser walks a List Char and restarts on a
 #    suffix at the true offset, so the same obligations are carried by
 #    Syntax/LocalitySkips, LocalitySuffix, LocalityCount and
 #    foldQuadLines11_fuel_indep instead.
 #  * 7 names are F*-string workarounds (cong_string_of_list,
 #    empty_string_concat_left/right, string_concat_assoc,
 #    lemma_fs_byte_index_concat, lemma_byte_index_at_middle,
 #    concat_all): List.append lemmas and List.flatten in Lean core.
 #  * quad_step and never_stop are adapter/flag glue for F*'s
 #    fold_nquads signature; the Lean consume takes Triple and
 #    Option Subject directly and the fold has no early-stop hook.
 "RDF.NQuads.Streaming":"Syntax.NQuadsStreaming",
 "RDF.Turtle.Serialize":"Syntax.TurtleSerialize",
 "RDF.Store.Loader":"RDF.StoreLoader",
 "RDF.Store.Capabilities":"RDF.StoreCapabilities",
 "RDF.Store.Columnar.DeltaMerge":"RDF.StoreDeltaMerge",
 "RDF.Store.Capabilities.Delta":"RDF.StoreCapabilitiesDelta",
 "RIF.Core.Refinement":"RIF.EngineTheorems",
 "SPARQL11.Parser.TokenRoundTrip":"SPARQL.TokenRoundTrip",
 "Tableau.CountingOracle":"OWL.CountingOracle",
 "Parser.BallyhooCOTTAS":"Cottas.Ballyhoo",
 "RIF.Core.Conformance":"RIF.Conformance",
  # Audited 2026-08-23 against the Lean module headers, one at a time.
 # Each of these four Lean modules SAYS it is the counterpart; the two
 # candidates that did NOT say so (OWL.Semantics.Soundness,
 # RDF.Entailment.RDFS.Completeness) are deliberately left uncovered.
 "Parser.JSONLD":"JSONLD.ToRdf",
 "RDF.CottasStore.PageCache.Bounds":"Cottas.PageCache",
 "SPARQL.Protocol.RoundTrip":"SPARQL.ResultsTheorems",
 "OWL.RL.Refinement":"OWL.RLTheorems",
 "Parser.RIFXML":"RIF.Xml",
 "RDF.Entailment.RDFS.FixedPoint":"RDFS.FixedPoint",
 "SPARQL11.EntailmentRegime.RDFS":"SPARQL.EntailmentRegimeRdfs",
 "SPARQL11.Algebra.BGPRefinement":"SPARQL.BgpRefinement",
 "RDF.Store.Combine":"RDF.StoreCombine",
 "SPARQL.Diagnostics":"SPARQL.Diagnostics",
 "RML.VirtualSource":"RML.VirtualSource",
 "JSONLD.Frame":"JSONLD.Frame",
 "RDFS.SchemaSplit":"RDFS.SchemaSplit",
 "SPARQL.Protocol.Client":"SPARQL.ProtocolClient",
 "RIF.Core.Translation":"RIF.Translation",
 "RDF.Entailment.Simple.Spec":"RDF.EntailmentSimpleSpec",
 "RDF.Entailment.RDF.Spec":"RDF.EntailmentRdfSpec",
 "RDF.Entailment.RDFS.Spec":"RDF.EntailmentRdfsSpec",
 "RDF.Entailment.Simple.ModelTheory":"RDF.Semantics",
 "OWL.Semantics":"OWL.Semantics",
 "RDF.Entailment.RDFS.ModelTheory":"RDF.EntailmentRdfsModelTheory",
 "RDF.Semantics.HypothesisWitness":"RDF.SemanticsHypothesisWitness",
 "RDF.Entailment.Simple.Boundary":"RDF.EntailmentSimpleBoundary",
 "RDF.Entailment.RDFS.DatatypeClash":"RDF.EntailmentRdfsDatatypeClash",
 # PARTIAL. The domain-neutral maths core the F* tree keeps in
 # Math.Expr.fst is embedded in MathML/Core.lean instead: the same
 # five-constructor AST, exact rational arithmetic, exact roots,
 # factorial and eval. Absent there: `parse_decimal` and the
 # reasoned `MV_Undef` value type (Core uses `Option`). Filed as
 # https://github.com/danbri/factoidal/issues/557.
 "Math.Expr":"MathML.Core",
 "OWL.Closure":"OWL.RLClosure","OWL.RL.Spec":"OWL.RLRules",
 "Tableau":"OWL.Tableau","Tableau.Refute":"OWL.Refute",
 "SPARQL.HTTP.Client":"HTTP.Client","SPARQL.HTTP.RunQuery":"HTTP.RunQuery",
 "SPARQL.HTTP.Routes":"HTTP.Server","SPARQL.HTTP.Response":"HTTP.Server",
 "SPARQL.HTTP.Admin":"HTTP.Ops","SPARQL.HTTP.BackendInfo":"HTTP.Ops",
 "SPARQL.HTTP.QueriesIndex":"HTTP.Ops","SPARQL.HTTP.StaticFiles":"HTTP.Ops",
 "SPARQL.HTTP":"HTTP.Server","XSD.Datatypes":"XSD.Facets",
 "MathML.Content":"MathML.Core","MathML.Present":"MathML.Core",
 "RDF.Store.Columnar.DeltaLog":"Storage.DeltaLog","RDF.Bytes":"Storage.Bytes",
 "DID.Key":"VC.DidKey",
 "RDFS.Closure.SemiNaive":"RDFS.SemiNaive",
 "SPARQL.Update.Analysis":"SPARQL.UpdateAnalysis",
 "SPARQL.Query.Analysis":"SPARQL.QueryAnalysis",
 "RDF.Dataset.Graphs":"RDF.DatasetGraphs",
 "RDF.Canonical.Manifest":"RDF.CanonicalManifest",
 "RDF.Dataset.Merge":"RDF.DatasetMerge",
 "SPARQL.JSON.Escape":"SPARQL.JsonEscape",
 "SPARQL.Eval.Limits":"SPARQL.EvalLimits",
 "SPARQL.Eval.TimeBudget":"SPARQL.TimeBudget",
 "OWL.DirectMapping.Filter":"OWL.DirectMappingFilter",
 "RDF.Entailment.RDFSPlus":"RDFS.RDFSPlus",
 "RDF.Entailment.Simple":"RDF.Entailment",
 "RDF.Entailment.Regime":"RDF.Entailment",
 "Parser.CSVResults":"SPARQL.ResultsCsvTsv",
 "RDF.Pretty":"RDF.Pretty",
 "SPARQL.Explain":"SPARQL.Explain",
 # Verified 2026-08-23 by reading the Lean module's own header, which
 # names the F* module it ports. Module-name matching could not see
 # these; see hazard #28 in skills/workflow-gotchas-debugging.
 "RDF.IRI":"Syntax.IriResolve",
 "SPARQL11.IRI.Resolve":"Syntax.IriResolve",
 "Parser.SRX":"SPARQL.ResultsXml",
 "Parser.JSONResults":"SPARQL.ResultsJson",
 "RDF.Entailment.RDFS.RhoDFClosure":"RDFS.RdfsCore",
 "SPARQL.FullText":"SPARQL.FullText",
 "SPARQL.Update.Sandbox":"SPARQL.UpdateSandbox",
 "OWL.Tests.Manifest":"OWL.TestsManifest",
 "RDF.Vocabulary.Axioms":"RDF.VocabularyAxioms",
 "RDF.CottasStore.PresenceBitmap":"Cottas.PresenceBitmap",
 "RDF.CottasStore.CompoundPresenceBitmap":"Cottas.CompoundPresenceBitmap",
 "SPARQL.Plan.Pruning":"Cottas.PlanPruning",
 "RDF.CottasStore.PresenceWriter":"Cottas.PresenceWriter",
 "RDF.CottasStore.CompoundPresenceWriter":"Cottas.CompoundPresenceWriter",
 "RDF.CottasStore.OffsetsWriter":"Cottas.OffsetsWriter",
 "RDF.CottasStore.SubjectOffsetsWriter":"Cottas.SubjectOffsetsWriter",
 "RDF.CottasStore.LazyDict":"Cottas.LazyDict",
 "RDF.CottasStore.LazyDictRegistry":"Cottas.LazyDictRegistry",
 "RDF.Store.LazyTermCache":"Cottas.LazyTermCache",
 "RDF.CottasStore.OnDiskIndex":"Cottas.OnDiskIndex",
 "RDF.CottasStore.PageCache":"Cottas.PageCache",
 "RDF.CottasStore.DictWriter":"Cottas.DictWriter",
 "SHACL.Rules":"SHACL.Rules",
 "SHACL.NodeExpr":"SHACL.NodeExpr",
 "OWL2.SyntaxDL":"OWL.SyntaxDL",
 "SPARQL.Plan.AccessPath":"Cottas.AccessPath",
 "SPARQL.Plan.Streamable":"SPARQL.PlanStreamable",
 "RML.Sources":"RML.Sources",
 "Parser.BallyhooHDT":"HDT.Store",
 # Verified 2026-08-23 by reading the Lean module header's own "Port of
 # formal/fstar/<X>.fst" line. These used to ride on a bare leaf-name
 # match; see the coverage rule below.
 "Parser.WKT":"Geo.Wkt",
 "SPARQL11.Algebra":"SPARQL.Algebra",
 "SPARQL11.Parser":"SPARQL.Parser",
 "RDF.Vocabulary":"RDFS.Vocabulary",
 # Verified by SUBJECT MATTER rather than a header citation: the Lean
 # RIF modules are the RIF Core abstract syntax, the RIF-DTB built-ins,
 # and forward chaining over RIF Core. The evaluator differs in design
 # (substitutions where F* threads solution mappings), so this is the
 # weaker evidence class and is labelled as such.
 "RIF.Core.Syntax":"RIF.Syntax",
 "RIF.Core.Builtins":"RIF.Builtins",
 "RIF.Core.Eval":"RIF.Engine",
 "RIF.Core.Tests":"RIF.EngineTests",
 "RDF.Store.Columnar.OffsetIndex":"Cottas.OffsetIndex",
 "RDF.Store.Columnar.SubjectOffsetIndex":"Cottas.SubjectOffsetIndex",
 "RDF.Entailment.RegimeDispatch":"RDFS.RegimeDispatch",
 "SPARQL11.Expression.Refinement":"SPARQL.ExprRefinement",
 "RDF.Entailment.RDFS.Completeness":"RDFS.RhoDfCompleteness",
 "RDF.NTriples.RoundTrip":"Syntax.NTriplesRoundTrip",
 "RDF.Entailment.Simple.Refinement":"RDF.EntailmentSimpleRefinement",
 "SPARQL11.Algebra.Spec":"SPARQL.AlgebraSpec",
 "RDF.List.Helpers":"RDF.ListHelpers",
 "RDF.Store.Capabilities.Cottas":"RDF.StoreCapabilitiesCottas",
 # OWL.QueryRewrite is ported across seven Lean modules under
 # L4Factoidal/OWL/QueryRewrite*.lean. The alias points at the last of
 # them. Coverage here is an explicit decision backed by a
 # definition-level audit, not a name match: every `let` in the 1,799-line
 # F* module was matched to a Lean definition on 2026-08-24, and the 30
 # names whose spelling differs were each resolved by hand (vocabulary
 # IRIs that live in OWL/Vocabulary.lean, renames such as ps_marker_key ->
 # subjectMarkerKey, and rewrite_query_for_owl_direct, which is an alias
 # of rewrite_query). The audit also FOUND two port defects, both fixed in
 # the same landing: rewrite_bgp_flat applied only the first marker where
 # the F* source applies every intersection then the first union, and the
 # someValuesFrom arm accepted a variable owl:onProperty where the F*
 # source falls back to the leaf.
 "OWL.QueryRewrite":"OWL.QueryRewriteNested",
 # SPARQL11.Store is ported across four Lean modules under
 # L4Factoidal/SPARQL/Store*.lean. As with OWL.QueryRewrite, coverage is
 # an explicit decision backed by a definition-level audit, not a name
 # match: every `let`, `let rec` AND `and`-bound name in the 1,452-line
 # F* module was matched to a Lean definition on 2026-08-24, and the 14
 # names whose spelling differs were resolved by hand. Ten are renames
 # (estimate_tp_backend_mu -> estimateTpBackend,
 # materialize_dataset_backend -> materialiseDatasetBackend, and so on);
 # list_take_n is capsTakeN in RDF/StoreCapabilities.lean; and
 # indexed_graph_backend_for, indexed_dataset_backend_for and
 # indexed_dataset_backend_for_query have no Lean counterpart BY DESIGN,
 # for the reason already recorded for the RDF.Indexed.KeyInjectivity
 # group -- the Lean index is a Std.HashMap keyed on structured values,
 # so there are no six buckets to choose between and nothing for a
 # bucket_needs flag to select.
 #
 # The audit's own reach was a finding: an earlier pass matched only
 # `^let` and could not see the mutually recursive `and`-bound group,
 # which hid eval_pattern_backend and the two query entry points. The
 # regex above is the corrected one (hazard #28: state the method next
 # to the result).
 "SPARQL11.Store":"SPARQL.StoreDataset",
 # RDF.CottasStore.BaseWriter is ported across six Lean modules under
 # L4Factoidal/Cottas/BaseWriter*.lean. Definition-level audit, 2026-08-24:
 # 124 F* names, 53 unmatched by spelling, every one resolved by hand.
 #  * 25 are ACCUMULATOR variants (*_acc, *_racc) folded into their
 #    non-accumulator Lean forms. The F* accumulators exist for OCaml
 #    stack safety; Lean core rewrites List.append and List.flatMap to
 #    tail-recursive versions at code generation (@[csimp], finding A11),
 #    so the split serves nothing here.
 #  * 10 are renames (write_uvarint -> uvarintEncode,
 #    build_def_level_section -> defLevelSection, and so on) or stdlib
 #    substitutions (list_len -> List.length, split_pos_str_acc ->
 #    List.take/List.drop, concat_bytes_list -> List.flatten).
 #  * 4 are the per-column projections map_cq_s/p/o/g, which are
 #    rows.map (.s) in Lean.
 #  * 14 are the lemma_* version-field HEX round-trip family. They have no
 #    Lean counterpart BY DESIGN: their subject is Parquet.Footer's
 #    hex-string reader, the layer finding A4 is about, and the Lean tree
 #    reads bytes rather than hex. The byte-level fact those lemmas exist
 #    to establish -- that field 1 of the file metadata is
 #    [21, 250, 6] = version 445 -- is #guarded in
 #    Cottas/BaseWriterFileV2.lean.
 "RDF.CottasStore.BaseWriter":"Cottas.BaseWriterFileV2",
# RDF.CottasStore (2,825 lines) is ported across nine Lean modules under
# Cottas/OnDisk*.lean; the alias points at the last one. AUDIT METHOD,
# because a name is a hint and coverage is a decision
# (skills/counting-coverage): every name matched by
# `^(let (rec )?|and |assume val |noeq type |type )` in the F* module --
# 125 of them -- was resolved BY HAND against the Lean tree, not by name
# shape. A name-shape pre-pass matched only 51 of the 125; that figure is
# evidence about the PASS, not about the code (hazard #28).
# Findings of the hand pass:
#  * 8 of the module's 10 `assume val`s are not I/O at all -- they are
#    the two directions of one dictionary -- and became the fields of
#    TokenTables. `cottas_ondisk_open` is StoreIo, the opened handle
#    supplied by the caller; `cottas_ondisk_close` has no F* use site and
#    Lean has no handle to release.
#  * The ~14 walk variants (search/estimate x cached/global x tok/id x
#    limited) collapse to walkRangeTok, walkCandidatesTok,
#    walkRangeCount, walkCandidatesCount and walkCandidatesLimitedTok.
#    The id-shaped variants are recovered by mapping rowOfTok, which
#    layer 2 PROVES is the relation (filterSeq_eq_map_filterTokSeq_start)
#    rather than asserting it.
#  * The two sidecar prunes (compound predicate-object, subject offsets)
#    are StoreIo parameters on purpose: compound_po_dict_encode resolves
#    ids through the .p.dict sorted-rank space and NOT through the lazy
#    runtime's first-occurrence space, and the F* source documents that
#    mixing them prunes the row group holding the pair. Their loop bodies
#    ARE ported (subjectRangeCandidateRgsLoop).
#  * filter_zipped_rows_limited (list shape) has no in-tree callers
#    post-2.5c per its own comment; it is covered by filterListTok plus
#    the limit, and the list/indexed shape equivalence is proved
#    (filterTokSeq_eq_filterListTok_start).
# Two defects were found by the port and filed rather than fixed:
# issue 571 (a corrupt row group and an empty one give the same answer)
# and issue 572 (the selective exact-count and the full count disagree on
# a null cell in an unbound column).
 "RDF.CottasStore":"Cottas.OnDiskCountExact",
# SPARQL11.Parser.AskBgpRoundTrip is covered by TWO Lean modules:
# SPARQL/AskBgpRoundTrip.lean (the fragment predicate, printer, expected
# tokens and the payload scan lemmas) and SPARQL/AskBgpRoundTripString.lean
# (the string round trip). The alias points at the second.
#
# This is the one module where the Lean tree proves MORE than the F* one,
# and the F* source says so itself. Its banner marks stage (a) --
# `tokenize (print_query_1 q) == expected_tokens_1 q` -- as IMPOSSIBLE,
# with a counter-probe, because FStar.String.sub's ulib specification
# exposes a length refinement and nothing relating its output characters
# to its input. Every payload-carrying token is blocked by that, not just
# this fragment's.
#
# The Lean lexer scans `List Char`, so scanIriBody and scanVarName have
# ordinary equation lemmas, and askBgp_string_roundtrip is proved.
# The obstruction was never about RDF or SPARQL: it was one library's
# interface to one datatype, which is exactly the kind of difference the
# two-tree design exists to separate out.
#
# The proof also produced issue 573: writing the theorem's side condition
# forced the question of WHICH IRI bodies round-trip, and the answer is
# narrower than the specification -- <1abc> is a valid IRIREF that both
# trees mis-lex, confirmed on the committed binary. iriFirstOk is the
# honest side condition until that is fixed.
 "SPARQL11.Parser.AskBgpRoundTrip":"SPARQL.AskBgpRoundTripString",
}
# ---------------------------------------------------------------------------
# What counts as coverage.
#
# An explicit alias, or a match on the LAST TWO name components. A bare
# last-component match does NOT count.
#
# It used to. On 2026-08-23 a new `HDT/Store.lean` made `SPARQL11.Store`
# (1,452 lines) vanish from the not-covered list, because both end in
# "Store". Auditing the rest found thirteen more modules resting on a
# bare leaf match, of which seven were wrong the same way -- including
# two whose alias TARGET does not exist (`RDF.Serialize`), so the broken
# alias was silently rescued by the leaf match and the breakage was
# invisible. See hazard #31 in skills/workflow-gotchas-debugging.
#
# Everything genuine that relied on a bare leaf match is now an explicit
# alias, each verified by reading the Lean module's own header.
# ---------------------------------------------------------------------------
def leafkeys(m):
    p = m.split('.')
    return {(p[-2] + "." + p[-1]).lower()} if len(p) > 1 else {p[-1].lower()}

lidx = set()
for m in ln:
    lidx |= leafkeys(m)

covered, missing, broken_alias = [], [], []
for m in fs:
    if m in alias:
        if alias[m] in ln:
            covered.append(m)
            continue
        broken_alias.append((m, alias[m]))
    if leafkeys(m) & lidx:
        covered.append(m)
    else:
        missing.append(m)

if broken_alias:
    print("BROKEN ALIASES -- the target Lean module does not exist:")
    for m, t in broken_alias:
        print(f"  {m} -> {t}")
    print()
def lines(m):
    try: return sum(1 for _ in open(os.path.join(FSTAR_DIR, m + ".fst"),encoding='utf-8',errors='replace'))
    except: return 0
from collections import defaultdict
g=defaultdict(list)
for m in missing: g[m.split('.')[0]].append(m)
out=[]
out.append(f"F* modules: {len(fs)}. Covered by a Lean module: {len(covered)}. Not covered: {len(missing)}.\n")
rows=[(k,len(g[k]),sum(lines(m) for m in g[k]),sorted(g[k])) for k in g]
rows.sort(key=lambda r:-r[2])
out.append("| Group | Modules | F* lines |")
out.append("|---|---|---|")
for k,n,tot,ms in rows: out.append(f"| `{k}.*` | {n} | {tot} |")
out.append(f"| **Total** | **{len(missing)}** | **{sum(r[2] for r in rows)}** |\n")
for k,n,tot,ms in rows:
    out.append(f"### {k} — {n} modules, {tot} lines\n")
    for m in ms: out.append(f"- `{m}` ({lines(m)} lines)")
    out.append("")
GAP_MD = os.path.join(D, "gap.md")
open(GAP_MD, "w").write("\n".join(out))
print("\n".join(out[:22]))

# ---------------------------------------------------------------------------
# Classified summary. Hand-maintained numbers in the design doc drifted
# three times in one session (2026-08-23); generating them here is the
# fix. PROOF modules are F* files whose content is a proof ABOUT the F*
# implementation -- the Lean tree carries its own theorem layer, so a
# module-for-module count is the wrong measure for that column and it is
# reported as UNKNOWN rather than as a gap. BY-DESIGN modules have no
# Lean counterpart because the reason they exist is absent in Lean.
# ---------------------------------------------------------------------------
PROOF_SUFFIXES = (".Spec", ".Refinement", ".ModelTheory", ".Completeness",
                  ".Axioms", ".RoundTrip", ".Soundness")
# Parser.NTriples.Locality MOVED here from BY_DESIGN_EXACT, 2026-08-24.
# It was the only entry in that set with NO reason recorded beside it,
# and the reason it would have needed is false. Its own banner says it
# exists because two theorems -- theorem_stream_eq_batch (task #48) and
# the N-Triples round trip -- both need "a reader behaves identically on
# `complete ^ carry` at any position inside `complete` as it does on
# `complete` alone", and that F* cannot get there cheaply because Z3 has
# no associativity theory for FStar.String.strcat over symbolic operands.
#
# The Lean tree does NOT escape that obligation. A list-based reader can
# still read past the end of a prefix: `List.span isBnodeChar` on
# "_:abc" stops at end-of-input and on "_:abc" ++ "d" consumes the d as
# well, so `readBlankNodeLabel` is not local without a stopped-short
# side condition. Two #guards in Syntax/Locality.lean exhibit that pair.
# What IS different is the register -- list suffixes instead of byte
# offsets, so the proofs are structural inductions -- which is a reason
# the Lean version is smaller, not a reason it is unnecessary.
#
# PROOF rather than engine: the module's own header calls it PROOF-ONLY
# and it is not in build-ocaml.sh. Syntax/Locality.lean is the Lean
# tree's counterpart layer, carrying the pilot the F* program itself
# chose (the IRI scanner) plus the refutation that fixes the side
# condition. The emit-step case and everything above it remain unproved
# and are named in that module's header;
# https://github.com/danbri/factoidal/issues/570 tracks the streaming
# theorem that needs them.
PROOF_EXACT = {"OWL.Semantics", "Parser.NTriples.Locality"}
BY_DESIGN_PREFIXES = ("Parser.FastString",)
# The four index-key-repair modules (2026-08-23). The F* index builds a
# composite bucket key by concatenating strings, and that key is not
# injective, because `is_iri` admits U+001F. KeyInjectivity proves the
# one-sided injectivity, SepFree proves that every RDFS closure row keeps
# a graph free of U+001F, ChainWf folds the rows into the chain, and
# RDF.Indexed.Completeness proves the bucket coverage direction from three
# FStar.String.compare axioms. The Lean index is a `Std.HashMap` keyed on
# STRUCTURED values (`Subject`, `WfIri`, `Subject x WfIri`, `WfIri x Term`),
# so there is no separator character, no composite string key, and no side
# condition to discharge: `OWL.RLClosureIndexed.Wf.ofGraph` holds for every
# graph. See docs/designissues/2026-08-23-lean-port-gap.md.
# Two more, 2026-08-23, for the SAME structural reason.
#  * OWL.Semantics.MemLemmas is membership-preservation infrastructure
#    for the F* bucket_tree build: tree_ok / lemma_slt_tree_ok /
#    lemma_build_bucket_ok plus five lemma_build_indexed_wf_* rows, and
#    lemmas about List.Tot.sortWith / partition / rev that exist ONLY
#    because that build sorts and partitions. The Lean index does
#    neither -- Index.ofGraph folds HashMap.insert, BucketWf is an
#    equation between a lookup and a filter -- and OWL/RLTheorems.lean
#    proves the same soundness results without any of it.
#  * RDF.CottasStore.ColumnSeq is `assume new type cottas_column` plus
#    O(1) accessors, realised in OCaml as `string option array`. Its own
#    banner gives the reason: the F*-pure decoders produce
#    `list (option string)` and every walk cons-cell-chases, so F* needs
#    an array-shaped abstract type to retire the OCaml perf shim. Lean
#    has Array natively and totally; `Array.size`, `arr[i]?` and
#    `Array.toList` are the whole module.
#  * RDF.List.Helpers WAS on this list and was removed 2026-08-24. The
#    by-design reasoning was right about the CAUSE -- Lean core ships
#    `List.appendTR` and `List.flatMapTR` under `@[csimp]`, so the
#    compiler substitutes a tail-recursive version with no call-site
#    change and the stack-overflow incidents that produced the F* module
#    cannot recur. It was wrong to conclude no counterpart was wanted.
#    `RDF/ListHelpers.lean` transcribes the three F* functions arm for
#    arm, so the two trees can be compared on the SPARQL/RIF hot path,
#    and `appendTr_eq_core` proves the F* accumulator and
#    `List.appendTR` are the same algorithm. The module is now COVERED,
#    which is why the count moved from 193 to 194 in that landing.
BY_DESIGN_EXACT = {"RDF.Indexed.KeyInjectivity",
                   "RDF.Indexed.Completeness",
                   "RDF.Entailment.RDFS.SepFree",
                   "RDF.Entailment.RDFS.ChainWf",
                   "OWL.Semantics.MemLemmas",
                   "RDF.CottasStore.ColumnSeq"}

def classify(m):
    # BY-DESIGN is tested FIRST: `RDF.Indexed.Completeness` ends in a
    # PROOF_SUFFIX, and the by-design reason is the stronger statement.
    if m.startswith(BY_DESIGN_PREFIXES) or m in BY_DESIGN_EXACT: return "bydesign"
    if m.endswith(PROOF_SUFFIXES) or m in PROOF_EXACT: return "proof"
    return "engine"

buckets = {"engine": [], "proof": [], "bydesign": []}
for m in missing:
    buckets[classify(m)].append(m)

out.append("")
out.append("## Summary (generated -- do not hand-edit)")
out.append("")
out.append("| Kind | Modules | F\\* lines |")
out.append("|---|---|---|")
lab = {"engine": "Engine and specification code — to port",
       "proof": "Proofs about the F\\* implementation — see below",
       "bydesign": "F\\*-only machinery with no Lean counterpart by design"}
for k in ("engine", "proof", "bydesign"):
    n = len(buckets[k]); tot = sum(lines(m) for m in buckets[k])
    out.append(f"| {lab[k]} | {n} | {tot} |")
out.append(f"| **Total not covered** | **{len(missing)}** | "
           f"**{sum(lines(m) for m in missing)}** |")
out.append("")
out.append(f"{len(covered)} of {len(fs)} F\\* modules have a Lean counterpart.")

print('\n'.join(out))
print("\nfull group listing written to " + GAP_MD)
