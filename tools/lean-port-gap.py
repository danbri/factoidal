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
PROOF_EXACT = {"OWL.Semantics"}
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
BY_DESIGN_EXACT = {"RDF.List.Helpers",
                   "RDF.Indexed.KeyInjectivity",
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
