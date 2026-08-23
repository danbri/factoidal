D="/tmp/claude-0/-home-user-factoidal/55df18c7-5121-5dfd-9568-3f65b4548058/scratchpad"
fs=[l.strip() for l in open(D+"/fstar-modules.txt") if l.strip()]
ln=set(l.strip() for l in open(D+"/lean-modules.txt") if l.strip())
alias={
 "Parser.XML":"XML.Parser","Parser.NTriples":"Syntax.NTriples","Parser.NQuads":"Syntax.NQuads",
 "Parser.Turtle":"Syntax.Turtle","Parser.TriG":"Syntax.TriG","Parser.RDFXML":"Syntax.RdfXml",
 "Parser.IRI":"Syntax.IriResolve","Parser.JSON":"JSON.Parser","Parser.XPath":"XPath.Expr",
 "Parser.ShExC":"ShEx.Compact","Parser.OWLFunctional":"OWL.FunctionalSyntax",
 "Parser.Combinators":"Syntax.Lexing","Parser.TurtleScanner":"Syntax.Lexing",
 "RDF.Term":"RDF.Core","RDF.Triple":"RDF.Core","RDF.Graph.Executable":"RDF.Graph",
 "RDF.GraphIsomorphism":"RDF.Isomorphism","RDF.Indexed":"OWL.RLClosureIndexed",
 "RDF.NQuads.Serialize":"RDF.Serialize","RDF.Turtle.Serialize":"RDF.Serialize",
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
 "RDF.Entailment.RegimeDispatch":"RDFS.RegimeDispatch",
}
def leafkeys(m):
    p=m.split('.'); s={p[-1].lower()}
    if len(p)>1: s.add((p[-2]+"."+p[-1]).lower())
    return s
lidx=set()
for m in ln: lidx |= leafkeys(m)
covered,missing=[],[]
for m in fs:
    if (m in alias and alias[m] in ln) or (leafkeys(m) & lidx): covered.append(m)
    else: missing.append(m)
def lines(m):
    try: return sum(1 for _ in open("/home/user/factoidal/formal/fstar/"+m+".fst",encoding='utf-8',errors='replace'))
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
open(D+"/gap.md","w").write("\n".join(out))
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
BY_DESIGN_EXACT = {"RDF.List.Helpers"}

def classify(m):
    if m.endswith(PROOF_SUFFIXES) or m in PROOF_EXACT: return "proof"
    if m.startswith(BY_DESIGN_PREFIXES) or m in BY_DESIGN_EXACT: return "bydesign"
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
