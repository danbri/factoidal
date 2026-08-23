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
