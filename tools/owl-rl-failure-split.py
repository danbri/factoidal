#!/usr/bin/env python3
"""Classify the l4owl-probe FAIL lines by the FIRST missing conclusion
triple, into the buckets of
docs/designissues/2026-09-04-owl-rl-resplit.md.

Usage:
  formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl > run.txt
  python3 tools/owl-rl-failure-split.py run.txt

Reads the probe run given on the command line and nothing else, so it
cannot report a cached tree (anti-pattern 30). It classifies on the
PREDICATE of the first missing triple, and for rdf:type on its object;
the blind spots of that method are listed in the design document.
"""
import re, sys, collections

def main(path):
    RDF="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
    RDFS="http://www.w3.org/2000/01/rdf-schema#"
    OWL="http://www.w3.org/2002/07/owl#"
    def sh(t):
        for p,n in ((RDF,"rdf:"),(RDFS,"rdfs:"),(OWL,"owl:")):
            if t.startswith("<"+p): return n+t[1+len(p):-1]
        return t
    STRUCT={"owl:unionOf","owl:intersectionOf","owl:complementOf","owl:oneOf",
     "owl:someValuesFrom","owl:allValuesFrom","owl:hasValue","owl:hasSelf",
     "owl:onProperty","owl:onClass","owl:onDataRange","owl:onDatatype",
     "owl:cardinality","owl:minCardinality","owl:maxCardinality",
     "owl:qualifiedCardinality","owl:minQualifiedCardinality","owl:maxQualifiedCardinality",
     "owl:withRestrictions","owl:datatypeComplementOf","owl:members","owl:distinctMembers",
     "owl:propertyChainAxiom","owl:disjointUnionOf","rdf:first","rdf:rest"}
    STRUCT_TYPES={"owl:Restriction","owl:AllDifferent","owl:AllDisjointClasses",
     "owl:AllDisjointProperties","owl:DataRange","rdf:List","owl:NegativePropertyAssertion"}
    ANNOT={"rdfs:comment","rdfs:label","rdfs:seeAlso","rdfs:isDefinedBy","owl:versionInfo"}
    SCHEMA={"rdfs:subClassOf","rdfs:subPropertyOf","rdfs:domain","rdfs:range",
     "owl:equivalentClass","owl:equivalentProperty","owl:disjointWith","owl:inverseOf",
     "owl:propertyDisjointWith"}
    SCHEMA_TYPES={"owl:FunctionalProperty","owl:InverseFunctionalProperty",
     "owl:TransitiveProperty","owl:SymmetricProperty","owl:AsymmetricProperty",
     "owl:ReflexiveProperty","owl:IrreflexiveProperty","owl:ObjectProperty",
     "owl:DatatypeProperty","owl:AnnotationProperty","owl:Class","rdfs:Class",
     "rdf:Property","rdfs:Datatype","owl:Ontology"}
    buckets=collections.defaultdict(list)
    for line in open(path):
        line=line.rstrip("\n")
        if not line.startswith("FAIL "): continue
        m=re.match(r"^FAIL (.*?) \[(\w+)\]: (\w[\w-]*): (.*)$", line)
        if not m:
            buckets["UNPARSED"].append(line); continue
        ident,ttype,tag,rest=m.groups()
        key=f"{ident} [{ttype}]"
        if tag!="closure-gap":
            buckets["C"].append(key); continue
        if rest.startswith("no clash row fired"):
            buckets["B3"].append(key); continue
        if rest.startswith("no single blank-node mapping"):
            buckets["B6"].append(key); continue
        if rest.startswith("every non-conclusion triple"):
            buckets["B4"].append(key); continue
        mm=re.match(r"^missing (\S+) (\S+) (.*?) \(closure .*$", rest)
        if not mm:
            buckets["UNPARSED"].append(line); continue
        s,p,o=mm.groups(); p=sh(p); o=sh(o.strip()); s=sh(s)
        tail=" | "+p+(" "+o if p=="rdf:type" else "")
        if p in STRUCT or (p=="rdf:type" and o in STRUCT_TYPES):
            buckets["B1"].append(key+tail)
        elif p=="rdf:type" and o.startswith("_:"):
            buckets["B1"].append(key+" | rdf:type BNODE-class")
        elif p in ANNOT:
            buckets["B2"].append(key+tail)
        elif p in SCHEMA or (p=="rdf:type" and o in SCHEMA_TYPES):
            buckets["B7"].append(key+tail)
        else:
            buckets["B5"].append(key+tail)
    for b in ["C","B1","B2","B3","B4","B5","B6","B7","UNPARSED"]:
        print("### %s: %d" % (b, len(buckets[b])))
        for x in sorted(buckets[b]): print("   ",x)

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print(__doc__)
        raise SystemExit(2)
    main(sys.argv[1])
