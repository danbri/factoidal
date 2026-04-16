#!/usr/bin/bash


curl --silent http://www.ivan-herman.net/foaf.rdf > data/third_party/ivan_foaf.rdf

# factoidal --dump --format rdfxml data/third_party/ivan_foaf.rdf

/home/danbri/working/sandbox/foaf25/codex/factoidal/formal/fstar/ocaml-output/factoidal -d data/third_party/ivan_foaf.rdf -e '
  PREFIX foaf: <http://xmlns.com/foaf/0.1/>
  SELECT ?person ?name ?rel
  WHERE 
  { 
    ?person foaf:name ?name .
    <https://www.ivan-herman.net/foaf#me> ?rel ?person .
  } '
