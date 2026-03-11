#!/usr/bin/bash

curl --silent http://www.ivan-herman.net/foaf.rdf > data/third_party/ivan_foaf.rdf

# Dump the NTriples of a graph from an RDF/XML file

factoidal --dump --format rdfxml data/third_party/ivan_foaf.rdf
