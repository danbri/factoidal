#!/bin/bash

curl -sL "http://dbpedia.org/data/Berlin.ttl" > data/third_party/Berlin.ttl


#  | factoidal -d - -e 'PREFIX dbo: <http://dbpedia.org/ontology/>
#    SELECT ?pop WHERE { ?s dbo:populationTotal ?pop }'
