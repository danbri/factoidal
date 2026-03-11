#!/usr/bin/bash


#curl -sO "https://raw.githubusercontent.com/RaresM7373/rdf-turtle/refs/heads/master/turtle/General_Country_Info_Dataset.ttl" > data/third_party/General_Country_Info_Dataset.ttl

curl -sL https://raw.githubusercontent.com/RaresM7373/rdf-turtle/refs/heads/master/turtle/General_Country_Info_Dataset.ttl > data/third_party/General_Country_Info_Dataset.ttl

# :Country\/IR a :Country ; :iso_3166-1_alpha-2_code 'IR'^^xsd:string ; :iso_3166-1_alpha-3_code 'IRN'^^xsd:string ; :iso_3166-1_numeric_code '364'^^xsd:string ; :country_name 'Iran'^^xsd:string ; skos:prefLabel 'Iran'@en ; :area_in_sq_km '1648000'^^xsd:double ; :population '81800269'^^xsd:integer .

# :has_country_neighbour

factoidal -d data/third_party/General_Country_Info_Dataset.ttl -e ' 
PREFIX : <http://example.com/demo/> 
SELECT ?nc WHERE {
:Country\/IR :has_country_neighbour ?nc .
} '
