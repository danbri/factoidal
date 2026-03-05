//! SPARQL tests against a larger, more realistic graph.
//!
//! Tests the SPARQL engine with a 100+ triple graph covering:
//! - Multiple entity types (people, organizations, publications)
//! - Numeric and date-typed literals
//! - Language-tagged strings
//! - Multi-hop joins
//! - OPTIONAL with missing data
//! - DISTINCT on larger result sets
//! - ORDER BY + LIMIT on realistic data
//! - FILTER with various functions
//! - Complex graph patterns

/// Build a rich test graph using Turtle (parsed by our own parser).
fn large_graph() -> rdf_wasm::RdfGraph {
    let turtle = r#"
@prefix rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
@prefix ex:   <http://example.org/> .
@prefix xsd:  <http://www.w3.org/2001/XMLSchema#> .
@prefix dc:   <http://purl.org/dc/elements/1.1/> .
@prefix dct:  <http://purl.org/dc/terms/> .

# === People ===

ex:alice a foaf:Person ;
    foaf:name "Alice Smith" ;
    foaf:name "Alice Smith"@en ;
    foaf:age "30"^^xsd:integer ;
    foaf:mbox <mailto:alice@example.org> ;
    foaf:knows ex:bob, ex:charlie, ex:dana ;
    ex:worksAt ex:acme ;
    ex:skill "RDF", "SPARQL", "Rust" .

ex:bob a foaf:Person ;
    foaf:name "Bob Jones" ;
    foaf:name "Bob Jones"@en ;
    foaf:age "25"^^xsd:integer ;
    foaf:mbox <mailto:bob@example.org> ;
    foaf:knows ex:alice ;
    ex:worksAt ex:acme ;
    ex:skill "Python", "SPARQL" .

ex:charlie a foaf:Person ;
    foaf:name "Charlie Brown" ;
    foaf:name "Charlie Brown"@en ;
    foaf:age "35"^^xsd:integer ;
    foaf:knows ex:alice, ex:dana ;
    ex:worksAt ex:widgetco ;
    ex:skill "Java", "RDF" .

ex:dana a foaf:Person ;
    foaf:name "Dana White" ;
    foaf:name "Dana White"@en ;
    foaf:age "28"^^xsd:integer ;
    foaf:mbox <mailto:dana@example.org> ;
    foaf:knows ex:charlie ;
    ex:worksAt ex:widgetco ;
    ex:skill "F*", "Rust", "WASM" .

ex:eve a foaf:Person ;
    foaf:name "Eve Adams" ;
    foaf:name "Eve Adams"@en ;
    foaf:age "45"^^xsd:integer ;
    ex:worksAt ex:bigcorp ;
    ex:skill "Management" .

ex:frank a foaf:Person ;
    foaf:name "Frank Miller" ;
    foaf:name "Frank Miller"@en ;
    foaf:name "Frank Miller"@de ;
    foaf:age "50"^^xsd:integer ;
    foaf:knows ex:eve ;
    ex:worksAt ex:bigcorp ;
    ex:skill "Strategy", "RDF" .

# === Organizations ===

ex:acme a foaf:Organization ;
    foaf:name "Acme Corp" ;
    ex:founded "2010"^^xsd:integer ;
    ex:country "US" ;
    ex:size "50"^^xsd:integer .

ex:widgetco a foaf:Organization ;
    foaf:name "Widget Co" ;
    ex:founded "2015"^^xsd:integer ;
    ex:country "UK" ;
    ex:size "20"^^xsd:integer .

ex:bigcorp a foaf:Organization ;
    foaf:name "Big Corp International" ;
    ex:founded "1990"^^xsd:integer ;
    ex:country "US" ;
    ex:size "5000"^^xsd:integer .

# === Publications ===

ex:paper1 a ex:Publication ;
    dc:title "Verified RDF Transforms" ;
    dc:creator ex:alice, ex:dana ;
    dct:issued "2024"^^xsd:integer ;
    ex:topic "RDF", "Verification" .

ex:paper2 a ex:Publication ;
    dc:title "SPARQL Optimization Techniques" ;
    dc:creator ex:bob ;
    dct:issued "2023"^^xsd:integer ;
    ex:topic "SPARQL", "Performance" .

ex:paper3 a ex:Publication ;
    dc:title "Formal Methods for the Semantic Web" ;
    dc:creator ex:charlie, ex:alice ;
    dct:issued "2024"^^xsd:integer ;
    ex:topic "RDF", "F*", "Formal Methods" .

ex:paper4 a ex:Publication ;
    dc:title "Enterprise Knowledge Graphs" ;
    dc:creator ex:frank, ex:eve ;
    dct:issued "2022"^^xsd:integer ;
    ex:topic "Knowledge Graphs", "Enterprise" .

# === Projects ===

ex:proj1 a ex:Project ;
    foaf:name "Factoidal" ;
    ex:lead ex:alice ;
    ex:member ex:alice, ex:bob, ex:dana ;
    ex:status "active" .

ex:proj2 a ex:Project ;
    foaf:name "WidgetML" ;
    ex:lead ex:charlie ;
    ex:member ex:charlie, ex:dana ;
    ex:status "active" .

ex:proj3 a ex:Project ;
    foaf:name "Legacy System" ;
    ex:lead ex:frank ;
    ex:member ex:frank, ex:eve ;
    ex:status "completed" .
"#;

    rdf_wasm::turtle::parse(turtle).expect("Turtle parse of large graph should succeed")
}

// ---------------------------------------------------------------------------
// Basic queries on the large graph
// ---------------------------------------------------------------------------

#[test]
fn large_graph_triple_count() {
    let g = large_graph();
    // Should have a substantial number of triples
    assert!(g.len() > 100, "Expected 100+ triples, got {}", g.len());
    eprintln!("Large graph: {} triples", g.len());
}

#[test]
fn large_graph_all_people() {
    let g = large_graph();
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT ?person ?name WHERE {
           ?person rdf:type foaf:Person .
           ?person foaf:name ?name .
           FILTER (!BOUND(?name) || !CONTAINS(STR(?name), \"@\"))
         }",
    )
    .unwrap();
    // 6 people, but some have multiple name triples (en, de)
    assert!(r.rows.len() >= 6, "Expected at least 6 person-name rows, got {}", r.rows.len());
    eprintln!("People query: {} rows", r.rows.len());
}

#[test]
fn large_graph_all_organizations() {
    let g = large_graph();
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT ?org ?name WHERE {
           ?org rdf:type foaf:Organization .
           ?org foaf:name ?name
         }",
    )
    .unwrap();
    assert_eq!(r.rows.len(), 3, "Expected 3 organizations");
}

// ---------------------------------------------------------------------------
// Multi-hop joins
// ---------------------------------------------------------------------------

#[test]
fn large_graph_person_employer_name() {
    let g = large_graph();
    // Two-hop: person -> worksAt -> org name
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX ex:   <http://example.org/>
         SELECT ?personName ?orgName WHERE {
           ?person foaf:name ?personName .
           ?person ex:worksAt ?org .
           ?org foaf:name ?orgName
         }",
    )
    .unwrap();
    // 6 people * their org names (each person has 2-3 name triples)
    assert!(r.rows.len() >= 6, "Expected at least 6 person-org rows, got {}", r.rows.len());
    eprintln!("Person-employer join: {} rows", r.rows.len());
}

#[test]
fn large_graph_coauthors() {
    let g = large_graph();
    // Find pairs of people who co-authored a paper (using != to avoid self-pairs)
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX dc:  <http://purl.org/dc/elements/1.1/>
         PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         SELECT ?name1 ?name2 ?title WHERE {
           ?paper dc:creator ?p1 .
           ?paper dc:creator ?p2 .
           ?p1 foaf:name ?name1 .
           ?p2 foaf:name ?name2 .
           ?paper dc:title ?title .
           FILTER (?p1 != ?p2)
           FILTER (LANG(?name1) = \"\")
           FILTER (LANG(?name2) = \"\")
         }",
    )
    .unwrap();
    // paper1: alice+dana (both dirs), paper3: alice+charlie (both dirs), paper4: frank+eve (both dirs)
    // 3 papers x 2 directions = 6
    assert_eq!(r.rows.len(), 6, "Expected 6 co-author pairs (bidirectional), got {}", r.rows.len());
    eprintln!("Co-author pairs: {} rows", r.rows.len());
}

#[test]
fn large_graph_friends_of_friends() {
    let g = large_graph();
    // Three-hop: person -> knows -> knows -> name
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         SELECT DISTINCT ?name ?fofName WHERE {
           ?person foaf:name ?name .
           ?person foaf:knows ?friend .
           ?friend foaf:knows ?fof .
           ?fof foaf:name ?fofName .
           FILTER (?person != ?fof)
         }",
    )
    .unwrap();
    assert!(r.rows.len() >= 1, "Expected friends-of-friends results");
    eprintln!("Friends of friends: {} rows", r.rows.len());
}

// ---------------------------------------------------------------------------
// OPTIONAL with missing data
// ---------------------------------------------------------------------------

#[test]
fn large_graph_optional_email() {
    let g = large_graph();
    // Not all people have mbox
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT ?name ?email WHERE {
           ?person rdf:type foaf:Person .
           ?person foaf:name ?name .
           OPTIONAL { ?person foaf:mbox ?email }
         }",
    )
    .unwrap();
    // Should include all people, some with email, some without
    assert!(r.rows.len() >= 6, "Expected at least 6 rows (all people)");

    // Count how many have email bound
    let email_idx = r.variables.iter().position(|v| v == "email").unwrap();
    let with_email = r.rows.iter().filter(|row| row[email_idx].is_some()).count();
    let without_email = r.rows.iter().filter(|row| row[email_idx].is_none()).count();
    eprintln!("Optional email: {} with, {} without, {} total", with_email, without_email, r.rows.len());
    assert!(with_email > 0, "Some people should have email");
    assert!(without_email > 0, "Some people should lack email");
}

// ---------------------------------------------------------------------------
// DISTINCT and ORDER BY on larger sets
// ---------------------------------------------------------------------------

#[test]
fn large_graph_distinct_skills() {
    let g = large_graph();
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX ex: <http://example.org/>
         SELECT DISTINCT ?skill WHERE {
           ?person ex:skill ?skill
         }",
    )
    .unwrap();
    // Skills: RDF, SPARQL, Rust, Python, Java, F*, WASM, Management, Strategy
    assert!(r.rows.len() >= 9, "Expected at least 9 distinct skills, got {}", r.rows.len());
    eprintln!("Distinct skills: {} rows", r.rows.len());
}

#[test]
fn large_graph_order_by_name() {
    let g = large_graph();
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT ?name WHERE {
           ?person rdf:type foaf:Person .
           ?person foaf:name ?name .
           FILTER (LANG(?name) = \"\")
         } ORDER BY ASC(?name)",
    )
    .unwrap();
    // Check alphabetical ordering
    assert!(r.rows.len() >= 6, "Expected at least 6 rows");
    let names: Vec<String> = r.rows.iter()
        .filter_map(|row| row[0].as_ref())
        .map(|s| s.to_string())
        .collect();
    for i in 1..names.len() {
        assert!(
            names[i - 1] <= names[i],
            "Names not sorted: '{}' should come before '{}'",
            names[i - 1], names[i]
        );
    }
    eprintln!("Sorted names: {:?}", names);
}

#[test]
fn large_graph_limit_offset() {
    let g = large_graph();
    let all = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT ?name WHERE {
           ?person rdf:type foaf:Person .
           ?person foaf:name ?name .
           FILTER (LANG(?name) = \"\")
         } ORDER BY ASC(?name)",
    )
    .unwrap();

    let page1 = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT ?name WHERE {
           ?person rdf:type foaf:Person .
           ?person foaf:name ?name .
           FILTER (LANG(?name) = \"\")
         } ORDER BY ASC(?name) LIMIT 3",
    )
    .unwrap();

    let page2 = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT ?name WHERE {
           ?person rdf:type foaf:Person .
           ?person foaf:name ?name .
           FILTER (LANG(?name) = \"\")
         } ORDER BY ASC(?name) LIMIT 3 OFFSET 3",
    )
    .unwrap();

    assert_eq!(page1.rows.len(), 3);
    assert_eq!(page1.rows.len() + page2.rows.len(), all.rows.len());
    eprintln!("Pagination: {} total, page1={}, page2={}", all.rows.len(), page1.rows.len(), page2.rows.len());
}

// ---------------------------------------------------------------------------
// FILTER functions
// ---------------------------------------------------------------------------

#[test]
fn large_graph_filter_regex() {
    let g = large_graph();
    // People whose names contain "a" (case-insensitive)
    let r = rdf_wasm::sparql::execute(
        &g,
        r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
           PREFIX rdf:  <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
           SELECT ?name WHERE {
             ?person rdf:type foaf:Person .
             ?person foaf:name ?name .
             FILTER (LANG(?name) = "")
             FILTER (REGEX(STR(?name), "^[A-D]"))
           }"#,
    )
    .unwrap();
    // Alice, Bob, Charlie, Dana — names starting with A-D
    assert_eq!(r.rows.len(), 4, "Expected 4 people with names starting A-D, got {}", r.rows.len());
}

#[test]
fn large_graph_filter_string_functions() {
    let g = large_graph();
    // Papers with "RDF" in topic
    let r = rdf_wasm::sparql::execute(
        &g,
        r#"PREFIX ex:  <http://example.org/>
           PREFIX dc:  <http://purl.org/dc/elements/1.1/>
           SELECT ?title WHERE {
             ?paper dc:title ?title .
             ?paper ex:topic ?topic .
             FILTER (CONTAINS(STR(?topic), "RDF"))
           }"#,
    )
    .unwrap();
    // paper1 and paper3 have topic "RDF"
    assert!(r.rows.len() >= 2, "Expected at least 2 papers with RDF topic, got {}", r.rows.len());
}

#[test]
fn large_graph_filter_isiri() {
    let g = large_graph();
    // Find all IRI-valued objects for alice
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX ex: <http://example.org/>
         SELECT ?p ?o WHERE {
           ex:alice ?p ?o .
           FILTER (ISIRI(?o))
         }",
    )
    .unwrap();
    // alice's IRI objects: mbox, knows(3), worksAt, rdf:type
    assert!(r.rows.len() >= 5, "Expected at least 5 IRI objects for alice, got {}", r.rows.len());
}

// ---------------------------------------------------------------------------
// Cross-type queries
// ---------------------------------------------------------------------------

#[test]
fn large_graph_us_company_employees() {
    let g = large_graph();
    let r = rdf_wasm::sparql::execute(
        &g,
        r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
           PREFIX ex:   <http://example.org/>
           SELECT ?personName ?orgName WHERE {
             ?person foaf:name ?personName .
             ?person ex:worksAt ?org .
             ?org foaf:name ?orgName .
             ?org ex:country ?country .
             FILTER (?country = "US")
             FILTER (LANG(?personName) = "")
           }"#,
    )
    .unwrap();
    // Acme (US): Alice, Bob. BigCorp (US): Eve, Frank.
    assert_eq!(r.rows.len(), 4, "Expected 4 US company employees, got {}", r.rows.len());
    eprintln!("US employees: {} rows", r.rows.len());
}

#[test]
fn large_graph_active_project_members() {
    let g = large_graph();
    let r = rdf_wasm::sparql::execute(
        &g,
        r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
           PREFIX ex:   <http://example.org/>
           SELECT ?projName ?memberName WHERE {
             ?proj foaf:name ?projName .
             ?proj ex:status ?status .
             ?proj ex:member ?member .
             ?member foaf:name ?memberName .
             FILTER (?status = "active")
             FILTER (LANG(?memberName) = "")
           }"#,
    )
    .unwrap();
    // proj1 (Factoidal): alice, bob, dana = 3. proj2 (WidgetML): charlie, dana = 2. Total = 5
    assert_eq!(r.rows.len(), 5, "Expected 5 active project members, got {}", r.rows.len());
}

#[test]
fn large_graph_publication_authors_with_org() {
    let g = large_graph();
    // Three-hop: publication -> creator -> worksAt -> org name
    let r = rdf_wasm::sparql::execute(
        &g,
        "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
         PREFIX dc:   <http://purl.org/dc/elements/1.1/>
         PREFIX ex:   <http://example.org/>
         SELECT ?title ?authorName ?orgName WHERE {
           ?paper dc:title ?title .
           ?paper dc:creator ?author .
           ?author foaf:name ?authorName .
           ?author ex:worksAt ?org .
           ?org foaf:name ?orgName .
           FILTER (LANG(?authorName) = \"\")
         }",
    )
    .unwrap();
    // paper1: alice@acme, dana@widgetco = 2
    // paper2: bob@acme = 1
    // paper3: charlie@widgetco, alice@acme = 2
    // paper4: frank@bigcorp, eve@bigcorp = 2
    // Total = 7
    assert_eq!(r.rows.len(), 7, "Expected 7 author-org rows, got {}", r.rows.len());
    eprintln!("Publication authors with orgs: {} rows", r.rows.len());
}

// ---------------------------------------------------------------------------
// Summary
// ---------------------------------------------------------------------------

#[test]
fn large_graph_summary() {
    let g = large_graph();
    eprintln!("\n╔═══════════════════════════════════════════╗");
    eprintln!("║     Large Graph SPARQL Test Summary       ║");
    eprintln!("╠═══════════════════════════════════════════╣");
    eprintln!("║ Graph size:     {:>4} triples              ║", g.len());

    let type_q = rdf_wasm::sparql::execute(
        &g,
        "PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
         SELECT DISTINCT ?type WHERE { ?s rdf:type ?type }",
    ).unwrap();
    eprintln!("║ Distinct types: {:>4}                      ║", type_q.rows.len());

    let pred_q = rdf_wasm::sparql::execute(
        &g,
        "SELECT DISTINCT ?p WHERE { ?s ?p ?o }",
    ).unwrap();
    eprintln!("║ Distinct preds: {:>4}                      ║", pred_q.rows.len());

    let subj_q = rdf_wasm::sparql::execute(
        &g,
        "SELECT DISTINCT ?s WHERE { ?s ?p ?o }",
    ).unwrap();
    eprintln!("║ Distinct subjs: {:>4}                      ║", subj_q.rows.len());

    eprintln!("╚═══════════════════════════════════════════╝");
}
