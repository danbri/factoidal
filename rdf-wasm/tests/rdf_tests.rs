//! Unit tests for the RDF Core 1.1 types and graph.

use rdf_wasm::*;

// ---------------------------------------------------------------------------
// IRI tests
// ---------------------------------------------------------------------------

#[test]
fn iri_valid() {
    let iri = Iri::new("http://example.org/foo");
    assert!(iri.is_ok());
    assert_eq!(iri.unwrap().as_str(), "http://example.org/foo");
}

#[test]
fn iri_rejects_empty() {
    assert!(Iri::new("").is_err());
}

#[test]
fn iri_rejects_no_colon() {
    assert!(Iri::new("noscheme").is_err());
}

#[test]
fn iri_display() {
    let iri = Iri::new("http://example.org/x").unwrap();
    assert_eq!(format!("{iri}"), "<http://example.org/x>");
}

// ---------------------------------------------------------------------------
// BNode tests
// ---------------------------------------------------------------------------

#[test]
fn bnode_id() {
    let b = BNode::new("b1");
    assert_eq!(b.id(), "b1");
    assert_eq!(format!("{b}"), "_:b1");
}

// ---------------------------------------------------------------------------
// Literal tests
// ---------------------------------------------------------------------------

#[test]
fn plain_literal() {
    let lit = Literal::plain("hello");
    assert_eq!(lit.lexical_form, "hello");
    assert_eq!(lit.datatype.as_str(), XSD_STRING);
    assert!(lit.lang_tag.is_none());
    assert_eq!(format!("{lit}"), "\"hello\"");
}

#[test]
fn lang_literal() {
    let lit = Literal::lang("bonjour", "fr");
    assert_eq!(lit.lang_tag.as_deref(), Some("fr"));
    assert_eq!(lit.datatype.as_str(), RDF_LANG_STRING);
    assert_eq!(format!("{lit}"), "\"bonjour\"@fr");
}

#[test]
fn typed_literal_display() {
    let dt = Iri::new("http://www.w3.org/2001/XMLSchema#integer").unwrap();
    let lit = Literal::new("42", dt, None).unwrap();
    assert_eq!(
        format!("{lit}"),
        "\"42\"^^<http://www.w3.org/2001/XMLSchema#integer>"
    );
}

#[test]
fn literal_rejects_lang_with_wrong_datatype() {
    let dt = Iri::new(XSD_STRING).unwrap();
    let result = Literal::new("hello", dt, Some("en"));
    assert!(result.is_err());
}

#[test]
fn literal_rejects_langstring_without_tag() {
    let dt = Iri::new(RDF_LANG_STRING).unwrap();
    let result = Literal::new("hello", dt, None);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// Triple tests
// ---------------------------------------------------------------------------

#[test]
fn triple_display_ntriples() {
    let t = Triple {
        s: Subject::Iri(Iri::new("http://example.org/s").unwrap()),
        p: Iri::new("http://example.org/p").unwrap(),
        o: RdfTerm::Literal(Literal::plain("value")),
    };
    assert_eq!(
        format!("{t}"),
        "<http://example.org/s> <http://example.org/p> \"value\" ."
    );
}

// ---------------------------------------------------------------------------
// Graph tests
// ---------------------------------------------------------------------------

fn sample_graph() -> RdfGraph {
    let mut g = RdfGraph::new();
    g.add(Triple {
        s: Subject::Iri(Iri::new("http://example.org/alice").unwrap()),
        p: Iri::new("http://xmlns.com/foaf/0.1/name").unwrap(),
        o: RdfTerm::Literal(Literal::plain("Alice")),
    });
    g.add(Triple {
        s: Subject::Iri(Iri::new("http://example.org/alice").unwrap()),
        p: Iri::new("http://xmlns.com/foaf/0.1/knows").unwrap(),
        o: RdfTerm::Iri(Iri::new("http://example.org/bob").unwrap()),
    });
    g.add(Triple {
        s: Subject::BNode(BNode::new("b1")),
        p: Iri::new("http://xmlns.com/foaf/0.1/name").unwrap(),
        o: RdfTerm::Literal(Literal::lang("Robert", "en")),
    });
    g
}

#[test]
fn graph_add_and_size() {
    let g = sample_graph();
    assert_eq!(g.len(), 3);
}

#[test]
fn graph_no_duplicates() {
    let mut g = sample_graph();
    let before = g.len();
    // Add the same triple again
    g.add(Triple {
        s: Subject::Iri(Iri::new("http://example.org/alice").unwrap()),
        p: Iri::new("http://xmlns.com/foaf/0.1/name").unwrap(),
        o: RdfTerm::Literal(Literal::plain("Alice")),
    });
    assert_eq!(g.len(), before);
}

#[test]
fn graph_remove() {
    let mut g = sample_graph();
    let t = Triple {
        s: Subject::Iri(Iri::new("http://example.org/alice").unwrap()),
        p: Iri::new("http://xmlns.com/foaf/0.1/name").unwrap(),
        o: RdfTerm::Literal(Literal::plain("Alice")),
    };
    assert!(g.remove(&t).is_ok());
    assert_eq!(g.len(), 2);
}

#[test]
fn graph_remove_not_found() {
    let mut g = sample_graph();
    let t = Triple {
        s: Subject::Iri(Iri::new("http://example.org/nobody").unwrap()),
        p: Iri::new("http://example.org/p").unwrap(),
        o: RdfTerm::Literal(Literal::plain("x")),
    };
    assert_eq!(g.remove(&t), Err(RdfError::TripleNotFound));
}

#[test]
fn graph_bnodes() {
    let g = sample_graph();
    let ids = g.bnodes();
    assert!(ids.contains(&"b1".to_string()));
}

#[test]
fn graph_find_by_subject() {
    let g = sample_graph();
    let results = g.find_by_subject("http://example.org/alice");
    assert_eq!(results.len(), 2);
}

#[test]
fn graph_find_by_predicate() {
    let g = sample_graph();
    let results = g.find_by_predicate("http://xmlns.com/foaf/0.1/name");
    assert_eq!(results.len(), 2);
}

#[test]
fn graph_to_ntriples() {
    let g = sample_graph();
    let nt = g.to_ntriples();
    assert!(nt.contains("<http://example.org/alice>"));
    assert!(nt.contains("\"Alice\""));
    assert!(nt.contains("\"Robert\"@en"));
}

#[test]
fn graph_empty() {
    let g = RdfGraph::new();
    assert!(g.is_empty());
    assert_eq!(g.len(), 0);
    assert_eq!(g.bnodes().len(), 0);
}

#[test]
fn graph_serde_roundtrip() {
    let g = sample_graph();
    let json = serde_json::to_string(&g).unwrap();
    let g2: RdfGraph = serde_json::from_str(&json).unwrap();
    assert_eq!(g.len(), g2.len());
}
