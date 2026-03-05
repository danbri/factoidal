//! JavaScript/WASM bindings via wasm-bindgen.

use wasm_bindgen::prelude::*;
use crate::rdf;

// ---------------------------------------------------------------------------
// JsRdfGraph — the main entry point from JavaScript
// ---------------------------------------------------------------------------

#[wasm_bindgen]
pub struct JsRdfGraph {
    inner: rdf::RdfGraph,
}

#[wasm_bindgen]
impl JsRdfGraph {
    /// Create an empty RDF graph.
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        JsRdfGraph {
            inner: rdf::RdfGraph::new(),
        }
    }

    /// Add a triple from string components.
    ///
    /// `subject`   — an IRI string or "_:bnodeId"
    /// `predicate` — an IRI string
    /// `object`    — an IRI string, "_:bnodeId", or a literal via `literal(...)` helper
    #[wasm_bindgen(js_name = addTriple)]
    pub fn add_triple(
        &mut self,
        subject: &str,
        predicate: &str,
        object: &str,
    ) -> Result<(), JsError> {
        let s = parse_subject(subject)?;
        let p = rdf::Iri::new(predicate).map_err(|e| JsError::new(&e.to_string()))?;
        let o = parse_object(object)?;
        self.inner.add(rdf::Triple { s, p, o });
        Ok(())
    }

    /// Add a triple whose object is a language-tagged literal.
    #[wasm_bindgen(js_name = addTripleLang)]
    pub fn add_triple_lang(
        &mut self,
        subject: &str,
        predicate: &str,
        lexical: &str,
        lang: &str,
    ) -> Result<(), JsError> {
        let s = parse_subject(subject)?;
        let p = rdf::Iri::new(predicate).map_err(|e| JsError::new(&e.to_string()))?;
        let o = rdf::RdfTerm::Literal(rdf::Literal::lang(lexical, lang));
        self.inner.add(rdf::Triple { s, p, o });
        Ok(())
    }

    /// Add a triple whose object is a typed literal.
    #[wasm_bindgen(js_name = addTripleTyped)]
    pub fn add_triple_typed(
        &mut self,
        subject: &str,
        predicate: &str,
        lexical: &str,
        datatype: &str,
    ) -> Result<(), JsError> {
        let s = parse_subject(subject)?;
        let p = rdf::Iri::new(predicate).map_err(|e| JsError::new(&e.to_string()))?;
        let dt = rdf::Iri::new(datatype).map_err(|e| JsError::new(&e.to_string()))?;
        let lit = rdf::Literal::new(lexical, dt, None)
            .map_err(|e| JsError::new(&e.to_string()))?;
        let o = rdf::RdfTerm::Literal(lit);
        self.inner.add(rdf::Triple { s, p, o });
        Ok(())
    }

    /// Number of triples in the graph.
    #[wasm_bindgen(getter)]
    pub fn size(&self) -> usize {
        self.inner.len()
    }

    /// Return all blank-node IDs as a JSON array.
    #[wasm_bindgen(js_name = bnodes)]
    pub fn bnodes(&self) -> String {
        serde_json::to_string(&self.inner.bnodes()).unwrap_or_else(|_| "[]".into())
    }

    /// Find triples by subject IRI; returns JSON array of {s, p, o} objects.
    #[wasm_bindgen(js_name = findBySubject)]
    pub fn find_by_subject(&self, subject_iri: &str) -> String {
        let results: Vec<_> = self.inner.find_by_subject(subject_iri);
        triples_to_json(&results)
    }

    /// Find triples by predicate IRI; returns JSON array.
    #[wasm_bindgen(js_name = findByPredicate)]
    pub fn find_by_predicate(&self, predicate_iri: &str) -> String {
        let results: Vec<_> = self.inner.find_by_predicate(predicate_iri);
        triples_to_json(&results)
    }

    /// Serialize the graph to N-Triples.
    #[wasm_bindgen(js_name = toNTriples)]
    pub fn to_ntriples(&self) -> String {
        self.inner.to_ntriples()
    }

    /// Serialize the full graph as JSON.
    #[wasm_bindgen(js_name = toJSON)]
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(&self.inner).unwrap_or_else(|_| "{}".into())
    }

    /// Remove all triples from the graph.
    #[wasm_bindgen]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Remove a triple by its index (0-based).
    #[wasm_bindgen(js_name = removeByIndex)]
    pub fn remove_by_index(&mut self, index: usize) -> Result<(), JsError> {
        let triples = self.inner.triples();
        if index >= triples.len() {
            return Err(JsError::new("Index out of bounds"));
        }
        let triple = triples[index].clone();
        self.inner
            .remove(&triple)
            .map_err(|e| JsError::new(&e.to_string()))
    }

    /// Return all triples as a JSON array with s/p/o structure.
    #[wasm_bindgen(js_name = triplesJSON)]
    pub fn triples_json(&self) -> String {
        let triples: Vec<_> = self.inner.triples().iter().collect();
        triples_to_json(&triples)
    }

    /// Execute a SPARQL SELECT query. Returns JSON with `variables` and `rows`.
    #[wasm_bindgen(js_name = sparqlQuery)]
    pub fn sparql_query(&self, query: &str) -> Result<String, JsError> {
        let result = crate::sparql::execute(&self.inner, query)
            .map_err(|e| JsError::new(&e))?;
        serde_json::to_string_pretty(&result)
            .map_err(|e| JsError::new(&e.to_string()))
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn parse_subject(s: &str) -> Result<rdf::Subject, JsError> {
    if let Some(id) = s.strip_prefix("_:") {
        Ok(rdf::Subject::BNode(rdf::BNode::from_str(id)))
    } else {
        rdf::Iri::new(s)
            .map(rdf::Subject::Iri)
            .map_err(|e| JsError::new(&e.to_string()))
    }
}

fn parse_object(o: &str) -> Result<rdf::RdfTerm, JsError> {
    if let Some(id) = o.strip_prefix("_:") {
        Ok(rdf::RdfTerm::BNode(rdf::BNode::from_str(id)))
    } else if o.contains(':') {
        rdf::Iri::new(o)
            .map(rdf::RdfTerm::Iri)
            .map_err(|e| JsError::new(&e.to_string()))
    } else {
        // Treat as plain string literal
        Ok(rdf::RdfTerm::Literal(rdf::Literal::plain(o)))
    }
}

fn triples_to_json(triples: &[&rdf::Triple]) -> String {
    serde_json::to_string_pretty(triples).unwrap_or_else(|_| "[]".into())
}
