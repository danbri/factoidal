use serde::{Deserialize, Serialize};
use std::fmt;

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

pub const RDF_LANG_STRING: &str =
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString";
pub const XSD_STRING: &str =
    "http://www.w3.org/2001/XMLSchema#string";

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RdfError {
    InvalidIri(String),
    InvalidLiteral(String),
    InvalidSubject(String),
    InvalidPredicate(String),
    TripleNotFound,
}

impl fmt::Display for RdfError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RdfError::InvalidIri(s) => write!(f, "Invalid IRI: {s}"),
            RdfError::InvalidLiteral(s) => write!(f, "Invalid literal: {s}"),
            RdfError::InvalidSubject(s) => write!(f, "Invalid subject: {s}"),
            RdfError::InvalidPredicate(s) => write!(f, "Invalid predicate: {s}"),
            RdfError::TripleNotFound => write!(f, "Triple not found"),
        }
    }
}

// ---------------------------------------------------------------------------
// Well-formed IRI (refined type — must be non-empty and contain ':')
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Iri(String);

impl Iri {
    pub fn new(s: &str) -> Result<Self, RdfError> {
        if !s.is_empty() && s.contains(':') {
            Ok(Iri(s.to_string()))
        } else {
            Err(RdfError::InvalidIri(s.to_string()))
        }
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Iri {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}>", self.0)
    }
}

// ---------------------------------------------------------------------------
// Blank Node
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct BNode(String);

impl BNode {
    pub fn new(id: &str) -> Self {
        BNode(id.to_string())
    }

    pub fn id(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for BNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_:{}", self.0)
    }
}

// ---------------------------------------------------------------------------
// Well-formed Literal (mirrors F* `wf_literal` refinement)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Literal {
    pub lexical_form: String,
    pub datatype: Iri,
    pub lang_tag: Option<String>,
}

impl Literal {
    /// Create a well-formed literal, enforcing the F* refinement:
    /// - If lang_tag is Some, datatype MUST be rdf:langString
    /// - If lang_tag is None, datatype MUST NOT be rdf:langString
    pub fn new(
        lexical_form: &str,
        datatype: Iri,
        lang_tag: Option<&str>,
    ) -> Result<Self, RdfError> {
        match &lang_tag {
            Some(_) if datatype.as_str() != RDF_LANG_STRING => {
                Err(RdfError::InvalidLiteral(
                    "Language-tagged literal must have datatype rdf:langString".into(),
                ))
            }
            None if datatype.as_str() == RDF_LANG_STRING => {
                Err(RdfError::InvalidLiteral(
                    "Datatype rdf:langString requires a language tag".into(),
                ))
            }
            _ => Ok(Literal {
                lexical_form: lexical_form.to_string(),
                datatype,
                lang_tag: lang_tag.map(|s| s.to_string()),
            }),
        }
    }

    /// Convenience: plain string literal (xsd:string, no lang tag).
    pub fn plain(lexical_form: &str) -> Self {
        Literal {
            lexical_form: lexical_form.to_string(),
            datatype: Iri::new(XSD_STRING).unwrap(),
            lang_tag: None,
        }
    }

    /// Convenience: language-tagged literal.
    pub fn lang(lexical_form: &str, tag: &str) -> Self {
        Literal {
            lexical_form: lexical_form.to_string(),
            datatype: Iri::new(RDF_LANG_STRING).unwrap(),
            lang_tag: Some(tag.to_string()),
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\"{}\"", self.lexical_form)?;
        if let Some(tag) = &self.lang_tag {
            write!(f, "@{tag}")
        } else if self.datatype.as_str() != XSD_STRING {
            write!(f, "^^{}", self.datatype)
        } else {
            Ok(())
        }
    }
}

// ---------------------------------------------------------------------------
// RDF Term, Subject, Triple
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RdfTerm {
    Iri(Iri),
    BNode(BNode),
    Literal(Literal),
}

impl fmt::Display for RdfTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RdfTerm::Iri(i) => write!(f, "{i}"),
            RdfTerm::BNode(b) => write!(f, "{b}"),
            RdfTerm::Literal(l) => write!(f, "{l}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Subject {
    Iri(Iri),
    BNode(BNode),
}

impl fmt::Display for Subject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Subject::Iri(i) => write!(f, "{i}"),
            Subject::BNode(b) => write!(f, "{b}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Triple {
    pub s: Subject,
    pub p: Iri,
    pub o: RdfTerm,
}

impl fmt::Display for Triple {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} {} .", self.s, self.p, self.o)
    }
}

// ---------------------------------------------------------------------------
// RDF Graph (list-based, mirrors F* `rdf_graph = list triple`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct RdfGraph {
    triples: Vec<Triple>,
}

impl RdfGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, triple: Triple) {
        if !self.triples.contains(&triple) {
            self.triples.push(triple);
        }
    }

    pub fn remove(&mut self, triple: &Triple) -> Result<(), RdfError> {
        let before = self.triples.len();
        self.triples.retain(|t| t != triple);
        if self.triples.len() == before {
            Err(RdfError::TripleNotFound)
        } else {
            Ok(())
        }
    }

    pub fn len(&self) -> usize {
        self.triples.len()
    }

    pub fn is_empty(&self) -> bool {
        self.triples.is_empty()
    }

    pub fn triples(&self) -> &[Triple] {
        &self.triples
    }

    /// Return all blank-node IDs in the graph (mirrors F* `graph_bnodes`).
    pub fn bnodes(&self) -> Vec<String> {
        let mut ids: Vec<String> = Vec::new();
        for t in &self.triples {
            if let Subject::BNode(b) = &t.s {
                if !ids.contains(&b.id().to_string()) {
                    ids.push(b.id().to_string());
                }
            }
            if let RdfTerm::BNode(b) = &t.o {
                if !ids.contains(&b.id().to_string()) {
                    ids.push(b.id().to_string());
                }
            }
        }
        ids
    }

    /// Find triples by subject IRI.
    pub fn find_by_subject(&self, subject_iri: &str) -> Vec<&Triple> {
        self.triples
            .iter()
            .filter(|t| match &t.s {
                Subject::Iri(i) => i.as_str() == subject_iri,
                _ => false,
            })
            .collect()
    }

    /// Find triples by predicate IRI.
    pub fn find_by_predicate(&self, predicate_iri: &str) -> Vec<&Triple> {
        self.triples
            .iter()
            .filter(|t| t.p.as_str() == predicate_iri)
            .collect()
    }

    /// Serialize to N-Triples format.
    pub fn to_ntriples(&self) -> String {
        self.triples
            .iter()
            .map(|t| format!("{t}"))
            .collect::<Vec<_>>()
            .join("\n")
    }
}

impl fmt::Display for RdfGraph {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_ntriples())
    }
}
