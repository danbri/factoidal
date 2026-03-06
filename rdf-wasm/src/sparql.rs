//! Minimal SPARQL SELECT engine over an RdfGraph.
//!
//! Supports:
//! - SELECT with explicit variables or *
//! - Basic Graph Patterns (triple patterns with ?variables)
//! - FILTER with comparison operators (=, !=, <, >, <=, >=), STR(), LANG(),
//!   DATATYPE(), BOUND(), REGEX(), CONTAINS(), STRSTARTS(), STRENDS(),
//!   ISLITERAL(), ISIRI()/ISURI(), ISBLANK(), boolean AND (&&), OR (||)
//! - OPTIONAL patterns
//! - DISTINCT
//! - ORDER BY (ASC/DESC)
//! - LIMIT / OFFSET
//! - PREFIX declarations

use crate::rdf::{self, RdfGraph, RdfTerm, Subject, Triple};
use regex::RegexBuilder;
use serde::Serialize;
use std::collections::HashMap;

/// A single binding row: variable name -> RdfTerm (as display string).
pub type Binding = HashMap<String, TermValue>;

/// Represents a bound RDF term with enough structure for filtering.
#[derive(Debug, Clone, PartialEq)]
pub enum TermValue {
    Iri(String),
    BNode(String),
    Literal {
        lexical: String,
        datatype: String,
        lang: Option<String>,
    },
}

impl TermValue {
    fn from_rdf_term(t: &RdfTerm) -> Self {
        match t {
            RdfTerm::Iri(i) => TermValue::Iri(i.as_str().to_string()),
            RdfTerm::BNode(b) => TermValue::BNode(format!("b{}", b.id())),
            RdfTerm::Literal(l) => TermValue::Literal {
                lexical: l.lexical_form.clone(),
                datatype: l.datatype.as_str().to_string(),
                lang: l.lang_tag.clone(),
            },
        }
    }

    fn from_subject(s: &Subject) -> Self {
        match s {
            Subject::Iri(i) => TermValue::Iri(i.as_str().to_string()),
            Subject::BNode(b) => TermValue::BNode(format!("b{}", b.id())),
        }
    }

    fn display(&self) -> String {
        match self {
            TermValue::Iri(s) => format!("<{s}>"),
            TermValue::BNode(s) => format!("_:{s}"),
            TermValue::Literal {
                lexical,
                datatype,
                lang,
            } => {
                if let Some(tag) = lang {
                    format!("\"{lexical}\"@{tag}")
                } else if datatype == rdf::XSD_STRING {
                    format!("\"{lexical}\"")
                } else {
                    format!("\"{lexical}\"^^<{datatype}>")
                }
            }
        }
    }

    fn as_str_value(&self) -> &str {
        match self {
            TermValue::Iri(s) | TermValue::BNode(s) => s,
            TermValue::Literal { lexical, .. } => lexical,
        }
    }

    /// Sort key for ORDER BY.
    fn sort_key(&self) -> (u8, &str) {
        match self {
            TermValue::BNode(s) => (0, s),
            TermValue::Iri(s) => (1, s),
            TermValue::Literal { lexical, .. } => (2, lexical),
        }
    }
}

// ---------------------------------------------------------------------------
// Parsed SPARQL structures
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum PatternElement {
    Variable(String),
    Iri(String),
    PrefixedName(String, String), // prefix, local
    Literal(String, Option<String>, Option<String>), // lexical, lang, datatype
}

#[derive(Debug, Clone)]
struct TriplePattern {
    s: PatternElement,
    p: PatternElement,
    o: PatternElement,
}

#[derive(Debug, Clone)]
enum Filter {
    Comparison(FilterExpr, CompOp, FilterExpr),
    And(Box<Filter>, Box<Filter>),
    Or(Box<Filter>, Box<Filter>),
    Not(Box<Filter>),
    BooleanEffectiveValue(FilterExpr),
    FnBound(String),
    FnIsLiteral(FilterExpr),
    FnIsIri(FilterExpr),
    FnIsBlank(FilterExpr),
    FnRegex(FilterExpr, String, Option<String>),
    FnContains(FilterExpr, FilterExpr),
    FnStrStarts(FilterExpr, FilterExpr),
    FnStrEnds(FilterExpr, FilterExpr),
}

#[derive(Debug, Clone)]
enum FilterExpr {
    Variable(String),
    StringLit(String),
    NumericLit(f64),
    IriLit(String),
    FnStr(Box<FilterExpr>),
    FnLang(Box<FilterExpr>),
    FnDatatype(Box<FilterExpr>),
    Arithmetic(Box<FilterExpr>, String, Box<FilterExpr>), // left, op (+,-,*,/), right
}

#[derive(Debug, Clone)]
enum CompOp {
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

#[derive(Debug, Clone)]
enum OrderDir {
    Asc,
    Desc,
}

#[derive(Debug, Clone)]
struct OrderClause {
    var: String,
    dir: OrderDir,
}

#[derive(Debug, Clone)]
enum WhereClause {
    Pattern(TriplePattern),
    Filter(Filter),
    Optional(Vec<WhereClause>),
    Union(Vec<WhereClause>),           // right side of UNION (legacy, appended to previous)
    UnionGroup(Vec<Vec<WhereClause>>), // { } UNION { } UNION { } — list of branches
}

#[derive(Debug)]
struct ParsedQuery {
    prefixes: HashMap<String, String>,
    variables: Vec<String>, // empty = SELECT *
    distinct: bool,
    where_clauses: Vec<WhereClause>,
    order_by: Vec<OrderClause>,
    limit: Option<usize>,
    offset: Option<usize>,
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

struct Parser {
    tokens: Vec<String>,
    pos: usize,
}

impl Parser {
    fn new(input: &str) -> Self {
        Parser {
            tokens: tokenize(input),
            pos: 0,
        }
    }

    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.pos).map(|s| s.as_str())
    }

    fn next(&mut self) -> Result<String, String> {
        if self.pos < self.tokens.len() {
            let t = self.tokens[self.pos].clone();
            self.pos += 1;
            Ok(t)
        } else {
            Err("Unexpected end of query".into())
        }
    }

    fn expect(&mut self, expected: &str) -> Result<(), String> {
        let t = self.next()?;
        if t.to_uppercase() == expected.to_uppercase() {
            Ok(())
        } else {
            Err(format!("Expected '{expected}', got '{t}'"))
        }
    }

    fn parse_query(&mut self) -> Result<ParsedQuery, String> {
        let mut prefixes = HashMap::new();
        let mut base_iri: Option<String> = None;

        // Parse PREFIX and BASE declarations
        loop {
            match self.peek().map(|t| t.to_uppercase()) {
                Some(ref s) if s == "PREFIX" => {
                    self.next()?; // PREFIX
                    let prefix = self.next()?; // e.g. "foaf:"
                    let iri_tok = self.next()?; // e.g. "<http://...>"
                    let iri = iri_tok
                        .trim_start_matches('<')
                        .trim_end_matches('>')
                        .to_string();
                    prefixes.insert(prefix.trim_end_matches(':').to_string(), iri);
                }
                Some(ref s) if s == "BASE" => {
                    self.next()?; // BASE
                    let iri_tok = self.next()?;
                    base_iri = Some(
                        iri_tok
                            .trim_start_matches('<')
                            .trim_end_matches('>')
                            .to_string(),
                    );
                    // Register base as empty prefix for resolving relative IRIs
                }
                _ => break,
            }
        }

        // If we have a BASE, use it to resolve empty prefix
        if let Some(ref base) = base_iri {
            if !prefixes.contains_key("") {
                prefixes.insert(String::new(), base.clone());
            }
        }

        self.expect("SELECT")?;

        let distinct = self.peek().map(|t| t.to_uppercase()) == Some("DISTINCT".to_string());
        if distinct {
            self.next()?;
        }

        // Variables
        let mut variables = Vec::new();
        if self.peek() == Some("*") {
            self.next()?;
        } else {
            while let Some(t) = self.peek() {
                if t.starts_with('?') {
                    variables.push(self.next()?[1..].to_string());
                } else {
                    break;
                }
            }
            if variables.is_empty() {
                return Err("Expected variable list or * after SELECT".into());
            }
        }

        // WHERE keyword is optional in SPARQL
        if self.peek().map(|t| t.to_uppercase()) == Some("WHERE".to_string()) {
            self.next()?; // consume WHERE
        }
        self.expect("{")?;

        let where_clauses = self.parse_where_body()?;

        self.expect("}")?;

        // ORDER BY
        let mut order_by = Vec::new();
        if self.peek().map(|t| t.to_uppercase()) == Some("ORDER".to_string()) {
            self.next()?; // ORDER
            self.expect("BY")?;
            while let Some(t) = self.peek() {
                let upper = t.to_uppercase();
                if upper == "ASC" || upper == "DESC" {
                    let dir = if upper == "ASC" {
                        OrderDir::Asc
                    } else {
                        OrderDir::Desc
                    };
                    self.next()?;
                    self.expect("(")?;
                    let var = self.next()?;
                    if !var.starts_with('?') {
                        return Err(format!("Expected variable in ORDER BY, got '{var}'"));
                    }
                    self.expect(")")?;
                    order_by.push(OrderClause {
                        var: var[1..].to_string(),
                        dir,
                    });
                } else if t.starts_with('?') {
                    let var = self.next()?;
                    order_by.push(OrderClause {
                        var: var[1..].to_string(),
                        dir: OrderDir::Asc,
                    });
                } else {
                    break;
                }
            }
        }

        // LIMIT
        let mut limit = None;
        if self.peek().map(|t| t.to_uppercase()) == Some("LIMIT".to_string()) {
            self.next()?;
            let n = self.next()?;
            limit = Some(
                n.parse::<usize>()
                    .map_err(|_| format!("Invalid LIMIT value: {n}"))?,
            );
        }

        // OFFSET
        let mut offset = None;
        if self.peek().map(|t| t.to_uppercase()) == Some("OFFSET".to_string()) {
            self.next()?;
            let n = self.next()?;
            offset = Some(
                n.parse::<usize>()
                    .map_err(|_| format!("Invalid OFFSET value: {n}"))?,
            );
        }

        Ok(ParsedQuery {
            prefixes,
            variables,
            distinct,
            where_clauses,
            order_by,
            limit,
            offset,
        })
    }

    fn parse_where_body(&mut self) -> Result<Vec<WhereClause>, String> {
        let mut clauses = Vec::new();

        while let Some(t) = self.peek() {
            if t == "}" {
                break;
            }
            let upper = t.to_uppercase();
            if upper == "FILTER" {
                self.next()?; // FILTER
                // SPARQL allows both FILTER(expr) and FILTER expr
                // Check if next token is a function name (like REGEX, BOUND, etc.)
                // or if it starts with (
                let next = self.peek().ok_or("Unexpected end after FILTER")?;
                let _next_upper = next.to_uppercase();
                let needs_outer_paren = next == "(";
                if needs_outer_paren {
                    self.next()?; // (
                }
                let filter = self.parse_filter()?;
                if needs_outer_paren {
                    self.expect(")")?;
                }
                // optional trailing .
                if self.peek() == Some(".") {
                    self.next()?;
                }
                clauses.push(WhereClause::Filter(filter));
            } else if upper == "OPTIONAL" {
                self.next()?; // OPTIONAL
                self.expect("{")?;
                let inner = self.parse_where_body()?;
                self.expect("}")?;
                // optional trailing .
                if self.peek() == Some(".") {
                    self.next()?;
                }
                clauses.push(WhereClause::Optional(inner));
            } else if upper == "UNION" {
                // UNION — combine previous group with next group
                self.next()?; // UNION
                self.expect("{")?;
                let right = self.parse_where_body()?;
                self.expect("}")?;
                // optional trailing .
                if self.peek() == Some(".") {
                    self.next()?;
                }
                clauses.push(WhereClause::Union(right));
            } else if t == "{" {
                // Sub-group pattern (can be left side of UNION)
                self.next()?; // {
                let inner = self.parse_where_body()?;
                self.expect("}")?;
                // Check if followed by UNION
                if self.peek().map(|s| s.to_uppercase()) == Some("UNION".to_string()) {
                    // This is the left side of a UNION
                    let mut union_branches = vec![inner];
                    while self.peek().map(|s| s.to_uppercase()) == Some("UNION".to_string()) {
                        self.next()?; // UNION
                        self.expect("{")?;
                        let branch = self.parse_where_body()?;
                        self.expect("}")?;
                        union_branches.push(branch);
                    }
                    // optional trailing .
                    if self.peek() == Some(".") {
                        self.next()?;
                    }
                    clauses.push(WhereClause::UnionGroup(union_branches));
                } else {
                    // Just a sub-group, inline it
                    clauses.extend(inner);
                    // optional trailing .
                    if self.peek() == Some(".") {
                        self.next()?;
                    }
                }
            } else {
                // Triple pattern
                let s = self.parse_pattern_element()?;
                let p = self.parse_pattern_element()?;
                let o = self.parse_pattern_element()?;
                clauses.push(WhereClause::Pattern(TriplePattern { s: s.clone(), p: p.clone(), o }));
                // Handle , for object list (same subject+predicate, different objects)
                while self.peek() == Some(",") {
                    self.next()?; // ,
                    let o2 = self.parse_pattern_element()?;
                    clauses.push(WhereClause::Pattern(TriplePattern {
                        s: s.clone(),
                        p: p.clone(),
                        o: o2,
                    }));
                }
                // Handle ; for property list (same subject, different predicates)
                while self.peek() == Some(";") {
                    self.next()?; // ;
                    // Check if next is } or . or another non-predicate (end of property list)
                    if self.peek() == Some("}") || self.peek() == Some(".") || self.peek().is_none() {
                        break;
                    }
                    let p2 = self.parse_pattern_element()?;
                    let o2 = self.parse_pattern_element()?;
                    clauses.push(WhereClause::Pattern(TriplePattern {
                        s: s.clone(),
                        p: p2.clone(),
                        o: o2,
                    }));
                    // Handle , after ; (object list for new predicate)
                    while self.peek() == Some(",") {
                        self.next()?; // ,
                        let o3 = self.parse_pattern_element()?;
                        clauses.push(WhereClause::Pattern(TriplePattern {
                            s: s.clone(),
                            p: p2.clone(),
                            o: o3,
                        }));
                    }
                }
                // optional .
                if self.peek() == Some(".") {
                    self.next()?;
                }
            }
        }

        Ok(clauses)
    }

    fn parse_pattern_element(&mut self) -> Result<PatternElement, String> {
        let t = self.next()?;
        if t.starts_with('?') || t.starts_with('$') {
            Ok(PatternElement::Variable(t[1..].to_string()))
        } else if t == "a" {
            // 'a' is shorthand for rdf:type
            Ok(PatternElement::Iri(
                "http://www.w3.org/1999/02/22-rdf-syntax-ns#type".to_string(),
            ))
        } else if t.starts_with('<') && t.ends_with('>') {
            Ok(PatternElement::Iri(
                t[1..t.len() - 1].to_string(),
            ))
        } else if t.starts_with('"') || t.starts_with('\'') {
            // String literal — may have @lang or ^^type
            let quote_char = t.chars().next().unwrap();
            // Handle triple-quoted strings
            let lexical = if t.starts_with("\"\"\"") || t.starts_with("'''") {
                let q3 = &t[..3];
                let end_q3 = if t.len() >= 6 && t.ends_with(q3) {
                    t[3..t.len()-3].to_string()
                } else {
                    t[3..].trim_end_matches(quote_char).to_string()
                };
                end_q3
            } else {
                t[1..t.len()-1].to_string()
            };
            let mut lang = None;
            let mut datatype = None;
            if let Some(next) = self.peek() {
                if next.starts_with('@') {
                    lang = Some(self.next()?[1..].to_string());
                } else if next == "^^" {
                    self.next()?; // ^^
                    let dt = self.next()?;
                    if dt.contains(':') && !dt.starts_with('<') {
                        // Prefixed datatype like xsd:integer
                        datatype = Some(dt.to_string());
                    } else {
                        datatype = Some(
                            dt.trim_start_matches('<')
                                .trim_end_matches('>')
                                .to_string(),
                        );
                    }
                }
            }
            Ok(PatternElement::Literal(lexical, lang, datatype))
        } else if t == "true" || t == "false" {
            // Boolean literal
            Ok(PatternElement::Literal(
                t.to_string(),
                None,
                Some("http://www.w3.org/2001/XMLSchema#boolean".to_string()),
            ))
        } else if t.chars().next().map_or(false, |c| c.is_ascii_digit() || c == '+' || c == '-') {
            // Numeric literal
            let datatype = if t.contains('.') {
                "http://www.w3.org/2001/XMLSchema#decimal"
            } else if t.contains('e') || t.contains('E') {
                "http://www.w3.org/2001/XMLSchema#double"
            } else {
                "http://www.w3.org/2001/XMLSchema#integer"
            };
            Ok(PatternElement::Literal(
                t.to_string(),
                None,
                Some(datatype.to_string()),
            ))
        } else if t.contains(':') {
            // Prefixed name like foaf:name
            let parts: Vec<&str> = t.splitn(2, ':').collect();
            Ok(PatternElement::PrefixedName(
                parts[0].to_string(),
                parts.get(1).unwrap_or(&"").to_string(),
            ))
        } else if t == "[]" {
            // Blank node [] tokenized as single token — anonymous blank node
            let bnode_var = format!("__bnode_{}", self.pos);
            Ok(PatternElement::Variable(bnode_var))
        } else if t == "[" {
            // Blank node [] — anonymous blank node, acts as a fresh variable
            let bnode_var = format!("__bnode_{}", self.pos);
            // Handle empty [] or property list [ :p :o ; :p2 :o2 ]
            if self.peek() == Some("]") {
                self.next()?; // ]
            } else {
                // Skip property list content until matching ]
                let mut depth = 1;
                while depth > 0 {
                    match self.peek() {
                        Some("[") => { self.next()?; depth += 1; }
                        Some("]") => { self.next()?; depth -= 1; }
                        Some(_) => { self.next()?; }
                        None => break,
                    }
                }
            }
            Ok(PatternElement::Variable(bnode_var))
        } else {
            Err(format!("Unexpected token in pattern: '{t}'"))
        }
    }

    fn parse_filter(&mut self) -> Result<Filter, String> {
        self.parse_filter_or()
    }

    fn parse_filter_or(&mut self) -> Result<Filter, String> {
        let mut left = self.parse_filter_and()?;
        while self.peek() == Some("||") {
            self.next()?;
            let right = self.parse_filter_and()?;
            left = Filter::Or(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_filter_and(&mut self) -> Result<Filter, String> {
        let mut left = self.parse_filter_primary()?;
        while self.peek() == Some("&&") {
            self.next()?;
            let right = self.parse_filter_primary()?;
            left = Filter::And(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_filter_primary(&mut self) -> Result<Filter, String> {
        let t = self.peek().ok_or("Unexpected end in FILTER")?.to_string();
        let upper = t.to_uppercase();

        if t == "!" {
            self.next()?;
            let inner = self.parse_filter_primary()?;
            return Ok(Filter::Not(Box::new(inner)));
        }

        if t == "(" {
            self.next()?;
            let f = self.parse_filter()?;
            self.expect(")")?;
            return Ok(f);
        }

        // Function-style filters
        match upper.as_str() {
            "BOUND" => {
                self.next()?;
                self.expect("(")?;
                let var = self.next()?;
                if !var.starts_with('?') {
                    return Err(format!("BOUND expects a variable, got '{var}'"));
                }
                self.expect(")")?;
                return Ok(Filter::FnBound(var[1..].to_string()));
            }
            "ISLITERAL" => {
                self.next()?;
                self.expect("(")?;
                let expr = self.parse_filter_expr()?;
                self.expect(")")?;
                return Ok(Filter::FnIsLiteral(expr));
            }
            "ISIRI" | "ISURI" => {
                self.next()?;
                self.expect("(")?;
                let expr = self.parse_filter_expr()?;
                self.expect(")")?;
                return Ok(Filter::FnIsIri(expr));
            }
            "ISBLANK" => {
                self.next()?;
                self.expect("(")?;
                let expr = self.parse_filter_expr()?;
                self.expect(")")?;
                return Ok(Filter::FnIsBlank(expr));
            }
            "REGEX" => {
                self.next()?;
                self.expect("(")?;
                let expr = self.parse_filter_expr()?;
                self.expect(",")?;
                let pattern = self.next()?.trim_matches('"').to_string();
                let mut flags = None;
                if self.peek() == Some(",") {
                    self.next()?;
                    flags = Some(self.next()?.trim_matches('"').to_string());
                }
                self.expect(")")?;
                return Ok(Filter::FnRegex(expr, pattern, flags));
            }
            "CONTAINS" => {
                self.next()?;
                self.expect("(")?;
                let a = self.parse_filter_expr()?;
                self.expect(",")?;
                let b = self.parse_filter_expr()?;
                self.expect(")")?;
                return Ok(Filter::FnContains(a, b));
            }
            "STRSTARTS" => {
                self.next()?;
                self.expect("(")?;
                let a = self.parse_filter_expr()?;
                self.expect(",")?;
                let b = self.parse_filter_expr()?;
                self.expect(")")?;
                return Ok(Filter::FnStrStarts(a, b));
            }
            "STRENDS" => {
                self.next()?;
                self.expect("(")?;
                let a = self.parse_filter_expr()?;
                self.expect(",")?;
                let b = self.parse_filter_expr()?;
                self.expect(")")?;
                return Ok(Filter::FnStrEnds(a, b));
            }
            _ => {}
        }

        // Comparison: expr OP expr, or bare expression (boolean effective value)
        let left = self.parse_filter_expr()?;
        // Check if next token is a comparison operator
        if let Some(op_tok) = self.peek() {
            let op = match op_tok {
                "=" => Some(CompOp::Eq),
                "!=" => Some(CompOp::Ne),
                "<" => Some(CompOp::Lt),
                ">" => Some(CompOp::Gt),
                "<=" => Some(CompOp::Le),
                ">=" => Some(CompOp::Ge),
                // Arithmetic operators — parse as comparison with special handling
                "+" | "-" | "*" | "/" => {
                    // Parse arithmetic expression: left OP right [CMP right2]
                    let arith_op = self.next()?;
                    let right_expr = self.parse_filter_expr()?;
                    // Check if there's a comparison after
                    if let Some(cmp) = self.peek() {
                        let cmp_op = match cmp {
                            "=" => Some(CompOp::Eq),
                            "!=" => Some(CompOp::Ne),
                            "<" => Some(CompOp::Lt),
                            ">" => Some(CompOp::Gt),
                            "<=" => Some(CompOp::Le),
                            ">=" => Some(CompOp::Ge),
                            _ => None,
                        };
                        if let Some(op) = cmp_op {
                            self.next()?;
                            let rhs = self.parse_filter_expr()?;
                            return Ok(Filter::Comparison(
                                FilterExpr::Arithmetic(Box::new(left), arith_op, Box::new(right_expr)),
                                op,
                                rhs,
                            ));
                        }
                    }
                    // No comparison — treat as boolean effective value of arithmetic
                    return Ok(Filter::BooleanEffectiveValue(
                        FilterExpr::Arithmetic(Box::new(left), arith_op, Box::new(right_expr)),
                    ));
                }
                _ => None,
            };
            if let Some(op) = op {
                self.next()?; // consume the operator
                let right = self.parse_filter_expr()?;
                return Ok(Filter::Comparison(left, op, right));
            }
        }
        // No comparison operator — boolean effective value
        Ok(Filter::BooleanEffectiveValue(left))
    }

    fn parse_filter_expr(&mut self) -> Result<FilterExpr, String> {
        let t = self.peek().ok_or("Unexpected end in filter expression")?.to_string();
        let upper = t.to_uppercase();

        match upper.as_str() {
            "STR" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnStr(Box::new(inner)))
            }
            "LANG" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnLang(Box::new(inner)))
            }
            "DATATYPE" => {
                self.next()?;
                self.expect("(")?;
                let inner = self.parse_filter_expr()?;
                self.expect(")")?;
                Ok(FilterExpr::FnDatatype(Box::new(inner)))
            }
            _ => {
                let tok = self.next()?;
                if tok.starts_with('?') || tok.starts_with('$') {
                    Ok(FilterExpr::Variable(tok[1..].to_string()))
                } else if tok.starts_with('"') || tok.starts_with('\'') {
                    let lexical = tok[1..tok.len()-1].to_string();
                    // Check for ^^datatype
                    if self.peek() == Some("^^") {
                        self.next()?; // ^^
                        let dt = self.next()?;
                        let _dt_iri = dt.trim_start_matches('<').trim_end_matches('>');
                        // Return as string lit (for comparison purposes)
                        Ok(FilterExpr::StringLit(lexical))
                    } else if let Some(next) = self.peek() {
                        if next.starts_with('@') {
                            self.next()?; // @lang
                        }
                        Ok(FilterExpr::StringLit(lexical))
                    } else {
                        Ok(FilterExpr::StringLit(lexical))
                    }
                } else if tok.starts_with('<') && tok.ends_with('>') {
                    Ok(FilterExpr::IriLit(
                        tok[1..tok.len() - 1].to_string(),
                    ))
                } else if tok == "true" || tok == "false" {
                    Ok(FilterExpr::StringLit(tok))
                } else if tok.chars().next().map_or(false, |c| c.is_ascii_digit() || c == '+' || c == '-') {
                    if let Ok(n) = tok.parse::<f64>() {
                        Ok(FilterExpr::NumericLit(n))
                    } else {
                        Ok(FilterExpr::StringLit(tok))
                    }
                } else if tok.contains(':') {
                    // Prefixed name in filter — treat as string for now
                    Ok(FilterExpr::StringLit(tok))
                } else {
                    Ok(FilterExpr::StringLit(tok))
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Tokenizer
// ---------------------------------------------------------------------------

fn tokenize(input: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let chars: Vec<char> = input.chars().collect();
    let len = chars.len();
    let mut i = 0;

    while i < len {
        // Skip whitespace
        if chars[i].is_whitespace() {
            i += 1;
            continue;
        }
        // Skip comments
        if chars[i] == '#' {
            while i < len && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        // Two-char operators
        if i + 1 < len {
            let two: String = chars[i..=i + 1].iter().collect();
            if matches!(two.as_str(), "!=" | "<=" | ">=" | "^^" | "||" | "&&") {
                tokens.push(two);
                i += 2;
                continue;
            }
        }
        // Single-char tokens
        if matches!(chars[i], '{' | '}' | '(' | ')' | '.' | ',' | '*' | '=' | '<' | '>' | '!' | ';' | '[' | ']') {
            // But < could start an IRI
            if chars[i] == '<' {
                let start = i;
                i += 1;
                while i < len && chars[i] != '>' {
                    i += 1;
                }
                if i < len {
                    i += 1; // consume >
                }
                let iri: String = chars[start..i].iter().collect();
                tokens.push(iri);
                continue;
            }
            tokens.push(chars[i].to_string());
            i += 1;
            continue;
        }
        // String literal
        if chars[i] == '"' {
            let start = i;
            i += 1;
            while i < len && chars[i] != '"' {
                if chars[i] == '\\' {
                    i += 1; // skip escaped char
                }
                i += 1;
            }
            if i < len {
                i += 1; // consume closing "
            }
            let s: String = chars[start..i].iter().collect();
            tokens.push(s);
            // Check for @lang immediately after
            if i < len && chars[i] == '@' {
                let ls = i;
                i += 1;
                while i < len && (chars[i].is_alphanumeric() || chars[i] == '-') {
                    i += 1;
                }
                let lang: String = chars[ls..i].iter().collect();
                tokens.push(lang);
            }
            continue;
        }
        // Word/prefixed-name/variable
        let start = i;
        while i < len
            && !chars[i].is_whitespace()
            && !matches!(chars[i], '{' | '}' | '(' | ')' | ',' | ';' | '"')
        {
            // Stop at . only if it's a statement terminator (followed by whitespace/EOF/})
            if chars[i] == '.' {
                let next = if i + 1 < len { chars[i + 1] } else { ' ' };
                if next.is_whitespace() || next == '}' || i + 1 >= len {
                    break;
                }
            }
            i += 1;
        }
        if i > start {
            let word: String = chars[start..i].iter().collect();
            tokens.push(word);
        }
    }
    tokens
}

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------

fn resolve_element(
    elem: &PatternElement,
    prefixes: &HashMap<String, String>,
) -> PatternElement {
    match elem {
        PatternElement::PrefixedName(prefix, local) => {
            if let Some(base) = prefixes.get(prefix) {
                PatternElement::Iri(format!("{base}{local}"))
            } else {
                elem.clone()
            }
        }
        PatternElement::Literal(lex, lang, Some(dt)) if dt.contains(':') && !dt.starts_with("http") => {
            // Resolve prefixed datatype like xsd:integer
            let parts: Vec<&str> = dt.splitn(2, ':').collect();
            if let Some(base) = prefixes.get(parts[0]) {
                PatternElement::Literal(
                    lex.clone(),
                    lang.clone(),
                    Some(format!("{}{}", base, parts.get(1).unwrap_or(&""))),
                )
            } else {
                elem.clone()
            }
        }
        other => other.clone(),
    }
}

fn match_element(elem: &PatternElement, term: &TermValue) -> Option<Option<(String, TermValue)>> {
    match elem {
        PatternElement::Variable(name) => Some(Some((name.clone(), term.clone()))),
        PatternElement::Iri(iri) => {
            if let TermValue::Iri(s) = term {
                if s == iri {
                    Some(None)
                } else {
                    None
                }
            } else {
                None
            }
        }
        PatternElement::Literal(lex, lang, dt) => {
            if let TermValue::Literal {
                lexical,
                datatype,
                lang: tlang,
            } = term
            {
                if lexical != lex {
                    return None;
                }
                if let Some(l) = lang {
                    if tlang.as_deref() != Some(l.as_str()) {
                        return None;
                    }
                }
                if let Some(d) = dt {
                    if datatype != d {
                        return None;
                    }
                }
                Some(None)
            } else {
                None
            }
        }
        PatternElement::PrefixedName(_, _) => None, // should be resolved already
    }
}

fn match_triple(
    pattern: &TriplePattern,
    triple: &Triple,
    existing: &Binding,
    prefixes: &HashMap<String, String>,
) -> Option<Binding> {
    let s_elem = resolve_element(&pattern.s, prefixes);
    let p_elem = resolve_element(&pattern.p, prefixes);
    let o_elem = resolve_element(&pattern.o, prefixes);

    let s_term = TermValue::from_subject(&triple.s);
    let p_term = TermValue::Iri(triple.p.as_str().to_string());
    let o_term = TermValue::from_rdf_term(&triple.o);

    let mut new_bindings = existing.clone();

    for (elem, term) in [(&s_elem, &s_term), (&p_elem, &p_term), (&o_elem, &o_term)] {
        // If the element is a variable already bound, check consistency
        if let PatternElement::Variable(name) = elem {
            if let Some(bound) = existing.get(name) {
                if bound != term {
                    return None;
                }
                continue;
            }
        }
        match match_element(elem, term) {
            Some(Some((name, val))) => {
                new_bindings.insert(name, val);
            }
            Some(None) => {} // matched constant
            None => return None,
        }
    }

    Some(new_bindings)
}

/// Typed filter value for type-aware SPARQL comparisons.
#[derive(Debug, Clone)]
enum TypedFilterValue {
    Iri(String),
    BNode(String),
    PlainLiteral(String),         // xsd:string or untyped
    LangLiteral(String, String),  // lexical, lang tag
    NumericLiteral(f64, String),  // numeric value, datatype IRI
    TypedLiteral(String, String), // lexical, datatype IRI (non-numeric, non-string)
    BooleanLiteral(bool),
}

impl TypedFilterValue {
    fn as_string(&self) -> String {
        match self {
            TypedFilterValue::Iri(s) | TypedFilterValue::BNode(s) => s.clone(),
            TypedFilterValue::PlainLiteral(s) => s.clone(),
            TypedFilterValue::LangLiteral(s, _) => s.clone(),
            TypedFilterValue::NumericLiteral(n, _) => n.to_string(),
            TypedFilterValue::TypedLiteral(s, _) => s.clone(),
            TypedFilterValue::BooleanLiteral(b) => if *b { "true" } else { "false" }.to_string(),
        }
    }

    fn is_numeric(&self) -> bool {
        matches!(self, TypedFilterValue::NumericLiteral(..))
    }
}

const XSD_INTEGER: &str = "http://www.w3.org/2001/XMLSchema#integer";
const XSD_DECIMAL: &str = "http://www.w3.org/2001/XMLSchema#decimal";
const XSD_DOUBLE: &str = "http://www.w3.org/2001/XMLSchema#double";
const XSD_FLOAT: &str = "http://www.w3.org/2001/XMLSchema#float";
const XSD_BOOLEAN: &str = "http://www.w3.org/2001/XMLSchema#boolean";

fn is_numeric_type(dt: &str) -> bool {
    dt == XSD_INTEGER || dt == XSD_DECIMAL || dt == XSD_DOUBLE || dt == XSD_FLOAT
}

fn term_to_typed(tv: &TermValue) -> TypedFilterValue {
    match tv {
        TermValue::Iri(s) => TypedFilterValue::Iri(s.clone()),
        TermValue::BNode(s) => TypedFilterValue::BNode(s.clone()),
        TermValue::Literal { lexical, datatype, lang } => {
            if let Some(l) = lang {
                TypedFilterValue::LangLiteral(lexical.clone(), l.clone())
            } else if datatype == XSD_BOOLEAN {
                TypedFilterValue::BooleanLiteral(lexical == "true" || lexical == "1")
            } else if is_numeric_type(datatype) {
                if let Ok(n) = lexical.parse::<f64>() {
                    TypedFilterValue::NumericLiteral(n, datatype.clone())
                } else {
                    TypedFilterValue::TypedLiteral(lexical.clone(), datatype.clone())
                }
            } else if datatype == rdf::XSD_STRING {
                TypedFilterValue::PlainLiteral(lexical.clone())
            } else {
                TypedFilterValue::TypedLiteral(lexical.clone(), datatype.clone())
            }
        }
    }
}

fn eval_filter_expr_typed(expr: &FilterExpr, binding: &Binding) -> Option<TypedFilterValue> {
    match expr {
        FilterExpr::Variable(name) => binding.get(name).map(term_to_typed),
        FilterExpr::StringLit(s) => Some(TypedFilterValue::PlainLiteral(s.clone())),
        FilterExpr::NumericLit(n) => Some(TypedFilterValue::NumericLiteral(*n, XSD_INTEGER.to_string())),
        FilterExpr::IriLit(s) => Some(TypedFilterValue::Iri(s.clone())),
        FilterExpr::FnStr(inner) => {
            let v = eval_filter_expr_typed(inner, binding)?;
            Some(TypedFilterValue::PlainLiteral(v.as_string()))
        }
        FilterExpr::FnLang(inner) => {
            if let FilterExpr::Variable(name) = inner.as_ref() {
                if let Some(TermValue::Literal { lang, .. }) = binding.get(name) {
                    Some(TypedFilterValue::PlainLiteral(lang.clone().unwrap_or_default()))
                } else {
                    Some(TypedFilterValue::PlainLiteral(String::new()))
                }
            } else {
                Some(TypedFilterValue::PlainLiteral(String::new()))
            }
        }
        FilterExpr::FnDatatype(inner) => {
            if let FilterExpr::Variable(name) = inner.as_ref() {
                if let Some(TermValue::Literal { datatype, .. }) = binding.get(name) {
                    Some(TypedFilterValue::Iri(datatype.clone()))
                } else {
                    None
                }
            } else {
                None
            }
        }
        FilterExpr::Arithmetic(left, op, right) => {
            let lv = eval_filter_expr_typed(left, binding)?;
            let rv = eval_filter_expr_typed(right, binding)?;
            let ln = match &lv {
                TypedFilterValue::NumericLiteral(n, _) => *n,
                TypedFilterValue::PlainLiteral(s) => s.parse::<f64>().ok()?,
                _ => return None,
            };
            let rn = match &rv {
                TypedFilterValue::NumericLiteral(n, _) => *n,
                TypedFilterValue::PlainLiteral(s) => s.parse::<f64>().ok()?,
                _ => return None,
            };
            let result = match op.as_str() {
                "+" => ln + rn,
                "-" => ln - rn,
                "*" => ln * rn,
                "/" => {
                    if rn == 0.0 { return None; }
                    ln / rn
                }
                _ => return None,
            };
            // Determine result type: promote to double if either is double/decimal
            let dt = match (&lv, &rv) {
                (TypedFilterValue::NumericLiteral(_, ld), TypedFilterValue::NumericLiteral(_, rd)) => {
                    if ld == XSD_DOUBLE || rd == XSD_DOUBLE { XSD_DOUBLE }
                    else if ld == XSD_DECIMAL || rd == XSD_DECIMAL { XSD_DECIMAL }
                    else { XSD_INTEGER }
                }
                _ => XSD_DOUBLE,
            };
            Some(TypedFilterValue::NumericLiteral(result, dt.to_string()))
        }
    }
}

/// SPARQL value equality (=) with type awareness.
/// Returns None for type errors (incomparable types).
fn typed_compare(lv: &TypedFilterValue, rv: &TypedFilterValue, op: &CompOp) -> Option<bool> {
    match (lv, rv) {
        // Numeric vs numeric: cross-type comparison allowed
        (TypedFilterValue::NumericLiteral(ln, _), TypedFilterValue::NumericLiteral(rn, _)) => {
            Some(match op {
                CompOp::Eq => (ln - rn).abs() < f64::EPSILON,
                CompOp::Ne => (ln - rn).abs() >= f64::EPSILON,
                CompOp::Lt => ln < rn,
                CompOp::Gt => ln > rn,
                CompOp::Le => ln <= rn,
                CompOp::Ge => ln >= rn,
            })
        }
        // Boolean vs boolean
        (TypedFilterValue::BooleanLiteral(l), TypedFilterValue::BooleanLiteral(r)) => {
            Some(match op {
                CompOp::Eq => l == r,
                CompOp::Ne => l != r,
                _ => return None,
            })
        }
        // Plain literal vs plain literal: string comparison
        (TypedFilterValue::PlainLiteral(l), TypedFilterValue::PlainLiteral(r)) => {
            Some(match op {
                CompOp::Eq => l == r,
                CompOp::Ne => l != r,
                CompOp::Lt => l < r,
                CompOp::Gt => l > r,
                CompOp::Le => l <= r,
                CompOp::Ge => l >= r,
            })
        }
        // Lang literals: equal only if both lexical and lang match
        (TypedFilterValue::LangLiteral(llex, llang), TypedFilterValue::LangLiteral(rlex, rlang)) => {
            Some(match op {
                CompOp::Eq => llex == rlex && llang.to_lowercase() == rlang.to_lowercase(),
                CompOp::Ne => llex != rlex || llang.to_lowercase() != rlang.to_lowercase(),
                _ => return None,
            })
        }
        // IRI vs IRI
        (TypedFilterValue::Iri(l), TypedFilterValue::Iri(r)) => {
            Some(match op {
                CompOp::Eq => l == r,
                CompOp::Ne => l != r,
                CompOp::Lt => l < r,
                CompOp::Gt => l > r,
                CompOp::Le => l <= r,
                CompOp::Ge => l >= r,
            })
        }
        // BNode vs BNode
        (TypedFilterValue::BNode(l), TypedFilterValue::BNode(r)) => {
            Some(match op {
                CompOp::Eq => l == r,
                CompOp::Ne => l != r,
                _ => return None,
            })
        }
        // Same unknown typed literals: compare if same datatype
        (TypedFilterValue::TypedLiteral(llex, ldt), TypedFilterValue::TypedLiteral(rlex, rdt)) => {
            if ldt == rdt {
                // Same datatype: lexical comparison for ordering
                Some(match op {
                    CompOp::Eq => llex == rlex,
                    CompOp::Ne => llex != rlex,
                    CompOp::Lt => llex < rlex,
                    CompOp::Gt => llex > rlex,
                    CompOp::Le => llex <= rlex,
                    CompOp::Ge => llex >= rlex,
                })
            } else {
                // Different unknown types: type error
                None
            }
        }
        // Incompatible types (plain vs numeric, etc.): type error → None
        _ => None,
    }
}

fn eval_filter_expr(expr: &FilterExpr, binding: &Binding) -> Option<String> {
    eval_filter_expr_typed(expr, binding).map(|v| v.as_string())
}

fn eval_filter(filter: &Filter, binding: &Binding) -> bool {
    match filter {
        Filter::Comparison(left, op, right) => {
            let lv = eval_filter_expr_typed(left, binding);
            let rv = eval_filter_expr_typed(right, binding);
            match (lv, rv) {
                (Some(l), Some(r)) => typed_compare(&l, &r, op).unwrap_or(false),
                _ => false,
            }
        }
        Filter::And(a, b) => eval_filter(a, binding) && eval_filter(b, binding),
        Filter::Or(a, b) => eval_filter(a, binding) || eval_filter(b, binding),
        Filter::Not(inner) => !eval_filter(inner, binding),
        Filter::BooleanEffectiveValue(expr) => {
            // SPARQL boolean effective value:
            // - bound variable with non-empty string → true
            // - "true"^^xsd:boolean → true
            // - non-zero numeric → true
            // - "" or "0" or "false" or unbound → false
            match expr {
                FilterExpr::Variable(name) => {
                    if let Some(val) = binding.get(name) {
                        match val {
                            TermValue::Literal { lexical, datatype, .. } => {
                                if datatype == "http://www.w3.org/2001/XMLSchema#boolean" {
                                    lexical == "true" || lexical == "1"
                                } else if datatype == "http://www.w3.org/2001/XMLSchema#integer"
                                    || datatype == "http://www.w3.org/2001/XMLSchema#decimal"
                                    || datatype == "http://www.w3.org/2001/XMLSchema#double"
                                    || datatype == "http://www.w3.org/2001/XMLSchema#float"
                                {
                                    lexical.parse::<f64>().map_or(false, |n| n != 0.0)
                                } else {
                                    !lexical.is_empty()
                                }
                            }
                            TermValue::Iri(_) | TermValue::BNode(_) => true,
                        }
                    } else {
                        false // unbound → false
                    }
                }
                _ => {
                    if let Some(val) = eval_filter_expr(expr, binding) {
                        !val.is_empty() && val != "0" && val != "false"
                    } else {
                        false
                    }
                }
            }
        }
        Filter::FnBound(var) => binding.contains_key(var),
        Filter::FnIsLiteral(expr) => {
            if let FilterExpr::Variable(name) = expr {
                matches!(binding.get(name), Some(TermValue::Literal { .. }))
            } else {
                false
            }
        }
        Filter::FnIsIri(expr) => {
            if let FilterExpr::Variable(name) = expr {
                matches!(binding.get(name), Some(TermValue::Iri(_)))
            } else {
                false
            }
        }
        Filter::FnIsBlank(expr) => {
            if let FilterExpr::Variable(name) = expr {
                matches!(binding.get(name), Some(TermValue::BNode(_)))
            } else {
                false
            }
        }
        Filter::FnRegex(expr, pattern, flags) => {
            if let Some(val) = eval_filter_expr(expr, binding) {
                let case_insensitive = flags.as_ref().map_or(false, |f| f.contains('i'));
                let dot_matches_newline = flags.as_ref().map_or(false, |f| f.contains('s'));
                let multi_line = flags.as_ref().map_or(false, |f| f.contains('m'));
                match RegexBuilder::new(pattern)
                    .case_insensitive(case_insensitive)
                    .dot_matches_new_line(dot_matches_newline)
                    .multi_line(multi_line)
                    .build()
                {
                    Ok(re) => re.is_match(&val),
                    Err(_) => false, // invalid regex pattern → no match
                }
            } else {
                false
            }
        }
        Filter::FnContains(a, b) => {
            let av = eval_filter_expr(a, binding);
            let bv = eval_filter_expr(b, binding);
            match (av, bv) {
                (Some(a), Some(b)) => a.contains(&b),
                _ => false,
            }
        }
        Filter::FnStrStarts(a, b) => {
            let av = eval_filter_expr(a, binding);
            let bv = eval_filter_expr(b, binding);
            match (av, bv) {
                (Some(a), Some(b)) => a.starts_with(&b),
                _ => false,
            }
        }
        Filter::FnStrEnds(a, b) => {
            let av = eval_filter_expr(a, binding);
            let bv = eval_filter_expr(b, binding);
            match (av, bv) {
                (Some(a), Some(b)) => a.ends_with(&b),
                _ => false,
            }
        }
    }
}

fn evaluate_clauses(
    clauses: &[WhereClause],
    graph: &RdfGraph,
    initial: Vec<Binding>,
    prefixes: &HashMap<String, String>,
) -> Vec<Binding> {
    let mut results = initial;

    for clause in clauses {
        match clause {
            WhereClause::Pattern(pattern) => {
                let mut new_results = Vec::new();
                for binding in &results {
                    for triple in graph.triples() {
                        if let Some(new_binding) = match_triple(pattern, triple, binding, prefixes)
                        {
                            new_results.push(new_binding);
                        }
                    }
                }
                results = new_results;
            }
            WhereClause::Filter(filter) => {
                results.retain(|b| eval_filter(filter, b));
            }
            WhereClause::Optional(inner_clauses) => {
                let mut new_results = Vec::new();
                for binding in &results {
                    let matched =
                        evaluate_clauses(inner_clauses, graph, vec![binding.clone()], prefixes);
                    if matched.is_empty() {
                        new_results.push(binding.clone());
                    } else {
                        new_results.extend(matched);
                    }
                }
                results = new_results;
            }
            WhereClause::Union(right_clauses) => {
                // Evaluate right branch from scratch, union with current results
                let right_results =
                    evaluate_clauses(right_clauses, graph, vec![Binding::new()], prefixes);
                results.extend(right_results);
            }
            WhereClause::UnionGroup(branches) => {
                // Evaluate each branch independently, union all results
                let mut union_results = Vec::new();
                for branch in branches {
                    // Each branch starts from current results (join semantics)
                    let branch_results =
                        evaluate_clauses(branch, graph, results.clone(), prefixes);
                    union_results.extend(branch_results);
                }
                results = union_results;
            }
        }
    }

    results
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Result of a SPARQL SELECT query.
#[derive(Debug, Clone, Serialize)]
pub struct QueryResult {
    pub variables: Vec<String>,
    pub rows: Vec<Vec<Option<String>>>,
}

/// Execute a SPARQL SELECT query against the given graph.
pub fn execute(graph: &RdfGraph, query_str: &str) -> Result<QueryResult, String> {
    let mut parser = Parser::new(query_str);
    let query = parser.parse_query()?;

    let initial = vec![Binding::new()];
    let mut results = evaluate_clauses(&query.where_clauses, graph, initial, &query.prefixes);

    // Determine output variables
    let vars = if query.variables.is_empty() {
        // SELECT * — collect all variables seen
        let mut all_vars: Vec<String> = Vec::new();
        for binding in &results {
            for key in binding.keys() {
                if !all_vars.contains(key) {
                    all_vars.push(key.clone());
                }
            }
        }
        all_vars.sort();
        all_vars
    } else {
        query.variables
    };

    // ORDER BY
    if !query.order_by.is_empty() {
        results.sort_by(|a, b| {
            for oc in &query.order_by {
                let av = a.get(&oc.var);
                let bv = b.get(&oc.var);
                let cmp = match (av, bv) {
                    (Some(av), Some(bv)) => av.sort_key().cmp(&bv.sort_key()),
                    (Some(_), None) => std::cmp::Ordering::Less,
                    (None, Some(_)) => std::cmp::Ordering::Greater,
                    (None, None) => std::cmp::Ordering::Equal,
                };
                let cmp = match oc.dir {
                    OrderDir::Asc => cmp,
                    OrderDir::Desc => cmp.reverse(),
                };
                if cmp != std::cmp::Ordering::Equal {
                    return cmp;
                }
            }
            std::cmp::Ordering::Equal
        });
    }

    // DISTINCT
    if query.distinct {
        let mut seen: Vec<Vec<Option<String>>> = Vec::new();
        results.retain(|b| {
            let row: Vec<Option<String>> = vars
                .iter()
                .map(|v| b.get(v).map(|tv| tv.display()))
                .collect();
            if seen.contains(&row) {
                false
            } else {
                seen.push(row);
                true
            }
        });
    }

    // OFFSET
    if let Some(offset) = query.offset {
        if offset < results.len() {
            results = results[offset..].to_vec();
        } else {
            results.clear();
        }
    }

    // LIMIT
    if let Some(limit) = query.limit {
        results.truncate(limit);
    }

    // Format output
    let rows: Vec<Vec<Option<String>>> = results
        .iter()
        .map(|binding| {
            vars.iter()
                .map(|v| binding.get(v).map(|tv| tv.display()))
                .collect()
        })
        .collect();

    Ok(QueryResult {
        variables: vars,
        rows,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rdf::*;

    fn test_graph() -> RdfGraph {
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
            s: Subject::Iri(Iri::new("http://example.org/bob").unwrap()),
            p: Iri::new("http://xmlns.com/foaf/0.1/name").unwrap(),
            o: RdfTerm::Literal(Literal::lang("Bob", "en")),
        });
        g.add(Triple {
            s: Subject::Iri(Iri::new("http://example.org/bob").unwrap()),
            p: Iri::new("http://www.w3.org/1999/02/22-rdf-syntax-ns#type").unwrap(),
            o: RdfTerm::Iri(Iri::new("http://xmlns.com/foaf/0.1/Person").unwrap()),
        });
        g
    }

    #[test]
    fn select_star() {
        let g = test_graph();
        let r = execute(&g, "SELECT * WHERE { ?s ?p ?o }").unwrap();
        assert_eq!(r.rows.len(), 4);
        assert_eq!(r.variables.len(), 3);
    }

    #[test]
    fn select_with_prefix() {
        let g = test_graph();
        let r = execute(
            &g,
            "PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?s ?name WHERE { ?s foaf:name ?name }",
        )
        .unwrap();
        assert_eq!(r.rows.len(), 2);
    }

    #[test]
    fn select_with_filter() {
        let g = test_graph();
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?s ?name WHERE { ?s foaf:name ?name . FILTER (LANG(?name) = "en") }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1);
    }

    #[test]
    fn select_distinct() {
        let g = test_graph();
        let r = execute(
            &g,
            "PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT DISTINCT ?s WHERE { ?s foaf:name ?name }",
        )
        .unwrap();
        assert_eq!(r.rows.len(), 2);
    }

    #[test]
    fn select_limit_offset() {
        let g = test_graph();
        let r = execute(&g, "SELECT * WHERE { ?s ?p ?o } LIMIT 2").unwrap();
        assert_eq!(r.rows.len(), 2);

        let r = execute(&g, "SELECT * WHERE { ?s ?p ?o } LIMIT 2 OFFSET 3").unwrap();
        assert_eq!(r.rows.len(), 1);
    }

    #[test]
    fn select_optional() {
        let g = test_graph();
        let r = execute(
            &g,
            "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
             PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
             SELECT ?s ?name WHERE {
               ?s rdf:type foaf:Person .
               OPTIONAL { ?s foaf:name ?name }
             }",
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1); // only bob has rdf:type
    }

    #[test]
    fn select_join() {
        let g = test_graph();
        let r = execute(
            &g,
            "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
             SELECT ?name ?friend_name WHERE {
               ?s foaf:name ?name .
               ?s foaf:knows ?friend .
               ?friend foaf:name ?friend_name
             }",
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1); // Alice knows Bob, Bob has name
    }

    #[test]
    fn empty_graph_query() {
        let g = RdfGraph::new();
        let r = execute(&g, "SELECT * WHERE { ?s ?p ?o }").unwrap();
        assert_eq!(r.rows.len(), 0);
    }

    #[test]
    fn no_matches() {
        let g = test_graph();
        let r = execute(
            &g,
            "SELECT ?s WHERE { ?s <http://example.org/nonexistent> ?o }",
        )
        .unwrap();
        assert_eq!(r.rows.len(), 0);
    }

    #[test]
    fn invalid_query_errors() {
        let g = test_graph();
        assert!(execute(&g, "NOT SPARQL").is_err());
        assert!(execute(&g, "SELECT").is_err());
        assert!(execute(&g, "SELECT * WHERE").is_err());
    }

    #[test]
    fn regex_actual_pattern() {
        let g = test_graph();
        // ^A matches "Alice" but not "Bob"
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE {
                 ?s foaf:name ?name .
                 FILTER (REGEX(STR(?name), "^A"))
               }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1);

        // Case-insensitive regex
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE {
                 ?s foaf:name ?name .
                 FILTER (REGEX(STR(?name), "^b", "i"))
               }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1);

        // Regex with character class
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE {
                 ?s foaf:name ?name .
                 FILTER (REGEX(STR(?name), "[aeiou]ce$"))
               }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1); // "Alice" matches [aeiou]ce$
    }

    #[test]
    fn numeric_comparison() {
        let mut g = RdfGraph::new();
        let xsd_int = Iri::new("http://www.w3.org/2001/XMLSchema#integer").unwrap();
        for (name, age) in [("Alice", "30"), ("Bob", "2"), ("Charlie", "10")] {
            g.add(Triple {
                s: Subject::Iri(Iri::new(&format!("http://example.org/{}", name.to_lowercase())).unwrap()),
                p: Iri::new("http://example.org/age").unwrap(),
                o: RdfTerm::Literal(Literal::new(age, xsd_int.clone(), None).unwrap()),
            });
        }

        // String comparison would give "10" < "2" = true (wrong), "30" < "2" = false
        // Numeric comparison: 10 > 2 (correct)
        let r = execute(
            &g,
            r#"SELECT ?s ?age WHERE {
                 ?s <http://example.org/age> ?age .
                 FILTER (?age > 5)
               }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 2); // Alice (30) and Charlie (10), NOT Bob (2)
    }

    #[test]
    fn limit_zero() {
        let g = test_graph();
        let r = execute(&g, "SELECT * WHERE { ?s ?p ?o } LIMIT 0").unwrap();
        assert_eq!(r.rows.len(), 0);
    }

    #[test]
    fn offset_beyond_results() {
        let g = test_graph();
        let r = execute(&g, "SELECT * WHERE { ?s ?p ?o } OFFSET 100").unwrap();
        assert_eq!(r.rows.len(), 0);
    }

    #[test]
    fn order_by_asc_desc() {
        let g = test_graph();
        let r = execute(
            &g,
            "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
             SELECT ?name WHERE { ?s foaf:name ?name } ORDER BY ASC(?name)",
        )
        .unwrap();
        assert_eq!(r.rows.len(), 2);
        // Alice < Bob lexicographically
        let first = r.rows[0][0].as_ref().unwrap();
        assert!(first.contains("Alice"));

        let r = execute(
            &g,
            "PREFIX foaf: <http://xmlns.com/foaf/0.1/>
             SELECT ?name WHERE { ?s foaf:name ?name } ORDER BY DESC(?name)",
        )
        .unwrap();
        let first = r.rows[0][0].as_ref().unwrap();
        assert!(first.contains("Bob"));
    }

    #[test]
    fn filter_isiri_isliteral_isblank() {
        let mut g = RdfGraph::new();
        g.add(Triple {
            s: Subject::Iri(Iri::new("http://example.org/a").unwrap()),
            p: Iri::new("http://example.org/p").unwrap(),
            o: RdfTerm::Iri(Iri::new("http://example.org/b").unwrap()),
        });
        g.add(Triple {
            s: Subject::Iri(Iri::new("http://example.org/a").unwrap()),
            p: Iri::new("http://example.org/q").unwrap(),
            o: RdfTerm::Literal(Literal::plain("text")),
        });
        g.add(Triple {
            s: Subject::Iri(Iri::new("http://example.org/a").unwrap()),
            p: Iri::new("http://example.org/r").unwrap(),
            o: RdfTerm::BNode(BNode::new(999)),
        });

        let r = execute(&g, "SELECT ?o WHERE { ?s ?p ?o . FILTER (ISIRI(?o)) }").unwrap();
        assert_eq!(r.rows.len(), 1);

        let r = execute(&g, "SELECT ?o WHERE { ?s ?p ?o . FILTER (ISLITERAL(?o)) }").unwrap();
        assert_eq!(r.rows.len(), 1);

        let r = execute(&g, "SELECT ?o WHERE { ?s ?p ?o . FILTER (ISBLANK(?o)) }").unwrap();
        assert_eq!(r.rows.len(), 1);
    }

    #[test]
    fn filter_boolean_operators() {
        let g = test_graph();
        // AND
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE {
                 ?s foaf:name ?name .
                 FILTER (ISLITERAL(?name) && LANG(?name) = "en")
               }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1);

        // OR
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE {
                 ?s foaf:name ?name .
                 FILTER (LANG(?name) = "en" || STR(?name) = "Alice")
               }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 2);
    }

    #[test]
    fn filter_contains_strstarts_strends() {
        let g = test_graph();
        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE { ?s foaf:name ?name . FILTER (CONTAINS(STR(?name), "lic")) }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1); // Alice

        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE { ?s foaf:name ?name . FILTER (STRSTARTS(STR(?name), "A")) }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1);

        let r = execute(
            &g,
            r#"PREFIX foaf: <http://xmlns.com/foaf/0.1/>
               SELECT ?name WHERE { ?s foaf:name ?name . FILTER (STRENDS(STR(?name), "ob")) }"#,
        )
        .unwrap();
        assert_eq!(r.rows.len(), 1); // Bob
    }
}
