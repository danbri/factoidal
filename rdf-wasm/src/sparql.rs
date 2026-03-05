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
            RdfTerm::BNode(b) => TermValue::BNode(b.id().to_string()),
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
            Subject::BNode(b) => TermValue::BNode(b.id().to_string()),
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
    FnStr(Box<FilterExpr>),
    FnLang(Box<FilterExpr>),
    FnDatatype(Box<FilterExpr>),
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

        // Parse PREFIX declarations
        while self.peek().map(|t| t.to_uppercase()) == Some("PREFIX".to_string()) {
            self.next()?; // PREFIX
            let prefix = self.next()?; // e.g. "foaf:"
            let iri_tok = self.next()?; // e.g. "<http://...>"
            let iri = iri_tok
                .trim_start_matches('<')
                .trim_end_matches('>')
                .to_string();
            prefixes.insert(prefix.trim_end_matches(':').to_string(), iri);
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

        self.expect("WHERE")?;
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
                self.expect("(")?;
                let filter = self.parse_filter()?;
                self.expect(")")?;
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
            } else {
                // Triple pattern
                let s = self.parse_pattern_element()?;
                let p = self.parse_pattern_element()?;
                let o = self.parse_pattern_element()?;
                // optional .
                if self.peek() == Some(".") {
                    self.next()?;
                }
                clauses.push(WhereClause::Pattern(TriplePattern { s, p, o }));
            }
        }

        Ok(clauses)
    }

    fn parse_pattern_element(&mut self) -> Result<PatternElement, String> {
        let t = self.next()?;
        if t.starts_with('?') {
            Ok(PatternElement::Variable(t[1..].to_string()))
        } else if t.starts_with('<') && t.ends_with('>') {
            Ok(PatternElement::Iri(
                t[1..t.len() - 1].to_string(),
            ))
        } else if t.starts_with('"') {
            // String literal — may have @lang or ^^type
            let lexical = t.trim_matches('"').to_string();
            let mut lang = None;
            let mut datatype = None;
            if let Some(next) = self.peek() {
                if next.starts_with('@') {
                    lang = Some(self.next()?[1..].to_string());
                } else if next == "^^" {
                    self.next()?; // ^^
                    let dt = self.next()?;
                    datatype = Some(
                        dt.trim_start_matches('<')
                            .trim_end_matches('>')
                            .to_string(),
                    );
                }
            }
            Ok(PatternElement::Literal(lexical, lang, datatype))
        } else if t.contains(':') {
            // Prefixed name like foaf:name
            let parts: Vec<&str> = t.splitn(2, ':').collect();
            Ok(PatternElement::PrefixedName(
                parts[0].to_string(),
                parts.get(1).unwrap_or(&"").to_string(),
            ))
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

        // Comparison: expr OP expr
        let left = self.parse_filter_expr()?;
        let op_tok = self.next()?;
        let op = match op_tok.as_str() {
            "=" => CompOp::Eq,
            "!=" => CompOp::Ne,
            "<" => CompOp::Lt,
            ">" => CompOp::Gt,
            "<=" => CompOp::Le,
            ">=" => CompOp::Ge,
            other => return Err(format!("Unknown comparison operator: '{other}'")),
        };
        let right = self.parse_filter_expr()?;
        Ok(Filter::Comparison(left, op, right))
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
                if tok.starts_with('?') {
                    Ok(FilterExpr::Variable(tok[1..].to_string()))
                } else if tok.starts_with('"') {
                    Ok(FilterExpr::StringLit(tok.trim_matches('"').to_string()))
                } else if tok.starts_with('<') && tok.ends_with('>') {
                    Ok(FilterExpr::StringLit(
                        tok[1..tok.len() - 1].to_string(),
                    ))
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
        if matches!(chars[i], '{' | '}' | '(' | ')' | '.' | ',' | '*' | '=' | '<' | '>' | '!' | ';') {
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

fn eval_filter_expr(expr: &FilterExpr, binding: &Binding) -> Option<String> {
    match expr {
        FilterExpr::Variable(name) => binding.get(name).map(|v| v.as_str_value().to_string()),
        FilterExpr::StringLit(s) => Some(s.clone()),
        FilterExpr::FnStr(inner) => {
            if let FilterExpr::Variable(name) = inner.as_ref() {
                binding.get(name).map(|v| v.as_str_value().to_string())
            } else {
                eval_filter_expr(inner, binding)
            }
        }
        FilterExpr::FnLang(inner) => {
            if let FilterExpr::Variable(name) = inner.as_ref() {
                if let Some(TermValue::Literal { lang, .. }) = binding.get(name) {
                    Some(lang.clone().unwrap_or_default())
                } else {
                    Some(String::new())
                }
            } else {
                Some(String::new())
            }
        }
        FilterExpr::FnDatatype(inner) => {
            if let FilterExpr::Variable(name) = inner.as_ref() {
                if let Some(TermValue::Literal { datatype, .. }) = binding.get(name) {
                    Some(datatype.clone())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }
}

fn eval_filter(filter: &Filter, binding: &Binding) -> bool {
    match filter {
        Filter::Comparison(left, op, right) => {
            let lv = eval_filter_expr(left, binding);
            let rv = eval_filter_expr(right, binding);
            match (lv, rv) {
                (Some(l), Some(r)) => match op {
                    CompOp::Eq => l == r,
                    CompOp::Ne => l != r,
                    CompOp::Lt => l < r,
                    CompOp::Gt => l > r,
                    CompOp::Le => l <= r,
                    CompOp::Ge => l >= r,
                },
                _ => false,
            }
        }
        Filter::And(a, b) => eval_filter(a, binding) && eval_filter(b, binding),
        Filter::Or(a, b) => eval_filter(a, binding) || eval_filter(b, binding),
        Filter::Not(inner) => !eval_filter(inner, binding),
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
                if case_insensitive {
                    val.to_lowercase()
                        .contains(&pattern.to_lowercase())
                } else {
                    val.contains(pattern.as_str())
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
}
